//! Canonical semantic sidecar facts for prepared SSA functions.
//!
//! These facts keep object, memory, predicate, and call-site provenance in
//! `r2ssa` so downstream crates stop reconstructing them independently.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::address::{AddressProvenanceFacts, collect_address_provenance};
use crate::assumption::{AssumptionSet, AssumptionSubject, AssumptionUsageReport, AssumptionValue};
use crate::cfg::BlockTerminator;
use crate::function::{DecompilePrepFacts, SSAFunction, StackAddressBase, StackAddressRoot};
use crate::graph::{InstId, InstPayload, SsaGraph, ValueId};
use crate::machine_context::{
    SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SOURCE_TYPE_GRAPH_SCHEMA_VERSION, SourceCallResult,
    SourceCallSiteIdentity, SourceCarrierKind, SourceFunctionReturn, SourceLogicalValue,
    SourceMachineContext, SourceTypeKind,
};
use crate::obligation::SemanticObligationInventory;
use crate::op::SSAOp;
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobalObjectKey {
    pub space: String,
    pub address: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectKind {
    StackSlot { base: StackAddressBase, offset: i64 },
    FrameObject { base: StackAddressBase, offset: i64 },
    Parameter { index: usize },
    Global { space: String, address: u64 },
    HeapAlloc { call_site: CallSiteId },
    EscapedUnknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectFact {
    pub id: ObjectId,
    pub kind: ObjectKind,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ObjectModel {
    pub objects: BTreeMap<ObjectId, ObjectFact>,
    pub value_objects: BTreeMap<ValueId, ObjectId>,
    pub stack_objects: BTreeMap<StackAddressRoot, ObjectId>,
    pub parameter_objects: BTreeMap<usize, ObjectId>,
    pub global_objects: BTreeMap<GlobalObjectKey, ObjectId>,
    pub escaped_unknown: Option<ObjectId>,
}

impl ObjectModel {
    pub fn object_for_value(&self, value: ValueId) -> Option<ObjectId> {
        self.value_objects.get(&value).copied()
    }

    pub fn object_for_var(&self, graph: &SsaGraph, value: &SSAVar) -> Option<ObjectId> {
        graph
            .value_id_for_var(value)
            .and_then(|value_id| self.object_for_value(value_id))
    }

    pub fn object(&self, id: ObjectId) -> Option<&ObjectFact> {
        self.objects.get(&id)
    }

    pub fn escaped_unknown_object(&self) -> Option<ObjectId> {
        self.escaped_unknown
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryLocation {
    pub object: ObjectId,
    pub address: RelativeMemoryAddress,
    pub size: u32,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCallBoundaryFact {
    pub call_site: CallSiteId,
    pub at: InstId,
    pub calling_convention: Option<String>,
    pub variadic: Option<bool>,
    pub noreturn: Option<bool>,
    pub result_kind: Option<SourceCallResult>,
    pub arguments: Vec<CallBoundaryValueFact>,
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceReturnAddressFact {
    pub storage: CanonicalStorageId,
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
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LoopCarrierUpdateFact {
    pub predecessor: u64,
    pub value: ValueId,
    /// Values bit-identical to `value` through same-width copy chains.
    pub identity_values: BTreeSet<ValueId>,
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
    pub object: ObjectId,
    pub address: ValueId,
    pub value: Option<ValueId>,
    pub is_write: bool,
    pub width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackSlotCertificate {
    pub object: ObjectId,
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
        name: String,
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
        Self::collect_inner(function, graph, &AssumptionSet::default(), None)
    }

    pub fn collect_with_assumptions(
        function: &SSAFunction,
        graph: &SsaGraph,
        assumptions: &AssumptionSet,
    ) -> Self {
        Self::collect_inner(function, graph, assumptions, None)
    }

    pub(crate) fn collect_with_context(
        function: &SSAFunction,
        graph: &SsaGraph,
        assumptions: &AssumptionSet,
        machine_context: &SourceMachineContext,
    ) -> Self {
        Self::collect_inner(function, graph, assumptions, Some(machine_context))
    }

    fn collect_inner(
        function: &SSAFunction,
        graph: &SsaGraph,
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
        let (objects, memory) =
            collect_object_and_memory_facts(function, graph, &addresses, &call_sites);
        let predicates = apply_assumptions_to_predicate_facts(
            collect_predicate_facts(function, graph),
            assumptions,
        );
        let boundaries =
            collect_source_boundary_facts(function, graph, &call_sites, machine_context);
        let structured = collect_structured_dataflow_facts(
            function,
            graph,
            StructuredCollectionInputs {
                objects: &objects,
                memory: &memory,
                predicates: &predicates,
                call_sites: &call_sites,
            },
        );
        let control_domains = collect_control_domain_facts(function, &predicates, &structured);
        let obligations = SemanticObligationInventory::collect(graph, &structured, &boundaries);
        let certificates = collect_prepared_function_certificates(
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

fn apply_assumptions_to_predicate_facts(
    mut predicates: PredicateFacts,
    assumptions: &AssumptionSet,
) -> PredicateFacts {
    for assumption in assumptions.iter() {
        let (predicate_id, block_addr, predecessor, truth) =
            match (&assumption.subject, &assumption.value) {
                (
                    AssumptionSubject::Predicate {
                        predicate,
                        block_addr,
                        predecessor,
                    },
                    AssumptionValue::Branch { truth },
                ) => (*predicate, *block_addr, *predecessor, *truth),
                _ => continue,
            };
        if !predicates.predicates.contains_key(&predicate_id) {
            continue;
        }
        let entry = predicates.block_assumptions.entry(block_addr).or_default();
        if entry.iter().any(|existing| {
            existing.predicate == predicate_id
                && existing.predecessor == predecessor.unwrap_or(existing.predecessor)
                && existing.truth == truth
        }) {
            continue;
        }
        entry.push(BlockAssumption {
            predecessor: predecessor.unwrap_or(block_addr),
            predicate: predicate_id,
            truth,
        });
    }
    predicates
}

fn collect_prepared_assumption_usage(
    graph: &SsaGraph,
    objects: &ObjectModel,
    predicates: &PredicateFacts,
    assumptions: &AssumptionSet,
) -> (Vec<PreparedAssumptionBinding>, AssumptionUsageReport) {
    let mut bindings = Vec::new();
    let mut usage = AssumptionUsageReport::default();

    for assumption in assumptions.iter() {
        match (&assumption.subject, &assumption.value) {
            (
                AssumptionSubject::Predicate {
                    predicate,
                    block_addr,
                    predecessor,
                },
                AssumptionValue::Branch { truth },
            ) => {
                let Some(fact) = predicates.predicates.get(predicate) else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                if fact.block_addr != *block_addr {
                    usage.mark_conflict(
                        assumption,
                        format!(
                            "predicate block mismatch (expected 0x{block_addr:x}, observed 0x{:x})",
                            fact.block_addr
                        ),
                    );
                    continue;
                }
                if let Some(pred) = predecessor {
                    let expected = if *truth {
                        fact.true_target
                    } else {
                        fact.false_target
                    };
                    if *pred != expected {
                        usage.mark_conflict(
                            assumption,
                            format!(
                                "branch predecessor 0x{pred:x} does not match selected edge 0x{expected:x}"
                            ),
                        );
                        continue;
                    }
                }
                usage.mark_applied(assumption);
                bindings.push(PreparedAssumptionBinding {
                    assumption: assumption.clone(),
                    binding: PreparedAssumptionBindingKind::Predicate {
                        predicate: *predicate,
                        block_addr: *block_addr,
                        predecessor: *predecessor,
                        truth: *truth,
                    },
                });
            }
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
                    objects.stack_objects.iter().find_map(|(root, object)| {
                        let matches_base = matches!(
                            (base.as_str(), root.base),
                            ("bp", StackAddressBase::FramePointer)
                                | ("frame", StackAddressBase::FramePointer)
                                | ("rbp", StackAddressBase::FramePointer)
                                | ("sp", StackAddressBase::StackPointer)
                                | ("stack", StackAddressBase::StackPointer)
                                | ("rsp", StackAddressBase::StackPointer)
                        );
                        (matches_base && root.offset == *offset).then_some((*root, *object))
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
    value_objects: BTreeMap<ValueId, ObjectId>,
    stack_objects: BTreeMap<StackAddressRoot, ObjectId>,
    parameter_objects: BTreeMap<usize, ObjectId>,
    global_objects: BTreeMap<GlobalObjectKey, ObjectId>,
    escaped_unknown: ObjectId,
    next_object_id: u32,
}

impl<'a> ObjectModelBuilder<'a> {
    fn new(facts: Option<&'a DecompilePrepFacts>, addresses: &'a AddressProvenanceFacts) -> Self {
        let escaped_unknown = ObjectId(0);
        let mut objects = BTreeMap::new();
        objects.insert(
            escaped_unknown,
            ObjectFact {
                id: escaped_unknown,
                kind: ObjectKind::EscapedUnknown,
            },
        );
        Self {
            facts,
            addresses,
            objects,
            value_objects: BTreeMap::new(),
            stack_objects: BTreeMap::new(),
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
                self.ensure_stack_object(root);
            }
            for var in facts.stack_address_roots.keys() {
                let _ = self.object_for_address_value(graph, var, "ram");
            }
        }
        let parameter_indices = self
            .addresses
            .parameter_expressions
            .values()
            .map(|expression| expression.parameter)
            .collect::<BTreeSet<_>>();
        for parameter in parameter_indices {
            self.ensure_parameter_object(parameter);
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
                        let _ = self.object_for_address_value(graph, addr, space);
                    }
                    _ => {}
                }
            }
        }

        ObjectModel {
            objects: self.objects,
            value_objects: self.value_objects,
            stack_objects: self.stack_objects,
            parameter_objects: self.parameter_objects,
            global_objects: self.global_objects,
            escaped_unknown: Some(self.escaped_unknown),
        }
    }

    fn object_for_address_value(
        &mut self,
        graph: &SsaGraph,
        value: &SSAVar,
        space: &str,
    ) -> ObjectId {
        let Some(value_id) = graph.value_id_for_var(value) else {
            return self.escaped_unknown;
        };
        if let Some(object) = self.value_objects.get(&value_id).copied() {
            return object;
        }

        if let Some(root) = resolve_stack_root(self.facts, value) {
            let object = self.ensure_stack_object(root);
            self.value_objects.insert(value_id, object);
            return object;
        }

        if let Some(expression) = self.addresses.parameter_expression(value_id) {
            let object = self.ensure_parameter_object(expression.parameter);
            self.value_objects.insert(value_id, object);
            return object;
        }

        if let Some(address) = resolve_const_value(self.facts, value) {
            let object = self.ensure_global_object(GlobalObjectKey {
                space: space.to_string(),
                address,
            });
            self.value_objects.insert(value_id, object);
            return object;
        }

        self.value_objects.insert(value_id, self.escaped_unknown);
        self.escaped_unknown
    }

    fn ensure_stack_object(&mut self, root: StackAddressRoot) -> ObjectId {
        if let Some(object) = self.stack_objects.get(&root).copied() {
            return object;
        }
        let id = self.alloc_object_id();
        self.objects.insert(
            id,
            ObjectFact {
                id,
                kind: ObjectKind::StackSlot {
                    base: root.base,
                    offset: root.offset,
                },
            },
        );
        self.stack_objects.insert(root, id);
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
                    space: key.space.clone(),
                    address: key.address,
                },
            },
        );
        self.global_objects.insert(key, id);
        id
    }

    fn ensure_parameter_object(&mut self, index: usize) -> ObjectId {
        if let Some(object) = self.parameter_objects.get(&index).copied() {
            return object;
        }
        let id = self.alloc_object_id();
        self.objects.insert(
            id,
            ObjectFact {
                id,
                kind: ObjectKind::Parameter { index },
            },
        );
        self.parameter_objects.insert(index, id);
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
) -> (ObjectModel, MemorySSAFacts) {
    let facts = function.decompile_prep_facts();
    let builder = ObjectModelBuilder::new(facts, addresses);
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
    let escaped_unknown = object_model.escaped_unknown_object().unwrap_or(ObjectId(0));

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
                        space,
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
                        space,
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
                        space,
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
                        space,
                        expected.size.max(replacement.size),
                    );
                    uses.push(location.clone());
                    defs.push(location);
                }
                SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                    if call_sites.by_inst.contains_key(&inst_id) {
                        let location = MemoryLocation {
                            object: escaped_unknown,
                            address: RelativeMemoryAddress::Unknown,
                            size: 0,
                        };
                        uses.push(location.clone());
                        defs.push(location);
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
    if left.object == right.object {
        return relative_memory_ranges_may_overlap(
            &left.address,
            left.size,
            &right.address,
            right.size,
        );
    }
    match (&left_object.kind, &right_object.kind) {
        (ObjectKind::EscapedUnknown, _) | (_, ObjectKind::EscapedUnknown) => true,
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
                address: left_base, ..
            },
            ObjectKind::Global {
                address: right_base,
                ..
            },
        ) => absolute_memory_ranges_may_overlap(
            i128::from(*left_base),
            &left.address,
            left.size,
            i128::from(*right_base),
            &right.address,
            right.size,
        ),
        (
            ObjectKind::StackSlot {
                base: left_base,
                offset: left_offset,
            }
            | ObjectKind::FrameObject {
                base: left_base,
                offset: left_offset,
            },
            ObjectKind::StackSlot {
                base: right_base,
                offset: right_offset,
            }
            | ObjectKind::FrameObject {
                base: right_base,
                offset: right_offset,
            },
        ) if left_base == right_base => absolute_memory_ranges_may_overlap(
            i128::from(*left_offset),
            &left.address,
            left.size,
            i128::from(*right_offset),
            &right.address,
            right.size,
        ),
        (
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. },
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. },
        ) => true,
        (ObjectKind::HeapAlloc { call_site: left }, ObjectKind::HeapAlloc { call_site: right }) => {
            left == right
        }
        _ => false,
    }
}

fn absolute_memory_ranges_may_overlap(
    left_base: i128,
    left: &RelativeMemoryAddress,
    left_size: u32,
    right_base: i128,
    right: &RelativeMemoryAddress,
    right_size: u32,
) -> bool {
    let (Some(left), Some(right)) = (left.exact_offset(), right.exact_offset()) else {
        return true;
    };
    ranges_overlap_i128(
        left_base + i128::from(left),
        left_size,
        right_base + i128::from(right),
        right_size,
    )
}

fn relative_memory_ranges_may_overlap(
    left: &RelativeMemoryAddress,
    left_size: u32,
    right: &RelativeMemoryAddress,
    right_size: u32,
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
    let constant = i128::from(left_offset) - i128::from(right_offset);
    let low = -i128::from(left_size.saturating_sub(1));
    let high = i128::from(right_size.saturating_sub(1));
    let modulus = difference
        .values()
        .map(|coefficient| coefficient.unsigned_abs())
        .fold(0u128, gcd_u128);
    if modulus == 0 {
        return constant >= low && constant <= high;
    }
    let Ok(modulus) = i128::try_from(modulus) else {
        return true;
    };
    let candidate = low + (constant.rem_euclid(modulus) - low).rem_euclid(modulus);
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

fn ranges_overlap_i128(left: i128, left_size: u32, right: i128, right_size: u32) -> bool {
    let left_end = left.saturating_add(i128::from(left_size.max(1)));
    let right_end = right.saturating_add(i128::from(right_size.max(1)));
    left < right_end && right < left_end
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
}

fn collect_structured_dataflow_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    inputs: StructuredCollectionInputs<'_>,
) -> StructuredDataflowFacts {
    let loops = collect_structured_loop_facts(function, graph, inputs.predicates);
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
                        reaching_abi_value_in_block(
                            function,
                            graph,
                            machine_context,
                            block_addr,
                            op_index,
                            argument.storage(),
                        )
                        .map(|value| CallBoundaryValueFact {
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
            if let Some(machine_context) = machine_context.filter(|context| {
                context.abi_model().is_available() && context.abi_model().is_coherent()
            }) {
                let return_slots = machine_context.abi_model().return_registers();
                let stack_pointer_storage = machine_context
                    .function_interface()
                    .and_then(|interface| interface.stack_pointer_storage());
                let return_address_storage = machine_context
                    .function_interface()
                    .and_then(|interface| interface.return_address_storage());
                match machine_context
                    .function_interface()
                    .map(|interface| interface.return_kind())
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
                match stack_pointer_storage {
                    Some(storage) => {
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
                    None => {}
                }
                match return_address_storage {
                    Some(storage) => {
                        return_address = exact_return_address_fact(graph, inst, storage);
                        complete &= return_address.is_some();
                    }
                    None => {}
                }
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
    let [value] = return_inst.inputs.as_slice() else {
        return None;
    };
    let value = graph.value(*value)?;
    (value.var.size == storage.size && value.canonical_storage == Some(storage)).then_some(
        SourceReturnAddressFact {
            storage,
            value: value.id,
        },
    )
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
        || carrier.size_bits() % 8 != 0
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
            ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset } => {
                Some((
                    *object,
                    StackSlotCertificate {
                        object: *object,
                        base,
                        offset,
                        size: None,
                    },
                ))
            }
            ObjectKind::Global { .. }
            | ObjectKind::Parameter { .. }
            | ObjectKind::HeapAlloc { .. }
            | ObjectKind::EscapedUnknown => None,
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
        collect_call_result_certificates(function, graph, objects, call_sites, structured);
    let stack_reloads =
        collect_stack_reload_source_certificates(function, graph, objects, memory, structured);
    let (returns, returns_by_inst) = collect_return_value_certificates(
        function,
        graph,
        predicates,
        &call_results,
        &stack_reloads,
    );

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
    function: &SSAFunction,
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    call_results: &BTreeMap<ValueId, CallResultCertificate>,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
) -> (Vec<ReturnValueCertificate>, BTreeMap<InstId, usize>) {
    let mut returns = Vec::new();
    let mut returns_by_inst = BTreeMap::new();
    let mut return_blocks = BTreeSet::new();

    for block in function.blocks() {
        let cfg_return = function
            .cfg()
            .get_block(block.addr)
            .is_some_and(|cfg_block| matches!(cfg_block.terminator, BlockTerminator::Return));
        if cfg_return
            || block
                .ops
                .iter()
                .any(|op| matches!(op, SSAOp::Return { .. }))
        {
            return_blocks.insert(block.addr);
        }
    }

    let mut return_context_blocks = return_blocks.clone();
    for block in function.blocks() {
        if function
            .successors(block.addr)
            .iter()
            .any(|succ| return_blocks.contains(succ))
        {
            return_context_blocks.insert(block.addr);
        }
    }

    let reaching_control_returns = collect_reaching_control_return_values(
        function,
        graph,
        predicates,
        call_results,
        stack_reloads,
    );

    for block in function.blocks() {
        let mut last_return_value_write = None;
        let mut has_explicit_return = false;
        for (op_idx, op) in block.ops.iter().enumerate() {
            if let SSAOp::Return { target } = op {
                has_explicit_return = true;
                if is_return_value_register(target) {
                    push_return_value_certificate(
                        graph,
                        &mut returns,
                        &mut returns_by_inst,
                        block.addr,
                        op_idx,
                        target,
                    );
                } else if is_control_return_target(target) {
                    if let Some((_, value)) = last_return_value_write {
                        push_return_value_certificate(
                            graph,
                            &mut returns,
                            &mut returns_by_inst,
                            block.addr,
                            op_idx,
                            value,
                        );
                    } else if let Some(value) =
                        reaching_control_returns.get(&(block.addr, op_idx)).copied()
                    {
                        push_return_value_certificate_for_value(
                            graph,
                            &mut returns,
                            &mut returns_by_inst,
                            block.addr,
                            op_idx,
                            value,
                        );
                    } else if let Some(return_phi) = unique_return_value_phi_for_block(block) {
                        push_return_value_certificate(
                            graph,
                            &mut returns,
                            &mut returns_by_inst,
                            block.addr,
                            op_idx,
                            return_phi,
                        );
                    }
                } else {
                    push_return_value_certificate(
                        graph,
                        &mut returns,
                        &mut returns_by_inst,
                        block.addr,
                        op_idx,
                        target,
                    );
                }
                continue;
            }

            if return_context_blocks.contains(&block.addr)
                && let Some(dst) = op.dst()
                && is_return_value_register(dst)
            {
                let preserve_wider_call_alias = matches!(op, SSAOp::CallDefine { .. })
                    && last_return_value_write.is_some_and(|(_, current)| {
                        synthetic_call_results_share_site(graph, call_results, current, dst)
                            && current.size > dst.size
                    });
                if !preserve_wider_call_alias {
                    last_return_value_write = Some((op_idx, dst));
                }
            }
        }

        if !has_explicit_return
            && return_blocks.contains(&block.addr)
            && let Some((op_idx, dst)) = last_return_value_write
        {
            push_return_value_certificate(
                graph,
                &mut returns,
                &mut returns_by_inst,
                block.addr,
                op_idx,
                dst,
            );
        }
    }

    (returns, returns_by_inst)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReachingReturnValue {
    value: ValueId,
    identity: ReturnSemanticIdentity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ReturnSemanticIdentity {
    CallResult(CallSiteId),
    StackSlot(ObjectId, i64),
    Value(ValueId),
    Const(u64),
}

fn collect_reaching_control_return_values(
    function: &SSAFunction,
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    call_results: &BTreeMap<ValueId, CallResultCertificate>,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
) -> BTreeMap<(u64, usize), ValueId> {
    let mut in_states = BTreeMap::<u64, Option<ReachingReturnValue>>::new();
    let mut out_states = BTreeMap::<u64, Option<ReachingReturnValue>>::new();
    let mut returns_by_op = BTreeMap::new();
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
        let input = merge_reaching_return_predecessors(
            function,
            graph,
            predicates,
            call_results,
            stack_reloads,
            &out_states,
            block_addr,
        );
        if in_states.get(&block_addr) != Some(&input) {
            in_states.insert(block_addr, input);
        }
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        let (output, block_returns) =
            process_reaching_return_block(graph, call_results, stack_reloads, block, input);
        for (site, value) in block_returns {
            returns_by_op.insert(site, value);
        }
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

    returns_by_op
}

fn merge_reaching_return_predecessors(
    function: &SSAFunction,
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    call_results: &BTreeMap<ValueId, CallResultCertificate>,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
    out_states: &BTreeMap<u64, Option<ReachingReturnValue>>,
    block_addr: u64,
) -> Option<ReachingReturnValue> {
    let preds = function.predecessors(block_addr);
    let (first, rest) = preds.split_first()?;
    let first_state = out_states.get(first).copied().flatten()?;
    let mut common = return_identity_candidates_for_block(
        *first,
        first_state,
        graph,
        predicates,
        call_results,
        stack_reloads,
    );
    let mut all_states = vec![first_state];
    for pred in rest {
        if let Some(pred_state) = out_states.get(pred).copied().flatten() {
            let pred_candidates = return_identity_candidates_for_block(
                *pred,
                pred_state,
                graph,
                predicates,
                call_results,
                stack_reloads,
            );
            common.retain(|identity| pred_candidates.contains(identity));
            all_states.push(pred_state);
        }
    }
    if !common.is_empty() {
        let identity = common
            .iter()
            .find(|identity| !matches!(identity, ReturnSemanticIdentity::Const(_)))
            .copied()
            .or_else(|| common.iter().next().copied())?;
        let value = preds
            .iter()
            .filter_map(|pred| out_states.get(pred).copied().flatten())
            .find(|state| state.identity == identity)
            .map(|state| state.value)
            .unwrap_or(first_state.value);
        return Some(ReachingReturnValue { value, identity });
    }

    let non_const_states: Vec<_> = all_states
        .iter()
        .filter(|state| !matches!(state.identity, ReturnSemanticIdentity::Const(_)))
        .copied()
        .collect();
    if non_const_states.len() == 1 {
        return Some(non_const_states[0]);
    }

    None
}

fn process_reaching_return_block(
    graph: &SsaGraph,
    call_results: &BTreeMap<ValueId, CallResultCertificate>,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
    block: &crate::function::SSABlock,
    mut state: Option<ReachingReturnValue>,
) -> (Option<ReachingReturnValue>, BTreeMap<(u64, usize), ValueId>) {
    let mut returns_by_op = BTreeMap::new();
    let return_phis = block
        .phis
        .iter()
        .filter(|phi| is_return_value_register(&phi.dst))
        .filter_map(|phi| {
            reaching_return_value_for_var(graph, call_results, stack_reloads, &phi.dst)
        })
        .collect::<Vec<_>>();
    match return_phis.as_slice() {
        [return_phi] if state.is_none() => state = Some(*return_phi),
        [] | [_] => {}
        _ => state = None,
    }
    for (op_idx, op) in block.ops.iter().enumerate() {
        if let SSAOp::Return { target } = op
            && is_control_return_target(target)
            && let Some(state) = state
        {
            returns_by_op.insert((block.addr, op_idx), state.value);
        }
        if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
            state = None;
        }
        if let Some(dst) = op.dst()
            && is_return_value_register(dst)
        {
            let candidate = reaching_return_value_for_var(graph, call_results, stack_reloads, dst);
            let preserve_wider_call_alias = matches!(op, SSAOp::CallDefine { .. })
                && state.is_some_and(|current| {
                    candidate.is_some_and(|candidate| {
                        current.identity == candidate.identity
                            && graph
                                .value(current.value)
                                .zip(graph.value(candidate.value))
                                .is_some_and(|(current, candidate)| {
                                    current.var.size > candidate.var.size
                                })
                    })
                });
            if !preserve_wider_call_alias {
                state = candidate;
            }
        }
    }
    (state, returns_by_op)
}

fn synthetic_call_results_share_site(
    graph: &SsaGraph,
    call_results: &BTreeMap<ValueId, CallResultCertificate>,
    lhs: &SSAVar,
    rhs: &SSAVar,
) -> bool {
    graph
        .value_id_for_var(lhs)
        .and_then(|value| call_results.get(&value))
        .zip(
            graph
                .value_id_for_var(rhs)
                .and_then(|value| call_results.get(&value)),
        )
        .is_some_and(|(lhs, rhs)| lhs.call_site == rhs.call_site)
}

fn reaching_return_value_for_var(
    graph: &SsaGraph,
    call_results: &BTreeMap<ValueId, CallResultCertificate>,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
    var: &SSAVar,
) -> Option<ReachingReturnValue> {
    let value = graph.value_id_for_var(var)?;
    Some(ReachingReturnValue {
        value,
        identity: return_semantic_identity_for_value(graph, call_results, stack_reloads, value),
    })
}

fn return_identity_candidates_for_block(
    block_addr: u64,
    state: ReachingReturnValue,
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    call_results: &BTreeMap<ValueId, CallResultCertificate>,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
) -> BTreeSet<ReturnSemanticIdentity> {
    let mut candidates = BTreeSet::from([state.identity]);
    let Some(assumptions) = predicates.block_assumptions.get(&block_addr) else {
        return candidates;
    };

    let mut changed = true;
    while changed {
        changed = false;
        for assumption in assumptions {
            let Some(predicate) = predicates.predicates.get(&assumption.predicate) else {
                continue;
            };
            let Some(compare) = &predicate.comparison else {
                continue;
            };
            if !assumption_proves_equality(compare.kind, assumption.truth) {
                continue;
            }
            let lhs =
                return_semantic_identity_for_value(graph, call_results, stack_reloads, compare.lhs);
            let rhs =
                return_semantic_identity_for_value(graph, call_results, stack_reloads, compare.rhs);
            if candidates.contains(&lhs) && candidates.insert(rhs) {
                changed = true;
            }
            if candidates.contains(&rhs) && candidates.insert(lhs) {
                changed = true;
            }
        }
    }

    candidates
}

fn assumption_proves_equality(kind: CompareKind, truth: bool) -> bool {
    matches!(
        (kind, truth),
        (CompareKind::Equal, true) | (CompareKind::NotEqual, false)
    )
}

fn return_semantic_identity_for_value(
    graph: &SsaGraph,
    call_results: &BTreeMap<ValueId, CallResultCertificate>,
    stack_reloads: &BTreeMap<ValueId, StackReloadSourceCertificate>,
    value: ValueId,
) -> ReturnSemanticIdentity {
    if let Some(call_result) = call_results.get(&value) {
        if let Some(ValueOwner::StackSlot { object, offset }) = call_result.owner {
            return ReturnSemanticIdentity::StackSlot(object, offset);
        }
        return ReturnSemanticIdentity::CallResult(call_result.call_site);
    }
    if let Some(reload) = stack_reloads.get(&value) {
        return ReturnSemanticIdentity::StackSlot(reload.object, reload.offset);
    }
    let canonical = canonical_graph_value_root(graph, value);
    if let Some(var) = graph.value(canonical).map(|value| &value.var)
        && let Some(literal) = const_value(var)
    {
        return ReturnSemanticIdentity::Const(literal);
    }
    ReturnSemanticIdentity::Value(canonical)
}

fn canonical_graph_value_root(graph: &SsaGraph, value: ValueId) -> ValueId {
    let mut current = value;
    for _ in 0..32 {
        let Some(def_inst) = graph.def_inst(current) else {
            break;
        };
        let Some(inst) = graph.inst(def_inst) else {
            break;
        };
        let next = match &inst.payload {
            InstPayload::Phi { .. } => {
                let Some(first) = inst.inputs.first().copied() else {
                    break;
                };
                if inst.inputs.iter().all(|input| *input == first) {
                    first
                } else {
                    break;
                }
            }
            InstPayload::Op(SSAOp::Copy { .. }) => {
                let Some(first) = inst.inputs.first().copied() else {
                    break;
                };
                first
            }
            _ => break,
        };
        if next == current {
            break;
        }
        current = next;
    }
    current
}

fn unique_return_value_phi_for_block(block: &crate::function::SSABlock) -> Option<&SSAVar> {
    let mut matches = block
        .phis
        .iter()
        .filter(|phi| is_return_value_register(&phi.dst))
        .map(|phi| &phi.dst);
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
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

    for access in structured
        .memory_accesses
        .values()
        .filter(|access| !access.is_write)
    {
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
    for access in structured
        .memory_accesses
        .values()
        .filter(|access| access.is_write)
    {
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
        .filter(|def| def.location.object == access.object && def.location.size == access.width);
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
            use_fact.location.object == access.object && use_fact.location.size == access.width
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
                kill_return_register_flow_values(&mut state, graph);
                active_call = callsites_by_op.get(&(block.addr, op_index)).copied();
            }
            SSAOp::CallDefine { dst } => {
                let Some(call_site_id) = active_call else {
                    continue;
                };
                let Some(call_site) = call_sites.by_id.get(&call_site_id) else {
                    continue;
                };
                let Some(carrier) = return_carrier_for_value(dst) else {
                    continue;
                };
                let Some(value) = graph.value_id_for_var(dst) else {
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
            SSAOp::Store { val, .. } => {
                let value = graph.value_id_for_var(val);
                let stack_access = value
                    .and_then(|value| {
                        stack_memory_access_at(
                            structured,
                            objects,
                            block.addr,
                            op_index,
                            true,
                            Some(value),
                        )
                    })
                    .or_else(|| {
                        stack_memory_access_at(
                            structured, objects, block.addr, op_index, true, None,
                        )
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
            SSAOp::Load { dst, .. } => {
                let Some(dst_value) = graph.value_id_for_var(dst) else {
                    continue;
                };
                let Some((object, offset, access)) = stack_memory_access_at(
                    structured,
                    objects,
                    block.addr,
                    op_index,
                    false,
                    Some(dst_value),
                ) else {
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

fn kill_return_register_flow_values(state: &mut CallResultFlowState, graph: &SsaGraph) {
    state.tracked.retain(|value, _| {
        graph
            .value(*value)
            .is_none_or(|value| !is_return_value_register(&value.var))
    });
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

fn stack_memory_access_at(
    structured: &StructuredDataflowFacts,
    objects: &ObjectModel,
    block_addr: u64,
    op_index: usize,
    is_write: bool,
    value: Option<ValueId>,
) -> Option<(ObjectId, i64, StructuredAccessId)> {
    structured
        .memory_accesses
        .iter()
        .filter(|(_, access)| {
            access.block_addr == block_addr
                && access.op_index == op_index
                && access.is_write == is_write
                && value.is_none_or(|value| access.value == Some(value))
        })
        .filter_map(|(access_id, access)| {
            stack_object_offset(objects, access.object)
                .map(|offset| (access.object, offset, *access_id))
        })
        .next()
}

fn push_return_value_certificate(
    graph: &SsaGraph,
    returns: &mut Vec<ReturnValueCertificate>,
    returns_by_inst: &mut BTreeMap<InstId, usize>,
    block_addr: u64,
    op_idx: usize,
    value_var: &SSAVar,
) {
    let Some(at) = graph.inst_id_for_op_site(block_addr, op_idx) else {
        return;
    };
    if returns_by_inst.contains_key(&at) {
        return;
    }
    let Some(value) = graph.value_id_for_var(value_var) else {
        return;
    };
    returns_by_inst.insert(at, returns.len());
    returns.push(ReturnValueCertificate {
        at,
        block_addr,
        op_index: op_idx,
        value,
        width: value_var.size,
        carrier: return_carrier_for_value(value_var),
    });
}

fn push_return_value_certificate_for_value(
    graph: &SsaGraph,
    returns: &mut Vec<ReturnValueCertificate>,
    returns_by_inst: &mut BTreeMap<InstId, usize>,
    block_addr: u64,
    op_idx: usize,
    value: ValueId,
) {
    let Some(at) = graph.inst_id_for_op_site(block_addr, op_idx) else {
        return;
    };
    if returns_by_inst.contains_key(&at) {
        return;
    }
    let Some(value_var) = graph.value(value).map(|value| &value.var) else {
        return;
    };
    returns_by_inst.insert(at, returns.len());
    returns.push(ReturnValueCertificate {
        at,
        block_addr,
        op_index: op_idx,
        value,
        width: value_var.size,
        carrier: return_carrier_for_value(value_var),
    });
}

fn return_carrier_for_value(value: &SSAVar) -> Option<ReturnCarrier> {
    if is_return_value_register(value) {
        return Some(ReturnCarrier::Register {
            name: value.name.clone(),
        });
    }
    None
}

fn is_return_value_register(value: &SSAVar) -> bool {
    if !value.is_register() {
        return false;
    }
    let name = value
        .name
        .trim()
        .trim_start_matches('$')
        .to_ascii_lowercase();
    matches!(
        name.as_str(),
        "rax" | "eax" | "ax" | "al" | "xmm0" | "st0" | "x0" | "w0" | "r0" | "v0" | "a0" | "r3"
    )
}

fn is_control_return_target(value: &SSAVar) -> bool {
    if !value.is_register() {
        return false;
    }
    let name = value
        .name
        .trim()
        .trim_start_matches('$')
        .to_ascii_lowercase();
    matches!(name.as_str(), "pc" | "lr" | "ra" | "x30" | "rip" | "eip")
}

fn collect_structured_loop_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    predicates: &PredicateFacts,
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
        let carriers = loop_carrier_facts(function, graph, id, header, &latches);
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
) -> Vec<LoopCarrierFact> {
    let Some(header_block) = function.get_block(header) else {
        return Vec::new();
    };
    let mut carriers = header_block
        .phis
        .iter()
        .filter_map(|phi| {
            let phi_value = graph.value_id_for_var(&phi.dst)?;
            // Pruned SSA is not guaranteed at this seam. A loop-local output
            // can induce a syntactic header phi whose value is never read;
            // such a dead merge carries no live state and must not acquire a
            // preservation obligation.
            if graph.use_sites(phi_value).is_empty() {
                return None;
            }
            let mut entries = Vec::new();
            let mut updates = Vec::new();
            for (predecessor, source) in &phi.sources {
                let edge = LoopCarrierEdgeValue {
                    predecessor: *predecessor,
                    value: graph.value_id_for_var(source)?,
                };
                if latches.contains(predecessor) {
                    updates.push(LoopCarrierUpdateFact {
                        predecessor: edge.predecessor,
                        value: edge.value,
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
            })
        })
        .collect::<Vec<_>>();

    // A post-loop phi such as `result = phi(init, update)` denotes the same
    // mutable carrier after structured control flow. Discover these aliases by
    // exact ValueId membership, never by storage names.
    let mut changed = true;
    while changed {
        changed = false;
        for block in function.blocks() {
            if block.addr == header {
                continue;
            }
            for phi in &block.phis {
                let Some(output) = graph.value_id_for_var(&phi.dst) else {
                    continue;
                };
                if carriers
                    .iter()
                    .any(|carrier| carrier.identity_values.contains(&output))
                {
                    continue;
                }
                let inputs = phi
                    .sources
                    .iter()
                    .filter_map(|(_, source)| graph.value_id_for_var(source))
                    .collect::<BTreeSet<_>>();
                if inputs.len() != phi.sources.len() || inputs.is_empty() {
                    continue;
                }
                let mut matches = carriers.iter_mut().filter(|carrier| {
                    let state_values = carrier
                        .identity_values
                        .iter()
                        .copied()
                        .chain(carrier.entries.iter().map(|edge| edge.value))
                        .chain(carrier.updates.iter().flat_map(|update| {
                            std::iter::once(update.value)
                                .chain(update.identity_values.iter().copied())
                        }))
                        .collect::<BTreeSet<_>>();
                    inputs.iter().all(|input| state_values.contains(input))
                        && inputs.iter().any(|input| {
                            carrier.identity_values.contains(input)
                                || carrier.updates.iter().any(|update| {
                                    update.value == *input || update.identity_values.contains(input)
                                })
                        })
                });
                let Some(carrier) = matches.next() else {
                    continue;
                };
                if matches.next().is_none() && carrier.identity_values.insert(output) {
                    for (predecessor, source) in &phi.sources {
                        let Some(value) = graph.value_id_for_var(source) else {
                            continue;
                        };
                        if carrier.entries.iter().any(|entry| entry.value == value)
                            && function.dominates(*predecessor, header)
                        {
                            carrier.dominating_initializers.push(LoopCarrierEdgeValue {
                                predecessor: *predecessor,
                                value,
                            });
                        }
                    }
                    changed = true;
                }
            }
        }
    }

    for carrier in &mut carriers {
        carrier.dominating_initializers.sort_unstable();
        carrier.dominating_initializers.dedup();
    }
    carriers.sort_by_key(|carrier| carrier.phi);
    carriers
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
                SSAOp::Load { dst, addr, .. }
                | SSAOp::LoadLinked { dst, addr, .. }
                | SSAOp::LoadGuarded { dst, addr, .. } => {
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
                            graph.value_id_for_var(dst),
                            false,
                            dst.size,
                        );
                    }
                }
                SSAOp::Store { addr, val, .. } | SSAOp::StoreGuarded { addr, val, .. } => {
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
                            graph.value_id_for_var(val),
                            true,
                            val.size,
                        );
                    }
                }
                SSAOp::StoreConditional { addr, val, .. } => {
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
        .filter(|location| location.size == width)
        .collect::<Vec<_>>();
    let provenance_complete = annotations.len() == 1 && matching.len() == 1;
    let object = matching
        .first()
        .map(|location| location.object)
        .or_else(|| objects.escaped_unknown_object())
        .unwrap_or(ObjectId(0));
    insert_structured_memory_access(
        access_facts,
        inst,
        ordinal,
        block_addr,
        op_index,
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
        let SSAOp::Store { val, .. } = op else {
            continue;
        };
        let Some(value) = graph.value_id_for_var(val) else {
            continue;
        };

        for (access_id, access) in structured.memory_accesses.iter().filter(|(_, access)| {
            access.block_addr == block_addr && access.op_index == producer_idx && access.is_write
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
            base: StackAddressBase::StackPointer,
            offset,
        }
        | ObjectKind::FrameObject {
            base: StackAddressBase::StackPointer,
            offset,
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
        ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset } => {
            Some((base, offset))
        }
        _ => None,
    }
}

fn call_argument_value_for_op(op: &SSAOp, graph: &SsaGraph) -> Option<(usize, ValueId, String)> {
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
    space: &str,
    size: u32,
) -> MemoryLocation {
    let parameter_expression = graph
        .value_id_for_var(addr)
        .and_then(|value| addresses.parameter_expression(value));
    let object = object_model
        .object_for_var(graph, addr)
        .or_else(|| {
            resolve_stack_root(prep_facts, addr)
                .and_then(|root| object_model.stack_objects.get(&root).copied())
        })
        .or_else(|| {
            resolve_const_value(prep_facts, addr).and_then(|address| {
                object_model
                    .global_objects
                    .get(&GlobalObjectKey {
                        space: space.to_string(),
                        address,
                    })
                    .copied()
            })
        })
        .or_else(|| object_model.escaped_unknown_object())
        .unwrap_or(ObjectId(0));
    MemoryLocation {
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
    use std::collections::BTreeMap;

    use super::{
        ControlGuard, MemoryDefFact, MemoryLocation, MemorySSAFacts, MemoryUseFact, MemoryVersion,
        ObjectId, ObjectModel, RelativeMemoryAddress, StructuredAccessId,
    };
    use crate::{
        CanonicalStorageId, CanonicalStorageSpace, InstId, SSAVar, SemanticObligationKind,
        SourceAbiParameterSpec, SourceFunctionInterface, SourceFunctionReturn, SsaArtifact,
        ValueId,
    };
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn test_reg(offset: u64) -> Varnode {
        Varnode::new(SpaceId::Register, offset, 8)
    }

    fn test_const(value: u64) -> Varnode {
        Varnode::constant(value, 8)
    }

    fn raw_memory_access(
        locations: Vec<MemoryLocation>,
        is_write: bool,
        width: u32,
    ) -> super::StructuredMemoryAccessFact {
        let inst = InstId(0);
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
            &ObjectModel::default(),
            inst,
            &mut ordinal,
            0x1000,
            0,
            ValueId(0),
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

    fn return_boundary_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("return-boundary-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        arch.add_register(RegisterDef::new("cond", 24, 1));
        arch.add_register(RegisterDef::new("sp", 32, 8));
        arch.add_register(RegisterDef::sub("sp_low", 32, 4, "sp"));
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

        for target in [Varnode::register(0, 8), Varnode::constant(0, 8)] {
            let mut corrupt = R2ILBlock::new(0x6160, 4);
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
