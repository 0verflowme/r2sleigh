//! Source-driven certification kernel.
//!
//! `r2ssa` owns the exhaustive source obligation inventory. This crate owns the
//! only operation that can close that inventory: assigning exactly one proven
//! final disposition to every obligation. Rendered text, names, statement
//! counts, and AST positions are intentionally absent from this API.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use r2ssa::{
    AssumptionSet, BlockTerminator, CallBoundarySlot, CallSiteId, CanonicalInstructionId,
    CanonicalInstructionSite, CanonicalStorageId, CanonicalStorageSpace, FunctionPrepareMode,
    GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION, InstId, InstPayload, LoopId,
    MACHINE_CONTEXT_SCHEMA_VERSION, MachineAddressSpace, MachineBitVector, MachineBuildError,
    MachineEntity, MachineExprId, MachineExprKind, MachineMemoryEndianness, MachineMemoryModel,
    MachineProjection, MachineType, MachineValueUse, ObjectId, ObjectKind, OwnedFunctionSnapshot,
    PredicateId, RelativeMemoryAddress, SEMANTIC_OBLIGATION_SCHEMA_VERSION,
    SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION, SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION, SSAOp,
    SSAVar, SemanticInstructionState, SemanticObligationComponent, SemanticObligationId,
    SemanticObligationInventory, SemanticObligationKind, SemanticSourceSite, SourceCallResult,
    SourceCallSiteIdentity, SourceCarrierKind, SourceFunctionInterface, SourceFunctionReturn,
    SourceLogicalValue, SourceMachineContext, SourceReturnBoundaryFact,
    SourceReturnRegisterCompositionFact, SourceReturnRegisterDefinitionFact,
    SourceReturnStackPointerFact, SourceStackGrowth, SsaArtifact, SsaArtifactAuthority,
    StackAddressBase, StackAddressRoot, StructuredAccessId, StructuredLoopKind, TrustedSsaArtifact,
    ValueId,
};
use serde::{Deserialize, Serialize};

#[cfg(test)]
use r2ssa::SourceStackAllocationContract;

mod aggregate_member;
mod private_frame_conditional_join;
mod private_frame_value_flow;

pub use aggregate_member::{
    CERTIFIED_AGGREGATE_MEMBER_ACCESS_CONTRACT_VERSION, CertifiedAggregateElementIndex,
    CertifiedAggregateMemberAccess, CertifiedAggregateMemberAccessSemantics,
    CertifiedAggregateStructuredAccess, CertifiedNaturalScalarAggregateLayout,
};
pub use private_frame_conditional_join::{
    CertifiedInertPrivateFrameJoinPhi, CertifiedPrivateFrameConditionalArm,
    CertifiedPrivateFrameConditionalJoin, CertifiedPrivateFrameJoinTransfer,
    CertifiedPrivateFrameTransparentBranch, certify_private_frame_conditional_join_region,
};
pub use private_frame_value_flow::{
    CertifiedPrivateFrameLoad, CertifiedPrivateFramePhi, CertifiedPrivateFramePhiInput,
    CertifiedPrivateFrameStore, CertifiedPrivateFrameValueFlow,
    CertifiedPrivateFrameVersionDefinition,
};

pub const CERTIFICATION_SCHEMA_VERSION: u32 = 36;

/// Unforgeable run-local identity for one proof authority domain.
///
/// Artifact-bound proofs retain the identity created with the immutable SSA
/// artifact, so independently certifying that same artifact composes safely.
/// Standalone certification owners receive a private local identity. Rebuilding
/// identical source bytes still creates a distinct artifact identity.
#[derive(Clone)]
struct CertifiedAuthoritySeal {
    artifact: Option<SsaArtifactAuthority>,
    source_snapshot: Option<OwnedFunctionSnapshot>,
    local: Arc<()>,
}

impl CertifiedAuthoritySeal {
    fn new() -> Self {
        Self {
            artifact: None,
            source_snapshot: None,
            local: Arc::new(()),
        }
    }

    fn for_artifact(trusted: &TrustedSsaArtifact) -> Self {
        Self {
            artifact: Some(trusted.artifact().authority().clone()),
            source_snapshot: Some(trusted.source().clone()),
            local: Arc::new(()),
        }
    }
}

impl std::fmt::Debug for CertifiedAuthoritySeal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("CertifiedAuthoritySeal(..)")
    }
}

impl PartialEq for CertifiedAuthoritySeal {
    fn eq(&self, other: &Self) -> bool {
        match (
            &self.artifact,
            &self.source_snapshot,
            &other.artifact,
            &other.source_snapshot,
        ) {
            (Some(left_artifact), Some(left_source), Some(right_artifact), Some(right_source)) => {
                left_artifact == right_artifact && left_source == right_source
            }
            (None, None, None, None) => Arc::ptr_eq(&self.local, &other.local),
            _ => false,
        }
    }
}

impl Eq for CertifiedAuthoritySeal {}

/// Stable preparation mode committed by a certification origin.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedPreparationMode {
    Generic,
    Raw,
    Decompile,
    Patterns,
    DataRefs,
    Symbolic,
}

impl From<FunctionPrepareMode> for CertifiedPreparationMode {
    fn from(mode: FunctionPrepareMode) -> Self {
        match mode {
            FunctionPrepareMode::Generic => Self::Generic,
            FunctionPrepareMode::Raw => Self::Raw,
            FunctionPrepareMode::Decompile => Self::Decompile,
            FunctionPrepareMode::Patterns => Self::Patterns,
            FunctionPrepareMode::DataRefs => Self::DataRefs,
            FunctionPrepareMode::Symbolic => Self::Symbolic,
        }
    }
}

/// Typed identity snapshot of every decompiler-preparation map retained by an
/// SSA artifact. `None` in [`CertifiedArtifactOrigin`] means that preparation
/// facts were not materialized for that artifact mode.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedDecompilerPreparationSnapshot {
    canonical_value_roots: Box<[(SSAVar, SSAVar)]>,
    stack_address_roots: Box<[(SSAVar, StackAddressRoot)]>,
    entry_stack_address_roots: Box<[(SSAVar, StackAddressRoot)]>,
    formal_parameters: Box<[(SSAVar, usize)]>,
    formal_parameter_bases: Box<[(SSAVar, usize)]>,
}

impl CertifiedDecompilerPreparationSnapshot {
    pub const fn canonical_value_roots(&self) -> &[(SSAVar, SSAVar)] {
        &self.canonical_value_roots
    }

    pub const fn stack_address_roots(&self) -> &[(SSAVar, StackAddressRoot)] {
        &self.stack_address_roots
    }

    pub const fn entry_stack_address_roots(&self) -> &[(SSAVar, StackAddressRoot)] {
        &self.entry_stack_address_roots
    }

    pub const fn formal_parameters(&self) -> &[(SSAVar, usize)] {
        &self.formal_parameters
    }

    pub const fn formal_parameter_bases(&self) -> &[(SSAVar, usize)] {
        &self.formal_parameter_bases
    }
}

/// Exact immutable source revision shared by certificates derived from one
/// prepared SSA artifact.
///
/// The graph snapshot is a canonical serialization of the ordered graph
/// payload rather than a probabilistic hash. Consumers compare this sealed
/// value directly before composing artifact-local handles from child proofs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedArtifactOrigin {
    schema_version: u32,
    lift_provenance_schema_version: u32,
    /// Stable diagnostic binding only. Runtime authority remains opaque and
    /// cannot be reconstructed from this hash.
    lift_manifest_hash: u64,
    /// Runtime proof authority. Serialized origin fields are diagnostics and
    /// replay context only; they cannot be deserialized into permission.
    #[serde(skip_serializing)]
    authority: CertifiedAuthoritySeal,
    graph_snapshot: Box<[u8]>,
    prepare_mode: CertifiedPreparationMode,
    decompile_preparation: Option<CertifiedDecompilerPreparationSnapshot>,
    /// Input order is retained intentionally as part of exact replay context.
    assumptions: AssumptionSet,
    machine_context: CertifiedMachineContext,
    source: SemanticObligationInventory,
    topology: CertifiedSourceTopology,
}

impl CertifiedArtifactOrigin {
    fn authority(&self) -> &CertifiedAuthoritySeal {
        &self.authority
    }

    pub(crate) fn is_valid(&self) -> bool {
        self.schema_version == CERTIFICATION_SCHEMA_VERSION
            && self.lift_provenance_schema_version == GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION
            && !self.graph_snapshot.is_empty()
            && self.source.schema_version() == SEMANTIC_OBLIGATION_SCHEMA_VERSION
            && self.topology.schema_version() == CERTIFICATION_SCHEMA_VERSION
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn lift_provenance_schema_version(&self) -> u32 {
        self.lift_provenance_schema_version
    }

    pub const fn lift_manifest_hash(&self) -> u64 {
        self.lift_manifest_hash
    }

    pub const fn machine_context(&self) -> &CertifiedMachineContext {
        &self.machine_context
    }

    pub const fn prepare_mode(&self) -> CertifiedPreparationMode {
        self.prepare_mode
    }

    pub const fn assumptions(&self) -> &AssumptionSet {
        &self.assumptions
    }

    /// Exact preparation maps used as artifact identity, not a semantic proof
    /// that any individual derived fact is valid.
    pub const fn decompile_preparation(&self) -> Option<&CertifiedDecompilerPreparationSnapshot> {
        self.decompile_preparation.as_ref()
    }

    pub const fn source(&self) -> &SemanticObligationInventory {
        &self.source
    }

    pub const fn topology(&self) -> &CertifiedSourceTopology {
        &self.topology
    }

    pub fn matches_retained_source(
        &self,
        source: &SemanticObligationInventory,
        topology: &CertifiedSourceTopology,
    ) -> bool {
        self.is_valid() && self.source == *source && self.topology == *topology
    }
}

/// Validated, immutable machine context retained by a certification owner.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedMachineContext {
    schema_version: u32,
    source: SourceMachineContext,
}

impl CertifiedMachineContext {
    fn from_artifact(artifact: &SsaArtifact) -> Result<Self, MachineBuildError> {
        let source = artifact.machine_context();
        if source.schema_version() != MACHINE_CONTEXT_SCHEMA_VERSION
            || source.memory_model().schema_version() != MACHINE_CONTEXT_SCHEMA_VERSION
            || source.abi_model().schema_version() != MACHINE_CONTEXT_SCHEMA_VERSION
        {
            return Err(MachineBuildError::MachineContextMismatch);
        }
        match source.function_interface() {
            Some(interface)
                if interface.schema_version() == SOURCE_FUNCTION_INTERFACE_SCHEMA_VERSION
                    && !interface.revision_identity().is_empty()
                    && !interface.calling_convention().trim().is_empty()
                    && source.abi_model().is_available()
                    && source.abi_model().is_coherent()
                    && source.abi_model().argument_registers().len()
                        == interface.parameters().len()
                    && source
                        .abi_model()
                        .argument_registers()
                        .iter()
                        .zip(interface.parameters())
                        .all(|(actual, expected)| {
                            actual.index() == expected.index()
                                && actual.storage() == expected.storage()
                        })
                    && match interface.return_kind() {
                        SourceFunctionReturn::Void => {
                            source.abi_model().return_registers().is_empty()
                        }
                        SourceFunctionReturn::Register { storage } => {
                            source.abi_model().return_registers().len() == 1
                                && source.abi_model().return_registers()[0].index() == 0
                                && source.abi_model().return_registers()[0].storage() == storage
                        }
                    } => {}
            None if !source.abi_model().is_available()
                && !source.abi_model().is_coherent()
                && source.abi_model().argument_registers().is_empty()
                && source.abi_model().return_registers().is_empty() => {}
            _ => return Err(MachineBuildError::MachineContextMismatch),
        }
        if !source.call_site_interfaces_are_coherent() {
            return Err(MachineBuildError::MachineContextMismatch);
        }
        for (call_site, identity) in source.raw_call_sites_by_id() {
            if artifact
                .call_sites()
                .by_id
                .get(call_site)
                .is_none_or(|fact| fact.raw_identity != Some(*identity))
            {
                return Err(MachineBuildError::MachineContextMismatch);
            }
        }
        for (identity, interface) in source.call_site_interfaces() {
            if interface.schema_version() != SOURCE_CALL_SITE_INTERFACE_SCHEMA_VERSION
                || interface.revision_identity().is_empty()
                || interface.identity() != *identity
                || interface.calling_convention().trim().is_empty()
                || !artifact
                    .call_sites()
                    .by_id
                    .values()
                    .any(|fact| fact.raw_identity == Some(*identity))
                || source.function_interface().is_some_and(|function| {
                    function.revision_identity() != interface.revision_identity()
                })
            {
                return Err(MachineBuildError::MachineContextMismatch);
            }
        }
        let graph = artifact.graph();
        let mut expected_sites = BTreeMap::new();
        for access in artifact.facts().structured.memory_accesses.values() {
            if expected_sites
                .insert((access.block_addr, access.op_index), access.space)
                .is_some_and(|prior| prior != access.space)
            {
                return Err(MachineBuildError::MachineContextMismatch);
            }
        }
        for ((block_addr, op_index), space) in source.memory_spaces_by_op() {
            let Some(instruction) = graph
                .inst_id_for_op_site(*block_addr, *op_index)
                .and_then(|inst| graph.inst(inst))
            else {
                return Err(MachineBuildError::MachineContextMismatch);
            };
            if !matches!(
                &instruction.payload,
                InstPayload::Op(op) if ssa_memory_space(op) == Some(*space)
            ) || expected_sites.get(&(*block_addr, *op_index)) != Some(space)
                || artifact
                    .function()
                    .get_block(*block_addr)
                    .and_then(|block| block.ops.get(*op_index))
                    .is_none_or(|source_op| {
                        !matches!(
                            &instruction.payload,
                            InstPayload::Op(graph_op) if graph_op == source_op
                        )
                    })
                || (source.memory_model().is_available()
                    && source.memory_model().space(*space).is_none())
            {
                return Err(MachineBuildError::MachineContextMismatch);
            }
        }
        if expected_sites
            .keys()
            .any(|(block_addr, op_index)| source.memory_space_at(*block_addr, *op_index).is_none())
        {
            return Err(MachineBuildError::MachineContextMismatch);
        }
        Ok(Self {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            source: source.clone(),
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn source(&self) -> &SourceMachineContext {
        &self.source
    }

    pub const fn memory_model(&self) -> &MachineMemoryModel {
        self.source.memory_model()
    }
}

fn ssa_memory_space(op: &SSAOp) -> Option<r2il::SpaceId> {
    match op {
        SSAOp::Load { space, .. }
        | SSAOp::Store { space, .. }
        | SSAOp::LoadLinked { space, .. }
        | SSAOp::StoreConditional { space, .. }
        | SSAOp::AtomicCAS { space, .. }
        | SSAOp::LoadGuarded { space, .. }
        | SSAOp::StoreGuarded { space, .. } => Some(*space),
        _ => None,
    }
}

/// Sealed producerless resource for one declared ABI parameter carrier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedAbiParameter {
    schema_version: u32,
    index: u32,
    abi_storage: CanonicalStorageId,
    graph_storage: CanonicalStorageId,
    logical_value: SourceLogicalValue,
    value: Option<MachineValueUse>,
}

impl CertifiedAbiParameter {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.abi_storage
    }

    pub const fn graph_storage(&self) -> CanonicalStorageId {
        self.graph_storage
    }

    pub const fn logical_value(&self) -> SourceLogicalValue {
        self.logical_value
    }

    /// Exact entry SSA carrier when the parameter is used by the graph.
    pub const fn value(&self) -> Option<&MachineValueUse> {
        self.value.as_ref()
    }

    fn validate_against_artifact(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        validate_schema(self.schema_version)
            .map_err(|_| MachineBuildError::MachineContextMismatch)?;
        let interface = artifact
            .machine_context()
            .function_interface()
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        let expected = interface
            .parameters()
            .iter()
            .zip(interface.parameter_logical_values())
            .find(|(parameter, _)| parameter.index() == self.index)
            .filter(|(parameter, logical)| {
                parameter.storage() == self.abi_storage
                    && **logical == self.logical_value
                    && projected_parameter_storage(parameter.storage(), **logical)
                        == Some(self.graph_storage)
            })
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        let source = artifact.facts().boundaries.parameters.get(&self.index);
        match (&self.value, source) {
            (None, None) => {}
            (Some(value), Some(source))
                if source.index == self.index
                    && source.abi_storage == expected.0.storage()
                    && source.graph_storage == self.graph_storage
                    && source.logical_value == self.logical_value
                    && value.binding().value() == source.value
                    && value.binding().width_bits()
                        == self.graph_storage.size.checked_mul(8).unwrap_or(0)
                    && value.producer().is_none()
                    && value.constant().is_none() => {}
            _ => return Err(MachineBuildError::MachineContextMismatch),
        }
        Ok(())
    }
}

fn projected_parameter_storage(
    abi_storage: CanonicalStorageId,
    logical: SourceLogicalValue,
) -> Option<CanonicalStorageId> {
    let abi_bits = u64::from(abi_storage.size).checked_mul(8)?;
    let carrier = logical.carrier();
    let size_bits = carrier.size_bits();
    if carrier.offset_bits() != 0 || size_bits == 0 || !size_bits.is_multiple_of(8) {
        return None;
    }
    match carrier.kind() {
        SourceCarrierKind::Full if size_bits == abi_bits => Some(abi_storage),
        SourceCarrierKind::LowBits if size_bits <= abi_bits => Some(CanonicalStorageId {
            size: u32::try_from(size_bits / 8).ok()?,
            ..abi_storage
        }),
        _ => None,
    }
}

fn exact_parameter_projection(
    abi_storage: CanonicalStorageId,
    graph_storage: CanonicalStorageId,
    logical_value: SourceLogicalValue,
) -> bool {
    projected_parameter_storage(abi_storage, logical_value) == Some(graph_storage)
}

fn interface_has_exact_parameter_projection(
    interface: &r2ssa::SourceFunctionInterface,
    index: u32,
    abi_storage: CanonicalStorageId,
    graph_storage: CanonicalStorageId,
    logical_value: SourceLogicalValue,
) -> bool {
    interface
        .parameters()
        .iter()
        .zip(interface.parameter_logical_values())
        .find(|(parameter, _)| parameter.index() == index)
        .is_some_and(|(parameter, logical)| {
            parameter.storage() == abi_storage
                && *logical == logical_value
                && exact_parameter_projection(abi_storage, graph_storage, logical_value)
        })
}

fn certified_abi_parameters(
    artifact: &SsaArtifact,
) -> Result<BTreeMap<u32, CertifiedAbiParameter>, MachineBuildError> {
    let Some(interface) = artifact.machine_context().function_interface() else {
        return Ok(BTreeMap::new());
    };
    let mut parameters = BTreeMap::new();
    for (parameter, logical_value) in interface
        .parameters()
        .iter()
        .zip(interface.parameter_logical_values())
    {
        let graph_storage = projected_parameter_storage(parameter.storage(), *logical_value)
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        let value = artifact
            .facts()
            .boundaries
            .parameters
            .get(&parameter.index())
            .map(|fact| MachineValueUse::from_artifact(artifact, fact.value))
            .transpose()?;
        let certified = CertifiedAbiParameter {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            index: parameter.index(),
            abi_storage: parameter.storage(),
            graph_storage,
            logical_value: *logical_value,
            value,
        };
        certified.validate_against_artifact(artifact)?;
        if parameters.insert(parameter.index(), certified).is_some() {
            return Err(MachineBuildError::MachineContextMismatch);
        }
    }
    Ok(parameters)
}

/// Sealed producerless resource for one exactly sized source-declared stack
/// slot. `object` is absent when the slot is unused by this graph; callers may
/// not infer an object or a size from address arithmetic alone.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedStackSlot {
    schema_version: u32,
    base: StackAddressBase,
    offset: i64,
    size_bytes: u32,
    object: Option<ObjectId>,
}

impl CertifiedStackSlot {
    pub const fn base(&self) -> StackAddressBase {
        self.base
    }

    pub const fn offset(&self) -> i64 {
        self.offset
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    /// Exact object-model identity when this slot is referenced by the graph.
    pub const fn object(&self) -> Option<ObjectId> {
        self.object
    }

    fn validate_against_artifact(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        validate_schema(self.schema_version)
            .map_err(|_| MachineBuildError::MachineContextMismatch)?;
        let interface = artifact
            .machine_context()
            .function_interface()
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        if !interface.stack_slots().iter().any(|slot| {
            slot.base() == self.base
                && slot.offset() == self.offset
                && slot.size_bytes() == self.size_bytes
        }) {
            return Err(MachineBuildError::MachineContextMismatch);
        }
        let matching_objects = artifact
            .facts()
            .certificates
            .stack_slots
            .values()
            .filter(|slot| slot.base == self.base && slot.offset == self.offset)
            .map(|slot| (slot.object, slot.space))
            .collect::<Vec<_>>();
        match (self.object, matching_objects.as_slice()) {
            (None, []) => {}
            (Some(actual), [(expected, r2il::SpaceId::Ram)]) if actual == *expected => {
                if !matches!(
                    artifact.objects().object(actual).map(|fact| &fact.kind),
                    Some(
                        ObjectKind::StackSlot { space, base, offset }
                            | ObjectKind::FrameObject { space, base, offset }
                    ) if *space == r2il::SpaceId::Ram
                        && *base == self.base
                        && *offset == self.offset
                ) {
                    return Err(MachineBuildError::MachineContextMismatch);
                }
                let locations = artifact
                    .facts()
                    .memory
                    .uses_by_inst
                    .values()
                    .flatten()
                    .map(|fact| &fact.location)
                    .chain(
                        artifact
                            .facts()
                            .memory
                            .defs_by_inst
                            .values()
                            .flatten()
                            .map(|fact| &fact.location),
                    )
                    .filter(|location| location.object == actual)
                    .collect::<Vec<_>>();
                if locations.is_empty()
                    || locations.iter().any(|location| {
                        let RelativeMemoryAddress::Exact(relative) = &location.address else {
                            return true;
                        };
                        location.size == 0
                            || *relative < 0
                            || u64::try_from(*relative)
                                .ok()
                                .and_then(|start| start.checked_add(u64::from(location.size)))
                                .is_none_or(|end| end > u64::from(self.size_bytes))
                    })
                {
                    return Err(MachineBuildError::MachineContextMismatch);
                }
            }
            _ => return Err(MachineBuildError::MachineContextMismatch),
        }
        Ok(())
    }
}

fn certified_stack_slots(
    artifact: &SsaArtifact,
) -> Result<BTreeMap<StackAddressRoot, CertifiedStackSlot>, MachineBuildError> {
    let Some(interface) = artifact.machine_context().function_interface() else {
        return Ok(BTreeMap::new());
    };
    let mut slots = BTreeMap::new();
    for source in interface.stack_slots() {
        let root = StackAddressRoot {
            base: source.base(),
            offset: source.offset(),
        };
        let matching_objects = artifact
            .facts()
            .certificates
            .stack_slots
            .values()
            .filter(|slot| slot.base == source.base() && slot.offset == source.offset())
            .map(|slot| (slot.object, slot.space))
            .collect::<Vec<_>>();
        let object = match matching_objects.as_slice() {
            [] => None,
            [(object, r2il::SpaceId::Ram)] => Some(*object),
            _ => return Err(MachineBuildError::MachineContextMismatch),
        };
        let certified = CertifiedStackSlot {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            base: source.base(),
            offset: source.offset(),
            size_bytes: source.size_bytes(),
            object,
        };
        certified.validate_against_artifact(artifact)?;
        if slots.insert(root, certified).is_some() {
            return Err(MachineBuildError::MachineContextMismatch);
        }
    }
    Ok(slots)
}

/// Stable description of how one source obligation was preserved or rejected.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum EffectDisposition {
    Rendered,
    AbsorbedIntoExpression {
        producer: CanonicalInstructionId,
    },
    AbsorbedIntoStatement {
        producer: CanonicalInstructionId,
    },
    /// Exact direct-call boundary and its ordered register arguments. This
    /// remains pending typed-call-region validation and is not final C
    /// authorization.
    AbsorbedIntoCall {
        producer: CanonicalInstructionId,
    },
    /// Exact ledger ownership by sealed terminal-control evidence. This remains
    /// pending typed-region validation and is not final C authorization.
    AbsorbedIntoControl {
        producer: CanonicalInstructionId,
    },
    /// Exact terminal return and its ordered returned-value obligations.
    AbsorbedIntoReturn {
        producer: CanonicalInstructionId,
    },
    Rewritten {
        pass: String,
    },
    Superseded {
        by: SemanticObligationId,
    },
    ProvenDead,
    Residualized {
        reason: String,
    },
    Refused {
        reason: String,
    },
}

impl EffectDisposition {
    const fn is_semantically_preserving(&self) -> bool {
        matches!(
            self,
            Self::Rendered
                | Self::AbsorbedIntoExpression { .. }
                | Self::AbsorbedIntoStatement { .. }
                | Self::AbsorbedIntoCall { .. }
                | Self::AbsorbedIntoControl { .. }
                | Self::AbsorbedIntoReturn { .. }
                | Self::Rewritten { .. }
                | Self::Superseded { .. }
                | Self::ProvenDead
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CertificationError {
    SchemaVersion { expected: u32, actual: u32 },
    IncompleteSourceInventory,
    EmptySourceSet,
    UnknownInstruction(CanonicalInstructionId),
    UnknownObligation(SemanticObligationId),
    ObligationNotMapped(SemanticObligationId),
    EmptyReason,
}

/// A semantic output entity anchored to a canonical producer.
///
/// Fields are private so a normal caller must validate it against a source
/// inventory. Deserialized values are validated again when entered in a
/// `CertifiedFunction`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedEntity {
    schema_version: u32,
    producer: CanonicalInstructionId,
    source_obligations: BTreeSet<SemanticObligationId>,
}

impl CertifiedEntity {
    // This constructor is test-only until a typed semantic-output validator
    // owns output provenance. Source IDs alone are not preservation evidence.
    #[cfg(test)]
    fn certify(
        source: &SemanticObligationInventory,
        producer: CanonicalInstructionId,
        source_obligations: impl IntoIterator<Item = SemanticObligationId>,
    ) -> Result<Self, CertificationError> {
        let entity = Self {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            producer,
            source_obligations: source_obligations.into_iter().collect(),
        };
        entity.validate(source)?;
        Ok(entity)
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.source_obligations
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_source(source)?;
        validate_schema(self.schema_version)?;
        if !source.instructions().contains_key(&self.producer) {
            return Err(CertificationError::UnknownInstruction(self.producer));
        }
        if self.source_obligations.is_empty() {
            return Err(CertificationError::EmptySourceSet);
        }
        for id in &self.source_obligations {
            if !source.obligations().contains_key(id) {
                return Err(CertificationError::UnknownObligation(*id));
            }
        }
        Ok(())
    }
}

/// A certified expression and its canonical producer dependencies.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedExpr {
    schema_version: u32,
    entity: CertifiedEntity,
    root: MachineExprId,
    inputs: BTreeSet<CanonicalInstructionId>,
}

impl CertifiedExpr {
    pub fn entity(&self) -> &CertifiedEntity {
        &self.entity
    }

    /// Exact machine-expression root validated for this certified entity.
    pub const fn root(&self) -> MachineExprId {
        self.root
    }

    pub fn inputs(&self) -> &BTreeSet<CanonicalInstructionId> {
        &self.inputs
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_source(source)?;
        validate_schema(self.schema_version)?;
        self.entity.validate(source)?;
        for input in &self.inputs {
            if !source.instructions().contains_key(input) {
                return Err(CertificationError::UnknownInstruction(*input));
            }
        }
        Ok(())
    }
}

/// Exact executable shape of one certified plain memory statement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedMemoryStatementKind {
    Read { result: MachineValueUse },
    Write { value: MachineValueUse },
}

/// Required execution policy for certified memory statements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedMemoryExecutionPolicy {
    /// Evaluate exactly once in certified source order. The generic rendering
    /// uses an address-space helper; a stronger exact typed-region certificate
    /// may instead project the same private access through a sealed C lvalue.
    /// An ordinary unproven C pointer dereference is never permitted evidence.
    ExactlyOnceInSourceOrder,
}

/// Sealed evidence for one plain source Load or Store.
///
/// Construction requires one complete structured access, an explicit coherent
/// machine-memory model, and no guarded, atomic, ordering, or unknown sibling
/// effect. The statement owns only its observable memory obligation. A load's
/// live result remains separately owned by its certified expression.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedMemoryStatement {
    schema_version: u32,
    producer: CanonicalInstructionId,
    access: StructuredAccessId,
    object: ObjectId,
    address: MachineValueUse,
    space: MachineAddressSpace,
    endianness: MachineMemoryEndianness,
    word_size_bytes: u32,
    width_bits: u32,
    execution: CertifiedMemoryExecutionPolicy,
    kind: CertifiedMemoryStatementKind,
    source_obligations: BTreeSet<SemanticObligationId>,
}

impl CertifiedMemoryStatement {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn access(&self) -> StructuredAccessId {
        self.access
    }

    pub const fn object(&self) -> ObjectId {
        self.object
    }

    pub const fn address(&self) -> &MachineValueUse {
        &self.address
    }

    pub const fn space(&self) -> MachineAddressSpace {
        self.space
    }

    pub const fn endianness(&self) -> MachineMemoryEndianness {
        self.endianness
    }

    pub const fn word_size_bytes(&self) -> u32 {
        self.word_size_bytes
    }

    pub const fn width_bits(&self) -> u32 {
        self.width_bits
    }

    pub const fn kind(&self) -> &CertifiedMemoryStatementKind {
        &self.kind
    }

    pub const fn execution(&self) -> CertifiedMemoryExecutionPolicy {
        self.execution
    }

    pub fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.source_obligations
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_source(source)?;
        validate_schema(self.schema_version)?;
        let mut obligations = self.source_obligations.iter().copied();
        let Some(obligation) = obligations.next() else {
            return Err(CertificationError::EmptySourceSet);
        };
        if obligations.next().is_some() {
            return Err(CertificationError::ObligationNotMapped(obligation));
        }
        let expected_kind = match self.kind {
            CertifiedMemoryStatementKind::Read { .. } => {
                SemanticObligationKind::ObservableMemoryRead
            }
            CertifiedMemoryStatementKind::Write { .. } => {
                SemanticObligationKind::ObservableMemoryWrite
            }
        };
        if self.width_bits == 0
            || self.word_size_bytes == 0
            || !matches!(
                self.endianness,
                MachineMemoryEndianness::Little | MachineMemoryEndianness::Big
            )
            || self.execution != CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrder
            || obligation.instruction != self.producer
            || obligation.kind != expected_kind
            || obligation.component
                != SemanticObligationComponent::MemoryAccess(self.access.ordinal)
        {
            return Err(CertificationError::ObligationNotMapped(obligation));
        }
        let source_obligation = source
            .obligations()
            .get(&obligation)
            .ok_or(CertificationError::UnknownObligation(obligation))?;
        let mut expected_inputs = vec![self.address.binding().value()];
        match &self.kind {
            CertifiedMemoryStatementKind::Read { result } => {
                if result.producer() != Some(self.producer)
                    || result.binding().width_bits() != self.width_bits
                {
                    return Err(CertificationError::ObligationNotMapped(obligation));
                }
            }
            CertifiedMemoryStatementKind::Write { value } => {
                if value.binding().width_bits() != self.width_bits {
                    return Err(CertificationError::ObligationNotMapped(obligation));
                }
                expected_inputs.push(value.binding().value());
            }
        }
        let address_type_matches = matches!(
            self.address.ty(),
            MachineType::Address { width_bits, space, .. }
                if *width_bits == self.address.binding().width_bits() && *space == self.space
        );
        if source_obligation.source.graph_inst() != Some(self.access.inst)
            || source_obligation.inputs != expected_inputs
            || self.address.memory_access() != Some(self.access)
            || !address_type_matches
        {
            return Err(CertificationError::ObligationNotMapped(obligation));
        }
        Ok(())
    }

    #[cfg(test)]
    fn validate_against_artifact(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let expected = try_certified_memory_statement(artifact, self.access.inst)?
            .ok_or(MachineBuildError::ObligationMismatch(self.access.inst))?;
        if expected == *self {
            Ok(())
        } else {
            Err(MachineBuildError::ObligationMismatch(self.access.inst))
        }
    }
}

/// One ordered register argument and the exact source obligation it owns.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedCallArgumentOrigin {
    Produced { producer: CanonicalInstructionId },
    Constant { value: MachineBitVector },
    AbiParameter { index: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedCallArgument {
    slot: CallBoundarySlot,
    value: MachineValueUse,
    origin: CertifiedCallArgumentOrigin,
    source_obligation: SemanticObligationId,
}

impl CertifiedCallArgument {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn value(&self) -> &MachineValueUse {
        &self.value
    }

    pub const fn origin(&self) -> &CertifiedCallArgumentOrigin {
        &self.origin
    }

    pub const fn source_obligation(&self) -> SemanticObligationId {
        self.source_obligation
    }
}

/// Sealed boundary evidence for the first admitted direct-call subset.
///
/// The call must be final in its block, direct, falling through to one existing
/// successor, nonvariadic, non-noreturn, explicitly void, and register-only.
/// This witness ends at the call and proves neither callee behavior nor
/// post-call register or memory state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedDirectCall {
    schema_version: u32,
    producer: CanonicalInstructionId,
    source_inst: r2ssa::InstId,
    call_site: CallSiteId,
    raw_identity: SourceCallSiteIdentity,
    interface_revision: Box<[u8]>,
    target: u64,
    fallthrough: u64,
    target_value: MachineValueUse,
    calling_convention: String,
    arguments: Box<[CertifiedCallArgument]>,
    call_obligation: SemanticObligationId,
}

impl CertifiedDirectCall {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn call_site(&self) -> CallSiteId {
        self.call_site
    }

    pub const fn raw_identity(&self) -> SourceCallSiteIdentity {
        self.raw_identity
    }

    pub const fn interface_revision(&self) -> &[u8] {
        &self.interface_revision
    }

    pub const fn target(&self) -> u64 {
        self.target
    }

    pub const fn fallthrough(&self) -> u64 {
        self.fallthrough
    }

    pub const fn target_value(&self) -> &MachineValueUse {
        &self.target_value
    }

    pub fn calling_convention(&self) -> &str {
        &self.calling_convention
    }

    pub const fn arguments(&self) -> &[CertifiedCallArgument] {
        &self.arguments
    }

    pub const fn call_obligation(&self) -> SemanticObligationId {
        self.call_obligation
    }

    pub fn source_obligations(&self) -> BTreeSet<SemanticObligationId> {
        std::iter::once(self.call_obligation)
            .chain(
                self.arguments
                    .iter()
                    .map(CertifiedCallArgument::source_obligation),
            )
            .collect()
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_source(source)?;
        validate_schema(self.schema_version)?;
        if self.interface_revision.is_empty()
            || self.calling_convention.trim().is_empty()
            || self.target == self.fallthrough
            || self.raw_identity.block_addr() != self.producer.block_addr
            || self.raw_identity.target().offset != self.target
            || self.call_obligation.instruction != self.producer
            || self.call_obligation.kind != SemanticObligationKind::Call
            || self.call_obligation.component != SemanticObligationComponent::Whole
            || self.source_obligations().len() != self.arguments.len().saturating_add(1)
        {
            return Err(CertificationError::ObligationNotMapped(
                self.call_obligation,
            ));
        }
        let call = source
            .obligations()
            .get(&self.call_obligation)
            .ok_or(CertificationError::UnknownObligation(self.call_obligation))?;
        if call.source.graph_inst() != Some(self.source_inst)
            || call.inputs != [self.target_value.binding().value()]
        {
            return Err(CertificationError::ObligationNotMapped(
                self.call_obligation,
            ));
        }
        for (position, argument) in self.arguments.iter().enumerate() {
            let CallBoundarySlot::Register { index, storage } = argument.slot else {
                return Err(CertificationError::ObligationNotMapped(
                    argument.source_obligation,
                ));
            };
            if u32::try_from(position) != Ok(index)
                || argument.source_obligation.instruction != self.producer
                || argument.source_obligation.kind != SemanticObligationKind::CallArgument
                || argument.source_obligation.component
                    != (SemanticObligationComponent::RegisterSlot { index, storage })
            {
                return Err(CertificationError::ObligationNotMapped(
                    argument.source_obligation,
                ));
            }
            let origin_matches = match argument.origin {
                CertifiedCallArgumentOrigin::Produced { producer } => {
                    argument.value.producer() == Some(producer)
                        && argument.value.constant().is_none()
                }
                CertifiedCallArgumentOrigin::Constant { value } => {
                    value.width_bits() == argument.value.binding().width_bits()
                        && (argument.value.constant() == Some(value)
                            || (argument.value.constant().is_none()
                                && argument.value.producer().is_some()))
                }
                CertifiedCallArgumentOrigin::AbiParameter { .. } => {
                    argument.value.constant().is_none()
                }
            };
            if !origin_matches {
                return Err(CertificationError::ObligationNotMapped(
                    argument.source_obligation,
                ));
            }
            let obligation = source
                .obligations()
                .get(&argument.source_obligation)
                .ok_or(CertificationError::UnknownObligation(
                    argument.source_obligation,
                ))?;
            if obligation.source.graph_inst() != Some(self.source_inst)
                || obligation.inputs != [argument.value.binding().value()]
            {
                return Err(CertificationError::ObligationNotMapped(
                    argument.source_obligation,
                ));
            }
        }
        Ok(())
    }
}

/// Sealed machine/topology evidence for one direct intra-function branch.
///
/// This owns one terminal edge and its `ControlTransfer/Whole` obligation. It
/// is not a structured region, executable statement, or function-exit proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedDirectControl {
    schema_version: u32,
    producer: CanonicalInstructionId,
    source_inst: r2ssa::InstId,
    target: u64,
    target_value: MachineValueUse,
    source_obligation: SemanticObligationId,
}

impl CertifiedDirectControl {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn target(&self) -> u64 {
        self.target
    }

    pub const fn target_value(&self) -> &MachineValueUse {
        &self.target_value
    }

    pub const fn source_obligation(&self) -> SemanticObligationId {
        self.source_obligation
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_source(source)?;
        validate_schema(self.schema_version)?;
        if self.source_obligation.instruction != self.producer
            || self.source_obligation.kind != SemanticObligationKind::ControlTransfer
            || self.source_obligation.component != SemanticObligationComponent::Whole
        {
            return Err(CertificationError::ObligationNotMapped(
                self.source_obligation,
            ));
        }
        let obligation = source.obligations().get(&self.source_obligation).ok_or(
            CertificationError::UnknownObligation(self.source_obligation),
        )?;
        if obligation.source.graph_inst() != Some(self.source_inst)
            || obligation.inputs != [self.target_value.binding().value()]
        {
            return Err(CertificationError::ObligationNotMapped(
                self.source_obligation,
            ));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedControlTruthiness {
    NonZeroIsTrue,
}

/// Sealed evidence for one direct two-arm conditional transfer.
///
/// Admission requires one final raw/SSA `CBranch`, exact distinct internal
/// true and block-end fallthrough targets, an exact two-successor topology, an
/// eight-bit condition, and matching `ControlPredicate/Whole` plus
/// `ControlTransfer/Whole` obligations. `NonZeroIsTrue` is full machine-
/// bitvector truthiness. This is not an `if`, ternary, join proof, structured
/// region, or rendering permission.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedConditionalControl {
    schema_version: u32,
    producer: CanonicalInstructionId,
    source_inst: r2ssa::InstId,
    true_target: u64,
    false_target: u64,
    target_value: MachineValueUse,
    condition: MachineValueUse,
    truthiness: CertifiedControlTruthiness,
    predicate_obligation: SemanticObligationId,
    transfer_obligation: SemanticObligationId,
}

impl CertifiedConditionalControl {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn true_target(&self) -> u64 {
        self.true_target
    }

    pub const fn false_target(&self) -> u64 {
        self.false_target
    }

    pub const fn target_value(&self) -> &MachineValueUse {
        &self.target_value
    }

    pub const fn condition(&self) -> &MachineValueUse {
        &self.condition
    }

    pub const fn truthiness(&self) -> CertifiedControlTruthiness {
        self.truthiness
    }

    pub const fn predicate_obligation(&self) -> SemanticObligationId {
        self.predicate_obligation
    }

    pub const fn transfer_obligation(&self) -> SemanticObligationId {
        self.transfer_obligation
    }

    pub fn source_obligations(&self) -> BTreeSet<SemanticObligationId> {
        BTreeSet::from([self.predicate_obligation, self.transfer_obligation])
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_source(source)?;
        validate_schema(self.schema_version)?;
        if self.true_target == self.false_target
            || self.truthiness != CertifiedControlTruthiness::NonZeroIsTrue
            || self.predicate_obligation.instruction != self.producer
            || self.predicate_obligation.kind != SemanticObligationKind::ControlPredicate
            || self.predicate_obligation.component != SemanticObligationComponent::Whole
            || self.transfer_obligation.instruction != self.producer
            || self.transfer_obligation.kind != SemanticObligationKind::ControlTransfer
            || self.transfer_obligation.component != SemanticObligationComponent::Whole
        {
            return Err(CertificationError::ObligationNotMapped(
                self.transfer_obligation,
            ));
        }
        let predicate = source.obligations().get(&self.predicate_obligation).ok_or(
            CertificationError::UnknownObligation(self.predicate_obligation),
        )?;
        let transfer = source.obligations().get(&self.transfer_obligation).ok_or(
            CertificationError::UnknownObligation(self.transfer_obligation),
        )?;
        if predicate.source.graph_inst() != Some(self.source_inst)
            || predicate.inputs != [self.condition.binding().value()]
            || transfer.source.graph_inst() != Some(self.source_inst)
            || transfer.inputs
                != [
                    self.target_value.binding().value(),
                    self.condition.binding().value(),
                ]
        {
            return Err(CertificationError::ObligationNotMapped(
                self.transfer_obligation,
            ));
        }
        Ok(())
    }
}

/// One ordered returned ABI value and the exact source obligation it owns.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedReturnValue {
    slot: CallBoundarySlot,
    value: MachineValueUse,
    source_obligation: SemanticObligationId,
}

/// One exact canonical register definition retained by a composed return.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedReturnRegisterDefinition {
    storage: CanonicalStorageId,
    value: MachineValueUse,
    producer: CanonicalInstructionId,
}

impl CertifiedReturnRegisterDefinition {
    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn value(&self) -> &MachineValueUse {
        &self.value
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }
}

/// One exact ordered contained-slice write over a composed return base.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedReturnRegisterOverlay {
    definition: CertifiedReturnRegisterDefinition,
    offset_bytes: u32,
}

impl CertifiedReturnRegisterOverlay {
    pub const fn definition(&self) -> &CertifiedReturnRegisterDefinition {
        &self.definition
    }

    pub const fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }
}

/// Sealed exact reconstruction of one full-width ABI return register.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedReturnRegisterComposition {
    slot: CallBoundarySlot,
    base: CertifiedReturnRegisterDefinition,
    overlays: Box<[CertifiedReturnRegisterOverlay]>,
    source_obligation: SemanticObligationId,
}

impl CertifiedReturnRegisterComposition {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn base(&self) -> &CertifiedReturnRegisterDefinition {
        &self.base
    }

    pub const fn overlays(&self) -> &[CertifiedReturnRegisterOverlay] {
        &self.overlays
    }

    pub const fn source_obligation(&self) -> SemanticObligationId {
        self.source_obligation
    }

    /// Exact base-then-overlay value order bound by the source obligation.
    pub fn ordered_values(&self) -> impl Iterator<Item = &MachineValueUse> {
        std::iter::once(self.base.value()).chain(
            self.overlays
                .iter()
                .map(|overlay| overlay.definition.value()),
        )
    }
}

/// Exact typed return-address carrier consumed by one machine return.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedReturnAddress {
    storage: CanonicalStorageId,
    value: MachineValueUse,
}

impl CertifiedReturnAddress {
    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn value(&self) -> &MachineValueUse {
        &self.value
    }
}

/// Exact typed stack-pointer state reaching one machine return.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedExitStackPointer {
    PreservedEntry {
        storage: CanonicalStorageId,
    },
    ReachingValue {
        storage: CanonicalStorageId,
        value: MachineValueUse,
    },
}

impl CertifiedExitStackPointer {
    pub const fn storage(&self) -> CanonicalStorageId {
        match self {
            Self::PreservedEntry { storage } | Self::ReachingValue { storage, .. } => *storage,
        }
    }

    pub const fn value(&self) -> Option<&MachineValueUse> {
        match self {
            Self::PreservedEntry { .. } => None,
            Self::ReachingValue { value, .. } => Some(value),
        }
    }
}

impl CertifiedReturnValue {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn value(&self) -> &MachineValueUse {
        &self.value
    }

    pub const fn source_obligation(&self) -> SemanticObligationId {
        self.source_obligation
    }
}

/// Sealed terminal-return evidence for one exact source block.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedReturnControl {
    schema_version: u32,
    producer: CanonicalInstructionId,
    source_inst: r2ssa::InstId,
    control_target: MachineValueUse,
    return_address: CertifiedReturnAddress,
    exit_stack_pointer: CertifiedExitStackPointer,
    values: Box<[CertifiedReturnValue]>,
    register_compositions: Box<[CertifiedReturnRegisterComposition]>,
    return_obligation: SemanticObligationId,
}

impl CertifiedReturnControl {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn control_target(&self) -> &MachineValueUse {
        &self.control_target
    }

    pub const fn return_address(&self) -> &CertifiedReturnAddress {
        &self.return_address
    }

    pub const fn exit_stack_pointer(&self) -> &CertifiedExitStackPointer {
        &self.exit_stack_pointer
    }

    pub const fn values(&self) -> &[CertifiedReturnValue] {
        &self.values
    }

    pub const fn register_compositions(&self) -> &[CertifiedReturnRegisterComposition] {
        &self.register_compositions
    }

    pub const fn return_obligation(&self) -> SemanticObligationId {
        self.return_obligation
    }

    pub fn source_obligations(&self) -> BTreeSet<SemanticObligationId> {
        std::iter::once(self.return_obligation)
            .chain(self.values.iter().map(|value| value.source_obligation))
            .chain(
                self.register_compositions
                    .iter()
                    .map(|composition| composition.source_obligation),
            )
            .collect()
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_source(source)?;
        validate_schema(self.schema_version)?;
        if self.return_obligation.instruction != self.producer
            || self.return_obligation.kind != SemanticObligationKind::Return
            || self.return_obligation.component != SemanticObligationComponent::Whole
            || self.source_obligations().len()
                != self
                    .values
                    .len()
                    .saturating_add(self.register_compositions.len())
                    .saturating_add(1)
            || self.return_address.value != self.control_target
        {
            return Err(CertificationError::ObligationNotMapped(
                self.return_obligation,
            ));
        }
        let terminal = source.obligations().get(&self.return_obligation).ok_or(
            CertificationError::UnknownObligation(self.return_obligation),
        )?;
        if terminal.source.graph_inst() != Some(self.source_inst)
            || terminal.inputs != [self.control_target.binding().value()]
        {
            return Err(CertificationError::ObligationNotMapped(
                self.return_obligation,
            ));
        }
        for returned in &self.values {
            if returned.source_obligation.instruction != self.producer
                || returned.source_obligation.kind != SemanticObligationKind::ReturnValue
                || returned.source_obligation.component != return_component(returned.slot)
            {
                return Err(CertificationError::ObligationNotMapped(
                    returned.source_obligation,
                ));
            }
            let obligation = source
                .obligations()
                .get(&returned.source_obligation)
                .ok_or(CertificationError::UnknownObligation(
                    returned.source_obligation,
                ))?;
            if obligation.source.graph_inst() != Some(self.source_inst)
                || obligation.inputs != [returned.value.binding().value()]
            {
                return Err(CertificationError::ObligationNotMapped(
                    returned.source_obligation,
                ));
            }
        }
        for composition in &self.register_compositions {
            if composition.overlays.is_empty()
                || composition.source_obligation.instruction != self.producer
                || composition.source_obligation.kind != SemanticObligationKind::ReturnValue
                || composition.source_obligation.component != return_component(composition.slot)
            {
                return Err(CertificationError::ObligationNotMapped(
                    composition.source_obligation,
                ));
            }
            let obligation = source
                .obligations()
                .get(&composition.source_obligation)
                .ok_or(CertificationError::UnknownObligation(
                    composition.source_obligation,
                ))?;
            let inputs = composition
                .ordered_values()
                .map(|value| value.binding().value())
                .collect::<Vec<_>>();
            if obligation.source.graph_inst() != Some(self.source_inst)
                || obligation.inputs != inputs
            {
                return Err(CertificationError::ObligationNotMapped(
                    composition.source_obligation,
                ));
            }
        }
        Ok(())
    }
}

fn return_component(slot: CallBoundarySlot) -> SemanticObligationComponent {
    match slot {
        CallBoundarySlot::Register { index, storage } => {
            SemanticObligationComponent::RegisterSlot { index, storage }
        }
        CallBoundarySlot::Stack(offset) => SemanticObligationComponent::StackOffset(offset),
    }
}

fn return_control_matches_interface(
    control: &CertifiedReturnControl,
    interface: &SourceFunctionInterface,
) -> bool {
    match interface.return_kind() {
        SourceFunctionReturn::Void => {
            control.values().is_empty() && control.register_compositions().is_empty()
        }
        SourceFunctionReturn::Register { storage } => {
            let slot = CallBoundarySlot::Register { index: 0, storage };
            (matches!(control.values(), [value] if value.slot() == slot)
                && control.register_compositions().is_empty())
                || (control.values().is_empty()
                    && matches!(
                        control.register_compositions(),
                        [composition] if composition.slot() == slot
                    ))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReturnClosureContract {
    Terminal,
    PlainRam,
    DirectCall,
    Conditional,
    Switch,
    Loop,
}

fn return_control_matches_closure(
    control: &CertifiedReturnControl,
    interface: &SourceFunctionInterface,
    contract: ReturnClosureContract,
) -> bool {
    return_control_matches_interface(control, interface)
        && (contract == ReturnClosureContract::Terminal
            || control.register_compositions().is_empty())
}

/// Sealed topology-and-predicate witness for the first admitted natural loop.
///
/// This proves only a carrier-free two-block routing shape. The entry and exit
/// remain open composition ports, and this is not executable-loop or rendering
/// permission.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedNaturalLoopRouting {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    loop_id: LoopId,
    predicate_id: PredicateId,
    header_control: CertifiedConditionalControl,
    body_transfer: CertifiedDirectControl,
    body_latch: u64,
    exit: u64,
    entry_predecessor: u64,
    continuation_on_true: bool,
}

impl CertifiedNaturalLoopRouting {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn loop_id(&self) -> LoopId {
        self.loop_id
    }

    pub const fn predicate_id(&self) -> PredicateId {
        self.predicate_id
    }

    pub const fn header_control(&self) -> &CertifiedConditionalControl {
        &self.header_control
    }

    pub const fn body_transfer(&self) -> &CertifiedDirectControl {
        &self.body_transfer
    }

    pub const fn header(&self) -> u64 {
        self.header_control.producer().block_addr
    }

    pub const fn body_latch(&self) -> u64 {
        self.body_latch
    }

    pub const fn exit(&self) -> u64 {
        self.exit
    }

    pub const fn entry_predecessor(&self) -> u64 {
        self.entry_predecessor
    }

    pub const fn continuation_on_true(&self) -> bool {
        self.continuation_on_true
    }
}

/// Sealed whole-function control evidence for the first executable natural
/// loop subset.
///
/// The function consists of one owned entry preheader, the carrier-free
/// header/body routing, and one terminal-return exit. The invariant header
/// condition is exactly one revision-bound ABI parameter carrier. This witness
/// is still not rendering permission; the complete obligation ledger and exit
/// return are checked by the typed-region permit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedClosedNaturalLoopControl {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    routing: CertifiedNaturalLoopRouting,
    preheader_transfer: CertifiedDirectControl,
    parameter_index: u32,
    parameter_abi_storage: CanonicalStorageId,
    parameter_graph_storage: CanonicalStorageId,
    parameter_logical_value: SourceLogicalValue,
}

impl CertifiedClosedNaturalLoopControl {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn routing(&self) -> &CertifiedNaturalLoopRouting {
        &self.routing
    }

    pub const fn preheader_transfer(&self) -> &CertifiedDirectControl {
        &self.preheader_transfer
    }

    pub const fn parameter_index(&self) -> u32 {
        self.parameter_index
    }

    pub const fn parameter_abi_storage(&self) -> CanonicalStorageId {
        self.parameter_abi_storage
    }

    pub const fn parameter_graph_storage(&self) -> CanonicalStorageId {
        self.parameter_graph_storage
    }

    pub const fn parameter_logical_value(&self) -> SourceLogicalValue {
        self.parameter_logical_value
    }

    pub const fn condition(&self) -> &MachineValueUse {
        self.routing.header_control().condition()
    }
}

/// Sealed structural witness for one final indirect branch with exact switch
/// labels and open targets.
///
/// This deliberately does not identify a selector or discharge the indirect
/// `ControlTransfer` obligation. It is topology evidence only and cannot
/// authorize a C `switch` or any target execution.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSwitchTopology {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    producer: CanonicalInstructionId,
    source_inst: r2ssa::InstId,
    indirect_target: MachineValueUse,
    switch_addr: u64,
    min_value: u64,
    max_value: u64,
    cases: Box<[(u64, u64)]>,
    default_target: u64,
    source_obligation: SemanticObligationId,
}

/// Sealed switch-control evidence retained separately from topology.
///
/// Construction binds the prepared selector to the terminal `BranchInd`, the
/// exact case/default topology, and one revision-bound ABI parameter carrier.
/// A topology witness alone can never acquire this evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSwitchControl {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    topology: CertifiedSwitchTopology,
    selector: MachineValueUse,
    parameter_index: u32,
    parameter_abi_storage: CanonicalStorageId,
    parameter_graph_storage: CanonicalStorageId,
    parameter_logical_value: SourceLogicalValue,
}

impl CertifiedSwitchControl {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.topology.producer()
    }

    pub const fn topology(&self) -> &CertifiedSwitchTopology {
        &self.topology
    }

    pub const fn selector(&self) -> &MachineValueUse {
        &self.selector
    }

    pub const fn indirect_target(&self) -> &MachineValueUse {
        self.topology.indirect_target()
    }

    pub const fn source_obligation(&self) -> SemanticObligationId {
        self.topology.source_obligation()
    }

    pub const fn parameter_index(&self) -> u32 {
        self.parameter_index
    }

    pub const fn parameter_abi_storage(&self) -> CanonicalStorageId {
        self.parameter_abi_storage
    }

    pub const fn parameter_graph_storage(&self) -> CanonicalStorageId {
        self.parameter_graph_storage
    }

    pub const fn parameter_logical_value(&self) -> SourceLogicalValue {
        self.parameter_logical_value
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_schema(self.schema_version)?;
        validate_schema(self.topology.schema_version())?;
        let obligation = source.obligations().get(&self.source_obligation()).ok_or(
            CertificationError::UnknownObligation(self.source_obligation()),
        )?;
        let parameter_matches = self
            .origin
            .machine_context()
            .source()
            .function_interface()
            .is_some_and(|interface| {
                interface_has_exact_parameter_projection(
                    interface,
                    self.parameter_index,
                    self.parameter_abi_storage,
                    self.parameter_graph_storage,
                    self.parameter_logical_value,
                )
            });
        if self.origin != *self.topology.origin()
            || obligation.id.kind != SemanticObligationKind::ControlTransfer
            || obligation.id.instruction != self.producer()
            || self.selector.binding().width_bits()
                != self
                    .parameter_graph_storage
                    .size
                    .checked_mul(8)
                    .unwrap_or(0)
            || self.selector.producer().is_some()
            || self.selector.constant().is_some()
            || self.selector.memory_access().is_some()
            || !parameter_matches
        {
            return Err(CertificationError::ObligationNotMapped(
                self.source_obligation(),
            ));
        }
        Ok(())
    }
}

impl CertifiedSwitchTopology {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn indirect_target(&self) -> &MachineValueUse {
        &self.indirect_target
    }

    pub const fn switch_addr(&self) -> u64 {
        self.switch_addr
    }

    pub const fn min_value(&self) -> u64 {
        self.min_value
    }

    pub const fn max_value(&self) -> u64 {
        self.max_value
    }

    /// Ordered `(case_value, successor_address)` pairs from the source.
    pub const fn cases(&self) -> &[(u64, u64)] {
        &self.cases
    }

    pub const fn default_target(&self) -> u64 {
        self.default_target
    }

    pub const fn source_obligation(&self) -> SemanticObligationId {
        self.source_obligation
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
enum DispositionEvidence {
    Output(CertifiedEntity),
    Expression(CertifiedExpr),
    Statement(CertifiedMemoryStatement),
    Call(CertifiedDirectCall),
    Control(CertifiedDirectControl),
    ConditionalControl(CertifiedConditionalControl),
    SwitchControl(Box<CertifiedSwitchControl>),
    ReturnControl(CertifiedReturnControl),
    Rewrite { schema_version: u32, pass: String },
    Diagnostic,
}

/// One proof-bearing disposition ready to enter the exact-once ledger.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedEffect {
    schema_version: u32,
    #[serde(skip_serializing)]
    authority: CertifiedAuthoritySeal,
    obligation: SemanticObligationId,
    disposition: EffectDisposition,
    evidence: DispositionEvidence,
}

impl CertifiedEffect {
    pub const fn obligation(&self) -> SemanticObligationId {
        self.obligation
    }

    pub const fn disposition(&self) -> &EffectDisposition {
        &self.disposition
    }

    pub const fn statement_evidence(&self) -> Option<&CertifiedMemoryStatement> {
        match &self.evidence {
            DispositionEvidence::Statement(statement) => Some(statement),
            _ => None,
        }
    }

    pub const fn expression_evidence(&self) -> Option<&CertifiedExpr> {
        match &self.evidence {
            DispositionEvidence::Expression(expression) => Some(expression),
            _ => None,
        }
    }

    pub const fn direct_call_evidence(&self) -> Option<&CertifiedDirectCall> {
        match &self.evidence {
            DispositionEvidence::Call(call) => Some(call),
            _ => None,
        }
    }

    pub const fn direct_control_evidence(&self) -> Option<&CertifiedDirectControl> {
        match &self.evidence {
            DispositionEvidence::Control(control) => Some(control),
            _ => None,
        }
    }

    pub const fn conditional_control_evidence(&self) -> Option<&CertifiedConditionalControl> {
        match &self.evidence {
            DispositionEvidence::ConditionalControl(control) => Some(control),
            _ => None,
        }
    }

    pub fn switch_control_evidence(&self) -> Option<&CertifiedSwitchControl> {
        match &self.evidence {
            DispositionEvidence::SwitchControl(control) => Some(control.as_ref()),
            _ => None,
        }
    }

    pub const fn return_control_evidence(&self) -> Option<&CertifiedReturnControl> {
        match &self.evidence {
            DispositionEvidence::ReturnControl(control) => Some(control),
            _ => None,
        }
    }

    fn validate(&self, source: &SemanticObligationInventory) -> Result<(), CertificationError> {
        validate_schema(self.schema_version)?;
        if !source.obligations().contains_key(&self.obligation) {
            return Err(CertificationError::UnknownObligation(self.obligation));
        }
        match (&self.disposition, &self.evidence) {
            (EffectDisposition::Rendered, DispositionEvidence::Output(entity)) => {
                entity.validate(source)?;
                ensure_mapped(entity.source_obligations(), self.obligation)
            }
            (
                EffectDisposition::AbsorbedIntoExpression { producer },
                DispositionEvidence::Expression(expression),
            ) => {
                expression.validate(source)?;
                if expression.entity().producer() != *producer {
                    return Err(CertificationError::UnknownInstruction(*producer));
                }
                ensure_mapped(expression.entity().source_obligations(), self.obligation)
            }
            (
                EffectDisposition::AbsorbedIntoStatement { producer },
                DispositionEvidence::Statement(statement),
            ) => {
                statement.validate(source)?;
                if statement.producer() != *producer {
                    return Err(CertificationError::UnknownInstruction(*producer));
                }
                ensure_mapped(statement.source_obligations(), self.obligation)
            }
            (EffectDisposition::AbsorbedIntoCall { producer }, DispositionEvidence::Call(call)) => {
                call.validate(source)?;
                if call.producer() != *producer
                    || !call.source_obligations().contains(&self.obligation)
                {
                    return Err(CertificationError::ObligationNotMapped(self.obligation));
                }
                Ok(())
            }
            (
                EffectDisposition::AbsorbedIntoControl { producer },
                DispositionEvidence::Control(control),
            ) => {
                control.validate(source)?;
                if control.producer() != *producer || control.source_obligation() != self.obligation
                {
                    return Err(CertificationError::ObligationNotMapped(self.obligation));
                }
                Ok(())
            }
            (
                EffectDisposition::AbsorbedIntoControl { producer },
                DispositionEvidence::ConditionalControl(control),
            ) => {
                control.validate(source)?;
                if control.producer() != *producer
                    || !control.source_obligations().contains(&self.obligation)
                {
                    return Err(CertificationError::ObligationNotMapped(self.obligation));
                }
                Ok(())
            }
            (
                EffectDisposition::AbsorbedIntoControl { producer },
                DispositionEvidence::SwitchControl(control),
            ) => {
                control.validate(source)?;
                if control.producer() != *producer || control.source_obligation() != self.obligation
                {
                    return Err(CertificationError::ObligationNotMapped(self.obligation));
                }
                Ok(())
            }
            (
                EffectDisposition::AbsorbedIntoReturn { producer },
                DispositionEvidence::ReturnControl(control),
            ) => {
                control.validate(source)?;
                if control.producer() != *producer
                    || !control.source_obligations().contains(&self.obligation)
                {
                    return Err(CertificationError::ObligationNotMapped(self.obligation));
                }
                Ok(())
            }
            (
                EffectDisposition::Rewritten { pass },
                DispositionEvidence::Rewrite {
                    schema_version,
                    pass: evidence_pass,
                },
            ) if !pass.trim().is_empty() && pass == evidence_pass => {
                validate_schema(*schema_version)
            }
            (
                EffectDisposition::Superseded { .. } | EffectDisposition::ProvenDead,
                DispositionEvidence::Rewrite {
                    schema_version,
                    pass,
                },
            ) if !pass.trim().is_empty() => validate_schema(*schema_version),
            (
                EffectDisposition::Residualized { reason } | EffectDisposition::Refused { reason },
                DispositionEvidence::Diagnostic,
            ) if !reason.trim().is_empty() => Ok(()),
            _ => Err(CertificationError::ObligationNotMapped(self.obligation)),
        }
    }
}

fn ensure_mapped(
    mapped: &BTreeSet<SemanticObligationId>,
    obligation: SemanticObligationId,
) -> Result<(), CertificationError> {
    mapped
        .contains(&obligation)
        .then_some(())
        .ok_or(CertificationError::ObligationNotMapped(obligation))
}

fn validate_schema(schema_version: u32) -> Result<(), CertificationError> {
    if schema_version == CERTIFICATION_SCHEMA_VERSION {
        Ok(())
    } else {
        Err(CertificationError::SchemaVersion {
            expected: CERTIFICATION_SCHEMA_VERSION,
            actual: schema_version,
        })
    }
}

fn validate_source(source: &SemanticObligationInventory) -> Result<(), CertificationError> {
    if source.schema_version() == SEMANTIC_OBLIGATION_SCHEMA_VERSION && source.is_complete() {
        Ok(())
    } else {
        Err(CertificationError::IncompleteSourceInventory)
    }
}

fn source_site_mismatch(
    id: CanonicalInstructionId,
    source: SemanticSourceSite,
) -> MachineBuildError {
    source.graph_inst().map_or(
        MachineBuildError::ObligationSourceMismatch(id),
        MachineBuildError::ObligationMismatch,
    )
}

/// Proof that one transformation accounted for all of its declared inputs.
///
/// Obligation IDs remain source identities across rewrites. The certificate
/// records semantic dispositions, not AST locations or output names.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RewriteCertificate {
    schema_version: u32,
    pass: String,
    inputs: BTreeSet<SemanticObligationId>,
    dispositions: BTreeMap<SemanticObligationId, Vec<EffectDisposition>>,
}

impl RewriteCertificate {
    pub fn new(
        pass: impl Into<String>,
        inputs: impl IntoIterator<Item = SemanticObligationId>,
    ) -> Self {
        Self {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            pass: pass.into(),
            inputs: inputs.into_iter().collect(),
            dispositions: BTreeMap::new(),
        }
    }

    pub fn residualize(&mut self, id: SemanticObligationId, reason: impl Into<String>) {
        self.push(
            id,
            EffectDisposition::Residualized {
                reason: reason.into(),
            },
        );
    }

    pub fn refuse(&mut self, id: SemanticObligationId, reason: impl Into<String>) {
        self.push(
            id,
            EffectDisposition::Refused {
                reason: reason.into(),
            },
        );
    }

    fn push(&mut self, id: SemanticObligationId, disposition: EffectDisposition) {
        self.dispositions.entry(id).or_default().push(disposition);
    }

    pub fn audit(&self, source: &SemanticObligationInventory) -> RewriteCertificateReport {
        let disposition_ids = self.dispositions.keys().copied().collect::<BTreeSet<_>>();
        let mut report = RewriteCertificateReport {
            missing: self.inputs.difference(&disposition_ids).copied().collect(),
            duplicate: self
                .dispositions
                .iter()
                .filter_map(|(id, dispositions)| (dispositions.len() > 1).then_some(*id))
                .collect(),
            unexpected: disposition_ids.difference(&self.inputs).copied().collect(),
            invalid: Vec::new(),
        };
        if let Err(error) = validate_schema(self.schema_version) {
            report.invalid.push(format!("{error:?}"));
        }
        if let Err(error) = validate_source(source) {
            report.invalid.push(format!("{error:?}"));
        }
        if self.pass.trim().is_empty() {
            report
                .invalid
                .push("rewrite pass identity is empty".to_string());
        }
        for id in &self.inputs {
            if !source.obligations().contains_key(id) {
                report
                    .invalid
                    .push(format!("rewrite input {id} is not a source obligation"));
            }
        }
        for (id, dispositions) in &self.dispositions {
            for disposition in dispositions {
                let valid = match disposition {
                    EffectDisposition::Rewritten { .. }
                    | EffectDisposition::Superseded { .. }
                    | EffectDisposition::ProvenDead => false,
                    EffectDisposition::Residualized { reason }
                    | EffectDisposition::Refused { reason } => !reason.trim().is_empty(),
                    EffectDisposition::Rendered
                    | EffectDisposition::AbsorbedIntoExpression { .. }
                    | EffectDisposition::AbsorbedIntoStatement { .. }
                    | EffectDisposition::AbsorbedIntoCall { .. }
                    | EffectDisposition::AbsorbedIntoControl { .. }
                    | EffectDisposition::AbsorbedIntoReturn { .. } => false,
                };
                if !valid {
                    report.invalid.push(format!(
                        "rewrite pass {:?} has invalid disposition for {id}",
                        self.pass
                    ));
                }
            }
        }
        report
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RewriteCertificateReport {
    pub missing: Vec<SemanticObligationId>,
    pub duplicate: Vec<SemanticObligationId>,
    pub unexpected: Vec<SemanticObligationId>,
    pub invalid: Vec<String>,
}

impl RewriteCertificateReport {
    pub fn is_closed(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }
}

/// Exact-once ledger. Entries are retained as proof-bearing effects so
/// duplication remains diagnosable rather than being silently overwritten.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ObligationLedger {
    schema_version: u32,
    #[serde(skip_serializing)]
    authority: CertifiedAuthoritySeal,
    effects: BTreeMap<SemanticObligationId, Vec<CertifiedEffect>>,
}

impl Default for ObligationLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl ObligationLedger {
    pub fn new() -> Self {
        Self {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: CertifiedAuthoritySeal::new(),
            effects: BTreeMap::new(),
        }
    }

    fn bound(origin: &CertifiedArtifactOrigin) -> Self {
        Self {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: origin.authority().clone(),
            effects: BTreeMap::new(),
        }
    }

    pub fn matches_origin(&self, origin: &CertifiedArtifactOrigin) -> bool {
        self.schema_version == CERTIFICATION_SCHEMA_VERSION && self.authority == *origin.authority()
    }

    pub fn effects(&self, id: SemanticObligationId) -> &[CertifiedEffect] {
        self.effects.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }

    fn record(&mut self, effect: CertifiedEffect) {
        self.effects
            .entry(effect.obligation())
            .or_default()
            .push(effect);
    }

    fn audit(&self, source: &SemanticObligationInventory) -> CertificationReport {
        let mut report = CertificationReport {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            source_obligations: source.obligations().len(),
            missing: Vec::new(),
            duplicate: Vec::new(),
            unexpected: Vec::new(),
            residualized: Vec::new(),
            refused: Vec::new(),
            pending_semantic_ast: Vec::new(),
            typed_region_required: false,
            invalid: Vec::new(),
        };

        if let Err(error) = validate_schema(self.schema_version) {
            report.invalid.push(CertificationFailure {
                obligation: None,
                reason: format!("{error:?}"),
            });
        }
        if let Err(error) = validate_source(source) {
            push_failure(&mut report, None, format!("{error:?}"));
        }
        for id in source.obligations().keys() {
            let effects = self.effects(*id);
            match effects.len() {
                0 => report.missing.push(*id),
                1 => {
                    let effect = &effects[0];
                    if effect.authority != self.authority {
                        push_failure(
                            &mut report,
                            Some(*id),
                            "effect authority does not match its obligation ledger",
                        );
                    }
                    if let Err(error) = effect.validate(source) {
                        push_failure(&mut report, Some(*id), format!("{error:?}"));
                    }
                    let disposition = effect.disposition();
                    if matches!(
                        disposition,
                        EffectDisposition::AbsorbedIntoExpression { .. }
                            | EffectDisposition::AbsorbedIntoStatement { .. }
                            | EffectDisposition::AbsorbedIntoCall { .. }
                            | EffectDisposition::AbsorbedIntoControl { .. }
                            | EffectDisposition::AbsorbedIntoReturn { .. }
                    ) {
                        report.pending_semantic_ast.push(*id);
                    }
                    if !disposition.is_semantically_preserving() {
                        match disposition {
                            EffectDisposition::Residualized { .. } => report.residualized.push(*id),
                            EffectDisposition::Refused { .. } => report.refused.push(*id),
                            _ => {}
                        }
                    }
                    if source
                        .instructions()
                        .get(&id.instruction)
                        .is_some_and(|instruction| {
                            instruction.state == SemanticInstructionState::UnsupportedUnknown
                                && disposition.is_semantically_preserving()
                        })
                    {
                        push_failure(
                            &mut report,
                            Some(*id),
                            "unsupported/unknown source semantics cannot authorize CertifiedC",
                        );
                    }
                }
                _ => report.duplicate.push(*id),
            }
        }

        for id in self.effects.keys() {
            if !source.obligations().contains_key(id) {
                report.unexpected.push(*id);
            }
        }
        validate_supersession_graph(self, source, &mut report);
        report
    }
}

fn validate_supersession_graph(
    ledger: &ObligationLedger,
    source: &SemanticObligationInventory,
    report: &mut CertificationReport,
) {
    let mut edges = BTreeMap::<SemanticObligationId, SemanticObligationId>::new();
    let mut incoming = BTreeMap::<SemanticObligationId, Vec<SemanticObligationId>>::new();
    for id in source.obligations().keys() {
        let [effect] = ledger.effects(*id) else {
            continue;
        };
        if let EffectDisposition::Superseded { by } = effect.disposition() {
            edges.insert(*id, *by);
            incoming.entry(*by).or_default().push(*id);
        }
    }
    for (target, predecessors) in incoming {
        if predecessors.len() > 1 {
            for predecessor in predecessors {
                push_failure(
                    report,
                    Some(predecessor),
                    format!("multiple obligations supersede the same target {target}"),
                );
            }
        }
    }
    for start in edges.keys() {
        let mut seen = BTreeSet::new();
        let mut cursor = *start;
        loop {
            if !seen.insert(cursor) {
                push_failure(report, Some(*start), "supersession chain contains a cycle");
                break;
            }
            let Some(next) = edges.get(&cursor).copied() else {
                let [terminal] = ledger.effects(cursor) else {
                    push_failure(
                        report,
                        Some(*start),
                        "supersession chain has no unique terminal disposition",
                    );
                    break;
                };
                if !terminal.disposition().is_semantically_preserving() {
                    push_failure(
                        report,
                        Some(*start),
                        "supersession chain terminates in a non-preserving disposition",
                    );
                }
                break;
            };
            cursor = next;
        }
    }
}

fn push_failure(
    report: &mut CertificationReport,
    obligation: Option<SemanticObligationId>,
    reason: impl Into<String>,
) {
    let failure = CertificationFailure {
        obligation,
        reason: reason.into(),
    };
    if !report.invalid.contains(&failure) {
        report.invalid.push(failure);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificationFailure {
    pub obligation: Option<SemanticObligationId>,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertificationReport {
    schema_version: u32,
    source_obligations: usize,
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    residualized: Vec<SemanticObligationId>,
    refused: Vec<SemanticObligationId>,
    pending_semantic_ast: Vec<SemanticObligationId>,
    typed_region_required: bool,
    invalid: Vec<CertificationFailure>,
}

impl CertificationReport {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn source_obligation_count(&self) -> usize {
        self.source_obligations
    }

    pub fn missing(&self) -> &[SemanticObligationId] {
        &self.missing
    }

    pub fn duplicate(&self) -> &[SemanticObligationId] {
        &self.duplicate
    }

    pub fn unexpected(&self) -> &[SemanticObligationId] {
        &self.unexpected
    }

    pub fn residualized(&self) -> &[SemanticObligationId] {
        &self.residualized
    }

    pub fn refused(&self) -> &[SemanticObligationId] {
        &self.refused
    }

    /// Preserved by a sealed semantic node but not yet validated as part of a
    /// complete typed output AST. `r2cert` alone cannot grant final C output.
    pub fn pending_semantic_ast(&self) -> &[SemanticObligationId] {
        &self.pending_semantic_ast
    }

    pub const fn requires_typed_region_validation(&self) -> bool {
        self.typed_region_required
    }

    pub fn invalid(&self) -> &[CertificationFailure] {
        &self.invalid
    }

    pub fn has_exactly_one_disposition_per_source(&self) -> bool {
        self.missing.is_empty() && self.duplicate.is_empty() && self.unexpected.is_empty()
    }

    pub fn is_closed_semantic_ledger(&self) -> bool {
        self.schema_version == CERTIFICATION_SCHEMA_VERSION
            && self.has_exactly_one_disposition_per_source()
            && self.residualized.is_empty()
            && self.refused.is_empty()
            && self.pending_semantic_ast.is_empty()
            && !self.typed_region_required
            && self.invalid.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedTypedRegionKind {
    TerminalReturnBlock,
    PlainRamMemoryTerminalReturnFunction,
    DirectCallTerminalReturnFunction,
    ConditionalTerminalReturnFunction,
    SwitchTerminalReturnFunction,
    CarrierFreeLoopTerminalReturnFunction,
    PrivateFrameConditionalJoinFunction,
}

pub const CERTIFIED_TERMINAL_RETURN_REGION_CONTRACT_VERSION: u32 = 5;
pub const CERTIFIED_PLAIN_RAM_MEMORY_RETURN_CONTRACT_VERSION: u32 = 4;
pub const CERTIFIED_DIRECT_CALL_TERMINAL_RETURN_CONTRACT_VERSION: u32 = 3;
pub const CERTIFIED_CONDITIONAL_TERMINAL_RETURN_CONTRACT_VERSION: u32 = 3;
pub const CERTIFIED_SWITCH_TERMINAL_RETURN_CONTRACT_VERSION: u32 = 3;
pub const CERTIFIED_CARRIER_FREE_LOOP_TERMINAL_RETURN_CONTRACT_VERSION: u32 = 3;
pub const CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION: u32 = 2;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TypedRegionMapping {
    obligation: SemanticObligationId,
    source_disposition: EffectDisposition,
}

impl TypedRegionMapping {
    pub const fn new(
        obligation: SemanticObligationId,
        source_disposition: EffectDisposition,
    ) -> Self {
        Self {
            obligation,
            source_disposition,
        }
    }

    pub const fn obligation(&self) -> SemanticObligationId {
        self.obligation
    }

    pub const fn source_disposition(&self) -> &EffectDisposition {
        &self.source_disposition
    }
}

/// Opaque proof that one sealed artifact ledger is closed exactly once for a
/// recognized structural region contract.
///
/// This token contains no typed-output identity and grants no C rendering
/// authority. A consumer must bind it to its own exact artifact-local output
/// owners before any rendering decision.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedLedgerClosure {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    region_kind: CertifiedTypedRegionKind,
    region_schema_version: u32,
    mappings: Box<[TypedRegionMapping]>,
}

impl CertifiedLedgerClosure {
    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn region_kind(&self) -> CertifiedTypedRegionKind {
        self.region_kind
    }

    pub const fn region_schema_version(&self) -> u32 {
        self.region_schema_version
    }

    pub const fn mappings(&self) -> &[TypedRegionMapping] {
        &self.mappings
    }

    fn has_closed_ledger_mapping(&self) -> bool {
        let recognized_contract = match self.region_kind {
            CertifiedTypedRegionKind::TerminalReturnBlock => {
                self.region_schema_version == CERTIFIED_TERMINAL_RETURN_REGION_CONTRACT_VERSION
            }
            CertifiedTypedRegionKind::PlainRamMemoryTerminalReturnFunction => {
                self.region_schema_version == CERTIFIED_PLAIN_RAM_MEMORY_RETURN_CONTRACT_VERSION
            }
            CertifiedTypedRegionKind::DirectCallTerminalReturnFunction => {
                self.region_schema_version == CERTIFIED_DIRECT_CALL_TERMINAL_RETURN_CONTRACT_VERSION
            }
            CertifiedTypedRegionKind::ConditionalTerminalReturnFunction => {
                self.region_schema_version == CERTIFIED_CONDITIONAL_TERMINAL_RETURN_CONTRACT_VERSION
            }
            CertifiedTypedRegionKind::SwitchTerminalReturnFunction => {
                self.region_schema_version == CERTIFIED_SWITCH_TERMINAL_RETURN_CONTRACT_VERSION
            }
            CertifiedTypedRegionKind::CarrierFreeLoopTerminalReturnFunction => {
                self.region_schema_version
                    == CERTIFIED_CARRIER_FREE_LOOP_TERMINAL_RETURN_CONTRACT_VERSION
            }
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction => {
                self.region_schema_version
                    == CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION
            }
        };
        let mapped_obligations = self
            .mappings
            .iter()
            .map(TypedRegionMapping::obligation)
            .collect::<BTreeSet<_>>();
        let source_obligations = self
            .origin
            .source()
            .obligations()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        self.schema_version == CERTIFICATION_SCHEMA_VERSION
            && self.origin.schema_version() == CERTIFICATION_SCHEMA_VERSION
            && recognized_contract
            && self.mappings.len() == mapped_obligations.len()
            && mapped_obligations == source_obligations
    }

    pub fn matches_ledger(
        &self,
        origin: &CertifiedArtifactOrigin,
        region_kind: CertifiedTypedRegionKind,
        region_schema_version: u32,
        mappings: &[TypedRegionMapping],
    ) -> bool {
        self.has_closed_ledger_mapping()
            && self.origin == *origin
            && self.region_kind == region_kind
            && self.region_schema_version == region_schema_version
            && self.mappings.as_ref() == mappings
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LedgerClosureError {
    InvalidOrigin,
    InvalidRegionSchema,
    InvalidRegionTopology,
    InvalidRegionDisposition(SemanticObligationId),
    IncompleteLedger,
    ResidualOrRefusedObligation(SemanticObligationId),
    UnsupportedSourceSemantics(CanonicalInstructionId),
    MissingMapping(SemanticObligationId),
    DuplicateMapping(SemanticObligationId),
    UnexpectedMapping(SemanticObligationId),
    DispositionMismatch(SemanticObligationId),
}

impl std::fmt::Display for LedgerClosureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "typed-region ledger closure failed: {self:?}")
    }
}

impl std::error::Error for LedgerClosureError {}

fn terminal_return_mechanics_producers(
    dependencies: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    roots: impl IntoIterator<Item = CanonicalInstructionId>,
    semantic_seeds: impl IntoIterator<Item = CanonicalInstructionId>,
) -> Option<BTreeSet<CanonicalInstructionId>> {
    let mut candidates = BTreeSet::new();
    let mut active = BTreeSet::new();
    let mut complete = BTreeSet::new();
    for root in roots {
        let mut stack = vec![(root, false)];
        while let Some((producer, leaving)) = stack.pop() {
            candidates.insert(producer);
            if leaving {
                active.remove(&producer);
                complete.insert(producer);
                continue;
            }
            if complete.contains(&producer) {
                continue;
            }
            let inputs = dependencies.get(&producer)?;
            if !active.insert(producer) {
                return None;
            }
            stack.push((producer, true));
            stack.extend(inputs.iter().rev().map(|input| (*input, false)));
        }
    }

    let mut semantic = semantic_seeds
        .into_iter()
        .filter(|producer| candidates.contains(producer))
        .collect::<BTreeSet<_>>();
    for (producer, inputs) in dependencies {
        if candidates.contains(producer) {
            continue;
        }
        semantic.extend(
            inputs
                .iter()
                .copied()
                .filter(|input| candidates.contains(input)),
        );
    }
    let mut frontier = semantic.iter().copied().collect::<Vec<_>>();
    while let Some(producer) = frontier.pop() {
        let inputs = dependencies.get(&producer)?;
        for input in inputs {
            if candidates.contains(input) && semantic.insert(*input) {
                frontier.push(*input);
            }
        }
    }
    Some(candidates.difference(&semantic).copied().collect())
}

fn terminal_return_semantic_producers(
    return_control: &CertifiedReturnControl,
) -> BTreeSet<CanonicalInstructionId> {
    return_control
        .values()
        .iter()
        .map(CertifiedReturnValue::value)
        .chain(
            return_control
                .register_compositions()
                .iter()
                .flat_map(CertifiedReturnRegisterComposition::ordered_values),
        )
        .filter_map(MachineValueUse::producer)
        .collect()
}

fn exact_terminal_return_mechanical_reads(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: &BTreeMap<SemanticObligationId, &TypedRegionMapping>,
    return_control: &CertifiedReturnControl,
) -> Option<BTreeSet<SemanticObligationId>> {
    let mut dependencies = BTreeMap::new();
    for instruction in origin.source().instructions().values() {
        let live = instruction
            .obligations
            .iter()
            .copied()
            .filter(|obligation| obligation.kind == SemanticObligationKind::LiveValueProducer)
            .collect::<Vec<_>>();
        if live.is_empty() {
            continue;
        }
        let [obligation] = live.as_slice() else {
            return None;
        };
        let [effect] = ledger.effects(*obligation) else {
            return None;
        };
        let expression = effect.expression_evidence()?;
        if effect.disposition()
            != &(EffectDisposition::AbsorbedIntoExpression {
                producer: instruction.id,
            })
            || expression.entity().producer() != instruction.id
            || expression.entity().source_obligations() != &BTreeSet::from([*obligation])
            || dependencies
                .insert(instruction.id, expression.inputs().clone())
                .is_some()
        {
            return None;
        }
    }
    let roots = [
        return_control.return_address().value().producer(),
        return_control
            .exit_stack_pointer()
            .value()
            .and_then(MachineValueUse::producer),
    ]
    .into_iter()
    .flatten();
    let semantic_seeds = terminal_return_semantic_producers(return_control);
    let mechanics = terminal_return_mechanics_producers(&dependencies, roots, semantic_seeds)?;

    let mut reads = BTreeSet::new();
    for obligation in origin
        .source()
        .obligations()
        .values()
        .filter(|obligation| obligation.id.kind == SemanticObligationKind::ObservableMemoryRead)
    {
        if !mechanics.contains(&obligation.id.instruction) {
            continue;
        }
        let [effect] = ledger.effects(obligation.id) else {
            return None;
        };
        let statement = effect.statement_evidence()?;
        let mapping = mappings.get(&obligation.id)?;
        if effect.disposition()
            != &(EffectDisposition::AbsorbedIntoStatement {
                producer: obligation.id.instruction,
            })
            || mapping.source_disposition() != effect.disposition()
            || statement.producer() != obligation.id.instruction
            || statement.source_obligations() != &BTreeSet::from([obligation.id])
            || statement.execution() != CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrder
            || !matches!(
                statement.kind(),
                CertifiedMemoryStatementKind::Read { result }
                    if result.producer() == Some(obligation.id.instruction)
            )
        {
            return None;
        }
        reads.insert(obligation.id);
    }
    Some(reads)
}

fn exact_terminal_frame_memory_obligations(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: &BTreeMap<SemanticObligationId, &TypedRegionMapping>,
    return_control: &CertifiedReturnControl,
    frame: &CertifiedFramePreservation,
) -> Option<BTreeSet<SemanticObligationId>> {
    let restore = exact_frame_restore_for_return(origin, frame, return_control)?;
    let mut statements = vec![(
        frame.entry_save(),
        SemanticObligationKind::ObservableMemoryWrite,
    )];
    statements.push((
        restore.restore_read(),
        SemanticObligationKind::ObservableMemoryRead,
    ));
    if let Some(return_address_read) = restore.return_address_read() {
        statements.push((
            return_address_read,
            SemanticObligationKind::ObservableMemoryRead,
        ));
    }

    let mut obligations = BTreeSet::new();
    for (statement, expected_kind) in statements {
        let kind_matches = matches!(
            (expected_kind, statement.kind()),
            (
                SemanticObligationKind::ObservableMemoryRead,
                CertifiedMemoryStatementKind::Read { .. }
            ) | (
                SemanticObligationKind::ObservableMemoryWrite,
                CertifiedMemoryStatementKind::Write { .. }
            )
        );
        if !kind_matches
            || statement.execution() != CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrder
            || statement.source_obligations().is_empty()
        {
            return None;
        }
        for obligation in statement.source_obligations() {
            let [effect] = ledger.effects(*obligation) else {
                return None;
            };
            let mapping = mappings.get(obligation)?;
            if obligation.instruction != statement.producer()
                || obligation.kind != expected_kind
                || !origin.source().obligations().contains_key(obligation)
                || effect.disposition()
                    != &(EffectDisposition::AbsorbedIntoStatement {
                        producer: statement.producer(),
                    })
                || effect.statement_evidence() != Some(statement)
                || mapping.source_disposition() != effect.disposition()
                || !obligations.insert(*obligation)
            {
                return None;
            }
        }
    }
    Some(obligations)
}

pub(crate) fn exact_frame_restore_for_return<'a>(
    origin: &CertifiedArtifactOrigin,
    frame: &'a CertifiedFramePreservation,
    return_control: &CertifiedReturnControl,
) -> Option<&'a CertifiedFrameRestore> {
    if frame.origin() != origin || frame.origin().schema_version() != CERTIFICATION_SCHEMA_VERSION {
        return None;
    }
    let matching = frame
        .restores()
        .iter()
        .filter(|restore| restore.return_control() == return_control)
        .collect::<Vec<_>>();
    let [restore] = matching.as_slice() else {
        return None;
    };
    Some(*restore)
}

fn terminal_return_obligation_is_admitted(
    obligation: SemanticObligationId,
    mechanical_reads: &BTreeSet<SemanticObligationId>,
    frame_memory: &BTreeSet<SemanticObligationId>,
) -> bool {
    matches!(
        obligation.kind,
        SemanticObligationKind::LiveValueProducer
            | SemanticObligationKind::Return
            | SemanticObligationKind::ReturnValue
    ) || obligation.kind == SemanticObligationKind::ObservableMemoryRead
        && mechanical_reads.contains(&obligation)
        || matches!(
            obligation.kind,
            SemanticObligationKind::ObservableMemoryRead
                | SemanticObligationKind::ObservableMemoryWrite
        ) && frame_memory.contains(&obligation)
}

pub fn certify_terminal_return_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    certify_terminal_return_region_with_frame(origin, ledger, mappings, None)
}

pub fn certify_terminal_return_region_with_frame(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    frame: Option<&CertifiedFramePreservation>,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    // An ABI is not required to close a terminal return region: exit machine
    // state is proven from the machine's own carriers just above, and the
    // values a return carries are certified separately and residualize when no
    // ABI describes them.
    if !origin.is_valid()
        || !ledger.matches_origin(origin)
        || !return_machine_state_matches_origin(origin, ledger)
    {
        return Err(LedgerClosureError::InvalidOrigin);
    }
    let [block] = origin.topology().blocks() else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    if !matches!(block.terminator(), CertifiedSourceTerminator::Return)
        || !block.successors().is_empty()
        || block.instructions().is_empty()
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    let report = ledger.audit(origin.source());
    if !report.has_exactly_one_disposition_per_source() || !report.invalid().is_empty() {
        return Err(LedgerClosureError::IncompleteLedger);
    }
    if let Some(obligation) = report.residualized().iter().chain(report.refused()).next() {
        return Err(LedgerClosureError::ResidualOrRefusedObligation(*obligation));
    }
    if let Some(instruction) = origin
        .source()
        .instructions()
        .values()
        .find(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
    {
        return Err(LedgerClosureError::UnsupportedSourceSemantics(
            instruction.id,
        ));
    }
    let mappings = mappings.into_iter().collect::<Vec<_>>();
    let mut by_obligation = BTreeMap::<SemanticObligationId, &TypedRegionMapping>::new();
    for mapping in &mappings {
        if !origin
            .source()
            .obligations()
            .contains_key(&mapping.obligation)
        {
            return Err(LedgerClosureError::UnexpectedMapping(mapping.obligation));
        }
        if by_obligation.insert(mapping.obligation, mapping).is_some() {
            return Err(LedgerClosureError::DuplicateMapping(mapping.obligation));
        }
    }
    let return_effects = origin
        .source()
        .obligations()
        .values()
        .filter(|obligation| obligation.id.kind == SemanticObligationKind::Return)
        .map(|obligation| ledger.effects(obligation.id))
        .collect::<Vec<_>>();
    let [[return_effect]] = return_effects.as_slice() else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    let Some(return_control) = return_effect.return_control_evidence() else {
        return Err(LedgerClosureError::InvalidRegionDisposition(
            return_effect.obligation(),
        ));
    };
    if block.instructions().last() != Some(&return_control.producer())
        || return_effect.disposition()
            != &(EffectDisposition::AbsorbedIntoReturn {
                producer: return_control.producer(),
            })
        || origin
            .machine_context()
            .source()
            .function_interface()
            .is_none_or(|interface| {
                !return_control_matches_closure(
                    return_control,
                    interface,
                    ReturnClosureContract::Terminal,
                )
            })
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    let mechanical_reads =
        exact_terminal_return_mechanical_reads(origin, ledger, &by_obligation, return_control)
            .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    let frame_memory = frame
        .map(|frame| {
            exact_terminal_frame_memory_obligations(
                origin,
                ledger,
                &by_obligation,
                return_control,
                frame,
            )
            .ok_or(LedgerClosureError::InvalidRegionTopology)
        })
        .transpose()?
        .unwrap_or_default();
    if origin.source().obligations().values().any(|obligation| {
        !terminal_return_obligation_is_admitted(obligation.id, &mechanical_reads, &frame_memory)
    }) {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    for obligation in origin.source().obligations().values() {
        let [effect] = ledger.effects(obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let valid = match obligation.id.kind {
            SemanticObligationKind::LiveValueProducer => matches!(
                effect.disposition(),
                EffectDisposition::AbsorbedIntoExpression { .. }
            ),
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
                effect.return_control_evidence() == Some(return_control)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoReturn { producer }
                            if *producer == return_control.producer()
                    )
            }
            SemanticObligationKind::ObservableMemoryRead
            | SemanticObligationKind::ObservableMemoryWrite => {
                (mechanical_reads.contains(&obligation.id) || frame_memory.contains(&obligation.id))
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoStatement { producer }
                            if *producer == obligation.id.instruction
                    )
            }
            _ => false,
        };
        if !valid {
            return Err(LedgerClosureError::InvalidRegionDisposition(obligation.id));
        }
    }
    for obligation in origin.source().obligations().keys() {
        let mapping = by_obligation
            .get(obligation)
            .ok_or(LedgerClosureError::MissingMapping(*obligation))?;
        let [effect] = ledger.effects(*obligation) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        if effect.disposition() != mapping.source_disposition()
            || matches!(
                mapping.source_disposition(),
                EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
            )
        {
            return Err(LedgerClosureError::DispositionMismatch(*obligation));
        }
    }
    Ok(CertifiedLedgerClosure {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::TerminalReturnBlock,
        region_schema_version: CERTIFIED_TERMINAL_RETURN_REGION_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

/// Authorize one exact closed single-block function containing supported value
/// expressions, at least one certified plain byte-addressed RAM access, and one
/// final return under the retained source function interface.
///
/// Memory is deliberately narrower than the general statement certificate:
/// custom spaces, word-addressed RAM, non-8/16/32/64 accesses, and any policy
/// other than an exactly-once source-ordered helper call remain unauthorized.
pub fn certify_plain_ram_memory_return_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    if !origin.is_valid()
        || !ledger.matches_origin(origin)
        || !return_machine_state_matches_origin(origin, ledger)
        || origin
            .machine_context()
            .source()
            .function_interface()
            .is_none()
    {
        return Err(LedgerClosureError::InvalidOrigin);
    }
    let [block] = origin.topology().blocks() else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    if origin.topology().entry_addr() != block.addr()
        || !block.predecessors().is_empty()
        || !matches!(block.terminator(), CertifiedSourceTerminator::Return)
        || !block.successors().is_empty()
        || block.instructions().is_empty()
        || origin.source().instructions().values().any(|instruction| {
            instruction.state == SemanticInstructionState::UnsupportedUnknown
                || matches!(instruction.id.site, r2ssa::CanonicalInstructionSite::Phi(_))
        })
        || origin.source().obligations().values().any(|obligation| {
            !matches!(
                obligation.id.kind,
                SemanticObligationKind::LiveValueProducer
                    | SemanticObligationKind::ObservableMemoryRead
                    | SemanticObligationKind::ObservableMemoryWrite
                    | SemanticObligationKind::Return
                    | SemanticObligationKind::ReturnValue
            )
        })
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    let report = ledger.audit(origin.source());
    if !report.has_exactly_one_disposition_per_source() || !report.invalid().is_empty() {
        return Err(LedgerClosureError::IncompleteLedger);
    }
    if let Some(obligation) = report.residualized().iter().chain(report.refused()).next() {
        return Err(LedgerClosureError::ResidualOrRefusedObligation(*obligation));
    }

    let return_effects = origin
        .source()
        .obligations()
        .values()
        .filter(|obligation| obligation.id.kind == SemanticObligationKind::Return)
        .map(|obligation| ledger.effects(obligation.id))
        .collect::<Vec<_>>();
    let [[return_effect]] = return_effects.as_slice() else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    let Some(return_control) = return_effect.return_control_evidence() else {
        return Err(LedgerClosureError::InvalidRegionDisposition(
            return_effect.obligation(),
        ));
    };
    if block.instructions().last() != Some(&return_control.producer())
        || return_effect.disposition()
            != &(EffectDisposition::AbsorbedIntoReturn {
                producer: return_control.producer(),
            })
        || origin
            .machine_context()
            .source()
            .function_interface()
            .is_none_or(|interface| {
                !return_control_matches_closure(
                    return_control,
                    interface,
                    ReturnClosureContract::PlainRam,
                )
            })
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }

    let mut memory_count = 0_usize;
    for obligation in origin.source().obligations().values() {
        let [effect] = ledger.effects(obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let valid = match obligation.id.kind {
            SemanticObligationKind::LiveValueProducer => matches!(
                effect.disposition(),
                EffectDisposition::AbsorbedIntoExpression { .. }
            ),
            SemanticObligationKind::ObservableMemoryRead
            | SemanticObligationKind::ObservableMemoryWrite => {
                memory_count += 1;
                effect.statement_evidence().is_some_and(|statement| {
                    statement.producer() == obligation.id.instruction
                        && statement.source_obligations() == &BTreeSet::from([obligation.id])
                        && statement.space() == MachineAddressSpace::Ram
                        && statement.word_size_bytes() == 1
                        && matches!(statement.width_bits(), 8 | 16 | 32 | 64)
                        && matches!(
                            statement.endianness(),
                            MachineMemoryEndianness::Little | MachineMemoryEndianness::Big
                        )
                        && statement.execution()
                            == CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrder
                        && effect.disposition()
                            == &EffectDisposition::AbsorbedIntoStatement {
                                producer: statement.producer(),
                            }
                        && matches!(
                            (obligation.id.kind, statement.kind()),
                            (
                                SemanticObligationKind::ObservableMemoryRead,
                                CertifiedMemoryStatementKind::Read { .. }
                            ) | (
                                SemanticObligationKind::ObservableMemoryWrite,
                                CertifiedMemoryStatementKind::Write { .. }
                            )
                        )
                })
            }
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
                effect.return_control_evidence() == Some(return_control)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoReturn { producer }
                            if *producer == return_control.producer()
                    )
            }
            _ => false,
        };
        if !valid {
            return Err(LedgerClosureError::InvalidRegionDisposition(obligation.id));
        }
    }
    if memory_count == 0 {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }

    let mappings = mappings.into_iter().collect::<Vec<_>>();
    let mut by_obligation = BTreeMap::<SemanticObligationId, &TypedRegionMapping>::new();
    for mapping in &mappings {
        if !origin
            .source()
            .obligations()
            .contains_key(&mapping.obligation)
        {
            return Err(LedgerClosureError::UnexpectedMapping(mapping.obligation));
        }
        if by_obligation.insert(mapping.obligation, mapping).is_some() {
            return Err(LedgerClosureError::DuplicateMapping(mapping.obligation));
        }
    }
    for obligation in origin.source().obligations().keys() {
        let mapping = by_obligation
            .get(obligation)
            .ok_or(LedgerClosureError::MissingMapping(*obligation))?;
        let [effect] = ledger.effects(*obligation) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        if effect.disposition() != mapping.source_disposition()
            || matches!(
                mapping.source_disposition(),
                EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
            )
        {
            return Err(LedgerClosureError::DispositionMismatch(*obligation));
        }
    }
    Ok(CertifiedLedgerClosure {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::PlainRamMemoryTerminalReturnFunction,
        region_schema_version: CERTIFIED_PLAIN_RAM_MEMORY_RETURN_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

/// Authorize one exact closed two-block function whose entry ends in one
/// certified void direct call and whose sole fallthrough block ends in one
/// terminal return.
///
/// The call target is deliberately outside the function. Its exact source
/// call-site interface, ordered register arguments, and side-effecting call
/// event are retained by the direct-call evidence. Callee behavior and
/// non-void call results are not admitted by this contract.
pub fn certify_direct_call_terminal_return_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    entry_addr: u64,
    return_addr: u64,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    if !origin.is_valid()
        || !ledger.matches_origin(origin)
        || !return_machine_state_matches_origin(origin, ledger)
        || origin
            .machine_context()
            .source()
            .function_interface()
            .is_none_or(|interface| !interface.stack_slots().is_empty())
    {
        return Err(LedgerClosureError::InvalidOrigin);
    }
    let topology = origin.topology();
    let (Some(entry), Some(returned)) = (topology.block(entry_addr), topology.block(return_addr))
    else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    if topology.entry_addr() != entry_addr
        || topology.blocks().len() != 2
        || entry_addr == return_addr
        || !entry.predecessors().is_empty()
        || entry.successors() != [return_addr]
        || returned.predecessors() != [entry_addr]
        || !returned.successors().is_empty()
        || entry.instructions().is_empty()
        || returned.instructions().is_empty()
        || origin.source().instructions().values().any(|instruction| {
            instruction.state == SemanticInstructionState::UnsupportedUnknown
                || matches!(instruction.id.site, r2ssa::CanonicalInstructionSite::Phi(_))
        })
        || origin.source().obligations().values().any(|obligation| {
            !matches!(
                obligation.id.kind,
                SemanticObligationKind::LiveValueProducer
                    | SemanticObligationKind::Call
                    | SemanticObligationKind::CallArgument
                    | SemanticObligationKind::Return
                    | SemanticObligationKind::ReturnValue
            )
        })
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }

    let call_effects = origin
        .source()
        .obligations()
        .values()
        .filter(|obligation| obligation.id.kind == SemanticObligationKind::Call)
        .map(|obligation| ledger.effects(obligation.id))
        .collect::<Vec<_>>();
    let [[call_effect]] = call_effects.as_slice() else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    let Some(call) = call_effect.direct_call_evidence() else {
        return Err(LedgerClosureError::InvalidRegionDisposition(
            call_effect.obligation(),
        ));
    };
    let call_topology_matches = matches!(
        entry.terminator(),
        CertifiedSourceTerminator::Call {
            target,
            fallthrough: Some(fallthrough),
        } if *target == call.target() && *fallthrough == return_addr
    ) && entry.instructions().last() == Some(&call.producer())
        && call.fallthrough() == return_addr
        && call_effect.disposition()
            == &(EffectDisposition::AbsorbedIntoCall {
                producer: call.producer(),
            });
    let source_call = origin
        .machine_context()
        .source()
        .call_site_interface(call.call_site());
    let source_call_matches = source_call.is_some_and(|interface| {
        interface.identity() == call.raw_identity()
            && interface.revision_identity() == call.interface_revision()
            && interface.is_complete()
            && !interface.is_variadic()
            && !interface.is_noreturn()
            && interface.result() == SourceCallResult::Void
            && interface.calling_convention() == call.calling_convention()
            && interface.arguments().len() == call.arguments().len()
            && interface
                .arguments()
                .iter()
                .zip(call.arguments())
                .all(|(source, certified)| {
                    matches!(
                        certified.slot(),
                        CallBoundarySlot::Register { index, storage }
                            if index == source.index() && storage == source.storage()
                    )
                })
    });
    if !call_topology_matches || !source_call_matches {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }

    let return_effects = origin
        .source()
        .obligations()
        .values()
        .filter(|obligation| obligation.id.kind == SemanticObligationKind::Return)
        .map(|obligation| ledger.effects(obligation.id))
        .collect::<Vec<_>>();
    let [[return_effect]] = return_effects.as_slice() else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    let Some(return_control) = return_effect.return_control_evidence() else {
        return Err(LedgerClosureError::InvalidRegionDisposition(
            return_effect.obligation(),
        ));
    };
    let return_matches = matches!(returned.terminator(), CertifiedSourceTerminator::Return)
        && returned.instructions().last() == Some(&return_control.producer())
        && return_effect.disposition()
            == &(EffectDisposition::AbsorbedIntoReturn {
                producer: return_control.producer(),
            })
        && origin
            .machine_context()
            .source()
            .function_interface()
            .is_some_and(|interface| {
                return_control_matches_closure(
                    return_control,
                    interface,
                    ReturnClosureContract::DirectCall,
                )
            });
    if !return_matches {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }

    let report = ledger.audit(origin.source());
    if !report.has_exactly_one_disposition_per_source() || !report.invalid().is_empty() {
        return Err(LedgerClosureError::IncompleteLedger);
    }
    if let Some(obligation) = report.residualized().iter().chain(report.refused()).next() {
        return Err(LedgerClosureError::ResidualOrRefusedObligation(*obligation));
    }
    for obligation in origin.source().obligations().values() {
        let [effect] = ledger.effects(obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let valid = match obligation.id.kind {
            SemanticObligationKind::LiveValueProducer => matches!(
                effect.disposition(),
                EffectDisposition::AbsorbedIntoExpression { .. }
            ),
            SemanticObligationKind::Call | SemanticObligationKind::CallArgument => {
                effect.direct_call_evidence() == Some(call)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoCall { producer }
                            if *producer == call.producer()
                    )
            }
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
                effect.return_control_evidence() == Some(return_control)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoReturn { producer }
                            if *producer == return_control.producer()
                    )
            }
            _ => false,
        };
        if !valid {
            return Err(LedgerClosureError::InvalidRegionDisposition(obligation.id));
        }
    }

    let mappings = mappings.into_iter().collect::<Vec<_>>();
    let mut by_obligation = BTreeMap::<SemanticObligationId, &TypedRegionMapping>::new();
    for mapping in &mappings {
        if !origin
            .source()
            .obligations()
            .contains_key(&mapping.obligation)
        {
            return Err(LedgerClosureError::UnexpectedMapping(mapping.obligation));
        }
        if by_obligation.insert(mapping.obligation, mapping).is_some() {
            return Err(LedgerClosureError::DuplicateMapping(mapping.obligation));
        }
    }
    for obligation in origin.source().obligations().keys() {
        let mapping = by_obligation
            .get(obligation)
            .ok_or(LedgerClosureError::MissingMapping(*obligation))?;
        let [effect] = ledger.effects(*obligation) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        if effect.disposition() != mapping.source_disposition()
            || matches!(
                mapping.source_disposition(),
                EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
            )
        {
            return Err(LedgerClosureError::DispositionMismatch(*obligation));
        }
    }
    Ok(CertifiedLedgerClosure {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::DirectCallTerminalReturnFunction,
        region_schema_version: CERTIFIED_DIRECT_CALL_TERMINAL_RETURN_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

/// Authorize one exact closed three-block conditional-return function.
///
/// The source topology, conditional polarity, both terminal returns, complete
/// ledger, and exact mapping manifest are all checked here. Child block
/// regions cannot independently acquire this whole-function authority.
pub fn certify_conditional_terminal_return_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    header_addr: u64,
    true_addr: u64,
    false_addr: u64,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    if !origin.is_valid()
        || !ledger.matches_origin(origin)
        || !return_machine_state_matches_origin(origin, ledger)
        || origin
            .machine_context()
            .source()
            .function_interface()
            .is_none()
    {
        return Err(LedgerClosureError::InvalidOrigin);
    }
    let topology = origin.topology();
    if topology.entry_addr() != header_addr
        || BTreeSet::from([header_addr, true_addr, false_addr]).len() != 3
        || topology.blocks().len() != 3
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    let header = topology
        .block(header_addr)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    let true_block = topology
        .block(true_addr)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    let false_block = topology
        .block(false_addr)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    if !header.predecessors().is_empty()
        || !matches!(
            header.terminator(),
            CertifiedSourceTerminator::ConditionalBranch {
                true_target,
                false_target,
            } if *true_target == true_addr && *false_target == false_addr
        )
        || header.successors().len() != 2
        || header.successors().iter().copied().collect::<BTreeSet<_>>()
            != BTreeSet::from([true_addr, false_addr])
        || header.instructions().is_empty()
        || true_block.predecessors() != [header_addr]
        || false_block.predecessors() != [header_addr]
        || !matches!(true_block.terminator(), CertifiedSourceTerminator::Return)
        || !matches!(false_block.terminator(), CertifiedSourceTerminator::Return)
        || !true_block.successors().is_empty()
        || !false_block.successors().is_empty()
        || true_block.instructions().is_empty()
        || false_block.instructions().is_empty()
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    if origin.source().instructions().values().any(|instruction| {
        instruction.state == SemanticInstructionState::UnsupportedUnknown
            || matches!(instruction.id.site, r2ssa::CanonicalInstructionSite::Phi(_))
    }) {
        return Err(LedgerClosureError::UnsupportedSourceSemantics(
            origin
                .source()
                .instructions()
                .values()
                .find(|instruction| {
                    instruction.state == SemanticInstructionState::UnsupportedUnknown
                        || matches!(instruction.id.site, r2ssa::CanonicalInstructionSite::Phi(_))
                })
                .expect("checked unsupported instruction")
                .id,
        ));
    }
    if origin.source().obligations().values().any(|obligation| {
        !matches!(
            obligation.id.kind,
            SemanticObligationKind::LiveValueProducer
                | SemanticObligationKind::ControlPredicate
                | SemanticObligationKind::ControlTransfer
                | SemanticObligationKind::Return
                | SemanticObligationKind::ReturnValue
        )
    }) {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    let report = ledger.audit(origin.source());
    if !report.has_exactly_one_disposition_per_source() || !report.invalid().is_empty() {
        return Err(LedgerClosureError::IncompleteLedger);
    }
    if let Some(obligation) = report.residualized().iter().chain(report.refused()).next() {
        return Err(LedgerClosureError::ResidualOrRefusedObligation(*obligation));
    }

    let predicate = origin
        .source()
        .obligations()
        .values()
        .filter(|obligation| obligation.id.kind == SemanticObligationKind::ControlPredicate)
        .collect::<Vec<_>>();
    let transfer = origin
        .source()
        .obligations()
        .values()
        .filter(|obligation| obligation.id.kind == SemanticObligationKind::ControlTransfer)
        .collect::<Vec<_>>();
    let ([predicate], [transfer]) = (predicate.as_slice(), transfer.as_slice()) else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    let ([predicate_effect], [transfer_effect]) =
        (ledger.effects(predicate.id), ledger.effects(transfer.id))
    else {
        return Err(LedgerClosureError::IncompleteLedger);
    };
    let conditional = predicate_effect
        .conditional_control_evidence()
        .filter(|control| transfer_effect.conditional_control_evidence() == Some(*control));
    if conditional.is_none_or(|control| {
        header.instructions().last() != Some(&control.producer())
            || control.true_target() != true_addr
            || control.false_target() != false_addr
            || control.truthiness() != CertifiedControlTruthiness::NonZeroIsTrue
            || control.source_obligations() != BTreeSet::from([predicate.id, transfer.id])
            || predicate_effect.disposition()
                != &EffectDisposition::AbsorbedIntoControl {
                    producer: control.producer(),
                }
            || transfer_effect.disposition()
                != &EffectDisposition::AbsorbedIntoControl {
                    producer: control.producer(),
                }
    }) {
        return Err(LedgerClosureError::InvalidRegionDisposition(predicate.id));
    }

    let interface = origin
        .machine_context()
        .source()
        .function_interface()
        .expect("checked function interface");
    for block in [true_block, false_block] {
        let producer = *block
            .instructions()
            .last()
            .expect("checked nonempty return block");
        let return_obligations = origin
            .source()
            .obligations()
            .values()
            .filter(|obligation| {
                obligation.id.instruction == producer
                    && obligation.id.kind == SemanticObligationKind::Return
            })
            .collect::<Vec<_>>();
        let [return_obligation] = return_obligations.as_slice() else {
            return Err(LedgerClosureError::InvalidRegionTopology);
        };
        let [return_effect] = ledger.effects(return_obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let Some(return_control) = return_effect.return_control_evidence() else {
            return Err(LedgerClosureError::InvalidRegionDisposition(
                return_obligation.id,
            ));
        };
        let return_matches = return_control.producer() == producer
            && return_effect.disposition() == &EffectDisposition::AbsorbedIntoReturn { producer }
            && return_control_matches_closure(
                return_control,
                interface,
                ReturnClosureContract::Conditional,
            );
        if !return_matches {
            return Err(LedgerClosureError::InvalidRegionDisposition(
                return_obligation.id,
            ));
        }
    }

    for obligation in origin.source().obligations().values() {
        let [effect] = ledger.effects(obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let valid = match obligation.id.kind {
            SemanticObligationKind::LiveValueProducer => matches!(
                effect.disposition(),
                EffectDisposition::AbsorbedIntoExpression { .. }
            ),
            SemanticObligationKind::ControlPredicate | SemanticObligationKind::ControlTransfer => {
                matches!(
                    effect.disposition(),
                    EffectDisposition::AbsorbedIntoControl { producer }
                        if producer.block_addr == header_addr
                )
            }
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => matches!(
                effect.disposition(),
                EffectDisposition::AbsorbedIntoReturn { producer }
                    if producer.block_addr == true_addr || producer.block_addr == false_addr
            ),
            _ => false,
        };
        if !valid {
            return Err(LedgerClosureError::InvalidRegionDisposition(obligation.id));
        }
    }

    let mappings = mappings.into_iter().collect::<Vec<_>>();
    let mut by_obligation = BTreeMap::<SemanticObligationId, &TypedRegionMapping>::new();
    for mapping in &mappings {
        if !origin
            .source()
            .obligations()
            .contains_key(&mapping.obligation)
        {
            return Err(LedgerClosureError::UnexpectedMapping(mapping.obligation));
        }
        if by_obligation.insert(mapping.obligation, mapping).is_some() {
            return Err(LedgerClosureError::DuplicateMapping(mapping.obligation));
        }
    }
    for obligation in origin.source().obligations().keys() {
        let mapping = by_obligation
            .get(obligation)
            .ok_or(LedgerClosureError::MissingMapping(*obligation))?;
        let [effect] = ledger.effects(*obligation) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        if effect.disposition() != mapping.source_disposition()
            || matches!(
                mapping.source_disposition(),
                EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
            )
        {
            return Err(LedgerClosureError::DispositionMismatch(*obligation));
        }
    }
    Ok(CertifiedLedgerClosure {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::ConditionalTerminalReturnFunction,
        region_schema_version: CERTIFIED_CONDITIONAL_TERMINAL_RETURN_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

/// Authorize one exact closed switch whose every labeled target is a terminal
/// return block. Selector evidence is a separate requirement: topology alone
/// cannot acquire this permit.
pub fn certify_switch_terminal_return_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    topology_witness: &CertifiedSwitchTopology,
    switch_control: &CertifiedSwitchControl,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    if !origin.is_valid()
        || !ledger.matches_origin(origin)
        || !return_machine_state_matches_origin(origin, ledger)
        || origin
            .machine_context()
            .source()
            .function_interface()
            .is_none()
    {
        return Err(LedgerClosureError::InvalidOrigin);
    }
    if topology_witness.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || switch_control.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || topology_witness.origin() != origin
        || switch_control.origin() != origin
        || switch_control.topology() != topology_witness
        || switch_control.producer() != topology_witness.producer()
        || switch_control.indirect_target() != topology_witness.indirect_target()
        || switch_control.source_obligation() != topology_witness.source_obligation()
        || switch_control.selector().binding().width_bits() == 0
        || switch_control.selector().binding().width_bits() > 64
        || switch_control.validate(origin.source()).is_err()
        || origin
            .machine_context()
            .source()
            .function_interface()
            .is_none_or(|interface| {
                !interface_has_exact_parameter_projection(
                    interface,
                    switch_control.parameter_index(),
                    switch_control.parameter_abi_storage(),
                    switch_control.parameter_graph_storage(),
                    switch_control.parameter_logical_value(),
                )
            })
        || switch_control.parameter_graph_storage().size.checked_mul(8)
            != Some(switch_control.selector().binding().width_bits())
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }

    let topology = origin.topology();
    let header_addr = topology_witness.producer().block_addr;
    let arm_addrs = topology_witness
        .cases()
        .iter()
        .map(|(_, target)| *target)
        .chain([topology_witness.default_target()])
        .collect::<BTreeSet<_>>();
    if topology.entry_addr() != header_addr
        || topology.blocks().len() != arm_addrs.len() + 1
        || arm_addrs.len() != topology_witness.cases().len() + 1
        || arm_addrs.contains(&header_addr)
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    let header = topology
        .block(header_addr)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    if !header.predecessors().is_empty()
        || !matches!(
            header.terminator(),
            CertifiedSourceTerminator::Switch {
                switch_addr,
                terminal_instruction_addr,
                min_value,
                max_value,
                cases,
                default,
            } if *switch_addr == topology_witness.switch_addr()
                && switch_addr == terminal_instruction_addr
                && *min_value == topology_witness.min_value()
                && *max_value == topology_witness.max_value()
                && cases.as_ref() == topology_witness.cases()
                && *default == Some(topology_witness.default_target())
        )
        || header.instructions().last() != Some(&topology_witness.producer())
        || header.successors().iter().copied().collect::<BTreeSet<_>>() != arm_addrs
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    for arm_addr in &arm_addrs {
        let arm = topology
            .block(*arm_addr)
            .ok_or(LedgerClosureError::InvalidRegionTopology)?;
        if arm.predecessors() != [header_addr]
            || !matches!(arm.terminator(), CertifiedSourceTerminator::Return)
            || !arm.successors().is_empty()
            || arm.instructions().is_empty()
        {
            return Err(LedgerClosureError::InvalidRegionTopology);
        }
    }
    if origin.source().instructions().values().any(|instruction| {
        instruction.state == SemanticInstructionState::UnsupportedUnknown
            || matches!(instruction.id.site, r2ssa::CanonicalInstructionSite::Phi(_))
    }) || origin.source().obligations().values().any(|obligation| {
        !matches!(
            obligation.id.kind,
            SemanticObligationKind::LiveValueProducer
                | SemanticObligationKind::ControlTransfer
                | SemanticObligationKind::Return
                | SemanticObligationKind::ReturnValue
        )
    }) {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }

    let report = ledger.audit(origin.source());
    if !report.has_exactly_one_disposition_per_source() || !report.invalid().is_empty() {
        return Err(LedgerClosureError::IncompleteLedger);
    }
    if let Some(obligation) = report.residualized().iter().chain(report.refused()).next() {
        return Err(LedgerClosureError::ResidualOrRefusedObligation(*obligation));
    }
    let [switch_effect] = ledger.effects(topology_witness.source_obligation()) else {
        return Err(LedgerClosureError::IncompleteLedger);
    };
    if switch_effect.switch_control_evidence() != Some(switch_control)
        || switch_effect.disposition()
            != &(EffectDisposition::AbsorbedIntoControl {
                producer: topology_witness.producer(),
            })
    {
        return Err(LedgerClosureError::InvalidRegionDisposition(
            topology_witness.source_obligation(),
        ));
    }

    let interface = origin
        .machine_context()
        .source()
        .function_interface()
        .expect("checked function interface");
    for arm_addr in &arm_addrs {
        let arm = topology
            .block(*arm_addr)
            .expect("checked switch return arm");
        let producer = *arm.instructions().last().expect("checked nonempty arm");
        let returns = origin
            .source()
            .obligations()
            .values()
            .filter(|obligation| {
                obligation.id.instruction == producer
                    && obligation.id.kind == SemanticObligationKind::Return
            })
            .collect::<Vec<_>>();
        let [return_obligation] = returns.as_slice() else {
            return Err(LedgerClosureError::InvalidRegionTopology);
        };
        let [effect] = ledger.effects(return_obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let Some(control) = effect.return_control_evidence() else {
            return Err(LedgerClosureError::InvalidRegionDisposition(
                return_obligation.id,
            ));
        };
        let matches_interface =
            return_control_matches_closure(control, interface, ReturnClosureContract::Switch);
        if control.producer() != producer
            || effect.disposition() != &(EffectDisposition::AbsorbedIntoReturn { producer })
            || !matches_interface
        {
            return Err(LedgerClosureError::InvalidRegionDisposition(
                return_obligation.id,
            ));
        }
    }

    for obligation in origin.source().obligations().values() {
        let [effect] = ledger.effects(obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let valid = match obligation.id.kind {
            SemanticObligationKind::LiveValueProducer => matches!(
                effect.disposition(),
                EffectDisposition::AbsorbedIntoExpression { .. }
            ),
            SemanticObligationKind::ControlTransfer => {
                obligation.id == topology_witness.source_obligation()
                    && effect.switch_control_evidence() == Some(switch_control)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoControl { producer }
                            if *producer == topology_witness.producer()
                    )
            }
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => matches!(
                effect.disposition(),
                EffectDisposition::AbsorbedIntoReturn { producer }
                    if arm_addrs.contains(&producer.block_addr)
            ),
            _ => false,
        };
        if !valid {
            return Err(LedgerClosureError::InvalidRegionDisposition(obligation.id));
        }
    }

    let mappings = mappings.into_iter().collect::<Vec<_>>();
    let mut by_obligation = BTreeMap::<SemanticObligationId, &TypedRegionMapping>::new();
    for mapping in &mappings {
        if !origin
            .source()
            .obligations()
            .contains_key(&mapping.obligation)
        {
            return Err(LedgerClosureError::UnexpectedMapping(mapping.obligation));
        }
        if by_obligation.insert(mapping.obligation, mapping).is_some() {
            return Err(LedgerClosureError::DuplicateMapping(mapping.obligation));
        }
    }
    for obligation in origin.source().obligations().keys() {
        let mapping = by_obligation
            .get(obligation)
            .ok_or(LedgerClosureError::MissingMapping(*obligation))?;
        let [effect] = ledger.effects(*obligation) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        if effect.disposition() != mapping.source_disposition()
            || matches!(
                mapping.source_disposition(),
                EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
            )
        {
            return Err(LedgerClosureError::DispositionMismatch(*obligation));
        }
    }
    Ok(CertifiedLedgerClosure {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::SwitchTerminalReturnFunction,
        region_schema_version: CERTIFIED_SWITCH_TERMINAL_RETURN_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

/// Authorize the exact four-block carrier-free loop function sealed by
/// [`CertifiedClosedNaturalLoopControl`]. The invariant ABI condition may
/// either exit immediately or keep traversing the empty backedge forever; no
/// termination claim is made.
pub fn certify_carrier_free_loop_terminal_return_region(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    loop_control: &CertifiedClosedNaturalLoopControl,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    let Some(interface) = origin.machine_context().source().function_interface() else {
        return Err(LedgerClosureError::InvalidOrigin);
    };
    if !origin.is_valid()
        || !ledger.matches_origin(origin)
        || !return_machine_state_matches_origin(origin, ledger)
        || loop_control.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || loop_control.origin() != origin
        || loop_control.routing().schema_version() != CERTIFICATION_SCHEMA_VERSION
        || loop_control.routing().origin() != origin
        || loop_control.condition().binding().width_bits() != 8
        || loop_control.condition().producer().is_some()
        || loop_control.condition().constant().is_some()
        || loop_control.condition().memory_access().is_some()
        || interface.parameters().len() != 1
        || !interface_has_exact_parameter_projection(
            interface,
            loop_control.parameter_index(),
            loop_control.parameter_abi_storage(),
            loop_control.parameter_graph_storage(),
            loop_control.parameter_logical_value(),
        )
        || loop_control.parameter_graph_storage().size.checked_mul(8)
            != Some(loop_control.condition().binding().width_bits())
    {
        return Err(LedgerClosureError::InvalidOrigin);
    }

    let topology = origin.topology();
    let routing = loop_control.routing();
    let preheader_addr = routing.entry_predecessor();
    let header_addr = routing.header();
    let body_addr = routing.body_latch();
    let exit_addr = routing.exit();
    if topology.entry_addr() != preheader_addr
        || topology.blocks().len() != 4
        || BTreeSet::from([preheader_addr, header_addr, body_addr, exit_addr]).len() != 4
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    let preheader = topology
        .block(preheader_addr)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    let header = topology
        .block(header_addr)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    let body = topology
        .block(body_addr)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    let exit = topology
        .block(exit_addr)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    let continuation_target = if routing.continuation_on_true() {
        routing.header_control().true_target()
    } else {
        routing.header_control().false_target()
    };
    let exit_target = if routing.continuation_on_true() {
        routing.header_control().false_target()
    } else {
        routing.header_control().true_target()
    };
    if !preheader.predecessors().is_empty()
        || preheader.instructions().last() != Some(&loop_control.preheader_transfer().producer())
        || preheader.successors() != [header_addr]
        || !matches!(
            preheader.terminator(),
            CertifiedSourceTerminator::Branch { target } if *target == header_addr
        )
        || loop_control.preheader_transfer().target() != header_addr
        || header.instructions().last() != Some(&routing.header_control().producer())
        || header
            .predecessors()
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            != BTreeSet::from([preheader_addr, body_addr])
        || header.successors().iter().copied().collect::<BTreeSet<_>>()
            != BTreeSet::from([body_addr, exit_addr])
        || continuation_target != body_addr
        || exit_target != exit_addr
        || body.instructions().last() != Some(&routing.body_transfer().producer())
        || body.predecessors() != [header_addr]
        || body.successors() != [header_addr]
        || !matches!(
            body.terminator(),
            CertifiedSourceTerminator::Branch { target } if *target == header_addr
        )
        || routing.body_transfer().target() != header_addr
        || exit.predecessors() != [header_addr]
        || !exit.successors().is_empty()
        || !matches!(exit.terminator(), CertifiedSourceTerminator::Return)
        || exit.instructions().is_empty()
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    if origin.source().instructions().values().any(|instruction| {
        instruction.state == SemanticInstructionState::UnsupportedUnknown
            || matches!(instruction.id.site, CanonicalInstructionSite::Phi(_))
    }) || origin.source().obligations().values().any(|obligation| {
        !matches!(
            obligation.id.kind,
            SemanticObligationKind::LiveValueProducer
                | SemanticObligationKind::ControlPredicate
                | SemanticObligationKind::ControlTransfer
                | SemanticObligationKind::Return
                | SemanticObligationKind::ReturnValue
        ) || (obligation.id.kind == SemanticObligationKind::LiveValueProducer
            && obligation.id.instruction.block_addr != exit_addr)
    }) {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }

    let report = ledger.audit(origin.source());
    if !report.has_exactly_one_disposition_per_source() || !report.invalid().is_empty() {
        return Err(LedgerClosureError::IncompleteLedger);
    }
    if let Some(obligation) = report.residualized().iter().chain(report.refused()).next() {
        return Err(LedgerClosureError::ResidualOrRefusedObligation(*obligation));
    }

    let preheader_obligation = loop_control.preheader_transfer().source_obligation();
    let predicate_obligation = routing.header_control().predicate_obligation();
    let header_transfer_obligation = routing.header_control().transfer_obligation();
    let backedge_obligation = routing.body_transfer().source_obligation();
    if BTreeSet::from([
        preheader_obligation,
        predicate_obligation,
        header_transfer_obligation,
        backedge_obligation,
    ])
    .len()
        != 4
    {
        return Err(LedgerClosureError::InvalidRegionTopology);
    }
    let [preheader_effect] = ledger.effects(preheader_obligation) else {
        return Err(LedgerClosureError::IncompleteLedger);
    };
    let [predicate_effect] = ledger.effects(predicate_obligation) else {
        return Err(LedgerClosureError::IncompleteLedger);
    };
    let [header_transfer_effect] = ledger.effects(header_transfer_obligation) else {
        return Err(LedgerClosureError::IncompleteLedger);
    };
    let [backedge_effect] = ledger.effects(backedge_obligation) else {
        return Err(LedgerClosureError::IncompleteLedger);
    };
    let preheader_producer = loop_control.preheader_transfer().producer();
    let header_producer = routing.header_control().producer();
    let backedge_producer = routing.body_transfer().producer();
    if preheader_effect.direct_control_evidence() != Some(loop_control.preheader_transfer())
        || preheader_effect.disposition()
            != &(EffectDisposition::AbsorbedIntoControl {
                producer: preheader_producer,
            })
        || predicate_effect.conditional_control_evidence() != Some(routing.header_control())
        || header_transfer_effect.conditional_control_evidence() != Some(routing.header_control())
        || predicate_effect.disposition()
            != &(EffectDisposition::AbsorbedIntoControl {
                producer: header_producer,
            })
        || header_transfer_effect.disposition()
            != &(EffectDisposition::AbsorbedIntoControl {
                producer: header_producer,
            })
        || backedge_effect.direct_control_evidence() != Some(routing.body_transfer())
        || backedge_effect.disposition()
            != &(EffectDisposition::AbsorbedIntoControl {
                producer: backedge_producer,
            })
    {
        return Err(LedgerClosureError::InvalidRegionDisposition(
            preheader_obligation,
        ));
    }

    let exit_producer = *exit
        .instructions()
        .last()
        .expect("checked nonempty loop exit");
    let exit_returns = origin
        .source()
        .obligations()
        .values()
        .filter(|obligation| {
            obligation.id.instruction == exit_producer
                && obligation.id.kind == SemanticObligationKind::Return
        })
        .collect::<Vec<_>>();
    let [exit_return] = exit_returns.as_slice() else {
        return Err(LedgerClosureError::InvalidRegionTopology);
    };
    let [exit_return_effect] = ledger.effects(exit_return.id) else {
        return Err(LedgerClosureError::IncompleteLedger);
    };
    let Some(return_control) = exit_return_effect.return_control_evidence() else {
        return Err(LedgerClosureError::InvalidRegionDisposition(exit_return.id));
    };
    let return_matches =
        return_control_matches_closure(return_control, interface, ReturnClosureContract::Loop);
    if return_control.producer() != exit_producer
        || exit_return_effect.disposition()
            != &(EffectDisposition::AbsorbedIntoReturn {
                producer: exit_producer,
            })
        || !return_matches
    {
        return Err(LedgerClosureError::InvalidRegionDisposition(exit_return.id));
    }

    for obligation in origin.source().obligations().values() {
        let [effect] = ledger.effects(obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let valid = match obligation.id.kind {
            SemanticObligationKind::LiveValueProducer => {
                obligation.id.instruction.block_addr == exit_addr
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoExpression { .. }
                    )
            }
            SemanticObligationKind::ControlPredicate => {
                obligation.id == predicate_obligation
                    && effect.conditional_control_evidence() == Some(routing.header_control())
            }
            SemanticObligationKind::ControlTransfer => {
                (obligation.id == preheader_obligation
                    && effect.direct_control_evidence() == Some(loop_control.preheader_transfer()))
                    || (obligation.id == header_transfer_obligation
                        && effect.conditional_control_evidence() == Some(routing.header_control()))
                    || (obligation.id == backedge_obligation
                        && effect.direct_control_evidence() == Some(routing.body_transfer()))
            }
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
                obligation.id.instruction == exit_producer
                    && effect.return_control_evidence() == Some(return_control)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoReturn { producer }
                            if *producer == exit_producer
                    )
            }
            _ => false,
        };
        if !valid {
            return Err(LedgerClosureError::InvalidRegionDisposition(obligation.id));
        }
    }

    let mappings = mappings.into_iter().collect::<Vec<_>>();
    let mut by_obligation = BTreeMap::<SemanticObligationId, &TypedRegionMapping>::new();
    for mapping in &mappings {
        if !origin
            .source()
            .obligations()
            .contains_key(&mapping.obligation)
        {
            return Err(LedgerClosureError::UnexpectedMapping(mapping.obligation));
        }
        if by_obligation.insert(mapping.obligation, mapping).is_some() {
            return Err(LedgerClosureError::DuplicateMapping(mapping.obligation));
        }
    }
    for obligation in origin.source().obligations().keys() {
        let mapping = by_obligation
            .get(obligation)
            .ok_or(LedgerClosureError::MissingMapping(*obligation))?;
        let [effect] = ledger.effects(*obligation) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        if effect.disposition() != mapping.source_disposition()
            || matches!(
                mapping.source_disposition(),
                EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
            )
        {
            return Err(LedgerClosureError::DispositionMismatch(*obligation));
        }
    }
    Ok(CertifiedLedgerClosure {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::CarrierFreeLoopTerminalReturnFunction,
        region_schema_version: CERTIFIED_CARRIER_FREE_LOOP_TERMINAL_RETURN_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

/// Certification owner for one canonical function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedFunction {
    schema_version: u32,
    #[serde(skip_serializing)]
    authority: CertifiedAuthoritySeal,
    source: SemanticObligationInventory,
    ledger: ObligationLedger,
}

impl CertifiedFunction {
    pub fn new(source: SemanticObligationInventory) -> Result<Self, CertificationError> {
        validate_source(&source)?;
        let authority = CertifiedAuthoritySeal::new();
        Ok(Self {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: authority.clone(),
            source,
            ledger: ObligationLedger {
                schema_version: CERTIFICATION_SCHEMA_VERSION,
                authority,
                effects: BTreeMap::new(),
            },
        })
    }

    fn bound(
        source: SemanticObligationInventory,
        origin: &CertifiedArtifactOrigin,
    ) -> Result<Self, CertificationError> {
        validate_source(&source)?;
        Ok(Self {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: origin.authority().clone(),
            source,
            ledger: ObligationLedger::bound(origin),
        })
    }

    pub fn source(&self) -> &SemanticObligationInventory {
        &self.source
    }

    pub fn ledger(&self) -> &ObligationLedger {
        &self.ledger
    }

    // Positive dispositions stay sealed until the typed semantic AST validator
    // can construct proof-bearing output entities.
    #[cfg(test)]
    fn record_rendered(
        &mut self,
        obligation: SemanticObligationId,
        output: CertifiedEntity,
    ) -> Result<(), CertificationError> {
        let effect = CertifiedEffect {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: self.authority.clone(),
            obligation,
            disposition: EffectDisposition::Rendered,
            evidence: DispositionEvidence::Output(output),
        };
        effect.validate(&self.source)?;
        self.ledger.record(effect);
        Ok(())
    }

    fn record_absorbed_expression(
        &mut self,
        obligation: SemanticObligationId,
        expression: CertifiedExpr,
    ) -> Result<(), CertificationError> {
        if obligation.kind != SemanticObligationKind::LiveValueProducer {
            return Err(CertificationError::ObligationNotMapped(obligation));
        }
        let producer = expression.entity().producer();
        let effect = CertifiedEffect {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: self.authority.clone(),
            obligation,
            disposition: EffectDisposition::AbsorbedIntoExpression { producer },
            evidence: DispositionEvidence::Expression(expression),
        };
        effect.validate(&self.source)?;
        self.ledger.record(effect);
        Ok(())
    }

    fn record_absorbed_statement(
        &mut self,
        obligation: SemanticObligationId,
        statement: CertifiedMemoryStatement,
    ) -> Result<(), CertificationError> {
        if !matches!(
            obligation.kind,
            SemanticObligationKind::ObservableMemoryRead
                | SemanticObligationKind::ObservableMemoryWrite
        ) {
            return Err(CertificationError::ObligationNotMapped(obligation));
        }
        let producer = statement.producer();
        let effect = CertifiedEffect {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: self.authority.clone(),
            obligation,
            disposition: EffectDisposition::AbsorbedIntoStatement { producer },
            evidence: DispositionEvidence::Statement(statement),
        };
        effect.validate(&self.source)?;
        self.ledger.record(effect);
        Ok(())
    }

    fn record_absorbed_control(
        &mut self,
        control: CertifiedDirectControl,
    ) -> Result<(), CertificationError> {
        let obligation = control.source_obligation();
        if obligation.kind != SemanticObligationKind::ControlTransfer {
            return Err(CertificationError::ObligationNotMapped(obligation));
        }
        let producer = control.producer();
        let effect = CertifiedEffect {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: self.authority.clone(),
            obligation,
            disposition: EffectDisposition::AbsorbedIntoControl { producer },
            evidence: DispositionEvidence::Control(control),
        };
        effect.validate(&self.source)?;
        self.ledger.record(effect);
        Ok(())
    }

    fn record_absorbed_call(
        &mut self,
        call: CertifiedDirectCall,
    ) -> Result<(), CertificationError> {
        let producer = call.producer();
        for obligation in call.source_obligations() {
            if !matches!(
                obligation.kind,
                SemanticObligationKind::Call | SemanticObligationKind::CallArgument
            ) {
                return Err(CertificationError::ObligationNotMapped(obligation));
            }
            let effect = CertifiedEffect {
                schema_version: CERTIFICATION_SCHEMA_VERSION,
                authority: self.authority.clone(),
                obligation,
                disposition: EffectDisposition::AbsorbedIntoCall { producer },
                evidence: DispositionEvidence::Call(call.clone()),
            };
            effect.validate(&self.source)?;
            self.ledger.record(effect);
        }
        Ok(())
    }

    fn record_absorbed_conditional_control(
        &mut self,
        control: CertifiedConditionalControl,
    ) -> Result<(), CertificationError> {
        let producer = control.producer();
        for obligation in control.source_obligations() {
            if !matches!(
                obligation.kind,
                SemanticObligationKind::ControlPredicate | SemanticObligationKind::ControlTransfer
            ) {
                return Err(CertificationError::ObligationNotMapped(obligation));
            }
            let effect = CertifiedEffect {
                schema_version: CERTIFICATION_SCHEMA_VERSION,
                authority: self.authority.clone(),
                obligation,
                disposition: EffectDisposition::AbsorbedIntoControl { producer },
                evidence: DispositionEvidence::ConditionalControl(control.clone()),
            };
            effect.validate(&self.source)?;
            self.ledger.record(effect);
        }
        Ok(())
    }

    fn record_absorbed_switch_control(
        &mut self,
        control: CertifiedSwitchControl,
    ) -> Result<(), CertificationError> {
        let obligation = control.source_obligation();
        if obligation.kind != SemanticObligationKind::ControlTransfer {
            return Err(CertificationError::ObligationNotMapped(obligation));
        }
        let producer = control.producer();
        let effect = CertifiedEffect {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: self.authority.clone(),
            obligation,
            disposition: EffectDisposition::AbsorbedIntoControl { producer },
            evidence: DispositionEvidence::SwitchControl(Box::new(control)),
        };
        effect.validate(&self.source)?;
        self.ledger.record(effect);
        Ok(())
    }

    fn record_absorbed_return(
        &mut self,
        control: CertifiedReturnControl,
    ) -> Result<(), CertificationError> {
        let producer = control.producer();
        for obligation in control.source_obligations() {
            if !matches!(
                obligation.kind,
                SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
            ) {
                return Err(CertificationError::ObligationNotMapped(obligation));
            }
            let effect = CertifiedEffect {
                schema_version: CERTIFICATION_SCHEMA_VERSION,
                authority: self.authority.clone(),
                obligation,
                disposition: EffectDisposition::AbsorbedIntoReturn { producer },
                evidence: DispositionEvidence::ReturnControl(control.clone()),
            };
            effect.validate(&self.source)?;
            self.ledger.record(effect);
        }
        Ok(())
    }

    pub fn residualize(
        &mut self,
        obligation: SemanticObligationId,
        reason: impl Into<String>,
    ) -> Result<(), CertificationError> {
        self.record_diagnostic(obligation, reason.into(), false)
    }

    pub fn refuse(
        &mut self,
        obligation: SemanticObligationId,
        reason: impl Into<String>,
    ) -> Result<(), CertificationError> {
        self.record_diagnostic(obligation, reason.into(), true)
    }

    fn record_diagnostic(
        &mut self,
        obligation: SemanticObligationId,
        reason: String,
        refused: bool,
    ) -> Result<(), CertificationError> {
        if reason.trim().is_empty() {
            return Err(CertificationError::EmptyReason);
        }
        let disposition = if refused {
            EffectDisposition::Refused { reason }
        } else {
            EffectDisposition::Residualized { reason }
        };
        let effect = CertifiedEffect {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            authority: self.authority.clone(),
            obligation,
            disposition,
            evidence: DispositionEvidence::Diagnostic,
        };
        effect.validate(&self.source)?;
        self.ledger.record(effect);
        Ok(())
    }

    pub fn apply_rewrite(&mut self, certificate: &RewriteCertificate) -> RewriteCertificateReport {
        let report = certificate.audit(&self.source);
        if !report.is_closed() {
            return report;
        }
        for (id, dispositions) in &certificate.dispositions {
            for disposition in dispositions {
                let evidence = if matches!(
                    disposition,
                    EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
                ) {
                    DispositionEvidence::Diagnostic
                } else {
                    DispositionEvidence::Rewrite {
                        schema_version: certificate.schema_version,
                        pass: certificate.pass.clone(),
                    }
                };
                self.ledger.record(CertifiedEffect {
                    schema_version: CERTIFICATION_SCHEMA_VERSION,
                    authority: self.authority.clone(),
                    obligation: *id,
                    disposition: disposition.clone(),
                    evidence,
                });
            }
        }
        report
    }

    pub fn finish(&self) -> CertificationReport {
        let mut report = self.ledger.audit(&self.source);
        if let Err(error) = validate_schema(self.schema_version) {
            push_failure(&mut report, None, format!("{error:?}"));
        }
        report
    }
}

/// One immutable canonical block in the artifact that owns certification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSourceBlock {
    addr: u64,
    predecessors: Box<[u64]>,
    successors: Box<[u64]>,
    terminator: CertifiedSourceTerminator,
    instructions: Box<[CanonicalInstructionId]>,
}

impl CertifiedSourceBlock {
    pub const fn addr(&self) -> u64 {
        self.addr
    }

    pub const fn predecessors(&self) -> &[u64] {
        &self.predecessors
    }

    pub const fn successors(&self) -> &[u64] {
        &self.successors
    }

    pub const fn terminator(&self) -> &CertifiedSourceTerminator {
        &self.terminator
    }

    pub const fn instructions(&self) -> &[CanonicalInstructionId] {
        &self.instructions
    }
}

/// Exact source terminator, retaining branch-arm and switch-case identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedSourceTerminator {
    Fallthrough {
        next: u64,
    },
    Branch {
        target: u64,
    },
    ConditionalBranch {
        true_target: u64,
        false_target: u64,
    },
    IndirectBranch,
    Switch {
        switch_addr: u64,
        terminal_instruction_addr: u64,
        min_value: u64,
        max_value: u64,
        cases: Box<[(u64, u64)]>,
        default: Option<u64>,
    },
    Call {
        target: u64,
        fallthrough: Option<u64>,
    },
    IndirectCall {
        fallthrough: Option<u64>,
    },
    Return,
    None,
}

impl CertifiedSourceTerminator {
    fn from_block(block: &r2ssa::BasicBlock) -> Result<Self, MachineBuildError> {
        Ok(match &block.terminator {
            BlockTerminator::Fallthrough { next } => Self::Fallthrough { next: *next },
            BlockTerminator::Branch { target } => Self::Branch { target: *target },
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => Self::ConditionalBranch {
                true_target: *true_target,
                false_target: *false_target,
            },
            BlockTerminator::IndirectBranch => Self::IndirectBranch,
            BlockTerminator::Switch { cases, default } => {
                let switch = block
                    .switch_info
                    .as_ref()
                    .ok_or(MachineBuildError::TopologyMismatch)?;
                let source_cases = switch
                    .cases
                    .iter()
                    .map(|case| (case.value, case.target))
                    .collect::<Vec<_>>();
                if source_cases != *cases || switch.default_target != *default {
                    return Err(MachineBuildError::TopologyMismatch);
                }
                Self::Switch {
                    switch_addr: switch.switch_addr,
                    terminal_instruction_addr: block
                        .terminal_instruction_addr()
                        .ok_or(MachineBuildError::TopologyMismatch)?,
                    min_value: switch.min_val,
                    max_value: switch.max_val,
                    cases: cases.clone().into_boxed_slice(),
                    default: *default,
                }
            }
            BlockTerminator::Call {
                target,
                fallthrough,
            } => Self::Call {
                target: *target,
                fallthrough: *fallthrough,
            },
            BlockTerminator::IndirectCall { fallthrough } => Self::IndirectCall {
                fallthrough: *fallthrough,
            },
            BlockTerminator::Return => Self::Return,
            BlockTerminator::None => Self::None,
        })
    }
}

/// Artifact-bound source topology, including empty canonical blocks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSourceTopology {
    schema_version: u32,
    entry_addr: u64,
    blocks: Box<[CertifiedSourceBlock]>,
}

impl CertifiedSourceTopology {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn entry_addr(&self) -> u64 {
        self.entry_addr
    }

    pub const fn blocks(&self) -> &[CertifiedSourceBlock] {
        &self.blocks
    }

    pub fn block(&self, addr: u64) -> Option<&CertifiedSourceBlock> {
        self.blocks.iter().find(|block| block.addr == addr)
    }
}

fn certified_artifact_origin(
    trusted: &TrustedSsaArtifact,
    machine_context: &CertifiedMachineContext,
    topology: &CertifiedSourceTopology,
) -> Result<CertifiedArtifactOrigin, MachineBuildError> {
    let authority = CertifiedAuthoritySeal::for_artifact(trusted);
    let artifact = trusted.artifact();
    let lift_authority = trusted.lift_authority();
    let graph = artifact.graph();
    let graph_snapshot = serde_json::to_vec(&(
        graph.entry,
        &graph.block_order,
        &graph.blocks,
        &graph.insts,
        &graph.values,
        &graph.def_of,
        &graph.uses_of,
    ))
    .map_err(|_| MachineBuildError::TopologyMismatch)?;
    if graph_snapshot.is_empty() {
        return Err(MachineBuildError::TopologyMismatch);
    }
    let decompile_preparation = artifact.function().decompile_prep_facts().map(|facts| {
        CertifiedDecompilerPreparationSnapshot {
            canonical_value_roots: facts
                .canonical_value_roots
                .iter()
                .map(|(value, root)| (value.clone(), root.clone()))
                .collect(),
            stack_address_roots: facts
                .stack_address_roots
                .iter()
                .map(|(value, root)| (value.clone(), *root))
                .collect(),
            entry_stack_address_roots: facts
                .entry_stack_address_roots
                .iter()
                .map(|(value, root)| (value.clone(), *root))
                .collect(),
            formal_parameters: facts
                .formal_parameters
                .iter()
                .map(|(value, index)| (value.clone(), *index))
                .collect(),
            formal_parameter_bases: facts
                .formal_parameter_bases
                .iter()
                .map(|(value, index)| (value.clone(), *index))
                .collect(),
        }
    });
    Ok(CertifiedArtifactOrigin {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        lift_provenance_schema_version: lift_authority.lift_authority().schema_version(),
        lift_manifest_hash: lift_authority.source_manifest_hash(),
        authority,
        graph_snapshot: graph_snapshot.into_boxed_slice(),
        prepare_mode: artifact.mode().into(),
        decompile_preparation,
        assumptions: artifact.facts().assumptions.clone(),
        machine_context: machine_context.clone(),
        source: artifact.obligations().clone(),
        topology: topology.clone(),
    })
}

fn certified_direct_calls(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
) -> Result<BTreeMap<CanonicalInstructionId, CertifiedDirectCall>, MachineBuildError> {
    let graph = artifact.graph();
    let cfg = artifact.function().cfg();
    let mut calls = BTreeMap::new();
    for block in topology.blocks() {
        let CertifiedSourceTerminator::Call {
            target,
            fallthrough: Some(fallthrough),
        } = block.terminator()
        else {
            continue;
        };
        if *target == block.addr()
            || *target == *fallthrough
            || *fallthrough == block.addr()
            || topology.block(*fallthrough).is_none()
            || block.successors() != [*fallthrough]
        {
            continue;
        }
        let Some(producer) = block.instructions().last().copied() else {
            continue;
        };
        if has_earlier_terminal_control(artifact.obligations(), block) {
            continue;
        }
        let Some(disposition) = artifact.obligations().instructions().get(&producer) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(inst_id) = disposition.source.graph_inst() else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(inst) = graph.inst(inst_id) else {
            return Err(MachineBuildError::MissingInstruction(inst_id));
        };
        let Some((block_addr, op_index)) = graph.op_site_for_inst(inst.id) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(source_block) = cfg.get_block(block.addr()) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let raw_target = source_block.ops.get(op_index).and_then(|op| match op {
            r2il::R2ILOp::Call { target: raw_target }
                if matches!(raw_target.space, r2il::SpaceId::Ram | r2il::SpaceId::Const)
                    && raw_target.offset == *target =>
            {
                Some(raw_target)
            }
            _ => None,
        });
        let Some(call_site_id) = artifact.call_sites().by_inst.get(&inst.id).copied() else {
            continue;
        };
        let Some(call_site) = artifact.call_sites().by_id.get(&call_site_id) else {
            continue;
        };
        let Some(raw_identity) = call_site.raw_identity else {
            continue;
        };
        let Some(interface) = artifact.machine_context().call_site_interface(call_site_id) else {
            continue;
        };
        let Some(boundary) = artifact.facts().boundaries.calls.get(&call_site_id) else {
            continue;
        };
        if disposition.state != SemanticInstructionState::LiveObligation
            || block_addr != block.addr()
            || op_index + 1 != source_block.ops.len()
            || raw_target.is_none()
            || !matches!(inst.payload, InstPayload::Op(SSAOp::Call { .. }))
            || inst.inputs.len() != 1
            || call_site.at != inst.id
            || call_site.raw_identity != Some(interface.identity())
            || raw_identity != interface.identity()
            || call_site.direct_target != Some(*target)
            || call_site.fallthrough != Some(*fallthrough)
            || !interface.is_complete()
            || interface.is_variadic()
            || interface.is_noreturn()
            || !matches!(interface.result(), SourceCallResult::Void)
            || !boundary.complete
            || boundary.call_site != call_site_id
            || boundary.at != inst.id
            || boundary.calling_convention.as_deref() != Some(interface.calling_convention())
            || boundary.variadic != Some(false)
            || boundary.noreturn != Some(false)
            || boundary.result_kind != Some(SourceCallResult::Void)
            || !boundary.results.is_empty()
            || boundary.arguments.len() != interface.arguments().len()
        {
            continue;
        }
        let raw_target = raw_target.expect("checked direct call target");
        let Some(target_bits) = raw_target.size.checked_mul(8).filter(|bits| *bits != 0) else {
            continue;
        };
        let memory_model = artifact.machine_context().memory_model();
        if (memory_model.is_available()
            && (memory_model.default_address_bits() == 0
                || target_bits != memory_model.default_address_bits()))
            || (target_bits < 64 && *target >= (1_u64 << target_bits))
        {
            continue;
        }
        let target_value = MachineValueUse::from_artifact(artifact, inst.inputs[0])?;
        if target_value.binding().width_bits() != target_bits
            || match raw_target.space {
                r2il::SpaceId::Const => target_value.constant().is_none_or(|constant| {
                    constant.width_bits() != target_bits || constant.bits() != *target
                }),
                r2il::SpaceId::Ram => target_value.constant().is_some(),
                _ => true,
            }
        {
            continue;
        }
        let arguments = boundary
            .arguments
            .iter()
            .zip(interface.arguments())
            .enumerate()
            .map(|(position, (value, expected))| {
                let CallBoundarySlot::Register { index, storage } = value.slot else {
                    return Err(MachineBuildError::ObligationMismatch(inst.id));
                };
                if u32::try_from(position) != Ok(index)
                    || index != expected.index()
                    || storage != expected.storage()
                {
                    return Err(MachineBuildError::ObligationMismatch(inst.id));
                }
                let value_use = MachineValueUse::from_artifact(artifact, value.value)?;
                if value_use.binding().width_bits()
                    != storage
                        .size
                        .checked_mul(8)
                        .ok_or(MachineBuildError::ObligationMismatch(inst.id))?
                {
                    return Err(MachineBuildError::ObligationMismatch(inst.id));
                }
                let origin = call_argument_origin_before_boundary(
                    artifact, block, producer, storage, &value_use,
                )
                .ok_or(MachineBuildError::ObligationMismatch(inst.id))?;
                Ok(CertifiedCallArgument {
                    slot: value.slot,
                    value: value_use,
                    origin,
                    source_obligation: SemanticObligationId {
                        instruction: producer,
                        kind: SemanticObligationKind::CallArgument,
                        component: SemanticObligationComponent::RegisterSlot { index, storage },
                    },
                })
            })
            .collect::<Result<Vec<_>, MachineBuildError>>()?;
        let call_obligation = SemanticObligationId {
            instruction: producer,
            kind: SemanticObligationKind::Call,
            component: SemanticObligationComponent::Whole,
        };
        let expected_obligations = std::iter::once(call_obligation)
            .chain(
                arguments
                    .iter()
                    .map(CertifiedCallArgument::source_obligation),
            )
            .collect::<BTreeSet<_>>();
        if disposition.obligations != expected_obligations {
            continue;
        }
        let call = CertifiedDirectCall {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            producer,
            source_inst: inst.id,
            call_site: call_site_id,
            raw_identity,
            interface_revision: interface.revision_identity().to_vec().into_boxed_slice(),
            target: *target,
            fallthrough: *fallthrough,
            target_value,
            calling_convention: interface.calling_convention().to_string(),
            arguments: arguments.into_boxed_slice(),
            call_obligation,
        };
        call.validate(artifact.obligations())
            .map_err(|_| MachineBuildError::ObligationMismatch(inst.id))?;
        if calls.insert(producer, call).is_some() {
            return Err(MachineBuildError::ObligationMismatch(inst.id));
        }
    }
    Ok(calls)
}

fn call_argument_origin_before_boundary(
    artifact: &SsaArtifact,
    block: &CertifiedSourceBlock,
    call_producer: CanonicalInstructionId,
    storage: CanonicalStorageId,
    value: &MachineValueUse,
) -> Option<CertifiedCallArgumentOrigin> {
    if let Some(constant) = value.constant() {
        return Some(CertifiedCallArgumentOrigin::Constant { value: constant });
    }
    if let Some(producer) = value.producer() {
        let call_position = block
            .instructions()
            .iter()
            .position(|candidate| *candidate == call_producer)?;
        let producer_is_before_call = block
            .instructions()
            .iter()
            .position(|candidate| *candidate == producer)
            .is_some_and(|position| position < call_position);
        if !producer_is_before_call {
            return None;
        }
        let source_inst = artifact
            .obligations()
            .instructions()
            .get(&producer)
            .and_then(|instruction| instruction.source.graph_inst())
            .and_then(|instruction| artifact.graph().inst(instruction));
        if let Some(source_inst) = source_inst
            && matches!(source_inst.payload, InstPayload::Op(SSAOp::Copy { .. }))
            && let [input] = source_inst.inputs.as_slice()
        {
            let input = MachineValueUse::from_artifact(artifact, *input).ok()?;
            if let Some(constant) = input.constant() {
                return Some(CertifiedCallArgumentOrigin::Constant { value: constant });
            }
            if input.producer().is_none() {
                let matching = artifact
                    .facts()
                    .boundaries
                    .parameters
                    .iter()
                    .filter_map(|(index, parameter)| {
                        (parameter.abi_storage == storage
                            && parameter.value == input.binding().value())
                        .then_some(*index)
                    })
                    .collect::<Vec<_>>();
                if let [index] = matching.as_slice() {
                    return Some(CertifiedCallArgumentOrigin::AbiParameter { index: *index });
                }
            }
        }
        return Some(CertifiedCallArgumentOrigin::Produced { producer });
    }
    let matching = artifact
        .facts()
        .boundaries
        .parameters
        .iter()
        .filter_map(|(index, parameter)| {
            (parameter.abi_storage == storage && parameter.value == value.binding().value())
                .then_some(*index)
        })
        .collect::<Vec<_>>();
    let [index] = matching.as_slice() else {
        return None;
    };
    Some(CertifiedCallArgumentOrigin::AbiParameter { index: *index })
}

fn certified_direct_controls(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
) -> Result<BTreeMap<CanonicalInstructionId, CertifiedDirectControl>, MachineBuildError> {
    let graph = artifact.graph();
    let cfg = artifact.function().cfg();
    let mut controls = BTreeMap::new();
    for block in topology.blocks() {
        let CertifiedSourceTerminator::Branch { target } = block.terminator() else {
            continue;
        };
        if *target == block.addr()
            || topology.block(*target).is_none()
            || block.successors() != [*target]
        {
            continue;
        }
        let Some(producer) = block.instructions().last().copied() else {
            continue;
        };
        if has_earlier_terminal_control(artifact.obligations(), block) {
            continue;
        }
        let Some(disposition) = artifact.obligations().instructions().get(&producer) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(inst_id) = disposition.source.graph_inst() else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(inst) = graph.inst(inst_id) else {
            return Err(MachineBuildError::MissingInstruction(inst_id));
        };
        let Some((block_addr, op_index)) = graph.op_site_for_inst(inst.id) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(source_block) = cfg.get_block(block.addr()) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let raw_target = source_block.ops.get(op_index).and_then(|op| match op {
            r2il::R2ILOp::Branch { target: raw_target }
                if matches!(raw_target.space, r2il::SpaceId::Ram | r2il::SpaceId::Const)
                    && raw_target.offset == *target =>
            {
                Some(raw_target)
            }
            _ => None,
        });
        if disposition.state != SemanticInstructionState::LiveObligation
            || block_addr != block.addr()
            || op_index + 1 != source_block.ops.len()
            || raw_target.is_none()
            || !matches!(inst.payload, InstPayload::Op(SSAOp::Branch { .. }))
            || inst.inputs.len() != 1
        {
            continue;
        }
        let raw_target = raw_target.expect("checked direct target");
        let Some(target_bits) = raw_target.size.checked_mul(8).filter(|bits| *bits != 0) else {
            continue;
        };
        let memory_model = artifact.machine_context().memory_model();
        let target_matches_available_arch = raw_target.space == r2il::SpaceId::Const
            || !memory_model.is_available()
            || (memory_model.default_address_bits() != 0
                && target_bits == memory_model.default_address_bits());
        if !target_matches_available_arch || (target_bits < 64 && *target >= (1_u64 << target_bits))
        {
            continue;
        }
        let obligation = SemanticObligationId {
            instruction: producer,
            kind: SemanticObligationKind::ControlTransfer,
            component: SemanticObligationComponent::Whole,
        };
        if disposition.obligations != BTreeSet::from([obligation])
            || artifact
                .obligations()
                .obligations()
                .get(&obligation)
                .is_none_or(|source| {
                    source.source.graph_inst() != Some(inst.id)
                        || source.inputs.as_slice() != inst.inputs
                })
        {
            continue;
        }
        let target_value = MachineValueUse::from_artifact(artifact, inst.inputs[0])?;
        if target_value.binding().width_bits() != target_bits
            || (raw_target.space == r2il::SpaceId::Const
                && target_value.constant().is_none_or(|constant| {
                    constant.width_bits() != target_bits || constant.bits() != *target
                }))
        {
            continue;
        }
        let control = CertifiedDirectControl {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            producer,
            source_inst: inst.id,
            target: *target,
            target_value,
            source_obligation: obligation,
        };
        control
            .validate(artifact.obligations())
            .map_err(|_| MachineBuildError::ObligationMismatch(inst.id))?;
        if controls.insert(producer, control).is_some() {
            return Err(MachineBuildError::ObligationMismatch(inst.id));
        }
    }
    Ok(controls)
}

fn certified_conditional_controls(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
) -> Result<BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>, MachineBuildError> {
    let graph = artifact.graph();
    let cfg = artifact.function().cfg();
    let mut controls = BTreeMap::new();
    for block in topology.blocks() {
        let CertifiedSourceTerminator::ConditionalBranch {
            true_target,
            false_target,
        } = block.terminator()
        else {
            continue;
        };
        let expected_successors = BTreeSet::from([*true_target, *false_target]);
        if true_target == false_target
            || *true_target == block.addr()
            || *false_target == block.addr()
            || topology.block(*true_target).is_none()
            || topology.block(*false_target).is_none()
            || block.successors().iter().copied().collect::<BTreeSet<_>>() != expected_successors
            || block.successors().len() != 2
        {
            continue;
        }
        let Some(producer) = block.instructions().last().copied() else {
            continue;
        };
        if has_earlier_terminal_control(artifact.obligations(), block) {
            continue;
        }
        let Some(disposition) = artifact.obligations().instructions().get(&producer) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(inst_id) = disposition.source.graph_inst() else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(inst) = graph.inst(inst_id) else {
            return Err(MachineBuildError::MissingInstruction(inst_id));
        };
        let Some((block_addr, op_index)) = graph.op_site_for_inst(inst.id) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(source_block) = cfg.get_block(block.addr()) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let raw = source_block.ops.get(op_index).and_then(|op| match op {
            r2il::R2ILOp::CBranch { target, cond }
                if matches!(target.space, r2il::SpaceId::Ram | r2il::SpaceId::Const)
                    && target.offset == *true_target =>
            {
                Some((target, cond))
            }
            _ => None,
        });
        let false_target_matches =
            block.addr().checked_add(u64::from(source_block.size)) == Some(*false_target);
        if disposition.state != SemanticInstructionState::LiveObligation
            || block_addr != block.addr()
            || op_index + 1 != source_block.ops.len()
            || raw.is_none()
            || !false_target_matches
            || !matches!(inst.payload, InstPayload::Op(SSAOp::CBranch { .. }))
            || inst.inputs.len() != 2
        {
            continue;
        }
        let (raw_target, raw_condition) = raw.expect("checked conditional source");
        let Some(target_bits) = raw_target.size.checked_mul(8).filter(|bits| *bits != 0) else {
            continue;
        };
        let Some(condition_bits) = raw_condition.size.checked_mul(8).filter(|bits| *bits == 8)
        else {
            continue;
        };
        let memory_model = artifact.machine_context().memory_model();
        let target_matches_available_arch = raw_target.space == r2il::SpaceId::Const
            || !memory_model.is_available()
            || (memory_model.default_address_bits() != 0
                && target_bits == memory_model.default_address_bits());
        if !target_matches_available_arch
            || (target_bits < 64
                && (*true_target >= (1_u64 << target_bits)
                    || *false_target >= (1_u64 << target_bits)))
        {
            continue;
        }
        let predicate_obligation = SemanticObligationId {
            instruction: producer,
            kind: SemanticObligationKind::ControlPredicate,
            component: SemanticObligationComponent::Whole,
        };
        let transfer_obligation = SemanticObligationId {
            instruction: producer,
            kind: SemanticObligationKind::ControlTransfer,
            component: SemanticObligationComponent::Whole,
        };
        if disposition.obligations != BTreeSet::from([predicate_obligation, transfer_obligation]) {
            continue;
        }
        let target_value = MachineValueUse::from_artifact(artifact, inst.inputs[0])?;
        let condition = MachineValueUse::from_artifact(artifact, inst.inputs[1])?;
        if target_value.binding().width_bits() != target_bits
            || condition.binding().width_bits() != condition_bits
            || (raw_target.space == r2il::SpaceId::Const
                && target_value.constant().is_none_or(|constant| {
                    constant.width_bits() != target_bits || constant.bits() != *true_target
                }))
        {
            continue;
        }
        let control = CertifiedConditionalControl {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            producer,
            source_inst: inst.id,
            true_target: *true_target,
            false_target: *false_target,
            target_value,
            condition,
            truthiness: CertifiedControlTruthiness::NonZeroIsTrue,
            predicate_obligation,
            transfer_obligation,
        };
        control
            .validate(artifact.obligations())
            .map_err(|_| MachineBuildError::ObligationMismatch(inst.id))?;
        if controls.insert(producer, control).is_some() {
            return Err(MachineBuildError::ObligationMismatch(inst.id));
        }
    }
    Ok(controls)
}

fn certified_return_controls(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
) -> Result<BTreeMap<CanonicalInstructionId, CertifiedReturnControl>, MachineBuildError> {
    let graph = artifact.graph();
    let cfg = artifact.function().cfg();
    let mut returns = BTreeMap::new();
    for block in topology.blocks() {
        if !matches!(block.terminator(), CertifiedSourceTerminator::Return) {
            continue;
        }
        let Some(producer) = block.instructions().last().copied() else {
            continue;
        };
        if has_earlier_terminal_control(artifact.obligations(), block) {
            continue;
        }
        let disposition = artifact
            .obligations()
            .instructions()
            .get(&producer)
            .ok_or(MachineBuildError::TopologyMismatch)?;
        let inst_id = disposition
            .source
            .graph_inst()
            .ok_or(MachineBuildError::TopologyMismatch)?;
        let inst = graph
            .inst(inst_id)
            .ok_or(MachineBuildError::MissingInstruction(inst_id))?;
        let (block_addr, op_index) = graph
            .op_site_for_inst(inst.id)
            .ok_or(MachineBuildError::TopologyMismatch)?;
        let source_block = cfg
            .get_block(block.addr())
            .ok_or(MachineBuildError::TopologyMismatch)?;
        let raw_target = source_block.ops.get(op_index).and_then(|op| match op {
            r2il::R2ILOp::Return { target } => Some(target),
            _ => None,
        });
        let boundary = artifact.facts().boundaries.returns.get(&inst.id);
        if disposition.state != SemanticInstructionState::LiveObligation
            || block_addr != block.addr()
            || op_index + 1 != source_block.ops.len()
            || raw_target.is_none()
            || !matches!(inst.payload, InstPayload::Op(SSAOp::Return { .. }))
            || inst.inputs.len() != 1
            || boundary.is_none_or(|boundary| !boundary.complete)
        {
            continue;
        }
        let raw_target = raw_target.expect("checked raw return");
        let target_bits = raw_target
            .size
            .checked_mul(8)
            .filter(|width| *width > 0)
            .ok_or(MachineBuildError::InvalidValueWidth {
                value: inst.inputs[0],
                size_bytes: raw_target.size,
            })?;
        let control_target = MachineValueUse::from_artifact(artifact, inst.inputs[0])?;
        if control_target.binding().width_bits() != target_bits {
            continue;
        }
        let boundary = boundary.expect("checked complete return boundary");
        // The carriers holding the return address and the stack pointer are
        // machine facts, so a return's exit state is provable without an ABI.
        // What the return *carries* remains an ABI question and is certified
        // separately.
        let (Some(return_address_storage), Some(stack_pointer_storage)) = (
            artifact.machine_context().return_address_carrier(),
            artifact.machine_context().stack_pointer_carrier(),
        ) else {
            continue;
        };
        let Some(return_address_fact) = boundary.return_address else {
            continue;
        };
        if return_address_fact.storage != return_address_storage
            || return_address_fact.value != inst.inputs[0]
        {
            continue;
        }
        let return_address = CertifiedReturnAddress {
            storage: return_address_fact.storage,
            value: MachineValueUse::from_artifact(artifact, return_address_fact.value)?,
        };
        let exit_stack_pointer = match boundary.exit_stack_pointer {
            Some(SourceReturnStackPointerFact::PreservedEntry { storage })
                if storage == stack_pointer_storage =>
            {
                CertifiedExitStackPointer::PreservedEntry { storage }
            }
            Some(SourceReturnStackPointerFact::ReachingValue { storage, value })
                if storage == stack_pointer_storage =>
            {
                CertifiedExitStackPointer::ReachingValue {
                    storage,
                    value: MachineValueUse::from_artifact(artifact, value)?,
                }
            }
            _ => continue,
        };
        let Some(CertifiedReturnShapes {
            values,
            register_compositions,
        }) = certified_return_shapes(artifact, inst.id, producer, boundary)?
        else {
            continue;
        };
        let return_obligation = SemanticObligationId {
            instruction: producer,
            kind: SemanticObligationKind::Return,
            component: SemanticObligationComponent::Whole,
        };
        let expected_obligations = std::iter::once(return_obligation)
            .chain(values.iter().map(|value| value.source_obligation))
            .chain(
                register_compositions
                    .iter()
                    .map(|composition| composition.source_obligation),
            )
            .collect::<BTreeSet<_>>();
        if disposition.obligations != expected_obligations {
            continue;
        }
        let control = CertifiedReturnControl {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            producer,
            source_inst: inst.id,
            control_target,
            return_address,
            exit_stack_pointer,
            values: values.into_boxed_slice(),
            register_compositions: register_compositions.into_boxed_slice(),
            return_obligation,
        };
        control
            .validate(artifact.obligations())
            .map_err(|_| MachineBuildError::ObligationMismatch(inst.id))?;
        if returns.insert(producer, control).is_some() {
            return Err(MachineBuildError::ObligationMismatch(inst.id));
        }
    }
    Ok(returns)
}

struct CertifiedReturnShapes {
    values: Vec<CertifiedReturnValue>,
    register_compositions: Vec<CertifiedReturnRegisterComposition>,
}

fn certified_return_shapes(
    artifact: &SsaArtifact,
    boundary_at: InstId,
    return_producer: CanonicalInstructionId,
    boundary: &SourceReturnBoundaryFact,
) -> Result<Option<CertifiedReturnShapes>, MachineBuildError> {
    let machine_context = artifact.machine_context();
    let expected_slots = machine_context
        .abi_model()
        .return_registers()
        .iter()
        .map(|slot| CallBoundarySlot::Register {
            index: slot.index(),
            storage: slot.storage(),
        })
        .collect::<BTreeSet<_>>();
    let supplied_slots = boundary
        .values
        .iter()
        .map(|value| value.slot)
        .chain(
            boundary
                .register_compositions
                .iter()
                .map(|composition| composition.slot),
        )
        .collect::<BTreeSet<_>>();
    let supplied_count = boundary
        .values
        .len()
        .saturating_add(boundary.register_compositions.len());
    if !boundary.complete
        || boundary.at != boundary_at
        || !machine_context.abi_model().is_available()
        || !machine_context.abi_model().is_coherent()
        || supplied_slots.len() != supplied_count
        || supplied_slots != expected_slots
    {
        return Ok(None);
    }

    let mut values = Vec::with_capacity(boundary.values.len());
    for fact in &boundary.values {
        let CallBoundarySlot::Register { storage, .. } = fact.slot else {
            return Ok(None);
        };
        let Some(graph_value) = artifact.graph().value(fact.value) else {
            return Ok(None);
        };
        let value = MachineValueUse::from_artifact(artifact, fact.value)?;
        if storage.space != CanonicalStorageSpace::Register
            || storage.size == 0
            || graph_value.canonical_storage != Some(storage)
            || storage.size.checked_mul(8) != Some(value.binding().width_bits())
        {
            return Ok(None);
        }
        values.push(CertifiedReturnValue {
            slot: fact.slot,
            value,
            source_obligation: SemanticObligationId {
                instruction: return_producer,
                kind: SemanticObligationKind::ReturnValue,
                component: return_component(fact.slot),
            },
        });
    }

    let mut register_compositions = Vec::with_capacity(boundary.register_compositions.len());
    for fact in &boundary.register_compositions {
        let Some(composition) =
            certified_return_register_composition(artifact, boundary_at, return_producer, fact)?
        else {
            return Ok(None);
        };
        register_compositions.push(composition);
    }
    Ok(Some(CertifiedReturnShapes {
        values,
        register_compositions,
    }))
}

fn certified_return_register_definition(
    artifact: &SsaArtifact,
    fact: SourceReturnRegisterDefinitionFact,
) -> Result<Option<CertifiedReturnRegisterDefinition>, MachineBuildError> {
    let Some(inst) = artifact.graph().inst(fact.producer) else {
        return Ok(None);
    };
    let Some(disposition) = artifact.obligations().instruction_for_inst(fact.producer) else {
        return Ok(None);
    };
    let value = MachineValueUse::from_artifact(artifact, fact.value)?;
    if fact.storage.space != CanonicalStorageSpace::Register
        || fact.storage.size == 0
        || inst.output != Some(fact.value)
        || inst.canonical_storage != Some(fact.storage)
        || fact.storage.size.checked_mul(8) != Some(value.binding().width_bits())
        || value.producer() != Some(disposition.id)
    {
        return Ok(None);
    }
    Ok(Some(CertifiedReturnRegisterDefinition {
        storage: fact.storage,
        value,
        producer: disposition.id,
    }))
}

fn certified_return_register_composition(
    artifact: &SsaArtifact,
    boundary_at: InstId,
    return_producer: CanonicalInstructionId,
    fact: &SourceReturnRegisterCompositionFact,
) -> Result<Option<CertifiedReturnRegisterComposition>, MachineBuildError> {
    if !fact.validate(
        artifact.function(),
        artifact.graph(),
        artifact.machine_context(),
        boundary_at,
    ) {
        return Ok(None);
    }
    let CallBoundarySlot::Register { storage, .. } = fact.slot else {
        return Ok(None);
    };
    let Some(base) = certified_return_register_definition(artifact, fact.base)? else {
        return Ok(None);
    };
    if base.storage != storage
        || storage.size.checked_mul(8) != Some(base.value.binding().width_bits())
    {
        return Ok(None);
    }
    let mut overlays = Vec::with_capacity(fact.overlays.len());
    for overlay in &fact.overlays {
        let Some(definition) = certified_return_register_definition(artifact, overlay.definition)?
        else {
            return Ok(None);
        };
        let Some(end) = overlay.offset_bytes.checked_add(definition.storage.size) else {
            return Ok(None);
        };
        if storage.offset.checked_add(u64::from(overlay.offset_bytes))
            != Some(definition.storage.offset)
            || end > storage.size
        {
            return Ok(None);
        }
        overlays.push(CertifiedReturnRegisterOverlay {
            definition,
            offset_bytes: overlay.offset_bytes,
        });
    }
    Ok(Some(CertifiedReturnRegisterComposition {
        slot: fact.slot,
        base,
        overlays: overlays.into_boxed_slice(),
        source_obligation: SemanticObligationId {
            instruction: return_producer,
            kind: SemanticObligationKind::ReturnValue,
            component: return_component(fact.slot),
        },
    }))
}

fn has_earlier_terminal_control(
    source: &SemanticObligationInventory,
    block: &CertifiedSourceBlock,
) -> bool {
    let earlier_count = block.instructions().len().saturating_sub(1);
    block
        .instructions()
        .iter()
        .take(earlier_count)
        .filter_map(|producer| source.instructions().get(producer))
        .flat_map(|instruction| instruction.obligations.iter())
        .any(|obligation| {
            matches!(
                obligation.kind,
                SemanticObligationKind::Return
                    | SemanticObligationKind::ControlTransfer
                    | SemanticObligationKind::Trap
            )
        })
}

fn certified_switch_topologies(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
) -> Result<BTreeMap<u64, CertifiedSwitchTopology>, MachineBuildError> {
    let graph = artifact.graph();
    let source = artifact.obligations();
    let mut switches = BTreeMap::new();
    for block in topology.blocks() {
        let CertifiedSourceTerminator::Switch {
            switch_addr,
            terminal_instruction_addr,
            min_value,
            max_value,
            cases,
            default,
        } = block.terminator()
        else {
            continue;
        };
        let Some(default_target) = *default else {
            continue;
        };
        let case_values = cases
            .iter()
            .map(|(value, _)| *value)
            .collect::<BTreeSet<_>>();
        let targets = cases
            .iter()
            .map(|(_, target)| *target)
            .chain([default_target])
            .collect::<BTreeSet<_>>();
        if cases.is_empty()
            || switch_addr != terminal_instruction_addr
            || min_value > max_value
            || cases
                .iter()
                .any(|(value, _)| value < min_value || value > max_value)
            || case_values.len() != cases.len()
            || targets.len() != cases.len() + 1
            || targets.contains(&block.addr())
            || targets
                .iter()
                .any(|target| topology.block(*target).is_none())
            || block.successors().len() != targets.len()
            || block.successors().iter().copied().collect::<BTreeSet<_>>() != targets
        {
            continue;
        }
        let Some(producer) = block.instructions().last().copied() else {
            continue;
        };
        if has_earlier_terminal_control(source, block) {
            continue;
        }
        let Some(disposition) = source.instructions().get(&producer) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(inst_id) = disposition.source.graph_inst() else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(instruction) = graph.inst(inst_id) else {
            return Err(MachineBuildError::MissingInstruction(inst_id));
        };
        let Some((block_addr, op_index)) = graph.op_site_for_inst(instruction.id) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let Some(source_block) = artifact.function().get_block(block.addr()) else {
            return Err(MachineBuildError::TopologyMismatch);
        };
        let obligation = SemanticObligationId {
            instruction: producer,
            kind: SemanticObligationKind::ControlTransfer,
            component: SemanticObligationComponent::Whole,
        };
        if block_addr != block.addr()
            || op_index + 1 != source_block.ops.len()
            || !matches!(
                instruction.payload,
                InstPayload::Op(SSAOp::BranchInd { .. })
            )
            || instruction.inputs.len() != 1
            || disposition.state != SemanticInstructionState::LiveObligation
            || disposition.obligations != BTreeSet::from([obligation])
            || source.obligations().get(&obligation).is_none_or(|fact| {
                fact.source.graph_inst() != Some(instruction.id)
                    || fact.inputs != instruction.inputs
            })
        {
            continue;
        }
        let indirect_target = MachineValueUse::from_artifact(artifact, instruction.inputs[0])?;
        let memory_model = artifact.machine_context().memory_model();
        let target_bits = indirect_target.binding().width_bits();
        if memory_model.is_available()
            && (memory_model.default_address_bits() == 0
                || target_bits != memory_model.default_address_bits())
        {
            continue;
        }
        if target_bits == 0
            || (target_bits < 64
                && (switch_addr >= &(1_u64 << target_bits)
                    || targets
                        .iter()
                        .any(|target| *target >= (1_u64 << target_bits))))
        {
            continue;
        }
        let witness = CertifiedSwitchTopology {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            origin: origin.clone(),
            producer,
            source_inst: instruction.id,
            indirect_target,
            switch_addr: *switch_addr,
            min_value: *min_value,
            max_value: *max_value,
            cases: cases.clone(),
            default_target,
            source_obligation: obligation,
        };
        if switches.insert(block.addr(), witness).is_some() {
            return Err(MachineBuildError::TopologyMismatch);
        }
    }
    Ok(switches)
}

fn certified_switch_controls(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topologies: &BTreeMap<u64, CertifiedSwitchTopology>,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
) -> Result<BTreeMap<u64, CertifiedSwitchControl>, MachineBuildError> {
    let mut controls = BTreeMap::new();
    for (block_addr, topology) in topologies {
        let Some(certificate) = artifact.certificates().switches.get(block_addr) else {
            continue;
        };
        let Some(selector_value) = certificate.selector else {
            continue;
        };
        if certificate.block_addr != *block_addr
            || certificate.cases.as_slice() != topology.cases()
            || certificate.default != Some(topology.default_target())
        {
            continue;
        }
        let Some(instruction) = artifact.graph().inst(topology.source_inst) else {
            return Err(MachineBuildError::MissingInstruction(topology.source_inst));
        };
        let InstPayload::Op(SSAOp::BranchInd { target }) = &instruction.payload else {
            continue;
        };
        let Some(target_value) = artifact.graph().value_id_for_var(target) else {
            return Err(MachineBuildError::MissingGraphValue(selector_value));
        };
        if instruction.inputs.as_slice() != [target_value]
            || artifact
                .function()
                .infer_switch_selector_var(*block_addr)
                .and_then(|selector| artifact.graph().value_id_for_var(&selector))
                != Some(selector_value)
        {
            continue;
        }
        let selector = MachineValueUse::from_artifact(artifact, selector_value)?;
        let selector_bits = selector.binding().width_bits();
        if selector_bits == 0
            || selector_bits > 64
            || (selector_bits < 64
                && topology
                    .cases()
                    .iter()
                    .any(|(value, _)| *value >= (1_u64 << selector_bits)))
        {
            continue;
        }
        let matching_parameters = abi_parameters
            .values()
            .filter(|parameter| {
                parameter.value().is_some_and(|value| {
                    value == &selector
                        && value.producer().is_none()
                        && value.constant().is_none()
                        && value.memory_access().is_none()
                        && parameter.graph_storage().size.checked_mul(8) == Some(selector_bits)
                        && exact_parameter_projection(
                            parameter.storage(),
                            parameter.graph_storage(),
                            parameter.logical_value(),
                        )
                })
            })
            .collect::<Vec<_>>();
        let [parameter] = matching_parameters.as_slice() else {
            continue;
        };
        let witness = CertifiedSwitchControl {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            origin: origin.clone(),
            topology: topology.clone(),
            selector,
            parameter_index: parameter.index(),
            parameter_abi_storage: parameter.storage(),
            parameter_graph_storage: parameter.graph_storage(),
            parameter_logical_value: parameter.logical_value(),
        };
        witness
            .validate(artifact.obligations())
            .map_err(|_| MachineBuildError::ObligationMismatch(topology.source_inst))?;
        if controls.insert(*block_addr, witness).is_some() {
            return Err(MachineBuildError::TopologyMismatch);
        }
    }
    Ok(controls)
}

fn certified_natural_loop_routings(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    direct_controls: &BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    conditional_controls: &BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
) -> Result<BTreeMap<u64, CertifiedNaturalLoopRouting>, MachineBuildError> {
    let mut routings = BTreeMap::new();
    for fact in artifact.structured().loops.values() {
        let [body_latch] = fact.latches.as_slice() else {
            continue;
        };
        let [exit] = fact.exits.as_slice() else {
            continue;
        };
        let body = fact.body.iter().copied().collect::<BTreeSet<_>>();
        if fact.kind != StructuredLoopKind::Natural
            || !fact.carriers.is_empty()
            || body != BTreeSet::from([fact.header, *body_latch])
            || BTreeSet::from([fact.header, *body_latch, *exit]).len() != 3
        {
            continue;
        }
        let Some(header_block) = topology.block(fact.header) else {
            continue;
        };
        let Some(body_block) = topology.block(*body_latch) else {
            continue;
        };
        let Some(exit_block) = topology.block(*exit) else {
            continue;
        };
        let Some(header_producer) = header_block.instructions().last() else {
            continue;
        };
        let Some(body_producer) = body_block.instructions().last() else {
            continue;
        };
        let Some(header_control) = conditional_controls.get(header_producer) else {
            continue;
        };
        let Some(body_transfer) = direct_controls.get(body_producer) else {
            continue;
        };
        let (continuation_on_true, topology_exit) = match header_block.terminator() {
            CertifiedSourceTerminator::ConditionalBranch {
                true_target,
                false_target,
            } if *true_target == *body_latch => (true, *false_target),
            CertifiedSourceTerminator::ConditionalBranch {
                true_target,
                false_target,
            } if *false_target == *body_latch => (false, *true_target),
            _ => continue,
        };
        let external_predecessors = header_block
            .predecessors()
            .iter()
            .copied()
            .filter(|predecessor| *predecessor != *body_latch)
            .collect::<Vec<_>>();
        let [entry_predecessor] = external_predecessors.as_slice() else {
            continue;
        };
        let Some(predicate_id) = fact.condition else {
            continue;
        };
        let Some(predicate) = artifact.predicates().predicates.get(&predicate_id) else {
            continue;
        };
        let has_loop_state_obligation = artifact.obligations().obligations().keys().any(|id| {
            matches!(
                id.kind,
                SemanticObligationKind::LoopCarriedState
                    | SemanticObligationKind::LiveStateTransition
            ) && body.contains(&id.instruction.block_addr)
        });
        if topology_exit != *exit
            || *entry_predecessor == *exit
            || exit_block.addr() != *exit
            || header_control.true_target()
                != match header_block.terminator() {
                    CertifiedSourceTerminator::ConditionalBranch { true_target, .. } => {
                        *true_target
                    }
                    _ => unreachable!("matched conditional header"),
                }
            || header_control.false_target()
                != match header_block.terminator() {
                    CertifiedSourceTerminator::ConditionalBranch { false_target, .. } => {
                        *false_target
                    }
                    _ => unreachable!("matched conditional header"),
                }
            || body_transfer.target() != fact.header
            || body_block.successors() != [fact.header]
            || body_block.predecessors() != [fact.header]
            || header_block.predecessors() != [*entry_predecessor, *body_latch]
                && header_block.predecessors() != [*body_latch, *entry_predecessor]
            || predicate.block_addr != fact.header
            || predicate.true_target != header_control.true_target()
            || predicate.false_target != header_control.false_target()
            || predicate.condition != header_control.condition().binding().value()
            || has_loop_state_obligation
        {
            continue;
        }
        let routing = CertifiedNaturalLoopRouting {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            origin: origin.clone(),
            loop_id: fact.id,
            predicate_id,
            header_control: header_control.clone(),
            body_transfer: body_transfer.clone(),
            body_latch: *body_latch,
            exit: *exit,
            entry_predecessor: *entry_predecessor,
            continuation_on_true,
        };
        if routings.insert(fact.header, routing).is_some() {
            return Err(MachineBuildError::TopologyMismatch);
        }
    }
    Ok(routings)
}

fn certified_closed_natural_loop_controls(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    routings: &BTreeMap<u64, CertifiedNaturalLoopRouting>,
    direct_controls: &BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    abi_parameters: &BTreeMap<u32, CertifiedAbiParameter>,
) -> Result<BTreeMap<u64, CertifiedClosedNaturalLoopControl>, MachineBuildError> {
    let mut controls = BTreeMap::new();
    let Some(interface) = artifact.machine_context().function_interface() else {
        return Ok(controls);
    };
    if interface.parameters().len() != 1 {
        return Ok(controls);
    }
    for (header_addr, routing) in routings {
        let preheader_addr = routing.entry_predecessor();
        let body_addr = routing.body_latch();
        let exit_addr = routing.exit();
        if routing.origin() != origin
            || topology.entry_addr() != preheader_addr
            || topology.blocks().len() != 4
            || BTreeSet::from([preheader_addr, *header_addr, body_addr, exit_addr]).len() != 4
        {
            continue;
        }
        let Some(preheader) = topology.block(preheader_addr) else {
            continue;
        };
        let Some(header) = topology.block(*header_addr) else {
            continue;
        };
        let Some(body) = topology.block(body_addr) else {
            continue;
        };
        let Some(exit) = topology.block(exit_addr) else {
            continue;
        };
        let Some(preheader_producer) = preheader.instructions().last() else {
            continue;
        };
        let Some(preheader_transfer) = direct_controls.get(preheader_producer) else {
            continue;
        };
        let continuation_target = if routing.continuation_on_true() {
            routing.header_control().true_target()
        } else {
            routing.header_control().false_target()
        };
        let exit_target = if routing.continuation_on_true() {
            routing.header_control().false_target()
        } else {
            routing.header_control().true_target()
        };
        if !preheader.predecessors().is_empty()
            || preheader.successors() != [*header_addr]
            || !matches!(
                preheader.terminator(),
                CertifiedSourceTerminator::Branch { target } if *target == *header_addr
            )
            || preheader_transfer.target() != *header_addr
            || preheader_transfer.producer() != *preheader_producer
            || header
                .predecessors()
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                != BTreeSet::from([preheader_addr, body_addr])
            || header.successors().iter().copied().collect::<BTreeSet<_>>()
                != BTreeSet::from([body_addr, exit_addr])
            || continuation_target != body_addr
            || exit_target != exit_addr
            || body.predecessors() != [*header_addr]
            || body.successors() != [*header_addr]
            || !matches!(
                body.terminator(),
                CertifiedSourceTerminator::Branch { target } if *target == *header_addr
            )
            || exit.predecessors() != [*header_addr]
            || !exit.successors().is_empty()
            || !matches!(exit.terminator(), CertifiedSourceTerminator::Return)
            || preheader_transfer.validate(artifact.obligations()).is_err()
            || routing
                .header_control()
                .validate(artifact.obligations())
                .is_err()
            || routing
                .body_transfer()
                .validate(artifact.obligations())
                .is_err()
        {
            continue;
        }
        let condition = routing.header_control().condition();
        if condition.binding().width_bits() != 8
            || condition.producer().is_some()
            || condition.constant().is_some()
            || condition.memory_access().is_some()
        {
            continue;
        }
        let matching_parameters = abi_parameters
            .values()
            .filter(|parameter| {
                parameter.value() == Some(condition)
                    && parameter.graph_storage().size.checked_mul(8)
                        == Some(condition.binding().width_bits())
                    && interface_has_exact_parameter_projection(
                        interface,
                        parameter.index(),
                        parameter.storage(),
                        parameter.graph_storage(),
                        parameter.logical_value(),
                    )
            })
            .collect::<Vec<_>>();
        let [parameter] = matching_parameters.as_slice() else {
            continue;
        };
        parameter.validate_against_artifact(artifact)?;
        let control = CertifiedClosedNaturalLoopControl {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            origin: origin.clone(),
            routing: routing.clone(),
            preheader_transfer: preheader_transfer.clone(),
            parameter_index: parameter.index(),
            parameter_abi_storage: parameter.storage(),
            parameter_graph_storage: parameter.graph_storage(),
            parameter_logical_value: parameter.logical_value(),
        };
        if controls.insert(*header_addr, control).is_some() {
            return Err(MachineBuildError::TopologyMismatch);
        }
    }
    Ok(controls)
}

fn certified_memory_statements(
    artifact: &SsaArtifact,
) -> Result<BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>, MachineBuildError> {
    let mut statements = BTreeMap::new();
    for inst in &artifact.graph().insts {
        if !matches!(
            inst.payload,
            InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. })
        ) {
            continue;
        }
        let Some(statement) = try_certified_memory_statement(artifact, inst.id)? else {
            continue;
        };
        if statements.insert(statement.producer(), statement).is_some() {
            return Err(MachineBuildError::ObligationMismatch(inst.id));
        }
    }
    Ok(statements)
}

fn try_certified_memory_statement(
    artifact: &SsaArtifact,
    inst_id: r2ssa::InstId,
) -> Result<Option<CertifiedMemoryStatement>, MachineBuildError> {
    let graph = artifact.graph();
    let Some(inst) = graph.inst(inst_id) else {
        return Err(MachineBuildError::MissingInstruction(inst_id));
    };
    let Some(disposition) = artifact.obligations().instruction_for_inst(inst_id) else {
        return Err(MachineBuildError::MissingInstructionDisposition(inst_id));
    };
    if disposition.state != SemanticInstructionState::LiveObligation {
        return Ok(None);
    }
    let InstPayload::Op(op @ (SSAOp::Load { .. } | SSAOp::Store { .. })) = &inst.payload else {
        return Ok(None);
    };
    let accesses = artifact
        .facts()
        .structured
        .memory_accesses
        .iter()
        .filter(|(_, access)| access.id.inst == inst_id)
        .collect::<Vec<_>>();
    let [(access_key, access)] = accesses.as_slice() else {
        return Ok(None);
    };
    let Some(width_bits) = access.width.checked_mul(8).filter(|width| *width != 0) else {
        return Ok(None);
    };
    if !access.provenance_complete
        || **access_key != access.id
        || access.id.ordinal != 0
        || graph.op_site_for_inst(inst_id) != Some((access.block_addr, access.op_index))
        || artifact.objects().object(access.object).is_none()
    {
        return Ok(None);
    }
    if artifact
        .function()
        .get_block(access.block_addr)
        .and_then(|block| block.ops.get(access.op_index))
        != Some(op)
    {
        return Ok(None);
    }
    let source_context = artifact.machine_context();
    let model = source_context.memory_model();
    let Some(source_space) = source_context.memory_space_at(access.block_addr, access.op_index)
    else {
        return Ok(None);
    };
    if access.space != source_space
        || ssa_memory_space(op) != Some(source_space)
        || artifact
            .objects()
            .object_for_value(access.address, source_space)
            != Some(access.object)
        || artifact
            .objects()
            .object(access.object)
            .is_none_or(|object| object.kind.space() != source_space)
    {
        return Ok(None);
    }
    let Some(space_model) = model
        .space(source_space)
        .filter(|_| model.is_available() && model.is_coherent())
    else {
        return Ok(None);
    };
    if space_model.address_bits() == 0
        || space_model.word_size_bytes() == 0
        || !matches!(
            space_model.endianness(),
            MachineMemoryEndianness::Little | MachineMemoryEndianness::Big
        )
    {
        return Ok(None);
    }
    let space = MachineAddressSpace::from(source_space);
    if !matches!(
        space,
        MachineAddressSpace::Ram | MachineAddressSpace::Custom(_)
    ) {
        return Ok(None);
    }
    let Ok(address) = MachineValueUse::memory_address_for_access(artifact, access.id) else {
        return Ok(None);
    };

    let (obligation_kind, kind, expected_inputs) = match op {
        SSAOp::Load { .. } => {
            let Some(output) = inst.output.filter(|output| access.value == Some(*output)) else {
                return Ok(None);
            };
            if access.is_write || inst.inputs.as_slice() != [access.address] {
                return Ok(None);
            }
            let Ok(result) = MachineValueUse::from_artifact(artifact, output) else {
                return Ok(None);
            };
            if result.binding().width_bits() != width_bits {
                return Ok(None);
            }
            (
                SemanticObligationKind::ObservableMemoryRead,
                CertifiedMemoryStatementKind::Read { result },
                vec![access.address],
            )
        }
        SSAOp::Store { .. } => {
            let Some(value_id) = access.value else {
                return Ok(None);
            };
            if !access.is_write
                || inst.output.is_some()
                || inst.inputs.as_slice() != [access.address, value_id]
            {
                return Ok(None);
            }
            let Ok(value) = MachineValueUse::from_artifact(artifact, value_id) else {
                return Ok(None);
            };
            if value.binding().width_bits() != width_bits {
                return Ok(None);
            }
            (
                SemanticObligationKind::ObservableMemoryWrite,
                CertifiedMemoryStatementKind::Write { value },
                vec![access.address, value_id],
            )
        }
        _ => unreachable!(),
    };
    let obligation = SemanticObligationId {
        instruction: disposition.id,
        kind: obligation_kind,
        component: SemanticObligationComponent::MemoryAccess(access.id.ordinal),
    };
    let source_obligation_matches = artifact
        .obligations()
        .obligations()
        .get(&obligation)
        .is_some_and(|candidate| {
            candidate.source.graph_inst() == Some(inst_id) && candidate.inputs == expected_inputs
        });
    let sibling_obligations_are_plain = disposition.obligations.iter().all(|candidate| {
        *candidate == obligation
            || (matches!(op, SSAOp::Load { .. })
                && candidate.kind == SemanticObligationKind::LiveValueProducer
                && candidate.component == SemanticObligationComponent::Whole)
    });
    if !source_obligation_matches || !sibling_obligations_are_plain {
        return Ok(None);
    }
    let statement = CertifiedMemoryStatement {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        producer: disposition.id,
        access: access.id,
        object: access.object,
        address,
        space,
        endianness: space_model.endianness(),
        word_size_bytes: space_model.word_size_bytes(),
        width_bits,
        execution: CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrder,
        kind,
        source_obligations: BTreeSet::from([obligation]),
    };
    if statement.validate(artifact.obligations()).is_err() {
        return Ok(None);
    }
    Ok(Some(statement))
}

fn memory_statement_input_producers(
    statement: &CertifiedMemoryStatement,
) -> BTreeSet<CanonicalInstructionId> {
    let mut producers = BTreeSet::new();
    if let Some(producer) = statement.address().producer() {
        producers.insert(producer);
    }
    if let CertifiedMemoryStatementKind::Write { value } = statement.kind()
        && let Some(producer) = value.producer()
    {
        producers.insert(producer);
    }
    producers
}

fn conditional_control_input_producers(
    control: &CertifiedConditionalControl,
) -> BTreeSet<CanonicalInstructionId> {
    [control.target_value(), control.condition()]
        .into_iter()
        .filter_map(MachineValueUse::producer)
        .collect()
}

fn direct_call_input_producers(call: &CertifiedDirectCall) -> BTreeSet<CanonicalInstructionId> {
    std::iter::once(call.target_value())
        .chain(call.arguments().iter().map(CertifiedCallArgument::value))
        .filter_map(MachineValueUse::producer)
        .collect()
}

fn return_control_input_producers(
    control: &CertifiedReturnControl,
) -> BTreeSet<CanonicalInstructionId> {
    std::iter::once(control.control_target())
        .chain(control.values().iter().map(CertifiedReturnValue::value))
        .chain(
            control
                .register_compositions()
                .iter()
                .flat_map(CertifiedReturnRegisterComposition::ordered_values),
        )
        .chain(control.exit_stack_pointer().value())
        .filter_map(MachineValueUse::producer)
        .collect()
}

pub(crate) fn return_machine_state_matches_origin(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
) -> bool {
    // Exit machine state is proven against the machine's own carriers, which
    // exist whether or not an ABI was recovered.
    let (Some(return_address_storage), Some(stack_pointer_storage)) = (
        origin.machine_context().source().return_address_carrier(),
        origin.machine_context().source().stack_pointer_carrier(),
    ) else {
        return false;
    };
    let mut controls = BTreeMap::<CanonicalInstructionId, &CertifiedReturnControl>::new();
    for obligation in origin.source().obligations().values().filter(|obligation| {
        matches!(
            obligation.id.kind,
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
        )
    }) {
        let [effect] = ledger.effects(obligation.id) else {
            return false;
        };
        let Some(control) = effect.return_control_evidence() else {
            return false;
        };
        if controls
            .insert(control.producer(), control)
            .is_some_and(|existing| existing != control)
        {
            return false;
        }
    }
    if controls.is_empty() {
        return false;
    }
    controls.values().all(|control| {
        if control.return_address().storage() != return_address_storage
            || control.return_address().value() != control.control_target()
            || control.exit_stack_pointer().storage() != stack_pointer_storage
        {
            return false;
        }
        let Some(value) = control.exit_stack_pointer().value() else {
            return true;
        };
        let Some(producer) = value.producer() else {
            return true;
        };
        let Some(instruction) = origin.source().instructions().get(&producer) else {
            return false;
        };
        let live = instruction.obligations.iter().filter(|obligation| {
            obligation.kind == SemanticObligationKind::LiveValueProducer
        });
        let mut count = 0_usize;
        for obligation in live {
            count += 1;
            let [effect] = ledger.effects(*obligation) else {
                return false;
            };
            if effect.expression_evidence().is_none_or(|expression| {
                expression.entity().producer() != producer
            }) || !matches!(
                effect.disposition(),
                EffectDisposition::AbsorbedIntoExpression { producer: owner } if *owner == producer
            ) {
                return false;
            }
        }
        count == 1
    })
}

fn certified_read_matches_machine_entity(
    statement: &CertifiedMemoryStatement,
    entity: &MachineEntity,
    kind: &MachineExprKind,
) -> bool {
    let CertifiedMemoryStatementKind::Read { result } = statement.kind() else {
        return false;
    };
    let MachineExprKind::MemoryRead {
        access,
        object,
        space,
        endianness,
        word_size_bytes,
        width_bits,
        ..
    } = kind
    else {
        return false;
    };
    entity.producer() == statement.producer()
        && entity.output() == result.binding()
        && *access == statement.access()
        && *object == statement.object()
        && *space == statement.space()
        && *endianness == statement.endianness()
        && *word_size_bytes == statement.word_size_bytes()
        && *width_bits == statement.width_bits()
}

/// One exact stack interval normalized to the architectural entry stack
/// pointer. The signed offset is diagnostic; authority remains sealed in the
/// containing frame certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct CertifiedNormalizedStackRange {
    offset: i64,
    size_bytes: u32,
}

impl CertifiedNormalizedStackRange {
    pub const fn offset(&self) -> i64 {
        self.offset
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }
}

/// Exact load-and-register-restore evidence effective at one terminal return.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedFrameRestore {
    return_control: CertifiedReturnControl,
    return_address_read: Option<CertifiedMemoryStatement>,
    restore_read: CertifiedMemoryStatement,
    restore_copies: Box<[CertifiedFrameCopy]>,
    restore_assignment: CertifiedFrameRegisterAssignment,
}

impl CertifiedFrameRestore {
    pub const fn return_control(&self) -> &CertifiedReturnControl {
        &self.return_control
    }

    pub const fn return_address_read(&self) -> Option<&CertifiedMemoryStatement> {
        self.return_address_read.as_ref()
    }

    pub const fn restore_read(&self) -> &CertifiedMemoryStatement {
        &self.restore_read
    }

    pub const fn restore_copies(&self) -> &[CertifiedFrameCopy] {
        &self.restore_copies
    }

    pub const fn restore_assignment(&self) -> &CertifiedFrameRegisterAssignment {
        &self.restore_assignment
    }
}

/// Exact full-width, bit-preserving copy retained inside a frame-restore chain.
/// It grants no independent semantic disposition.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedFrameCopy {
    producer: CanonicalInstructionId,
    root: MachineExprId,
    input: MachineValueUse,
    output: r2ssa::MachineValueBinding,
}

impl CertifiedFrameCopy {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn root(&self) -> MachineExprId {
        self.root
    }

    pub const fn input(&self) -> &MachineValueUse {
        &self.input
    }

    pub const fn output(&self) -> r2ssa::MachineValueBinding {
        self.output
    }
}

/// Exact full-width machine assignment into the source-declared frame pointer.
/// Restore outputs are normally dead at the semantic ledger boundary, so this
/// witness is sealed directly from the retained machine entity instead of
/// inventing a live-value obligation.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedFrameRegisterAssignment {
    producer: CanonicalInstructionId,
    root: MachineExprId,
    input: MachineValueUse,
    output: r2ssa::MachineValueBinding,
    storage: CanonicalStorageId,
    normalized_affine_relation: Option<CertifiedFrameAffineRelation>,
}

impl CertifiedFrameRegisterAssignment {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn root(&self) -> MachineExprId {
        self.root
    }

    pub const fn input(&self) -> &MachineValueUse {
        &self.input
    }

    pub const fn output(&self) -> r2ssa::MachineValueBinding {
        self.output
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn normalized_affine_relation(&self) -> Option<CertifiedFrameAffineRelation> {
        self.normalized_affine_relation
    }
}

/// Exact address relation of a mechanical frame-register assignment, normalized
/// to the source-declared entry stack pointer. It grants no semantic ledger
/// disposition independently of its containing frame certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedFrameAffineRelation {
    base_storage: CanonicalStorageId,
    offset_bytes: i64,
    width_bits: u32,
}

impl CertifiedFrameAffineRelation {
    pub const fn base_storage(&self) -> CanonicalStorageId {
        self.base_storage
    }

    pub const fn offset_bytes(&self) -> i64 {
        self.offset_bytes
    }

    pub const fn width_bits(&self) -> u32 {
        self.width_bits
    }
}

/// Exact full-width assignment to the source-declared stack pointer, bound to
/// its machine entity and normalized to the unique entry stack-pointer value.
/// It grants no semantic disposition independently of its containing stack
/// discipline certificate.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedStackPointerAssignment {
    producer: CanonicalInstructionId,
    root: MachineExprId,
    input: MachineValueUse,
    output: r2ssa::MachineValueBinding,
    storage: CanonicalStorageId,
    normalized_affine_relation: CertifiedFrameAffineRelation,
}

impl CertifiedStackPointerAssignment {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn root(&self) -> MachineExprId {
        self.root
    }

    pub const fn input(&self) -> &MachineValueUse {
        &self.input
    }

    pub const fn output(&self) -> r2ssa::MachineValueBinding {
        self.output
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn normalized_affine_relation(&self) -> CertifiedFrameAffineRelation {
        self.normalized_affine_relation
    }
}

/// One exact plain-memory access whose address is proven entry-stack-relative
/// and contained in the certified private reservation. The statement retains
/// ownership of its observable memory obligation; this witness owns only the
/// address transport classification.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedPrivateStackAccess {
    statement: CertifiedMemoryStatement,
    range: CertifiedNormalizedStackRange,
}

impl CertifiedPrivateStackAccess {
    pub const fn statement(&self) -> &CertifiedMemoryStatement {
        &self.statement
    }

    pub const fn range(&self) -> CertifiedNormalizedStackRange {
        self.range
    }
}

/// Exact machine-derived private stack object and the complete set of its
/// certified plain accesses. No source name, type, or declared slot is inferred
/// from this manifest.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedPrivateStackRegion {
    objects: Box<[ObjectId]>,
    accessed_range: CertifiedNormalizedStackRange,
    accesses: Box<[CertifiedPrivateStackAccess]>,
}

impl CertifiedPrivateStackRegion {
    /// Exact object-model identities proven to name this one normalized stack
    /// interval. Multiple identities are retained only when every access spans
    /// the complete same interval; partial/hull-based aliasing is refused.
    pub const fn objects(&self) -> &[ObjectId] {
        &self.objects
    }

    pub const fn accessed_range(&self) -> CertifiedNormalizedStackRange {
        self.accessed_range
    }

    pub const fn accesses(&self) -> &[CertifiedPrivateStackAccess] {
        &self.accesses
    }
}

/// Per-return proof that the private reservation has been restored before the
/// source return. A stacked return may additionally advance the stack pointer
/// by its exact source-declared return-mechanism delta.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedStackRelease {
    return_control: CertifiedReturnControl,
    restoration: CertifiedStackPointerAssignment,
    post_restoration: Option<CertifiedStackPointerAssignment>,
    return_address_read: Option<CertifiedMemoryStatement>,
}

impl CertifiedStackRelease {
    pub const fn return_control(&self) -> &CertifiedReturnControl {
        &self.return_control
    }

    pub const fn restoration(&self) -> &CertifiedStackPointerAssignment {
        &self.restoration
    }

    pub const fn post_restoration(&self) -> Option<&CertifiedStackPointerAssignment> {
        self.post_restoration.as_ref()
    }

    pub const fn exit_stack_pointer(&self) -> &CertifiedExitStackPointer {
        self.return_control.exit_stack_pointer()
    }

    pub const fn return_address_read(&self) -> Option<&CertifiedMemoryStatement> {
        self.return_address_read.as_ref()
    }
}

/// Sealed proof of a source-bound private stack reservation, its exact
/// machine-derived access/address manifest, and restoration on every return.
///
/// The certificate is architecture- and mnemonic-independent. It consumes no
/// semantic obligation: memory statements, expression producers, and returns
/// must already be owned exactly once by the same artifact ledger.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedStackDiscipline {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    stack_pointer_storage: CanonicalStorageId,
    entry_stack_pointer: MachineValueUse,
    reservation_range: CertifiedNormalizedStackRange,
    private_ownership_range: CertifiedNormalizedStackRange,
    implicit_active_sp_bytes: u32,
    reservation: CertifiedStackPointerAssignment,
    assignments: Box<[CertifiedStackPointerAssignment]>,
    private_regions: Box<[CertifiedPrivateStackRegion]>,
    releases: Box<[CertifiedStackRelease]>,
}

impl CertifiedStackDiscipline {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn stack_pointer_storage(&self) -> CanonicalStorageId {
        self.stack_pointer_storage
    }

    pub const fn entry_stack_pointer(&self) -> &MachineValueUse {
        &self.entry_stack_pointer
    }

    pub const fn reservation_range(&self) -> CertifiedNormalizedStackRange {
        self.reservation_range
    }

    /// Complete entry-SP-relative envelope owned while the certified
    /// reservation is active, including source-declared implicit bytes.
    pub const fn private_ownership_range(&self) -> CertifiedNormalizedStackRange {
        self.private_ownership_range
    }

    /// Exact source-declared bytes beyond the active SP included in the
    /// private ownership envelope.
    pub const fn implicit_active_sp_bytes(&self) -> u32 {
        self.implicit_active_sp_bytes
    }

    pub const fn reservation(&self) -> &CertifiedStackPointerAssignment {
        &self.reservation
    }

    pub const fn assignments(&self) -> &[CertifiedStackPointerAssignment] {
        &self.assignments
    }

    pub const fn private_regions(&self) -> &[CertifiedPrivateStackRegion] {
        &self.private_regions
    }

    pub const fn releases(&self) -> &[CertifiedStackRelease] {
        &self.releases
    }
}

/// Sealed proof that one exact source-declared frame-pointer carrier is saved
/// to a private normalized stack interval and restored on every return.
///
/// This proof consumes no semantic obligation and grants no ledger
/// disposition. It only retains already-certified expression, memory, return,
/// topology, and source-interface evidence from the same artifact origin.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedFramePreservation {
    origin: CertifiedArtifactOrigin,
    frame_pointer_storage: CanonicalStorageId,
    stack_pointer_storage: CanonicalStorageId,
    saved_range: CertifiedNormalizedStackRange,
    stack_allocation: CertifiedExpr,
    entry_save: CertifiedMemoryStatement,
    entry_save_copies: Box<[CertifiedExpr]>,
    frame_relation: CertifiedFrameRegisterAssignment,
    restores: Box<[CertifiedFrameRestore]>,
}

impl CertifiedFramePreservation {
    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn frame_pointer_storage(&self) -> CanonicalStorageId {
        self.frame_pointer_storage
    }

    pub const fn stack_pointer_storage(&self) -> CanonicalStorageId {
        self.stack_pointer_storage
    }

    pub const fn saved_range(&self) -> CertifiedNormalizedStackRange {
        self.saved_range
    }

    pub const fn stack_allocation(&self) -> &CertifiedExpr {
        &self.stack_allocation
    }

    pub const fn entry_save(&self) -> &CertifiedMemoryStatement {
        &self.entry_save
    }

    pub const fn entry_save_copies(&self) -> &[CertifiedExpr] {
        &self.entry_save_copies
    }

    pub const fn frame_relation(&self) -> &CertifiedFrameRegisterAssignment {
        &self.frame_relation
    }

    pub const fn restores(&self) -> &[CertifiedFrameRestore] {
        &self.restores
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FrameAffine {
    offset_bits: u64,
    width_bits: u32,
}

impl FrameAffine {
    fn mask(width_bits: u32) -> Option<u64> {
        match width_bits {
            1..=63 => Some((1_u64 << width_bits) - 1),
            64 => Some(u64::MAX),
            _ => None,
        }
    }

    fn add(self, bits: u64) -> Option<Self> {
        let mask = Self::mask(self.width_bits)?;
        Some(Self {
            offset_bits: self.offset_bits.wrapping_add(bits) & mask,
            ..self
        })
    }

    fn sub(self, bits: u64) -> Option<Self> {
        let mask = Self::mask(self.width_bits)?;
        Some(Self {
            offset_bits: self.offset_bits.wrapping_sub(bits) & mask,
            ..self
        })
    }

    fn signed_offset(self) -> Option<i64> {
        let mask = Self::mask(self.width_bits)?;
        let bits = self.offset_bits & mask;
        if self.width_bits == 64 {
            Some(bits as i64)
        } else {
            let sign = 1_u64 << (self.width_bits - 1);
            Some(if bits & sign == 0 {
                bits as i64
            } else {
                (bits | !mask) as i64
            })
        }
    }
}

#[derive(Clone, Copy)]
struct FrameAffineRegisterContext<'a> {
    artifact: &'a SsaArtifact,
    projection: &'a MachineProjection,
    entry_stack_pointer: ValueId,
    stack_pointer_storage: CanonicalStorageId,
    register_storage: CanonicalStorageId,
    width_bits: u32,
}

struct FrameStackedReturnContext<'a> {
    artifact: &'a SsaArtifact,
    memory_statements: &'a BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    entry_stack_pointer: ValueId,
    stack_pointer_storage: CanonicalStorageId,
    width_bits: u32,
}

#[derive(Debug, Clone)]
struct FrameRestoreCandidate {
    read: CertifiedMemoryStatement,
    copies: Vec<CertifiedFrameCopy>,
    assignment: CertifiedFrameRegisterAssignment,
    read_inst: InstId,
    assignment_inst: InstId,
    restored_value: ValueId,
    range: CertifiedNormalizedStackRange,
}

#[derive(Debug, Clone)]
struct FramePreservationEvidence {
    frame_pointer_storage: CanonicalStorageId,
    stack_pointer_storage: CanonicalStorageId,
    saved_range: CertifiedNormalizedStackRange,
    stack_allocation: CertifiedExpr,
    entry_save: CertifiedMemoryStatement,
    entry_save_copies: Vec<CertifiedExpr>,
    frame_relation: CertifiedFrameRegisterAssignment,
    restores: Vec<(
        CertifiedReturnControl,
        FrameRestoreCandidate,
        Option<CertifiedMemoryStatement>,
    )>,
}

fn certified_register_storages_overlap(
    left: CanonicalStorageId,
    right: CanonicalStorageId,
) -> bool {
    if left.space != CanonicalStorageSpace::Register
        || right.space != CanonicalStorageSpace::Register
    {
        return false;
    }
    let (Some(left_end), Some(right_end)) = (
        left.offset.checked_add(u64::from(left.size)),
        right.offset.checked_add(u64::from(right.size)),
    ) else {
        return true;
    };
    left.offset < right_end && right.offset < left_end
}

fn frame_constant_bits(artifact: &SsaArtifact, value: ValueId, width_bits: u32) -> Option<u64> {
    frame_constant_bits_from_graph(artifact.graph(), value, width_bits)
}

fn frame_constant_bits_from_graph(
    graph: &r2ssa::SsaGraph,
    value: ValueId,
    width_bits: u32,
) -> Option<u64> {
    let mask = FrameAffine::mask(width_bits)?;
    let graph_value = graph.value(value)?;
    if graph_value.var.size.checked_mul(8) != Some(width_bits) {
        return None;
    }
    if let Some(bits) = graph_value.var.constant_bits() {
        return Some(bits & mask);
    }

    let definition = graph.def_inst(value)?;
    let inst = graph.inst(definition)?;
    let InstPayload::Op(SSAOp::Copy { dst, src }) = &inst.payload else {
        return None;
    };
    let [input] = inst.inputs.as_slice() else {
        return None;
    };
    if inst.output != Some(value)
        || inst.canonical_storage != graph_value.canonical_storage
        || graph_value.var != *dst
        || graph
            .block(inst.block)
            .is_none_or(|block| !block.insts.contains(&inst.id))
        || graph.def_inst(*input).is_some()
    {
        return None;
    }
    let input_value = graph.value(*input)?;
    let bits = input_value.var.constant_bits()?;
    if input_value.var != *src
        || input_value.var.size.checked_mul(8) != Some(width_bits)
        || input_value.canonical_storage
            != Some(CanonicalStorageId {
                space: CanonicalStorageSpace::Constant,
                offset: bits,
                size: input_value.var.size,
            })
    {
        return None;
    }
    Some(bits & mask)
}

fn frame_affine_value(
    artifact: &SsaArtifact,
    value: ValueId,
    entry_stack_pointer: ValueId,
    width_bits: u32,
    memo: &mut BTreeMap<ValueId, Option<FrameAffine>>,
    visiting: &mut BTreeSet<ValueId>,
) -> Option<FrameAffine> {
    if value == entry_stack_pointer {
        return Some(FrameAffine {
            offset_bits: 0,
            width_bits,
        });
    }
    if let Some(cached) = memo.get(&value) {
        return *cached;
    }
    if !visiting.insert(value) {
        return None;
    }
    let result = (|| {
        let graph = artifact.graph();
        let graph_value = graph.value(value)?;
        if graph_value.var.size.checked_mul(8) != Some(width_bits) {
            return None;
        }
        let inst = graph.inst(graph.def_inst(value)?)?;
        match &inst.payload {
            InstPayload::Op(SSAOp::Copy { .. }) if inst.inputs.len() == 1 => frame_affine_value(
                artifact,
                inst.inputs[0],
                entry_stack_pointer,
                width_bits,
                memo,
                visiting,
            ),
            InstPayload::Op(SSAOp::IntAdd { .. }) if inst.inputs.len() == 2 => {
                let left = frame_affine_value(
                    artifact,
                    inst.inputs[0],
                    entry_stack_pointer,
                    width_bits,
                    memo,
                    visiting,
                );
                let right = frame_affine_value(
                    artifact,
                    inst.inputs[1],
                    entry_stack_pointer,
                    width_bits,
                    memo,
                    visiting,
                );
                match (left, right) {
                    (Some(base), None) => frame_constant_bits(artifact, inst.inputs[1], width_bits)
                        .and_then(|constant| base.add(constant)),
                    (None, Some(base)) => frame_constant_bits(artifact, inst.inputs[0], width_bits)
                        .and_then(|constant| base.add(constant)),
                    _ => None,
                }
            }
            InstPayload::Op(SSAOp::IntSub { .. }) if inst.inputs.len() == 2 => {
                let base = frame_affine_value(
                    artifact,
                    inst.inputs[0],
                    entry_stack_pointer,
                    width_bits,
                    memo,
                    visiting,
                )?;
                frame_constant_bits(artifact, inst.inputs[1], width_bits)
                    .and_then(|constant| base.sub(constant))
            }
            InstPayload::Phi { .. } if !inst.inputs.is_empty() => {
                let mut inputs = inst.inputs.iter().copied();
                let first = frame_affine_value(
                    artifact,
                    inputs.next()?,
                    entry_stack_pointer,
                    width_bits,
                    memo,
                    visiting,
                )?;
                inputs
                    .all(|input| {
                        frame_affine_value(
                            artifact,
                            input,
                            entry_stack_pointer,
                            width_bits,
                            memo,
                            visiting,
                        ) == Some(first)
                    })
                    .then_some(first)
            }
            _ => None,
        }
    })();
    visiting.remove(&value);
    memo.insert(value, result);
    result
}

fn frame_affine_leaf_dead_consumer(
    artifact: &SsaArtifact,
    value: ValueId,
    use_site: r2ssa::UseSite,
) -> bool {
    let graph = artifact.graph();
    let source = artifact.obligations();
    if !source.is_complete() {
        return false;
    }
    let Some(consumer) = graph.inst(use_site.inst) else {
        return false;
    };
    let Some(input) = consumer.inputs.get(use_site.input_idx) else {
        return false;
    };
    let Some(output) = consumer.output else {
        return false;
    };
    let Some(disposition) = source.instruction_for_inst(consumer.id) else {
        return false;
    };
    *input == value
        && disposition.source.graph_inst() == Some(consumer.id)
        && disposition.state == SemanticInstructionState::ProvenDead
        && disposition.obligations.is_empty()
        && graph.def_inst(output) == Some(consumer.id)
        && graph.use_sites(output).is_empty()
}

fn frame_range_segments(
    range: CertifiedNormalizedStackRange,
    width_bits: u32,
) -> Option<Vec<(u128, u128)>> {
    let modulus = 1_u128.checked_shl(width_bits)?;
    let mask = modulus - 1;
    let start = u128::from(range.offset as u64) & mask;
    let size = u128::from(range.size_bytes);
    if size == 0 || size > modulus {
        return None;
    }
    let end = start + size;
    Some(if end <= modulus {
        vec![(start, end)]
    } else {
        vec![(start, modulus), (0, end - modulus)]
    })
}

fn frame_ranges_overlap(
    left: CertifiedNormalizedStackRange,
    right: CertifiedNormalizedStackRange,
    width_bits: u32,
) -> bool {
    let (Some(left), Some(right)) = (
        frame_range_segments(left, width_bits),
        frame_range_segments(right, width_bits),
    ) else {
        return true;
    };
    left.iter().any(|left| {
        right
            .iter()
            .any(|right| left.0 < right.1 && right.0 < left.1)
    })
}

fn frame_range_contains(
    outer: CertifiedNormalizedStackRange,
    inner: CertifiedNormalizedStackRange,
) -> bool {
    let (Some(outer_end), Some(inner_end)) = (
        outer.offset.checked_add(i64::from(outer.size_bytes)),
        inner.offset.checked_add(i64::from(inner.size_bytes)),
    ) else {
        return false;
    };
    outer.offset <= inner.offset && inner_end <= outer_end
}

fn frame_instruction_dominates(artifact: &SsaArtifact, left: InstId, right: InstId) -> bool {
    let graph = artifact.graph();
    let (Some(left), Some(right)) = (graph.inst(left), graph.inst(right)) else {
        return false;
    };
    let (Some(left_block), Some(right_block)) = (graph.block(left.block), graph.block(right.block))
    else {
        return false;
    };
    if left.block == right.block {
        left.ordinal < right.ordinal
    } else {
        artifact
            .function()
            .dominates(left_block.addr, right_block.addr)
    }
}

fn frame_instruction_can_reach(artifact: &SsaArtifact, left: InstId, right: InstId) -> bool {
    let graph = artifact.graph();
    let (Some(left), Some(right)) = (graph.inst(left), graph.inst(right)) else {
        return false;
    };
    if left.block == right.block {
        return left.ordinal < right.ordinal;
    }
    let mut seen = BTreeSet::new();
    let mut work = graph
        .block(left.block)
        .map(|block| block.successors.clone())
        .unwrap_or_default();
    while let Some(block) = work.pop() {
        if block == right.block {
            return true;
        }
        if seen.insert(block)
            && let Some(block) = graph.block(block)
        {
            work.extend(block.successors.iter().copied());
        }
    }
    false
}

fn frame_value_descends_from(
    artifact: &SsaArtifact,
    value: ValueId,
    ancestor: ValueId,
    visited: &mut BTreeSet<ValueId>,
) -> bool {
    value == ancestor
        || visited.insert(value)
            && artifact
                .graph()
                .def_inst(value)
                .and_then(|inst| artifact.graph().inst(inst))
                .is_some_and(|inst| {
                    inst.inputs
                        .iter()
                        .copied()
                        .any(|input| frame_value_descends_from(artifact, input, ancestor, visited))
                })
}

fn frame_expression_is_ledgered(expression: &CertifiedExpr, ledger: &ObligationLedger) -> bool {
    expression
        .entity()
        .source_obligations()
        .iter()
        .all(|obligation| {
            matches!(ledger.effects(*obligation), [effect]
            if effect.expression_evidence() == Some(expression)
                && matches!(effect.disposition(), EffectDisposition::AbsorbedIntoExpression {
                    producer
                } if *producer == expression.entity().producer()))
        })
}

fn frame_statement_is_ledgered(
    statement: &CertifiedMemoryStatement,
    ledger: &ObligationLedger,
) -> bool {
    statement.source_obligations().iter().all(|obligation| {
        matches!(ledger.effects(*obligation), [effect]
            if effect.statement_evidence() == Some(statement)
                && matches!(effect.disposition(), EffectDisposition::AbsorbedIntoStatement {
                    producer
                } if *producer == statement.producer()))
    })
}

fn frame_return_is_ledgered(control: &CertifiedReturnControl, ledger: &ObligationLedger) -> bool {
    control.source_obligations().into_iter().all(|obligation| {
        matches!(ledger.effects(obligation), [effect]
            if effect.return_control_evidence() == Some(control)
                && matches!(effect.disposition(), EffectDisposition::AbsorbedIntoReturn {
                    producer
                } if *producer == control.producer()))
    })
}

#[derive(Clone, Copy)]
struct FrameMechanicalWitness {
    producer: CanonicalInstructionId,
    root: MachineExprId,
    output: r2ssa::MachineValueBinding,
}

fn frame_mechanical_producer_is_accounted(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    witness: FrameMechanicalWitness,
    already_accounted: &BTreeSet<SemanticObligationId>,
    expressions: &BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    ledger: &ObligationLedger,
) -> bool {
    let Some(instruction) = artifact.obligations().instructions().get(&witness.producer) else {
        return false;
    };
    if !already_accounted.is_subset(&instruction.obligations) {
        return false;
    }
    let remaining = instruction
        .obligations
        .difference(already_accounted)
        .copied()
        .collect::<BTreeSet<_>>();
    let Some(machine_entity) = projection.entity_for_producer(witness.producer) else {
        return false;
    };
    if machine_entity.root() != witness.root || machine_entity.output() != witness.output {
        return false;
    }
    if remaining.is_empty() {
        return true;
    }
    remaining
        .iter()
        .all(|obligation| obligation.kind == SemanticObligationKind::LiveValueProducer)
        && expressions
            .get(&witness.producer)
            .is_some_and(|expression| {
                expression.root() == witness.root
                    && expression.entity().source_obligations() == &remaining
                    && frame_expression_is_ledgered(expression, ledger)
            })
}

fn frame_topology_is_balanced(topology: &CertifiedSourceTopology) -> bool {
    let returns = topology
        .blocks()
        .iter()
        .filter(|block| matches!(block.terminator(), CertifiedSourceTerminator::Return))
        .map(CertifiedSourceBlock::addr)
        .collect::<BTreeSet<_>>();
    if returns.is_empty()
        || topology.blocks().iter().any(|block| {
            block.successors().is_empty()
                && !matches!(block.terminator(), CertifiedSourceTerminator::Return)
                || matches!(
                    block.terminator(),
                    CertifiedSourceTerminator::Call { .. }
                        | CertifiedSourceTerminator::IndirectCall { .. }
                )
        })
    {
        return false;
    }
    let mut reachable = BTreeSet::from([topology.entry_addr()]);
    let mut work = vec![topology.entry_addr()];
    while let Some(addr) = work.pop() {
        let Some(block) = topology.block(addr) else {
            return false;
        };
        for successor in block.successors() {
            if reachable.insert(*successor) {
                work.push(*successor);
            }
        }
    }
    if reachable.len() != topology.blocks().len() {
        return false;
    }
    let mut reaches_return = returns;
    loop {
        let mut changed = false;
        for block in topology.blocks() {
            if block
                .successors()
                .iter()
                .any(|successor| reaches_return.contains(successor))
            {
                changed |= reaches_return.insert(block.addr());
            }
        }
        if !changed {
            break;
        }
    }
    reaches_return.len() == topology.blocks().len()
}

fn frame_producer_for_inst(artifact: &SsaArtifact, inst: InstId) -> Option<CanonicalInstructionId> {
    artifact
        .obligations()
        .instruction_for_inst(inst)
        .map(|instruction| instruction.id)
}

fn frame_expression_for_inst<'a>(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    expressions: &'a BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    inst: InstId,
) -> Option<&'a CertifiedExpr> {
    let producer = frame_producer_for_inst(artifact, inst)?;
    let expression = expressions.get(&producer)?;
    let entity = projection.entity_for_producer(producer)?;
    (expression.entity().producer() == producer
        && expression.root() == entity.root()
        && entity.output().value() == artifact.graph().inst(inst)?.output?)
        .then_some(expression)
}

fn frame_statement_for_inst<'a>(
    artifact: &SsaArtifact,
    statements: &'a BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    inst: InstId,
) -> Option<&'a CertifiedMemoryStatement> {
    let producer = frame_producer_for_inst(artifact, inst)?;
    statements
        .get(&producer)
        .filter(|statement| statement.access().inst == inst)
}

fn frame_register_assignment_for_inst(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    inst: InstId,
    input: ValueId,
    storage: CanonicalStorageId,
) -> Option<CertifiedFrameRegisterAssignment> {
    let producer = frame_producer_for_inst(artifact, inst)?;
    let entity = projection.entity_for_producer(producer)?;
    let graph_inst = artifact.graph().inst(inst)?;
    let output = graph_inst.output?;
    (entity.output().value() == output
        && entity.output().width_bits() == storage.size.checked_mul(8)?
        && graph_inst.canonical_storage == Some(storage))
    .then_some(CertifiedFrameRegisterAssignment {
        producer,
        root: entity.root(),
        input: MachineValueUse::from_artifact(artifact, input).ok()?,
        output: entity.output(),
        storage,
        normalized_affine_relation: None,
    })
}

fn frame_affine_assignment_input(
    artifact: &SsaArtifact,
    inst: InstId,
    entry_stack_pointer: ValueId,
    width_bits: u32,
    affine: &mut BTreeMap<ValueId, Option<FrameAffine>>,
) -> Option<ValueId> {
    let graph_inst = artifact.graph().inst(inst)?;
    match &graph_inst.payload {
        InstPayload::Op(SSAOp::Copy { .. }) => {
            let [input] = graph_inst.inputs.as_slice() else {
                return None;
            };
            frame_affine_value(
                artifact,
                *input,
                entry_stack_pointer,
                width_bits,
                affine,
                &mut BTreeSet::new(),
            )?;
            Some(*input)
        }
        InstPayload::Op(SSAOp::IntAdd { .. }) => {
            let [left, right] = graph_inst.inputs.as_slice() else {
                return None;
            };
            let left_affine = frame_affine_value(
                artifact,
                *left,
                entry_stack_pointer,
                width_bits,
                affine,
                &mut BTreeSet::new(),
            );
            let right_affine = frame_affine_value(
                artifact,
                *right,
                entry_stack_pointer,
                width_bits,
                affine,
                &mut BTreeSet::new(),
            );
            match (left_affine, right_affine) {
                (Some(_), None) if frame_constant_bits(artifact, *right, width_bits).is_some() => {
                    Some(*left)
                }
                (None, Some(_)) if frame_constant_bits(artifact, *left, width_bits).is_some() => {
                    Some(*right)
                }
                _ => None,
            }
        }
        InstPayload::Op(SSAOp::IntSub { .. }) => {
            let [base, offset] = graph_inst.inputs.as_slice() else {
                return None;
            };
            frame_affine_value(
                artifact,
                *base,
                entry_stack_pointer,
                width_bits,
                affine,
                &mut BTreeSet::new(),
            )?;
            frame_constant_bits(artifact, *offset, width_bits)?;
            Some(*base)
        }
        _ => None,
    }
}

fn frame_affine_register_assignment_for_inst(
    context: FrameAffineRegisterContext<'_>,
    inst: InstId,
    affine: &mut BTreeMap<ValueId, Option<FrameAffine>>,
) -> Option<CertifiedFrameRegisterAssignment> {
    let graph_inst = context.artifact.graph().inst(inst)?;
    let output = graph_inst.output?;
    let input = frame_affine_assignment_input(
        context.artifact,
        inst,
        context.entry_stack_pointer,
        context.width_bits,
        affine,
    )?;
    let relation = frame_affine_value(
        context.artifact,
        output,
        context.entry_stack_pointer,
        context.width_bits,
        affine,
        &mut BTreeSet::new(),
    )?;
    let mut assignment = frame_register_assignment_for_inst(
        context.artifact,
        context.projection,
        inst,
        input,
        context.register_storage,
    )?;
    assignment.normalized_affine_relation = Some(CertifiedFrameAffineRelation {
        base_storage: context.stack_pointer_storage,
        offset_bytes: relation.signed_offset()?,
        width_bits: relation.width_bits,
    });
    Some(assignment)
}

fn frame_affine_register_assignment_matches(
    context: FrameAffineRegisterContext<'_>,
    assignment: &CertifiedFrameRegisterAssignment,
    affine: &mut BTreeMap<ValueId, Option<FrameAffine>>,
) -> bool {
    let Some(instruction) = context
        .artifact
        .obligations()
        .instructions()
        .get(&assignment.producer)
    else {
        return false;
    };
    instruction.source.graph_inst().is_some_and(|inst| {
        frame_affine_register_assignment_for_inst(context, inst, affine).as_ref()
            == Some(assignment)
    })
}

fn stack_pointer_assignment_for_inst(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    inst: InstId,
    entry_stack_pointer: ValueId,
    stack_pointer_storage: CanonicalStorageId,
    width_bits: u32,
    affine: &mut BTreeMap<ValueId, Option<FrameAffine>>,
) -> Option<CertifiedStackPointerAssignment> {
    let assignment = frame_affine_register_assignment_for_inst(
        FrameAffineRegisterContext {
            artifact,
            projection,
            entry_stack_pointer,
            stack_pointer_storage,
            register_storage: stack_pointer_storage,
            width_bits,
        },
        inst,
        affine,
    )?;
    Some(CertifiedStackPointerAssignment {
        producer: assignment.producer,
        root: assignment.root,
        input: assignment.input,
        output: assignment.output,
        storage: assignment.storage,
        normalized_affine_relation: assignment.normalized_affine_relation?,
    })
}

fn frame_copy_for_inst(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    inst: InstId,
    input: ValueId,
) -> Option<CertifiedFrameCopy> {
    let producer = frame_producer_for_inst(artifact, inst)?;
    let entity = projection.entity_for_producer(producer)?;
    let graph_inst = artifact.graph().inst(inst)?;
    let output = graph_inst.output?;
    matches!(graph_inst.payload, InstPayload::Op(SSAOp::Copy { .. }))
        .then_some(CertifiedFrameCopy {
            producer,
            root: entity.root(),
            input: MachineValueUse::from_artifact(artifact, input).ok()?,
            output: entity.output(),
        })
        .filter(|copy| copy.output.value() == output)
}

fn frame_entry_save_copy_chain(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    expressions: &BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    entry_frame_pointer: ValueId,
    saved_value: ValueId,
    save_inst: InstId,
    width_bits: u32,
) -> Option<Vec<CertifiedExpr>> {
    let graph = artifact.graph();
    let mut current = saved_value;
    let mut expected_use = r2ssa::UseSite {
        inst: save_inst,
        input_idx: 1,
    };
    let mut reversed = Vec::new();
    let mut visited = BTreeSet::new();
    while current != entry_frame_pointer {
        if !visited.insert(current) || graph.use_sites(current) != [expected_use] {
            return None;
        }
        let inst_id = graph.def_inst(current)?;
        let inst = graph.inst(inst_id)?;
        let InstPayload::Op(SSAOp::Copy { .. }) = &inst.payload else {
            return None;
        };
        let [input] = inst.inputs.as_slice() else {
            return None;
        };
        if graph.value(current)?.var.size.checked_mul(8) != Some(width_bits)
            || graph.value(*input)?.var.size.checked_mul(8) != Some(width_bits)
        {
            return None;
        }
        if !frame_instruction_dominates(artifact, inst_id, expected_use.inst) {
            return None;
        }
        let expression = frame_expression_for_inst(artifact, projection, expressions, inst_id)?;
        reversed.push(expression.clone());
        expected_use = r2ssa::UseSite {
            inst: inst_id,
            input_idx: 0,
        };
        current = *input;
    }
    if graph.use_sites(entry_frame_pointer) != [expected_use] {
        return None;
    }
    reversed.reverse();
    Some(reversed)
}

fn frame_restore_copy_chain(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    restored_input: ValueId,
    assignment_inst: InstId,
    width_bits: u32,
) -> Option<(CertifiedMemoryStatement, InstId, Vec<CertifiedFrameCopy>)> {
    let graph = artifact.graph();
    let mut current = restored_input;
    let mut expected_use = r2ssa::UseSite {
        inst: assignment_inst,
        input_idx: 0,
    };
    let mut reversed = Vec::new();
    let mut visited = BTreeSet::new();
    loop {
        if !visited.insert(current) || graph.use_sites(current) != [expected_use] {
            return None;
        }
        let inst_id = graph.def_inst(current)?;
        let inst = graph.inst(inst_id)?;
        if let InstPayload::Op(SSAOp::Load { .. }) = &inst.payload {
            let read = frame_statement_for_inst(artifact, memory_statements, inst_id)?.clone();
            if !matches!(read.kind(), CertifiedMemoryStatementKind::Read { result }
                if result.binding().value() == current
                    && result.binding().width_bits() == width_bits)
                || !frame_instruction_dominates(artifact, inst_id, expected_use.inst)
            {
                return None;
            }
            reversed.reverse();
            return Some((read, inst_id, reversed));
        }
        let InstPayload::Op(SSAOp::Copy { .. }) = &inst.payload else {
            return None;
        };
        let [input] = inst.inputs.as_slice() else {
            return None;
        };
        if graph.value(current)?.var.size.checked_mul(8) != Some(width_bits)
            || graph.value(*input)?.var.size.checked_mul(8) != Some(width_bits)
            || !frame_instruction_dominates(artifact, inst_id, expected_use.inst)
        {
            return None;
        }
        reversed.push(frame_copy_for_inst(artifact, projection, inst_id, *input)?);
        expected_use = r2ssa::UseSite {
            inst: inst_id,
            input_idx: 0,
        };
        current = *input;
    }
}

fn frame_normalized_range(
    artifact: &SsaArtifact,
    statement: &CertifiedMemoryStatement,
    entry_stack_pointer: ValueId,
    width_bits: u32,
    memo: &mut BTreeMap<ValueId, Option<FrameAffine>>,
) -> Option<CertifiedNormalizedStackRange> {
    if !statement.width_bits().is_multiple_of(8) {
        return None;
    }
    let affine = frame_affine_value(
        artifact,
        statement.address().binding().value(),
        entry_stack_pointer,
        width_bits,
        memo,
        &mut BTreeSet::new(),
    )?;
    Some(CertifiedNormalizedStackRange {
        offset: affine.signed_offset()?,
        size_bytes: statement.width_bits().checked_div(8)?,
    })
}

fn frame_statement_has_exact_nonstack_object(
    artifact: &SsaArtifact,
    statement: &CertifiedMemoryStatement,
) -> bool {
    matches!(
        artifact.objects().objects.get(&statement.object()),
        Some(object)
            if matches!(
                object.kind,
                ObjectKind::Parameter { .. }
                    | ObjectKind::Global { .. }
                    | ObjectKind::HeapAlloc { .. }
            )
    )
}

fn frame_stacked_return_read(
    context: FrameStackedReturnContext<'_>,
    control: &CertifiedReturnControl,
    return_inst: InstId,
    exit_offset: i64,
    affine: &mut BTreeMap<ValueId, Option<FrameAffine>>,
) -> Option<CertifiedMemoryStatement> {
    let interface = context.artifact.machine_context().function_interface()?;
    let return_address_storage = interface.return_address_storage()?;
    let mechanism = interface.return_mechanism()?;
    let address_size = mechanism.address_size_bytes();
    let address_bits = address_size.checked_mul(8)?;
    if mechanism.stack_offset() != 0
        || mechanism.slot_size_bytes() != address_size
        || mechanism.stack_pointer_delta_bytes() != address_size
        || exit_offset != i64::from(address_size)
        || address_bits != context.width_bits
        || return_address_storage.size != address_size
        || context.stack_pointer_storage.size != address_size
        || control.return_address().storage() != return_address_storage
        || control.control_target().binding().width_bits() != address_bits
    {
        return None;
    }
    let memory_model = context.artifact.machine_context().memory_model();
    let ram = memory_model.space(r2il::SpaceId::Ram)?;
    if !memory_model.is_available()
        || !memory_model.is_coherent()
        || memory_model.default_address_bits() != address_bits
        || ram.address_bits() != address_bits
        || ram.word_size_bytes() != 1
    {
        return None;
    }
    let return_range = CertifiedNormalizedStackRange {
        offset: mechanism.stack_offset(),
        size_bytes: mechanism.slot_size_bytes(),
    };
    let reads = context
        .memory_statements
        .values()
        .filter(|statement| {
            statement.space() == MachineAddressSpace::Ram
                && statement.word_size_bytes() == 1
                && statement.width_bits() == address_bits
                && statement.endianness() == ram.endianness()
                && frame_normalized_range(
                    context.artifact,
                    statement,
                    context.entry_stack_pointer,
                    context.width_bits,
                    affine,
                ) == Some(return_range)
                && matches!(statement.kind(), CertifiedMemoryStatementKind::Read { result }
                    if result == control.control_target()
                        && result == control.return_address().value()
                        && result.producer() == Some(statement.producer()))
                && frame_instruction_dominates(
                    context.artifact,
                    statement.access().inst,
                    return_inst,
                )
        })
        .cloned()
        .collect::<Vec<_>>();
    let [return_read] = reads.as_slice() else {
        return None;
    };
    Some(return_read.clone())
}

fn frame_evidence_from_certified_parts(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    topology: &CertifiedSourceTopology,
    expressions: &BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    return_controls: &BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
) -> Option<FramePreservationEvidence> {
    let interface = artifact.machine_context().function_interface()?;
    let frame_pointer_storage = interface.exact_frame_pointer_storage()?;
    let stack_pointer_storage = interface.stack_pointer_storage()?;
    let stack_allocation_contract = interface.stack_allocation_contract()?;
    if stack_allocation_contract.growth() != SourceStackGrowth::LowerAddresses {
        return None;
    }
    let width_bits = frame_pointer_storage.size.checked_mul(8)?;
    if width_bits == 0
        || width_bits > 64
        || frame_pointer_storage.size != stack_pointer_storage.size
        || !frame_topology_is_balanced(topology)
    {
        return None;
    }
    let graph = artifact.graph();
    if !graph.block(graph.entry)?.predecessors.is_empty()
        || artifact
            .obligations()
            .instructions()
            .values()
            .any(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
        || artifact
            .obligations()
            .obligations()
            .values()
            .any(|obligation| obligation.id.kind == SemanticObligationKind::VolatileOrUnknownEffect)
        || graph.insts.iter().any(|inst| {
            matches!(
                inst.payload,
                InstPayload::Op(SSAOp::Call { .. } | SSAOp::CallInd { .. })
            )
        })
    {
        return None;
    }
    let exact_entry_value = |storage| {
        let values = graph
            .values
            .iter()
            .filter(|value| {
                value.canonical_storage == Some(storage) && graph.def_inst(value.id).is_none()
            })
            .map(|value| value.id)
            .collect::<Vec<_>>();
        match values.as_slice() {
            [value] => Some(*value),
            _ => None,
        }
    };
    let entry_frame_pointer = exact_entry_value(frame_pointer_storage)?;
    let entry_stack_pointer = exact_entry_value(stack_pointer_storage)?;
    if graph.values.iter().any(|value| {
        value.canonical_storage.is_some_and(|storage| {
            (certified_register_storages_overlap(storage, frame_pointer_storage)
                && storage != frame_pointer_storage)
                || (certified_register_storages_overlap(storage, stack_pointer_storage)
                    && storage != stack_pointer_storage)
        })
    }) {
        return None;
    }

    let mut affine = BTreeMap::new();
    let frame_relation_context = FrameAffineRegisterContext {
        artifact,
        projection,
        entry_stack_pointer,
        stack_pointer_storage,
        register_storage: frame_pointer_storage,
        width_bits,
    };
    let mut relation: Option<(CertifiedFrameRegisterAssignment, InstId, ValueId)> = None;
    let mut restore_candidates = Vec::<FrameRestoreCandidate>::new();
    for inst in &graph.insts {
        if inst.canonical_storage != Some(frame_pointer_storage) {
            continue;
        }
        let output = inst.output?;
        if frame_affine_value(
            artifact,
            output,
            entry_stack_pointer,
            width_bits,
            &mut affine,
            &mut BTreeSet::new(),
        )
        .is_some()
        {
            let assignment = frame_affine_register_assignment_for_inst(
                frame_relation_context,
                inst.id,
                &mut affine,
            )?;
            if relation.replace((assignment, inst.id, output)).is_some() {
                return None;
            }
            continue;
        }
        if matches!(inst.payload, InstPayload::Op(SSAOp::Load { .. })) {
            let read = frame_statement_for_inst(artifact, memory_statements, inst.id)?.clone();
            if !matches!(read.kind(), CertifiedMemoryStatementKind::Read { result }
                if result.binding().value() == output
                    && result.binding().width_bits() == width_bits)
            {
                return None;
            }
            let range = frame_normalized_range(
                artifact,
                &read,
                entry_stack_pointer,
                width_bits,
                &mut affine,
            )?;
            restore_candidates.push(FrameRestoreCandidate {
                read,
                copies: Vec::new(),
                assignment: frame_register_assignment_for_inst(
                    artifact,
                    projection,
                    inst.id,
                    output,
                    frame_pointer_storage,
                )?,
                read_inst: inst.id,
                assignment_inst: inst.id,
                restored_value: output,
                range,
            });
            continue;
        }
        let InstPayload::Op(SSAOp::Copy { .. }) = &inst.payload else {
            return None;
        };
        let [input] = inst.inputs.as_slice() else {
            return None;
        };
        let (read, read_inst, copies) = frame_restore_copy_chain(
            artifact,
            projection,
            memory_statements,
            *input,
            inst.id,
            width_bits,
        )?;
        let assignment = frame_register_assignment_for_inst(
            artifact,
            projection,
            inst.id,
            *input,
            frame_pointer_storage,
        )?;
        let range = frame_normalized_range(
            artifact,
            &read,
            entry_stack_pointer,
            width_bits,
            &mut affine,
        )?;
        restore_candidates.push(FrameRestoreCandidate {
            read,
            copies,
            assignment,
            read_inst,
            assignment_inst: inst.id,
            restored_value: output,
            range,
        });
    }
    let (frame_relation, relation_inst, relation_value) = relation?;
    let relation_affine = frame_affine_value(
        artifact,
        relation_value,
        entry_stack_pointer,
        width_bits,
        &mut affine,
        &mut BTreeSet::new(),
    )?;
    if relation_affine.width_bits != width_bits
        || !frame_affine_register_assignment_matches(
            frame_relation_context,
            &frame_relation,
            &mut affine,
        )
    {
        return None;
    }
    for inst in &graph.insts {
        if inst.canonical_storage == Some(stack_pointer_storage) {
            let output = inst.output?;
            frame_affine_value(
                artifact,
                output,
                entry_stack_pointer,
                width_bits,
                &mut affine,
                &mut BTreeSet::new(),
            )?;
        }
    }
    let saves = memory_statements
        .values()
        .filter_map(|statement| {
            let CertifiedMemoryStatementKind::Write { value } = statement.kind() else {
                return None;
            };
            if value.binding().width_bits() != width_bits {
                return None;
            }
            let copies = frame_entry_save_copy_chain(
                artifact,
                projection,
                expressions,
                entry_frame_pointer,
                value.binding().value(),
                statement.access().inst,
                width_bits,
            )?;
            Some((statement, copies))
        })
        .collect::<Vec<_>>();
    let [(entry_save, entry_save_copies)] = saves.as_slice() else {
        return None;
    };
    let entry_save = (*entry_save).clone();
    let entry_save_copies = entry_save_copies.clone();
    let save_inst = entry_save.access().inst;
    let save_graph_inst = graph.inst(save_inst)?;
    let relation_graph_inst = graph.inst(relation_inst)?;
    let entry_block = graph.block(graph.entry)?;
    if save_graph_inst.block != graph.entry
        || relation_graph_inst.block != graph.entry
        || save_graph_inst.ordinal >= relation_graph_inst.ordinal
    {
        return None;
    }
    let saved_range = frame_normalized_range(
        artifact,
        &entry_save,
        entry_stack_pointer,
        width_bits,
        &mut affine,
    )?;
    if saved_range.size_bytes != frame_pointer_storage.size
        || entry_save.space() != MachineAddressSpace::Ram
        || entry_save.word_size_bytes() != 1
        || entry_block.addr != topology.entry_addr()
    {
        return None;
    }
    let saved_end = saved_range
        .offset
        .checked_add(i64::from(saved_range.size_bytes))?;
    let allocations = graph
        .insts
        .iter()
        .filter_map(|inst| {
            (inst.canonical_storage == Some(stack_pointer_storage)).then_some(())?;
            let output = inst.output?;
            let allocation = frame_affine_value(
                artifact,
                output,
                entry_stack_pointer,
                width_bits,
                &mut affine,
                &mut BTreeSet::new(),
            )?
            .signed_offset()?;
            (allocation < 0 && frame_instruction_dominates(artifact, inst.id, save_inst)).then(
                || {
                    frame_expression_for_inst(artifact, projection, expressions, inst.id)
                        .map(|expression| (inst.id, output, allocation, expression.clone()))
                },
            )?
        })
        .collect::<Vec<_>>();
    let latest_allocations = allocations
        .iter()
        .filter(|(candidate, _, _, _)| {
            allocations.iter().all(|(other, _, _, _)| {
                candidate == other || frame_instruction_dominates(artifact, *other, *candidate)
            })
        })
        .collect::<Vec<_>>();
    let [(allocation_inst, allocation_value, allocation_offset, stack_allocation)] =
        latest_allocations.as_slice()
    else {
        return None;
    };
    let allocation_size = u32::try_from(allocation_offset.checked_neg()?).ok()?;
    if !stack_allocation_contract
        .owns_entry_relative_reservation(*allocation_offset, allocation_size)
        || saved_range.offset < *allocation_offset
        || saved_end > 0
        || !frame_value_descends_from(
            artifact,
            entry_save.address().binding().value(),
            *allocation_value,
            &mut BTreeSet::new(),
        )
        || !frame_value_descends_from(
            artifact,
            relation_value,
            *allocation_value,
            &mut BTreeSet::new(),
        )
        || !frame_instruction_dominates(artifact, *allocation_inst, relation_inst)
        || restore_candidates.iter().any(|restore| {
            !frame_instruction_dominates(artifact, *allocation_inst, restore.read_inst)
                || (restore.assignment_inst != restore.read_inst
                    && !frame_instruction_dominates(
                        artifact,
                        *allocation_inst,
                        restore.assignment_inst,
                    ))
        })
    {
        return None;
    }
    let stack_allocation = stack_allocation.clone();

    for inst in &graph.insts {
        match &inst.payload {
            InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. }) => {
                frame_statement_for_inst(artifact, memory_statements, inst.id)?;
            }
            InstPayload::Op(
                SSAOp::LoadLinked { .. }
                | SSAOp::StoreConditional { .. }
                | SSAOp::AtomicCAS { .. }
                | SSAOp::LoadGuarded { .. }
                | SSAOp::StoreGuarded { .. }
                | SSAOp::Fence { .. },
            ) => return None,
            _ => {}
        }
    }
    let restore_reads = restore_candidates
        .iter()
        .map(|restore| restore.read_inst)
        .collect::<BTreeSet<_>>();
    for statement in memory_statements.values() {
        if statement.space() != entry_save.space() {
            continue;
        }
        let Some(range) = frame_normalized_range(
            artifact,
            statement,
            entry_stack_pointer,
            width_bits,
            &mut affine,
        ) else {
            if frame_statement_has_exact_nonstack_object(artifact, statement) {
                continue;
            }
            return None;
        };
        if !frame_ranges_overlap(saved_range, range, width_bits) {
            continue;
        }
        let is_save = statement.access().inst == save_inst && *statement == entry_save;
        let is_restore = restore_reads.contains(&statement.access().inst)
            && restore_candidates
                .iter()
                .any(|restore| restore.read == *statement && restore.range == saved_range);
        if !is_save && !is_restore {
            return None;
        }
    }
    if restore_candidates.is_empty()
        || restore_candidates.iter().any(|restore| {
            restore.range != saved_range
                || restore.read.space() != entry_save.space()
                || restore.read.word_size_bytes() != entry_save.word_size_bytes()
                || restore.read.endianness() != entry_save.endianness()
                || restore.read.width_bits() != entry_save.width_bits()
                || !frame_instruction_dominates(artifact, relation_inst, restore.read_inst)
        })
    {
        return None;
    }

    for value in &graph.values {
        if frame_affine_value(
            artifact,
            value.id,
            entry_stack_pointer,
            width_bits,
            &mut affine,
            &mut BTreeSet::new(),
        )
        .is_none()
        {
            continue;
        }
        for use_site in graph.use_sites(value.id) {
            let consumer = graph.inst(use_site.inst)?;
            let allowed = match &consumer.payload {
                InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. }) => {
                    use_site.input_idx == 0
                }
                InstPayload::Op(
                    SSAOp::Copy { .. } | SSAOp::IntAdd { .. } | SSAOp::IntSub { .. },
                )
                | InstPayload::Phi { .. } => consumer.output.is_some_and(|output| {
                    frame_affine_value(
                        artifact,
                        output,
                        entry_stack_pointer,
                        width_bits,
                        &mut affine,
                        &mut BTreeSet::new(),
                    )
                    .is_some()
                }),
                _ => frame_affine_leaf_dead_consumer(artifact, value.id, *use_site),
            };
            if !allowed {
                return None;
            }
        }
    }
    let return_blocks = topology
        .blocks()
        .iter()
        .filter(|block| matches!(block.terminator(), CertifiedSourceTerminator::Return))
        .count();
    if return_controls.len() != return_blocks {
        return None;
    }
    let has_stack_pointer_def = graph
        .insts
        .iter()
        .any(|inst| inst.canonical_storage == Some(stack_pointer_storage));
    let mut used_restores = BTreeSet::new();
    let mut restores = Vec::new();
    for control in return_controls.values() {
        let return_inst = artifact
            .obligations()
            .instructions()
            .get(&control.producer())?
            .source
            .graph_inst()?;
        let return_escapes_frame = std::iter::once(control.control_target())
            .chain(control.values().iter().map(CertifiedReturnValue::value))
            .chain(
                control
                    .register_compositions()
                    .iter()
                    .flat_map(CertifiedReturnRegisterComposition::ordered_values),
            )
            .any(|value| {
                frame_affine_value(
                    artifact,
                    value.binding().value(),
                    entry_stack_pointer,
                    width_bits,
                    &mut affine,
                    &mut BTreeSet::new(),
                )
                .is_some()
            });
        let exit_offset = match control.exit_stack_pointer() {
            CertifiedExitStackPointer::PreservedEntry { storage } => {
                (*storage == stack_pointer_storage && !has_stack_pointer_def).then_some(0)
            }
            CertifiedExitStackPointer::ReachingValue { storage, value } => (*storage
                == stack_pointer_storage)
                .then(|| {
                    frame_affine_value(
                        artifact,
                        value.binding().value(),
                        entry_stack_pointer,
                        width_bits,
                        &mut affine,
                        &mut BTreeSet::new(),
                    )?
                    .signed_offset()
                })
                .flatten(),
        };
        let exit_offset = exit_offset?;
        let declared_stacked_return = artifact
            .machine_context()
            .function_interface()?
            .return_mechanism()
            .is_some();
        let return_address_read = match (declared_stacked_return, exit_offset) {
            (false, 0) => None,
            (false, _) => return None,
            (true, _) => Some(frame_stacked_return_read(
                FrameStackedReturnContext {
                    artifact,
                    memory_statements,
                    entry_stack_pointer,
                    stack_pointer_storage,
                    width_bits,
                },
                control,
                return_inst,
                exit_offset,
                &mut affine,
            )?),
        };
        let effective = restore_candidates
            .iter()
            .filter(|restore| {
                frame_instruction_dominates(artifact, restore.assignment_inst, return_inst)
            })
            .collect::<Vec<_>>();
        let [restore] = effective.as_slice() else {
            return None;
        };
        let later_frame_definition = (relation_inst != restore.assignment_inst
            && frame_instruction_can_reach(artifact, restore.assignment_inst, relation_inst)
            && frame_instruction_can_reach(artifact, relation_inst, return_inst))
            || restore_candidates.iter().any(|other| {
                other.assignment_inst != restore.assignment_inst
                    && frame_instruction_can_reach(
                        artifact,
                        restore.assignment_inst,
                        other.assignment_inst,
                    )
                    && frame_instruction_can_reach(artifact, other.assignment_inst, return_inst)
            });
        if return_escapes_frame
            || later_frame_definition
            || !graph.use_sites(restore.restored_value).is_empty()
        {
            return None;
        }
        used_restores.insert(restore.assignment_inst);
        restores.push((control.clone(), (*restore).clone(), return_address_read));
    }
    if used_restores.len() != restore_candidates.len() {
        return None;
    }
    if let Some(mechanism) = interface.return_mechanism() {
        let return_range = CertifiedNormalizedStackRange {
            offset: mechanism.stack_offset(),
            size_bytes: mechanism.slot_size_bytes(),
        };
        let sealed_return_reads = restores
            .iter()
            .map(|(_, _, read)| read.as_ref().map(CertifiedMemoryStatement::producer))
            .collect::<Option<BTreeSet<_>>>()?;
        for statement in memory_statements.values() {
            if statement.space() != MachineAddressSpace::Ram {
                continue;
            }
            let Some(range) = frame_normalized_range(
                artifact,
                statement,
                entry_stack_pointer,
                width_bits,
                &mut affine,
            ) else {
                if frame_statement_has_exact_nonstack_object(artifact, statement) {
                    continue;
                }
                return None;
            };
            if frame_ranges_overlap(return_range, range, width_bits)
                && !sealed_return_reads.contains(&statement.producer())
            {
                return None;
            }
        }
    }
    Some(FramePreservationEvidence {
        frame_pointer_storage,
        stack_pointer_storage,
        saved_range,
        stack_allocation,
        entry_save,
        entry_save_copies,
        frame_relation,
        restores,
    })
}

#[derive(Debug, Clone)]
struct StackAssignmentEvidence {
    inst: InstId,
    offset: i64,
    assignment: CertifiedStackPointerAssignment,
}

#[derive(Debug, Clone)]
struct StackDisciplineEvidence {
    stack_pointer_storage: CanonicalStorageId,
    entry_stack_pointer: MachineValueUse,
    reservation_range: CertifiedNormalizedStackRange,
    private_ownership_range: CertifiedNormalizedStackRange,
    implicit_active_sp_bytes: u32,
    reservation: CertifiedStackPointerAssignment,
    assignments: Vec<CertifiedStackPointerAssignment>,
    private_regions: Vec<CertifiedPrivateStackRegion>,
    releases: Vec<CertifiedStackRelease>,
}

pub(crate) fn exact_frame_pointer_storage_is_unused(
    artifact: &SsaArtifact,
    storage: CanonicalStorageId,
) -> bool {
    artifact.graph().values.iter().all(|value| {
        value.canonical_storage.is_none_or(|candidate| {
            !certified_register_storages_overlap(candidate, storage)
                || candidate == storage
                    && artifact.graph().def_inst(value.id).is_none()
                    && artifact.graph().use_sites(value.id).is_empty()
        })
    })
}

fn stack_discipline_evidence_from_certified_parts(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    topology: &CertifiedSourceTopology,
    memory_statements: &BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    return_controls: &BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
    frame: Option<&CertifiedFramePreservation>,
) -> Option<StackDisciplineEvidence> {
    let interface = artifact.machine_context().function_interface()?;
    let stack_pointer_storage = interface.stack_pointer_storage()?;
    let stack_allocation_contract = interface.stack_allocation_contract()?;
    match frame {
        Some(frame)
            if interface.exact_frame_pointer_storage() != Some(frame.frame_pointer_storage()) =>
        {
            return None;
        }
        None => {
            if let Some(storage) = interface.exact_frame_pointer_storage()
                && !exact_frame_pointer_storage_is_unused(artifact, storage)
            {
                return None;
            }
        }
        Some(_) => {}
    }
    let width_bits = stack_pointer_storage.size.checked_mul(8)?;
    if width_bits == 0 || width_bits > 64 || !frame_topology_is_balanced(topology) {
        return None;
    }
    let graph = artifact.graph();
    if !graph.block(graph.entry)?.predecessors.is_empty()
        || artifact
            .obligations()
            .instructions()
            .values()
            .any(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
        || artifact
            .obligations()
            .obligations()
            .values()
            .any(|obligation| obligation.id.kind == SemanticObligationKind::VolatileOrUnknownEffect)
        || graph.insts.iter().any(|inst| {
            matches!(
                inst.payload,
                InstPayload::Op(
                    SSAOp::Call { .. }
                        | SSAOp::CallInd { .. }
                        | SSAOp::CallOther { .. }
                        | SSAOp::LoadLinked { .. }
                        | SSAOp::StoreConditional { .. }
                        | SSAOp::AtomicCAS { .. }
                        | SSAOp::LoadGuarded { .. }
                        | SSAOp::StoreGuarded { .. }
                        | SSAOp::Fence { .. }
                )
            )
        })
    {
        return None;
    }
    let entry_values = graph
        .values
        .iter()
        .filter(|value| {
            value.canonical_storage == Some(stack_pointer_storage)
                && graph.def_inst(value.id).is_none()
        })
        .map(|value| value.id)
        .collect::<Vec<_>>();
    let [entry_stack_pointer_value] = entry_values.as_slice() else {
        return None;
    };
    let entry_stack_pointer_value = *entry_stack_pointer_value;
    let entry_stack_pointer =
        MachineValueUse::from_artifact(artifact, entry_stack_pointer_value).ok()?;
    if graph.values.iter().any(|value| {
        value.canonical_storage.is_some_and(|storage| {
            certified_register_storages_overlap(storage, stack_pointer_storage)
                && storage != stack_pointer_storage
        })
    }) {
        return None;
    }

    let mut affine = BTreeMap::new();
    if frame.is_some_and(|frame| {
        frame_normalized_range(
            artifact,
            frame.entry_save(),
            entry_stack_pointer_value,
            width_bits,
            &mut affine,
        ) != Some(frame.saved_range())
            || frame.restores().iter().any(|restore| {
                frame_normalized_range(
                    artifact,
                    restore.restore_read(),
                    entry_stack_pointer_value,
                    width_bits,
                    &mut affine,
                ) != Some(frame.saved_range())
            })
    }) {
        return None;
    }
    let mut assignment_evidence = Vec::new();
    for inst in &graph.insts {
        if inst.canonical_storage != Some(stack_pointer_storage) {
            continue;
        }
        let output = inst.output?;
        let offset = frame_affine_value(
            artifact,
            output,
            entry_stack_pointer_value,
            width_bits,
            &mut affine,
            &mut BTreeSet::new(),
        )?
        .signed_offset()?;
        assignment_evidence.push(StackAssignmentEvidence {
            inst: inst.id,
            offset,
            assignment: stack_pointer_assignment_for_inst(
                artifact,
                projection,
                inst.id,
                entry_stack_pointer_value,
                stack_pointer_storage,
                width_bits,
                &mut affine,
            )?,
        });
    }
    let reservations = assignment_evidence
        .iter()
        .filter(|assignment| match stack_allocation_contract.growth() {
            SourceStackGrowth::LowerAddresses => assignment.offset < 0,
            SourceStackGrowth::HigherAddresses => assignment.offset > 0,
        })
        .collect::<Vec<_>>();
    let [reservation] = reservations.as_slice() else {
        return None;
    };
    let (reservation_offset, reservation_size_i64) = match stack_allocation_contract.growth() {
        SourceStackGrowth::LowerAddresses => {
            (reservation.offset, reservation.offset.checked_neg()?)
        }
        SourceStackGrowth::HigherAddresses => (0, reservation.offset),
    };
    let reservation_size = u32::try_from(reservation_size_i64).ok()?;
    let reservation_range = CertifiedNormalizedStackRange {
        offset: reservation_offset,
        size_bytes: reservation_size,
    };
    if !stack_allocation_contract
        .owns_entry_relative_reservation(reservation_range.offset, reservation_range.size_bytes)
    {
        return None;
    }
    let private_ownership_envelope =
        stack_allocation_contract.owned_entry_relative_envelope(reservation.offset)?;
    let private_ownership_size = u32::try_from(
        private_ownership_envelope
            .end
            .checked_sub(private_ownership_envelope.start)?,
    )
    .ok()?;
    let private_ownership_range = CertifiedNormalizedStackRange {
        offset: private_ownership_envelope.start,
        size_bytes: private_ownership_size,
    };

    let return_blocks = topology
        .blocks()
        .iter()
        .filter(|block| matches!(block.terminator(), CertifiedSourceTerminator::Return))
        .count();
    if return_controls.len() != return_blocks || return_controls.is_empty() {
        return None;
    }
    let mechanism = interface.return_mechanism();
    let expected_exit_offset = mechanism
        .map(|mechanism| i64::from(mechanism.stack_pointer_delta_bytes()))
        .unwrap_or(0);
    let mut used_assignments = BTreeSet::from([reservation.inst]);
    let mut release_evidence = Vec::new();
    let mut sealed_return_reads = BTreeSet::new();
    for control in return_controls.values() {
        let return_inst = artifact
            .obligations()
            .instructions()
            .get(&control.producer())?
            .source
            .graph_inst()?;
        if std::iter::once(control.control_target())
            .chain(control.values().iter().map(CertifiedReturnValue::value))
            .chain(
                control
                    .register_compositions()
                    .iter()
                    .flat_map(CertifiedReturnRegisterComposition::ordered_values),
            )
            .any(|value| {
                frame_affine_value(
                    artifact,
                    value.binding().value(),
                    entry_stack_pointer_value,
                    width_bits,
                    &mut affine,
                    &mut BTreeSet::new(),
                )
                .is_some()
            })
        {
            return None;
        }
        let CertifiedExitStackPointer::ReachingValue { storage, value } =
            control.exit_stack_pointer()
        else {
            return None;
        };
        if *storage != stack_pointer_storage {
            return None;
        }
        let exit_assignments = assignment_evidence
            .iter()
            .filter(|assignment| {
                assignment.assignment.output().value() == value.binding().value()
                    && assignment.offset == expected_exit_offset
                    && frame_instruction_dominates(artifact, assignment.inst, return_inst)
            })
            .collect::<Vec<_>>();
        let [exit_assignment] = exit_assignments.as_slice() else {
            return None;
        };
        let return_address_read = if mechanism.is_some() {
            let read = frame_stacked_return_read(
                FrameStackedReturnContext {
                    artifact,
                    memory_statements,
                    entry_stack_pointer: entry_stack_pointer_value,
                    stack_pointer_storage,
                    width_bits,
                },
                control,
                return_inst,
                expected_exit_offset,
                &mut affine,
            )?;
            sealed_return_reads.insert(read.producer());
            Some(read)
        } else {
            None
        };
        let restorations = assignment_evidence
            .iter()
            .filter(|assignment| {
                assignment.offset == 0
                    && frame_instruction_dominates(artifact, reservation.inst, assignment.inst)
                    && frame_instruction_dominates(artifact, assignment.inst, return_inst)
                    && return_address_read.as_ref().is_none_or(|read| {
                        frame_instruction_dominates(artifact, assignment.inst, read.access().inst)
                            && frame_instruction_dominates(
                                artifact,
                                read.access().inst,
                                exit_assignment.inst,
                            )
                    })
            })
            .collect::<Vec<_>>();
        let [restoration] = restorations.as_slice() else {
            return None;
        };
        used_assignments.insert(restoration.inst);
        used_assignments.insert(exit_assignment.inst);
        release_evidence.push((
            return_inst,
            restoration.inst,
            CertifiedStackRelease {
                return_control: control.clone(),
                restoration: restoration.assignment.clone(),
                post_restoration: (exit_assignment.inst != restoration.inst)
                    .then(|| exit_assignment.assignment.clone()),
                return_address_read,
            },
        ));
    }
    if used_assignments
        != assignment_evidence
            .iter()
            .map(|assignment| assignment.inst)
            .collect()
    {
        return None;
    }

    let graph_memory_instructions = graph
        .insts
        .iter()
        .filter_map(|inst| {
            matches!(
                inst.payload,
                InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. })
            )
            .then_some(inst.id)
        })
        .collect::<BTreeSet<_>>();
    let certified_memory_instructions = memory_statements
        .values()
        .map(|statement| statement.access().inst)
        .collect::<BTreeSet<_>>();
    let source_memory_obligations = artifact
        .obligations()
        .obligations()
        .values()
        .filter(|obligation| {
            matches!(
                obligation.id.kind,
                SemanticObligationKind::ObservableMemoryRead
                    | SemanticObligationKind::ObservableMemoryWrite
            )
        })
        .map(|obligation| obligation.id)
        .collect::<BTreeSet<_>>();
    let certified_memory_obligations = memory_statements
        .values()
        .flat_map(|statement| statement.source_obligations().iter().copied())
        .collect::<BTreeSet<_>>();
    if graph_memory_instructions != certified_memory_instructions
        || source_memory_obligations != certified_memory_obligations
        || memory_statements.len() != graph_memory_instructions.len()
        || memory_statements.len() != source_memory_obligations.len()
    {
        return None;
    }

    let mut stack_regions = BTreeMap::<
        CertifiedNormalizedStackRange,
        (BTreeSet<ObjectId>, Vec<CertifiedPrivateStackAccess>),
    >::new();
    for statement in memory_statements.values() {
        if sealed_return_reads.contains(&statement.producer()) {
            continue;
        }
        if frame.is_some_and(|frame| {
            *statement == *frame.entry_save()
                || frame
                    .restores()
                    .iter()
                    .any(|restore| *statement == *restore.restore_read())
        }) {
            continue;
        }
        let normalized = frame_normalized_range(
            artifact,
            statement,
            entry_stack_pointer_value,
            width_bits,
            &mut affine,
        );
        let Some(range) = normalized else {
            if frame_statement_has_exact_nonstack_object(artifact, statement) {
                continue;
            }
            return None;
        };
        if frame.is_some_and(|frame| frame_ranges_overlap(frame.saved_range(), range, width_bits)) {
            return None;
        }
        if statement.space() != MachineAddressSpace::Ram
            || statement.word_size_bytes() != 1
            || !frame_range_contains(private_ownership_range, range)
            || !frame_value_descends_from(
                artifact,
                statement.address().binding().value(),
                reservation.assignment.output().value(),
                &mut BTreeSet::new(),
            )
            || !frame_instruction_dominates(artifact, reservation.inst, statement.access().inst)
            || !matches!(
                artifact.objects().objects.get(&statement.object()),
                Some(object) if matches!(
                    object.kind,
                    ObjectKind::StackSlot { space: r2il::SpaceId::Ram, .. }
                        | ObjectKind::FrameObject { space: r2il::SpaceId::Ram, .. }
                )
            )
        {
            return None;
        }
        for (return_inst, restoration_inst, _) in &release_evidence {
            if frame_instruction_can_reach(artifact, statement.access().inst, *return_inst)
                && (!frame_instruction_can_reach(
                    artifact,
                    statement.access().inst,
                    *restoration_inst,
                ) || frame_instruction_can_reach(
                    artifact,
                    *restoration_inst,
                    statement.access().inst,
                ))
            {
                return None;
            }
        }
        let region = stack_regions.entry(range).or_default();
        region.0.insert(statement.object());
        region.1.push(CertifiedPrivateStackAccess {
            statement: statement.clone(),
            range,
        });
    }
    let ranges = stack_regions.keys().copied().collect::<Vec<_>>();
    for (index, range) in ranges.iter().enumerate() {
        if ranges[index + 1..]
            .iter()
            .any(|other| frame_ranges_overlap(*range, *other, width_bits))
        {
            return None;
        }
    }
    let private_regions = stack_regions
        .into_iter()
        .map(
            |(accessed_range, (objects, accesses))| CertifiedPrivateStackRegion {
                objects: objects.into_iter().collect::<Vec<_>>().into_boxed_slice(),
                accessed_range,
                accesses: accesses.into_boxed_slice(),
            },
        )
        .collect();

    for value in &graph.values {
        if frame_affine_value(
            artifact,
            value.id,
            entry_stack_pointer_value,
            width_bits,
            &mut affine,
            &mut BTreeSet::new(),
        )
        .is_none()
        {
            continue;
        }
        for use_site in graph.use_sites(value.id) {
            let consumer = graph.inst(use_site.inst)?;
            let allowed = match &consumer.payload {
                InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. }) => {
                    use_site.input_idx == 0
                }
                InstPayload::Op(
                    SSAOp::Copy { .. } | SSAOp::IntAdd { .. } | SSAOp::IntSub { .. },
                )
                | InstPayload::Phi { .. } => consumer.output.is_some_and(|output| {
                    frame_affine_value(
                        artifact,
                        output,
                        entry_stack_pointer_value,
                        width_bits,
                        &mut affine,
                        &mut BTreeSet::new(),
                    )
                    .is_some()
                }),
                _ => frame_affine_leaf_dead_consumer(artifact, value.id, *use_site),
            };
            if !allowed {
                return None;
            }
        }
    }

    Some(StackDisciplineEvidence {
        stack_pointer_storage,
        entry_stack_pointer,
        reservation_range,
        private_ownership_range,
        implicit_active_sp_bytes: stack_allocation_contract.implicit_active_sp_bytes(),
        reservation: reservation.assignment.clone(),
        assignments: assignment_evidence
            .into_iter()
            .map(|assignment| assignment.assignment)
            .collect(),
        private_regions,
        releases: release_evidence
            .into_iter()
            .map(|(_, _, release)| release)
            .collect(),
    })
}

#[derive(Clone, Copy)]
struct FrameCertifiedParts<'a> {
    projection: &'a MachineProjection,
    topology: &'a CertifiedSourceTopology,
    expressions: &'a BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    memory_statements: &'a BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    return_controls: &'a BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
}

fn certified_stack_discipline(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    parts: FrameCertifiedParts<'_>,
    frame: Option<&CertifiedFramePreservation>,
    ledger: &ObligationLedger,
) -> Option<CertifiedStackDiscipline> {
    if !origin.is_valid() || !ledger.matches_origin(origin) {
        return None;
    }
    if frame.is_some_and(|frame| {
        frame.origin() != origin
            || frame.origin().schema_version() != CERTIFICATION_SCHEMA_VERSION
            || artifact
                .machine_context()
                .function_interface()
                .and_then(|interface| interface.stack_pointer_storage())
                != Some(frame.stack_pointer_storage())
            || parts.memory_statements.get(&frame.entry_save().producer())
                != Some(frame.entry_save())
            || !frame_statement_is_ledgered(frame.entry_save(), ledger)
            || frame.restores().iter().any(|restore| {
                restore.restore_read().space() != frame.entry_save().space()
                    || restore.restore_read().word_size_bytes()
                        != frame.entry_save().word_size_bytes()
                    || restore.restore_read().width_bits() != frame.entry_save().width_bits()
                    || restore.restore_read().endianness() != frame.entry_save().endianness()
                    || parts
                        .memory_statements
                        .get(&restore.restore_read().producer())
                        != Some(restore.restore_read())
                    || !frame_statement_is_ledgered(restore.restore_read(), ledger)
            })
    }) {
        return None;
    }
    let evidence = stack_discipline_evidence_from_certified_parts(
        artifact,
        parts.projection,
        parts.topology,
        parts.memory_statements,
        parts.return_controls,
        frame,
    )?;
    let no_obligations = BTreeSet::new();
    if evidence.assignments.iter().any(|assignment| {
        !frame_mechanical_producer_is_accounted(
            artifact,
            parts.projection,
            FrameMechanicalWitness {
                producer: assignment.producer,
                root: assignment.root,
                output: assignment.output,
            },
            &no_obligations,
            parts.expressions,
            ledger,
        )
    }) || evidence.private_regions.iter().any(|region| {
        region
            .accesses
            .iter()
            .any(|access| !frame_statement_is_ledgered(&access.statement, ledger))
    }) || evidence.releases.iter().any(|release| {
        !frame_return_is_ledgered(&release.return_control, ledger)
            || release
                .return_address_read
                .as_ref()
                .is_some_and(|statement| !frame_statement_is_ledgered(statement, ledger))
    }) {
        return None;
    }
    Some(CertifiedStackDiscipline {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        stack_pointer_storage: evidence.stack_pointer_storage,
        entry_stack_pointer: evidence.entry_stack_pointer,
        reservation_range: evidence.reservation_range,
        private_ownership_range: evidence.private_ownership_range,
        implicit_active_sp_bytes: evidence.implicit_active_sp_bytes,
        reservation: evidence.reservation,
        assignments: evidence.assignments.into_boxed_slice(),
        private_regions: evidence.private_regions.into_boxed_slice(),
        releases: evidence.releases.into_boxed_slice(),
    })
}

fn certified_frame_preservation(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    parts: FrameCertifiedParts<'_>,
    ledger: &ObligationLedger,
) -> Option<CertifiedFramePreservation> {
    if !origin.is_valid() || !ledger.matches_origin(origin) {
        return None;
    }
    let evidence = frame_evidence_from_certified_parts(
        artifact,
        parts.projection,
        parts.topology,
        parts.expressions,
        parts.memory_statements,
        parts.return_controls,
    )?;
    let no_obligations = BTreeSet::new();
    if !frame_expression_is_ledgered(&evidence.stack_allocation, ledger)
        || !frame_mechanical_producer_is_accounted(
            artifact,
            parts.projection,
            FrameMechanicalWitness {
                producer: evidence.frame_relation.producer,
                root: evidence.frame_relation.root,
                output: evidence.frame_relation.output,
            },
            &no_obligations,
            parts.expressions,
            ledger,
        )
        || !frame_statement_is_ledgered(&evidence.entry_save, ledger)
        || evidence
            .entry_save_copies
            .iter()
            .any(|copy| !frame_expression_is_ledgered(copy, ledger))
        || evidence
            .restores
            .iter()
            .any(|(control, restore, return_address_read)| {
                !frame_return_is_ledgered(control, ledger)
                    || !frame_statement_is_ledgered(&restore.read, ledger)
                    || return_address_read
                        .as_ref()
                        .is_some_and(|statement| !frame_statement_is_ledgered(statement, ledger))
                    || !frame_mechanical_producer_is_accounted(
                        artifact,
                        parts.projection,
                        FrameMechanicalWitness {
                            producer: restore.assignment.producer,
                            root: restore.assignment.root,
                            output: restore.assignment.output,
                        },
                        if restore.assignment.producer == restore.read.producer() {
                            restore.read.source_obligations()
                        } else {
                            &no_obligations
                        },
                        parts.expressions,
                        ledger,
                    )
                    || restore.copies.iter().any(|copy| {
                        !frame_mechanical_producer_is_accounted(
                            artifact,
                            parts.projection,
                            FrameMechanicalWitness {
                                producer: copy.producer,
                                root: copy.root,
                                output: copy.output,
                            },
                            &no_obligations,
                            parts.expressions,
                            ledger,
                        )
                    })
            })
    {
        return None;
    }
    Some(CertifiedFramePreservation {
        origin: origin.clone(),
        frame_pointer_storage: evidence.frame_pointer_storage,
        stack_pointer_storage: evidence.stack_pointer_storage,
        saved_range: evidence.saved_range,
        stack_allocation: evidence.stack_allocation,
        entry_save: evidence.entry_save,
        entry_save_copies: evidence.entry_save_copies.into_boxed_slice(),
        frame_relation: evidence.frame_relation,
        restores: evidence
            .restores
            .into_iter()
            .map(
                |(return_control, restore, return_address_read)| CertifiedFrameRestore {
                    return_control,
                    return_address_read,
                    restore_read: restore.read,
                    restore_copies: restore.copies.into_boxed_slice(),
                    restore_assignment: restore.assignment,
                },
            )
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    })
}

/// Replay the complete frame witness after the caller has bound `artifact` to
/// `origin`. Both production callers enforce that artifact-authority check at
/// their public or construction boundary before entering this kernel.
pub(crate) fn replay_certified_frame_preservation(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
) -> Option<CertifiedFramePreservation> {
    if !origin.is_valid()
        || origin.source() != artifact.obligations()
        || !ledger.matches_origin(origin)
    {
        return None;
    }
    let projection = MachineProjection::from_artifact(artifact).ok()?;
    projection.validate_against(artifact).ok()?;
    let topology = certified_source_topology(artifact).ok()?;
    if &topology != origin.topology() {
        return None;
    }
    let memory_statements = certified_memory_statements(artifact).ok()?;
    let return_controls = certified_return_controls(artifact, &topology).ok()?;
    let mut expressions = BTreeMap::new();
    for entity in projection.entities() {
        let obligations = entity
            .source_obligations()
            .iter()
            .copied()
            .filter(|obligation| obligation.kind == SemanticObligationKind::LiveValueProducer)
            .collect::<BTreeSet<_>>();
        if obligations.is_empty() {
            continue;
        }
        let expression =
            certified_expr_from_machine(artifact, &projection, entity, obligations).ok()?;
        if expressions.insert(entity.producer(), expression).is_some() {
            return None;
        }
    }
    certified_frame_preservation(
        artifact,
        origin,
        FrameCertifiedParts {
            projection: &projection,
            topology: &topology,
            expressions: &expressions,
            memory_statements: &memory_statements,
            return_controls: &return_controls,
        },
        ledger,
    )
}

/// Machine semantics and their source-bound certification ledger.
///
/// Construction is intentionally artifact-only: callers cannot combine a
/// `MachineProjection` with an inventory from another artifact. It retains sealed
/// expression, plain-memory, and admitted terminal-control evidence. These
/// dispositions remain pending typed-region validation and cannot independently
/// authorize final C.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedMachineFunction {
    origin: CertifiedArtifactOrigin,
    projection: MachineProjection,
    machine_context: CertifiedMachineContext,
    abi_parameters: BTreeMap<u32, CertifiedAbiParameter>,
    stack_slots: BTreeMap<StackAddressRoot, CertifiedStackSlot>,
    certification: CertifiedFunction,
    expressions: BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    memory_statements: BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    aggregate_member_accesses: BTreeMap<StructuredAccessId, CertifiedAggregateMemberAccess>,
    direct_calls: BTreeMap<CanonicalInstructionId, CertifiedDirectCall>,
    direct_controls: BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    conditional_controls: BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
    return_controls: BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
    natural_loop_routings: BTreeMap<u64, CertifiedNaturalLoopRouting>,
    closed_natural_loop_controls: BTreeMap<u64, CertifiedClosedNaturalLoopControl>,
    switch_topologies: BTreeMap<u64, CertifiedSwitchTopology>,
    switch_controls: BTreeMap<u64, CertifiedSwitchControl>,
    stack_discipline: Option<CertifiedStackDiscipline>,
    private_frame_value_flows: BTreeMap<StructuredAccessId, CertifiedPrivateFrameValueFlow>,
    private_frame_conditional_joins: BTreeMap<u64, CertifiedPrivateFrameConditionalJoin>,
    frame_preservation: Option<CertifiedFramePreservation>,
    topology: CertifiedSourceTopology,
}

impl CertifiedMachineFunction {
    pub fn from_artifact(trusted: &TrustedSsaArtifact) -> Result<Self, MachineBuildError> {
        let artifact = trusted.artifact();
        let projection = MachineProjection::from_artifact(artifact)?;
        projection.validate_against(artifact)?;
        let machine_context = CertifiedMachineContext::from_artifact(artifact)?;
        let topology = certified_source_topology(artifact)?;
        let origin = certified_artifact_origin(trusted, &machine_context, &topology)?;
        let abi_parameters = certified_abi_parameters(artifact)?;
        let stack_slots = certified_stack_slots(artifact)?;
        let direct_calls = certified_direct_calls(artifact, &topology)?;
        let direct_controls = certified_direct_controls(artifact, &topology)?;
        let conditional_controls = certified_conditional_controls(artifact, &topology)?;
        let return_controls = certified_return_controls(artifact, &topology)?;
        let memory_statements = certified_memory_statements(artifact)?;
        let aggregate_member_accesses = aggregate_member::certified_aggregate_member_accesses(
            artifact,
            &origin,
            &abi_parameters,
            &memory_statements,
        )?;
        let switch_topologies = certified_switch_topologies(artifact, &origin, &topology)?;
        let switch_controls =
            certified_switch_controls(artifact, &origin, &switch_topologies, &abi_parameters)?;
        let natural_loop_routings = certified_natural_loop_routings(
            artifact,
            &origin,
            &topology,
            &direct_controls,
            &conditional_controls,
        )?;
        let closed_natural_loop_controls = certified_closed_natural_loop_controls(
            artifact,
            &origin,
            &topology,
            &natural_loop_routings,
            &direct_controls,
            &abi_parameters,
        )?;
        let mut expressions = BTreeMap::new();
        for machine_entity in projection.entities() {
            let source_obligations = machine_entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if source_obligations.is_empty() {
                continue;
            }
            let inst_id = artifact
                .graph()
                .def_inst(machine_entity.output().value())
                .ok_or(MachineBuildError::ObligationSourceMismatch(
                    machine_entity.producer(),
                ))?;
            let expression = certified_expr_from_machine(
                artifact,
                &projection,
                machine_entity,
                source_obligations,
            )?;
            if expressions
                .insert(machine_entity.producer(), expression)
                .is_some()
            {
                return Err(MachineBuildError::ObligationMismatch(inst_id));
            }
        }
        let source = artifact.obligations().clone();
        let mut certification = CertifiedFunction::bound(source, &origin)
            .map_err(|_| MachineBuildError::IncompleteObligationInventory)?;
        let mut absorbed = BTreeSet::new();

        let mut absorbed_calls = BTreeSet::new();
        for call in direct_calls.values() {
            if call
                .source_obligations()
                .iter()
                .all(|obligation| absorbed.contains(obligation))
            {
                continue;
            }
            for obligation in call.source_obligations() {
                if !absorbed_calls.insert(obligation) {
                    return Err(MachineBuildError::ObligationMismatch(call.source_inst));
                }
            }
            certification
                .record_absorbed_call(call.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(call.source_inst))?;
        }

        let mut absorbed_controls = BTreeSet::new();
        for control in direct_controls.values() {
            if absorbed.contains(&control.source_obligation()) {
                continue;
            }
            if !absorbed_controls.insert(control.source_obligation()) {
                return Err(MachineBuildError::ObligationMismatch(control.source_inst));
            }
            certification
                .record_absorbed_control(control.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(control.source_inst))?;
        }
        for control in conditional_controls.values() {
            if control
                .source_obligations()
                .iter()
                .all(|obligation| absorbed.contains(obligation))
            {
                continue;
            }
            for obligation in control.source_obligations() {
                if !absorbed_controls.insert(obligation) {
                    return Err(MachineBuildError::ObligationMismatch(control.source_inst));
                }
            }
            certification
                .record_absorbed_conditional_control(control.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(control.source_inst))?;
        }
        for control in switch_controls.values() {
            let obligation = control.source_obligation();
            if absorbed.contains(&obligation) {
                continue;
            }
            if !absorbed_controls.insert(obligation) {
                let source_inst = artifact
                    .obligations()
                    .obligations()
                    .get(&obligation)
                    .map(|fact| fact.source);
                return Err(source_inst.map_or(
                    MachineBuildError::ObligationSourceMismatch(obligation.instruction),
                    |source| source_site_mismatch(obligation.instruction, source),
                ));
            }
            certification
                .record_absorbed_switch_control(control.clone())
                .map_err(|_| MachineBuildError::ObligationSourceMismatch(obligation.instruction))?;
        }
        for control in return_controls.values() {
            if control
                .source_obligations()
                .iter()
                .all(|obligation| absorbed.contains(obligation))
            {
                continue;
            }
            for obligation in control.source_obligations() {
                if !absorbed_controls.insert(obligation) {
                    return Err(MachineBuildError::ObligationMismatch(control.source_inst));
                }
            }
            certification
                .record_absorbed_return(control.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(control.source_inst))?;
        }

        for statement in memory_statements.values() {
            for obligation in statement.source_obligations() {
                if absorbed.contains(obligation) {
                    continue;
                }
                if !absorbed.insert(*obligation) {
                    return Err(MachineBuildError::ObligationMismatch(
                        statement.access().inst,
                    ));
                }
                certification
                    .record_absorbed_statement(*obligation, statement.clone())
                    .map_err(|_| MachineBuildError::ObligationMismatch(statement.access().inst))?;
            }
        }

        for expression in expressions.values() {
            let producer = expression.entity().producer();
            let source_inst = artifact
                .obligations()
                .instructions()
                .get(&producer)
                .map(|source| source.source)
                .ok_or(MachineBuildError::ObligationSourceMismatch(producer))?;
            let pending_obligations = expression
                .entity()
                .source_obligations()
                .iter()
                .copied()
                .filter(|obligation| !absorbed.contains(obligation))
                .collect::<Vec<_>>();
            for obligation in pending_obligations {
                if !absorbed.insert(obligation) {
                    return Err(source_site_mismatch(producer, source_inst));
                }
                certification
                    .record_absorbed_expression(obligation, expression.clone())
                    .map_err(|_| source_site_mismatch(producer, source_inst))?;
            }
        }

        for obligation in artifact
            .obligations()
            .obligations()
            .values()
            .filter(|obligation| obligation.id.kind == SemanticObligationKind::LiveValueProducer)
        {
            if !absorbed.contains(&obligation.id) {
                return Err(source_site_mismatch(
                    obligation.id.instruction,
                    obligation.source,
                ));
            }
        }

        for statement in memory_statements.values() {
            let missing_inputs = memory_statement_input_producers(statement)
                .iter()
                .copied()
                .filter(|producer| !expressions.contains_key(producer))
                .collect::<BTreeSet<_>>();
            if !missing_inputs.is_empty() {
                return Err(MachineBuildError::ObligationMismatch(
                    statement.access().inst,
                ));
            }
            if matches!(statement.kind(), CertifiedMemoryStatementKind::Read { .. }) {
                let entity = projection.entity_for_producer(statement.producer()).ok_or(
                    MachineBuildError::ObligationMismatch(statement.access().inst),
                )?;
                let kind = projection
                    .expr(entity.root())
                    .map(|expression| expression.kind())
                    .ok_or(MachineBuildError::ObligationMismatch(
                        statement.access().inst,
                    ))?;
                if !certified_read_matches_machine_entity(statement, entity, kind) {
                    return Err(MachineBuildError::ObligationMismatch(
                        statement.access().inst,
                    ));
                }
            }
        }

        for control in conditional_controls.values() {
            if conditional_control_input_producers(control)
                .iter()
                .any(|producer| !expressions.contains_key(producer))
            {
                return Err(MachineBuildError::ObligationMismatch(control.source_inst));
            }
        }

        for call in direct_calls.values() {
            if direct_call_input_producers(call)
                .iter()
                .any(|producer| !expressions.contains_key(producer))
            {
                return Err(MachineBuildError::ObligationMismatch(call.source_inst));
            }
        }

        for control in return_controls.values() {
            if return_control_input_producers(control)
                .iter()
                .any(|producer| !expressions.contains_key(producer))
            {
                return Err(MachineBuildError::ObligationMismatch(control.source_inst));
            }
        }

        let certified_parts = FrameCertifiedParts {
            projection: &projection,
            topology: &topology,
            expressions: &expressions,
            memory_statements: &memory_statements,
            return_controls: &return_controls,
        };
        let frame_preservation = certified_frame_preservation(
            artifact,
            &origin,
            certified_parts,
            certification.ledger(),
        );
        let stack_discipline = certified_stack_discipline(
            artifact,
            &origin,
            certified_parts,
            frame_preservation.as_ref(),
            certification.ledger(),
        );
        let private_frame_value_flows =
            private_frame_value_flow::certified_private_frame_value_flows(
                artifact,
                &origin,
                stack_discipline.as_ref(),
                &memory_statements,
                certification.ledger(),
            );
        let private_frame_conditional_joins =
            private_frame_conditional_join::certified_private_frame_conditional_joins(
                private_frame_conditional_join::PrivateFrameConditionalJoinCertificationInput {
                    artifact,
                    origin: &origin,
                    topology: &topology,
                    stack: stack_discipline.as_ref(),
                    frame: frame_preservation.as_ref(),
                    flows: &private_frame_value_flows,
                    direct_controls: &direct_controls,
                    conditional_controls: &conditional_controls,
                    return_controls: &return_controls,
                    ledger: certification.ledger(),
                },
            );
        Ok(Self {
            origin,
            projection,
            machine_context,
            abi_parameters,
            stack_slots,
            certification,
            expressions,
            memory_statements,
            aggregate_member_accesses,
            direct_calls,
            direct_controls,
            conditional_controls,
            return_controls,
            natural_loop_routings,
            closed_natural_loop_controls,
            switch_topologies,
            switch_controls,
            stack_discipline,
            private_frame_value_flows,
            private_frame_conditional_joins,
            frame_preservation,
            topology,
        })
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn projection(&self) -> &MachineProjection {
        &self.projection
    }

    pub const fn machine_context(&self) -> &CertifiedMachineContext {
        &self.machine_context
    }

    pub const fn abi_parameters(&self) -> &BTreeMap<u32, CertifiedAbiParameter> {
        &self.abi_parameters
    }

    pub const fn stack_slots(&self) -> &BTreeMap<StackAddressRoot, CertifiedStackSlot> {
        &self.stack_slots
    }

    pub const fn frame_preservation(&self) -> Option<&CertifiedFramePreservation> {
        self.frame_preservation.as_ref()
    }

    pub const fn stack_discipline(&self) -> Option<&CertifiedStackDiscipline> {
        self.stack_discipline.as_ref()
    }

    pub fn private_frame_value_flow(
        &self,
        load: StructuredAccessId,
    ) -> Option<&CertifiedPrivateFrameValueFlow> {
        self.private_frame_value_flows.get(&load)
    }

    pub const fn private_frame_value_flows(
        &self,
    ) -> &BTreeMap<StructuredAccessId, CertifiedPrivateFrameValueFlow> {
        &self.private_frame_value_flows
    }

    pub fn private_frame_conditional_join(
        &self,
        header: u64,
    ) -> Option<&CertifiedPrivateFrameConditionalJoin> {
        self.private_frame_conditional_joins.get(&header)
    }

    pub const fn private_frame_conditional_joins(
        &self,
    ) -> &BTreeMap<u64, CertifiedPrivateFrameConditionalJoin> {
        &self.private_frame_conditional_joins
    }

    pub fn source(&self) -> &SemanticObligationInventory {
        self.certification.source()
    }

    pub fn ledger(&self) -> &ObligationLedger {
        self.certification.ledger()
    }

    pub const fn topology(&self) -> &CertifiedSourceTopology {
        &self.topology
    }

    /// Certified expression bound to one canonical producer.
    pub fn expression_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedExpr> {
        self.expressions.get(&producer)
    }

    pub fn memory_statement_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedMemoryStatement> {
        self.memory_statements.get(&producer)
    }

    pub fn aggregate_member_access(
        &self,
        access: StructuredAccessId,
    ) -> Option<&CertifiedAggregateMemberAccess> {
        self.aggregate_member_accesses.get(&access)
    }

    pub const fn aggregate_member_accesses(
        &self,
    ) -> &BTreeMap<StructuredAccessId, CertifiedAggregateMemberAccess> {
        &self.aggregate_member_accesses
    }

    pub fn direct_call_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedDirectCall> {
        self.direct_calls.get(&producer)
    }

    pub const fn direct_calls(&self) -> &BTreeMap<CanonicalInstructionId, CertifiedDirectCall> {
        &self.direct_calls
    }

    pub fn direct_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedDirectControl> {
        self.direct_controls.get(&producer)
    }

    pub fn conditional_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedConditionalControl> {
        self.conditional_controls.get(&producer)
    }

    pub fn return_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedReturnControl> {
        self.return_controls.get(&producer)
    }

    pub const fn return_controls(
        &self,
    ) -> &BTreeMap<CanonicalInstructionId, CertifiedReturnControl> {
        &self.return_controls
    }

    pub fn natural_loop_routing_for_header(
        &self,
        header: u64,
    ) -> Option<&CertifiedNaturalLoopRouting> {
        self.natural_loop_routings.get(&header)
    }

    pub fn closed_natural_loop_control_for_header(
        &self,
        header: u64,
    ) -> Option<&CertifiedClosedNaturalLoopControl> {
        self.closed_natural_loop_controls.get(&header)
    }

    pub fn switch_topology_for_block(&self, block_addr: u64) -> Option<&CertifiedSwitchTopology> {
        self.switch_topologies.get(&block_addr)
    }

    pub fn switch_control_for_block(&self, block_addr: u64) -> Option<&CertifiedSwitchControl> {
        self.switch_controls.get(&block_addr)
    }

    pub fn finish(&self) -> CertificationReport {
        let mut report = self.certification.finish();
        report.typed_region_required = true;
        report
    }
}

/// Fail-closed machine projection retaining supported expression, plain-memory,
/// and admitted terminal-control evidence. Unsupported producers and their
/// dependents receive exact residual dispositions. Retained evidence remains
/// pending typed-region validation and cannot independently authorize final C.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedMachineProjection {
    origin: CertifiedArtifactOrigin,
    projection: MachineProjection,
    machine_context: CertifiedMachineContext,
    abi_parameters: BTreeMap<u32, CertifiedAbiParameter>,
    stack_slots: BTreeMap<StackAddressRoot, CertifiedStackSlot>,
    certification: CertifiedFunction,
    expressions: BTreeMap<CanonicalInstructionId, CertifiedExpr>,
    memory_statements: BTreeMap<CanonicalInstructionId, CertifiedMemoryStatement>,
    aggregate_member_accesses: BTreeMap<StructuredAccessId, CertifiedAggregateMemberAccess>,
    direct_calls: BTreeMap<CanonicalInstructionId, CertifiedDirectCall>,
    direct_controls: BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    conditional_controls: BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
    return_controls: BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
    natural_loop_routings: BTreeMap<u64, CertifiedNaturalLoopRouting>,
    closed_natural_loop_controls: BTreeMap<u64, CertifiedClosedNaturalLoopControl>,
    switch_topologies: BTreeMap<u64, CertifiedSwitchTopology>,
    switch_controls: BTreeMap<u64, CertifiedSwitchControl>,
    stack_discipline: Option<CertifiedStackDiscipline>,
    private_frame_value_flows: BTreeMap<StructuredAccessId, CertifiedPrivateFrameValueFlow>,
    private_frame_conditional_joins: BTreeMap<u64, CertifiedPrivateFrameConditionalJoin>,
    frame_preservation: Option<CertifiedFramePreservation>,
    residual_producers: BTreeSet<CanonicalInstructionId>,
    topology: CertifiedSourceTopology,
}

impl CertifiedMachineProjection {
    pub fn from_artifact(trusted: &TrustedSsaArtifact) -> Result<Self, MachineBuildError> {
        let artifact = trusted.artifact();
        let projection = MachineProjection::from_artifact(artifact)?;
        projection.validate_against(artifact)?;
        let machine_context = CertifiedMachineContext::from_artifact(artifact)?;
        let topology = certified_source_topology(artifact)?;
        let origin = certified_artifact_origin(trusted, &machine_context, &topology)?;
        let abi_parameters = certified_abi_parameters(artifact)?;
        let stack_slots = certified_stack_slots(artifact)?;
        let candidate_direct_calls = certified_direct_calls(artifact, &topology)?;
        let direct_controls = certified_direct_controls(artifact, &topology)?;
        let candidate_conditional_controls = certified_conditional_controls(artifact, &topology)?;
        let candidate_return_controls = certified_return_controls(artifact, &topology)?;
        let switch_topologies = certified_switch_topologies(artifact, &origin, &topology)?;
        let candidate_switch_controls =
            certified_switch_controls(artifact, &origin, &switch_topologies, &abi_parameters)?;
        let candidate_natural_loop_routings = certified_natural_loop_routings(
            artifact,
            &origin,
            &topology,
            &direct_controls,
            &candidate_conditional_controls,
        )?;
        let graph = artifact.graph();
        let source = artifact.obligations().clone();
        let mut certification = CertifiedFunction::bound(source, &origin)
            .map_err(|_| MachineBuildError::IncompleteObligationInventory)?;
        let candidate_memory_statements = certified_memory_statements(artifact)?;
        let mut absorbed_controls = BTreeSet::new();
        for control in direct_controls.values() {
            if !absorbed_controls.insert(control.source_obligation()) {
                return Err(MachineBuildError::ObligationMismatch(control.source_inst));
            }
            certification
                .record_absorbed_control(control.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(control.source_inst))?;
        }
        let mut blocked_outputs = projection
            .failures()
            .iter()
            .map(|failure| failure.output())
            .collect::<BTreeSet<_>>();
        blocked_outputs.extend(
            artifact
                .obligations()
                .instructions()
                .values()
                .filter(|instruction| {
                    instruction.obligations.iter().any(|obligation| {
                        matches!(
                            obligation.kind,
                            SemanticObligationKind::ObservableMemoryRead
                                | SemanticObligationKind::ObservableMemoryWrite
                        )
                    }) && !candidate_memory_statements.contains_key(&instruction.id)
                })
                .filter_map(|instruction| {
                    instruction
                        .source
                        .graph_inst()
                        .and_then(|inst| graph.inst(inst))
                        .and_then(|instruction| instruction.output)
                }),
        );
        blocked_outputs.extend(
            artifact
                .obligations()
                .instructions()
                .values()
                .filter(|instruction| {
                    instruction.state == SemanticInstructionState::UnsupportedUnknown
                })
                .filter_map(|instruction| {
                    instruction
                        .source
                        .graph_inst()
                        .and_then(|inst| graph.inst(inst))
                        .and_then(|instruction| instruction.output)
                }),
        );

        loop {
            let mut changed = false;
            for entity in projection.entities() {
                if blocked_outputs.contains(&entity.output().value()) {
                    continue;
                }
                let inst_id = graph.def_inst(entity.output().value()).ok_or(
                    MachineBuildError::ObligationSourceMismatch(entity.producer()),
                )?;
                let inst = graph
                    .inst(inst_id)
                    .ok_or(MachineBuildError::MissingInstruction(inst_id))?;
                if inst
                    .inputs
                    .iter()
                    .any(|input| blocked_outputs.contains(input))
                {
                    changed |= blocked_outputs.insert(entity.output().value());
                }
            }
            if !changed {
                break;
            }
        }

        let mut residual_producers = BTreeSet::new();
        for instruction in artifact.obligations().instructions().values() {
            let blocked_output = instruction
                .source
                .graph_inst()
                .and_then(|inst| graph.inst(inst))
                .and_then(|inst| inst.output)
                .is_some_and(|output| blocked_outputs.contains(&output));
            if instruction.state == SemanticInstructionState::UnsupportedUnknown || blocked_output {
                residual_producers.insert(instruction.id);
            }
        }
        let direct_calls = candidate_direct_calls
            .into_iter()
            .filter(|(_, call)| {
                direct_call_input_producers(call)
                    .iter()
                    .all(|producer| !residual_producers.contains(producer))
            })
            .collect::<BTreeMap<_, _>>();
        let memory_statements = candidate_memory_statements
            .into_iter()
            .filter(|(_, statement)| {
                let address_is_supported = statement
                    .address()
                    .producer()
                    .is_none_or(|producer| !residual_producers.contains(&producer));
                let value_is_supported = match statement.kind() {
                    CertifiedMemoryStatementKind::Read { .. } => true,
                    CertifiedMemoryStatementKind::Write { value } => value
                        .producer()
                        .is_none_or(|producer| !residual_producers.contains(&producer)),
                };
                address_is_supported && value_is_supported
            })
            .collect::<BTreeMap<_, _>>();
        let aggregate_member_accesses = aggregate_member::certified_aggregate_member_accesses(
            artifact,
            &origin,
            &abi_parameters,
            &memory_statements,
        )?;
        let conditional_controls = candidate_conditional_controls
            .into_iter()
            .filter(|(_, control)| {
                conditional_control_input_producers(control)
                    .iter()
                    .all(|producer| !residual_producers.contains(producer))
            })
            .collect::<BTreeMap<_, _>>();
        let return_controls = candidate_return_controls
            .into_iter()
            .filter(|(_, control)| {
                return_control_input_producers(control)
                    .iter()
                    .all(|producer| !residual_producers.contains(producer))
            })
            .collect::<BTreeMap<_, _>>();
        let natural_loop_routings = candidate_natural_loop_routings
            .into_iter()
            .filter(|(_, routing)| {
                conditional_controls.contains_key(&routing.header_control().producer())
                    && direct_controls.contains_key(&routing.body_transfer().producer())
            })
            .collect::<BTreeMap<_, _>>();
        let closed_natural_loop_controls = certified_closed_natural_loop_controls(
            artifact,
            &origin,
            &topology,
            &natural_loop_routings,
            &direct_controls,
            &abi_parameters,
        )?;
        let switch_controls = candidate_switch_controls;
        let mut absorbed_calls = BTreeSet::new();
        for call in direct_calls.values() {
            for obligation in call.source_obligations() {
                if !absorbed_calls.insert(obligation) {
                    return Err(MachineBuildError::ObligationMismatch(call.source_inst));
                }
            }
            certification
                .record_absorbed_call(call.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(call.source_inst))?;
        }
        for control in conditional_controls.values() {
            for obligation in control.source_obligations() {
                if !absorbed_controls.insert(obligation) {
                    return Err(MachineBuildError::ObligationMismatch(control.source_inst));
                }
            }
            certification
                .record_absorbed_conditional_control(control.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(control.source_inst))?;
        }
        for control in switch_controls.values() {
            let obligation = control.source_obligation();
            if !absorbed_controls.insert(obligation) {
                return Err(MachineBuildError::ObligationMismatch(
                    control.topology.source_inst,
                ));
            }
            certification
                .record_absorbed_switch_control(control.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(control.topology.source_inst))?;
        }
        for control in return_controls.values() {
            for obligation in control.source_obligations() {
                if !absorbed_controls.insert(obligation) {
                    return Err(MachineBuildError::ObligationMismatch(control.source_inst));
                }
            }
            certification
                .record_absorbed_return(control.clone())
                .map_err(|_| MachineBuildError::ObligationMismatch(control.source_inst))?;
        }
        let mut absorbed_statements = BTreeSet::new();
        for statement in memory_statements.values() {
            for obligation in statement.source_obligations() {
                if !absorbed_statements.insert(*obligation) {
                    return Err(MachineBuildError::ObligationMismatch(
                        statement.access().inst,
                    ));
                }
                certification
                    .record_absorbed_statement(*obligation, statement.clone())
                    .map_err(|_| MachineBuildError::ObligationMismatch(statement.access().inst))?;
            }
        }

        let mut residualized = BTreeSet::new();
        for instruction in artifact.obligations().instructions().values() {
            let blocked_output = instruction
                .source
                .graph_inst()
                .and_then(|inst| graph.inst(inst))
                .and_then(|inst| inst.output)
                .is_some_and(|output| blocked_outputs.contains(&output));
            let has_memory_obligation = instruction.obligations.iter().any(|obligation| {
                matches!(
                    obligation.kind,
                    SemanticObligationKind::ObservableMemoryRead
                        | SemanticObligationKind::ObservableMemoryWrite
                )
            });
            let lacks_memory_statement =
                has_memory_obligation && !memory_statements.contains_key(&instruction.id);
            let has_call_obligation = instruction.obligations.iter().any(|obligation| {
                matches!(
                    obligation.kind,
                    SemanticObligationKind::Call
                        | SemanticObligationKind::CallArgument
                        | SemanticObligationKind::CallResult
                )
            });
            let lacks_call_certificate =
                has_call_obligation && !direct_calls.contains_key(&instruction.id);
            let has_control_transfer = instruction
                .obligations
                .iter()
                .any(|obligation| obligation.kind == SemanticObligationKind::ControlTransfer);
            let lacks_control_certificate = has_control_transfer
                && !direct_controls.contains_key(&instruction.id)
                && !conditional_controls.contains_key(&instruction.id)
                && !switch_controls
                    .values()
                    .any(|control| control.producer() == instruction.id);
            let has_return_obligation = instruction.obligations.iter().any(|obligation| {
                matches!(
                    obligation.kind,
                    SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
                )
            });
            let lacks_return_certificate =
                has_return_obligation && !return_controls.contains_key(&instruction.id);
            if instruction.state != SemanticInstructionState::UnsupportedUnknown
                && !blocked_output
                && !lacks_memory_statement
                && !lacks_call_certificate
                && !lacks_control_certificate
                && !lacks_return_certificate
            {
                continue;
            }
            residual_producers.insert(instruction.id);
            let reason = if instruction.state == SemanticInstructionState::UnsupportedUnknown {
                "source instruction has unsupported or unknown semantics"
            } else if lacks_memory_statement {
                "memory effect lacks an exact plain-statement certificate"
            } else if lacks_call_certificate {
                "call boundary lacks an exact direct-call certificate"
            } else if lacks_control_certificate {
                "control transfer lacks an exact control certificate"
            } else if lacks_return_certificate {
                "return boundary lacks an exact return certificate"
            } else {
                "value expression depends on an unsupported producer"
            };
            for obligation in &instruction.obligations {
                if absorbed_statements.contains(obligation)
                    || absorbed_calls.contains(obligation)
                    || absorbed_controls.contains(obligation)
                {
                    return Err(source_site_mismatch(instruction.id, instruction.source));
                }
                if !residualized.insert(*obligation) {
                    return Err(source_site_mismatch(instruction.id, instruction.source));
                }
                certification
                    .residualize(*obligation, reason)
                    .map_err(|_| source_site_mismatch(instruction.id, instruction.source))?;
            }
        }

        let mut expressions = BTreeMap::new();
        let mut absorbed = BTreeSet::new();
        for entity in projection.entities() {
            if residual_producers.contains(&entity.producer()) {
                continue;
            }
            let source_obligations = entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if source_obligations.is_empty() {
                continue;
            }
            let inst_id = graph.def_inst(entity.output().value()).ok_or(
                MachineBuildError::ObligationSourceMismatch(entity.producer()),
            )?;
            let expression = certified_expr_from_projection(
                artifact,
                &projection,
                entity,
                source_obligations.clone(),
            )?;
            if expression
                .inputs()
                .iter()
                .any(|producer| residual_producers.contains(producer))
            {
                return Err(MachineBuildError::ObligationMismatch(inst_id));
            }
            if expressions
                .insert(entity.producer(), expression.clone())
                .is_some()
            {
                return Err(MachineBuildError::ObligationMismatch(inst_id));
            }
            for obligation in source_obligations {
                if !absorbed.insert(obligation) || residualized.contains(&obligation) {
                    return Err(MachineBuildError::ObligationMismatch(inst_id));
                }
                certification
                    .record_absorbed_expression(obligation, expression.clone())
                    .map_err(|_| MachineBuildError::ObligationMismatch(inst_id))?;
            }
        }

        for obligation in artifact
            .obligations()
            .obligations()
            .values()
            .filter(|obligation| obligation.id.kind == SemanticObligationKind::LiveValueProducer)
        {
            if absorbed.contains(&obligation.id) == residualized.contains(&obligation.id) {
                return Err(source_site_mismatch(
                    obligation.id.instruction,
                    obligation.source,
                ));
            }
        }

        for obligation in artifact
            .obligations()
            .obligations()
            .values()
            .filter(|obligation| {
                matches!(
                    obligation.id.kind,
                    SemanticObligationKind::Call
                        | SemanticObligationKind::CallArgument
                        | SemanticObligationKind::CallResult
                )
            })
        {
            if absorbed_calls.contains(&obligation.id) == residualized.contains(&obligation.id) {
                return Err(source_site_mismatch(
                    obligation.id.instruction,
                    obligation.source,
                ));
            }
        }

        for obligation in artifact
            .obligations()
            .obligations()
            .values()
            .filter(|obligation| {
                matches!(
                    obligation.id.kind,
                    SemanticObligationKind::ControlPredicate
                        | SemanticObligationKind::ControlTransfer
                        | SemanticObligationKind::Return
                        | SemanticObligationKind::ReturnValue
                )
            })
        {
            if absorbed_controls.contains(&obligation.id) == residualized.contains(&obligation.id) {
                return Err(source_site_mismatch(
                    obligation.id.instruction,
                    obligation.source,
                ));
            }
        }

        for obligation in artifact
            .obligations()
            .obligations()
            .values()
            .filter(|obligation| {
                matches!(
                    obligation.id.kind,
                    SemanticObligationKind::ObservableMemoryRead
                        | SemanticObligationKind::ObservableMemoryWrite
                )
            })
        {
            if absorbed_statements.contains(&obligation.id) == residualized.contains(&obligation.id)
            {
                return Err(source_site_mismatch(
                    obligation.id.instruction,
                    obligation.source,
                ));
            }
        }

        for statement in memory_statements.values() {
            if memory_statement_input_producers(statement)
                .iter()
                .any(|producer| !expressions.contains_key(producer))
            {
                return Err(MachineBuildError::ObligationMismatch(
                    statement.access().inst,
                ));
            }
            if matches!(statement.kind(), CertifiedMemoryStatementKind::Read { .. }) {
                let entity = projection.entity_for_producer(statement.producer()).ok_or(
                    MachineBuildError::ObligationMismatch(statement.access().inst),
                )?;
                let kind = projection
                    .expr(entity.root())
                    .map(|expression| expression.kind())
                    .ok_or(MachineBuildError::ObligationMismatch(
                        statement.access().inst,
                    ))?;
                if !certified_read_matches_machine_entity(statement, entity, kind) {
                    return Err(MachineBuildError::ObligationMismatch(
                        statement.access().inst,
                    ));
                }
            }
        }

        for control in conditional_controls.values() {
            if conditional_control_input_producers(control)
                .iter()
                .any(|producer| !expressions.contains_key(producer))
            {
                return Err(MachineBuildError::ObligationMismatch(control.source_inst));
            }
        }

        for call in direct_calls.values() {
            if direct_call_input_producers(call)
                .iter()
                .any(|producer| !expressions.contains_key(producer))
            {
                return Err(MachineBuildError::ObligationMismatch(call.source_inst));
            }
        }

        for control in return_controls.values() {
            if return_control_input_producers(control)
                .iter()
                .any(|producer| !expressions.contains_key(producer))
            {
                return Err(MachineBuildError::ObligationMismatch(control.source_inst));
            }
        }

        let certified_parts = FrameCertifiedParts {
            projection: &projection,
            topology: &topology,
            expressions: &expressions,
            memory_statements: &memory_statements,
            return_controls: &return_controls,
        };
        let frame_preservation = certified_frame_preservation(
            artifact,
            &origin,
            certified_parts,
            certification.ledger(),
        );
        let stack_discipline = certified_stack_discipline(
            artifact,
            &origin,
            certified_parts,
            frame_preservation.as_ref(),
            certification.ledger(),
        );
        let private_frame_value_flows =
            private_frame_value_flow::certified_private_frame_value_flows(
                artifact,
                &origin,
                stack_discipline.as_ref(),
                &memory_statements,
                certification.ledger(),
            );
        let private_frame_conditional_joins =
            private_frame_conditional_join::certified_private_frame_conditional_joins(
                private_frame_conditional_join::PrivateFrameConditionalJoinCertificationInput {
                    artifact,
                    origin: &origin,
                    topology: &topology,
                    stack: stack_discipline.as_ref(),
                    frame: frame_preservation.as_ref(),
                    flows: &private_frame_value_flows,
                    direct_controls: &direct_controls,
                    conditional_controls: &conditional_controls,
                    return_controls: &return_controls,
                    ledger: certification.ledger(),
                },
            );
        Ok(Self {
            origin,
            projection,
            machine_context,
            abi_parameters,
            stack_slots,
            certification,
            expressions,
            memory_statements,
            aggregate_member_accesses,
            direct_calls,
            direct_controls,
            conditional_controls,
            return_controls,
            natural_loop_routings,
            closed_natural_loop_controls,
            switch_topologies,
            switch_controls,
            stack_discipline,
            private_frame_value_flows,
            private_frame_conditional_joins,
            frame_preservation,
            residual_producers,
            topology,
        })
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn projection(&self) -> &MachineProjection {
        &self.projection
    }

    pub const fn machine_context(&self) -> &CertifiedMachineContext {
        &self.machine_context
    }

    pub const fn abi_parameters(&self) -> &BTreeMap<u32, CertifiedAbiParameter> {
        &self.abi_parameters
    }

    pub const fn stack_slots(&self) -> &BTreeMap<StackAddressRoot, CertifiedStackSlot> {
        &self.stack_slots
    }

    pub const fn frame_preservation(&self) -> Option<&CertifiedFramePreservation> {
        self.frame_preservation.as_ref()
    }

    pub const fn stack_discipline(&self) -> Option<&CertifiedStackDiscipline> {
        self.stack_discipline.as_ref()
    }

    pub fn private_frame_value_flow(
        &self,
        load: StructuredAccessId,
    ) -> Option<&CertifiedPrivateFrameValueFlow> {
        self.private_frame_value_flows.get(&load)
    }

    pub const fn private_frame_value_flows(
        &self,
    ) -> &BTreeMap<StructuredAccessId, CertifiedPrivateFrameValueFlow> {
        &self.private_frame_value_flows
    }

    pub fn private_frame_conditional_join(
        &self,
        header: u64,
    ) -> Option<&CertifiedPrivateFrameConditionalJoin> {
        self.private_frame_conditional_joins.get(&header)
    }

    pub const fn private_frame_conditional_joins(
        &self,
    ) -> &BTreeMap<u64, CertifiedPrivateFrameConditionalJoin> {
        &self.private_frame_conditional_joins
    }

    pub fn source(&self) -> &SemanticObligationInventory {
        self.certification.source()
    }

    pub fn ledger(&self) -> &ObligationLedger {
        self.certification.ledger()
    }

    pub const fn topology(&self) -> &CertifiedSourceTopology {
        &self.topology
    }

    pub const fn residual_producers(&self) -> &BTreeSet<CanonicalInstructionId> {
        &self.residual_producers
    }

    pub fn expression_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedExpr> {
        self.expressions.get(&producer)
    }

    pub fn memory_statement_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedMemoryStatement> {
        self.memory_statements.get(&producer)
    }

    pub fn aggregate_member_access(
        &self,
        access: StructuredAccessId,
    ) -> Option<&CertifiedAggregateMemberAccess> {
        self.aggregate_member_accesses.get(&access)
    }

    pub const fn aggregate_member_accesses(
        &self,
    ) -> &BTreeMap<StructuredAccessId, CertifiedAggregateMemberAccess> {
        &self.aggregate_member_accesses
    }

    pub fn direct_call_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedDirectCall> {
        self.direct_calls.get(&producer)
    }

    pub const fn direct_calls(&self) -> &BTreeMap<CanonicalInstructionId, CertifiedDirectCall> {
        &self.direct_calls
    }

    pub fn direct_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedDirectControl> {
        self.direct_controls.get(&producer)
    }

    pub fn conditional_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedConditionalControl> {
        self.conditional_controls.get(&producer)
    }

    pub fn return_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedReturnControl> {
        self.return_controls.get(&producer)
    }

    pub const fn return_controls(
        &self,
    ) -> &BTreeMap<CanonicalInstructionId, CertifiedReturnControl> {
        &self.return_controls
    }

    pub fn natural_loop_routing_for_header(
        &self,
        header: u64,
    ) -> Option<&CertifiedNaturalLoopRouting> {
        self.natural_loop_routings.get(&header)
    }

    pub fn closed_natural_loop_control_for_header(
        &self,
        header: u64,
    ) -> Option<&CertifiedClosedNaturalLoopControl> {
        self.closed_natural_loop_controls.get(&header)
    }

    pub fn switch_topology_for_block(&self, block_addr: u64) -> Option<&CertifiedSwitchTopology> {
        self.switch_topologies.get(&block_addr)
    }

    pub fn switch_control_for_block(&self, block_addr: u64) -> Option<&CertifiedSwitchControl> {
        self.switch_controls.get(&block_addr)
    }

    pub fn finish(&self) -> CertificationReport {
        let mut report = self.certification.finish();
        report.typed_region_required = true;
        report
    }
}

fn certified_source_topology(
    artifact: &SsaArtifact,
) -> Result<CertifiedSourceTopology, MachineBuildError> {
    let graph = artifact.graph();
    let source = artifact.obligations();
    let function = artifact.function();
    let cfg = function.cfg();
    let entry = graph
        .block(graph.entry)
        .filter(|block| block.id == graph.entry)
        .ok_or(MachineBuildError::TopologyMismatch)?;
    if entry.addr != function.entry
        || entry.addr != cfg.entry
        || graph.block_order.first() != Some(&graph.entry)
        || graph.block_order.len() != graph.blocks.len()
        || cfg.num_blocks() != graph.blocks.len()
        || function.num_blocks() != graph.blocks.len()
    {
        return Err(MachineBuildError::TopologyMismatch);
    }

    let ordered_blocks = graph.block_order.iter().copied().collect::<BTreeSet<_>>();
    if ordered_blocks.len() != graph.blocks.len() {
        return Err(MachineBuildError::TopologyMismatch);
    }
    for (index, block) in graph.blocks.iter().enumerate() {
        if block.id.0 as usize != index
            || !ordered_blocks.contains(&block.id)
            || graph.block_by_addr.get(&block.addr) != Some(&block.id)
            || function
                .get_block(block.addr)
                .is_none_or(|source_block| source_block.size != block.size)
            || cfg
                .get_block(block.addr)
                .is_none_or(|source_block| source_block.size != block.size)
        {
            return Err(MachineBuildError::TopologyMismatch);
        }
    }
    if graph.block_by_addr.len() != graph.blocks.len() {
        return Err(MachineBuildError::TopologyMismatch);
    }
    for (index, instruction) in graph.insts.iter().enumerate() {
        if instruction.id.0 as usize != index {
            return Err(MachineBuildError::TopologyMismatch);
        }
    }

    let mut addresses = BTreeSet::new();
    let mut instruction_ids = BTreeSet::new();
    let mut graph_instructions = BTreeSet::new();
    let mut blocks = Vec::with_capacity(graph.block_order.len());

    for block_id in &graph.block_order {
        let block = graph
            .block(*block_id)
            .ok_or(MachineBuildError::MissingGraphBlock(*block_id))?;
        if !addresses.insert(block.addr) {
            return Err(MachineBuildError::DuplicateBlockAddress(block.addr));
        }
        let predecessor_ids = block.predecessors.iter().copied().collect::<BTreeSet<_>>();
        let successor_ids = block.successors.iter().copied().collect::<BTreeSet<_>>();
        if predecessor_ids.len() != block.predecessors.len()
            || successor_ids.len() != block.successors.len()
        {
            return Err(MachineBuildError::TopologyMismatch);
        }
        let predecessors = block
            .predecessors
            .iter()
            .map(|predecessor| {
                graph
                    .block(*predecessor)
                    .map(|block| block.addr)
                    .ok_or(MachineBuildError::MissingGraphBlock(*predecessor))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let successors = block
            .successors
            .iter()
            .map(|successor| {
                graph
                    .block(*successor)
                    .map(|block| block.addr)
                    .ok_or(MachineBuildError::MissingGraphBlock(*successor))
            })
            .collect::<Result<Vec<_>, _>>()?;
        if predecessors != cfg.predecessors(block.addr) || successors != cfg.successors(block.addr)
        {
            return Err(MachineBuildError::TopologyMismatch);
        }
        for predecessor in &block.predecessors {
            let predecessor = graph
                .block(*predecessor)
                .ok_or(MachineBuildError::MissingGraphBlock(*predecessor))?;
            if predecessor
                .successors
                .iter()
                .filter(|successor| **successor == block.id)
                .count()
                != 1
            {
                return Err(MachineBuildError::TopologyMismatch);
            }
        }
        for successor in &block.successors {
            let successor = graph
                .block(*successor)
                .ok_or(MachineBuildError::MissingGraphBlock(*successor))?;
            if successor
                .predecessors
                .iter()
                .filter(|predecessor| **predecessor == block.id)
                .count()
                != 1
            {
                return Err(MachineBuildError::TopologyMismatch);
            }
        }
        let instructions = block
            .insts
            .iter()
            .enumerate()
            .map(|(ordinal, inst)| {
                let graph_inst = graph
                    .inst(*inst)
                    .filter(|instruction| {
                        instruction.id == *inst
                            && instruction.block == block.id
                            && instruction.ordinal == ordinal
                    })
                    .ok_or(MachineBuildError::TopologyMismatch)?;
                if !graph_instructions.insert(graph_inst.id) {
                    return Err(MachineBuildError::TopologyMismatch);
                }
                let id = source
                    .instruction_for_inst(*inst)
                    .map(|instruction| instruction.id)
                    .ok_or(MachineBuildError::MissingInstructionDisposition(*inst))?;
                if id.block_addr != block.addr || !instruction_ids.insert(id) {
                    return Err(MachineBuildError::TopologyMismatch);
                }
                Ok(id)
            })
            .collect::<Result<Vec<_>, MachineBuildError>>()?;
        let terminator = cfg
            .get_block(block.addr)
            .ok_or(MachineBuildError::TopologyMismatch)
            .and_then(CertifiedSourceTerminator::from_block)?;
        blocks.push(CertifiedSourceBlock {
            addr: block.addr,
            predecessors: predecessors.into_boxed_slice(),
            successors: successors.into_boxed_slice(),
            terminator,
            instructions: instructions.into_boxed_slice(),
        });
    }

    if graph.blocks.len() != blocks.len()
        || graph_instructions
            != graph
                .insts
                .iter()
                .map(|instruction| instruction.id)
                .collect()
        || instruction_ids
            != source
                .instructions()
                .values()
                .filter(|instruction| instruction.source.graph_inst().is_some())
                .map(|instruction| instruction.id)
                .collect()
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(CertifiedSourceTopology {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        entry_addr: entry.addr,
        blocks: blocks.into_boxed_slice(),
    })
}

fn certified_expr_from_machine(
    artifact: &SsaArtifact,
    machine: &MachineProjection,
    machine_entity: &MachineEntity,
    source_obligations: BTreeSet<SemanticObligationId>,
) -> Result<CertifiedExpr, MachineBuildError> {
    let graph = artifact.graph();
    let inst_id = graph.def_inst(machine_entity.output().value()).ok_or(
        MachineBuildError::ObligationSourceMismatch(machine_entity.producer()),
    )?;
    let inst = graph
        .inst(inst_id)
        .ok_or(MachineBuildError::MissingInstruction(inst_id))?;
    let producer = artifact
        .obligations()
        .instruction_for_inst(inst_id)
        .ok_or(MachineBuildError::MissingInstructionDisposition(inst_id))?
        .id;
    if producer != machine_entity.producer()
        || machine
            .expr(machine_entity.root())
            .is_none_or(|root| root.origin() != Some(producer))
    {
        return Err(MachineBuildError::EntityMismatch(inst_id));
    }

    let mut inputs = BTreeSet::new();
    for input in &inst.inputs {
        let Some(input_inst) = graph.def_inst(*input) else {
            continue;
        };
        let input_producer = artifact
            .obligations()
            .instruction_for_inst(input_inst)
            .ok_or(MachineBuildError::MissingInstructionDisposition(input_inst))?
            .id;
        inputs.insert(input_producer);
    }

    let expression = CertifiedExpr {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        entity: CertifiedEntity {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            producer,
            source_obligations,
        },
        root: machine_entity.root(),
        inputs,
    };
    expression
        .validate(artifact.obligations())
        .map_err(|_| MachineBuildError::ObligationMismatch(inst_id))?;
    Ok(expression)
}

fn certified_expr_from_projection(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    machine_entity: &MachineEntity,
    source_obligations: BTreeSet<SemanticObligationId>,
) -> Result<CertifiedExpr, MachineBuildError> {
    let graph = artifact.graph();
    let inst_id = graph.def_inst(machine_entity.output().value()).ok_or(
        MachineBuildError::ObligationSourceMismatch(machine_entity.producer()),
    )?;
    let inst = graph
        .inst(inst_id)
        .ok_or(MachineBuildError::MissingInstruction(inst_id))?;
    let producer = artifact
        .obligations()
        .instruction_for_inst(inst_id)
        .ok_or(MachineBuildError::MissingInstructionDisposition(inst_id))?
        .id;
    if producer != machine_entity.producer()
        || projection
            .expr(machine_entity.root())
            .is_none_or(|root| root.origin() != Some(producer))
    {
        return Err(MachineBuildError::EntityMismatch(inst_id));
    }

    let mut inputs = BTreeSet::new();
    for input in &inst.inputs {
        let Some(input_inst) = graph.def_inst(*input) else {
            continue;
        };
        let input_producer = artifact
            .obligations()
            .instruction_for_inst(input_inst)
            .ok_or(MachineBuildError::MissingInstructionDisposition(input_inst))?
            .id;
        inputs.insert(input_producer);
    }

    let expression = CertifiedExpr {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        entity: CertifiedEntity {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            producer,
            source_obligations,
        },
        root: machine_entity.root(),
        inputs,
    };
    expression
        .validate(artifact.obligations())
        .map_err(|_| MachineBuildError::ObligationMismatch(inst_id))?;
    Ok(expression)
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{
        AddressSpace, ArchSpec, Endianness, MemoryOrdering, R2ILBlock, R2ILOp, RegisterDef,
        SpaceId, Varnode,
    };
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, InstPayload, SSAOp, SourceAbiParameterSpec,
        SourceCallArgumentSpec, SourceCallResult, SourceCallSiteIdentity, SourceCallSiteInterface,
        SourceFunctionInterface, SourceFunctionReturn, SourceStackSlotSpec, SsaArtifact,
    };

    fn inventory() -> SemanticObligationInventory {
        let mut block = R2ILBlock::new(0x1000, 4);
        let address = Varnode::register(0, 8);
        let value = Varnode::unique(0x10, 4);
        block.push(R2ILOp::Load {
            dst: value.clone(),
            space: SpaceId::Ram,
            addr: address.clone(),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address,
            val: value,
        });
        SsaArtifact::raw(&[block], None)
            .expect("source artifact")
            .obligations()
            .clone()
    }

    #[test]
    fn memory_space_matching_rejects_ram_custom_swaps() {
        let address = SSAVar::new("addr", 0, 8);
        let value = SSAVar::new("value", 0, 4);
        let load = SSAOp::Load {
            dst: value.clone(),
            space: SpaceId::Ram,
            addr: address.clone(),
        };
        let store = SSAOp::Store {
            space: SpaceId::Custom(7),
            addr: address,
            val: value,
        };

        assert_eq!(ssa_memory_space(&load), Some(SpaceId::Ram));
        assert_ne!(ssa_memory_space(&load), Some(SpaceId::Custom(7)));
        assert_eq!(ssa_memory_space(&store), Some(SpaceId::Custom(7)));
        assert_ne!(ssa_memory_space(&store), Some(SpaceId::Ram));
    }

    fn copied_literal_graph() -> (r2ssa::SsaGraph, InstId, ValueId, ValueId) {
        let mut block = R2ILBlock::new(0x1080, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x100, 8),
            src: Varnode::constant(0x10, 8),
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("copied-literal artifact");
        let graph = artifact.graph().clone();
        let inst = graph.insts.first().expect("one copied-literal instruction");
        let inst_id = inst.id;
        let output = inst.output.expect("copied-literal output");
        let [input] = inst.inputs.as_slice() else {
            panic!("one copied-literal input")
        };
        let input = *input;
        (graph, inst_id, output, input)
    }

    #[test]
    fn frame_constant_accepts_only_exact_one_hop_copied_literal() {
        let (graph, inst, output, input) = copied_literal_graph();
        assert_eq!(
            frame_constant_bits_from_graph(&graph, input, 64),
            Some(0x10)
        );
        assert_eq!(
            frame_constant_bits_from_graph(&graph, output, 64),
            Some(0x10)
        );
        assert_eq!(frame_constant_bits_from_graph(&graph, output, 32), None);
        assert_eq!(frame_constant_bits_from_graph(&graph, output, 0), None);

        let assert_refused = |mutate: fn(&mut r2ssa::SsaGraph)| {
            let (mut mutated, _, output, _) = copied_literal_graph();
            mutate(&mut mutated);
            assert_eq!(frame_constant_bits_from_graph(&mutated, output, 64), None);
        };
        assert_refused(|graph| graph.insts[0].output = None);
        assert_refused(|graph| {
            let output = graph.insts[0].output.expect("copied-literal output");
            graph.def_of[output.0 as usize] = None;
        });
        assert_refused(|graph| graph.insts[0].inputs.clear());
        assert_refused(|graph| {
            let input = graph.insts[0].inputs[0];
            graph.insts[0].inputs.push(input);
        });
        assert_refused(|graph| graph.insts[0].canonical_storage = None);
        assert_refused(|graph| graph.blocks[0].insts.clear());
        assert_refused(|graph| {
            let input = graph.insts[0].inputs[0];
            graph.def_of[input.0 as usize] = Some(graph.insts[0].id);
        });
        assert_refused(|graph| {
            let input = graph.insts[0].inputs[0];
            graph.values[input.0 as usize].canonical_storage = None;
        });
        assert_refused(|graph| {
            let input = graph.insts[0].inputs[0];
            graph.values[input.0 as usize]
                .canonical_storage
                .as_mut()
                .expect("constant storage")
                .offset += 1;
        });
        assert_refused(|graph| {
            let InstPayload::Op(SSAOp::Copy { dst, src }) = &graph.insts[0].payload else {
                unreachable!()
            };
            graph.insts[0].payload = InstPayload::Op(SSAOp::IntAdd {
                dst: dst.clone(),
                a: src.clone(),
                b: src.clone(),
            });
        });
        assert_refused(|graph| {
            let InstPayload::Op(SSAOp::Copy { src, .. }) = &graph.insts[0].payload else {
                unreachable!()
            };
            graph.insts[0].payload = InstPayload::Op(SSAOp::Copy {
                dst: SSAVar::new("foreign", 0, 8),
                src: src.clone(),
            });
        });
        assert_refused(|graph| {
            let InstPayload::Op(SSAOp::Copy { dst, .. }) = &graph.insts[0].payload else {
                unreachable!()
            };
            graph.insts[0].payload = InstPayload::Op(SSAOp::Copy {
                dst: dst.clone(),
                src: SSAVar::new("foreign", 0, 8),
            });
        });

        assert_eq!(graph.def_inst(output), Some(inst));
    }

    #[test]
    fn frame_constant_rejects_nonliteral_and_two_hop_copy() {
        let mut nonliteral = R2ILBlock::new(0x1090, 4);
        nonliteral.push(R2ILOp::Copy {
            dst: Varnode::unique(0x100, 8),
            src: Varnode::register(0, 8),
        });
        let artifact = SsaArtifact::raw(&[nonliteral], None).expect("nonliteral copy artifact");
        let output = artifact.graph().insts[0].output.expect("copy output");
        assert_eq!(frame_constant_bits(&artifact, output, 64), None);

        let first = Varnode::unique(0x100, 8);
        let second = Varnode::unique(0x108, 8);
        let mut two_hop = R2ILBlock::new(0x10a0, 4);
        two_hop.push(R2ILOp::Copy {
            dst: first.clone(),
            src: Varnode::constant(0x10, 8),
        });
        two_hop.push(R2ILOp::Copy {
            dst: second,
            src: first,
        });
        let artifact = SsaArtifact::raw(&[two_hop], None).expect("two-hop copy artifact");
        let first_output = artifact.graph().insts[0].output.expect("first copy output");
        let second_output = artifact.graph().insts[1]
            .output
            .expect("second copy output");
        assert_eq!(frame_constant_bits(&artifact, first_output, 64), Some(0x10));
        assert_eq!(frame_constant_bits(&artifact, second_output, 64), None);
    }

    fn first_input_use(artifact: &SsaArtifact, inst_index: usize) -> (ValueId, r2ssa::UseSite) {
        let inst = &artifact.graph().insts[inst_index];
        let value = inst.inputs[0];
        let use_site = artifact
            .graph()
            .use_sites(value)
            .iter()
            .copied()
            .find(|use_site| use_site.inst == inst.id && use_site.input_idx == 0)
            .expect("exact first-input use");
        (value, use_site)
    }

    #[test]
    fn frame_affine_use_accepts_only_exact_leaf_proven_dead_consumers() {
        let left = Varnode::register(0, 8);
        let right = Varnode::constant(0x10, 8);
        for op in [
            R2ILOp::IntCarry {
                dst: Varnode::unique(0x100, 1),
                a: left.clone(),
                b: right.clone(),
            },
            R2ILOp::IntSCarry {
                dst: Varnode::unique(0x108, 1),
                a: left.clone(),
                b: right.clone(),
            },
            R2ILOp::IntSLess {
                dst: Varnode::unique(0x110, 1),
                a: left.clone(),
                b: right.clone(),
            },
            R2ILOp::IntEqual {
                dst: Varnode::unique(0x118, 1),
                a: left.clone(),
                b: right.clone(),
            },
        ] {
            let mut block = R2ILBlock::new(0x10b0, 4);
            block.push(op);
            let artifact = SsaArtifact::raw(&[block], None).expect("dead flag artifact");
            let (value, use_site) = first_input_use(&artifact, 0);
            let consumer = artifact.graph().inst(use_site.inst).expect("flag consumer");
            let output = consumer.output.expect("flag output");
            let disposition = artifact
                .obligations()
                .instruction_for_inst(consumer.id)
                .expect("flag disposition");
            assert_eq!(disposition.state, SemanticInstructionState::ProvenDead);
            assert!(disposition.obligations.is_empty());
            assert!(artifact.graph().use_sites(output).is_empty());
            assert!(frame_affine_leaf_dead_consumer(&artifact, value, use_site));
        }

        let flag = Varnode::unique(0x120, 1);
        let mut dead_chain = R2ILBlock::new(0x10c0, 4);
        dead_chain.push(R2ILOp::IntCarry {
            dst: flag.clone(),
            a: left.clone(),
            b: right.clone(),
        });
        dead_chain.push(R2ILOp::Copy {
            dst: Varnode::unique(0x128, 1),
            src: flag,
        });
        let artifact = SsaArtifact::raw(&[dead_chain], None).expect("dead flag chain artifact");
        let (value, use_site) = first_input_use(&artifact, 0);
        assert!(!frame_affine_leaf_dead_consumer(&artifact, value, use_site));

        let mut trapping = R2ILBlock::new(0x10d0, 4);
        trapping.push(R2ILOp::IntDiv {
            dst: Varnode::unique(0x130, 8),
            a: left,
            b: right,
        });
        let artifact = SsaArtifact::raw(&[trapping], None).expect("trapping artifact");
        let (value, use_site) = first_input_use(&artifact, 0);
        assert!(!frame_affine_leaf_dead_consumer(&artifact, value, use_site));
    }

    #[test]
    fn projected_control_carrier_uses_graph_width_not_full_abi_width() {
        let abi_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 48,
            size: 8,
        };
        let graph_storage = CanonicalStorageId {
            size: 4,
            ..abi_storage
        };
        let logical_value = SourceLogicalValue::new(
            0,
            r2ssa::SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32),
        );
        let type_graph = r2ssa::SourceTypeGraph::new(
            [r2ssa::SourceType::new(
                0,
                r2ssa::SourceTypeKind::UnsignedInteger,
                32,
                32,
            )],
            [],
        )
        .expect("scalar source type");
        let interface = SourceFunctionInterface::new_with_logical_types(
            b"projected-control-carrier".to_vec(),
            "test-abi",
            [SourceAbiParameterSpec::new(0, abi_storage)],
            SourceFunctionReturn::Void,
            [],
            [logical_value],
            None,
            Some(type_graph),
        )
        .expect("projected source interface");

        assert_ne!(abi_storage.size, graph_storage.size);
        assert_eq!(graph_storage.size.checked_mul(8), Some(32));
        assert!(interface_has_exact_parameter_projection(
            &interface,
            0,
            abi_storage,
            graph_storage,
            logical_value,
        ));
    }

    #[test]
    fn projected_control_carrier_rejects_graph_and_logical_mutations() {
        let abi_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 48,
            size: 8,
        };
        let graph_storage = CanonicalStorageId {
            size: 4,
            ..abi_storage
        };
        let low_bits = SourceLogicalValue::new(
            0,
            r2ssa::SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32),
        );
        let shifted = SourceLogicalValue::new(
            0,
            r2ssa::SourceCarrierProjection::new(SourceCarrierKind::LowBits, 8, 32),
        );
        let full_width = SourceLogicalValue::new(
            0,
            r2ssa::SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
        );

        assert!(exact_parameter_projection(
            abi_storage,
            graph_storage,
            low_bits
        ));
        assert!(!exact_parameter_projection(
            abi_storage,
            abi_storage,
            low_bits
        ));
        assert!(!exact_parameter_projection(
            abi_storage,
            graph_storage,
            shifted
        ));
        assert!(!exact_parameter_projection(
            abi_storage,
            graph_storage,
            full_width
        ));
    }

    fn typed_memory_artifact() -> SsaArtifact {
        let address = Varnode::register(0, 8);
        let loaded = Varnode::unique(0x10, 4);
        let mut block = R2ILBlock::new(0x1800, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: address.clone(),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address,
            val: loaded,
        });
        let mut arch = ArchSpec::new("certified-memory-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Big);
        SsaArtifact::raw(&[block], Some(&arch)).expect("typed memory artifact")
    }

    fn unsupported_inventory() -> SemanticObligationInventory {
        let mut block = R2ILBlock::new(0x2000, 4);
        block.push(R2ILOp::Fence {
            ordering: MemoryOrdering::Unknown,
        });
        SsaArtifact::raw(&[block], None)
            .expect("unsupported artifact")
            .obligations()
            .clone()
    }
    fn explicit_return_artifact(return_kind: SourceFunctionReturn) -> SsaArtifact {
        let mut block = R2ILBlock::new(0x3080, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(8, 8),
        });
        if matches!(return_kind, SourceFunctionReturn::Register { .. }) {
            block.push(R2ILOp::Copy {
                dst: Varnode::register(0, 8),
                src: Varnode::unique(0x10, 8),
            });
        }
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let mut arch = ArchSpec::new("explicit-interface-test");
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        let interface = SourceFunctionInterface::new(
            b"certified-interface-revision-1".to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(
                0,
                CanonicalStorageId {
                    space: CanonicalStorageSpace::Register,
                    offset: 8,
                    size: 8,
                },
            )],
            return_kind,
            [],
        )
        .expect("valid interface");
        SsaArtifact::raw_with_interface(&[block], Some(&arch), interface)
            .expect("explicit return artifact")
    }

    fn exact_rax_return_artifact(with_al_overlay: bool) -> SsaArtifact {
        let rax = Varnode::register(0, 8);
        let al = Varnode::register(0, 1);
        let rip = Varnode::register(16, 8);
        let mut block = R2ILBlock::new(0x30a0, 4);
        block.push(R2ILOp::Copy {
            dst: rax,
            src: Varnode::constant(0x1122_3344_5566_7788, 8),
        });
        if with_al_overlay {
            block.push(R2ILOp::Copy {
                dst: al,
                src: Varnode::constant(0xaa, 1),
            });
        }
        block.push(R2ILOp::Return { target: rip });

        let storage = |offset, size| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        };
        let mut arch = ArchSpec::new("exact-return-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::sub("al", 0, 1, "rax"));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        arch.add_register(RegisterDef::new("rsp", 24, 8));
        let interface = SourceFunctionInterface::new_exact(
            b"exact-return-revision-1".to_vec(),
            "test-register-abi",
            [],
            SourceFunctionReturn::Register {
                storage: storage(0, 8),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(24, 8)))
        .expect("exact return interface");
        SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("exact return artifact")
    }

    fn composed_rax_al_return_artifact() -> SsaArtifact {
        exact_rax_return_artifact(true)
    }
    fn explicit_stack_slot_artifact(slot_size_bytes: u32) -> SsaArtifact {
        let mut block = R2ILBlock::new(0x30c0, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(24, 8),
            val: Varnode::constant(0x1122_3344_5566_7788, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let mut arch = ArchSpec::new("explicit-stack-interface-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rip", 16, 8));
        arch.add_register(RegisterDef::new("rsp", 24, 8));
        let interface = SourceFunctionInterface::new(
            b"certified-stack-interface-revision-1".to_vec(),
            "test-stack-abi",
            [],
            SourceFunctionReturn::Void,
            [
                SourceStackSlotSpec::new(
                    StackAddressBase::StackPointer,
                    CanonicalStorageId {
                        space: CanonicalStorageSpace::Register,
                        offset: 24,
                        size: 8,
                    },
                    0,
                    slot_size_bytes,
                ),
                SourceStackSlotSpec::new(
                    StackAddressBase::StackPointer,
                    CanonicalStorageId {
                        space: CanonicalStorageSpace::Register,
                        offset: 24,
                        size: 8,
                    },
                    16,
                    4,
                ),
            ],
        )
        .expect("valid stack interface");
        SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("explicit stack artifact")
    }

    #[derive(Debug, Clone, Copy)]
    enum FrameMutation {
        None,
        MissingAllocationContract,
        OppositeAllocationContract,
        ExplicitNoSlots,
        ComposedReturn,
        MissingExplicitNoSlots,
        AffineRelation,
        ZeroObligationRelation,
        TransitiveRestore,
        DirectLoadRestore,
        SplitAllocation,
        OverlappingWrite,
        Call,
        UnknownEffect,
        Escape,
        WrongRestoreRange,
        MissingRestore,
        WrongRestoreStorage,
        RestoreBeforeRelation,
        PositiveSaveRange,
        ZeroSaveRange,
        OtherRestoreSpace,
        CustomSaveAndRestore,
        StaleSplitAllocation,
        GlobalLoad,
        ParameterMemory,
        UnknownPointerLoad,
        WrongAffineRoot,
        EntrySelfLoop,
        UnbalancedStackPointer,
        PartialFramePointerWrite,
        StackedReturn,
        StackedNoContract,
        StackedWrongOffset,
        StackedWrongWidth,
        StackedWrongSpace,
        StackedWrongTarget,
        StackedWrongDelta,
        StackedZeroExit,
        StackedDuplicateRead,
        StackedUnledgeredRead,
        StackedOverlappingStore,
        StackedPartialOverlappingStore,
        StackedUnknownPointerStore,
        StackedAtomic,
        ImplicitPrivateStack,
        ImplicitPrivateStackCall,
        ImplicitPrivateStackOverlap,
    }

    #[derive(Debug, Clone, Copy)]
    enum StackDisciplineMutation {
        None,
        HigherAddresses,
        MissingAllocationContract,
        OppositeAllocationContract,
        MissingReservation,
        WrongReservation,
        MissingRestoration,
        WrongRestoration,
        PartialStackPointerWrite,
        ExtraStackPointerWrite,
        OutOfEnvelopeAccess,
        StackPointerEscape,
        Call,
        UnknownEffect,
        EntryReturnAddressOverlap,
        AccessBeforeReservation,
        AccessAfterRestoration,
        ExactUnusedFramePointer,
        UnpreservedFrameUse,
    }

    fn frameless_stack_artifact(mutation: StackDisciplineMutation) -> SsaArtifact {
        let upward = matches!(mutation, StackDisciplineMutation::HigherAddresses);
        let sp = Varnode::register(0, 8);
        let ra = Varnode::register(8, 8);
        let fp = Varnode::register(16, 8);
        let first_address = Varnode::unique(0x100, 8);
        let second_address = Varnode::unique(0x108, 8);
        let loaded = Varnode::unique(0x110, 4);
        let release = Varnode::unique(0x118, 8);
        let mut block = R2ILBlock::new(0x3600, 4);
        if matches!(mutation, StackDisciplineMutation::AccessBeforeReservation) {
            block.push(R2ILOp::IntSub {
                dst: Varnode::unique(0x130, 8),
                a: sp.clone(),
                b: Varnode::constant(8, 8),
            });
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::unique(0x130, 8),
                val: Varnode::constant(0, 4),
            });
        }
        if !matches!(mutation, StackDisciplineMutation::MissingReservation) {
            let amount = Varnode::constant(
                if matches!(mutation, StackDisciplineMutation::WrongReservation) {
                    8
                } else {
                    16
                },
                8,
            );
            block.push(if upward {
                R2ILOp::IntAdd {
                    dst: sp.clone(),
                    a: sp.clone(),
                    b: amount,
                }
            } else {
                R2ILOp::IntSub {
                    dst: sp.clone(),
                    a: sp.clone(),
                    b: amount,
                }
            });
        }
        let first_delta = Varnode::constant(
            if matches!(mutation, StackDisciplineMutation::OutOfEnvelopeAccess) {
                20
            } else {
                8
            },
            8,
        );
        block.push(if upward {
            R2ILOp::IntSub {
                dst: first_address.clone(),
                a: sp.clone(),
                b: first_delta,
            }
        } else {
            R2ILOp::IntAdd {
                dst: first_address.clone(),
                a: sp.clone(),
                b: first_delta,
            }
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: first_address.clone(),
            val: Varnode::constant(0x1122_3344, 4),
        });
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: first_address,
        });
        block.push(if upward {
            R2ILOp::IntSub {
                dst: second_address.clone(),
                a: sp.clone(),
                b: Varnode::constant(4, 8),
            }
        } else {
            R2ILOp::IntAdd {
                dst: second_address.clone(),
                a: sp.clone(),
                b: Varnode::constant(12, 8),
            }
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: second_address.clone(),
            val: loaded,
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x120, 4),
            space: SpaceId::Ram,
            addr: second_address,
        });
        match mutation {
            StackDisciplineMutation::PartialStackPointerWrite => block.push(R2ILOp::Copy {
                dst: Varnode::register(0, 4),
                src: Varnode::constant(0, 4),
            }),
            StackDisciplineMutation::StackPointerEscape => block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(0x8800, 8),
                val: sp.clone(),
            }),
            StackDisciplineMutation::Call => block.push(R2ILOp::Call {
                target: Varnode::ram(0x4400, 8),
            }),
            StackDisciplineMutation::UnknownEffect => block.push(R2ILOp::CallOther {
                output: None,
                userop: 7,
                inputs: vec![],
            }),
            StackDisciplineMutation::EntryReturnAddressOverlap => {
                block.push(R2ILOp::IntAdd {
                    dst: Varnode::unique(0x128, 8),
                    a: sp.clone(),
                    b: Varnode::constant(16, 8),
                });
                block.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: Varnode::unique(0x128, 8),
                    val: Varnode::constant(0, 8),
                });
            }
            StackDisciplineMutation::None
            | StackDisciplineMutation::HigherAddresses
            | StackDisciplineMutation::MissingAllocationContract
            | StackDisciplineMutation::OppositeAllocationContract
            | StackDisciplineMutation::MissingReservation
            | StackDisciplineMutation::WrongReservation
            | StackDisciplineMutation::MissingRestoration
            | StackDisciplineMutation::WrongRestoration
            | StackDisciplineMutation::ExtraStackPointerWrite
            | StackDisciplineMutation::OutOfEnvelopeAccess
            | StackDisciplineMutation::AccessBeforeReservation
            | StackDisciplineMutation::AccessAfterRestoration
            | StackDisciplineMutation::ExactUnusedFramePointer
            | StackDisciplineMutation::UnpreservedFrameUse => {}
        }
        if matches!(mutation, StackDisciplineMutation::UnpreservedFrameUse) {
            block.push(R2ILOp::Copy {
                dst: fp,
                src: sp.clone(),
            });
        }
        if !matches!(mutation, StackDisciplineMutation::MissingRestoration) {
            let amount = Varnode::constant(
                if matches!(mutation, StackDisciplineMutation::WrongRestoration) {
                    8
                } else {
                    16
                },
                8,
            );
            block.push(if upward {
                R2ILOp::IntSub {
                    dst: release.clone(),
                    a: sp.clone(),
                    b: amount,
                }
            } else {
                R2ILOp::IntAdd {
                    dst: release.clone(),
                    a: sp.clone(),
                    b: amount,
                }
            });
            block.push(R2ILOp::Copy {
                dst: sp.clone(),
                src: release,
            });
        }
        if matches!(mutation, StackDisciplineMutation::AccessAfterRestoration) {
            block.push(R2ILOp::IntSub {
                dst: Varnode::unique(0x138, 8),
                a: sp.clone(),
                b: Varnode::constant(8, 8),
            });
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::unique(0x138, 8),
                val: Varnode::constant(0, 4),
            });
        }
        if matches!(mutation, StackDisciplineMutation::ExtraStackPointerWrite) {
            block.push(R2ILOp::Copy {
                dst: sp.clone(),
                src: sp.clone(),
            });
        }
        block.push(R2ILOp::Return { target: ra.clone() });

        let mut arch = ArchSpec::new("arm64-frameless-stack-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("x30", 8, 8));
        if matches!(
            mutation,
            StackDisciplineMutation::ExactUnusedFramePointer
                | StackDisciplineMutation::UnpreservedFrameUse
        ) {
            arch.add_register(RegisterDef::new("fp", 16, 8));
        }
        arch.add_space(AddressSpace::ram(8));
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"arm64-frameless-stack-revision-1".to_vec(),
            "test-arm64-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(8)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0)))
        .expect("exact frameless stack interface");
        let interface = if matches!(
            mutation,
            StackDisciplineMutation::ExactUnusedFramePointer
                | StackDisciplineMutation::UnpreservedFrameUse
        ) {
            interface
                .with_frame_pointer_storage(storage(16))
                .expect("exact unused frame-pointer identity")
        } else {
            interface
        };
        let interface = if matches!(mutation, StackDisciplineMutation::MissingAllocationContract) {
            interface
        } else {
            let growth = if upward
                || matches!(
                    mutation,
                    StackDisciplineMutation::OppositeAllocationContract
                ) {
                SourceStackGrowth::HigherAddresses
            } else {
                SourceStackGrowth::LowerAddresses
            };
            interface
                .with_stack_allocation_contract(SourceStackAllocationContract::new(growth))
                .expect("exact frameless stack allocation contract")
        };
        SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("frameless stack artifact")
    }

    #[derive(Clone, Copy, Debug)]
    enum TwoReturnMutation {
        None,
        SharedRead,
        CrossArmStore,
        DuplicateDominatingRead,
    }

    fn preserved_frame_artifact(mutation: FrameMutation) -> SsaArtifact {
        let stacked_return = matches!(
            mutation,
            FrameMutation::StackedReturn
                | FrameMutation::StackedNoContract
                | FrameMutation::StackedWrongOffset
                | FrameMutation::StackedWrongWidth
                | FrameMutation::StackedWrongSpace
                | FrameMutation::StackedWrongTarget
                | FrameMutation::StackedWrongDelta
                | FrameMutation::StackedZeroExit
                | FrameMutation::StackedDuplicateRead
                | FrameMutation::StackedUnledgeredRead
                | FrameMutation::StackedOverlappingStore
                | FrameMutation::StackedPartialOverlappingStore
                | FrameMutation::StackedUnknownPointerStore
                | FrameMutation::StackedAtomic
                | FrameMutation::ImplicitPrivateStack
                | FrameMutation::ImplicitPrivateStackCall
                | FrameMutation::ImplicitPrivateStackOverlap
        );
        let fp = Varnode::register(0, 8);
        let sp = Varnode::register(8, 8);
        let ra = Varnode::register(16, 8);
        let loaded = Varnode::unique(0x100, 8);
        let restore_address = Varnode::unique(0x108, 8);
        let escape_address = Varnode::unique(0x110, 8);
        let saved_frame_pointer = Varnode::unique(0x118, 8);
        let restore_copy = Varnode::unique(0x120, 8);
        let stale_save_address = Varnode::unique(0x128, 8);
        let unrelated_load = Varnode::unique(0x130, 8);
        let return_address = Varnode::unique(0x138, 8);
        let duplicate_return_address = Varnode::unique(0x140, 8);
        let adjusted_return_slot = Varnode::unique(0x148, 8);
        let first_private_address = Varnode::unique(0x158, 8);
        let first_private_value = Varnode::unique(0x160, 4);
        let second_private_address = Varnode::unique(0x168, 8);
        let second_private_value = Varnode::unique(0x170, 4);
        let overlapping_private_address = Varnode::unique(0x178, 8);
        let mut block = R2ILBlock::new(0x3300, 4);
        if !matches!(mutation, FrameMutation::ZeroSaveRange) {
            if matches!(mutation, FrameMutation::PositiveSaveRange) {
                block.push(R2ILOp::IntAdd {
                    dst: sp.clone(),
                    a: sp.clone(),
                    b: Varnode::constant(8, 8),
                });
            } else {
                block.push(R2ILOp::IntSub {
                    dst: sp.clone(),
                    a: sp.clone(),
                    b: Varnode::constant(8, 8),
                });
            }
        }
        if matches!(mutation, FrameMutation::StaleSplitAllocation) {
            block.push(R2ILOp::Copy {
                dst: stale_save_address.clone(),
                src: sp.clone(),
            });
        }
        if matches!(
            mutation,
            FrameMutation::SplitAllocation | FrameMutation::StaleSplitAllocation
        ) {
            block.push(R2ILOp::IntSub {
                dst: sp.clone(),
                a: sp.clone(),
                b: Varnode::constant(8, 8),
            });
        }
        block.push(R2ILOp::Copy {
            dst: saved_frame_pointer.clone(),
            src: fp.clone(),
        });
        block.push(R2ILOp::Store {
            space: if matches!(mutation, FrameMutation::CustomSaveAndRestore) {
                SpaceId::Custom(1)
            } else {
                SpaceId::Ram
            },
            addr: if matches!(mutation, FrameMutation::StaleSplitAllocation) {
                stale_save_address
            } else {
                sp.clone()
            },
            val: saved_frame_pointer,
        });
        if !matches!(mutation, FrameMutation::RestoreBeforeRelation) {
            if matches!(mutation, FrameMutation::WrongAffineRoot) {
                block.push(R2ILOp::Copy {
                    dst: fp.clone(),
                    src: ra.clone(),
                });
            } else if matches!(mutation, FrameMutation::AffineRelation) {
                block.push(R2ILOp::IntAdd {
                    dst: fp.clone(),
                    a: sp.clone(),
                    b: Varnode::constant(0, 8),
                });
            } else {
                block.push(R2ILOp::Copy {
                    dst: fp.clone(),
                    src: sp.clone(),
                });
            }
        }
        if matches!(
            mutation,
            FrameMutation::ImplicitPrivateStack
                | FrameMutation::ImplicitPrivateStackCall
                | FrameMutation::ImplicitPrivateStackOverlap
        ) {
            block.push(R2ILOp::IntSub {
                dst: first_private_address.clone(),
                a: fp.clone(),
                b: Varnode::constant(8, 8),
            });
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: first_private_address.clone(),
                val: Varnode::constant(0x1122_3344, 4),
            });
            block.push(R2ILOp::Load {
                dst: first_private_value.clone(),
                space: SpaceId::Ram,
                addr: first_private_address,
            });
            block.push(R2ILOp::IntSub {
                dst: second_private_address.clone(),
                a: fp.clone(),
                b: Varnode::constant(4, 8),
            });
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: second_private_address.clone(),
                val: first_private_value,
            });
            block.push(R2ILOp::Load {
                dst: second_private_value,
                space: SpaceId::Ram,
                addr: second_private_address,
            });
            if matches!(mutation, FrameMutation::ImplicitPrivateStackOverlap) {
                block.push(R2ILOp::IntAdd {
                    dst: overlapping_private_address.clone(),
                    a: fp.clone(),
                    b: Varnode::constant(4, 8),
                });
                block.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: overlapping_private_address,
                    val: Varnode::constant(0, 4),
                });
            }
        }
        match mutation {
            FrameMutation::OverlappingWrite => block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: fp.clone(),
                val: Varnode::constant(0, 8),
            }),
            FrameMutation::Call | FrameMutation::ImplicitPrivateStackCall => {
                block.push(R2ILOp::Call {
                    target: Varnode::ram(0x4400, 8),
                })
            }
            FrameMutation::UnknownEffect => block.push(R2ILOp::CallOther {
                output: None,
                userop: 7,
                inputs: vec![],
            }),
            FrameMutation::Escape => {
                block.push(R2ILOp::IntAdd {
                    dst: escape_address.clone(),
                    a: fp.clone(),
                    b: Varnode::constant(16, 8),
                });
                block.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: escape_address,
                    val: fp.clone(),
                });
            }
            FrameMutation::PartialFramePointerWrite => block.push(R2ILOp::Copy {
                dst: Varnode::register(0, 4),
                src: Varnode::constant(0, 4),
            }),
            FrameMutation::None
            | FrameMutation::MissingAllocationContract
            | FrameMutation::OppositeAllocationContract
            | FrameMutation::ExplicitNoSlots
            | FrameMutation::ComposedReturn
            | FrameMutation::MissingExplicitNoSlots
            | FrameMutation::AffineRelation
            | FrameMutation::ZeroObligationRelation
            | FrameMutation::TransitiveRestore
            | FrameMutation::DirectLoadRestore
            | FrameMutation::SplitAllocation
            | FrameMutation::WrongRestoreRange
            | FrameMutation::MissingRestore
            | FrameMutation::WrongRestoreStorage
            | FrameMutation::RestoreBeforeRelation
            | FrameMutation::PositiveSaveRange
            | FrameMutation::ZeroSaveRange
            | FrameMutation::OtherRestoreSpace
            | FrameMutation::CustomSaveAndRestore
            | FrameMutation::StaleSplitAllocation
            | FrameMutation::GlobalLoad
            | FrameMutation::ParameterMemory
            | FrameMutation::UnknownPointerLoad
            | FrameMutation::WrongAffineRoot
            | FrameMutation::EntrySelfLoop
            | FrameMutation::UnbalancedStackPointer
            | FrameMutation::StackedReturn
            | FrameMutation::StackedNoContract
            | FrameMutation::StackedWrongOffset
            | FrameMutation::StackedWrongWidth
            | FrameMutation::StackedWrongSpace
            | FrameMutation::StackedWrongTarget
            | FrameMutation::StackedWrongDelta
            | FrameMutation::StackedZeroExit
            | FrameMutation::StackedDuplicateRead
            | FrameMutation::StackedUnledgeredRead
            | FrameMutation::StackedOverlappingStore
            | FrameMutation::StackedPartialOverlappingStore
            | FrameMutation::StackedUnknownPointerStore
            | FrameMutation::StackedAtomic
            | FrameMutation::ImplicitPrivateStack
            | FrameMutation::ImplicitPrivateStackOverlap => {}
        }
        if matches!(mutation, FrameMutation::ParameterMemory) {
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::register(40, 8),
                val: Varnode::constant(0x1122_3344, 4),
            });
            block.push(R2ILOp::Load {
                dst: unrelated_load.clone(),
                space: SpaceId::Ram,
                addr: Varnode::register(40, 8),
            });
        } else if matches!(mutation, FrameMutation::GlobalLoad) {
            block.push(R2ILOp::Load {
                dst: unrelated_load.clone(),
                space: SpaceId::Ram,
                addr: Varnode::constant(0x8800, 8),
            });
        } else if matches!(mutation, FrameMutation::UnknownPointerLoad) {
            block.push(R2ILOp::Load {
                dst: unrelated_load.clone(),
                space: SpaceId::Ram,
                addr: Varnode::register(24, 8),
            });
        }
        let restore_address = if matches!(mutation, FrameMutation::WrongRestoreRange) {
            block.push(R2ILOp::IntAdd {
                dst: restore_address.clone(),
                a: fp.clone(),
                b: Varnode::constant(8, 8),
            });
            restore_address
        } else if matches!(
            mutation,
            FrameMutation::RestoreBeforeRelation | FrameMutation::ZeroObligationRelation
        ) {
            sp.clone()
        } else {
            fp.clone()
        };
        if !matches!(mutation, FrameMutation::MissingRestore) {
            block.push(R2ILOp::Load {
                dst: if matches!(mutation, FrameMutation::DirectLoadRestore) {
                    fp.clone()
                } else {
                    loaded.clone()
                },
                space: if matches!(
                    mutation,
                    FrameMutation::OtherRestoreSpace | FrameMutation::CustomSaveAndRestore
                ) {
                    SpaceId::Custom(1)
                } else {
                    SpaceId::Ram
                },
                addr: restore_address,
            });
            if !matches!(mutation, FrameMutation::DirectLoadRestore) {
                let restored = if matches!(mutation, FrameMutation::TransitiveRestore) {
                    block.push(R2ILOp::Copy {
                        dst: restore_copy.clone(),
                        src: loaded,
                    });
                    restore_copy
                } else {
                    loaded
                };
                block.push(R2ILOp::Copy {
                    dst: if matches!(mutation, FrameMutation::WrongRestoreStorage) {
                        Varnode::register(24, 8)
                    } else {
                        fp.clone()
                    },
                    src: restored,
                });
            }
        }
        if matches!(mutation, FrameMutation::RestoreBeforeRelation) {
            block.push(R2ILOp::Copy {
                dst: fp.clone(),
                src: sp.clone(),
            });
        }
        if !matches!(mutation, FrameMutation::UnbalancedStackPointer) {
            block.push(R2ILOp::IntAdd {
                dst: sp.clone(),
                a: sp.clone(),
                b: Varnode::constant(
                    if matches!(
                        mutation,
                        FrameMutation::SplitAllocation | FrameMutation::StaleSplitAllocation
                    ) {
                        16
                    } else {
                        8
                    },
                    8,
                ),
            });
        }
        let mut return_target = ra.clone();
        if stacked_return {
            if matches!(mutation, FrameMutation::StackedOverlappingStore) {
                block.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: sp.clone(),
                    val: Varnode::constant(0, 8),
                });
            } else if matches!(mutation, FrameMutation::StackedPartialOverlappingStore) {
                block.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: sp.clone(),
                    val: Varnode::constant(0, 4),
                });
            } else if matches!(mutation, FrameMutation::StackedUnknownPointerStore) {
                block.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: Varnode::register(24, 8),
                    val: Varnode::constant(0, 8),
                });
            }
            let return_slot = if matches!(mutation, FrameMutation::StackedWrongOffset) {
                block.push(R2ILOp::IntAdd {
                    dst: adjusted_return_slot.clone(),
                    a: sp.clone(),
                    b: Varnode::constant(8, 8),
                });
                adjusted_return_slot
            } else {
                sp.clone()
            };
            if matches!(mutation, FrameMutation::StackedDuplicateRead) {
                block.push(R2ILOp::Load {
                    dst: duplicate_return_address,
                    space: SpaceId::Ram,
                    addr: return_slot.clone(),
                });
            }
            if matches!(mutation, FrameMutation::StackedUnledgeredRead) {
                block.push(R2ILOp::LoadGuarded {
                    dst: ra.clone(),
                    space: SpaceId::Ram,
                    addr: return_slot,
                    guard: Varnode::constant(1, 1),
                    ordering: MemoryOrdering::Relaxed,
                });
            } else if matches!(mutation, FrameMutation::StackedAtomic) {
                block.push(R2ILOp::LoadLinked {
                    dst: ra.clone(),
                    space: SpaceId::Ram,
                    addr: return_slot,
                    ordering: MemoryOrdering::Relaxed,
                });
            } else {
                let target = if matches!(mutation, FrameMutation::StackedWrongWidth) {
                    Varnode::unique(0x150, 4)
                } else {
                    ra.clone()
                };
                block.push(R2ILOp::Load {
                    dst: target.clone(),
                    space: if matches!(mutation, FrameMutation::StackedWrongSpace) {
                        SpaceId::Custom(1)
                    } else {
                        SpaceId::Ram
                    },
                    addr: return_slot,
                });
                return_target = target;
            }
            if !matches!(mutation, FrameMutation::StackedZeroExit) {
                block.push(R2ILOp::IntAdd {
                    dst: sp.clone(),
                    a: sp.clone(),
                    b: Varnode::constant(
                        if matches!(mutation, FrameMutation::StackedWrongDelta) {
                            4
                        } else {
                            8
                        },
                        8,
                    ),
                });
            }
            if matches!(
                mutation,
                FrameMutation::StackedUnledgeredRead | FrameMutation::StackedAtomic
            ) {
                return_target = ra.clone();
            }
            if matches!(mutation, FrameMutation::StackedWrongTarget) {
                return_target = return_address;
            }
        }
        if matches!(mutation, FrameMutation::EntrySelfLoop) {
            block.push(R2ILOp::Branch {
                target: Varnode::ram(0x3300, 8),
            });
        } else {
            if matches!(mutation, FrameMutation::ComposedReturn) {
                block.push(R2ILOp::Copy {
                    dst: Varnode::register(32, 8),
                    src: Varnode::constant(0x1122_3344_5566_7788, 8),
                });
                block.push(R2ILOp::Copy {
                    dst: Varnode::register(32, 1),
                    src: Varnode::constant(0xaa, 1),
                });
            }
            block.push(R2ILOp::Return {
                target: return_target,
            });
        }

        let mut arch = ArchSpec::new(if matches!(mutation, FrameMutation::ParameterMemory) {
            "x86-64"
        } else {
            "preserved-frame-test"
        });
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("fp", 0, 8));
        arch.add_register(RegisterDef::sub("fp_low", 0, 4, "fp"));
        arch.add_register(RegisterDef::new("sp", 8, 8));
        arch.add_register(RegisterDef::new("ra", 16, 8));
        arch.add_register(RegisterDef::new("other", 24, 8));
        arch.add_register(RegisterDef::new("ret", 32, 8));
        arch.add_register(RegisterDef::sub("ret_low", 32, 1, "ret"));
        if matches!(mutation, FrameMutation::ParameterMemory) {
            arch.add_register(RegisterDef::new("rdi", 40, 8));
        }
        arch.add_space(AddressSpace::ram(8));
        arch.add_space(AddressSpace::new(SpaceId::Custom(1), "other-memory", 8));
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let stack_slots = if matches!(
            mutation,
            FrameMutation::ExplicitNoSlots | FrameMutation::MissingExplicitNoSlots
        ) {
            Vec::new()
        } else {
            vec![SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                storage(0),
                0,
                8,
            )]
        };
        let return_kind = if matches!(mutation, FrameMutation::ComposedReturn) {
            SourceFunctionReturn::Register {
                storage: storage(32),
            }
        } else {
            SourceFunctionReturn::Void
        };
        let interface = if matches!(mutation, FrameMutation::ParameterMemory) {
            let logical_value = SourceLogicalValue::new(
                1,
                r2ssa::SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
            );
            let type_graph = r2ssa::SourceTypeGraph::new(
                [
                    r2ssa::SourceType::new(0, r2ssa::SourceTypeKind::UnsignedInteger, 32, 32),
                    r2ssa::SourceType::new(
                        1,
                        r2ssa::SourceTypeKind::Pointer { target_type_id: 0 },
                        64,
                        64,
                    ),
                ],
                [],
            )
            .expect("parameter-memory source type graph");
            SourceFunctionInterface::new_exact_with_logical_types(
                b"preserved-frame-revision-1".to_vec(),
                "test-frame-abi",
                [SourceAbiParameterSpec::new(0, storage(40))],
                return_kind,
                stack_slots,
                [logical_value],
                None,
                Some(type_graph),
            )
        } else {
            SourceFunctionInterface::new_exact(
                b"preserved-frame-revision-1".to_vec(),
                "test-frame-abi",
                [],
                return_kind,
                stack_slots,
            )
        }
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(8)))
        .expect("exact preserved-frame interface");
        let interface = if matches!(mutation, FrameMutation::MissingAllocationContract) {
            interface
        } else {
            let growth = if matches!(mutation, FrameMutation::OppositeAllocationContract) {
                SourceStackGrowth::HigherAddresses
            } else {
                SourceStackGrowth::LowerAddresses
            };
            let contract = if matches!(
                mutation,
                FrameMutation::ImplicitPrivateStack
                    | FrameMutation::ImplicitPrivateStackCall
                    | FrameMutation::ImplicitPrivateStackOverlap
            ) {
                SourceStackAllocationContract::with_implicit_active_sp_bytes(growth, 8)
            } else {
                SourceStackAllocationContract::new(growth)
            };
            interface
                .with_stack_allocation_contract(contract)
                .expect("exact preserved-frame stack allocation contract")
        };
        let interface = if matches!(mutation, FrameMutation::ExplicitNoSlots) {
            interface
                .with_frame_pointer_storage(storage(0))
                .expect("explicit frame-pointer storage")
        } else {
            interface
        };
        let interface = if stacked_return && !matches!(mutation, FrameMutation::StackedNoContract) {
            interface
                .with_exact_stacked_return(0, 8, 8, 8)
                .expect("exact stacked return contract")
        } else {
            interface
        };
        SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("preserved-frame artifact")
    }

    fn preserved_frame_two_return_artifact(mutation: TwoReturnMutation) -> SsaArtifact {
        let fp = Varnode::register(0, 8);
        let sp = Varnode::register(8, 8);
        let ra = Varnode::register(16, 8);
        let mut entry = R2ILBlock::new(0x3300, 4);
        entry.push(R2ILOp::IntSub {
            dst: sp.clone(),
            a: sp.clone(),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: Varnode::unique(0x200, 8),
            src: fp.clone(),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: sp.clone(),
            val: Varnode::unique(0x200, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: fp.clone(),
            src: sp.clone(),
        });
        if matches!(
            mutation,
            TwoReturnMutation::SharedRead | TwoReturnMutation::DuplicateDominatingRead
        ) {
            entry.push(R2ILOp::IntAdd {
                dst: Varnode::unique(0x208, 8),
                a: sp.clone(),
                b: Varnode::constant(8, 8),
            });
            entry.push(R2ILOp::Load {
                dst: if matches!(mutation, TwoReturnMutation::SharedRead) {
                    ra.clone()
                } else {
                    Varnode::unique(0x210, 8)
                },
                space: SpaceId::Ram,
                addr: Varnode::unique(0x208, 8),
            });
        }
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x3320, 8),
            cond: Varnode::constant(1, 1),
        });

        let build_return = |addr, loaded_offset, cross_arm_store| {
            let loaded = Varnode::unique(loaded_offset, 8);
            let mut block = R2ILBlock::new(addr, 4);
            block.push(R2ILOp::Load {
                dst: loaded.clone(),
                space: SpaceId::Ram,
                addr: fp.clone(),
            });
            block.push(R2ILOp::Copy {
                dst: fp.clone(),
                src: loaded,
            });
            block.push(R2ILOp::IntAdd {
                dst: sp.clone(),
                a: sp.clone(),
                b: Varnode::constant(8, 8),
            });
            if cross_arm_store {
                block.push(R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: sp.clone(),
                    val: Varnode::constant(0, 8),
                });
            }
            if !matches!(mutation, TwoReturnMutation::SharedRead) {
                block.push(R2ILOp::Load {
                    dst: ra.clone(),
                    space: SpaceId::Ram,
                    addr: sp.clone(),
                });
            }
            block.push(R2ILOp::IntAdd {
                dst: sp.clone(),
                a: sp.clone(),
                b: Varnode::constant(8, 8),
            });
            block.push(R2ILOp::Return { target: ra.clone() });
            block
        };
        let fallthrough = build_return(
            0x3304,
            0x218,
            matches!(mutation, TwoReturnMutation::CrossArmStore),
        );
        let taken = build_return(0x3320, 0x220, false);

        let mut arch = ArchSpec::new("two-return-preserved-frame-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("fp", 0, 8));
        arch.add_register(RegisterDef::new("sp", 8, 8));
        arch.add_register(RegisterDef::new("ra", 16, 8));
        arch.add_space(AddressSpace::ram(8));
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"two-return-frame-revision-1".to_vec(),
            "test-frame-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                storage(0),
                0,
                8,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(8)))
        .and_then(|interface| {
            interface.with_stack_allocation_contract(SourceStackAllocationContract::new(
                SourceStackGrowth::LowerAddresses,
            ))
        })
        .and_then(|interface| interface.with_exact_stacked_return(0, 8, 8, 8))
        .expect("exact two-return frame interface");
        SsaArtifact::for_decompile_with_interface(
            &[entry, fallthrough, taken],
            Some(&arch),
            interface,
        )
        .expect("two-return preserved-frame artifact")
    }

    fn preserved_frame_evidence(artifact: &SsaArtifact) -> Option<FramePreservationEvidence> {
        let projection = MachineProjection::from_artifact(artifact).ok()?;
        let topology = certified_source_topology(artifact).ok()?;
        let memory = certified_memory_statements(artifact).ok()?;
        let returns = certified_return_controls(artifact, &topology).ok()?;
        let mut expressions = BTreeMap::new();
        for entity in projection.entities() {
            let source_obligations = entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if source_obligations.is_empty() {
                continue;
            }
            let expression =
                certified_expr_from_projection(artifact, &projection, entity, source_obligations)
                    .ok()?;
            expressions.insert(entity.producer(), expression);
        }
        frame_evidence_from_certified_parts(
            artifact,
            &projection,
            &topology,
            &expressions,
            &memory,
            &returns,
        )
    }

    fn frameless_stack_evidence(artifact: &SsaArtifact) -> Option<StackDisciplineEvidence> {
        let projection = MachineProjection::from_artifact(artifact).ok()?;
        let topology = certified_source_topology(artifact).ok()?;
        let memory = certified_memory_statements(artifact).ok()?;
        let returns = certified_return_controls(artifact, &topology).ok()?;
        stack_discipline_evidence_from_certified_parts(
            artifact,
            &projection,
            &topology,
            &memory,
            &returns,
            None,
        )
    }

    fn frameless_stack_evidence_with_missing_memory_statement(
        artifact: &SsaArtifact,
    ) -> Option<StackDisciplineEvidence> {
        let projection = MachineProjection::from_artifact(artifact).ok()?;
        let topology = certified_source_topology(artifact).ok()?;
        let mut memory = certified_memory_statements(artifact).ok()?;
        let first = *memory.keys().next()?;
        memory.remove(&first);
        let returns = certified_return_controls(artifact, &topology).ok()?;
        stack_discipline_evidence_from_certified_parts(
            artifact,
            &projection,
            &topology,
            &memory,
            &returns,
            None,
        )
    }

    #[derive(Clone, Copy)]
    enum StackAuthorityMutation {
        None,
        OriginSchema,
        OriginAuthority,
        LedgerAuthority,
    }

    fn certified_frameless_stack(
        artifact_mutation: StackDisciplineMutation,
        authority_mutation: StackAuthorityMutation,
    ) -> Option<CertifiedStackDiscipline> {
        let artifact = frameless_stack_artifact(artifact_mutation);
        let projection = MachineProjection::from_artifact(&artifact).ok()?;
        let machine_context = CertifiedMachineContext::from_artifact(&artifact).ok()?;
        let topology = certified_source_topology(&artifact).ok()?;
        let memory = certified_memory_statements(&artifact).ok()?;
        let returns = certified_return_controls(&artifact, &topology).ok()?;
        let mut expressions = BTreeMap::new();
        for entity in projection.entities() {
            let source_obligations = entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if source_obligations.is_empty() {
                continue;
            }
            let expression =
                certified_expr_from_projection(&artifact, &projection, entity, source_obligations)
                    .ok()?;
            expressions.insert(entity.producer(), expression);
        }
        let mut origin = CertifiedArtifactOrigin {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            lift_provenance_schema_version: GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION,
            lift_manifest_hash: 1,
            authority: CertifiedAuthoritySeal::new(),
            graph_snapshot: vec![1].into_boxed_slice(),
            prepare_mode: artifact.mode().into(),
            decompile_preparation: None,
            assumptions: artifact.facts().assumptions.clone(),
            machine_context,
            source: artifact.obligations().clone(),
            topology: topology.clone(),
        };
        let mut certification = CertifiedFunction::bound(origin.source().clone(), &origin).ok()?;
        for control in returns.values() {
            certification.record_absorbed_return(control.clone()).ok()?;
        }
        for statement in memory.values() {
            for obligation in statement.source_obligations() {
                certification
                    .record_absorbed_statement(*obligation, statement.clone())
                    .ok()?;
            }
        }
        for expression in expressions.values() {
            for obligation in expression.entity().source_obligations() {
                certification
                    .record_absorbed_expression(*obligation, expression.clone())
                    .ok()?;
            }
        }
        match authority_mutation {
            StackAuthorityMutation::None => {}
            StackAuthorityMutation::OriginSchema => {
                origin.schema_version += 1;
            }
            StackAuthorityMutation::OriginAuthority => {
                origin.authority = CertifiedAuthoritySeal::new();
            }
            StackAuthorityMutation::LedgerAuthority => {
                certification.ledger.authority = CertifiedAuthoritySeal::new();
            }
        }
        certified_stack_discipline(
            &artifact,
            &origin,
            FrameCertifiedParts {
                projection: &projection,
                topology: &topology,
                expressions: &expressions,
                memory_statements: &memory,
                return_controls: &returns,
            },
            None,
            certification.ledger(),
        )
    }

    #[derive(Clone, Copy)]
    enum PreservedStackAuthorityMutation {
        None,
        MissingFrame,
        ForeignFrame,
        MutatedSavedRange,
        MutatedEntrySaveObject,
    }

    fn certified_preserved_stack(
        artifact_mutation: FrameMutation,
        authority_mutation: PreservedStackAuthorityMutation,
    ) -> Option<CertifiedStackDiscipline> {
        let artifact = preserved_frame_artifact(artifact_mutation);
        let projection = MachineProjection::from_artifact(&artifact).ok()?;
        let machine_context = CertifiedMachineContext::from_artifact(&artifact).ok()?;
        let topology = certified_source_topology(&artifact).ok()?;
        let memory = certified_memory_statements(&artifact).ok()?;
        let returns = certified_return_controls(&artifact, &topology).ok()?;
        let mut expressions = BTreeMap::new();
        for entity in projection.entities() {
            let source_obligations = entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if source_obligations.is_empty() {
                continue;
            }
            let expression =
                certified_expr_from_projection(&artifact, &projection, entity, source_obligations)
                    .ok()?;
            expressions.insert(entity.producer(), expression);
        }
        let origin = CertifiedArtifactOrigin {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            lift_provenance_schema_version: GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION,
            lift_manifest_hash: 1,
            authority: CertifiedAuthoritySeal::new(),
            graph_snapshot: vec![1].into_boxed_slice(),
            prepare_mode: artifact.mode().into(),
            decompile_preparation: None,
            assumptions: artifact.facts().assumptions.clone(),
            machine_context,
            source: artifact.obligations().clone(),
            topology: topology.clone(),
        };
        let mut certification = CertifiedFunction::bound(origin.source().clone(), &origin).ok()?;
        for control in returns.values() {
            certification.record_absorbed_return(control.clone()).ok()?;
        }
        for statement in memory.values() {
            for obligation in statement.source_obligations() {
                certification
                    .record_absorbed_statement(*obligation, statement.clone())
                    .ok()?;
            }
        }
        for expression in expressions.values() {
            for obligation in expression.entity().source_obligations() {
                certification
                    .record_absorbed_expression(*obligation, expression.clone())
                    .ok()?;
            }
        }
        let parts = FrameCertifiedParts {
            projection: &projection,
            topology: &topology,
            expressions: &expressions,
            memory_statements: &memory,
            return_controls: &returns,
        };
        let mut frame =
            certified_frame_preservation(&artifact, &origin, parts, certification.ledger())?;
        match authority_mutation {
            PreservedStackAuthorityMutation::None
            | PreservedStackAuthorityMutation::MissingFrame => {}
            PreservedStackAuthorityMutation::ForeignFrame => {
                frame.origin.authority = CertifiedAuthoritySeal::new();
            }
            PreservedStackAuthorityMutation::MutatedSavedRange => {
                frame.saved_range.offset = frame.saved_range.offset.checked_sub(4)?;
            }
            PreservedStackAuthorityMutation::MutatedEntrySaveObject => {
                frame.entry_save.object = ObjectId(frame.entry_save.object.0.checked_add(1)?);
            }
        }
        let frame = (!matches!(
            authority_mutation,
            PreservedStackAuthorityMutation::MissingFrame
        ))
        .then_some(&frame);
        certified_stack_discipline(&artifact, &origin, parts, frame, certification.ledger())
    }

    fn terminal_frame_fixture(
        mutation: FrameMutation,
    ) -> Option<(
        SsaArtifact,
        CertifiedArtifactOrigin,
        ObligationLedger,
        CertifiedFramePreservation,
        Vec<TypedRegionMapping>,
    )> {
        let artifact = preserved_frame_artifact(mutation);
        let projection = MachineProjection::from_artifact(&artifact).ok()?;
        let machine_context = CertifiedMachineContext::from_artifact(&artifact).ok()?;
        let topology = certified_source_topology(&artifact).ok()?;
        let memory = certified_memory_statements(&artifact).ok()?;
        let returns = certified_return_controls(&artifact, &topology).ok()?;
        let mut expressions = BTreeMap::new();
        for entity in projection.entities() {
            let source_obligations = entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if source_obligations.is_empty() {
                continue;
            }
            let expression =
                certified_expr_from_projection(&artifact, &projection, entity, source_obligations)
                    .ok()?;
            expressions.insert(entity.producer(), expression);
        }
        let origin = CertifiedArtifactOrigin {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            lift_provenance_schema_version: GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION,
            lift_manifest_hash: 1,
            authority: CertifiedAuthoritySeal::new(),
            graph_snapshot: vec![1].into_boxed_slice(),
            prepare_mode: artifact.mode().into(),
            decompile_preparation: None,
            assumptions: artifact.facts().assumptions.clone(),
            machine_context,
            source: artifact.obligations().clone(),
            topology: topology.clone(),
        };
        let mut certification = CertifiedFunction::bound(origin.source().clone(), &origin).ok()?;
        for control in returns.values() {
            certification.record_absorbed_return(control.clone()).ok()?;
        }
        for statement in memory.values() {
            for obligation in statement.source_obligations() {
                certification
                    .record_absorbed_statement(*obligation, statement.clone())
                    .ok()?;
            }
        }
        for expression in expressions.values() {
            for obligation in expression.entity().source_obligations() {
                certification
                    .record_absorbed_expression(*obligation, expression.clone())
                    .ok()?;
            }
        }
        let frame = certified_frame_preservation(
            &artifact,
            &origin,
            FrameCertifiedParts {
                projection: &projection,
                topology: &topology,
                expressions: &expressions,
                memory_statements: &memory,
                return_controls: &returns,
            },
            certification.ledger(),
        )?;
        let mappings = origin
            .source()
            .obligations()
            .keys()
            .map(|obligation| {
                let [effect] = certification.ledger().effects(*obligation) else {
                    return None;
                };
                Some(TypedRegionMapping::new(
                    *obligation,
                    effect.disposition().clone(),
                ))
            })
            .collect::<Option<Vec<_>>>()?;
        Some((
            artifact,
            origin,
            certification.ledger().clone(),
            frame,
            mappings,
        ))
    }

    #[test]
    fn generic_frameless_stack_seals_exact_reservation_accesses_and_release() {
        let artifact = frameless_stack_artifact(StackDisciplineMutation::None);
        assert!(
            artifact
                .machine_context()
                .function_interface()
                .expect("frameless interface")
                .stack_slots()
                .is_empty(),
            "private objects must not come from source-declared slots"
        );
        let evidence = frameless_stack_evidence(&artifact).expect("frameless stack evidence");
        assert_eq!(evidence.stack_pointer_storage.offset, 0);
        assert_eq!(evidence.reservation_range.offset(), -16);
        assert_eq!(evidence.reservation_range.size_bytes(), 16);
        assert_eq!(evidence.private_ownership_range, evidence.reservation_range);
        assert_eq!(evidence.implicit_active_sp_bytes, 0);
        assert_eq!(
            evidence
                .reservation
                .normalized_affine_relation()
                .offset_bytes(),
            -16
        );
        assert_eq!(evidence.assignments.len(), 2);
        assert_eq!(evidence.releases.len(), 1);
        assert!(evidence.releases[0].post_restoration().is_none());
        assert!(evidence.releases[0].return_address_read().is_none());
        assert_eq!(
            evidence.releases[0]
                .restoration()
                .normalized_affine_relation()
                .offset_bytes(),
            0
        );
        let access_ranges = evidence
            .private_regions
            .iter()
            .flat_map(|object| object.accesses())
            .map(CertifiedPrivateStackAccess::range)
            .collect::<Vec<_>>();
        assert_eq!(access_ranges.len(), 4);
        assert!(
            access_ranges
                .iter()
                .all(|range| { matches!(range.offset(), -8 | -4) && range.size_bytes() == 4 })
        );

        let upward = frameless_stack_evidence(&frameless_stack_artifact(
            StackDisciplineMutation::HigherAddresses,
        ))
        .expect("the same proof supports an exact upward-growing source contract");
        assert_eq!(upward.reservation_range.offset(), 0);
        assert_eq!(upward.reservation_range.size_bytes(), 16);
        assert_eq!(
            upward
                .private_regions
                .iter()
                .flat_map(|region| region.accesses())
                .map(CertifiedPrivateStackAccess::range)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([
                CertifiedNormalizedStackRange {
                    offset: 8,
                    size_bytes: 4,
                },
                CertifiedNormalizedStackRange {
                    offset: 12,
                    size_bytes: 4,
                },
            ])
        );

        let certificate =
            certified_frameless_stack(StackDisciplineMutation::None, StackAuthorityMutation::None)
                .expect("same-origin ledger seals frameless stack discipline");
        let metadata_only = certified_frameless_stack(
            StackDisciplineMutation::ExactUnusedFramePointer,
            StackAuthorityMutation::None,
        )
        .expect("unused exact frame-pointer identity remains frameless");
        assert_eq!(metadata_only.stack_pointer_storage().offset, 0);
        assert!(
            certified_frameless_stack(
                StackDisciplineMutation::UnpreservedFrameUse,
                StackAuthorityMutation::None,
            )
            .is_none(),
            "an actual frame-pointer definition requires preservation evidence"
        );
        assert_eq!(certificate.schema_version(), CERTIFICATION_SCHEMA_VERSION);
        assert_eq!(
            certificate.private_ownership_range(),
            certificate.reservation_range()
        );
        assert_eq!(certificate.implicit_active_sp_bytes(), 0);
        let wire = serde_json::to_value((
            certificate.schema_version,
            certificate.stack_pointer_storage,
            certificate.reservation_range,
            certificate.private_ownership_range,
            certificate.implicit_active_sp_bytes,
            &certificate.reservation,
            &certificate.assignments,
            &certificate.private_regions,
            &certificate.releases,
        ))
        .expect("serialized stack certificate payload");
        assert_eq!(
            wire.get(0).and_then(serde_json::Value::as_u64),
            Some(u64::from(CERTIFICATION_SCHEMA_VERSION))
        );
        assert_eq!(
            wire.get(7)
                .and_then(serde_json::Value::as_array)
                .map(Vec::len),
            Some(2)
        );

        let stacked = certified_preserved_stack(
            FrameMutation::StackedReturn,
            PreservedStackAuthorityMutation::None,
        )
        .expect("same-origin frame evidence seals the x86 O0 stacked-return shape");
        assert_eq!(stacked.reservation_range.offset(), -8);
        assert_eq!(stacked.releases.len(), 1);
        assert!(stacked.releases[0].post_restoration().is_some());
        assert!(stacked.releases[0].return_address_read().is_some());
    }

    #[test]
    fn preserved_frame_extends_private_ownership_into_exact_implicit_sp_area() {
        preserved_frame_evidence(&preserved_frame_artifact(
            FrameMutation::ImplicitPrivateStack,
        ))
        .expect("implicit private accesses preserve exact frame evidence");
        let certificate = certified_preserved_stack(
            FrameMutation::ImplicitPrivateStack,
            PreservedStackAuthorityMutation::None,
        )
        .expect("same-origin frame mechanics open the exact implicit SP envelope");
        assert_eq!(certificate.reservation_range().offset(), -8);
        assert_eq!(certificate.reservation_range().size_bytes(), 8);
        assert_eq!(certificate.private_ownership_range().offset(), -16);
        assert_eq!(certificate.private_ownership_range().size_bytes(), 16);
        assert_eq!(certificate.implicit_active_sp_bytes(), 8);
        let private_ranges = certificate
            .private_regions()
            .iter()
            .flat_map(CertifiedPrivateStackRegion::accesses)
            .map(CertifiedPrivateStackAccess::range)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            private_ranges,
            BTreeSet::from([
                CertifiedNormalizedStackRange {
                    offset: -16,
                    size_bytes: 4,
                },
                CertifiedNormalizedStackRange {
                    offset: -12,
                    size_bytes: 4,
                },
            ])
        );
        assert!(private_ranges.iter().all(|range| {
            !frame_ranges_overlap(
                *range,
                CertifiedNormalizedStackRange {
                    offset: -8,
                    size_bytes: 8,
                },
                64,
            )
        }));
        let wire = serde_json::to_value((
            certificate.private_ownership_range(),
            certificate.implicit_active_sp_bytes(),
        ))
        .expect("serialized stack ownership fields");
        assert_eq!(wire.get(1).and_then(serde_json::Value::as_u64), Some(8));
        assert_eq!(
            wire.get(0)
                .and_then(|range| range.get("offset"))
                .and_then(serde_json::Value::as_i64),
            Some(-16)
        );
    }

    #[test]
    fn implicit_private_stack_requires_exact_frame_mechanics_and_no_calls() {
        for mutation in [
            PreservedStackAuthorityMutation::MissingFrame,
            PreservedStackAuthorityMutation::ForeignFrame,
            PreservedStackAuthorityMutation::MutatedSavedRange,
            PreservedStackAuthorityMutation::MutatedEntrySaveObject,
        ] {
            assert!(
                certified_preserved_stack(FrameMutation::ImplicitPrivateStack, mutation).is_none(),
                "mutated frame authority must refuse"
            );
        }
        assert!(
            certified_preserved_stack(
                FrameMutation::ImplicitPrivateStackCall,
                PreservedStackAuthorityMutation::None,
            )
            .is_none(),
            "a call invalidates the implicit active-SP area"
        );
        assert!(
            certified_preserved_stack(
                FrameMutation::ImplicitPrivateStackOverlap,
                PreservedStackAuthorityMutation::None,
            )
            .is_none(),
            "any non-mechanical access overlapping the saved frame must refuse"
        );
    }

    #[test]
    fn generic_frameless_stack_refuses_mutations_and_foreign_authority() {
        for mutation in [
            StackDisciplineMutation::MissingAllocationContract,
            StackDisciplineMutation::OppositeAllocationContract,
            StackDisciplineMutation::MissingReservation,
            StackDisciplineMutation::WrongReservation,
            StackDisciplineMutation::MissingRestoration,
            StackDisciplineMutation::WrongRestoration,
            StackDisciplineMutation::PartialStackPointerWrite,
            StackDisciplineMutation::ExtraStackPointerWrite,
            StackDisciplineMutation::OutOfEnvelopeAccess,
            StackDisciplineMutation::StackPointerEscape,
            StackDisciplineMutation::Call,
            StackDisciplineMutation::UnknownEffect,
            StackDisciplineMutation::EntryReturnAddressOverlap,
            StackDisciplineMutation::AccessBeforeReservation,
            StackDisciplineMutation::AccessAfterRestoration,
        ] {
            assert!(
                frameless_stack_evidence(&frameless_stack_artifact(mutation)).is_none(),
                "stack mutation must refuse: {mutation:?}"
            );
        }
        assert!(
            frameless_stack_evidence_with_missing_memory_statement(&frameless_stack_artifact(
                StackDisciplineMutation::None,
            ))
            .is_none(),
            "omitting one canonical memory statement must refuse the certificate"
        );
        for mutation in [
            FrameMutation::StackedNoContract,
            FrameMutation::StackedWrongOffset,
            FrameMutation::StackedWrongWidth,
            FrameMutation::StackedWrongSpace,
            FrameMutation::StackedWrongTarget,
            FrameMutation::StackedWrongDelta,
            FrameMutation::StackedZeroExit,
            FrameMutation::StackedDuplicateRead,
            FrameMutation::StackedUnledgeredRead,
            FrameMutation::StackedOverlappingStore,
            FrameMutation::StackedPartialOverlappingStore,
            FrameMutation::StackedUnknownPointerStore,
            FrameMutation::StackedAtomic,
        ] {
            assert!(
                frameless_stack_evidence(&preserved_frame_artifact(mutation)).is_none(),
                "bad stacked-return stack discipline must refuse: {mutation:?}"
            );
        }
        for mutation in [
            StackAuthorityMutation::OriginSchema,
            StackAuthorityMutation::OriginAuthority,
            StackAuthorityMutation::LedgerAuthority,
        ] {
            assert!(certified_frameless_stack(StackDisciplineMutation::None, mutation).is_none());
        }
    }

    #[test]
    fn terminal_return_frame_memory_requires_exact_preservation_manifest() {
        let (_, origin, ledger, frame, mappings) =
            terminal_frame_fixture(FrameMutation::StackedReturn)
                .expect("stacked frame terminal fixture");
        assert!(
            certify_terminal_return_region_with_frame(
                &origin,
                &ledger,
                mappings.clone(),
                Some(&frame),
            )
            .is_ok()
        );
        assert_eq!(
            certify_terminal_return_region(&origin, &ledger, mappings),
            Err(LedgerClosureError::InvalidRegionTopology),
        );

        let (_, origin, ledger, frame, mappings) =
            terminal_frame_fixture(FrameMutation::GlobalLoad)
                .expect("frame with unrelated global read");
        assert_eq!(
            certify_terminal_return_region_with_frame(&origin, &ledger, mappings, Some(&frame),),
            Err(LedgerClosureError::InvalidRegionTopology),
        );
    }

    #[test]
    fn frame_replay_kernel_refuses_missing_foreign_and_altered_save_restore_evidence() {
        let (artifact, origin, ledger, frame, _) =
            terminal_frame_fixture(FrameMutation::StackedReturn)
                .expect("stacked frame replay fixture");
        let replayed = replay_certified_frame_preservation(&artifact, &origin, &ledger)
            .expect("exact frame replay");
        assert_eq!(replayed, frame);

        let mut foreign_origin = origin.clone();
        foreign_origin.authority = CertifiedAuthoritySeal::new();
        assert!(replay_certified_frame_preservation(&artifact, &foreign_origin, &ledger).is_none());

        let mut foreign_frame = frame.clone();
        foreign_frame.origin.authority = CertifiedAuthoritySeal::new();
        assert_ne!(replayed, foreign_frame);
        let mut altered_range = frame.clone();
        altered_range.saved_range.offset -= 4;
        assert_ne!(replayed, altered_range);
        let mut altered_save = frame.clone();
        altered_save.entry_save.object = ObjectId(altered_save.entry_save.object.0 + 1);
        assert_ne!(replayed, altered_save);
        let mut altered_restore = frame.clone();
        altered_restore.restores[0].restore_read.object =
            ObjectId(altered_restore.restores[0].restore_read.object.0 + 1);
        assert_ne!(replayed, altered_restore);

        for statement in [frame.entry_save(), frame.restores()[0].restore_read()] {
            let obligation = *statement.source_obligations().iter().next().unwrap();
            let mut incomplete = ledger.clone();
            incomplete.effects.remove(&obligation);
            assert!(replay_certified_frame_preservation(&artifact, &origin, &incomplete).is_none());
        }
    }

    #[test]
    fn generic_preserved_frame_requires_sealed_save_relation_and_all_return_restore() {
        let artifact = preserved_frame_artifact(FrameMutation::None);
        let evidence = preserved_frame_evidence(&artifact).expect("preserved frame evidence");
        assert_eq!(evidence.frame_pointer_storage.offset, 0);
        assert_eq!(evidence.stack_pointer_storage.offset, 8);
        assert_eq!(evidence.saved_range.offset(), -8);
        assert_eq!(evidence.saved_range.size_bytes(), 8);
        assert_eq!(evidence.entry_save_copies.len(), 1);
        assert_eq!(evidence.restores.len(), 1);
        assert!(evidence.restores[0].1.copies.is_empty());
        assert_eq!(evidence.restores[0].1.range, evidence.saved_range);
        assert!(evidence.restores[0].2.is_none());

        let slot_derived_interface = artifact
            .machine_context()
            .function_interface()
            .expect("slot-derived frame interface");
        assert!(slot_derived_interface.frame_pointer_storage().is_none());
        assert!(!slot_derived_interface.stack_slots().is_empty());

        let explicit_artifact = preserved_frame_artifact(FrameMutation::ExplicitNoSlots);
        let explicit_interface = explicit_artifact
            .machine_context()
            .function_interface()
            .expect("explicit frame interface");
        assert!(explicit_interface.stack_slots().is_empty());
        assert_eq!(
            explicit_interface.frame_pointer_storage(),
            Some(evidence.frame_pointer_storage)
        );
        let explicit = preserved_frame_evidence(&explicit_artifact)
            .expect("explicit no-slot frame preservation evidence");
        assert_eq!(
            explicit.frame_pointer_storage,
            evidence.frame_pointer_storage
        );
        assert_eq!(explicit.saved_range, evidence.saved_range);

        let affine =
            preserved_frame_evidence(&preserved_frame_artifact(FrameMutation::AffineRelation))
                .expect("affine stack-derived relation");
        assert_eq!(affine.saved_range, evidence.saved_range);
        let affine_relation = affine
            .frame_relation
            .normalized_affine_relation()
            .expect("sealed normalized affine assignment");
        assert_eq!(affine_relation.base_storage(), affine.stack_pointer_storage);
        assert_eq!(affine_relation.offset_bytes(), -8);
        assert_eq!(affine_relation.width_bits(), 64);

        let zero_obligation_artifact =
            preserved_frame_artifact(FrameMutation::ZeroObligationRelation);
        let zero_obligation = preserved_frame_evidence(&zero_obligation_artifact)
            .expect("proven-dead frame relation remains mechanical evidence");
        let relation_instruction = zero_obligation_artifact
            .obligations()
            .instructions()
            .get(&zero_obligation.frame_relation.producer())
            .expect("frame relation source instruction");
        assert!(relation_instruction.obligations.is_empty());
        assert_eq!(
            relation_instruction.state,
            SemanticInstructionState::ProvenDead
        );
        assert_eq!(
            zero_obligation.frame_relation.normalized_affine_relation(),
            evidence.frame_relation.normalized_affine_relation()
        );

        let transitive =
            preserved_frame_evidence(&preserved_frame_artifact(FrameMutation::TransitiveRestore))
                .expect("bounded restore copy chain");
        assert_eq!(transitive.restores[0].1.copies.len(), 1);
        for mutation in [
            FrameMutation::DirectLoadRestore,
            FrameMutation::SplitAllocation,
            FrameMutation::GlobalLoad,
            FrameMutation::ParameterMemory,
            FrameMutation::ComposedReturn,
        ] {
            assert!(
                preserved_frame_evidence(&preserved_frame_artifact(mutation)).is_some(),
                "supported exact shape: {mutation:?}"
            );
        }

        let stacked_artifact = preserved_frame_artifact(FrameMutation::StackedReturn);
        let stacked = preserved_frame_evidence(&stacked_artifact)
            .expect("pinned x86 stacked return frame evidence");
        let return_read = stacked.restores[0]
            .2
            .as_ref()
            .expect("stacked return retains its exact RAM read");
        assert_eq!(return_read.space(), MachineAddressSpace::Ram);
        assert_eq!(return_read.word_size_bytes(), 1);
        assert_eq!(return_read.width_bits(), 64);

        let two_return = preserved_frame_evidence(&preserved_frame_two_return_artifact(
            TwoReturnMutation::None,
        ))
        .expect("distinct stacked reads seal both return arms");
        assert_eq!(two_return.restores.len(), 2);
        let return_read_producers = two_return
            .restores
            .iter()
            .map(|(_, _, read)| read.as_ref().expect("sealed return read").producer())
            .collect::<BTreeSet<_>>();
        assert_eq!(return_read_producers.len(), 2);

        let shared_return = preserved_frame_evidence(&preserved_frame_two_return_artifact(
            TwoReturnMutation::SharedRead,
        ))
        .expect("one dominating stacked read may serve both return arms");
        assert_eq!(shared_return.restores.len(), 2);
        let shared_read_producers = shared_return
            .restores
            .iter()
            .map(|(_, _, read)| read.as_ref().expect("sealed return read").producer())
            .collect::<BTreeSet<_>>();
        assert_eq!(shared_read_producers.len(), 1);
    }

    #[test]
    fn frame_relation_witness_binds_machine_assignment_and_replays_live_obligations() {
        let artifact = preserved_frame_artifact(FrameMutation::ZeroObligationRelation);
        let projection = MachineProjection::from_artifact(&artifact).expect("machine projection");
        let evidence = preserved_frame_evidence(&artifact).expect("zero-obligation frame evidence");
        let relation = evidence.frame_relation.clone();
        let entry_stack_pointer = artifact
            .graph()
            .values
            .iter()
            .find(|value| {
                value.canonical_storage == Some(evidence.stack_pointer_storage)
                    && artifact.graph().def_inst(value.id).is_none()
            })
            .expect("entry stack pointer")
            .id;
        let mut affine = BTreeMap::new();
        assert!(frame_affine_register_assignment_matches(
            FrameAffineRegisterContext {
                artifact: &artifact,
                projection: &projection,
                entry_stack_pointer,
                stack_pointer_storage: evidence.stack_pointer_storage,
                register_storage: evidence.frame_pointer_storage,
                width_bits: 64,
            },
            &relation,
            &mut affine,
        ));

        let other_entity = projection
            .entities()
            .iter()
            .find(|entity| entity.producer() != relation.producer)
            .expect("independent machine entity");
        let other_input = artifact
            .graph()
            .values
            .iter()
            .find(|value| value.id != relation.input.binding().value())
            .and_then(|value| MachineValueUse::from_artifact(&artifact, value.id).ok())
            .expect("independent machine input");
        let assert_invalid = |assignment: &CertifiedFrameRegisterAssignment| {
            assert!(!frame_affine_register_assignment_matches(
                FrameAffineRegisterContext {
                    artifact: &artifact,
                    projection: &projection,
                    entry_stack_pointer,
                    stack_pointer_storage: evidence.stack_pointer_storage,
                    register_storage: evidence.frame_pointer_storage,
                    width_bits: 64,
                },
                assignment,
                &mut BTreeMap::new(),
            ));
        };
        let mut mutated = relation.clone();
        mutated.producer = other_entity.producer();
        assert_invalid(&mutated);
        let mut mutated = relation.clone();
        mutated.root = other_entity.root();
        assert_invalid(&mutated);
        let mut mutated = relation.clone();
        mutated.input = other_input;
        assert_invalid(&mutated);
        let mut mutated = relation.clone();
        mutated.output = other_entity.output();
        assert_invalid(&mutated);
        let mut mutated = relation.clone();
        mutated.storage = evidence.stack_pointer_storage;
        assert_invalid(&mutated);
        let mut mutated = relation.clone();
        mutated
            .normalized_affine_relation
            .as_mut()
            .expect("normalized relation")
            .offset_bytes += 1;
        assert_invalid(&mutated);

        let no_obligations = BTreeSet::new();
        assert!(frame_mechanical_producer_is_accounted(
            &artifact,
            &projection,
            FrameMechanicalWitness {
                producer: relation.producer,
                root: relation.root,
                output: relation.output,
            },
            &no_obligations,
            &BTreeMap::new(),
            &ObligationLedger::new(),
        ));

        let live_artifact = preserved_frame_artifact(FrameMutation::None);
        let live_projection =
            MachineProjection::from_artifact(&live_artifact).expect("live machine projection");
        let live_evidence = preserved_frame_evidence(&live_artifact).expect("live frame evidence");
        let live_entity = live_projection
            .entity_for_producer(live_evidence.frame_relation.producer)
            .expect("live frame relation entity");
        let live_obligations = live_entity
            .source_obligations()
            .iter()
            .copied()
            .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
            .collect::<BTreeSet<_>>();
        assert!(!live_obligations.is_empty());
        let live_expression = certified_expr_from_projection(
            &live_artifact,
            &live_projection,
            live_entity,
            live_obligations.clone(),
        )
        .expect("live frame relation expression");
        let expressions = BTreeMap::from([(
            live_evidence.frame_relation.producer,
            live_expression.clone(),
        )]);
        let live_witness = FrameMechanicalWitness {
            producer: live_evidence.frame_relation.producer,
            root: live_evidence.frame_relation.root,
            output: live_evidence.frame_relation.output,
        };
        assert!(!frame_mechanical_producer_is_accounted(
            &live_artifact,
            &live_projection,
            live_witness,
            &no_obligations,
            &expressions,
            &ObligationLedger::new(),
        ));
        let mut certification = CertifiedFunction::new(live_artifact.obligations().clone())
            .expect("live relation ledger");
        for obligation in live_obligations {
            certification
                .record_absorbed_expression(obligation, live_expression.clone())
                .expect("ledger live relation expression");
        }
        assert!(frame_mechanical_producer_is_accounted(
            &live_artifact,
            &live_projection,
            live_witness,
            &no_obligations,
            &expressions,
            certification.ledger(),
        ));
    }

    #[test]
    fn generic_preserved_frame_refuses_mutated_authority_inputs() {
        assert!(
            preserved_frame_evidence(&preserved_frame_artifact(
                FrameMutation::MissingExplicitNoSlots
            ))
            .is_none(),
            "a no-slot interface without explicit FP authority must refuse"
        );

        let storage = |offset, size| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        };
        let explicit_base = SourceFunctionInterface::new_exact(
            b"invalid-explicit-frame-revision".to_vec(),
            "test-frame-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(8, 8)))
        .expect("coherent no-slot interface");
        assert!(
            explicit_base
                .clone()
                .with_frame_pointer_storage(storage(0, 4))
                .is_err(),
            "wrong-width explicit FP authority must not be constructible"
        );
        assert!(
            explicit_base
                .with_frame_pointer_storage(storage(8, 8))
                .is_err(),
            "overlapping explicit FP authority must not be constructible"
        );

        for mutation in [
            FrameMutation::MissingAllocationContract,
            FrameMutation::OppositeAllocationContract,
            FrameMutation::OverlappingWrite,
            FrameMutation::Call,
            FrameMutation::UnknownEffect,
            FrameMutation::Escape,
            FrameMutation::WrongRestoreRange,
            FrameMutation::MissingRestore,
            FrameMutation::WrongRestoreStorage,
            FrameMutation::RestoreBeforeRelation,
            FrameMutation::PositiveSaveRange,
            FrameMutation::ZeroSaveRange,
            FrameMutation::OtherRestoreSpace,
            FrameMutation::CustomSaveAndRestore,
            FrameMutation::StaleSplitAllocation,
            FrameMutation::UnknownPointerLoad,
            FrameMutation::WrongAffineRoot,
            FrameMutation::EntrySelfLoop,
            FrameMutation::UnbalancedStackPointer,
            FrameMutation::PartialFramePointerWrite,
            FrameMutation::StackedNoContract,
            FrameMutation::StackedWrongOffset,
            FrameMutation::StackedWrongWidth,
            FrameMutation::StackedWrongSpace,
            FrameMutation::StackedWrongTarget,
            FrameMutation::StackedWrongDelta,
            FrameMutation::StackedZeroExit,
            FrameMutation::StackedDuplicateRead,
            FrameMutation::StackedUnledgeredRead,
            FrameMutation::StackedOverlappingStore,
            FrameMutation::StackedPartialOverlappingStore,
            FrameMutation::StackedUnknownPointerStore,
            FrameMutation::StackedAtomic,
        ] {
            assert!(
                preserved_frame_evidence(&preserved_frame_artifact(mutation)).is_none(),
                "mutation must refuse: {mutation:?}"
            );
        }
        for mutation in [
            TwoReturnMutation::CrossArmStore,
            TwoReturnMutation::DuplicateDominatingRead,
        ] {
            assert!(
                preserved_frame_evidence(&preserved_frame_two_return_artifact(mutation)).is_none(),
                "two-return mutation must refuse: {mutation:?}"
            );
        }
    }

    fn obligation_ids(source: &SemanticObligationInventory) -> Vec<SemanticObligationId> {
        source.obligations().keys().copied().collect()
    }

    fn output_for(
        source: &SemanticObligationInventory,
        id: SemanticObligationId,
    ) -> CertifiedEntity {
        CertifiedEntity::certify(source, id.instruction, [id]).expect("certified output")
    }

    #[test]
    fn corrupted_memory_statement_witnesses_fail_artifact_revalidation() {
        let artifact = typed_memory_artifact();
        let statements = certified_memory_statements(&artifact).expect("memory statements");
        let load = artifact
            .graph()
            .insts
            .iter()
            .find(|inst| matches!(inst.payload, InstPayload::Op(SSAOp::Load { .. })))
            .expect("load instruction");
        let store = artifact
            .graph()
            .insts
            .iter()
            .find(|inst| matches!(inst.payload, InstPayload::Op(SSAOp::Store { .. })))
            .expect("store instruction");
        let load_producer = artifact
            .obligations()
            .instruction_for_inst(load.id)
            .expect("load source")
            .id;
        let store_producer = artifact
            .obligations()
            .instruction_for_inst(store.id)
            .expect("store source")
            .id;
        let original = statements
            .get(&load_producer)
            .expect("load statement")
            .clone();
        original
            .validate_against_artifact(&artifact)
            .expect("original statement revalidates");
        let assert_invalid = |statement: &CertifiedMemoryStatement| {
            assert!(matches!(
                statement.validate_against_artifact(&artifact),
                Err(MachineBuildError::ObligationMismatch(_))
            ));
        };

        let mut corrupted = original.clone();
        corrupted.schema_version += 1;
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        corrupted.producer = store_producer;
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        corrupted.access.ordinal += 1;
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        corrupted.object = ObjectId(corrupted.object.0 + 1);
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        corrupted.address =
            MachineValueUse::from_artifact(&artifact, load.output.expect("load output"))
                .expect("replacement value use");
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        corrupted.space = MachineAddressSpace::Custom(77);
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        corrupted.endianness = MachineMemoryEndianness::Little;
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        corrupted.word_size_bytes += 1;
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        corrupted.width_bits += 8;
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        let CertifiedMemoryStatementKind::Read { result } = original.kind() else {
            panic!("load read expected");
        };
        corrupted.kind = CertifiedMemoryStatementKind::Write {
            value: result.clone(),
        };
        assert_invalid(&corrupted);
        let mut corrupted = original.clone();
        let obligation = *corrupted
            .source_obligations
            .first()
            .expect("memory obligation");
        corrupted.source_obligations = BTreeSet::from([SemanticObligationId {
            kind: SemanticObligationKind::ObservableMemoryWrite,
            ..obligation
        }]);
        assert_invalid(&corrupted);
    }

    #[test]
    fn mixed_endian_memory_has_no_certified_helper_semantics() {
        let address = Varnode::register(0, 8);
        let loaded = Varnode::unique(0x10, 4);
        let mut block = R2ILBlock::new(0x1850, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: address.clone(),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address,
            val: loaded,
        });
        let mut arch = ArchSpec::new("mixed-memory-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Mixed);
        let artifact = SsaArtifact::raw(&[block], Some(&arch)).expect("mixed memory artifact");
        let statements = certified_memory_statements(&artifact).expect("memory extraction");
        assert!(statements.is_empty());
    }

    #[test]
    fn certified_topology_retains_empty_source_blocks() {
        let mut entry = R2ILBlock::new(0x3800, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x3810, 8),
        });
        let empty = R2ILBlock::new(0x3810, 4);
        let artifact = SsaArtifact::raw(&[entry, empty], None).expect("two-block artifact");
        let topology = certified_source_topology(&artifact).expect("source topology");

        assert_eq!(topology.blocks().len(), artifact.graph().blocks.len());
        assert_eq!(topology.entry_addr(), 0x3800);
        assert!(matches!(
            topology.block(0x3800).map(|block| block.terminator()),
            Some(CertifiedSourceTerminator::Branch { target: 0x3810 })
        ));
        assert!(
            topology
                .block(0x3810)
                .is_some_and(|block| block.instructions().is_empty())
        );
    }

    #[test]
    fn direct_branch_rejects_available_architecture_target_width_mismatch() {
        let mut entry = R2ILBlock::new(0x3838, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x3848, 8),
        });
        let target = R2ILBlock::new(0x3848, 4);
        let mut arch = ArchSpec::new("32-bit-direct-test");
        arch.addr_size = 4;
        let artifact =
            SsaArtifact::raw(&[entry, target], Some(&arch)).expect("direct branch artifact");
        let topology = certified_source_topology(&artifact).expect("source topology");
        let controls = certified_direct_controls(&artifact, &topology).expect("direct controls");
        assert!(controls.is_empty());
    }

    #[test]
    fn direct_branch_uses_r2il_effective_architecture_width_fallback() {
        let mut entry = R2ILBlock::new(0x30, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x40, 1),
        });
        let target = R2ILBlock::new(0x40, 4);
        let mut arch = ArchSpec::new("fallback-width-direct-test");
        arch.addr_size = 1;
        arch.add_register(RegisterDef::new("pc", 0, 8));
        let artifact =
            SsaArtifact::raw(&[entry, target], Some(&arch)).expect("direct branch artifact");
        let context = CertifiedMachineContext::from_artifact(&artifact).expect("machine context");
        assert_eq!(context.memory_model().default_address_bits(), 64);
        let topology = certified_source_topology(&artifact).expect("source topology");
        let controls = certified_direct_controls(&artifact, &topology).expect("direct controls");
        assert!(controls.is_empty());
    }

    #[test]
    fn conditional_control_rejects_non_byte_condition_and_available_arch_width_mismatch() {
        let build = |condition_size, arch: Option<&ArchSpec>| {
            let mut entry = R2ILBlock::new(0x3880, 4);
            entry.push(R2ILOp::CBranch {
                target: Varnode::ram(0x3890, 8),
                cond: Varnode::constant(1, condition_size),
            });
            let fallthrough = R2ILBlock::new(0x3884, 4);
            let taken = R2ILBlock::new(0x3890, 4);
            SsaArtifact::raw(&[entry, fallthrough, taken], arch).expect("conditional artifact")
        };
        let wide_condition = build(2, None);
        let mut arch = ArchSpec::new("32-bit-conditional-test");
        arch.addr_size = 4;
        let wrong_target_width = build(1, Some(&arch));

        for artifact in [wide_condition, wrong_target_width] {
            let topology = certified_source_topology(&artifact).expect("source topology");
            let controls =
                certified_conditional_controls(&artifact, &topology).expect("conditional controls");
            assert!(controls.is_empty());
        }
    }

    #[test]
    fn conditional_control_rejects_unrepresentable_fallthrough_target() {
        let mut entry = R2ILBlock::new(0xffff_fffe, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x1000, 4),
            cond: Varnode::constant(1, 1),
        });
        let taken = R2ILBlock::new(0x1000, 4);
        let fallthrough = R2ILBlock::new(0x1_0000_0002, 4);
        let mut arch = ArchSpec::new("32-bit-fallthrough-boundary-test");
        arch.addr_size = 4;
        let artifact = SsaArtifact::raw(&[entry, taken, fallthrough], Some(&arch))
            .expect("boundary conditional artifact");
        let topology = certified_source_topology(&artifact).expect("source topology");
        let controls =
            certified_conditional_controls(&artifact, &topology).expect("conditional controls");
        assert!(controls.is_empty());
    }

    #[test]
    fn certified_owner_retains_typed_memory_context_without_guessing_missing_architecture() {
        let mut block = R2ILBlock::new(0x3850, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
            val: Varnode::constant(1, 1),
        });
        let unavailable_artifact =
            SsaArtifact::raw(&[block.clone()], None).expect("untyped architecture artifact");
        let unavailable = CertifiedMachineContext::from_artifact(&unavailable_artifact)
            .expect("unavailable machine context");
        assert!(!unavailable.memory_model().is_available());
        assert_eq!(
            unavailable.source().memory_space_at(0x3850, 0),
            Some(SpaceId::Ram)
        );

        let mut arch = ArchSpec::new("big-endian-test");
        arch.set_memory_endianness(Endianness::Big);
        let artifact =
            SsaArtifact::raw(&[block], Some(&arch)).expect("typed architecture artifact");
        let certified =
            CertifiedMachineContext::from_artifact(&artifact).expect("typed machine context");
        assert!(certified.memory_model().is_available());
        assert!(certified.memory_model().is_coherent());
        assert_eq!(
            certified
                .memory_model()
                .space(SpaceId::Ram)
                .map(r2ssa::MachineMemorySpace::endianness),
            Some(r2ssa::MachineMemoryEndianness::Big)
        );
    }

    #[test]
    fn certified_topology_retains_conditional_branch_arm_identity() {
        let mut entry = R2ILBlock::new(0x3900, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x3910, 8),
            cond: Varnode::register(0, 1),
        });
        let mut false_block = R2ILBlock::new(0x3904, 4);
        false_block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut true_block = R2ILBlock::new(0x3910, 4);
        true_block.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });
        let artifact = SsaArtifact::raw(&[entry, false_block, true_block], None)
            .expect("conditional artifact");
        let topology = certified_source_topology(&artifact).expect("source topology");

        assert!(matches!(
            topology.block(0x3900).map(|block| block.terminator()),
            Some(CertifiedSourceTerminator::ConditionalBranch {
                true_target: 0x3910,
                false_target: 0x3904,
            })
        ));
    }

    #[test]
    fn synthetic_direct_void_caller_parameter_refuses_incomplete_machine_roles() {
        let target = Varnode::ram(0x7620, 8);
        let argument = Varnode::register(8, 8);
        let mut entry = R2ILBlock::new(0x7520, 4);
        entry.push(R2ILOp::Copy {
            dst: argument.clone(),
            src: argument,
        });
        entry.push(R2ILOp::Call {
            target: target.clone(),
        });
        let fallthrough = R2ILBlock::new(0x7524, 4);
        let mut arch = ArchSpec::new("certified-call-parameter-test");
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        let argument_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 8,
            size: 8,
        };
        let revision = b"certified-call-parameter-revision-1";
        let function_interface = SourceFunctionInterface::new(
            revision.to_vec(),
            "test-call-abi",
            [SourceAbiParameterSpec::new(0, argument_storage)],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("function interface");
        let identity =
            SourceCallSiteIdentity::new(0x7520, 1, CanonicalStorageId::from_varnode(&target));
        let call_interface = SourceCallSiteInterface::new(
            revision.to_vec(),
            identity,
            true,
            "test-call-abi",
            [SourceCallArgumentSpec::new(0, argument_storage)],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("callsite interface");
        let artifact = SsaArtifact::raw_with_interfaces(
            &[entry, fallthrough],
            Some(&arch),
            Some(function_interface),
            vec![call_interface],
        )
        .expect("parameter call artifact");
        assert!(matches!(
            CertifiedMachineContext::from_artifact(&artifact),
            Err(MachineBuildError::MachineContextMismatch)
        ));
    }

    #[test]
    fn synthetic_interface_register_return_refuses_incomplete_machine_roles() {
        let return_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let artifact = explicit_return_artifact(SourceFunctionReturn::Register {
            storage: return_storage,
        });
        assert!(matches!(
            CertifiedMachineContext::from_artifact(&artifact),
            Err(MachineBuildError::MachineContextMismatch)
        ));
    }

    #[test]
    fn exact_composed_rax_al_return_is_sealed_and_mutations_refuse() {
        let artifact = composed_rax_al_return_artifact();
        let topology = certified_source_topology(&artifact).expect("source topology");
        let controls = certified_return_controls(&artifact, &topology).expect("return controls");
        let mut controls = controls.values();
        let control = controls.next().expect("one composed return control");
        assert!(controls.next().is_none());
        assert!(control.values().is_empty());
        let [composition] = control.register_compositions() else {
            panic!("one return-register composition");
        };
        assert_eq!(
            composition.slot(),
            CallBoundarySlot::Register {
                index: 0,
                storage: CanonicalStorageId {
                    space: CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 8,
                },
            }
        );
        assert_eq!(composition.base().storage().size, 8);
        let [overlay] = composition.overlays() else {
            panic!("one exact AL overlay");
        };
        assert_eq!(overlay.definition().storage().size, 1);
        assert_eq!(overlay.offset_bytes(), 0);
        let ordered = composition
            .ordered_values()
            .map(|value| value.binding().value())
            .collect::<Vec<_>>();
        let obligation = artifact
            .obligations()
            .obligations()
            .get(&composition.source_obligation())
            .expect("composed ReturnValue obligation");
        assert_eq!(obligation.inputs, ordered);
        assert_eq!(control.source_obligations().len(), 2);
        assert_eq!(
            return_control_input_producers(control),
            [
                composition.base().producer(),
                overlay.definition().producer()
            ]
            .into_iter()
            .collect()
        );

        let (&boundary_at, boundary) = artifact
            .facts()
            .boundaries
            .returns
            .first_key_value()
            .expect("return boundary");
        let return_producer = artifact
            .obligations()
            .instruction_for_inst(boundary_at)
            .expect("return disposition")
            .id;
        let refuses = |boundary: &SourceReturnBoundaryFact| {
            certified_return_shapes(&artifact, boundary_at, return_producer, boundary)
                .expect("shape validation")
                .is_none()
        };

        let mut mixed = boundary.clone();
        mixed.values.push(r2ssa::CallBoundaryValueFact {
            slot: mixed.register_compositions[0].slot,
            value: mixed.register_compositions[0].base.value,
        });
        assert!(refuses(&mixed));

        let mut missing = boundary.clone();
        missing.register_compositions.clear();
        assert!(refuses(&missing));

        let mut wrong_base_storage = boundary.clone();
        wrong_base_storage.register_compositions[0]
            .base
            .storage
            .size = 4;
        assert!(refuses(&wrong_base_storage));

        let mut wrong_base_value = boundary.clone();
        wrong_base_value.register_compositions[0].base.value =
            wrong_base_value.register_compositions[0].overlays[0]
                .definition
                .value;
        assert!(refuses(&wrong_base_value));

        let mut wrong_base_producer = boundary.clone();
        wrong_base_producer.register_compositions[0].base.producer =
            wrong_base_producer.register_compositions[0].overlays[0]
                .definition
                .producer;
        assert!(refuses(&wrong_base_producer));

        let mut wrong_offset = boundary.clone();
        wrong_offset.register_compositions[0].overlays[0].offset_bytes = 1;
        assert!(refuses(&wrong_offset));

        let mut missing_overlay = boundary.clone();
        missing_overlay.register_compositions[0].overlays.clear();
        assert!(refuses(&missing_overlay));

        let mut reordered_obligation = (*control).clone();
        let composition = &mut reordered_obligation.register_compositions[0];
        std::mem::swap(
            &mut composition.base.value,
            &mut composition.overlays[0].definition.value,
        );
        assert!(
            reordered_obligation
                .validate(artifact.obligations())
                .is_err()
        );
    }

    #[test]
    fn logical_return_shape_accepts_exact_direct_or_composed_exclusively() {
        let one_control = |artifact: &SsaArtifact| {
            let topology = certified_source_topology(artifact).expect("source topology");
            let controls = certified_return_controls(artifact, &topology).expect("return controls");
            let mut controls = controls.into_values();
            let control = controls.next().expect("one return control");
            assert!(controls.next().is_none());
            control
        };

        let direct_artifact = exact_rax_return_artifact(false);
        let direct = one_control(&direct_artifact);
        let direct_interface = direct_artifact
            .machine_context()
            .function_interface()
            .expect("direct interface");
        assert_eq!(direct.values().len(), 1);
        assert!(direct.register_compositions().is_empty());
        assert!(return_control_matches_interface(&direct, direct_interface));

        let composed_artifact = exact_rax_return_artifact(true);
        let composed = one_control(&composed_artifact);
        let composed_interface = composed_artifact
            .machine_context()
            .function_interface()
            .expect("composed interface");
        assert!(composed.values().is_empty());
        assert_eq!(composed.register_compositions().len(), 1);
        assert!(return_control_matches_interface(
            &composed,
            composed_interface
        ));
        assert!(return_control_matches_closure(
            &composed,
            composed_interface,
            ReturnClosureContract::Terminal,
        ));
        for contract in [
            ReturnClosureContract::PlainRam,
            ReturnClosureContract::DirectCall,
            ReturnClosureContract::Conditional,
            ReturnClosureContract::Switch,
            ReturnClosureContract::Loop,
        ] {
            assert!(
                !return_control_matches_closure(&composed, composed_interface, contract),
                "nonterminal route must refuse composed return: {contract:?}"
            );
            assert!(
                return_control_matches_closure(&direct, direct_interface, contract),
                "direct return remains admitted: {contract:?}"
            );
        }

        let mut mixed = composed.clone();
        let composition = &mixed.register_compositions[0];
        mixed.values = vec![CertifiedReturnValue {
            slot: composition.slot,
            value: composition.base.value.clone(),
            source_obligation: composition.source_obligation,
        }]
        .into_boxed_slice();
        assert!(!return_control_matches_interface(
            &mixed,
            composed_interface
        ));

        let mut duplicate_direct = direct.clone();
        duplicate_direct.values =
            vec![direct.values[0].clone(), direct.values[0].clone()].into_boxed_slice();
        assert!(!return_control_matches_interface(
            &duplicate_direct,
            direct_interface
        ));

        let mut duplicate_composed = composed.clone();
        duplicate_composed.register_compositions = vec![
            composed.register_compositions[0].clone(),
            composed.register_compositions[0].clone(),
        ]
        .into_boxed_slice();
        assert!(!return_control_matches_interface(
            &duplicate_composed,
            composed_interface
        ));

        let mut wrong_slot = composed.clone();
        wrong_slot.register_compositions[0].slot = CallBoundarySlot::Register {
            index: 1,
            storage: wrong_slot.register_compositions[0].base.storage,
        };
        assert!(!return_control_matches_interface(
            &wrong_slot,
            composed_interface
        ));

        let void_interface = SourceFunctionInterface::new_exact(
            b"void-return-shape".to_vec(),
            "test-register-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("void interface");
        assert!(!return_control_matches_interface(&direct, &void_interface));
        assert!(!return_control_matches_interface(
            &composed,
            &void_interface
        ));
        let mut empty = direct.clone();
        empty.values = Box::new([]);
        assert!(return_control_matches_interface(&empty, &void_interface));
        assert!(!return_control_matches_interface(&empty, direct_interface));
    }

    #[test]
    fn synthetic_void_return_refuses_incomplete_machine_roles() {
        let artifact = explicit_return_artifact(SourceFunctionReturn::Void);
        assert!(matches!(
            CertifiedMachineContext::from_artifact(&artifact),
            Err(MachineBuildError::MachineContextMismatch)
        ));
    }

    #[test]
    fn synthetic_stack_slots_refuse_incomplete_machine_roles() {
        let artifact = explicit_stack_slot_artifact(8);
        assert!(matches!(
            CertifiedMachineContext::from_artifact(&artifact),
            Err(MachineBuildError::MachineContextMismatch)
        ));
    }

    #[test]
    fn exact_once_ledger_authorizes_fully_proven_source() {
        let mut function = CertifiedFunction::new(inventory()).expect("complete source");
        for id in obligation_ids(function.source()) {
            let output = output_for(function.source(), id);
            function.record_rendered(id, output).expect("output proof");
        }
        assert!(function.finish().is_closed_semantic_ledger());
    }

    #[test]
    fn exact_once_ledger_rejects_missing_and_duplicate_effects() {
        let mut function = CertifiedFunction::new(inventory()).expect("complete source");
        let ids = obligation_ids(function.source());
        let missing = ids[0];
        let duplicate = ids[1];
        for id in ids.iter().copied().filter(|id| *id != missing) {
            let output = output_for(function.source(), id);
            function.record_rendered(id, output).expect("output proof");
        }
        let output = output_for(function.source(), duplicate);
        function
            .record_rendered(duplicate, output)
            .expect("duplicate proof");
        let report = function.finish();
        assert_eq!(report.missing(), &[missing]);
        assert_eq!(report.duplicate(), &[duplicate]);
        assert!(!report.is_closed_semantic_ledger());
    }

    #[test]
    fn unsupported_semantics_must_residualize_or_refuse() {
        let source = unsupported_inventory();
        let ids = obligation_ids(&source);
        assert!(source.instructions().values().any(|instruction| {
            instruction.state == SemanticInstructionState::UnsupportedUnknown
        }));

        let mut rendered = CertifiedFunction::new(source.clone()).expect("complete source");
        for id in &ids {
            let output = output_for(rendered.source(), *id);
            rendered
                .record_rendered(*id, output)
                .expect("test-only structural proof");
        }
        assert_eq!(rendered.finish().invalid().len(), ids.len());

        let mut residual = CertifiedFunction::new(source).expect("complete source");
        for id in &ids {
            residual
                .residualize(*id, "unknown semantics")
                .expect("residual diagnostic");
        }
        let report = residual.finish();
        assert!(report.has_exactly_one_disposition_per_source());
        assert_eq!(report.residualized().len(), ids.len());
        assert!(!report.is_closed_semantic_ledger());
    }

    #[test]
    fn incomplete_rewrite_certificate_is_not_applied() {
        let mut function = CertifiedFunction::new(inventory()).expect("complete source");
        let ids = obligation_ids(function.source());
        let missing = ids[0];
        let condition = ids[1];
        let mut certificate = RewriteCertificate::new("while-to-for", [missing, condition]);
        certificate.push(
            condition,
            EffectDisposition::Rewritten {
                pass: "while-to-for".to_string(),
            },
        );
        let report = function.apply_rewrite(&certificate);
        assert_eq!(report.missing, vec![missing]);
        assert!(!report.invalid.is_empty());
        assert!(function.ledger().effects(condition).is_empty());
    }

    #[test]
    fn duplicate_rewrite_disposition_is_not_overwritten_or_applied() {
        let mut function = CertifiedFunction::new(inventory()).expect("complete source");
        let condition = obligation_ids(function.source())[0];
        let mut certificate = RewriteCertificate::new("if-normalize", [condition]);
        certificate.push(
            condition,
            EffectDisposition::Rewritten {
                pass: "if-normalize".to_string(),
            },
        );
        certificate.push(
            condition,
            EffectDisposition::Rewritten {
                pass: "if-normalize".to_string(),
            },
        );
        let report = function.apply_rewrite(&certificate);
        assert_eq!(report.duplicate, vec![condition]);
        assert!(function.ledger().effects(condition).is_empty());
    }

    #[test]
    fn self_attested_deadness_cannot_close_a_rewrite_certificate() {
        let mut function = CertifiedFunction::new(inventory()).expect("complete source");
        let write = obligation_ids(function.source())[0];
        let mut certificate = RewriteCertificate::new("unreachable-block", [write]);
        certificate.push(write, EffectDisposition::ProvenDead);
        assert!(!function.apply_rewrite(&certificate).is_closed());
        assert!(function.finish().missing().contains(&write));
        assert!(!function.finish().is_closed_semantic_ledger());
    }

    #[test]
    fn supersession_cycle_cannot_authorize_certified_c() {
        let mut function = CertifiedFunction::new(inventory()).expect("complete source");
        let ids = obligation_ids(function.source());
        let first = ids[0];
        let second = ids[1];
        let mut certificate = RewriteCertificate::new("cycle", [first, second]);
        certificate.push(first, EffectDisposition::Superseded { by: second });
        certificate.push(second, EffectDisposition::Superseded { by: first });
        assert!(!function.apply_rewrite(&certificate).is_closed());
        let report = function.finish();
        assert!(report.missing().contains(&first));
        assert!(report.missing().contains(&second));
        assert!(!report.is_closed_semantic_ledger());
    }

    #[test]
    fn output_entity_must_map_the_recorded_obligation() {
        let mut function = CertifiedFunction::new(inventory()).expect("complete source");
        let ids = obligation_ids(function.source());
        let read = ids[0];
        let write = ids[1];
        let wrong_output = output_for(function.source(), read);
        assert_eq!(
            function.record_rendered(write, wrong_output),
            Err(CertificationError::ObligationNotMapped(write))
        );
        assert_eq!(function.finish().missing().len(), ids.len());
    }

    #[test]
    fn incompatible_schema_and_rewrite_pass_are_rejected() {
        let source = inventory();
        let condition = obligation_ids(&source)[0];
        let mut certificate = RewriteCertificate::new("if-normalize", [condition]);
        certificate.push(
            condition,
            EffectDisposition::Rewritten {
                pass: "if-normalize".to_string(),
            },
        );
        certificate.schema_version = CERTIFICATION_SCHEMA_VERSION + 1;
        if let Some(dispositions) = certificate.dispositions.get_mut(&condition) {
            dispositions[0] = EffectDisposition::Rewritten {
                pass: "different-pass".to_string(),
            };
        }
        let report = certificate.audit(&source);
        assert_eq!(report.invalid.len(), 2);
        assert!(!report.is_closed());
    }

    #[test]
    fn terminal_return_mechanics_preserve_shared_producers_and_reject_malformed_closures() {
        let id = |ordinal| CanonicalInstructionId {
            block_addr: 0x5000,
            site: CanonicalInstructionSite::Op(ordinal),
        };
        let leaf = id(0);
        let return_address_read = id(1);
        let exit_stack_pointer = id(2);
        let semantic_consumer = id(3);
        let dependencies = BTreeMap::from([
            (leaf, BTreeSet::new()),
            (return_address_read, BTreeSet::from([leaf])),
            (exit_stack_pointer, BTreeSet::from([leaf])),
        ]);

        let pure = terminal_return_mechanics_producers(
            &dependencies,
            [return_address_read, exit_stack_pointer],
            [],
        )
        .expect("acyclic exact closure");
        assert_eq!(
            pure,
            BTreeSet::from([leaf, return_address_read, exit_stack_pointer])
        );

        let shared = terminal_return_mechanics_producers(
            &dependencies,
            [return_address_read, exit_stack_pointer],
            [return_address_read],
        )
        .expect("returned-value sharing remains structurally valid");
        assert_eq!(shared, BTreeSet::from([exit_stack_pointer]));

        let mut dependencies_with_outside_use = dependencies.clone();
        dependencies_with_outside_use
            .insert(semantic_consumer, BTreeSet::from([return_address_read]));
        let outside_use = terminal_return_mechanics_producers(
            &dependencies_with_outside_use,
            [return_address_read, exit_stack_pointer],
            [],
        )
        .expect("outside use is retained semantically");
        assert!(!outside_use.contains(&return_address_read));
        assert!(!outside_use.contains(&leaf));

        let cyclic = BTreeMap::from([
            (leaf, BTreeSet::from([return_address_read])),
            (return_address_read, BTreeSet::from([leaf])),
        ]);
        assert!(terminal_return_mechanics_producers(&cyclic, [return_address_read], []).is_none());
        assert!(
            terminal_return_mechanics_producers(
                &BTreeMap::from([(return_address_read, BTreeSet::from([leaf]))]),
                [return_address_read],
                [],
            )
            .is_none()
        );
    }

    #[test]
    fn composed_return_components_shared_with_terminal_mechanics_remain_semantic() {
        let artifact = composed_rax_al_return_artifact();
        let topology = certified_source_topology(&artifact).expect("source topology");
        let controls = certified_return_controls(&artifact, &topology).expect("return controls");
        let control = controls.values().next().expect("one return control");
        let [composition] = control.register_compositions() else {
            panic!("one return-register composition");
        };
        let component_producers = composition
            .ordered_values()
            .filter_map(MachineValueUse::producer)
            .collect::<BTreeSet<_>>();
        assert_eq!(component_producers.len(), 2);
        assert_eq!(
            terminal_return_semantic_producers(control),
            component_producers
        );

        let mechanical_root = CanonicalInstructionId {
            block_addr: 0x30a0,
            site: CanonicalInstructionSite::Op(99),
        };
        let mut dependencies = component_producers
            .iter()
            .copied()
            .map(|producer| (producer, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        dependencies.insert(mechanical_root, component_producers);
        let mechanics = terminal_return_mechanics_producers(
            &dependencies,
            [mechanical_root],
            terminal_return_semantic_producers(control),
        )
        .expect("shared composed-return closure");
        assert_eq!(mechanics, BTreeSet::from([mechanical_root]));
    }

    #[test]
    fn terminal_return_contract_admits_only_manifested_mechanical_reads() {
        let producer = CanonicalInstructionId {
            block_addr: 0x5100,
            site: CanonicalInstructionSite::Op(0),
        };
        let read = SemanticObligationId {
            instruction: producer,
            kind: SemanticObligationKind::ObservableMemoryRead,
            component: SemanticObligationComponent::MemoryAccess(0),
        };
        let write = SemanticObligationId {
            kind: SemanticObligationKind::ObservableMemoryWrite,
            ..read
        };
        let live = SemanticObligationId {
            kind: SemanticObligationKind::LiveValueProducer,
            component: SemanticObligationComponent::Whole,
            ..read
        };

        assert!(terminal_return_obligation_is_admitted(
            read,
            &BTreeSet::from([read]),
            &BTreeSet::new(),
        ));
        assert!(!terminal_return_obligation_is_admitted(
            read,
            &BTreeSet::new(),
            &BTreeSet::new(),
        ));
        assert!(terminal_return_obligation_is_admitted(
            write,
            &BTreeSet::new(),
            &BTreeSet::from([write]),
        ));
        assert!(terminal_return_obligation_is_admitted(
            live,
            &BTreeSet::new(),
            &BTreeSet::new(),
        ));
    }

    #[test]
    fn source_and_reports_are_issued_with_current_schemas() {
        let function = CertifiedFunction::new(inventory()).expect("source-issued inventory");
        let report = function.finish();
        assert_eq!(
            function.source().schema_version(),
            SEMANTIC_OBLIGATION_SCHEMA_VERSION
        );
        assert_eq!(report.schema_version(), CERTIFICATION_SCHEMA_VERSION);
        assert_eq!(report.source_obligation_count(), report.missing().len());
        assert!(!report.is_closed_semantic_ledger());
    }
}
