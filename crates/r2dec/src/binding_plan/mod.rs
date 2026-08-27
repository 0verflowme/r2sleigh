//! Typed boundary between canonical SSA facts and C lowering.
//!
//! Use and write geometry remain owned by the validated upstream
//! [`MachineProjection`]; this module delegates to that table instead of
//! copying a second answer into renderer-owned storage.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::CType;
use r2ssa::span::SpanId;
use r2ssa::{
    InstId, MachineExprId, MachineExprKind, MachineProjection, MachineUseDisposition,
    MachineWriteDisposition, MachineWriteProjection, SemanticId, SsaArtifactAuthority, UseSite,
    ValueId,
};
use r2types::SourceOwnedFunctionFacts;

/// Dense identity of one C object in a [`BindingPlan`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct BindingId(u32);

impl BindingId {
    /// Resolve an index in the sealed plan's dense binding domain.
    ///
    /// Callers must still validate the result against `BindingPlan::binding` or
    /// `BindingPlan::binding_count`; this conversion only prevents truncation.
    pub(crate) fn from_dense_index(index: usize) -> Option<Self> {
        u32::try_from(index).ok().map(Self)
    }

    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Opaque token minted only by this module's sealing pass after it has checked
/// the exact bound member set against the sorted upstream certificate sources.
/// It never repeats a machine location or stores a parallel member list.
#[derive(Debug, Clone, PartialEq, Eq)]
struct BindingCertificate {
    sources: Box<[BindingCertificateSource]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum BindingCertificateSource {
    Singleton,
    StorageSpan(SpanId),
    CertifiedEntity(SemanticId),
}

/// Declaration role proved by the same sealed facts that own the binding.
///
/// This is deliberately typed and name-free. In particular, a parameter is
/// externally declared because an exact source ABI slot owns it, never because
/// its presentation spelling resembles an argument register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BindingRole {
    Local,
    Parameter {
        slot: u32,
    },
    StackObject {
        object: r2ssa::ObjectId,
    },
    /// A caller-supplied value that no convention argument slot claims.
    ///
    /// SSA renaming gives version 0 to a read with no prior definition in this
    /// function, so such a value is supplied from outside by construction. The
    /// scratch registers a compiler reads before writing land here -- `xor ecx,
    /// ecx` reads `ecx` even though its result does not depend on it -- and so
    /// does any incoming register outside the convention's argument slots.
    ///
    /// The object therefore exists from function entry holding an indeterminate
    /// value, exactly as the machine does. Treating it as a local and demanding
    /// an assignment before its first read asks for a definition that cannot
    /// exist, which refused the whole function for saying what the program
    /// actually does.
    EntryValue,
}

/// One rendered C object. The name hint is presentation only, never identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Binding {
    declaration_type: CType,
    certificate: BindingCertificate,
    presentation_name_hint: Option<String>,
    /// Whether some member of this binding is supplied by the caller.
    ///
    /// Derived from the graph -- a value with no defining instruction -- and
    /// re-derived independently by the sealing oracle, never from a name or a
    /// register spelling.
    caller_supplied: bool,
}

impl Binding {
    pub(crate) const fn declaration_type(&self) -> &CType {
        &self.declaration_type
    }

    pub(crate) fn presentation_name_hint(&self) -> Option<&str> {
        self.presentation_name_hint.as_deref()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InlineProof {
    authority: SsaArtifactAuthority,
    literal: MachineExprId,
}

/// Proof that an exact upstream fact authorizes a value to have no rendered C
/// occurrence. The seal re-derives the reason-specific fact from the same SSA
/// authority; this token is not itself a second semantic answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ValueElisionProof {
    authority: SsaArtifactAuthority,
    value: ValueId,
}

/// Typed reason that a value cannot be represented honestly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ValueRefusal {
    MissingBindingCertificate { value: ValueId },
    MissingLiteralProjection { value: ValueId },
    IncoherentUseProjection { site: UseSite },
    IncoherentWriteProjection { value: ValueId },
    UnsupportedDeclarationWidth { value: ValueId, width_bits: u32 },
}

const fn declaration_width_is_supported(width_bits: u32) -> bool {
    matches!(width_bits, 8 | 16 | 32 | 64 | 128 | 256 | 512)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValueDisposition {
    Bound {
        binding: BindingId,
    },
    Inline {
        expr: MachineExprId,
        proof: InlineProof,
    },
    Elided {
        reason: r2ssa::ledger::ElisionReason,
        proof: ValueElisionProof,
    },
    Refused {
        reason: ValueRefusal,
    },
}

/// Exact graph uses that consume a source-certified machine return target.
///
/// This is a per-use answer. A return-address value may also have an ordinary
/// program use, which must remain renderable even though the `Return` operand
/// itself is machine control and has no C occurrence.
pub(super) fn certified_return_control_sites(source: &r2ssa::SsaArtifact) -> BTreeSet<UseSite> {
    let graph = source.graph();
    source
        .facts()
        .boundaries
        .returns
        .iter()
        .filter_map(|(at, boundary)| {
            let fact = boundary.return_address?;
            let site = UseSite {
                inst: *at,
                input_idx: 0,
            };
            (boundary.at == *at
                && graph.inst(*at).is_some_and(|inst| {
                    matches!(
                        inst.payload,
                        r2ssa::InstPayload::Op(r2ssa::SSAOp::Return { .. })
                    ) && inst.inputs.as_slice() == [fact.value]
                })
                && graph.use_sites(fact.value).contains(&site))
            .then_some(site)
        })
        .collect()
}

/// Return-target values whose complete use domain is machine return control.
///
/// Only these values may be globally elided from the binding domain. The
/// per-use accounting above remains independent so a mixed-use value stays
/// bound while its exact `Return` use is still justified as non-rendered.
pub(super) fn certified_return_control_values(source: &r2ssa::SsaArtifact) -> BTreeSet<ValueId> {
    let graph = source.graph();
    let sites = certified_return_control_sites(source);
    let mut values = sites
        .iter()
        .filter_map(|site| graph.inst(site.inst)?.inputs.get(site.input_idx).copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|value| {
            let uses = graph.use_sites(*value);
            !uses.is_empty() && uses.iter().all(|site| sites.contains(site))
        })
        .collect::<BTreeSet<_>>();
    values.extend(
        source
            .certificates()
            .machine_return_controls
            .values()
            .flat_map(|certificate| certificate.values.iter().copied()),
    );
    values
}

/// Exact direct-branch target uses already represented by CFG topology.
///
/// Only `Branch` and `CBranch` target operand zero qualify. Indirect branch,
/// call, predicate, and return operands have different rendering contracts.
pub(super) fn certified_direct_control_target_sites(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<UseSite> {
    let graph = source.graph();
    graph
        .insts
        .iter()
        .filter_map(|inst| {
            let target = match &inst.payload {
                r2ssa::InstPayload::Op(
                    r2ssa::SSAOp::Branch { target } | r2ssa::SSAOp::CBranch { target, .. },
                ) => target,
                _ => return None,
            };
            let value = graph.value_id_for_var(target)?;
            let site = UseSite {
                inst: inst.id,
                input_idx: 0,
            };
            (inst.inputs.first().copied() == Some(value) && graph.use_sites(value).contains(&site))
                .then_some(site)
        })
        .collect()
}

/// Direct-control target values whose complete use domain is CFG topology.
pub(super) fn certified_direct_control_target_values(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<ValueId> {
    let graph = source.graph();
    let sites = certified_direct_control_target_sites(source);
    sites
        .iter()
        .filter_map(|site| graph.inst(site.inst)?.inputs.get(site.input_idx).copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|value| {
            let uses = graph.use_sites(*value);
            !uses.is_empty() && uses.iter().all(|site| sites.contains(site))
        })
        .collect()
}

/// Values whose complete use domain belongs to an exact upstream frame
/// save/reload certificate. The certificate collector already proved the
/// closure; this is only its renderer-facing projection.
pub(super) fn certified_stack_frame_values(source: &r2ssa::SsaArtifact) -> BTreeSet<ValueId> {
    source
        .certificates()
        .stack_frame_round_trips
        .values()
        .flat_map(|certificate| certificate.values.iter().copied())
        .collect()
}

pub(super) fn certified_stack_geometry_values(source: &r2ssa::SsaArtifact) -> &BTreeSet<ValueId> {
    &source.certificates().stack_geometry.values
}

/// Failure of declaration placement or reaching-definition validation.
///
/// Placement itself is deliberately absent: it is derived from the sealed
/// structured-region artifact immediately before AST emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum PlacementRead {
    Use(UseSite),
    CertifiedValue { value: ValueId, at: InstId },
    StackAccess(r2ssa::StructuredAccessId),
    PreservedCarrierWrite(InstId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementRefusal {
    NoDominatingRegion {
        binding: BindingId,
    },
    MissingDefinition {
        binding: BindingId,
    },
    ReadBeforeAssignment {
        binding: BindingId,
        read: PlacementRead,
    },
    UnprovableExecutionOrder {
        binding: BindingId,
    },
}

/// Typed disposition of an addressable stack object. Stack objects do not have
/// SSA-value membership, so they occupy their own plan domain instead of being
/// reconstructed from an offset or a rendered local name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StackObjectDisposition {
    Bound {
        binding: BindingId,
    },
    Elided {
        reason: r2ssa::ledger::ElisionReason,
    },
    Refused {
        reason: StackObjectRefusal,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StackObjectRefusal {
    MissingSourceIdentity {
        object: r2ssa::ObjectId,
    },
    UnclassifiedSourceRole {
        object: r2ssa::ObjectId,
    },
    MissingWidth {
        object: r2ssa::ObjectId,
    },
    InvalidWidth {
        object: r2ssa::ObjectId,
        size_bytes: u32,
    },
    ParameterHomeUnavailable {
        object: r2ssa::ObjectId,
        parameter_index: u32,
    },
    ParameterHomeWidthMismatch {
        object: r2ssa::ObjectId,
        parameter_index: u32,
        slot_width_bits: u32,
        parameter_width_bits: u32,
    },
}

/// Exact disposition of one source-certified ABI parameter slot.
///
/// The width is the formal carrier width in bits. It is kept separate from a
/// reused binding's machine-carrier declaration width because an exact use may
/// project a narrow formal from a wider canonical register carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParameterDisposition {
    Bound { binding: BindingId, width_bits: u32 },
    Refused { reason: ParameterRefusal },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParameterRefusal {
    MissingWidth {
        entity: SemanticId,
        slot: u32,
    },
    InvalidWidth {
        entity: SemanticId,
        slot: u32,
        size_bytes: u32,
    },
    UnsupportedWidth {
        entity: SemanticId,
        slot: u32,
        width_bits: u32,
    },
    ConflictingSlotOwnership {
        slot: u32,
        first: SemanticId,
        second: SemanticId,
    },
    ConflictingEntityOwnership {
        entity: SemanticId,
        expected_slot: u32,
        claimed_slot: u32,
    },
    MissingValueBinding {
        entity: SemanticId,
        slot: u32,
        value: ValueId,
    },
    ConflictingBindingOwnership {
        binding: BindingId,
        first_slot: u32,
        second_slot: u32,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BindingPlanSourceMismatch {
    Authority,
    MachineProjection(r2ssa::MachineBuildError),
    ValueTopology {
        index: usize,
        value: ValueId,
    },
    DispositionCount {
        expected: usize,
        actual: usize,
    },
    BindingCount {
        expected: usize,
        actual: usize,
    },
    InvalidBindingReference {
        value: ValueId,
        binding: BindingId,
    },
    CertificateMembership {
        binding: BindingId,
    },
    DeclarationWidth {
        binding: BindingId,
    },
    InvalidLiteralInline {
        value: ValueId,
    },
    InvalidElisionProof {
        value: ValueId,
    },
    UnexpectedValueDisposition {
        value: ValueId,
    },
    StackObjectCount {
        expected: usize,
        actual: usize,
    },
    UnexpectedStackObjectDisposition {
        object: r2ssa::ObjectId,
    },
    StackObjectCertificate {
        object: r2ssa::ObjectId,
        binding: BindingId,
    },
    StackObjectDeclarationWidth {
        object: r2ssa::ObjectId,
        binding: BindingId,
    },
    ParameterCount {
        expected: usize,
        actual: usize,
    },
    UnexpectedParameterDisposition {
        slot: u32,
    },
    ParameterCertificate {
        slot: u32,
        binding: BindingId,
    },
    ParameterDeclarationWidth {
        slot: u32,
        binding: BindingId,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BindingPlanBuildError {
    MachineProjection(r2ssa::MachineBuildError),
    MissingStorageSpan { value: ValueId },
    InvalidValueWidth { value: ValueId, size_bytes: u32 },
    TooManyBindings { count: usize },
    InvalidCertifiedEntityValue { entity: SemanticId, value: ValueId },
    Seal(BindingPlanSourceMismatch),
}

#[derive(Debug)]
struct BindingComponent {
    members: BTreeSet<ValueId>,
    sources: BTreeSet<BindingCertificateSource>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BindingWidth {
    Exact(u32),
    Refused(ValueRefusal),
}

#[derive(Debug)]
struct SealBindingComponent {
    members: BTreeSet<ValueId>,
    sources: BTreeSet<BindingCertificateSource>,
}

#[derive(Debug)]
enum SealWidthEvidence {
    Exact { lower_bounds: Vec<u32> },
    Refused(ValueRefusal),
}

/// Dense identity of one component resolved directly from upstream storage and
/// semantic certificates by the independent sealing oracle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct CanonicalComponentId(u32);

impl CanonicalComponentId {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Canonical value answer recomputed for diagnostics without consulting the
/// candidate plan's stored disposition or binding membership.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UpstreamValueDisposition {
    Bound { component: CanonicalComponentId },
    InlineConstant,
    Elided(r2ssa::ledger::ElisionReason),
    Refused(ValueRefusal),
}

/// Transient Stage 4 validation oracle.
///
/// This is deliberately rebuilt from the exact source and is never retained by
/// a [`BindingPlan`] or consumed by lowering. Machine facts remain owned by the
/// source-backed [`MachineProjection`]; component membership is resolved by the
/// sealing module's independent certificate walk.
#[derive(Debug)]
pub(crate) struct UpstreamShadowOracle {
    machine_projection: MachineProjection,
    components: Box<[Box<[ValueId]>]>,
    values: Box<[UpstreamValueDisposition]>,
}

impl UpstreamShadowOracle {
    pub(crate) fn component(&self, id: CanonicalComponentId) -> Option<&[ValueId]> {
        self.components.get(id.index()).map(Box::as_ref)
    }

    pub(crate) fn value_disposition(&self, value: ValueId) -> Option<UpstreamValueDisposition> {
        self.values.get(value.0 as usize).copied()
    }

    pub(crate) fn use_disposition(&self, site: UseSite) -> Option<&MachineUseDisposition> {
        self.machine_projection.use_disposition(site)
    }

    pub(crate) fn write_disposition(&self, inst: InstId) -> Option<&MachineWriteDisposition> {
        self.machine_projection.write_disposition(inst)
    }
}

/// Complete renderer-side projection of one exact source-owned SSA artifact.
///
/// Dense vectors make value and binding lookup O(1). Exact/refused use and
/// write lookup delegates to the plan-owned [`MachineProjection`] in O(1), so
/// the source geometry has one owner. Observable-effect outcomes are absent:
/// they are only knowable after rendering and ledger reconciliation.
#[derive(Debug, Clone)]
pub(crate) struct BindingPlan {
    authority: SsaArtifactAuthority,
    machine_projection: MachineProjection,
    bindings: Box<[Binding]>,
    dispositions: Box<[ValueDisposition]>,
    parameters: Box<[Option<ParameterDisposition>]>,
    stack_objects: BTreeMap<r2ssa::ObjectId, StackObjectDisposition>,
}

mod construction;
mod name_resolution;
mod seal;

pub(crate) use name_resolution::{
    BindingNameResolution, BindingNameResolutionError, PlannedParameterSymbol, PlannedStackSymbol,
    PlannedValueSymbol, RenderedIdentityRefusal,
};
pub(crate) use seal::build_upstream_shadow_oracle;

#[cfg(test)]
use construction::binding_components;
#[cfg(test)]
use seal::seal_binding_components;
impl BindingPlan {
    pub(crate) const fn machine_projection(&self) -> &MachineProjection {
        &self.machine_projection
    }

    pub(crate) fn binding(&self, id: BindingId) -> Option<&Binding> {
        self.bindings.get(id.index())
    }

    /// Number of sealed bindings in the dense `BindingId` domain.
    pub(crate) const fn binding_count(&self) -> usize {
        self.bindings.len()
    }

    /// Iterate sealed bindings in ascending, deterministic `BindingId` order.
    pub(crate) fn bindings(&self) -> impl ExactSizeIterator<Item = (BindingId, &Binding)> {
        self.bindings.iter().enumerate().map(|(index, binding)| {
            let id = u32::try_from(index)
                .map(BindingId)
                .expect("sealed binding count fits the BindingId domain");
            (id, binding)
        })
    }

    pub(crate) fn disposition(&self, value: ValueId) -> Option<&ValueDisposition> {
        self.dispositions.get(value.0 as usize)
    }

    /// Resolve one exact ABI slot in O(1). The table is dense-indexed but may
    /// contain empty cells when the certified slot domain is sparse.
    pub(crate) fn parameter_disposition(&self, slot: u32) -> Option<ParameterDisposition> {
        self.parameters.get(slot as usize).copied().flatten()
    }

    pub(crate) fn binding_role(&self, binding: BindingId) -> Option<BindingRole> {
        let binding = self.binding(binding)?;
        let mut roles = binding.certificate.sources.iter().filter_map(|source| {
            let BindingCertificateSource::CertifiedEntity(entity) = source else {
                return None;
            };
            match *entity {
                SemanticId::Parameter(slot) => Some(BindingRole::Parameter { slot }),
                SemanticId::StackSlot(object) => Some(BindingRole::StackObject { object }),
                _ => None,
            }
        });
        // A certified entity is the stronger claim and decides on its own. An
        // argument slot is a caller-supplied value too, so the entity role has
        // to be consulted first or every parameter would answer `EntryValue`.
        let Some(role) = roles.next() else {
            return Some(if binding.caller_supplied {
                BindingRole::EntryValue
            } else {
                BindingRole::Local
            });
        };
        roles.all(|other| other == role).then_some(role)
    }

    /// Whether the function signature declares this object, so the body must
    /// not declare it again.
    pub(crate) fn binding_is_externally_declared(&self, binding: BindingId) -> Option<bool> {
        self.binding_role(binding)
            .map(|role| matches!(role, BindingRole::Parameter { .. }))
    }

    /// Whether the caller supplies this object's value without the signature
    /// naming it.
    ///
    /// The body still declares it, because no parameter does, but it holds a
    /// value on entry and therefore cannot be required to be assigned before
    /// its first read.
    pub(crate) fn binding_is_entry_declared(&self, binding: BindingId) -> Option<bool> {
        self.binding_role(binding)
            .map(|role| matches!(role, BindingRole::EntryValue))
    }

    pub(crate) fn stack_object_disposition(
        &self,
        object: r2ssa::ObjectId,
    ) -> Option<StackObjectDisposition> {
        self.stack_objects.get(&object).copied()
    }

    pub(crate) fn use_disposition(&self, site: UseSite) -> Option<&r2ssa::MachineUseDisposition> {
        self.machine_projection.use_disposition(site)
    }

    pub(crate) fn write_disposition(
        &self,
        inst: InstId,
    ) -> Option<&r2ssa::MachineWriteDisposition> {
        self.machine_projection.write_disposition(inst)
    }

    /// Validate the two upstream identities that must agree before any target
    /// module may pair this plan with source-owned facts.
    pub(crate) fn validate_source(
        &self,
        source: &r2ssa::SsaArtifact,
    ) -> Result<(), BindingPlanSourceMismatch> {
        if self.authority != *source.authority() {
            return Err(BindingPlanSourceMismatch::Authority);
        }
        self.machine_projection
            .validate_against(source)
            .map_err(BindingPlanSourceMismatch::MachineProjection)?;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn replace_value_disposition_for_shadow_test(
        &mut self,
        value: ValueId,
        disposition: ValueDisposition,
    ) {
        self.dispositions[value.0 as usize] = disposition;
    }
}

#[cfg(test)]
mod tests;
