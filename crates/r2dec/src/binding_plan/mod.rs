//! Typed boundary between canonical SSA facts and C lowering.
//!
//! Stage 4 constructs this plan in shadow mode but does not consume it while
//! rendering. Use and write geometry remain owned by the validated upstream
//! [`MachineProjection`]; this module delegates to that table instead of
//! copying a second answer into renderer-owned storage.

#![allow(
    dead_code,
    reason = "Stage 4 shadow plan is sealed before the Stage 5 render cutover"
)]

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

/// One rendered C object. The name hint is presentation only, never identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Binding {
    declaration_type: CType,
    certificate: BindingCertificate,
    presentation_name_hint: Option<String>,
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

/// Proof that a value has no surviving read or observable effect.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeadValueProof {
    authority: SsaArtifactAuthority,
    value: ValueId,
}

/// Typed reason that a value cannot be represented honestly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ValueRefusal {
    MissingBindingCertificate { value: ValueId },
    MissingLiteralProjection { value: ValueId },
    MissingUseProjection { site: UseSite },
    IncoherentUseProjection { site: UseSite },
    IncoherentWriteProjection { value: ValueId },
    UnsupportedMachineExpression { value: ValueId },
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
        proof: DeadValueProof,
    },
    Refused {
        reason: ValueRefusal,
    },
}

/// Failure of declaration placement or reaching-definition validation.
///
/// Placement itself is deliberately absent: it is derived from the sealed
/// structured-region artifact immediately before AST emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementRefusal {
    NoDominatingRegion { binding: BindingId },
    MissingDefinition { binding: BindingId },
    ReadBeforeAssignment { binding: BindingId, site: UseSite },
}

/// Typed disposition of an addressable stack object. Stack objects do not have
/// SSA-value membership, so they occupy their own plan domain instead of being
/// reconstructed from an offset or a rendered local name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StackObjectDisposition {
    Bound { binding: BindingId },
    Refused { reason: StackObjectRefusal },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StackObjectRefusal {
    MissingWidth {
        object: r2ssa::ObjectId,
    },
    InvalidWidth {
        object: r2ssa::ObjectId,
        size_bytes: u32,
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
    NonBoundValue {
        value: ValueId,
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
    stack_objects: BTreeMap<r2ssa::ObjectId, StackObjectDisposition>,
}

mod construction;
mod name_resolution;
mod seal;

pub(crate) use name_resolution::{
    BindingNameResolution, BindingNameResolutionError, PlannedValueSymbol,
};
pub(crate) use seal::build_upstream_shadow_oracle;

#[cfg(test)]
use construction::binding_components;
#[cfg(test)]
use seal::seal_binding_components;
impl BindingPlan {
    pub(crate) const fn authority(&self) -> &SsaArtifactAuthority {
        &self.authority
    }

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
