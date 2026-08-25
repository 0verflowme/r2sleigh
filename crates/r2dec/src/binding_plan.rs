//! Typed boundary between canonical SSA facts and C lowering.
//!
//! This module intentionally has no production constructor or render consumer
//! yet. Stage 4 will construct the plan in shadow mode; at that point remove
//! the module-level `dead_code` allowance rather than extending it.

#![allow(
    dead_code,
    reason = "Stage 1 scaffold; remove when Stage 4 constructs BindingPlan in shadow mode"
)]

use std::collections::BTreeMap;

use crate::ast::CType;
use r2ssa::span::SpanId;
use r2ssa::{
    CanonicalInstructionId, InstId, MachineCastKind, MachineExprId, MachineProjection, SemanticId,
    SemanticObligationId, SsaArtifactAuthority, UseSite, ValueId,
};

/// Dense identity of one C object in a [`BindingPlan`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct BindingId(u32);

impl BindingId {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Opaque token minted only by this module's future sealing pass after it has
/// checked the exact bound member set against one upstream source fact. It
/// never repeats a machine location or stores a parallel member list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BindingCertificate {
    source: BindingCertificateSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    producer: CanonicalInstructionId,
}

/// Proof that a value has no surviving read or observable effect.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeadValueProof {
    authority: SsaArtifactAuthority,
    obligation: SemanticObligationId,
}

/// Typed reason that a value cannot be represented honestly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ValueRefusal {
    MissingBindingCertificate { value: ValueId },
    MissingUseProjection { site: UseSite },
    UnsupportedMachineExpression { value: ValueId },
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

/// Conversion applied after selecting the exact bit slice consumed by a use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProjectionConversion {
    Identity,
    Cast {
        kind: MachineCastKind,
        to_width_bits: u32,
    },
}

/// Deliberately uninhabited until Stage 2 supplies the dedicated upstream
/// slice certificate. An artifact identity plus a semantic expression does not
/// prove which bits a particular use reads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum UseProjectionProof {}

/// The exact slice consumed by one canonical SSA use.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UseProjection {
    bit_offset: u32,
    width_bits: u32,
    conversion: ProjectionConversion,
    proof: UseProjectionProof,
}

impl UseProjection {
    pub(crate) const fn bit_offset(&self) -> u32 {
        self.bit_offset
    }

    pub(crate) const fn width_bits(&self) -> u32 {
        self.width_bits
    }

    pub(crate) const fn conversion(&self) -> ProjectionConversion {
        self.conversion
    }
}

/// The exact slice one SSA definition writes back to its certified binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum WriteProjection {
    Full {
        proof: WriteProjectionProof,
    },
    Insert {
        bit_offset: u32,
        width_bits: u32,
        proof: WriteProjectionProof,
    },
    ZeroExtend {
        from_width_bits: u32,
        to_width_bits: u32,
        proof: WriteProjectionProof,
    },
}

/// Deliberately uninhabited until Stage 2 supplies a definition-site write
/// certificate. A read-slice certificate cannot authorize a write.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum WriteProjectionProof {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EffectProof {
    authority: SsaArtifactAuthority,
    producer: CanonicalInstructionId,
}

/// The one and only disposition of an observable semantic obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EffectDisposition {
    Rendered {
        proof: EffectProof,
    },
    Elided {
        reason: r2ssa::ledger::ElisionReason,
        proof: EffectProof,
    },
    Refused {
        reason: r2ssa::ledger::RefusalReason,
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

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BindingPlanSourceMismatch {
    Authority,
    MachineProjection(r2ssa::MachineBuildError),
}

/// Complete renderer-side projection of one exact source-owned SSA artifact.
///
/// Dense vectors make value, definition, binding, and use lookup O(1). Effects
/// are keyed by stable semantic obligation identity and cost O(log n).
#[derive(Debug, Clone)]
pub(crate) struct BindingPlan {
    authority: SsaArtifactAuthority,
    machine_projection: MachineProjection,
    bindings: Box<[Binding]>,
    dispositions: Box<[ValueDisposition]>,
    uses: Box<[Box<[UseProjection]>]>,
    writes: Box<[Option<WriteProjection>]>,
    effects: BTreeMap<SemanticObligationId, EffectDisposition>,
}

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

    pub(crate) fn disposition(&self, value: ValueId) -> Option<&ValueDisposition> {
        self.dispositions.get(value.0 as usize)
    }

    pub(crate) fn use_projection(&self, site: UseSite) -> Option<&UseProjection> {
        self.uses.get(site.inst.0 as usize)?.get(site.input_idx)
    }

    pub(crate) fn write_projection(&self, inst: InstId) -> Option<&WriteProjection> {
        self.writes.get(inst.0 as usize)?.as_ref()
    }

    pub(crate) fn effect(&self, obligation: SemanticObligationId) -> Option<&EffectDisposition> {
        self.effects.get(&obligation)
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
            .map_err(BindingPlanSourceMismatch::MachineProjection)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{R2ILBlock, R2ILOp, Varnode};
    use r2ssa::SsaArtifact;

    fn source_and_projection() -> (SsaArtifact, MachineProjection, ValueId) {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        let source = SsaArtifact::raw(&[block], None).expect("test SSA artifact");
        let projection = MachineProjection::from_artifact(&source).expect("machine projection");
        let entity = projection.entities().first().expect("projected copy");
        (source, projection.clone(), entity.output().value())
    }

    fn plan_with(
        authority: SsaArtifactAuthority,
        machine_projection: MachineProjection,
        bindings: Vec<Binding>,
        dispositions: Vec<ValueDisposition>,
        uses: Vec<Vec<UseProjection>>,
    ) -> BindingPlan {
        BindingPlan {
            authority,
            machine_projection,
            bindings: bindings.into_boxed_slice(),
            dispositions: dispositions.into_boxed_slice(),
            uses: uses
                .into_iter()
                .map(Vec::into_boxed_slice)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            writes: Box::new([]),
            effects: BTreeMap::new(),
        }
    }

    #[test]
    fn dense_plan_accessors_do_not_store_location_or_placement() {
        let (source, projection, value) = source_and_projection();
        let mut dispositions = vec![
            ValueDisposition::Refused {
                reason: ValueRefusal::MissingBindingCertificate { value },
            };
            source.graph().values.len()
        ];
        dispositions[value.0 as usize] = ValueDisposition::Bound {
            binding: BindingId(0),
        };
        let plan = plan_with(
            source.authority().clone(),
            projection,
            vec![Binding {
                declaration_type: CType::u32(),
                certificate: BindingCertificate {
                    source: BindingCertificateSource::Singleton,
                },
                presentation_name_hint: Some("first".into()),
            }],
            dispositions,
            Vec::new(),
        );

        let binding = plan.binding(BindingId(0)).expect("dense binding");
        assert_eq!(binding.declaration_type(), &CType::u32());
        assert_eq!(
            binding.certificate.source,
            BindingCertificateSource::Singleton
        );
        assert_eq!(binding.presentation_name_hint(), Some("first"));
        assert!(plan.binding(BindingId(1)).is_none());
        assert!(matches!(
            plan.disposition(value),
            Some(ValueDisposition::Bound {
                binding: BindingId(0)
            })
        ));
        assert_eq!(plan.authority(), source.authority());
        assert_eq!(plan.machine_projection().entities().len(), 1);
        assert_eq!(plan.validate_source(&source), Ok(()));
        let (independent, _, _) = source_and_projection();
        assert_eq!(
            plan.validate_source(&independent),
            Err(BindingPlanSourceMismatch::Authority)
        );
        assert!(
            plan.use_projection(UseSite {
                inst: InstId(0),
                input_idx: 1
            })
            .is_none()
        );
    }
}
