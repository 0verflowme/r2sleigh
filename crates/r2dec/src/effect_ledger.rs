//! Close the source-effect ledger from the final emission tree.
//!
//! Rendering occurrence identity is owned by `observation_journal`.  This
//! module deliberately sees no fold cache, constructed-expression proof, or
//! block-visited side table: an obligation is rendered exactly when one marker
//! for that exact source cell survived emission preparation.

use crate::normalize::NormalizationOrigins;
use crate::observation_journal::SurvivingEffectObservations;
use r2ssa::ledger::{ElisionReason, LedgerLayer, ObligationLedger, Outcome, RefusalReason};
use r2ssa::{
    CanonicalInstructionSite, SemanticObligationComponent, SemanticObligationId,
    SemanticObligationKind, SsaArtifact,
};

fn rendered_site(id: SemanticObligationId) -> Option<(u64, usize)> {
    match id.instruction.site {
        CanonicalInstructionSite::Phi(_) => Some((id.instruction.block_addr, 0)),
        CanonicalInstructionSite::Op(op_idx) => usize::try_from(op_idx)
            .ok()
            .map(|op_idx| (id.instruction.block_addr, op_idx)),
        CanonicalInstructionSite::NativeSpan { .. } => None,
    }
}

/// Exact upstream disposition for a source effect that has no final occurrence.
///
/// These are not renderer guesses. Unsupported native effects are inventory
/// policy, unobserved merges are canonical SSA facts, and redundant phi edges
/// are certified by the sealed normalization sidecar. Every other zero is a
/// typed codegen refusal so deletion cannot be relabelled as successful elision.
fn upstream_zero_occurrence_outcome(
    prepared: &SsaArtifact,
    origins: &NormalizationOrigins,
    id: SemanticObligationId,
) -> Outcome {
    if matches!(
        id.kind,
        SemanticObligationKind::VolatileOrUnknownEffect | SemanticObligationKind::Trap
    ) {
        return Outcome::Refused {
            layer: LedgerLayer::Ssa,
            reason: RefusalReason::UnsupportedEffect,
        };
    }

    let graph = prepared.graph();
    let source_inst = prepared
        .obligations()
        .instructions()
        .get(&id.instruction)
        .and_then(|disposition| disposition.source.graph_inst());
    if matches!(id.instruction.site, CanonicalInstructionSite::Phi(_))
        && source_inst
            .and_then(|inst| graph.inst(inst))
            .and_then(|inst| inst.output)
            .is_some_and(|value| prepared.unobserved_merges().contains(value))
    {
        return Outcome::Elided(ElisionReason::UnobservedMerge);
    }

    if let Some(inst) = source_inst
        && let Some(removed) = origins
            .removed_phis()
            .iter()
            .find(|removed| removed.definition.inst == inst)
    {
        match (id.kind, id.component) {
            (
                SemanticObligationKind::LiveStateTransition,
                SemanticObligationComponent::LoopTransition { .. },
            ) if prepared
                .obligations()
                .obligations()
                .get(&id)
                .and_then(|obligation| obligation.edge_use)
                .is_some_and(|site| removed.noop_sites().contains(&site)) =>
            {
                return Outcome::Elided(ElisionReason::RedundantPhiEdge);
            }
            (SemanticObligationKind::LoopCarriedState, _)
                if removed
                    .incoming_sites
                    .iter()
                    .all(|site| removed.noop_sites().contains(site)) =>
            {
                return Outcome::Elided(ElisionReason::RedundantPhiEdge);
            }
            _ => {}
        }
    }

    Outcome::Refused {
        layer: LedgerLayer::Codegen,
        reason: RefusalReason::BlockNotRendered,
    }
}

/// Build one closed-domain ledger from exact surviving occurrence counts.
pub(crate) fn build_obligation_ledger(
    prepared: &SsaArtifact,
    origins: &NormalizationOrigins,
    effects: &SurvivingEffectObservations,
) -> ObligationLedger {
    let obligations = prepared.obligations();
    let mut ledger = ObligationLedger::open(obligations);
    for id in obligations.obligations().keys().copied() {
        let count = effects
            .occurrence_count(id)
            .expect("effect observation domain is opened from this source inventory");
        let outcome = match count {
            0 => Some(upstream_zero_occurrence_outcome(prepared, origins, id)),
            1 => rendered_site(id)
                .map(|(block_addr, op_idx)| Outcome::Rendered { block_addr, op_idx }),
            _ => Some(Outcome::Refused {
                layer: LedgerLayer::Codegen,
                reason: RefusalReason::DuplicateRenderedOccurrence,
            }),
        };
        if let Some(outcome) = outcome {
            let _ = ledger.record(id, outcome);
        }
    }
    ledger
}
