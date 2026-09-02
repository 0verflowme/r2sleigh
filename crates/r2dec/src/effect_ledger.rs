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

/// The zero-occurrence disposition, with an eye on the ones that must not be
/// elided.
///
/// A call is an observable effect. Eliding one drops it from the rendering with
/// no trace, which is how fourteen of twenty-six calls in a `-O0` binary went
/// missing under a proof line reading `0 refused`. Every elision of a call or
/// of one of its arguments says so under `R2DEC_TRACE_REFUSAL`, so the reason
/// that took it is named rather than hunted.
fn traced_zero_occurrence_outcome(
    prepared: &SsaArtifact,
    origins: &NormalizationOrigins,
    effects: &SurvivingEffectObservations,
    id: SemanticObligationId,
) -> Outcome {
    let outcome = upstream_zero_occurrence_outcome(prepared, origins, effects, id);
    if matches!(
        id.kind,
        SemanticObligationKind::Call
            | SemanticObligationKind::CallArgument
            | SemanticObligationKind::CallResult
    ) && let Outcome::Elided(reason) = outcome
    {
        r2il::refusal_evidence!(
            "call-elided",
            "a call effect was elided rather than rendered: kind={:?} reason={reason:?} \
             block={:#x} site={:?}",
            id.kind,
            id.instruction.block_addr,
            id.instruction.site
        );
    }
    outcome
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
    effects: &SurvivingEffectObservations,
    id: SemanticObligationId,
) -> Outcome {
    // The instruction does nothing, so there is nothing to render for it and
    // nothing left unaccounted when the rendering omits it.
    if id.kind == SemanticObligationKind::NoNativeSemantics {
        return Outcome::Elided(ElisionReason::NoNativeSemantics);
    }

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
    if source_inst.is_some_and(|inst| {
        prepared
            .certificates()
            .stack_frame_round_trip_by_inst
            .contains_key(&inst)
    }) {
        return Outcome::Elided(ElisionReason::StackFrame);
    }
    if source_inst.is_some_and(|inst| {
        prepared
            .certificates()
            .machine_return_control_by_inst
            .contains_key(&inst)
    }) {
        return Outcome::Elided(ElisionReason::ReturnControl);
    }
    // The copies a return address reaches its return through. AArch64's `ret`
    // is a copy of the link register into the program counter followed by a
    // return on that, and the copy carries an obligation of its own that no
    // statement answers, because the structured form says `return`.
    if source_inst.is_some_and(|inst| {
        crate::binding_plan::certified_return_control_insts(prepared).contains(&inst)
    }) {
        return Outcome::Elided(ElisionReason::ReturnControl);
    }
    // A store into a frame slot this function owns and never reads. The
    // obligation is real -- writing memory is an effect -- and it is answered
    // by the certificate that nothing can observe the result.
    if id.kind == SemanticObligationKind::ObservableMemoryWrite
        && let CanonicalInstructionSite::Op(op_index) = id.instruction.site
        && let Ok(op_index) = usize::try_from(op_index)
        && crate::binding_plan::certified_dead_frame_slot_accesses(prepared)
            .contains(&(id.instruction.block_addr, op_index))
    {
        return Outcome::Elided(ElisionReason::DeadFrameSlotStore);
    }
    // The push that records a call's return address. The call statement is the
    // transfer, and no C statement writes the machine's return address.
    if source_inst.is_some_and(|inst| {
        crate::binding_plan::certified_call_return_address_insts(prepared).contains(&inst)
    }) {
        return Outcome::Elided(ElisionReason::CallReturnAddress);
    }
    // The copies a callee's address reaches its call through. The call spells
    // the callee's name, so no statement answers for the copy that put the
    // address in a temporary first.
    if source_inst.is_some_and(|inst| {
        crate::binding_plan::certified_direct_call_target_insts(prepared).contains(&inst)
    }) {
        return Outcome::Elided(ElisionReason::DirectCallTarget);
    }
    if source_inst.is_some_and(|inst| prepared.certificates().stack_geometry.insts.contains(&inst))
    {
        return Outcome::Elided(ElisionReason::DeadStackBase);
    }
    if matches!(id.instruction.site, CanonicalInstructionSite::Phi(_))
        && source_inst
            .and_then(|inst| graph.inst(inst))
            .and_then(|inst| inst.output)
            .is_some_and(|value| prepared.unobserved_merges().contains(value))
    {
        return Outcome::Elided(ElisionReason::UnobservedMerge);
    }

    if let Some(inst) = source_inst
        && effects.is_coalesced_carrier_phi(inst)
        && matches!(
            id.kind,
            SemanticObligationKind::LoopCarriedState | SemanticObligationKind::LiveValueProducer
        )
    {
        return Outcome::Elided(ElisionReason::CoalescedIdentityPhi);
    }
    if id.kind == SemanticObligationKind::LiveStateTransition
        && prepared
            .obligations()
            .obligations()
            .get(&id)
            .and_then(|obligation| obligation.edge_use)
            .is_some_and(|site| effects.is_coalesced_carrier_use(site))
    {
        return Outcome::Elided(ElisionReason::CoalescedEdgeCopy);
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
            // Every input the merge had is written by a copy on its own
            // incoming edge, so the state it carried is carried by those
            // copies. Refusing here reported the merge as unrendered when what
            // it stood for is rendered, just as several assignments rather than
            // one merge.
            (
                SemanticObligationKind::LoopCarriedState
                | SemanticObligationKind::LiveValueProducer,
                _,
            ) if {
                let materialized = origins.materialized_phi_edges(inst);
                removed
                    .incoming_sites
                    .iter()
                    .all(|site| removed.noop_sites().contains(site) || materialized.contains(site))
            } =>
            {
                return Outcome::Elided(ElisionReason::MaterializedPhiEdges);
            }
            _ => {}
        }
    }

    // An unconditional branch is a transfer the structured form expresses by
    // where the block sits, not by a statement of its own. AArch64 at -O0 emits
    // one wherever x86 would fall through, so six functions were refused for a
    // transfer that is rendered -- as the ordering of the regions around it.
    //
    // Only the unconditional case. A conditional transfer has to render as an
    // `if`, and if no statement owns it then it genuinely did not render.
    if id.kind == SemanticObligationKind::ControlTransfer
        && source_inst
            .and_then(|inst| graph.inst(inst))
            .is_some_and(|inst| match &inst.payload {
                // Only a branch to one of this function's own blocks. The
                // elision says the structured form expresses the transfer by
                // where the target sits, and that is a claim about a block the
                // structured form places. A branch that leaves the function --
                // `b sym.imp.strcoll` ending a comparator, the ordinary shape
                // of a tail call -- has no such block, so nothing expresses it
                // and eliding it dropped the transfer with no trace: the
                // arguments it set up were dead once the call was gone, dead
                // store elimination took them, and a comparator rendered
                // without its fallback comparison at all, under a proof line
                // reading `0 refused`.
                r2ssa::InstPayload::Op(r2ssa::SSAOp::Branch { .. }) => graph
                    .block(inst.block)
                    .and_then(|block| prepared.function().cfg().get_block(block.addr))
                    .is_some_and(|block| match block.terminator {
                        r2ssa::cfg::BlockTerminator::Branch { target } => {
                            prepared.function().get_block(target).is_some()
                        }
                        _ => false,
                    }),
                // A certified jump table transfers by which case block the
                // structured form put the code in, exactly as an unconditional
                // branch transfers by where its block sits.
                r2ssa::InstPayload::Op(r2ssa::SSAOp::BranchInd { .. }) => {
                    graph.block(inst.block).is_some_and(|block| {
                        prepared.certificates().switches.contains_key(&block.addr)
                    })
                }
                _ => false,
            })
    {
        return Outcome::Elided(ElisionReason::DirectControlTarget);
    }

    r2il::refusal_evidence!(
        "zero-occurrence-outcome",
        "kind={:?} component={:?} block={:#x} source_inst={source_inst:?} inputs={:?}",
        id.kind,
        id.instruction.site,
        id.instruction.block_addr,
        prepared
            .obligations()
            .obligations()
            .get(&id)
            .map(|obligation| obligation.inputs.clone())
    );
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
            0 => Some(traced_zero_occurrence_outcome(
                prepared, origins, effects, id,
            )),
            1 => rendered_site(id)
                .map(|(block_addr, op_idx)| Outcome::Rendered { block_addr, op_idx }),
            // Several occurrences are one execution when the structured form
            // put them on paths that exclude one another -- a shared tail
            // emitted once per path that reaches it rather than jumped to.
            // Anything else rendered twice is a duplicate, which changes what
            // the program does and is scored as a refusal.
            _ if effects.duplicates_are_exclusive(id) => rendered_site(id)
                .map(|(block_addr, op_idx)| Outcome::Rendered { block_addr, op_idx }),
            // And several occurrences are one execution when what was rendered
            // is a literal. The machine writes the temporary once; a reader
            // that spells the constant instead of naming it performs nothing,
            // so the count is how many times the value was spelled and not how
            // many times it was computed. Admitted only for a value that reads
            // nothing at all, because an expression repeated at three readers
            // would be three evaluations.
            _ if effects.duplicates_are_a_repeated_literal(id) => rendered_site(id)
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
