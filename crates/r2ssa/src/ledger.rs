//! What became of every obligation the source inventory recorded.
//!
//! The inventory says what a function owes. Rendering discharges some of it,
//! proves some of it needs no output, and fails at the rest. Until now those
//! three answers were counted by walking the inventory at the end and asking
//! whether anything had been proven about each entry, which meant an obligation
//! nothing had an opinion about simply did not appear in any total: a body could
//! report "34 of 43 owned, 0 unsupported" with nine effects missing and no word
//! for them.
//!
//! A ledger cannot lose one. It opens holding every obligation the inventory
//! recorded, each undecided, and the only way an entry leaves that state is for
//! a layer to say what happened to it. Closing the ledger reports all four
//! counts and they sum to the total by construction, so the gap that used to be
//! silent is now a number with a name on it.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::obligation::{
    SemanticObligationId, SemanticObligationInventory, SemanticObligationKind,
};

/// Which layer decided an obligation's fate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum LedgerLayer {
    Ssa,
    Types,
    Structure,
    Fold,
    Codegen,
}

impl std::fmt::Display for LedgerLayer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Ssa => "ssa",
            Self::Types => "types",
            Self::Structure => "structure",
            Self::Fold => "fold",
            Self::Codegen => "codegen",
        })
    }
}

/// Why an obligation needed no output for the rendering to be complete.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ElisionReason {
    /// Frame setup and teardown the rendered function does not model.
    StackFrame,
    /// The exact machine control target consumed by a source-certified return.
    ///
    /// This is not the program value returned by the function. The lifted
    /// `Return` operand transports the return address, while source boundary
    /// facts separately certify any semantic return value.
    ReturnControl,
    /// A direct branch target already represented by the sealed CFG topology.
    ///
    /// The target operand is machine control, not a C expression. Conditional
    /// predicates remain ordinary exact uses and are never covered by this
    /// disposition.
    DirectControlTarget,
    /// A direct call's target operand, which the call expression renders by
    /// naming the callee.
    ///
    /// The address of a called function is not an object the program holds. It
    /// is spelled once, in the call itself, so the operand's occurrences are
    /// ordinary rendered uses while the value they name denotes nothing the
    /// function could declare. An indirect call is not covered: there the
    /// target really is a value the program computed and reads.
    DirectCallTarget,
    /// The push that carries a call's return address.
    ///
    /// The structured form spells the call, and the transfer is the call. The
    /// stack write the machine performs to record where to come back to is
    /// bookkeeping the C has no statement for, in the same way a return's own
    /// transfer is.
    CallReturnAddress,
    /// A store into a frame slot this function owns and never reads.
    ///
    /// Writing memory is an effect, but observable means observable from
    /// outside. Where the object is certified to lie wholly inside storage this
    /// function allocated, and every access to it is a write, nothing can read
    /// what was stored and no C statement has to carry it.
    DeadFrameSlotStore,
    /// An immutable phi whose inputs and output are one certified renderer
    /// binding has no runtime C operation. Its graph cells remain accounted,
    /// but no assignment or read is fabricated for the SSA merge itself.
    CoalescedImmutablePhi,
    /// A copy whose source and destination are one renderer binding, whole.
    /// Whatever wrote that binding has already written it, so the copy would
    /// only spell `x = x`.
    ///
    /// The copies normalization makes for a merge are the common case -- one
    /// on each materialised edge, and the initializer relocated ahead of a
    /// certified carrier's entry edges -- and the program's own copies are
    /// the other: `subs x1, x1, #1` lifts to a subtraction into a temporary
    /// and a copy of the temporary into `x1`, and once a carrier certificate
    /// puts the two in one object the copy says nothing. A program copy
    /// keeps its statement where it does something the name does not, a
    /// narrowing write or a converting read.
    ///
    /// This was once restricted to a certified loop carrier's edges with a
    /// defined source, which is where the case was found rather than the
    /// reason it holds: what makes the copy say nothing is that both sides
    /// are one binding. A source nothing defines -- a parameter -- is
    /// rendered by the binding's declaration, not by the copy.
    CoalescedCopy,
    /// Every incoming edge of a merge is either an SSA identity or coalesced
    /// to the merge's own binding, so the merge needs no standalone C write.
    ///
    /// Its output is not elided with it. The value is still rendered, under
    /// the binding's name, by whatever wrote that binding.
    CoalescedIdentityPhi,
    /// A condition-code write no rendered predicate reads.
    DeadCpuFlag,
    /// A value only ever read to compute a flag that is itself elided.
    DeadFlagOnly,
    /// A lifted temporary or constant carrier nothing outside its definition reads.
    DeadUnusedTemporary,
    /// A caller-saved register write no callee-crossing read observes.
    DeadCallerSaved,
    /// A register write consumed entirely by a rendered call's argument list.
    DeadCallArgument,
    /// A native instruction the lifter decoded to no semantics at all.
    ///
    /// There is nothing for the rendering to emit because the instruction does
    /// nothing. A failed decode produces an `Unimplemented` operation instead,
    /// so this is a positive fact about the instruction and not a way of
    /// saying the effect is unknown.
    NoNativeSemantics,
    /// A bound object placement removed because nothing read it.
    ///
    /// Distinct from `DeadUnusedTemporary`, which names a lifted temporary with
    /// no reader outside its own definition. This is the outcome for an object
    /// that had readers when the decisions were derived and lost them when
    /// another dead object's statements went: the value still exists in the
    /// source, and a caller-supplied one has no defining instruction at all, so
    /// there is no write cell to answer for it. What the removed statements did
    /// besides producing the value is answered by the effect ledger.
    DeadUnreadBinding,
    /// A write to the stack base that frame handling accounts for instead.
    DeadStackBase,
    /// A merge no observation depends on, so nothing reads what it decides.
    UnobservedMerge,
    /// A pure value outside the complete transitive observation slice.
    UnobservedValue,
    /// A source-classified structural instruction produced a value with no
    /// graph use and owns no semantic obligation.
    UnusedStructuralValue,
    /// The content an object already held when the function started.
    ///
    /// A value with no defining instruction was put there by the caller, so no
    /// statement in this function assigns it and none can be expected to. Where
    /// something reads it the read is its occurrence and this does not apply;
    /// this accounts for the entry content nothing in the function observes,
    /// which is what a register the caller happened to leave behind looks like
    /// once the merges that carried it are found to be unobserved.
    CallerSuppliedEntryValue,
    /// A removed merge input already names the merge result, so its edge copy
    /// would be the identity assignment `x = x`.
    RedundantPhiEdge,
    /// Every input of a removed merge is written by a copy on its own incoming
    /// edge, so the state the merge carried is carried by those copies and the
    /// merge itself needs no standalone C operation.
    MaterializedPhiEdges,
    /// Proven dead, with no rule yet naming which kind of dead it is.
    DeadUnclassified,
}

impl std::fmt::Display for ElisionReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::StackFrame => "stack-frame",
            Self::ReturnControl => "return-control",
            Self::DirectControlTarget => "direct-control-target",
            Self::DirectCallTarget => "direct-call-target",
            Self::CallReturnAddress => "call-return-address",
            Self::DeadFrameSlotStore => "dead-frame-slot-store",
            Self::CoalescedImmutablePhi => "coalesced-immutable-phi",
            Self::CoalescedCopy => "coalesced-copy",
            Self::CoalescedIdentityPhi => "coalesced-identity-phi",
            Self::DeadCpuFlag => "dead-cpu-flag",
            Self::DeadFlagOnly => "dead-flag-only",
            Self::DeadUnusedTemporary => "dead-unused-temp",
            Self::DeadCallerSaved => "dead-caller-saved",
            Self::DeadCallArgument => "dead-call-arg",
            Self::NoNativeSemantics => "no-native-semantics",
            Self::DeadUnreadBinding => "dead-unread-binding",
            Self::DeadStackBase => "dead-stack-base",
            Self::UnobservedMerge => "unobserved-merge",
            Self::UnobservedValue => "unobserved-value",
            Self::UnusedStructuralValue => "unused-structural-value",
            Self::CallerSuppliedEntryValue => "caller-supplied-entry-value",
            Self::RedundantPhiEdge => "redundant-phi-edge",
            Self::MaterializedPhiEdges => "materialized-phi-edges",
            Self::DeadUnclassified => "dead-unclassified",
        })
    }
}

/// Why an obligation could not be discharged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RefusalReason {
    /// The admission rule asks this effect to residualize rather than be owned.
    UnsupportedEffect,
    /// Final emission retained no occurrence that owns this obligation.
    ///
    /// This deliberately does not guess which earlier phase removed it. The
    /// absence of an occurrence proves the coverage failure, but it does not
    /// prove that the containing block was omitted.
    NoRenderedOccurrence,
    /// The value this obligation needs was never bound to anything the output names.
    ValueUnbound,
    /// A phase ran out of its budget before reaching this obligation.
    BudgetExhausted,
    /// More than one final output occurrence claimed the same source effect.
    ///
    /// One source obligation is one semantic event. Rendering it twice is not
    /// successful coverage: it changes program behavior and must therefore be
    /// scored as a refusal at the final emission boundary.
    DuplicateRenderedOccurrence,
    /// The layer refused and the reason is not yet one this enum distinguishes.
    Unclassified,
}

impl std::fmt::Display for RefusalReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::UnsupportedEffect => "unsupported-effect",
            Self::NoRenderedOccurrence => "no-rendered-occurrence",
            Self::ValueUnbound => "value-unbound",
            Self::BudgetExhausted => "budget-exhausted",
            Self::DuplicateRenderedOccurrence => "duplicate-rendered-occurrence",
            Self::Unclassified => "unclassified",
        })
    }
}

/// What became of one obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Outcome {
    /// Discharged by output at this operation site.
    Rendered { block_addr: u64, op_idx: usize },
    /// Proven to need no output.
    Elided(ElisionReason),
    /// Could not be discharged, and which layer said so.
    Refused {
        layer: LedgerLayer,
        reason: RefusalReason,
    },
    /// No layer recorded a fate, which is a decompiler defect rather than a property of the input.
    Unattributed,
}

impl Outcome {
    /// Whether a layer has spoken about this obligation.
    pub fn is_decided(self) -> bool {
        !matches!(self, Self::Unattributed)
    }
}

/// What happened when a layer tried to record an outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Record {
    /// The obligation was undecided and now holds this outcome.
    Accepted,
    /// The obligation already held exactly this outcome.
    Redundant,
    /// The obligation already held a different outcome, which is kept.
    Conflict(Outcome),
    /// No such obligation exists in the inventory this ledger was opened over.
    Unknown,
}

/// How the ledger stands, with every obligation in exactly one column.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LedgerClosure {
    pub total: usize,
    pub rendered: usize,
    pub elided: usize,
    pub refused: usize,
    pub unattributed: usize,
    pub conflicts: usize,
}

impl LedgerClosure {
    /// Whether every obligation has an outcome and the columns account for the total.
    pub fn is_closed(&self) -> bool {
        self.unattributed == 0 && self.accounted() == self.total
    }

    /// How many obligations the four columns name between them.
    pub fn accounted(&self) -> usize {
        self.rendered + self.elided + self.refused + self.unattributed
    }
}

/// Every obligation the inventory recorded, and what became of it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObligationLedger {
    outcomes: BTreeMap<SemanticObligationId, Outcome>,
    conflicts: BTreeMap<SemanticObligationId, usize>,
}

impl ObligationLedger {
    /// Open a ledger over an inventory, with every obligation present and undecided.
    pub fn open(inventory: &SemanticObligationInventory) -> Self {
        Self {
            outcomes: inventory
                .obligations()
                .keys()
                .map(|id| (*id, Outcome::Unattributed))
                .collect(),
            conflicts: BTreeMap::new(),
        }
    }

    /// Say what became of one obligation, keeping the first answer if two disagree.
    pub fn record(&mut self, id: SemanticObligationId, outcome: Outcome) -> Record {
        let Some(slot) = self.outcomes.get_mut(&id) else {
            return Record::Unknown;
        };
        match *slot {
            Outcome::Unattributed => {
                *slot = outcome;
                Record::Accepted
            }
            existing if existing == outcome => Record::Redundant,
            existing => {
                *self.conflicts.entry(id).or_insert(0) += 1;
                Record::Conflict(existing)
            }
        }
    }

    /// Record that several incompatible occurrences answer one obligation.
    ///
    /// The obligation keeps its first outcome so the closure equation still
    /// has one owner for every source cell. The conflict is an independent
    /// admission failure, keyed by that same canonical source identity so a
    /// refusal can name where the incompatible answers occurred.
    pub fn record_conflict(&mut self, id: SemanticObligationId) -> Record {
        let Some(existing) = self.outcomes.get(&id).copied() else {
            return Record::Unknown;
        };
        *self.conflicts.entry(id).or_insert(0) += 1;
        Record::Conflict(existing)
    }

    /// Replace an outcome a later layer disproved, without counting it as a conflict.
    pub fn overwrite(&mut self, id: SemanticObligationId, outcome: Outcome) -> Record {
        match self.outcomes.get_mut(&id) {
            Some(slot) => {
                *slot = outcome;
                Record::Accepted
            }
            None => Record::Unknown,
        }
    }

    /// What became of one obligation, or `Unattributed` for anything this ledger does not hold.
    pub fn outcome(&self, id: &SemanticObligationId) -> Outcome {
        self.outcomes
            .get(id)
            .copied()
            .unwrap_or(Outcome::Unattributed)
    }

    /// Every obligation, in inventory order.
    pub fn entries(&self) -> impl Iterator<Item = (&SemanticObligationId, Outcome)> {
        self.outcomes.iter().map(|(id, outcome)| (id, *outcome))
    }

    /// The obligations no layer spoke about, which is the list of decompiler defects.
    pub fn unattributed(&self) -> impl Iterator<Item = &SemanticObligationId> {
        self.outcomes
            .iter()
            .filter(|(_, outcome)| !outcome.is_decided())
            .map(|(id, _)| id)
    }

    /// How many undecided obligations there are of each kind.
    pub fn unattributed_by_kind(&self) -> BTreeMap<SemanticObligationKind, usize> {
        let mut counts = BTreeMap::new();
        for id in self.unattributed() {
            *counts.entry(id.kind).or_insert(0usize) += 1;
        }
        counts
    }

    /// Obligations with incompatible answers, in canonical source order.
    pub fn conflicts(&self) -> impl Iterator<Item = (&SemanticObligationId, usize)> {
        self.conflicts.iter().map(|(id, count)| (id, *count))
    }

    /// How many refusals there are, by the layer that made them and why.
    pub fn refusals_by_layer(&self) -> BTreeMap<(LedgerLayer, RefusalReason), usize> {
        let mut counts = BTreeMap::new();
        for (_, outcome) in self.entries() {
            if let Outcome::Refused { layer, reason } = outcome {
                *counts.entry((layer, reason)).or_insert(0usize) += 1;
            }
        }
        counts
    }

    /// How many elisions there are, by the reason given for each.
    pub fn elisions_by_reason(&self) -> BTreeMap<ElisionReason, usize> {
        let mut counts = BTreeMap::new();
        for (_, outcome) in self.entries() {
            if let Outcome::Elided(reason) = outcome {
                *counts.entry(reason).or_insert(0usize) += 1;
            }
        }
        counts
    }

    /// Count the ledger into its columns.
    pub fn close(&self) -> LedgerClosure {
        let mut closure = LedgerClosure {
            total: self.outcomes.len(),
            conflicts: self.conflicts.values().sum(),
            ..LedgerClosure::default()
        };
        let trace = std::env::var_os("R2DEC_TRACE_REFUSAL").is_some();
        for (id, outcome) in &self.outcomes {
            match outcome {
                Outcome::Rendered { .. } => closure.rendered += 1,
                Outcome::Elided(_) => closure.elided += 1,
                Outcome::Refused { .. } => {
                    closure.refused += 1;
                    if trace {
                        eprintln!("obligation refused {id:?} {outcome:?}");
                    }
                }
                Outcome::Unattributed => {
                    closure.unattributed += 1;
                    if trace {
                        eprintln!("obligation unattributed {id:?}");
                    }
                }
            }
        }
        closure
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::obligation::{
        CanonicalInstructionId, CanonicalInstructionSite, SemanticObligationComponent,
    };

    fn obligation(op_index: u64, kind: SemanticObligationKind) -> SemanticObligationId {
        SemanticObligationId {
            instruction: CanonicalInstructionId {
                block_addr: 0x1000,
                site: CanonicalInstructionSite::Op(op_index),
            },
            kind,
            component: SemanticObligationComponent::Whole,
        }
    }

    fn ledger_of(ids: &[SemanticObligationId]) -> ObligationLedger {
        ObligationLedger {
            outcomes: ids.iter().map(|id| (*id, Outcome::Unattributed)).collect(),
            conflicts: BTreeMap::new(),
        }
    }

    #[test]
    fn an_obligation_nothing_speaks_about_stays_visible() {
        let spoken = obligation(0, SemanticObligationKind::ObservableMemoryRead);
        let silent = obligation(1, SemanticObligationKind::LiveValueProducer);
        let mut ledger = ledger_of(&[spoken, silent]);

        ledger.record(
            spoken,
            Outcome::Rendered {
                block_addr: 0x1000,
                op_idx: 0,
            },
        );

        let closure = ledger.close();
        assert_eq!(closure.total, 2);
        assert_eq!(closure.rendered, 1);
        assert_eq!(closure.unattributed, 1);
        assert!(!closure.is_closed());
        assert_eq!(ledger.unattributed().count(), 1);
    }

    #[test]
    fn the_columns_always_account_for_the_total() {
        let ids = [
            obligation(0, SemanticObligationKind::ObservableMemoryRead),
            obligation(1, SemanticObligationKind::ObservableMemoryWrite),
            obligation(2, SemanticObligationKind::Trap),
            obligation(3, SemanticObligationKind::LiveValueProducer),
        ];
        let mut ledger = ledger_of(&ids);

        ledger.record(
            ids[0],
            Outcome::Rendered {
                block_addr: 0x1000,
                op_idx: 0,
            },
        );
        ledger.record(ids[1], Outcome::Elided(ElisionReason::StackFrame));
        ledger.record(
            ids[2],
            Outcome::Refused {
                layer: LedgerLayer::Ssa,
                reason: RefusalReason::UnsupportedEffect,
            },
        );

        let closure = ledger.close();
        assert_eq!(closure.accounted(), closure.total);
        assert_eq!(
            (closure.rendered, closure.elided, closure.refused),
            (1, 1, 1)
        );
        assert_eq!(closure.unattributed, 1);
    }

    #[test]
    fn a_second_answer_that_disagrees_is_reported_rather_than_applied() {
        let id = obligation(0, SemanticObligationKind::LiveValueProducer);
        let mut ledger = ledger_of(&[id]);
        let rendered = Outcome::Rendered {
            block_addr: 0x1000,
            op_idx: 0,
        };

        assert_eq!(ledger.record(id, rendered), Record::Accepted);
        assert_eq!(ledger.record(id, rendered), Record::Redundant);
        assert_eq!(
            ledger.record(id, Outcome::Elided(ElisionReason::DeadCpuFlag)),
            Record::Conflict(rendered)
        );

        assert_eq!(ledger.outcome(&id), rendered);
        assert_eq!(ledger.close().conflicts, 1);
    }

    #[test]
    fn taking_back_a_disproven_claim_is_not_a_conflict() {
        let id = obligation(0, SemanticObligationKind::LiveValueProducer);
        let mut ledger = ledger_of(&[id]);
        ledger.record(
            id,
            Outcome::Rendered {
                block_addr: 0x1000,
                op_idx: 0,
            },
        );

        let refused = Outcome::Refused {
            layer: LedgerLayer::Structure,
            reason: RefusalReason::NoRenderedOccurrence,
        };
        assert_eq!(ledger.overwrite(id, refused), Record::Accepted);

        assert_eq!(ledger.outcome(&id), refused);
        let closure = ledger.close();
        assert_eq!((closure.refused, closure.conflicts), (1, 0));
    }

    #[test]
    fn an_obligation_the_inventory_never_held_is_not_invented() {
        let held = obligation(0, SemanticObligationKind::LiveValueProducer);
        let foreign = obligation(9, SemanticObligationKind::Call);
        let mut ledger = ledger_of(&[held]);

        assert_eq!(
            ledger.record(
                foreign,
                Outcome::Rendered {
                    block_addr: 0x1000,
                    op_idx: 9,
                },
            ),
            Record::Unknown
        );
        assert_eq!(ledger.close().total, 1);
    }

    #[test]
    fn duplicate_render_refusal_has_a_stable_diagnostic_name() {
        assert_eq!(
            RefusalReason::DuplicateRenderedOccurrence.to_string(),
            "duplicate-rendered-occurrence"
        );
    }
}
