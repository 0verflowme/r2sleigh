//! Loop state a register holds only because memory already holds it.
//!
//! At low optimisation a compiler keeps a variable in its frame slot and moves
//! it through a register once per iteration: load, compute, store. Both the slot
//! and the register then look like loop-carried state, because both genuinely
//! are, and two layers each name the variable. The rendering ends up declaring
//! the register beside the slot, assigning it twice and reading it never, or
//! emitting the update once through each and losing the loop's shape to a copy
//! that says nothing.
//!
//! The register is the copy. What tells them apart is not liveness, which is
//! true of both, but where the value crosses the back edge: if the loop writes
//! the carrier to an object and reads that same object again, the object is what
//! carried it and the register only ferried it.

use std::collections::BTreeSet;

use crate::graph::ValueId;
use crate::semantic::{ObjectKind, ObjectModel, StructuredDataflowFacts, StructuredLoopFact};

/// Whether this loop moves the carrier through memory that already holds it.
///
/// The test is the reload. If a value the carrier passes through was read from a
/// frame slot inside the loop, then the register did not carry it across the back
/// edge -- the slot did, and the register was handed a copy on the way past.
///
/// Asking instead whether the carrier is written to a slot does not work, and was
/// tried: what gets stored is derived from the carrier rather than one of its own
/// values, so the store never names anything the carrier owns.
pub fn carrier_mirrors_memory(
    structured: &StructuredDataflowFacts,
    objects: &ObjectModel,
    loop_fact: &StructuredLoopFact,
    carrier_members: &BTreeSet<ValueId>,
) -> bool {
    let in_loop = loop_fact
        .body
        .iter()
        .chain(std::iter::once(&loop_fact.header))
        .chain(loop_fact.latches.iter())
        .copied()
        .collect::<BTreeSet<_>>();

    structured.memory_accesses.values().any(|access| {
        !access.is_write
            && access.provenance_complete
            && in_loop.contains(&access.block_addr)
            && access
                .value
                .is_some_and(|value| carrier_members.contains(&value))
            // A frame slot only. Reading somewhere the caller can see is an effect
            // of the program, not a place a local was being kept.
            && objects
                .object(access.object)
                .is_some_and(|object| matches!(object.kind, ObjectKind::StackSlot { .. }))
    })
}

/// Every value one carrier passes through, which is what a spill has to name.
pub fn carrier_members(carrier: &crate::semantic::LoopCarrierFact) -> BTreeSet<ValueId> {
    carrier
        .identity_values
        .iter()
        .copied()
        .chain(carrier.entries.iter().map(|edge| edge.value))
        .chain(carrier.updates.iter().flat_map(|update| {
            std::iter::once(update.value).chain(update.identity_values.iter().copied())
        }))
        .collect()
}
