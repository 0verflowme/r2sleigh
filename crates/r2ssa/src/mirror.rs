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

use crate::graph::{SsaGraph, ValueId};
use crate::semantic::{ObjectKind, ObjectModel, StructuredDataflowFacts, StructuredLoopFact};

/// Whether this loop moves the carrier through memory that already holds it.
///
/// The test is the reload, and it has to be asked about what the carrier is made
/// of rather than about the carrier's own values. Neither end of the spill names
/// a member directly: what the loop stores is computed *from* a member, and what
/// a member is computed from is what the loop loaded. So the question is whether
/// a frame-slot read inside the loop reaches a value the carrier passes through.
/// If it does, the slot carried the value and the register was handed a copy.
pub fn carrier_mirrors_memory(
    structured: &StructuredDataflowFacts,
    objects: &ObjectModel,
    graph: &SsaGraph,
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

    // Frame slots only. Reading somewhere the caller can see is an effect of the
    // program, not a place a local was being kept.
    let reloaded = structured
        .memory_accesses
        .values()
        .filter(|access| {
            !access.is_write
                && access.provenance_complete
                && in_loop.contains(&access.block_addr)
                && objects
                    .object(access.object)
                    .is_some_and(|object| matches!(object.kind, ObjectKind::StackSlot { .. }))
        })
        .filter_map(|access| access.value)
        .collect::<BTreeSet<_>>();
    if reloaded.is_empty() {
        return false;
    }

    // Walk back from what the carrier holds. Each value is visited once, so the
    // search costs one pass over the edges it can reach and no more.
    let mut seen = carrier_members.clone();
    let mut pending = carrier_members.iter().copied().collect::<Vec<_>>();
    while let Some(value) = pending.pop() {
        if reloaded.contains(&value) {
            return true;
        }
        let Some(inst) = graph.def_inst(value).and_then(|inst| graph.inst(inst)) else {
            continue;
        };
        for input in &inst.inputs {
            if seen.insert(*input) {
                pending.push(*input);
            }
        }
    }
    false
}
