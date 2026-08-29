//! The rules both binding-component derivations obey.
//!
//! A binding's membership is worked out twice: once by `construction`, which
//! unions values as it walks the certificates, and once by `seal`, which
//! recomputes the same components by a sorted traversal that cannot see the
//! construction pass's representatives, union schedule or accumulator. The
//! duplication is the point. The seal is a proof that the plan the renderer
//! will use is the plan the facts imply, and a proof that shared the
//! construction's working would prove nothing.
//!
//! What must not be duplicated is the *rules*. Two independent derivations of
//! one answer are a cross-check; two independently written statements of the
//! same rule are two answerers that can drift, and when they drift the seal
//! rejects a plan that is correct. So the rules live here, once, and both
//! derivations call them while keeping their own traversals.

use std::collections::BTreeSet;

use r2ssa::{SsaGraph, ValueId};
use r2types::SourceOwnedFunctionFacts;

use super::{
    BindingPlanBuildError, BindingPlanSourceMismatch, certified_direct_control_target_values,
    certified_return_control_values, certified_stack_frame_values, certified_stack_geometry_values,
};

/// Which values can be members of a binding at all.
///
/// A constant is an expression that initializes or updates an object, not an
/// object. The rest are values some other part of the model already answers
/// for -- an unobserved merge or value, a return-control or direct
/// control-flow target, the stack frame and its geometry, and values the
/// obligation ledger records as structurally unused. A binding for one of
/// those would be a second answer about the same value.
pub(super) fn component_eligible_values(
    source_owned: &SourceOwnedFunctionFacts,
) -> Result<Vec<bool>, BindingPlanBuildError> {
    let source = source_owned.source();
    let graph = source.graph();
    let unobserved_merges = source.unobserved_merges();
    let unobserved_values = source.unobserved_values();
    let return_controls = certified_return_control_values(source);
    let direct_control_targets = certified_direct_control_target_values(source);
    let stack_frame_values = certified_stack_frame_values(source);
    let stack_geometry_values = certified_stack_geometry_values(source);
    let structural_unused =
        source
            .obligations()
            .structural_unused_values(graph)
            .ok_or(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::Authority,
            ))?;
    Ok(graph
        .values
        .iter()
        .map(|value| {
            value.var.constant_bits().is_none()
                && !unobserved_merges.contains(value.id)
                && !unobserved_values.contains(&value.id)
                && !return_controls.contains(&value.id)
                && !direct_control_targets.contains(&value.id)
                && !stack_frame_values.contains(&value.id)
                && !stack_geometry_values.contains(&value.id)
                && !structural_unused.contains(&value.id)
        })
        .collect())
}

/// The pairs of values some one instruction reads at the same time.
///
/// If a single instruction takes both values as inputs, both hold their
/// content at that instruction, so they cannot be one C object. This is exact
/// rather than approximate, and it is the whole interference test that matters
/// here. `fnv1a64` is the case it was written for: `xor rax, r8` reads the
/// byte just loaded and the hash carried from the previous iteration, and a
/// loop carrier coalesced `rax`'s whole run into `r8` anyway. The rendering
/// then said `R8_1 ^= R8_1`, which is zero, and the function returned zero for
/// every non-empty input while compiling perfectly cleanly.
///
/// Only across storage locations. A carrier coalescing two runs of the same
/// register is the ordinary case and stays allowed; what has to be declined is
/// folding one machine location into another while both are needed, which is
/// what a copy into a carried register looks like.
pub(super) fn values_read_together(graph: &SsaGraph) -> BTreeSet<(ValueId, ValueId)> {
    let location_of = |value: ValueId| {
        graph
            .value(value)
            .and_then(|value| value.canonical_storage)
            .map(r2ssa::CanonicalStorageId::location)
    };
    let mut read_together = BTreeSet::new();
    for inst in &graph.insts {
        for (position, left) in inst.inputs.iter().enumerate() {
            for right in inst.inputs.iter().skip(position + 1) {
                if left == right {
                    continue;
                }
                let (Some(left_location), Some(right_location)) =
                    (location_of(*left), location_of(*right))
                else {
                    continue;
                };
                if left_location != right_location {
                    read_together.insert((*left.min(right), *left.max(right)));
                }
            }
        }
    }
    read_together
}

/// Whether putting exactly these values in one object would put two values
/// that some instruction reads together into it.
///
/// The two derivations compute the candidate set differently -- one from its
/// union-find state, the other from storage-span membership -- and that
/// difference is the independence worth keeping. The question asked of the
/// resulting set is the same one, so it is asked here.
pub(super) fn set_interferes(
    read_together: &BTreeSet<(ValueId, ValueId)>,
    members: &BTreeSet<ValueId>,
) -> bool {
    read_together
        .iter()
        .any(|(left, right)| members.contains(left) && members.contains(right))
}
