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
    BindingPlanBuildError, BindingPlanSourceMismatch, certified_direct_call_target_values,
    certified_direct_control_target_values, certified_return_control_values,
    certified_stack_frame_values, certified_stack_geometry_values,
};

/// Which values can be members of a binding at all.
///
/// A constant is an expression that initializes or updates an object, not an
/// object. The rest are values some other part of the model already answers
/// for -- an unobserved merge or value, a return-control or direct
/// control-flow target, the stack frame and its geometry, and values the
/// obligation ledger records as structurally unused, and the target of a direct
/// call, which the call expression spells as the callee's name. A binding for
/// one of those would be a second answer about the same value.
pub(super) fn component_eligible_values(
    source_owned: &SourceOwnedFunctionFacts,
) -> Result<Vec<bool>, BindingPlanBuildError> {
    let source = source_owned.source();
    let graph = source.graph();
    let unobserved_merges = source.unobserved_merges();
    let unobserved_values = source.unobserved_values();
    let return_controls = certified_return_control_values(source);
    let direct_control_targets = certified_direct_control_target_values(source);
    let direct_call_targets = certified_direct_call_target_values(source);
    let stack_frame_values = certified_stack_frame_values(source);
    let stack_geometry_values = certified_stack_geometry_values(source);
    let structural_unused = source
        .obligations()
        .structural_unused_values(graph, source.unobserved_merges().unobserved_uses())
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
                && !direct_call_targets.contains(&value.id)
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
/// Across storage locations always, and within one location when neither value
/// is carried.
///
/// Folding one machine location into another while both are needed is the
/// obvious interference. Two runs of the *same* location are the ordinary case
/// a carrier coalesces, and declining those breaks the carrier: seven corpus
/// functions rendered the wrong answer when this declined them all, because the
/// assignment that carries a loop round its back edge disappeared.
///
/// But two runs of one location that a single instruction reads at once, and
/// that are both computed here rather than carried in, are not that case. Both
/// hold their content at that instruction. `crc32_bitwise` at arm64 -O2 is the
/// case: the lift routes `w10` and `w11` through one p-code temporary, and
/// `eor w10, w10, w11` reads two versions of it. Coalescing them made that
/// statement the exclusive-or of a value with itself, which is zero for every
/// input.
///
/// A value defined by a merge is carried by definition, so a pair with one of
/// those in it stays exempt; a pair of ordinary definitions does not.
pub(super) fn values_read_together(graph: &SsaGraph) -> BTreeSet<(ValueId, ValueId)> {
    let location_of = |value: ValueId| {
        graph
            .value(value)
            .and_then(|value| value.canonical_storage)
            .map(r2ssa::CanonicalStorageId::location)
    };
    let is_merged = |value: ValueId| {
        graph
            .def_inst(value)
            .and_then(|inst| graph.inst(inst))
            .is_none_or(|inst| matches!(inst.payload, r2ssa::InstPayload::Phi { .. }))
    };
    let mut read_together = BTreeSet::new();
    for inst in &graph.insts {
        // A merge does not read its operands together. Each one reaches it on
        // its own edge, and only one of them is live at a time, which is the
        // whole reason a merge can be coalesced into one object at all.
        if matches!(inst.payload, r2ssa::InstPayload::Phi { .. }) {
            continue;
        }
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
                if left_location != right_location || (!is_merged(*left) && !is_merged(*right)) {
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

/// Whether any member of a candidate set is still needed where another member
/// is redefined.
///
/// Values read together by one instruction are the obvious interference and
/// `values_read_together` finds them. They are not the only one. Two values can
/// interfere without any single instruction naming both: it is enough that one
/// is still going to be read at a point after the other has been given a new
/// value, because putting them in one object means that new value overwrote it.
///
/// `xxhash32`'s remainder loop is the case. The machine computes
/// `x15 = x12 + 4`, loads through `x12` with a post-increment of eight, and
/// then does `x12 = x15`, so the pointer advances by four. A loop-carrier
/// certificate coalesced `x15` and `x12` into one object; no instruction reads
/// both, so the co-read test allowed it; and the rendering became
/// `x12 = x12 + 4` followed by a load through the already-advanced `x12`. It
/// compiled and hashed the wrong bytes.
///
/// The test is deliberately conservative and local: within one block, a member
/// defined before another member and read after it is interference. That is
/// exact for the straight-line case this exists for, and declining a
/// coalescing costs an assignment in the output and nothing in correctness.
pub(super) fn set_outlives_a_redefinition(graph: &SsaGraph, members: &BTreeSet<ValueId>) -> bool {
    let site_of = |value: ValueId| {
        let inst = graph.def_inst(value)?;
        let inst = graph.inst(inst)?;
        Some((inst.block, inst.ordinal))
    };
    for member in members {
        let Some((block, defined_at)) = site_of(*member) else {
            continue;
        };
        let last_use = graph
            .use_sites(*member)
            .iter()
            .filter_map(|site| {
                let inst = graph.inst(site.inst)?;
                (inst.block == block).then_some(inst.ordinal)
            })
            .max();
        let Some(last_use) = last_use else {
            continue;
        };
        for other in members {
            if other == member {
                continue;
            }
            if site_of(*other).is_some_and(|(other_block, other_at)| {
                other_block == block && other_at > defined_at && other_at < last_use
            }) {
                return true;
            }
        }
    }
    false
}
