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
//!
//! ## What may license a coalescing
//!
//! Three things, and they are proofs rather than exemptions. Two of them
//! propose a set of values as one object in `construction`: a *storage span*,
//! which says the values share a machine location, and a *certified entity*,
//! which says an upstream certificate found them to be one object. The rules
//! below then decline either proposal where it would put two values one
//! instruction reads at once into one object, or where one member is still
//! read after another has been given a new value.
//!
//! The third is newer and lives with the elision it licenses, in
//! `observation_journal::boundary_restores_carrier`: the *convention's
//! preserved-carrier statement*, which says a call leaves a named carrier
//! where it found it. It matters because the declines above are declines for
//! want of proof rather than prohibitions -- the comment beside the program
//! copy rule names "a save and restore around a clobber" as the shape that
//! must not fold, and the reason given is that nothing shows the object
//! survived. A call boundary's restore is exactly that shape and the source
//! does show it, naming the carrier it means, so the fold is admitted on the
//! proof and declined without it. Anything widening this further should
//! supply a fact of the same kind rather than a test on an operation's
//! spelling, which is what would turn the rule into a hole.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::ledger::ElisionReason;
use r2ssa::{InstId, SsaGraph, UseSite, ValueId};
use r2types::SourceOwnedFunctionFacts;

use super::{
    BindingPlanBuildError, BindingPlanSourceMismatch, ParameterRefusal, SemanticId,
    certified_direct_call_target_values, certified_direct_control_target_values,
    certified_elided_read_instructions, certified_return_control_values,
    certified_stack_frame_values, certified_stack_geometry_values, declaration_width_is_supported,
};

/// One ABI slot's evidence, before either derivation turns it into a
/// disposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ParameterCandidate {
    Exact {
        entity: SemanticId,
        width_bytes: u32,
        entry_values: BTreeSet<ValueId>,
    },
    Refused(ParameterRefusal),
}

/// Collect the dense exact ABI-parameter domain without consulting names.
///
/// The source interface supplies unused formals; a matching render entity
/// supplies its exact entry-value membership and source-var carrier width.
/// Two claims on one slot refuse it, and the first refusal stands: a later
/// claim on a slot already refused does not change why it was refused, and
/// construction and the seal once disagreed about exactly that -- one
/// overwrote the reason, the other kept it -- so the seal refused every
/// function in which a slot was claimed three times, for a plan that was
/// right. One statement here is what keeps them from disagreeing again.
pub(super) fn parameter_candidates(
    source_owned: &SourceOwnedFunctionFacts,
) -> Vec<Option<ParameterCandidate>> {
    let mut candidates = Vec::new();
    if let Some(interface) = source_owned.source().machine_context().function_interface() {
        for parameter in interface.parameters() {
            insert_formal_parameter_candidate(
                &mut candidates,
                parameter.index(),
                parameter.storage().size,
            );
        }
    }
    let Some(render) = source_owned.report().render() else {
        return candidates;
    };
    for (key, certified) in &render.certified_entities {
        let r2types::CertifiedEntity::Parameter {
            id,
            slot,
            entry_values,
            carrier_width,
            ..
        } = certified
        else {
            continue;
        };
        let Ok(index) = usize::try_from(*slot) else {
            continue;
        };
        if index >= candidates.len() {
            candidates.resize_with(index.saturating_add(1), || None);
        }
        let canonical = SemanticId::Parameter(*slot);
        if *key != *id || *id != canonical {
            candidates[index] = Some(ParameterCandidate::Refused(
                ParameterRefusal::ConflictingEntityOwnership {
                    entity: *id,
                    expected_slot: *slot,
                    claimed_slot: match *id {
                        SemanticId::Parameter(claimed) => claimed,
                        _ => u32::MAX,
                    },
                },
            ));
            continue;
        }
        candidates[index] = Some(match &candidates[index] {
            Some(ParameterCandidate::Exact { entity, .. }) if *entity != *id => {
                ParameterCandidate::Refused(ParameterRefusal::ConflictingSlotOwnership {
                    slot: *slot,
                    first: *entity,
                    second: *id,
                })
            }
            Some(ParameterCandidate::Refused(reason)) => ParameterCandidate::Refused(*reason),
            Some(ParameterCandidate::Exact { .. }) | None => ParameterCandidate::Exact {
                entity: *id,
                width_bytes: *carrier_width,
                entry_values: entry_values.clone(),
            },
        });
    }
    candidates
}

pub(super) fn insert_formal_parameter_candidate(
    candidates: &mut Vec<Option<ParameterCandidate>>,
    slot: u32,
    width_bytes: u32,
) {
    let index = slot as usize;
    if index >= candidates.len() {
        candidates.resize_with(index.saturating_add(1), || None);
    }
    let entity = SemanticId::Parameter(slot);
    candidates[index] = Some(match &candidates[index] {
        None => ParameterCandidate::Exact {
            entity,
            width_bytes,
            entry_values: BTreeSet::new(),
        },
        Some(ParameterCandidate::Exact { entity: first, .. }) => {
            ParameterCandidate::Refused(ParameterRefusal::ConflictingSlotOwnership {
                slot,
                first: *first,
                second: entity,
            })
        }
        Some(ParameterCandidate::Refused(reason)) => ParameterCandidate::Refused(*reason),
    });
}

/// The declaration width of one parameter slot, from its carrier width.
pub(super) fn parameter_width(
    entity: SemanticId,
    slot: u32,
    width_bytes: u32,
) -> Result<u32, ParameterRefusal> {
    if width_bytes == 0 {
        return Err(ParameterRefusal::MissingWidth { entity, slot });
    }
    let width_bits = width_bytes
        .checked_mul(8)
        .ok_or(ParameterRefusal::InvalidWidth {
            entity,
            slot,
            size_bytes: width_bytes,
        })?;
    declaration_width_is_supported(width_bits)
        .then_some(width_bits)
        .ok_or(ParameterRefusal::UnsupportedWidth {
            entity,
            slot,
            width_bits,
        })
}

/// Which values can be members of a binding at all.
///
/// A constant is an expression that initializes or updates an object, not an
/// object. The rest are values some other part of the model already answers
/// for -- an unobserved merge or value, a return-control or direct
/// control-flow target, the stack frame and its geometry, and values the
/// obligation ledger records as structurally unused, and the target of a direct
/// call, which the call expression spells as the callee's name. A binding for
/// one of those would be a second answer about the same value.
#[cfg(test)]
pub(super) fn component_eligible_values(
    source_owned: &SourceOwnedFunctionFacts,
    projection: &r2ssa::MachineProjection,
) -> Result<Vec<bool>, BindingPlanBuildError> {
    Ok(rewrite_inlining_partition(source_owned, projection)?.component_eligible)
}

/// The same answer from a stated inlining decision.
///
/// The partition is a function of which values are inlined, and the inlining
/// answer needs the partition to ask whether a literal is alone in its
/// object. Taking the decision as an argument is what lets the two be
/// computed in a stated order instead of one estimating the other.
pub(super) fn component_eligible_with(
    source_owned: &SourceOwnedFunctionFacts,
    projection: &r2ssa::MachineProjection,
    inlinable: &BTreeSet<ValueId>,
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
    let unread = unread_defined_values(source, projection);
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
                && !inlinable.contains(&value.id)
                && !unread.contains(&value.id)
        })
        .collect())
}

/// Values defined in this function that no graph or certified boundary reads.
///
/// Entry values are deliberately outside this set: an exact interface can own
/// an unused parameter declaration independently of a body read. Constants
/// likewise have no defining instruction to remove. For a defined value, the
/// graph use table plus the complete graphless boundary-reader inventory is the
/// closed read domain, so membership is a linear pass with `O(log n)` indexed
/// certificate lookups.
pub(super) fn unread_defined_values(
    source: &r2ssa::SsaArtifact,
    projection: &r2ssa::MachineProjection,
) -> BTreeSet<ValueId> {
    let certified = certified_value_readers(source);
    source
        .graph()
        .values
        .iter()
        .filter(|value| {
            let Some(definition) = source.graph().def_inst(value.id) else {
                return false;
            };
            matches!(
                projection.write_disposition(definition),
                Some(r2ssa::MachineWriteDisposition::Exact(_))
            ) && source.graph().inst(definition).is_some_and(|instruction| {
                (0..instruction.inputs.len()).all(|input_idx| {
                    matches!(
                        projection.use_disposition(r2ssa::UseSite {
                            inst: definition,
                            input_idx,
                        }),
                        Some(
                            r2ssa::MachineUseDisposition::Exact(_)
                                | r2ssa::MachineUseDisposition::MemoryAddress(_)
                        )
                    )
                })
            })
        })
        .filter(|value| source.graph().use_sites(value.id).is_empty())
        .filter(|value| !certified.contains_key(&value.id))
        .map(|value| value.id)
        .collect()
}

fn certified_value_readers(source: &r2ssa::SsaArtifact) -> BTreeMap<ValueId, Vec<InstId>> {
    let mut readers = BTreeMap::<ValueId, Vec<InstId>>::new();
    for inst in &source.graph().insts {
        for value in super::certified_boundary_read_values(source, inst.id) {
            readers.entry(value).or_default().push(inst.id);
        }
    }
    readers
}

/// The type one object is declared with.
///
/// Until now every binding was declared `CType::machine_bits(width)` -- the
/// unsigned integer of its storage's width -- and the recovered type was
/// reported by the typed-recovery score rather than asserted in the C. That
/// makes every parameter a `uint64_t`, so nothing the evidence solver proves
/// about a pointer or a narrower result reaches a reader or a recompile.
///
/// The evidence decides it now, and only where it agrees with itself and with
/// the storage. Every member of one binding is one object, so members that
/// carry different evidence types are a genuine conflict and the machine word
/// stands; a type whose width does not match the storage is not a description
/// of this object and is refused the same way. A pointer is the one type whose
/// width is the pointer width rather than the declared object's, and it is
/// admitted at exactly that width.
///
/// Casts follow the declaration -- the typed boundaries read a bound value
/// at its declared type -- so asserting here changes the operands too,
/// which is what keeps the emitted C compiling under `-Werror` rather than
/// converting an argument's signedness against its own declaration.
pub(super) fn declaration_type_for_binding(
    source_owned: &SourceOwnedFunctionFacts,
    members: impl IntoIterator<Item = ValueId>,
    width_bits: u32,
    ptr_bits: u32,
) -> r2types::CTypeLike {
    let machine = r2types::CTypeLike::machine_bits(width_bits);
    let evidence = source_owned.evidence_types();
    let mut agreed: Option<r2types::CTypeLike> = None;
    for value in members {
        let Some(ty) = evidence.value_type(value) else {
            continue;
        };
        match &agreed {
            None => agreed = Some(ty.clone()),
            Some(existing) if existing == ty => {}
            Some(_) => return machine,
        }
    }
    let Some(agreed) = agreed else {
        return machine;
    };
    admit_declaration(agreed, width_bits, ptr_bits)
}

/// The type a stack object is declared with.
///
/// A spilled pointer is a pointer. Declaring the slot the machine word while
/// the register it is spilled from is a pointer makes the reload
/// `p = slot;` -- an integer assigned to a pointer, which does not compile --
/// so the object and the values that flow through it have to be declared from
/// the same evidence.
pub(super) fn declaration_type_for_stack_object(
    source_owned: &SourceOwnedFunctionFacts,
    object: r2ssa::ObjectId,
    width_bits: u32,
    ptr_bits: u32,
) -> r2types::CTypeLike {
    let machine = r2types::CTypeLike::machine_bits(width_bits);
    let source = source_owned.source();
    let array_layout = source
        .certificates()
        .stack_slots
        .get(&object)
        .map(|certificate| &certificate.array_layout);
    match array_layout {
        Some(r2ssa::StackArrayLayoutDisposition::Proven(layout)) => {
            if layout.object == object
                && layout.element_width == layout.stride
                && layout.element_width > 0
                && layout
                    .extent
                    .is_multiple_of(u64::from(layout.element_width))
                && layout.extent.checked_mul(8) == Some(u64::from(width_bits))
                && let Ok(count) = usize::try_from(layout.extent / u64::from(layout.element_width))
                && let Some(element_bits) = layout.element_width.checked_mul(8)
            {
                return r2types::CTypeLike::Array(
                    Box::new(r2types::CTypeLike::machine_bits(element_bits)),
                    Some(count),
                );
            }
            // A malformed aggregate certificate cannot be retried from type
            // evidence: that would give the object a second geometry owner.
            return machine;
        }
        Some(r2ssa::StackArrayLayoutDisposition::Refused(_)) => {
            // Refusal is authoritative. In particular, conflicting access
            // widths and a missing constant bound must remain scalar even if
            // advisory type evidence happens to resemble an array.
            return machine;
        }
        Some(r2ssa::StackArrayLayoutDisposition::NotIndexed) | None => {}
    }
    let Some(fact) = source.objects().object(object) else {
        return machine;
    };
    let (base, offset) = match fact.kind {
        r2ssa::ObjectKind::StackSlot { base, offset, .. }
        | r2ssa::ObjectKind::FrameObject { base, offset, .. } => (base, offset),
        _ => return machine,
    };
    let key = r2types::StackSlotKey {
        base: match base {
            r2ssa::StackAddressBase::FramePointer => r2types::ExternalStackBase::FramePointer,
            r2ssa::StackAddressBase::StackPointer => r2types::ExternalStackBase::StackPointer,
        },
        offset,
    };
    let Some((_, ty)) = source_owned
        .evidence_types()
        .stack_slot_types()
        .find(|(slot, _)| **slot == key)
    else {
        return machine;
    };
    admit_declaration(ty.clone(), width_bits, ptr_bits)
}

/// Admit a recovered type only where it describes an object of this storage.
///
/// A type whose width is not the storage's width is not a description of this
/// object, whatever else it may be true of, and the machine word stands. A
/// pointer is the one type whose width is the pointer width rather than the
/// declared object's, and it is admitted at exactly that width.
pub(crate) fn admit_declaration(
    ty: r2types::CTypeLike,
    width_bits: u32,
    ptr_bits: u32,
) -> r2types::CTypeLike {
    r2types::admit_declaration_type(ty, width_bits, ptr_bits)
}

/// The storage width a declared type describes.
///
/// This is what the seal checks a declaration against. It used to compare the
/// declaration to `CType::machine_bits(width)` outright, which is a check that
/// the declaration is the machine word rather than a check that it describes
/// the storage -- so it rejected every recovered type on sight. The width is
/// the part the seal can re-derive from the source; what the evidence proved
/// beyond it is not something a second derivation of the *plan* can confirm.
pub(super) fn declaration_type_width(ty: &r2types::CTypeLike, ptr_bits: u32) -> Option<u32> {
    r2types::declaration_type_width_bits(ty, ptr_bits)
}

/// Whether a declaration describes an object of exactly this storage width.
pub(super) fn declaration_type_describes_width(
    ty: &r2types::CTypeLike,
    width_bits: u32,
    ptr_bits: u32,
) -> bool {
    declaration_type_width(ty, ptr_bits) == Some(width_bits)
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

/// Takes the projection rather than building one.
///
/// It used to build its own, and the seal asked it per value inside a loop, so
/// one render lowered the whole machine arena once for every inlined value.
/// That was seventy-two per cent of a render on `xxhash32`. The projection is
/// derived from the artifact and is the same object either way; deriving it
/// again is not a second opinion, only the same answer at a cost.
pub(super) struct RewriteInliningPartition {
    pub(super) canonical: r2rewrite::CanonicalRoots,
    pub(super) inlinable: BTreeSet<ValueId>,
    pub(super) component_eligible: Vec<bool>,
}

/// Compute producer expansion, expression inlining, and binding membership as
/// one bounded fixed point.
///
/// Pass one imports without absorbing producers. That is enough to decide
/// whether each value's own canonical root has a C form, without feeding a
/// binding decision back into the rewriter. The existing conservative
/// singleton partition then admits only bound literals that cannot orphan a
/// coalesced object. Pass two canonicalises once with that settled inlining set
/// as the expansion policy and derives the final component eligibility from the
/// same set. Every lookup is indexed; each pass is linear in the machine and
/// term arenas apart from the existing ordered component lookups.
pub(super) fn rewrite_inlining_partition(
    source_owned: &SourceOwnedFunctionFacts,
    projection: &r2ssa::MachineProjection,
) -> Result<RewriteInliningPartition, BindingPlanBuildError> {
    // Two passes, in a stated order, and no iteration.
    //
    // The gate below turns away a literal that lives in a register because
    // such a literal is frequently the only write of an object other values
    // are coalesced into: `R8_1 = 0xcbf29ce484222325` initialises the
    // accumulator `fnv1a64` then reads across its loop, and spelling the
    // constant at each reader leaves that object read before it is assigned.
    // The honest test is whether the value is alone in its binding, and that
    // needs the partition, which is computed from this answer.
    //
    // So the partition is built once from the answer that admits no such
    // literal -- the conservative one, which is what this function returned
    // before -- and a literal that is a *one-member component* there is
    // admitted on the second pass. Nothing coalesces with a one-member
    // component by definition, so removing that value removes its own object
    // and no other object loses a writer. A literal that shares an object,
    // like the accumulator, is not a singleton and stays bound.
    //
    // Termination is by construction rather than by convergence: pass one
    // does not depend on pass two, so there is no iteration to bound. The
    // second pass is conservative rather than maximal -- a candidate that
    // would become a singleton only after other candidates are inlined is
    // declined -- which is the safe direction, and it is why estimating the
    // partition from a relaxed eligibility set is not needed. That estimate
    // is also unsound: excluding a value removes it from the member set
    // `merge_would_interfere` reads, so it can remove the interference
    // blocking a merge and make a component *grow*.
    let source = source_owned.source();
    let seed_canonical = r2rewrite::canonicalize_with(source, projection, &|_| false)
        .map_err(BindingPlanBuildError::Canonicalisation)?;
    let conservative = inlinable_core(source_owned, projection, &seed_canonical, &BTreeSet::new());
    let eligible = component_eligible_with(source_owned, projection, &conservative)?;
    let components = super::construction::binding_components_with(source_owned, &eligible)?;
    let alone = components
        .iter()
        .filter(|component| component.members.len() == 1)
        .filter_map(|component| component.members.first().copied())
        .collect::<BTreeSet<_>>();
    let admitted = duplicable_bound_literals(projection, source_owned, &alone);
    let inlinable = if admitted.is_empty() {
        conservative
    } else {
        inlinable_core(source_owned, projection, &seed_canonical, &admitted)
    };
    let component_eligible = component_eligible_with(source_owned, projection, &inlinable)?;
    let canonical =
        r2rewrite::canonicalize_with(source, projection, &|query: &r2rewrite::ExpansionQuery<
            '_,
        >| {
            term_absorbs_producer(&inlinable, query)
        })
        .map_err(BindingPlanBuildError::Canonicalisation)?;
    Ok(RewriteInliningPartition {
        canonical,
        inlinable,
        component_eligible,
    })
}

/// Whether a reader's term may absorb the producer of `value`.
///
/// One question with one answer: a term absorbs a producer exactly when the
/// plan renders that producer's value without a local. Both are
/// `inlinable_values`, so there is nothing here for the two to disagree
/// about, and the plan and the seal each derive the set from their own
/// projection and then call this.
///
/// # Why duplicability is not a second reason
///
/// The policy used to admit a producer whose term is duplicable -- literals
/// and entry values the function never writes -- on the ground that
/// duplicability is a property of the term rather than of the plan's
/// disposition. That is true of duplicability and beside the point of this
/// question. Absorbing a producer does not remove the producer's own
/// statement; only the plan's disposition does. A value the plan bound is
/// therefore rendered twice: once as `name = ...`, and again inside every
/// term that absorbed it. The rewriter then reports that producer as
/// discharged by each of those terms, because its value is no longer a leaf
/// of them, and the renderer marks the vanished instruction's write on the
/// expression standing in for it -- a second answerer for a write the
/// producer's own statement already renders.
///
/// That went unnoticed while nothing rendered from the canonical terms. The
/// subscript renderer does, and `elem_at`, `elem_before`, `bounded_fetch` and
/// `half_stride` at x86-64 -O1 and -O2 stopped rendering: their index is
/// `sext(esi)`, whose value the plan binds because a width change has no
/// inline form, and whose term is duplicable because `esi` is an entry value.
/// Placement found the absorbed write inside the right-hand side of an
/// assignment, where C states no order between it and the reads beside it,
/// and refused with `ambiguous_observation_execution_order`.
pub(super) fn term_absorbs_producer(
    inlinable: &BTreeSet<ValueId>,
    query: &r2rewrite::ExpansionQuery<'_>,
) -> bool {
    inlinable.contains(&query.value)
}

/// Literals held in a machine location that are alone in their object.
///
/// A literal in a lowering temporary is admitted by the gate in
/// `inlinable_core` without asking anything else, because the lifter's own
/// scratch is never coalesced. This is the rest: a literal the machine keeps
/// in a register or a memory cell, which may be an object's only write, and
/// is safe to spell at its readers exactly when nothing shares that object.
fn duplicable_bound_literals(
    projection: &r2ssa::MachineProjection,
    source_owned: &SourceOwnedFunctionFacts,
    alone: &BTreeSet<ValueId>,
) -> BTreeSet<ValueId> {
    let graph = source_owned.source().graph();
    let mut expr_by_value = std::collections::BTreeMap::new();
    for entity in projection.entities() {
        expr_by_value.insert(entity.output().value(), entity.root());
    }
    let literal_candidates = graph
        .values
        .iter()
        .filter(|value| alone.contains(&value.id))
        .filter(|value| {
            expr_by_value
                .get(&value.id)
                .copied()
                .is_some_and(|root| r2rewrite::machine_expr_is_literal(projection, root))
        })
        .map(|value| value.id)
        .collect::<BTreeSet<_>>();
    literal_candidates.iter().copied().collect()
}

/// The frame object base whose exact call-boundary readers may replace this value.
///
/// This is deliberately narrower than a generic multi-reader exception.  The
/// graph readers must all be certified load/store address cells for the same
/// object, and every graphless boundary reader must contain the value in an
/// exact call-argument cell. Repeating a pure frame address across calls does
/// not repeat a program effect; each occurrence carries the same value/use/write
/// classification, while the effect ledger still rejects any duplicated live
/// obligation.
fn frame_object_address_replacement(
    source: &r2ssa::SsaArtifact,
    projection: &r2ssa::MachineProjection,
    value: ValueId,
    use_sites: &[UseSite],
    boundary_readers: &[InstId],
) -> Option<r2ssa::ObjectId> {
    if boundary_readers.is_empty() {
        return None;
    }
    let mut object = None;
    for call in boundary_readers {
        let call_site = source.certificates().callsites_by_inst.get(call)?;
        let certificate = source.certificates().callsites.get(call_site)?;
        let mut matched = false;
        for (argument_index, argument) in certificate.argument_values.iter().enumerate() {
            if *argument != value {
                continue;
            }
            let candidate =
                super::certified_frame_object_call_argument(source, *call, argument_index, value)?;
            if object.is_some_and(|object| object != candidate) {
                return None;
            }
            object = Some(candidate);
            matched = true;
        }
        if !matched {
            return None;
        }
    }
    let object = object?;
    use_sites
        .iter()
        .all(|site| {
            let Some(r2ssa::MachineUseDisposition::MemoryAddress(address)) =
                projection.use_disposition(*site)
            else {
                return false;
            };
            let Some(access) = address.memory_access() else {
                return false;
            };
            source
                .certificates()
                .memory_accesses
                .get(&access)
                .is_some_and(|memory| {
                    memory.access == access
                        && memory.address == value
                        && memory.object == object
                        && source.objects().object_for_value(value, memory.space) == Some(object)
                })
        })
        .then_some(object)
}

fn inlinable_core(
    source_owned: &SourceOwnedFunctionFacts,
    projection: &r2ssa::MachineProjection,
    canonical: &r2rewrite::CanonicalRoots,
    admitted: &BTreeSet<ValueId>,
) -> BTreeSet<ValueId> {
    let source = source_owned.source();
    let graph = source.graph();
    // Boundary certificates record reads that do not exist as SSA operands:
    // return values, call arguments, switch selectors and identity call-result
    // carriers read by derived-width results. A graph-only count made call
    // arguments look dead here before that case was fixed; counting only that
    // certificate kind would make the same mistake for the other three.
    let certified_readers = certified_value_readers(source);
    // Of those graphless reads, call arguments are the one kind the renderer
    // can currently consume from an inline expression. Return, switch and
    // derived-result markers require a binding symbol, so they count as reads
    // for deadness but remain explicit inlining refusals below.
    let mut call_arg_readers = BTreeMap::<ValueId, BTreeSet<InstId>>::new();
    if let Some(callsites) = source_owned.report().callsites() {
        for (site, facts) in &callsites.by_callsite {
            let Some(inst) = graph.inst_id_for_op_site(site.block_addr, site.op_index) else {
                continue;
            };
            for argument in &facts.argument_values {
                call_arg_readers
                    .entry(argument.value)
                    .or_default()
                    .insert(inst);
            }
        }
    }
    let mut expr_by_value = std::collections::BTreeMap::new();
    for entity in projection.entities() {
        expr_by_value.insert(entity.output().value(), entity.root());
    }
    // One statement of which reads the certificates elide, shared with the
    // observation journal. A certificate the cells cannot be built from is a
    // function the journal will refuse, so there is nothing to fold for.
    let Ok(cells) = certificate_elided_cells(source, projection) else {
        return BTreeSet::new();
    };
    let elided_reads = cells.read_elided_instructions;
    // Which gate turned a value away, by name. Reading this function said a
    // flag copy passes every test in it, and the corpus said it stays bound;
    // the two could only be reconciled by asking the function itself, one
    // value at a time. `R2SLEIGH_TRACE_INLINE=<display name>` or `=all`.
    let trace = std::env::var("R2SLEIGH_TRACE_INLINE").ok();
    let mut inlinable = BTreeSet::new();
    for value in &graph.values {
        let traced = trace.as_deref().is_some_and(|want| {
            want == "all" || value.var.display_name().eq_ignore_ascii_case(want)
        });
        let rejected = |gate: &str| {
            if traced {
                eprintln!(
                    "INLINE {} {:?} stays bound: {gate}",
                    value.var.display_name(),
                    value.id
                );
            }
        };
        let use_sites = graph.use_sites(value.id);
        let boundary_readers = certified_readers
            .get(&value.id)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let reader_count = use_sites.len() + boundary_readers.len();
        if reader_count == 0 {
            rejected("no readers");
            continue;
        }
        // A value that reads nothing but literals is the same at every reader
        // and costs nothing to spell there, so the single-reader rule does not
        // apply to it. The broader question `r2rewrite` answers for expansion,
        // whether rendering twice observes anything twice, is satisfied by an
        // entry value the function never writes as well -- but copying an
        // expression over two parameters to three readers is three copies of a
        // real computation, not a local removed, so the plan asks the stricter
        // question.
        // ...and whose own storage is a lowering temporary. A register or a
        // memory cell holding a literal is a machine object other values are
        // coalesced with, and its write is frequently the only definition the
        // resulting C object has: `RAX_1 = 0xcbf29ce484222325` initialises
        // the accumulator that the loop then updates, and the two are one
        // binding. Spelling the constant at each reader deletes that
        // definition, and placement then finds the object read before it is
        // assigned -- ten of the fifty-four corpus cells, all on x86-64,
        // where the initialiser is a bare register literal.
        //
        // The honest test is not the storage class but whether the value is
        // coalesced with anything, and that cannot be asked here: the
        // partition is computed *from* this answer. A `Unique` slot is the
        // lifter's own scratch, which is the case this can decide without the
        // partition. Widening it needs the two-pass structure described in
        // the handoff, and is a design question rather than a bug.
        let literal_only = expr_by_value
            .get(&value.id)
            .copied()
            .is_some_and(|root| r2rewrite::machine_expr_is_literal(projection, root))
            && (value.canonical_storage.is_none_or(|storage| {
                matches!(storage.space, r2ssa::CanonicalStorageSpace::Unique)
            }) || admitted.contains(&value.id));
        let frame_address_replacement = frame_object_address_replacement(
            source,
            projection,
            value.id,
            use_sites,
            boundary_readers,
        );
        let root_kind = expr_by_value
            .get(&value.id)
            .and_then(|root| projection.expr(*root))
            .map_or("<no entity>", |expr| machine_expr_kind_name(expr.kind()));
        // Every reader, not only the ones that render. Discounting a reader
        // whose instruction a certificate elides looks right -- such a read
        // spells nothing -- and it is what the DecBench staging locals need.
        // It is also unsound as the rest of this function stands: with the
        // elided readers discounted, a value that is read again after its
        // object is rewritten becomes single-use, and the interference test
        // below spans only the window between the definition and the one
        // reader it then believes in. `fnv1a64` at x86-64 -O2 renders
        // `R8_1 = byte3; R8_1 = (R8_1 ^ (... ^ R8_1) * k) * k`, reading the
        // accumulator after the byte load has overwritten it, and computes a
        // wrong hash under a proof line claiming nothing was refused. Three
        // corpus cells do this and five more refuse. See the handoff.
        if !literal_only && frame_address_replacement.is_none() && reader_count != 1 {
            rejected(&format!(
                "{reader_count} readers ({} of them certified boundary reads), of which {} sit in a \
                 certificate-elided instruction; root {root_kind}",
                boundary_readers.len(),
                use_sites
                    .iter()
                    .filter(|site| elided_reads.contains(&site.inst))
                    .count(),
            ));
            continue;
        }
        let renderable = expr_by_value
            .get(&value.id)
            .and_then(|root| projection.expr(*root))
            .is_some_and(|expr| expression_renders_inline(expr.kind()))
            && canonical.value(value.id).is_some_and(|value| {
                term_renders_inline(&canonical.arena().term(value.canonical).kind)
            });
        if !renderable {
            rejected(&format!(
                "expression kind does not render inline: {root_kind}"
            ));
            continue;
        }
        if boundary_readers.iter().any(|reader| {
            !call_arg_readers
                .get(&value.id)
                .is_some_and(|arguments| arguments.contains(reader))
        }) {
            rejected("a certified boundary reader requires a bound value");
            continue;
        }
        let Some(definition) = graph.def_inst(value.id) else {
            rejected("no defining instruction");
            continue;
        };
        // The renderer will ask the plan for a write observation on the
        // definition and a use observation on each of its operands, and either
        // can answer refused for something never meant to be rendered here.
        // Asking now is the difference between declining to fold and failing to
        // generate: plan and renderer agree before the tree exists.
        if !matches!(
            projection.write_disposition(definition),
            Some(r2ssa::MachineWriteDisposition::Exact(_))
        ) {
            rejected("definition has no exact write disposition");
            continue;
        }
        let Some(def_inst) = graph.inst(definition) else {
            rejected("defining instruction missing from the graph");
            continue;
        };
        if !(0..def_inst.inputs.len()).all(|input_idx| {
            matches!(
                projection.use_disposition(r2ssa::UseSite {
                    inst: definition,
                    input_idx,
                }),
                Some(
                    r2ssa::MachineUseDisposition::Exact(_)
                        | r2ssa::MachineUseDisposition::MemoryAddress(_)
                )
            )
        }) {
            rejected("an operand of the definition has no exact use disposition");
            continue;
        }
        // The read this expression would move into has to be a read that
        // actually appears. A value whose one use sits in an instruction a
        // certificate elides -- the prologue's `push rbp` is a certified frame
        // round trip -- disappears together with that instruction, and the
        // effect its definition answered for is then owed by nobody. The
        // ledger scores that as a refusal and the function falls back to no
        // decompilation at all, which is what `murmur3_32` and `xxhash32` did.
        if use_sites
            .iter()
            .any(|site| elided_reads.contains(&site.inst))
            || boundary_readers
                .iter()
                .any(|inst| elided_reads.contains(inst))
        {
            rejected("a reader sits in a certificate-elided instruction");
            continue;
        }
        if frame_address_replacement.is_some() {
            // The memory-address cells remain owned by their load/store
            // renderings.  The sole call-boundary replacement owns the
            // producer expression and spells the canonical object's address.
            inlinable.insert(value.id);
            continue;
        }
        if literal_only {
            // Nothing is being moved past anything. The tests below ask whether
            // a computation stays correct where it lands, and a literal is the
            // same in both places.
            inlinable.insert(value.id);
            continue;
        }
        // The one reader, whether the graph recorded it or a boundary
        // certificate did. Only its position is wanted from here on: which
        // block it sits in, and what runs between the definition and it.
        let reader = match (use_sites, boundary_readers) {
            ([site], []) => site.inst,
            ([], [inst]) => *inst,
            _ => unreachable!("a value that is not literal-only was required to have one reader"),
        };
        let Some(use_inst) = graph.inst(reader) else {
            rejected("reading instruction missing from the graph");
            continue;
        };
        // A merge reads its operands on edges, not at a position in a block, so
        // comparing ordinals against one says nothing and moving a computation
        // into a merge operand moves it across the edge that operand arrives
        // on. `crc32_bitwise` and `pearson` are the cases: their loop carriers
        // are merges, and folding into them computed the wrong answer while
        // every other check passed.
        if matches!(use_inst.payload, r2ssa::InstPayload::Phi { .. }) {
            rejected("the one reader is a merge");
            continue;
        }
        if def_inst.block != use_inst.block || def_inst.ordinal >= use_inst.ordinal {
            rejected("the one reader is in another block or does not follow the definition");
            continue;
        }
        // Every location the *rendered* expression reads, not only the ones the
        // defining instruction lists. A machine expression is a tree over the
        // arena, so moving it moves every leaf in it, and a leaf can name a
        // location the instruction itself never mentions. Checking only the
        // instruction's inputs let three corpus cells compute the wrong answer.
        let mut read_locations = BTreeSet::new();
        let mut pending = vec![*expr_by_value.get(&value.id).expect("checked above")];
        let mut seen = BTreeSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            let Some(expr) = projection.expr(node) else {
                continue;
            };
            if let r2ssa::MachineExprKind::Source { binding, storage } = expr.kind() {
                if let Some(storage) = storage {
                    read_locations.insert(storage.location());
                } else if let Some(storage) = graph
                    .value(binding.value())
                    .and_then(|v| v.canonical_storage)
                {
                    read_locations.insert(storage.location());
                }
            }
            pending.extend(expr.kind().children());
        }
        read_locations.extend(
            def_inst
                .inputs
                .iter()
                .filter_map(|i| graph.value(*i))
                .filter_map(|v| v.canonical_storage)
                .map(r2ssa::CanonicalStorageId::location),
        );
        let rewritten = graph.insts.iter().any(|inst| {
            inst.block == def_inst.block
                && inst.ordinal > def_inst.ordinal
                && inst.ordinal < use_inst.ordinal
                && inst
                    .output
                    .and_then(|o| graph.value(o))
                    .and_then(|v| v.canonical_storage)
                    .is_some_and(|s| read_locations.contains(&s.location()))
        });
        if rewritten {
            rejected("a location the expression reads is written between definition and reader");
        } else {
            inlinable.insert(value.id);
        }
    }
    inlinable
}

/// The name of a machine expression's kind, for the inlining probe.
fn machine_expr_kind_name(kind: &r2ssa::MachineExprKind) -> &'static str {
    use r2ssa::MachineExprKind as Kind;
    match kind {
        Kind::Source { .. } => "Source",
        Kind::Constant { .. } => "Constant",
        Kind::MemoryRead { .. } => "MemoryRead",
        Kind::Arithmetic { .. } => "Arithmetic",
        Kind::Bitwise { .. } => "Bitwise",
        Kind::BitwiseNot { .. } => "BitwiseNot",
        Kind::Boolean { .. } => "Boolean",
        Kind::BooleanNot { .. } => "BooleanNot",
        Kind::Compare { .. } => "Compare",
        Kind::Copy { .. } => "Copy",
        Kind::Negate { .. } => "Negate",
        Kind::Select { .. } => "Select",
        Kind::Shift { .. } => "Shift",
        Kind::Cast { .. } => "Cast",
        _ => "other",
    }
}

/// Whether the renderer has a form for this expression at a reader.
///
/// The list is exactly what `materialize_machine_expr` can build, and it is
/// asked of every folding candidate: a plan that promises an inline the
/// renderer cannot produce refuses the function rather than declining to
/// fold.
///
/// `Constant` belongs here and was missing, which is why a literal-only value
/// was admitted by the duplicable rule above and then turned away by this
/// one. That is the whole of the literal-only declaration column: the plan
/// agreed the value was cheap to spell at each reader and then asked whether
/// a constant renders inline, and this said no. It is the first arm of the
/// materialiser.
///
/// A computation *over* constants is not a constant. `machine_expr_is_literal`
/// is true of `popcount(0xf0f0)`, because it asks only whether every leaf is
/// a constant; the materialiser has no form for a population count, so the
/// shape is still asked here and that expression still keeps its statement.
fn expression_renders_inline(kind: &r2ssa::MachineExprKind) -> bool {
    use r2ssa::MachineExprKind as Kind;
    matches!(
        kind,
        Kind::Constant { .. }
            | Kind::Arithmetic { .. }
            | Kind::Bitwise { .. }
            | Kind::BitwiseNot { .. }
            | Kind::Boolean { .. }
            | Kind::BooleanNot { .. }
            | Kind::Compare { .. }
            | Kind::Copy { .. }
            | Kind::Negate { .. }
            | Kind::Select { .. }
            | Kind::Shift { .. }
            | Kind::Cast { .. }
            | Kind::Extract { .. }
            | Kind::Concat { .. }
            | Kind::ArithmeticFlag { .. }
    )
}

/// The canonical forms admitted by `expression_renders_inline`.
///
/// Keep this list identical to `materialize_term`. A machine `Copy` imports as
/// its child and the three unary machine kinds import as the corresponding
/// unary term kinds, so the two enums do not have identical spellings.
fn term_renders_inline(kind: &r2rewrite::TermKind) -> bool {
    use r2rewrite::TermKind as Kind;
    matches!(
        kind,
        Kind::Leaf(_)
            | Kind::Literal(_)
            | Kind::Arithmetic { .. }
            | Kind::Negate(_)
            | Kind::Bitwise { .. }
            | Kind::BitwiseNot(_)
            | Kind::Boolean { .. }
            | Kind::BooleanNot(_)
            | Kind::Compare { .. }
            | Kind::Cast { .. }
            | Kind::Extract { .. }
            | Kind::Concat { .. }
            | Kind::Select { .. }
            | Kind::Shift { .. }
            | Kind::Flag { .. }
    )
}

/// The use and write cells the upstream certificates answer for before any
/// statement is rendered.
///
/// This is one statement of the rule, read by every consumer that has to agree
/// with it: the observation journal seeds its cells from `uses` and `writes`
/// and refuses a rendered marker that contradicts them; the binding plan
/// refuses to fold a value into a read listed in `read_elided_instructions`,
/// because a value folded into a read that never appears loses its rendered
/// occurrence; and a rewrite must leave an instruction alone when a
/// certificate has already said what it renders. Two independently written
/// statements of which cells a certificate elides were two answerers that could
/// drift, and when they drift the seal rejects a plan that is correct.
///
/// The two views are deliberately not one set. The journal needs the reason
/// per use, and is exact per operand: a machine return control certificate
/// elides only the operand sites it names, and a stack-geometry operand that is
/// also a memory address keeps its rendered occurrence. The binding plan needs
/// only to know that an instruction's reads are not rendered, and it is asked
/// per instruction, including instructions -- a dead frame-slot store -- whose
/// cells the effect ledger answers for rather than these maps.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CertificateElidedCells {
    pub(crate) uses: BTreeMap<UseSite, ElisionReason>,
    pub(crate) writes: BTreeMap<InstId, ElisionReason>,
    pub(crate) read_elided_instructions: BTreeSet<InstId>,
}

/// Why the certificates could not be turned into cells.
///
/// Each variant names the same condition the observation journal reports for
/// it; the journal maps these onto its own error type without reinterpreting
/// them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CertificateElidedCellsError {
    InvalidWrite(InstId),
    InvalidValue(ValueId),
    ConflictingUse(UseSite),
    ConflictingWrite(InstId),
}

fn insert_elided_use(
    uses: &mut BTreeMap<UseSite, ElisionReason>,
    site: UseSite,
    reason: ElisionReason,
) -> Result<(), CertificateElidedCellsError> {
    match uses.insert(site, reason) {
        Some(existing) if existing != reason => {
            if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                eprintln!(
                    "conflicting use {site:?}: certificate reason {existing:?}, new reason {reason:?}"
                );
            }
            Err(CertificateElidedCellsError::ConflictingUse(site))
        }
        _ => Ok(()),
    }
}

fn insert_elided_write(
    writes: &mut BTreeMap<InstId, ElisionReason>,
    inst: InstId,
    reason: ElisionReason,
) -> Result<(), CertificateElidedCellsError> {
    match writes.insert(inst, reason) {
        Some(existing) if existing != reason => {
            Err(CertificateElidedCellsError::ConflictingWrite(inst))
        }
        _ => Ok(()),
    }
}

/// The cells the certificates of `source` elide, in the order the certificates
/// are consulted.
///
/// Order matters where domains overlap: an earlier machine or frame
/// certificate wins deterministically, and the unobserved-value domain only
/// fills cells nothing earlier has claimed. The `projection` is the machine
/// projection the plan was built from; it decides which stack-geometry
/// operands are memory addresses that keep their own rendered occurrence.
pub(crate) fn certificate_elided_cells(
    source: &r2ssa::SsaArtifact,
    projection: &r2ssa::MachineProjection,
) -> Result<CertificateElidedCells, CertificateElidedCellsError> {
    let graph = source.graph();
    let certificates = source.certificates();
    let mut uses = BTreeMap::new();
    let mut writes = BTreeMap::new();
    for certificate in certificates.stack_frame_round_trips.values() {
        for inst in &certificate.insts {
            let definition = graph
                .inst(*inst)
                .ok_or(CertificateElidedCellsError::InvalidWrite(*inst))?;
            for input_idx in 0..definition.inputs.len() {
                let site = UseSite {
                    inst: *inst,
                    input_idx,
                };
                insert_elided_use(&mut uses, site, ElisionReason::StackFrame)?;
            }
            if definition.output.is_some() {
                insert_elided_write(&mut writes, *inst, ElisionReason::StackFrame)?;
            }
        }
    }
    for certificate in certificates.machine_return_controls.values() {
        for site in &certificate.uses {
            insert_elided_use(&mut uses, *site, ElisionReason::ReturnControl)?;
        }
        for inst in &certificate.insts {
            let definition = graph
                .inst(*inst)
                .ok_or(CertificateElidedCellsError::InvalidWrite(*inst))?;
            if definition.output.is_some() {
                insert_elided_write(&mut writes, *inst, ElisionReason::ReturnControl)?;
            }
        }
    }
    for site in &certificates.stack_geometry.uses {
        // A stack-root value has no standalone C occurrence, but an exact
        // stack-object address operand still has its own contextual per-use
        // projection. The value and use ledgers are independent: seed only
        // geometry uses that disappear with their defining operation, and let
        // the rendered memory-address marker account for the surviving
        // operand.
        if matches!(
            projection.use_disposition(*site),
            Some(r2ssa::MachineUseDisposition::MemoryAddress(_))
        ) {
            continue;
        }
        insert_elided_use(&mut uses, *site, ElisionReason::DeadStackBase)?;
    }
    for inst in &certificates.stack_geometry.insts {
        let definition = graph
            .inst(*inst)
            .ok_or(CertificateElidedCellsError::InvalidWrite(*inst))?;
        if definition.output.is_some() {
            insert_elided_write(&mut writes, *inst, ElisionReason::DeadStackBase)?;
        }
    }
    // The SSA liveness owner publishes the complete pure domain outside the
    // transitive observation slice. Seed non-phi operations here; dead merges
    // keep their more specific reason below. Earlier machine/frame
    // certificates win deterministically when domains overlap.
    let unobserved = source.unobserved_merges();
    for site in unobserved.unobserved_uses() {
        if graph
            .inst(site.inst)
            .is_some_and(|inst| matches!(inst.payload, r2ssa::InstPayload::Phi { .. }))
        {
            continue;
        }
        uses.entry(*site).or_insert(ElisionReason::UnobservedValue);
    }
    for inst in unobserved.unobserved_insts() {
        let definition = graph
            .inst(*inst)
            .ok_or(CertificateElidedCellsError::InvalidWrite(*inst))?;
        if matches!(definition.payload, r2ssa::InstPayload::Phi { .. }) {
            continue;
        }
        if definition.output.is_some() {
            writes
                .entry(*inst)
                .or_insert(ElisionReason::UnobservedValue);
        }
    }
    for value in unobserved.iter() {
        let inst = graph
            .def_inst(value)
            .ok_or(CertificateElidedCellsError::InvalidValue(value))?;
        let definition = graph
            .inst(inst)
            .ok_or(CertificateElidedCellsError::InvalidWrite(inst))?;
        if !matches!(definition.payload, r2ssa::InstPayload::Phi { .. })
            || definition.output != Some(value)
        {
            return Err(CertificateElidedCellsError::InvalidWrite(inst));
        }
        writes.insert(inst, ElisionReason::UnobservedMerge);
        for input_idx in 0..definition.inputs.len() {
            uses.insert(UseSite { inst, input_idx }, ElisionReason::UnobservedMerge);
        }
    }
    for site in super::certified_return_control_sites(source) {
        // A merge the analysis already answered for keeps its answer. The link
        // register reaches a return through phis that merge it with itself,
        // and once the certificate covers the register those phi operands are
        // named twice -- as an unobserved merge and as return control. Both
        // say the same thing, and calling that a conflict refused every
        // function whose return address survives a branch.
        if uses.get(&site) == Some(&ElisionReason::UnobservedMerge) {
            continue;
        }
        insert_elided_use(&mut uses, site, ElisionReason::ReturnControl)?;
    }
    // Instructions the certificate took over from the prologue are shared with
    // whatever else describes them: one `stp x29, x30` is the frame's setup and
    // the return address's save at once, and one save serves every return.
    // Where such an instruction is already accounted for, that account stands;
    // both say it renders nothing, and treating the second one as a
    // contradiction refused the whole function.
    let shared = super::certified_return_control_absorbed_insts(source);
    for inst in super::certified_return_control_insts(source) {
        let definition = graph
            .inst(inst)
            .ok_or(CertificateElidedCellsError::InvalidWrite(inst))?;
        if shared.contains(&inst) {
            if definition.output.is_some() {
                writes.entry(inst).or_insert(ElisionReason::ReturnControl);
            }
            for input_idx in 0..definition.inputs.len() {
                uses.entry(UseSite { inst, input_idx })
                    .or_insert(ElisionReason::ReturnControl);
            }
            continue;
        }
        if definition.output.is_some() {
            insert_elided_write(&mut writes, inst, ElisionReason::ReturnControl)?;
        }
        // The instruction renders nothing, so it reads nothing. Its write was
        // already accounted on that ground and its operands stand on the same
        // one: an occurrence inside a statement no structured form emits is
        // not a read. On AArch64 the return address arrives through a copy of
        // the link register and the copy's operand is control-only in its own
        // right, so this was never needed; on amd64 `ret` lifts to a load of
        // the return address through the stack pointer, and the stack pointer
        // is read elsewhere for ordinary reasons, so nothing else could ever
        // close that cell.
        for input_idx in 0..definition.inputs.len() {
            insert_elided_use(
                &mut uses,
                UseSite { inst, input_idx },
                ElisionReason::ReturnControl,
            )?;
        }
    }
    for site in super::certified_direct_control_target_sites(source) {
        insert_elided_use(&mut uses, site, ElisionReason::DirectControlTarget)?;
    }
    // A direct call names its callee. The name comes from the symbol table,
    // not from any object the function holds, so the operand's occurrence is
    // not a read and the value it names is elided beside it.
    for site in super::certified_direct_call_target_sites(source) {
        insert_elided_use(&mut uses, site, ElisionReason::DirectCallTarget)?;
    }
    for inst in super::certified_call_return_address_insts(source) {
        let definition = graph
            .inst(inst)
            .ok_or(CertificateElidedCellsError::InvalidWrite(inst))?;
        if definition.output.is_some() {
            insert_elided_write(&mut writes, inst, ElisionReason::CallReturnAddress)?;
        }
        for input_idx in 0..definition.inputs.len() {
            insert_elided_use(
                &mut uses,
                UseSite { inst, input_idx },
                ElisionReason::CallReturnAddress,
            )?;
        }
    }
    for inst in super::certified_direct_call_target_insts(source) {
        let definition = graph
            .inst(inst)
            .ok_or(CertificateElidedCellsError::InvalidWrite(inst))?;
        if definition.output.is_some() {
            insert_elided_write(&mut writes, inst, ElisionReason::DirectCallTarget)?;
        }
        for input_idx in 0..definition.inputs.len() {
            insert_elided_use(
                &mut uses,
                UseSite { inst, input_idx },
                ElisionReason::DirectCallTarget,
            )?;
        }
    }
    Ok(CertificateElidedCells {
        uses,
        writes,
        read_elided_instructions: certified_elided_read_instructions(source),
    })
}

/// Merges that have no C operation of their own because every edge is an
/// identity.
///
/// A materialised merge edge whose incoming value and the merge's output are
/// one renderer binding renders as `x = x`. When every edge of a merge is like
/// that, the merge performs nothing: whatever wrote the binding has already
/// written it.
///
/// The merge's value stays `Bound` all the same, because its readers need a
/// name and the plan is what promises one. What the merge loses is a statement
/// of its own, not an object. Saying it were elided would make the ledger
/// claim the opposite of what happens: the value is rendered, under the
/// binding's name, by whatever wrote that binding.
///
/// `group_of` names whichever object a value belongs to on the caller's side --
/// the plan passes its `BindingId`, the seal its own component index. The
/// question is whether two values share one object, not what that object is
/// called, so neither derivation has to agree with the other about names in
/// order to agree about the answer.
///
/// A version-0 input is excluded, mirroring the journal's own exclusion: such
/// an input has no defining statement, so its edge copy is the only place the
/// value is written and is therefore rendered. Removing the exclusion is
/// tempting -- the copy spells `x = x` and the binding has a name already --
/// but a live-in register that is not a parameter has no declaration to be
/// rendered by, and placement then reports the object read before it is
/// assigned. Whether such a value should get an entry declaration is the
/// open question; until it is answered the edge copy is what defines it.
pub(super) fn identity_merge_values(
    graph: &SsaGraph,
    group_of: impl Fn(ValueId) -> Option<u32>,
) -> BTreeSet<ValueId> {
    let mut merges = BTreeSet::new();
    for inst in &graph.insts {
        if !matches!(inst.payload, r2ssa::InstPayload::Phi { .. }) || inst.inputs.is_empty() {
            continue;
        }
        let Some(output) = inst.output else {
            continue;
        };
        let Some(output_group) = group_of(output) else {
            continue;
        };
        if inst.inputs.iter().all(|input| {
            group_of(*input) == Some(output_group)
                && graph
                    .value(*input)
                    .is_some_and(|value| value.var.version != 0)
        }) {
            merges.insert(output);
        }
    }
    merges
}
