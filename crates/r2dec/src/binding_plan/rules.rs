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
    certified_direct_control_target_values, certified_elided_read_instructions,
    certified_return_control_values, certified_stack_frame_values, certified_stack_geometry_values,
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
    let inlinable = inlinable_values(source);
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
                && !inlinable.contains(&value.id)
        })
        .collect())
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
/// Casts follow the declaration -- `source_type_for_var` asks the declaration
/// before the certified hint -- so asserting here changes the operands too,
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
fn admit_declaration(ty: r2types::CTypeLike, width_bits: u32, ptr_bits: u32) -> r2types::CTypeLike {
    let admissible = match &ty {
        r2types::CTypeLike::Pointer(_) => width_bits == ptr_bits,
        r2types::CTypeLike::Int { bits, .. } => *bits == width_bits,
        r2types::CTypeLike::Float(bits) => *bits == width_bits,
        _ => false,
    };
    if admissible {
        ty
    } else {
        r2types::CTypeLike::machine_bits(width_bits)
    }
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
    match ty {
        r2types::CTypeLike::Int {
            bits,
            signedness: r2types::Signedness::Unsigned,
        } if *bits <= 128 => Some(*bits),
        r2types::CTypeLike::Int {
            bits,
            signedness: r2types::Signedness::Signed,
        } if *bits <= 128 => Some(*bits),
        r2types::CTypeLike::Float(bits) if *bits <= 128 => Some(*bits),
        r2types::CTypeLike::Pointer(_) => Some(ptr_bits),
        r2types::CTypeLike::BitVector(bits) if *bits > 128 => Some(*bits),
        _ => None,
    }
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

pub(super) fn inlinable_values(source: &r2ssa::SsaArtifact) -> BTreeSet<ValueId> {
    let graph = source.graph();
    let Ok(projection) = r2ssa::MachineProjection::from_artifact(source) else {
        return BTreeSet::new();
    };
    let mut expr_by_value = std::collections::BTreeMap::new();
    for entity in projection.entities() {
        expr_by_value.insert(entity.output().value(), entity.root());
    }
    let elided_reads = certified_elided_read_instructions(source);
    let mut inlinable = BTreeSet::new();
    for value in &graph.values {
        let [use_site] = graph.use_sites(value.id) else {
            continue;
        };
        let renderable = expr_by_value
            .get(&value.id)
            .and_then(|root| projection.expr(*root))
            .is_some_and(|expr| expression_renders_inline(expr.kind()));
        if !renderable {
            continue;
        }
        let Some(definition) = graph.def_inst(value.id) else {
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
            continue;
        }
        let Some(def_inst) = graph.inst(definition) else {
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
            continue;
        }
        // The read this expression would move into has to be a read that
        // actually appears. A value whose one use sits in an instruction a
        // certificate elides -- the prologue's `push rbp` is a certified frame
        // round trip -- disappears together with that instruction, and the
        // effect its definition answered for is then owed by nobody. The
        // ledger scores that as a refusal and the function falls back to no
        // decompilation at all, which is what `murmur3_32` and `xxhash32` did.
        if elided_reads.contains(&use_site.inst) {
            continue;
        }
        let Some(use_inst) = graph.inst(use_site.inst) else {
            continue;
        };
        // A merge reads its operands on edges, not at a position in a block, so
        // comparing ordinals against one says nothing and moving a computation
        // into a merge operand moves it across the edge that operand arrives
        // on. `crc32_bitwise` and `pearson` are the cases: their loop carriers
        // are merges, and folding into them computed the wrong answer while
        // every other check passed.
        if matches!(use_inst.payload, r2ssa::InstPayload::Phi { .. }) {
            continue;
        }
        if def_inst.block != use_inst.block || def_inst.ordinal >= use_inst.ordinal {
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
        if !rewritten {
            inlinable.insert(value.id);
        }
    }
    inlinable
}

fn expression_renders_inline(kind: &r2ssa::MachineExprKind) -> bool {
    use r2ssa::MachineExprKind as Kind;
    matches!(
        kind,
        Kind::Arithmetic { .. }
            | Kind::Bitwise { .. }
            | Kind::BitwiseNot { .. }
            | Kind::Boolean { .. }
            | Kind::BooleanNot { .. }
            | Kind::Compare { .. }
            | Kind::Copy { .. }
            | Kind::Negate { .. }
            | Kind::Select { .. }
            | Kind::Shift { .. }
    )
}
