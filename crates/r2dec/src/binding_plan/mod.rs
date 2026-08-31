//! Typed boundary between canonical SSA facts and C lowering.
//!
//! Use and write geometry remain owned by the validated upstream
//! [`MachineProjection`]; this module delegates to that table instead of
//! copying a second answer into renderer-owned storage.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::CType;
use r2ssa::span::SpanId;
use r2ssa::{
    InstId, MachineExprId, MachineExprKind, MachineProjection, MachineUseDisposition,
    MachineWriteDisposition, MachineWriteProjection, SemanticId, SsaArtifactAuthority, UseSite,
    ValueId,
};
use r2types::SourceOwnedFunctionFacts;

/// Dense identity of one C object in a [`BindingPlan`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct BindingId(u32);

impl BindingId {
    /// Resolve an index in the sealed plan's dense binding domain.
    ///
    /// Callers must still validate the result against `BindingPlan::binding` or
    /// `BindingPlan::binding_count`; this conversion only prevents truncation.
    pub(crate) fn from_dense_index(index: usize) -> Option<Self> {
        u32::try_from(index).ok().map(Self)
    }

    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Opaque token minted only by this module's sealing pass after it has checked
/// the exact bound member set against the sorted upstream certificate sources.
/// It never repeats a machine location or stores a parallel member list.
#[derive(Debug, Clone, PartialEq, Eq)]
struct BindingCertificate {
    sources: Box<[BindingCertificateSource]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum BindingCertificateSource {
    Singleton,
    StorageSpan(SpanId),
    CertifiedEntity(SemanticId),
}

/// Declaration role proved by the same sealed facts that own the binding.
///
/// This is deliberately typed and name-free. In particular, a parameter is
/// externally declared because an exact source ABI slot owns it, never because
/// its presentation spelling resembles an argument register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BindingRole {
    Local,
    Parameter {
        slot: u32,
    },
    StackObject {
        object: r2ssa::ObjectId,
    },
    /// A caller-supplied value that no convention argument slot claims.
    ///
    /// SSA renaming gives version 0 to a read with no prior definition in this
    /// function, so such a value is supplied from outside by construction. The
    /// scratch registers a compiler reads before writing land here -- `xor ecx,
    /// ecx` reads `ecx` even though its result does not depend on it -- and so
    /// does any incoming register outside the convention's argument slots.
    ///
    /// The object therefore exists from function entry holding an indeterminate
    /// value, exactly as the machine does. Treating it as a local and demanding
    /// an assignment before its first read asks for a definition that cannot
    /// exist, which refused the whole function for saying what the program
    /// actually does.
    EntryValue,
}

/// One rendered C object. The name hint is presentation only, never identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Binding {
    declaration_type: CType,
    certificate: BindingCertificate,
    presentation_name_hint: Option<String>,
    /// Whether some member of this binding is supplied by the caller.
    ///
    /// Derived from the graph -- a value with no defining instruction -- and
    /// re-derived independently by the sealing oracle, never from a name or a
    /// register spelling.
    caller_supplied: bool,
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
    literal: MachineExprId,
}

/// Proof that an exact upstream fact authorizes a value to have no rendered C
/// occurrence. The seal re-derives the reason-specific fact from the same SSA
/// authority; this token is not itself a second semantic answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ValueElisionProof {
    authority: SsaArtifactAuthority,
    value: ValueId,
}

/// Typed reason that a value cannot be represented honestly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ValueRefusal {
    MissingBindingCertificate { value: ValueId },
    MissingLiteralProjection { value: ValueId },
    IncoherentUseProjection { site: UseSite },
    IncoherentWriteProjection { value: ValueId },
    UnsupportedDeclarationWidth { value: ValueId, width_bits: u32 },
}

const fn declaration_width_is_supported(width_bits: u32) -> bool {
    matches!(width_bits, 8 | 16 | 32 | 64 | 128 | 256 | 512)
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
        proof: ValueElisionProof,
    },
    Refused {
        reason: ValueRefusal,
    },
}

/// Exact graph uses that consume a source-certified machine return target.
///
/// This is a per-use answer. A return-address value may also have an ordinary
/// program use, which must remain renderable even though the `Return` operand
/// itself is machine control and has no C occurrence.
/// The exact `Return` uses of a certified return address.
fn certified_return_transfer_sites(source: &r2ssa::SsaArtifact) -> BTreeSet<UseSite> {
    let graph = source.graph();
    source
        .facts()
        .boundaries
        .returns
        .iter()
        .filter_map(|(at, boundary)| {
            let fact = boundary.return_address?;
            let site = UseSite {
                inst: *at,
                input_idx: 0,
            };
            (boundary.at == *at
                && graph.inst(*at).is_some_and(|inst| {
                    matches!(
                        inst.payload,
                        r2ssa::InstPayload::Op(r2ssa::SSAOp::Return { .. })
                    ) && inst.inputs.as_slice() == [fact.value]
                })
                && graph.use_sites(fact.value).contains(&site))
            .then_some(site)
        })
        .collect()
}

/// Return-target values whose complete use domain is machine return control.
///
/// Only these values may be globally elided from the binding domain. The
/// per-use accounting above remains independent so a mixed-use value stays
/// bound while its exact `Return` use is still justified as non-rendered.
/// Every use that only ever carries a return address to its return.
///
/// The transfer itself, and the copies a return address reaches it through.
/// AArch64's `ret` lifts to a copy of the link register into the program
/// counter and a return on that, so the copy's read of the link register is
/// as much return control as the return's own read, and neither is rendered:
/// the structured form says `return`.
pub(super) fn certified_return_control_sites(source: &r2ssa::SsaArtifact) -> BTreeSet<UseSite> {
    let graph = source.graph();
    let mut sites = certified_return_transfer_sites(source);
    for value in certified_return_control_values(source) {
        sites.extend(graph.use_sites(value).iter().copied());
    }
    sites
}

/// The instructions a return-control certificate answers for.
///
/// Two kinds. The copy that moves a link register into the program counter
/// defines a value the structured form never emits, so its write is accounted
/// here rather than being left for a rendering that will not happen. And the
/// store that saved the return address in the first place, where the
/// certificate absorbed it: that write has no reader once the reload is
/// elided, and leaving it out of this set is what rendered it as an assignment
/// to a variable no one reads.
pub(super) fn certified_return_control_insts(source: &r2ssa::SsaArtifact) -> BTreeSet<InstId> {
    let graph = source.graph();
    let mut insts = certified_return_control_values(source)
        .into_iter()
        .filter_map(|value| graph.def_inst(value))
        .collect::<BTreeSet<_>>();
    insts.extend(
        source
            .certificates()
            .machine_return_controls
            .values()
            .flat_map(|certificate| certificate.insts.iter().copied()),
    );
    insts
}

/// The instructions a return-control certificate took over from the prologue.
///
/// A save is shared -- with the frame certificate, when one `stp` does both
/// jobs, and with every other return in the function. So where an account of
/// these instructions already exists, this certificate agrees with it rather
/// than contradicting it, and the journal keeps the one that was there.
pub(super) fn certified_return_control_absorbed_insts(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<InstId> {
    source
        .certificates()
        .machine_return_controls
        .values()
        .flat_map(|certificate| certificate.absorbed_insts.iter().copied())
        .collect()
}

/// The stack slots a return-control certificate claims.
///
/// A slot whose only write is the prologue's save of the return address and
/// whose only read is the reload the certificate already answers for is not a
/// local. Both binding derivations ask this the same way, so it is answered
/// once.
pub(super) fn certified_return_control_stack_objects(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<r2ssa::ObjectId> {
    source
        .certificates()
        .machine_return_controls
        .values()
        .filter_map(|certificate| certificate.stack_object)
        .collect()
}

pub(super) fn certified_return_control_values(source: &r2ssa::SsaArtifact) -> BTreeSet<ValueId> {
    let graph = source.graph();
    let sites = certified_return_transfer_sites(source);
    let mut values = sites
        .iter()
        .filter_map(|site| graph.inst(site.inst)?.inputs.get(site.input_idx).copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|value| {
            let uses = graph.use_sites(*value);
            !uses.is_empty() && uses.iter().all(|site| sites.contains(site))
        })
        .collect::<BTreeSet<_>>();
    values.extend(
        source
            .certificates()
            .machine_return_controls
            .values()
            .flat_map(|certificate| certificate.values.iter().copied()),
    );

    // Follow the copies a return address arrives through.
    //
    // AArch64's `ret` lifts to a copy of the link register into the program
    // counter and then a return on that. The return's own input is certified,
    // but the link register one copy upstream is not, so it was bound to an
    // object no rendering ever emitted and the seal refused the function for a
    // value nothing rendered.
    //
    // A value every one of whose uses is a copy producing something already
    // control-only is itself control-only: it reaches nothing but the return.
    loop {
        let mut added = false;
        for value in &graph.values {
            if values.contains(&value.id) {
                continue;
            }
            let uses = graph.use_sites(value.id);
            if uses.is_empty() {
                continue;
            }
            let reaches_only_control = uses.iter().all(|site| {
                graph.inst(site.inst).is_some_and(|inst| {
                    matches!(
                        inst.payload,
                        r2ssa::InstPayload::Op(r2ssa::SSAOp::Copy { .. })
                    ) && inst.output.is_some_and(|output| values.contains(&output))
                })
            });
            if reaches_only_control {
                values.insert(value.id);
                added = true;
            }
        }
        if !added {
            break;
        }
    }
    values
}

/// Exact direct-branch target uses already represented by CFG topology.
///
/// `Branch` and `CBranch` target operand zero qualify, and so does a
/// `BranchInd` whose switch is certified: the case topology is what expresses
/// it. Unresolved indirect branches, call, predicate, and return operands have
/// different rendering contracts.
pub(super) fn certified_direct_control_target_sites(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<UseSite> {
    let graph = source.graph();
    graph
        .insts
        .iter()
        .filter_map(|inst| {
            let target = match &inst.payload {
                r2ssa::InstPayload::Op(
                    r2ssa::SSAOp::Branch { target } | r2ssa::SSAOp::CBranch { target, .. },
                ) => target,
                // A resolved jump table is control too. The structured form
                // prints `switch` on the selector and puts each case where its
                // block sits, so the computed target it dispatches through is
                // expressed by the topology exactly as a direct branch's is.
                // Only where the switch is certified: an indirect branch nobody
                // resolved keeps its ordinary rendering contract.
                r2ssa::InstPayload::Op(r2ssa::SSAOp::BranchInd { target }) => {
                    let block_addr = graph.block(inst.block).map(|block| block.addr);
                    if !block_addr
                        .is_some_and(|addr| source.certificates().switches.contains_key(&addr))
                    {
                        return None;
                    }
                    target
                }
                _ => return None,
            };
            let value = graph.value_id_for_var(target)?;
            let site = UseSite {
                inst: inst.id,
                input_idx: 0,
            };
            (inst.inputs.first().copied() == Some(value) && graph.use_sites(value).contains(&site))
                .then_some(site)
        })
        .collect()
}

/// Exact direct-call target uses the call expression renders as the callee.
///
/// Only `Call` operand zero qualifies. `CallInd`'s target is a value the
/// program computed and reads, and it keeps its ordinary rendering contract.
pub(super) fn certified_direct_call_target_sites(source: &r2ssa::SsaArtifact) -> BTreeSet<UseSite> {
    let graph = source.graph();
    graph
        .insts
        .iter()
        .filter_map(|inst| {
            let r2ssa::InstPayload::Op(r2ssa::SSAOp::Call { target }) = &inst.payload else {
                return None;
            };
            let value = graph.value_id_for_var(target)?;
            let site = UseSite {
                inst: inst.id,
                input_idx: 0,
            };
            (inst.inputs.first().copied() == Some(value) && graph.use_sites(value).contains(&site))
                .then_some(site)
        })
        .collect()
}

/// Direct-call target values whose complete use domain is the callee's name.
pub(super) fn certified_direct_call_target_values(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<ValueId> {
    let graph = source.graph();
    let sites = certified_direct_call_target_sites(source);
    let mut values = sites
        .iter()
        .filter_map(|site| graph.inst(site.inst)?.inputs.get(site.input_idx).copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|value| {
            let uses = graph.use_sites(*value);
            !uses.is_empty() && uses.iter().all(|site| sites.contains(site))
        })
        .collect::<BTreeSet<_>>();

    // Follow the copies a callee's address arrives through, for the same
    // reason the return-address closure above does. A lift that materializes
    // the target into a temporary first leaves the call's own operand
    // certified and the copy one step upstream not, and that copy then lowered
    // to an assignment of an object the plan had already elided.
    loop {
        let mut added = false;
        for value in &graph.values {
            if values.contains(&value.id) {
                continue;
            }
            let uses = graph.use_sites(value.id);
            if uses.is_empty() {
                continue;
            }
            let reaches_only_target = uses.iter().all(|site| {
                graph.inst(site.inst).is_some_and(|inst| {
                    matches!(
                        inst.payload,
                        r2ssa::InstPayload::Op(r2ssa::SSAOp::Copy { .. })
                    ) && inst.output.is_some_and(|output| values.contains(&output))
                })
            });
            if reaches_only_target {
                values.insert(value.id);
                added = true;
            }
        }
        if !added {
            break;
        }
    }
    values
}

/// Definitions whose whole result is a callee's address on its way to the call.
///
/// The copy that materializes a call target renders nothing -- the call spells
/// the callee's name -- so its write and its operands are accounted here rather
/// than left for a statement that will not be emitted.
pub(super) fn certified_direct_call_target_insts(source: &r2ssa::SsaArtifact) -> BTreeSet<InstId> {
    let graph = source.graph();
    certified_direct_call_target_values(source)
        .into_iter()
        .filter_map(|value| graph.def_inst(value))
        .collect()
}

/// The stores that push a call's return address, and the values they consume.
///
/// A `call` on amd64 subtracts from the stack pointer and writes the address of
/// the instruction after it, and Sleigh lifts both. The structured form says
/// `f(...)`, which is the transfer; rendering the push beside it emits the
/// machine's bookkeeping as if it were program text, through a stack pointer
/// the function never assigned. That is where `murmur3_32`'s
/// `RSP_0 = RSP_0 - 8; *(int64_t*)RSP_0 = 0x1000009ce;` comes from.
///
/// A store qualifies only when the value it writes is the constant address the
/// call site falls through to, and it precedes that call in its own block.
/// Nothing else in a function stores its own continuation address.
pub(super) fn certified_call_return_address_insts(source: &r2ssa::SsaArtifact) -> BTreeSet<InstId> {
    let graph = source.graph();
    let Some(stack_pointer) = source.machine_context().stack_pointer_carrier() else {
        return BTreeSet::new();
    };
    let mut insts = BTreeSet::new();
    for certificate in source.certificates().callsites.values() {
        let Some(call) = graph.inst(certificate.at) else {
            continue;
        };
        // The nearest store before the call that writes a bare constant
        // through the stack pointer. Sleigh lifts `call` as a stack-pointer
        // decrement, this store of the address to come back to, and the
        // transfer; nothing else in a function stores a literal at the stack
        // pointer immediately before calling.
        let push = graph
            .insts
            .iter()
            .filter(|candidate| candidate.block == call.block && candidate.ordinal < call.ordinal)
            .filter(|candidate| {
                let r2ssa::InstPayload::Op(r2ssa::SSAOp::Store { val, .. }) = &candidate.payload
                else {
                    return false;
                };
                let through_stack_pointer =
                    candidate.inputs.first().is_some_and(|address: &ValueId| {
                        graph
                            .value(*address)
                            .and_then(|value| value.canonical_storage)
                            .is_some_and(|storage| storage.location() == stack_pointer.location())
                    });
                val.constant_bits().is_some() && through_stack_pointer
            })
            .max_by_key(|candidate| candidate.ordinal);
        if let Some(push) = push {
            insts.insert(push.id);
        }
    }
    insts
}

/// The return addresses those pushes write.
///
/// The constant is the machine's continuation address. Nothing in the C names
/// it, because the call statement is the transfer, so once the push is elided
/// the literal has no occurrence and no other answerer.
pub(super) fn certified_call_return_address_values(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<ValueId> {
    let graph = source.graph();
    let pushes = certified_call_return_address_insts(source);
    pushes
        .iter()
        .filter_map(|inst| graph.inst(*inst)?.inputs.get(1).copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|value| {
            let uses = graph.use_sites(*value);
            !uses.is_empty() && uses.iter().all(|site| pushes.contains(&site.inst))
        })
        .collect()
}

/// Accesses to a frame slot this function writes and never reads.
///
/// A store into memory is an effect, and the ledger holds the rendering to it,
/// which is why a dead frame slot cannot simply be dropped: the obligation
/// would go unanswered. But observable means observable from outside, and a
/// `CalleeStackAllocationCertificate` is the proof that the object lies wholly
/// inside storage this function owns at every access. Where every one of those
/// accesses is a write, nothing here or anywhere else can read what was stored,
/// and the store has no meaning the C has to carry.
///
/// This is what left `stack_m48` and its neighbours declared, assigned and
/// unused in `murmur3_32` and `xxhash32` at -O0: the slots an argument is
/// spilled into and then read back out of through the object rather than the
/// slot.
pub(super) fn certified_dead_frame_slot_accesses(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<(u64, usize)> {
    let certificates = source.certificates();
    let mut accesses = BTreeSet::new();
    for slot in certificates.stack_slots.values() {
        let Some(allocation) = slot.callee_allocation.as_ref() else {
            continue;
        };
        let Some(owned) = allocation
            .accesses
            .iter()
            .map(|access| certificates.memory_accesses.get(access))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        if owned.is_empty() || owned.iter().any(|access| !access.is_write) {
            continue;
        }
        accesses.extend(
            owned
                .iter()
                .map(|access| (access.block_addr, access.op_index)),
        );
    }
    accesses
}

/// Direct-control target values whose complete use domain is CFG topology.
pub(super) fn certified_direct_control_target_values(
    source: &r2ssa::SsaArtifact,
) -> BTreeSet<ValueId> {
    let graph = source.graph();
    let sites = certified_direct_control_target_sites(source);
    sites
        .iter()
        .filter_map(|site| graph.inst(site.inst)?.inputs.get(site.input_idx).copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|value| {
            let uses = graph.use_sites(*value);
            !uses.is_empty() && uses.iter().all(|site| sites.contains(site))
        })
        .collect()
}

/// Values whose complete use domain belongs to an exact upstream frame
/// save/reload certificate. The certificate collector already proved the
/// closure; this is only its renderer-facing projection.
pub(super) fn certified_stack_frame_values(source: &r2ssa::SsaArtifact) -> BTreeSet<ValueId> {
    source
        .certificates()
        .stack_frame_round_trips
        .values()
        .flat_map(|certificate| certificate.values.iter().copied())
        .collect()
}

pub(super) fn certified_stack_geometry_values(source: &r2ssa::SsaArtifact) -> &BTreeSet<ValueId> {
    &source.certificates().stack_geometry.values
}

/// Failure of declaration placement or reaching-definition validation.
///
/// Placement itself is deliberately absent: it is derived from the sealed
/// structured-region artifact immediately before AST emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum PlacementRead {
    Use(UseSite),
    CertifiedValue { value: ValueId, at: InstId },
    StackAccess(r2ssa::StructuredAccessId),
    PreservedCarrierWrite(InstId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementRefusal {
    NoDominatingRegion {
        binding: BindingId,
    },
    MissingDefinition {
        binding: BindingId,
    },
    ReadBeforeAssignment {
        binding: BindingId,
        read: PlacementRead,
    },
    UnprovableExecutionOrder {
        binding: BindingId,
    },
}

/// Typed disposition of an addressable stack object. Stack objects do not have
/// SSA-value membership, so they occupy their own plan domain instead of being
/// reconstructed from an offset or a rendered local name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StackObjectDisposition {
    Bound {
        binding: BindingId,
    },
    Elided {
        reason: r2ssa::ledger::ElisionReason,
    },
    Refused {
        reason: StackObjectRefusal,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StackObjectRefusal {
    MissingSourceIdentity {
        object: r2ssa::ObjectId,
    },
    UnclassifiedSourceRole {
        object: r2ssa::ObjectId,
    },
    MissingWidth {
        object: r2ssa::ObjectId,
    },
    InvalidWidth {
        object: r2ssa::ObjectId,
        size_bytes: u32,
    },
    ParameterHomeUnavailable {
        object: r2ssa::ObjectId,
        parameter_index: u32,
    },
    ParameterHomeWidthMismatch {
        object: r2ssa::ObjectId,
        parameter_index: u32,
        slot_width_bits: u32,
        parameter_width_bits: u32,
    },
}

/// Exact disposition of one source-certified ABI parameter slot.
///
/// The width is the formal carrier width in bits. It is kept separate from a
/// reused binding's machine-carrier declaration width because an exact use may
/// project a narrow formal from a wider canonical register carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParameterDisposition {
    Bound { binding: BindingId, width_bits: u32 },
    Refused { reason: ParameterRefusal },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParameterRefusal {
    MissingWidth {
        entity: SemanticId,
        slot: u32,
    },
    InvalidWidth {
        entity: SemanticId,
        slot: u32,
        size_bytes: u32,
    },
    UnsupportedWidth {
        entity: SemanticId,
        slot: u32,
        width_bits: u32,
    },
    ConflictingSlotOwnership {
        slot: u32,
        first: SemanticId,
        second: SemanticId,
    },
    ConflictingEntityOwnership {
        entity: SemanticId,
        expected_slot: u32,
        claimed_slot: u32,
    },
    MissingValueBinding {
        entity: SemanticId,
        slot: u32,
        value: ValueId,
    },
    ConflictingBindingOwnership {
        binding: BindingId,
        first_slot: u32,
        second_slot: u32,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BindingPlanSourceMismatch {
    Authority,
    MachineProjection(r2ssa::MachineBuildError),
    ValueTopology {
        index: usize,
        value: ValueId,
    },
    DispositionCount {
        expected: usize,
        actual: usize,
    },
    BindingCount {
        expected: usize,
        actual: usize,
    },
    InvalidBindingReference {
        value: ValueId,
        binding: BindingId,
    },
    CertificateMembership {
        binding: BindingId,
    },
    DeclarationWidth {
        binding: BindingId,
    },
    InvalidLiteralInline {
        value: ValueId,
    },
    InvalidElisionProof {
        value: ValueId,
    },
    UnexpectedValueDisposition {
        value: ValueId,
    },
    StackObjectCount {
        expected: usize,
        actual: usize,
    },
    UnexpectedStackObjectDisposition {
        object: r2ssa::ObjectId,
    },
    StackObjectCertificate {
        object: r2ssa::ObjectId,
        binding: BindingId,
    },
    StackObjectDeclarationWidth {
        object: r2ssa::ObjectId,
        binding: BindingId,
    },
    ParameterCount {
        expected: usize,
        actual: usize,
    },
    UnexpectedParameterDisposition {
        slot: u32,
    },
    ParameterCertificate {
        slot: u32,
        binding: BindingId,
    },
    ParameterDeclarationWidth {
        slot: u32,
        binding: BindingId,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BindingPlanBuildError {
    MachineProjection(r2ssa::MachineBuildError),
    MissingStorageSpan { value: ValueId },
    InvalidValueWidth { value: ValueId, size_bytes: u32 },
    TooManyBindings { count: usize },
    InvalidCertifiedEntityValue { entity: SemanticId, value: ValueId },
    Seal(BindingPlanSourceMismatch),
}

#[derive(Debug)]
struct BindingComponent {
    members: BTreeSet<ValueId>,
    sources: BTreeSet<BindingCertificateSource>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BindingWidth {
    Exact(u32),
    Refused(ValueRefusal),
}

#[derive(Debug)]
struct SealBindingComponent {
    members: BTreeSet<ValueId>,
    sources: BTreeSet<BindingCertificateSource>,
}

#[derive(Debug)]
enum SealWidthEvidence {
    Exact { lower_bounds: Vec<u32> },
    Refused(ValueRefusal),
}

/// Dense identity of one component resolved directly from upstream storage and
/// semantic certificates by the independent sealing oracle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct CanonicalComponentId(u32);

impl CanonicalComponentId {
    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Canonical value answer recomputed for diagnostics without consulting the
/// candidate plan's stored disposition or binding membership.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UpstreamValueDisposition {
    Bound { component: CanonicalComponentId },
    InlineConstant,
    Elided(r2ssa::ledger::ElisionReason),
    Refused(ValueRefusal),
}

/// Transient Stage 4 validation oracle.
///
/// This is deliberately rebuilt from the exact source and is never retained by
/// a [`BindingPlan`] or consumed by lowering. Machine facts remain owned by the
/// source-backed [`MachineProjection`]; component membership is resolved by the
/// sealing module's independent certificate walk.
#[derive(Debug)]
pub(crate) struct UpstreamShadowOracle {
    machine_projection: MachineProjection,
    components: Box<[Box<[ValueId]>]>,
    values: Box<[UpstreamValueDisposition]>,
}

impl UpstreamShadowOracle {
    pub(crate) fn component(&self, id: CanonicalComponentId) -> Option<&[ValueId]> {
        self.components.get(id.index()).map(Box::as_ref)
    }

    pub(crate) fn value_disposition(&self, value: ValueId) -> Option<UpstreamValueDisposition> {
        self.values.get(value.0 as usize).copied()
    }

    pub(crate) fn use_disposition(&self, site: UseSite) -> Option<&MachineUseDisposition> {
        self.machine_projection.use_disposition(site)
    }

    pub(crate) fn write_disposition(&self, inst: InstId) -> Option<&MachineWriteDisposition> {
        self.machine_projection.write_disposition(inst)
    }
}

/// Complete renderer-side projection of one exact source-owned SSA artifact.
///
/// Dense vectors make value and binding lookup O(1). Exact/refused use and
/// write lookup delegates to the plan-owned [`MachineProjection`] in O(1), so
/// the source geometry has one owner. Observable-effect outcomes are absent:
/// they are only knowable after rendering and ledger reconciliation.
#[derive(Debug, Clone)]
pub(crate) struct BindingPlan {
    authority: SsaArtifactAuthority,
    machine_projection: MachineProjection,
    bindings: Box<[Binding]>,
    dispositions: Box<[ValueDisposition]>,
    parameters: Box<[Option<ParameterDisposition>]>,
    stack_objects: BTreeMap<r2ssa::ObjectId, StackObjectDisposition>,
}

mod construction;
mod name_resolution;
mod rules;
mod seal;

pub(crate) use name_resolution::{
    BindingNameResolution, BindingNameResolutionError, PlannedParameterSymbol, PlannedStackSymbol,
    PlannedValueSymbol, RenderedIdentityRefusal,
};
pub(crate) use seal::build_upstream_shadow_oracle;

#[cfg(test)]
use construction::binding_components;
#[cfg(test)]
use seal::seal_binding_components;
impl BindingPlan {
    pub(crate) const fn machine_projection(&self) -> &MachineProjection {
        &self.machine_projection
    }

    pub(crate) fn binding(&self, id: BindingId) -> Option<&Binding> {
        self.bindings.get(id.index())
    }

    /// Number of sealed bindings in the dense `BindingId` domain.
    pub(crate) const fn binding_count(&self) -> usize {
        self.bindings.len()
    }

    /// Iterate sealed bindings in ascending, deterministic `BindingId` order.
    pub(crate) fn bindings(&self) -> impl ExactSizeIterator<Item = (BindingId, &Binding)> {
        self.bindings.iter().enumerate().map(|(index, binding)| {
            let id = u32::try_from(index)
                .map(BindingId)
                .expect("sealed binding count fits the BindingId domain");
            (id, binding)
        })
    }

    pub(crate) fn disposition(&self, value: ValueId) -> Option<&ValueDisposition> {
        self.dispositions.get(value.0 as usize)
    }

    /// Resolve one exact ABI slot in O(1). The table is dense-indexed but may
    /// contain empty cells when the certified slot domain is sparse.
    pub(crate) fn parameter_disposition(&self, slot: u32) -> Option<ParameterDisposition> {
        self.parameters.get(slot as usize).copied().flatten()
    }

    pub(crate) fn binding_role(&self, binding: BindingId) -> Option<BindingRole> {
        let binding = self.binding(binding)?;
        let mut roles = binding.certificate.sources.iter().filter_map(|source| {
            let BindingCertificateSource::CertifiedEntity(entity) = source else {
                return None;
            };
            match *entity {
                SemanticId::Parameter(slot) => Some(BindingRole::Parameter { slot }),
                SemanticId::StackSlot(object) => Some(BindingRole::StackObject { object }),
                _ => None,
            }
        });
        // A certified entity is the stronger claim and decides on its own. An
        // argument slot is a caller-supplied value too, so the entity role has
        // to be consulted first or every parameter would answer `EntryValue`.
        let Some(role) = roles.next() else {
            return Some(if binding.caller_supplied {
                BindingRole::EntryValue
            } else {
                BindingRole::Local
            });
        };
        roles.all(|other| other == role).then_some(role)
    }

    /// Whether the function signature declares this object, so the body must
    /// not declare it again.
    pub(crate) fn binding_is_externally_declared(&self, binding: BindingId) -> Option<bool> {
        self.binding_role(binding)
            .map(|role| matches!(role, BindingRole::Parameter { .. }))
    }

    /// Whether the caller supplies this object's value without the signature
    /// naming it.
    ///
    /// The body still declares it, because no parameter does, but it holds a
    /// value on entry and therefore cannot be required to be assigned before
    /// its first read.
    pub(crate) fn binding_is_entry_declared(&self, binding: BindingId) -> Option<bool> {
        self.binding_role(binding)
            .map(|role| matches!(role, BindingRole::EntryValue))
    }

    pub(crate) fn stack_object_disposition(
        &self,
        object: r2ssa::ObjectId,
    ) -> Option<StackObjectDisposition> {
        self.stack_objects.get(&object).copied()
    }

    pub(crate) fn use_disposition(&self, site: UseSite) -> Option<&r2ssa::MachineUseDisposition> {
        self.machine_projection.use_disposition(site)
    }

    pub(crate) fn write_disposition(
        &self,
        inst: InstId,
    ) -> Option<&r2ssa::MachineWriteDisposition> {
        self.machine_projection.write_disposition(inst)
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
            .map_err(BindingPlanSourceMismatch::MachineProjection)?;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn replace_value_disposition_for_shadow_test(
        &mut self,
        value: ValueId,
        disposition: ValueDisposition,
    ) {
        self.dispositions[value.0 as usize] = disposition;
    }
}

#[cfg(test)]
mod tests;
