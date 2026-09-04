//! Recovering a function's ABI from the machine code that implements it.
//!
//! A register a function reads before it writes is a value its caller supplied.
//! That is a dataflow fact, not an inference: SSA construction already assigns
//! version 0 to exactly those reads, because there is no prior definition in the
//! function to rename them to.
//!
//! Intersecting those reads with the calling convention's candidate slots yields
//! the parameters, and the convention's result slot yields the return. Nothing
//! here claims a type or a name, both of which compilation genuinely erases.

use r2source::{
    CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCallArgumentSpec,
    SourceCallResult, SourceCallSiteIdentity, SourceCallSiteInterface, SourceCarrierKind,
    SourceCarrierProjection, SourceConventionSlots, SourceFunctionInterface, SourceFunctionReturn,
    SourceLogicalValue, SourceMachineRoles, SourceType, SourceTypeGraph, SourceTypeKind,
};

use crate::function::SSAFunction;
use crate::graph::SsaGraph;
use crate::span::StorageSpans;
use crate::var::SSAVar;

/// One argument slot the machine code proves the function reads.
///
/// The slot is what the convention names, and the read is what the function
/// actually did with it. They differ whenever a parameter is narrower than the
/// register that carries it: an `int` third argument on amd64 arrives in `rdx`
/// and the callee reads `edx`. Keeping only the slot claimed the function reads
/// all eight bytes, and no value of that width exists, so the parameter was
/// left without a fact and eventually rendered as an unnamed binding or trimmed
/// away.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecoveredParameter {
    slot: CanonicalStorageId,
    observed: CanonicalStorageId,
}

impl RecoveredParameter {
    /// The convention's argument register.
    pub const fn slot(&self) -> CanonicalStorageId {
        self.slot
    }

    /// The entry read that satisfied it, never wider than the slot.
    pub const fn observed(&self) -> CanonicalStorageId {
        self.observed
    }
}

/// One result slot the function proves it fills, and the part it actually fills.
///
/// The convention names the full carrier while the defining operation names the
/// logical width. They differ for an `int` returned in a 64-bit register, just
/// as they do for a narrow parameter arriving in a full argument register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecoveredResult {
    slot: CanonicalStorageId,
    observed: CanonicalStorageId,
}

impl RecoveredResult {
    /// The convention's result register.
    pub const fn slot(self) -> CanonicalStorageId {
        self.slot
    }

    /// The widest definition that contributes to the result.
    pub const fn observed(self) -> CanonicalStorageId {
        self.observed
    }
}

/// What the machine code proves about a function's interface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveredInterface {
    parameters: Box<[RecoveredParameter]>,
    result: Option<RecoveredResult>,
}

impl RecoveredInterface {
    /// Parameter slots in convention order, contiguous from index zero, each
    /// with the entry read that proved it.
    pub const fn parameters(&self) -> &[RecoveredParameter] {
        &self.parameters
    }

    /// The result slot and observed logical width, when every return defines it.
    pub const fn result(&self) -> Option<RecoveredResult> {
        self.result
    }
}

/// True when this variable is a value the caller supplied.
///
/// Version 0 means SSA renaming found no prior definition in this function, so
/// the read observes whatever entered. Constants and non-register storage are
/// excluded: only a register can carry an argument under these conventions.
fn is_entry_read(func: &SSAFunction, var: &SSAVar) -> Option<CanonicalStorageId> {
    if var.version != 0 {
        return None;
    }
    let storage = func.canonical_storage_for_var(var)?;
    (storage.space == CanonicalStorageSpace::Register).then_some(storage)
}

/// Storages this function reads before writing and whose values reach a program
/// observation.
///
/// SSA normalization deliberately preserves machine-state joins that symbolic
/// execution still needs. Those joins may mention every incoming convention
/// register even when the native program never observes it, so occurrence in a
/// phi or alias-composition op is not parameter evidence. The upstream positive
/// observation certificate is the authority for admitting an entry read; an
/// unsupported/unknown obligation can cause refusal but cannot prove a parameter.
fn observed_entry_read_storages(
    func: &SSAFunction,
    graph: &SsaGraph,
    observations: &crate::deadphi::ProvenProgramObservations,
) -> Vec<CanonicalStorageId> {
    let mut reads = Vec::new();
    let mut note = |storage: CanonicalStorageId| {
        if !reads.contains(&storage) {
            reads.push(storage);
        }
    };
    for value in &graph.values {
        if observations.contains(value.id)
            && graph.def_inst(value.id).is_none()
            && let Some(storage) = is_entry_read(func, &value.var)
        {
            note(storage);
        }
    }
    reads
}

/// Storages this function hands to a call without ever defining them.
///
/// A parameter is otherwise proven by an entry read, and a carrier the function
/// only passes on is never read explicitly: a call takes its arguments
/// implicitly, so the ordinary observation scan cannot see it. Depending on
/// register normalization, the boundary may retain that state as
/// `PreservedEntry` or as a producerless version-zero graph value; both are the
/// same exact entry carrier, while a value with a definition is not.
/// The consequence was that the argument had no parameter to name, the call
/// rendered with it dropped, and its obligation could never be discharged --
/// the affected `/bin/ls` calls refuse that way.
///
/// The evidence is the callee's, not a guess about this function. A boundary's
/// arguments come from the callee's own interface, so the argument exists
/// because the callee takes it, and `SourceCallArgumentValue::PreservedEntry`
/// says the value it receives is the one this function was entered with. That
/// is what a parameter is.
fn passed_through_entry_storages(
    boundaries: &crate::semantic::SourceBoundaryFacts,
    graph: &SsaGraph,
) -> Vec<CanonicalStorageId> {
    let mut storages = Vec::new();
    for boundary in boundaries.calls.values() {
        for argument in &boundary.arguments {
            let crate::semantic::CallBoundarySlot::Register { storage, .. } = argument.slot else {
                continue;
            };
            let is_entry = match argument.value {
                crate::semantic::SourceCallArgumentValue::PreservedEntry => true,
                crate::semantic::SourceCallArgumentValue::Value(value) => {
                    graph.value(value).is_some_and(|graph_value| {
                        graph.def_inst(value).is_none()
                            && graph_value.var.version == 0
                            && graph_value.var.size == storage.size
                            && graph_value.canonical_storage == Some(storage)
                    })
                }
            };
            if !is_entry {
                continue;
            }
            if !storages.contains(&storage) {
                storages.push(storage);
            }
        }
    }
    storages
}

/// True when a read of `read` observes bytes of the candidate slot.
///
/// A convention slot names the full register; a function may read only its low
/// half (`w0` of `x0`). Both are the same argument, so containment rather than
/// equality decides.
fn read_covers_slot(read: CanonicalStorageId, slot: CanonicalStorageId) -> bool {
    read.space == slot.space
        && read.offset == slot.offset
        && read.size > 0
        && read.size <= slot.size
}

/// The widest low slice that contributes to a recovered result.
///
/// A full-width base followed by a narrow overlay is still a full-width value,
/// while a function that only defines the low half has a narrow logical result.
/// Requiring every contributing value to belong to the convention's exact
/// location keeps an unrelated register from becoming return-width evidence.
fn recovered_result(
    graph: &SsaGraph,
    live_out: &crate::liveout::FunctionLiveOut,
    slot: CanonicalStorageId,
) -> Option<RecoveredResult> {
    let mut observed = None;
    for value in live_out.iter() {
        let storage = graph.value(value)?.canonical_storage?;
        if storage.location() != slot.location() || storage.size == 0 || storage.size > slot.size {
            return None;
        }
        let observed_size = if storage == slot {
            narrow_zero_extend_input_size(graph, value).unwrap_or(storage.size)
        } else {
            storage.size
        };
        let storage = CanonicalStorageId {
            space: slot.space,
            offset: slot.offset,
            size: observed_size,
        };
        if observed.is_none_or(|current: CanonicalStorageId| storage.size > current.size) {
            observed = Some(storage);
        }
    }
    Some(RecoveredResult {
        slot,
        observed: observed?,
    })
}

/// The narrow value a full result definition zero-extends.
///
/// Lifters make implicit carrier clearing explicit: returning a value through
/// `eax`/`w0` is represented by a narrow definition followed by `rax`/`x0 =
/// zext(...)`. The live-out is consequently the full carrier, while the input
/// of that exact defining operation is the width the machine observed. Other
/// full-width definitions remain full width; no register name or architecture
/// convention is guessed here.
fn narrow_zero_extend_input_size(graph: &SsaGraph, value: crate::ValueId) -> Option<u32> {
    let definition = graph.def_inst(value).and_then(|inst| graph.inst(inst))?;
    let crate::graph::InstPayload::Op(crate::SSAOp::IntZExt { .. }) = &definition.payload else {
        return None;
    };
    let [input] = definition.inputs.as_slice() else {
        return None;
    };
    let input = graph.value(*input)?;
    let output = graph.value(value)?;
    let input_size = input.var.size;
    let output_size = output.var.size;
    (input_size > 0 && input_size < output_size).then_some(input_size)
}

/// Recover what the machine code proves about this function's interface.
///
/// Parameters are the longest prefix of the convention's candidate slots that
/// the function reads before writing. The prefix stops at the first slot it does
/// not read: a gap cannot be resolved, because an unread slot is equally
/// consistent with an unused parameter and with the function taking fewer
/// arguments, and claiming either would be a guess. Under-reporting a trailing
/// unused parameter is the safe direction.
///
/// Returns `None` when the convention offers no candidates, which leaves the
/// caller to refuse rather than assume a convention.
pub fn recover_interface(
    func: &SSAFunction,
    slots: &SourceConventionSlots,
) -> Option<RecoveredInterface> {
    recover_interface_inner(func, slots, None)
}

/// Recover an interface while retaining exact source-owned call boundaries.
///
/// This is the production path. The context is provisional only in that it
/// does not yet contain the function interface being recovered; its call-site
/// identities and interfaces are already final source facts.
pub(crate) fn recover_interface_with_context(
    func: &SSAFunction,
    slots: &SourceConventionSlots,
    machine_context: &crate::SourceMachineContext,
) -> Option<RecoveredInterface> {
    recover_interface_inner(func, slots, Some(machine_context))
}

fn recover_interface_inner(
    func: &SSAFunction,
    slots: &SourceConventionSlots,
    machine_context: Option<&crate::SourceMachineContext>,
) -> Option<RecoveredInterface> {
    if slots.argument_slots().is_empty() {
        return None;
    }
    // Recovery is intentionally a bounded two-phase path used only when the
    // source supplied no exact interface. This provisional O(V + E) fact pass
    // establishes the observation domain; the ordinary preparation pass then
    // seals the recovered interface into the final artifact. A cheaper raw-use
    // scan cannot distinguish program inputs from preserved machine state.
    let graph = SsaGraph::from_function(func);
    let facts = if let Some(machine_context) = machine_context {
        let storage_spans = StorageSpans::compute(func, &graph);
        crate::semantic::PreparedFunctionFacts::collect_with_context(
            func,
            &graph,
            &storage_spans,
            &crate::AssumptionSet::default(),
            machine_context,
        )
    } else {
        crate::semantic::PreparedFunctionFacts::collect(func, &graph)
    };
    if !facts.obligations.is_complete() {
        r2il::refusal_evidence!(
            "interface-recovery",
            "the obligation inventory is incomplete, so no interface is recovered and \
             every ABI question about this function answers `unavailable`"
        );
        return None;
    }

    let exact_tail_result = exact_tail_result_storage(&facts);
    let mut result = exact_tail_result.flatten().map(|slot| RecoveredResult {
        slot,
        observed: slot,
    });
    let mut live_out = crate::liveout::FunctionLiveOut::default();
    // An exact tail-call interface owns this boundary. Looking at the value
    // present before the branch would instead mistake a call argument for the
    // value the callee returns into the same register.
    if exact_tail_result.is_none()
        && let Some(candidate) = slots.result_slot()
    {
        let candidate_live_out =
            crate::liveout::FunctionLiveOut::compute(func, &graph, &[candidate]);
        if !candidate_live_out.is_empty() && candidate_live_out.unresolved_blocks().next().is_none()
        {
            result = recovered_result(&graph, &candidate_live_out, candidate);
            live_out = candidate_live_out;
        }
    }
    let Some(observations) =
        crate::deadphi::ProvenProgramObservations::find(&graph, &live_out, &facts)
    else {
        r2il::refusal_evidence!(
            "interface-recovery",
            "no proven program observations: result_slot={:?} live_out={} unresolved_blocks={}",
            slots.result_slot(),
            live_out.len(),
            live_out.unresolved_blocks().count()
        );
        return None;
    };
    let mut reads = observed_entry_read_storages(func, &graph, &observations);
    // A carrier passed straight to a call is read by that call, so it belongs
    // in the same evidence as an explicit entry read. The prefix rule below is
    // unchanged and still stops at the first candidate slot nothing observes.
    // Contextual recovery has the exact callsite interfaces production will
    // use, while context-free recovery may still derive a local boundary. In
    // either case a preserved carrier is a real entry read by the call. Final
    // preparation materializes its source-declared boundary value so every
    // consumer can use the same identity.
    for storage in passed_through_entry_storages(&facts.boundaries, &graph) {
        if !reads.contains(&storage) {
            reads.push(storage);
        }
    }
    let mut parameters = Vec::new();
    for slot in slots.argument_slots() {
        // The widest read that lands in this slot. A callee that both spills
        // the whole register and uses its low half proves the wider one, and
        // taking the widest keeps the recovered width from depending on which
        // read the scan happened to see first.
        let observed = reads
            .iter()
            .copied()
            .filter(|read| read_covers_slot(*read, *slot))
            .max_by_key(|read| read.size);
        let Some(observed) = observed else {
            break;
        };
        parameters.push(RecoveredParameter {
            slot: *slot,
            observed,
        });
    }
    Some(RecoveredInterface {
        parameters: parameters.into_boxed_slice(),
        result,
    })
}

/// The result carrier licensed by every source-proven tail boundary.
///
/// `Some(None)` is an exact void result; `None` means there is no complete,
/// unanimous tail boundary and ordinary live-out recovery remains responsible.
fn exact_tail_result_storage(
    facts: &crate::semantic::PreparedFunctionFacts,
) -> Option<Option<CanonicalStorageId>> {
    let mut results = facts
        .call_sites
        .by_id
        .values()
        .filter(|call| call.transfer == crate::CallSiteTransfer::TailCall)
        .map(|call| {
            let boundary = facts.boundaries.calls.get(&call.id)?;
            boundary.complete.then_some(boundary.result_kind?)
        });
    let first = results.next()??;
    if results.any(|result| result != Some(first)) {
        return None;
    }
    Some(match first {
        SourceCallResult::Void => None,
        SourceCallResult::Register { storage } => Some(storage),
    })
}

/// The width of a register storage, where it is one an integer type can have.
fn storage_bits(storage: CanonicalStorageId) -> Option<u32> {
    let bits = storage.size.checked_mul(8)?;
    matches!(bits, 8 | 16 | 32 | 64).then_some(bits)
}

/// Build a source interface from what the machine code proves.
///
/// Every parameter is an unsigned integer of the register's own width. That is
/// not a claim about the source type, which compilation erased: it is the same
/// convention the renderer already applies to every machine value, where a
/// value is an unsigned bit pattern and signedness comes from the operations
/// applied to it. Signedness, pointer-ness and names are never asserted.
///
/// The return-address and stack-pointer carriers come from the machine roles,
/// which the source resolves without any recovered prototype. Certification
/// requires both, so a source lacking either yields no interface rather than a
/// half-formed one.
pub fn mint_recovered_interface(
    recovered: &RecoveredInterface,
    roles: &SourceMachineRoles,
    revision_identity: &[u8],
    calling_convention: &str,
) -> Option<SourceFunctionInterface> {
    let minted =
        mint_recovered_interface_inner(recovered, roles, revision_identity, calling_convention);
    if minted.is_none() {
        r2il::refusal_evidence!(
            "interface-minting",
            "return_address={:?} stack_pointer={:?} identity={} convention={:?} \
             parameters={:?} result={:?}",
            roles.return_address_storage(),
            roles.stack_pointer_storage(),
            revision_identity.len(),
            calling_convention,
            recovered
                .parameters()
                .iter()
                .map(|parameter| (parameter.slot().size, parameter.observed().size))
                .collect::<Vec<_>>(),
            recovered
                .result()
                .map(|result| (result.slot().size, result.observed().size))
        );
    }
    minted
}

fn mint_recovered_interface_inner(
    recovered: &RecoveredInterface,
    roles: &SourceMachineRoles,
    revision_identity: &[u8],
    calling_convention: &str,
) -> Option<SourceFunctionInterface> {
    let return_address_storage = roles.return_address_storage()?;
    let stack_pointer_storage = roles.stack_pointer_storage()?;
    if revision_identity.is_empty() || calling_convention.trim().is_empty() {
        return None;
    }

    // One integer type per distinct width the interface actually uses, so the
    // graph describes exactly what is referenced and nothing more. The
    // constructor enforces that literally: a graph carrying a type no logical
    // value names is rejected outright.
    let mut widths: Vec<u32> = Vec::new();
    let mut width_of = |storage: CanonicalStorageId| -> Option<u32> {
        let bits = storage_bits(storage)?;
        if !widths.contains(&bits) {
            widths.push(bits);
        }
        Some(bits)
    };
    // The logical value is typed by what the function read, not by the size of
    // the register the convention put it in.
    let parameter_widths = recovered
        .parameters()
        .iter()
        .map(|parameter| width_of(parameter.observed()))
        .collect::<Option<Vec<_>>>()?;
    // The slot's width decides whether the read covers the whole carrier or
    // only its low half, and nothing else. It names no logical value, so it
    // must not put a type in the graph: an `int` parameter arriving in a
    // sixty-four-bit register is read as thirty-two bits, and registering the
    // carrier's width added a type nothing referenced and made the constructor
    // reject the interface. The function was then left with no ABI at all --
    // every question about its return kind answering `unavailable`, its return
    // boundary incomplete, and the renderer refusing. That was the largest
    // single refusal cause in the corpus, and it fires for any function taking
    // a parameter narrower than the register that carries it.
    let parameter_slot_widths = recovered
        .parameters()
        .iter()
        .map(|parameter| storage_bits(parameter.slot()))
        .collect::<Option<Vec<_>>>()?;
    let result_width = match recovered.result() {
        Some(result) => Some(width_of(result.observed())?),
        None => None,
    };
    widths.sort_unstable();

    let types = widths
        .iter()
        .enumerate()
        .map(|(index, bits)| {
            SourceType::new(
                u32::try_from(index).ok()?,
                SourceTypeKind::UnsignedInteger,
                u64::from(*bits),
                u64::from(*bits),
            )
            .into()
        })
        .collect::<Option<Vec<SourceType>>>()?;
    let type_graph = SourceTypeGraph::new(types, []).ok()?;
    let type_id = |bits: u32| -> Option<u32> {
        widths
            .iter()
            .position(|candidate| *candidate == bits)
            .and_then(|index| u32::try_from(index).ok())
    };
    // `Full` where the read is the whole register, `LowBits` where it is the
    // register's low half. The second is what an `int` parameter looks like in
    // a 64-bit argument register, and it is the projection the parameter-fact
    // collector already knows how to narrow.
    let logical = |bits: u32, carrier_bits: u32| -> Option<SourceLogicalValue> {
        let kind = if bits < carrier_bits {
            SourceCarrierKind::LowBits
        } else {
            SourceCarrierKind::Full
        };
        Some(SourceLogicalValue::new(
            type_id(bits)?,
            SourceCarrierProjection::new(kind, 0, u64::from(bits)),
        ))
    };

    let parameters = recovered
        .parameters()
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            Some(SourceAbiParameterSpec::new(
                u32::try_from(index).ok()?,
                parameter.slot(),
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let parameter_logical_values = parameter_widths
        .iter()
        .zip(parameter_slot_widths.iter())
        .map(|(bits, carrier_bits)| logical(*bits, *carrier_bits))
        .collect::<Option<Vec<_>>>()?;
    let (return_kind, return_logical_value) = match (recovered.result(), result_width) {
        (Some(result), Some(bits)) => (
            SourceFunctionReturn::Register {
                storage: result.slot(),
            },
            Some(logical(bits, result.slot().size.checked_mul(8)?)?),
        ),
        _ => (SourceFunctionReturn::Void, None),
    };

    // Exact: the stack slot roles are complete because there are none to
    // classify, which certification requires before it will trust the model.
    SourceFunctionInterface::new_exact_with_logical_types(
        revision_identity.to_vec(),
        calling_convention,
        parameters,
        return_kind,
        [],
        parameter_logical_values,
        return_logical_value,
        Some(type_graph),
    )
    .inspect_err(|error| {
        r2il::refusal_evidence!("interface-minting", "constructor rejected it: {error:?}");
    })
    .ok()?
    .with_return_address_storage(return_address_storage)
    .ok()?
    .with_stack_pointer_storage(stack_pointer_storage)
    .ok()
}

/// Mint a call-site interface from an interface recovered for the callee.
///
/// radare2 reports a prototype for a call only when it has one. For a local
/// function it usually has none: it correctly declines to assert a return type
/// it never inferred, and the snapshot carries that absence faithfully. The
/// call site is then left with no interface at all, its boundary never
/// completes, and every use of the call's result in the caller is refused.
///
/// But the callee's body arrives in the same capture, and its interface is
/// already recovered from its own SSA by `recover_interface` -- which is a
/// stronger fact than a prototype, because it is derived from the code rather
/// than declared about it. So where the source names no prototype and we hold
/// the callee, the call site is described from what the callee does.
///
/// The carriers come from the callee; the identity, revision and convention
/// come from the call site, so the result is indistinguishable from a
/// source-supplied interface to everything downstream and passes the same
/// admission gates.
pub fn mint_recovered_call_site_interface(
    callee: &SourceFunctionInterface,
    identity: SourceCallSiteIdentity,
    revision_identity: &[u8],
) -> Option<SourceCallSiteInterface> {
    let arguments = callee
        .parameters()
        .iter()
        .map(|parameter| SourceCallArgumentSpec::new(parameter.index(), parameter.storage()));
    let result = match callee.return_kind() {
        SourceFunctionReturn::Void => SourceCallResult::Void,
        SourceFunctionReturn::Register { storage } => SourceCallResult::Register { storage },
    };
    SourceCallSiteInterface::new(
        revision_identity.to_vec(),
        identity,
        true,
        callee.calling_convention(),
        arguments,
        false,
        false,
        result,
    )
    .and_then(|interface| interface.with_exact_callee_interface(callee.clone()))
    .ok()
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2source::SourceCallSiteInterfaceError;

    use super::*;

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0, 8));
        arch.add_register(RegisterDef::new("w0", 0, 4));
        arch.add_register(RegisterDef::new("x1", 8, 8));
        arch.add_register(RegisterDef::new("x2", 16, 8));
        arch
    }

    fn register(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn candidates() -> SourceConventionSlots {
        SourceConventionSlots::new(
            "arm64",
            [register(0, 8), register(8, 8), register(16, 8)],
            Some(register(0, 8)),
        )
        .expect("candidate slots")
    }

    fn recovered(mut block: R2ILBlock) -> RecoveredInterface {
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let arch = arch();
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&arch)).expect("ssa");
        recover_interface(&func, &candidates()).expect("recovery")
    }

    fn call_boundary_with(
        arguments: Vec<crate::semantic::SourceCallArgumentFact>,
    ) -> crate::semantic::SourceBoundaryFacts {
        let mut boundaries = crate::semantic::SourceBoundaryFacts::default();
        boundaries.calls.insert(
            crate::semantic::CallSiteId(0),
            crate::semantic::SourceCallBoundaryFact {
                call_site: crate::semantic::CallSiteId(0),
                at: crate::graph::InstId(0),
                calling_convention: None,
                variadic: None,
                noreturn: None,
                result_kind: None,
                fixed_argument_count: Some(arguments.len()),
                variadic_argument_count_evidence: None,
                variadic_argument_count_refusal: None,
                arguments,
                results: Vec::new(),
                complete: true,
            },
        );
        boundaries
    }

    fn graph_for(mut block: R2ILBlock) -> SsaGraph {
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let arch = arch();
        let function = SSAFunction::from_blocks_with_arch(&[block], Some(&arch)).expect("ssa");
        SsaGraph::from_function(&function)
    }

    fn register_argument(
        index: u32,
        storage: CanonicalStorageId,
        value: crate::semantic::SourceCallArgumentValue,
    ) -> crate::semantic::SourceCallArgumentFact {
        crate::semantic::SourceCallArgumentFact {
            slot: crate::semantic::CallBoundarySlot::Register { index, storage },
            value,
        }
    }

    #[test]
    fn a_carrier_passed_straight_to_a_call_counts_as_read() {
        // The callee's own interface says the argument exists and
        // `PreservedEntry` says the value is the one this function was entered
        // with, so it is a parameter even though nothing here reads it: a call
        // takes its arguments implicitly and leaves no explicit read behind.
        let boundaries = call_boundary_with(vec![register_argument(
            0,
            register(0, 8),
            crate::semantic::SourceCallArgumentValue::PreservedEntry,
        )]);
        let graph = graph_for(R2ILBlock::new(0x1000, 4));
        assert_eq!(
            passed_through_entry_storages(&boundaries, &graph),
            vec![register(0, 8)]
        );
    }

    #[test]
    fn a_producerless_boundary_value_is_the_same_passed_entry_carrier() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::register(0, 8),
        });
        let graph = graph_for(block);
        let entry = graph
            .values
            .iter()
            .find(|value| {
                value.canonical_storage == Some(register(0, 8))
                    && graph.def_inst(value.id).is_none()
            })
            .expect("producerless x0 entry value")
            .id;
        let boundaries = call_boundary_with(vec![register_argument(
            0,
            register(0, 8),
            crate::semantic::SourceCallArgumentValue::Value(entry),
        )]);

        assert_eq!(
            passed_through_entry_storages(&boundaries, &graph),
            vec![register(0, 8)]
        );
    }

    #[test]
    fn contextual_recovery_promotes_a_preserved_call_carrier() {
        let arch = arch();
        let target = Varnode::constant(0x401000, 8);
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Call {
            target: target.clone(),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let blocks = [block];
        let call_interface = SourceCallSiteInterface::new(
            b"contextual-preserved-entry".to_vec(),
            SourceCallSiteIdentity::new(0x1000, 0, CanonicalStorageId::from_varnode(&target)),
            true,
            "arm64",
            [SourceCallArgumentSpec::new(0, register(0, 8))],
            false,
            false,
            SourceCallResult::Register {
                storage: register(0, 8),
            },
        )
        .expect("exact callsite interface");
        let machine_context = crate::SourceMachineContext::from_blocks_with_interfaces(
            &blocks,
            Some(&arch),
            None,
            SourceMachineRoles::default(),
            Some(candidates()),
            vec![call_interface],
        );
        let function = SSAFunction::from_blocks_for_decompile(&blocks, Some(&arch))
            .expect("decompile-normalized ssa");
        let recovered = recover_interface_with_context(&function, &candidates(), &machine_context)
            .expect("contextual recovery");

        assert_eq!(recovered.parameters().len(), 1);
        assert_eq!(recovered.parameters()[0].slot(), register(0, 8));
    }

    #[test]
    fn an_argument_this_function_computed_is_not_a_passed_through_carrier() {
        // A value defined here already has a producer and an SSA value naming
        // it, so it needs no help from this rule and must not be reported as an
        // entry read: that would claim a parameter the function may not have.
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(7, 8),
        });
        let graph = graph_for(block);
        let defined = graph
            .inst_id_for_op_site(0x1000, 0)
            .and_then(|inst| graph.inst(inst))
            .and_then(|inst| inst.output)
            .expect("defined x0 value");
        let boundaries = call_boundary_with(vec![register_argument(
            0,
            register(0, 8),
            crate::semantic::SourceCallArgumentValue::Value(defined),
        )]);
        assert!(passed_through_entry_storages(&boundaries, &graph).is_empty());
    }

    #[test]
    fn a_register_read_before_any_write_is_a_parameter() {
        let mut block = R2ILBlock::new(0x1000, 4);
        // reads x0 and x1 without defining them first
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::register(8, 8),
        });
        let interface = recovered(block);
        assert_eq!(
            interface
                .parameters()
                .iter()
                .map(RecoveredParameter::slot)
                .collect::<Vec<_>>(),
            &[register(0, 8), register(8, 8)]
        );
        // x0 was written, so the result carrier is defined
        assert_eq!(
            interface.result(),
            Some(RecoveredResult {
                slot: register(0, 8),
                observed: register(0, 8),
            })
        );
    }

    #[test]
    fn a_narrow_result_keeps_the_full_slot_and_mints_its_observed_width() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 4),
            src: Varnode::constant(7, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: Varnode::register(0, 8),
            src: Varnode::register(0, 4),
        });
        let recovered = recovered(block);
        let result = recovered.result().expect("recovered narrow result");
        assert_eq!(result.slot(), register(0, 8));
        assert_eq!(result.observed(), register(0, 4));

        let roles = SourceMachineRoles::new(Some(register(0x80, 8)), Some(register(0x88, 8)))
            .expect("machine roles");
        let interface =
            mint_recovered_interface(&recovered, &roles, b"narrow-return-revision", "aapcs64")
                .expect("minted narrow return interface");
        assert_eq!(
            interface.return_kind(),
            SourceFunctionReturn::Register {
                storage: register(0, 8),
            }
        );
        let logical = interface
            .return_logical_value()
            .expect("logical return projection");
        assert_eq!(logical.carrier().kind(), SourceCarrierKind::LowBits);
        assert_eq!(logical.carrier().size_bits(), 32);
        let source_type = &interface.type_graph().expect("return type graph").types()
            [usize::try_from(logical.type_id()).expect("type index")];
        assert_eq!(source_type.kind(), SourceTypeKind::UnsignedInteger);
        assert_eq!(source_type.size_bits(), 32);

        let callsite = mint_recovered_call_site_interface(
            &interface,
            SourceCallSiteIdentity::new(
                0x2000,
                3,
                CanonicalStorageId {
                    space: CanonicalStorageSpace::Constant,
                    offset: 0x4000,
                    size: 8,
                },
            ),
            b"narrow-return-revision",
        )
        .expect("callsite with recovered callee interface");
        assert_eq!(callsite.exact_callee_interface(), Some(&interface));

        let incompatible = SourceCallSiteInterface::new(
            b"narrow-return-revision".to_vec(),
            callsite.identity(),
            true,
            "aapcs64",
            [],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("physically valid void callsite")
        .with_exact_callee_interface(interface);
        assert_eq!(
            incompatible,
            Err(SourceCallSiteInterfaceError::IncompatibleCalleeInterface)
        );
    }

    #[test]
    fn a_register_written_before_it_is_read_is_not_a_parameter() {
        let mut block = R2ILBlock::new(0x1000, 4);
        // x0 is defined from a constant, then read: the read observes this
        // function's own value, not the caller's
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(8, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(1, 8),
        });
        let interface = recovered(block);
        assert!(interface.parameters().is_empty());
    }

    #[test]
    fn the_parameter_prefix_stops_at_the_first_unread_slot() {
        let mut block = R2ILBlock::new(0x1000, 4);
        // reads x0 and x2 but never x1: x2 cannot be claimed, because an unread
        // x1 is equally consistent with an unused parameter and with the
        // function taking one argument
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::register(16, 8),
        });
        let interface = recovered(block);
        assert_eq!(
            interface
                .parameters()
                .iter()
                .map(RecoveredParameter::slot)
                .collect::<Vec<_>>(),
            &[register(0, 8)]
        );
    }

    #[test]
    fn a_narrow_read_still_names_the_whole_candidate_slot() {
        let mut block = R2ILBlock::new(0x1000, 4);
        // reads w0, the low half of x0: same argument, narrower view
        block.push(R2ILOp::IntZExt {
            dst: Varnode::register(0, 8),
            src: Varnode::register(0, 4),
        });
        let interface = recovered(block);
        assert_eq!(
            interface
                .parameters()
                .iter()
                .map(RecoveredParameter::slot)
                .collect::<Vec<_>>(),
            &[register(0, 8)]
        );
    }

    #[test]
    fn a_result_carrier_the_function_never_defines_is_not_claimed() {
        let mut block = R2ILBlock::new(0x1000, 4);
        // x0 is only read, never written, so nothing was produced in it
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::register(0, 8),
        });
        let interface = recovered(block);
        assert_eq!(interface.result(), None);
    }

    #[test]
    fn a_dead_entry_read_is_not_promoted_to_a_parameter() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::register(8, 8),
        });
        // x2 is a convention candidate and is genuinely read at the machine
        // level, but this pure result reaches no effect or return. Its presence
        // cannot prove a third source parameter.
        block.push(R2ILOp::IntAdd {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(1, 8),
        });
        let interface = recovered(block);
        assert_eq!(
            interface
                .parameters()
                .iter()
                .map(RecoveredParameter::slot)
                .collect::<Vec<_>>(),
            &[register(0, 8), register(8, 8)]
        );
    }

    #[test]
    fn a_convention_without_candidates_recovers_nothing() {
        let arch = arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::register(0, 8),
        });
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&arch)).expect("ssa");
        let empty = SourceConventionSlots::new("", [], None).expect("empty");
        assert!(recover_interface(&func, &empty).is_none());
    }
}
