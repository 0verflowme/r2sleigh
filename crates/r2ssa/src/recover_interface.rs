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

use r2source::{CanonicalStorageId, CanonicalStorageSpace, SourceConventionSlots};

use crate::function::SSAFunction;
use crate::var::SSAVar;

/// What the machine code proves about a function's interface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveredInterface {
    parameters: Box<[CanonicalStorageId]>,
    result: Option<CanonicalStorageId>,
}

impl RecoveredInterface {
    /// Parameter storages in convention order, contiguous from index zero.
    pub const fn parameters(&self) -> &[CanonicalStorageId] {
        &self.parameters
    }

    /// The result carrier, when the function defines it before returning.
    pub const fn result(&self) -> Option<CanonicalStorageId> {
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

/// Storages this function reads before writing anywhere in its body.
fn entry_read_storages(func: &SSAFunction) -> Vec<CanonicalStorageId> {
    let mut reads = Vec::new();
    let mut note = |storage: CanonicalStorageId| {
        if !reads.contains(&storage) {
            reads.push(storage);
        }
    };
    for block in func.blocks() {
        for phi in &block.phis {
            for (_, source) in &phi.sources {
                if let Some(storage) = is_entry_read(func, source) {
                    note(storage);
                }
            }
        }
        for op in &block.ops {
            op.for_each_source(&mut |source| {
                if let Some(storage) = is_entry_read(func, source) {
                    note(storage);
                }
            });
        }
    }
    reads
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
    if slots.argument_slots().is_empty() {
        return None;
    }
    let reads = entry_read_storages(func);
    let mut parameters = Vec::new();
    for slot in slots.argument_slots() {
        if !reads.iter().any(|read| read_covers_slot(*read, *slot)) {
            break;
        }
        parameters.push(*slot);
    }
    let result = slots
        .result_slot()
        .filter(|slot| function_defines(func, *slot));
    Some(RecoveredInterface {
        parameters: parameters.into_boxed_slice(),
        result,
    })
}

/// True when the function writes this storage somewhere in its body.
///
/// A result carrier the function never defines cannot be carrying a result it
/// produced, so the return is reported absent rather than assumed.
fn function_defines(func: &SSAFunction, storage: CanonicalStorageId) -> bool {
    for block in func.blocks() {
        for phi in &block.phis {
            if phi.dst.version != 0
                && func
                    .canonical_storage_for_var(&phi.dst)
                    .is_some_and(|defined| read_covers_slot(defined, storage))
            {
                return true;
            }
        }
        for op in &block.ops {
            if let Some(dst) = op.dst()
                && dst.version != 0
                && func
                    .canonical_storage_for_var(dst)
                    .is_some_and(|defined| read_covers_slot(defined, storage))
            {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};

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
            [register(0, 8), register(8, 8), register(16, 8)],
            Some(register(0, 8)),
        )
        .expect("candidate slots")
    }

    fn recovered(block: R2ILBlock) -> RecoveredInterface {
        let arch = arch();
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&arch)).expect("ssa");
        recover_interface(&func, &candidates()).expect("recovery")
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
        assert_eq!(interface.parameters(), &[register(0, 8), register(8, 8)]);
        // x0 was written, so the result carrier is defined
        assert_eq!(interface.result(), Some(register(0, 8)));
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
        assert_eq!(interface.parameters(), &[register(0, 8)]);
    }

    #[test]
    fn a_narrow_read_still_names_the_whole_candidate_slot() {
        let mut block = R2ILBlock::new(0x1000, 4);
        // reads w0, the low half of x0: same argument, narrower view
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::register(0, 4),
        });
        let interface = recovered(block);
        assert_eq!(interface.parameters(), &[register(0, 8)]);
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
    fn a_convention_without_candidates_recovers_nothing() {
        let arch = arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::register(0, 8),
        });
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&arch)).expect("ssa");
        let empty = SourceConventionSlots::new([], None).expect("empty");
        assert!(recover_interface(&func, &empty).is_none());
    }
}
