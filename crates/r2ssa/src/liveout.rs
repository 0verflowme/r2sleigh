//! Which values leave a function through its calling convention.
//!
//! A `Return` op names the instruction pointer, because that is what the machine
//! jumps to. That a register also carries the answer is a property of the calling
//! convention, and no operation in the lifted body records it. The consequence is
//! that the value a function returns has no reader anywhere in its own SSA: every
//! merge in an exit block reports zero uses, including the one holding the result.
//!
//! Reading that as deadness is wrong three times over. A carrier is refused
//! because nothing certifies a return. A test for whether a value is worth naming
//! cannot separate one that matters from one that does not. A merge that has to
//! survive looks exactly like one that could be dropped.
//!
//! This says the missing part out loud: at each block that returns, the values
//! sitting in the registers the caller is entitled to read are live, and being
//! read by the caller is a use like any other.

use std::collections::BTreeSet;

use crate::CanonicalStorageId;
use crate::function::SSAFunction;
use crate::graph::{SsaGraph, ValueId};

/// The values a function hands back to its caller.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionLiveOut {
    values: BTreeSet<ValueId>,
    /// Return blocks where no definition of a return register could be found.
    unresolved: BTreeSet<u64>,
}

/// Whether a write puts some of the returned bytes in place.
///
/// A `CanonicalLocation` is the register; a `CanonicalStorageId`'s size is only
/// how much of it one access took. `AL` and `RAX` are one place, so a write to
/// either contributes to what the caller reads out of that place.
fn contributes_to(write: CanonicalStorageId, return_storage: CanonicalStorageId) -> bool {
    write.location() == return_storage.location() && write.size > 0
}

/// Whether a write supplies every byte the caller reads.
///
/// Only such a write ends the backward walk: a narrower one leaves the
/// remaining bytes to whatever wrote them earlier.
fn covers_fully(write: CanonicalStorageId, return_storage: CanonicalStorageId) -> bool {
    write.location() == return_storage.location() && write.size >= return_storage.size
}

impl FunctionLiveOut {
    /// Work out what leaves through the return registers of every returning block.
    pub fn compute(
        func: &SSAFunction,
        graph: &SsaGraph,
        return_storages: &[CanonicalStorageId],
    ) -> Self {
        let mut live = Self::default();
        for block in func.blocks() {
            let returns = func
                .cfg()
                .get_block(block.addr)
                .is_some_and(|cfg| cfg.is_return());
            if !returns {
                continue;
            }
            // A returning block often holds no write to the return register at
            // all: the value was produced in the block before it, and a single
            // edge needs no merge to carry it across. Looking only here is what
            // made a function with an early-return arm report one live value and
            // one unresolved block, and left the value the loop computed
            // observed by nothing.
            let mut complete = !return_storages.is_empty();
            for storage in return_storages {
                complete &= live.collect_reaching(func, graph, *storage, block.addr);
            }
            if !complete {
                live.unresolved.insert(block.addr);
            }
        }
        live
    }

    /// Find what reaches a returning block in the return registers, walking back
    /// through predecessors until each path names a definition.
    ///
    /// The walk stops on a path as soon as that path defines the register, so a
    /// join is answered by its merge rather than by whatever lies beyond it, and
    /// a block already visited is not walked twice.
    fn collect_reaching(
        &mut self,
        func: &SSAFunction,
        graph: &SsaGraph,
        return_storage: CanonicalStorageId,
        from: u64,
    ) -> bool {
        let mut found = false;
        let mut clobbered_any = false;
        let mut seen = BTreeSet::new();
        let mut pending = std::collections::VecDeque::from([from]);
        while let Some(addr) = pending.pop_front() {
            if !seen.insert(addr) {
                continue;
            }
            let Some(block) = func.get_block(addr) else {
                continue;
            };
            let mut defined_here = false;
            // Whether a call on this path leaves the return register holding a
            // value this function never defines.
            let mut clobbered = false;
            // The last write to the *location* wins, and one write need not be
            // the whole value. `xor eax, eax` followed by `sete al` leaves the
            // returned `RAX` composed of a full-width zero and a one-byte
            // result, so matching the return storage by width alone saw only
            // the zero and left everything the comparison computed observed by
            // nothing. Walking back until the location is covered names every
            // definition the caller actually reads.
            for op in block.ops.iter().rev() {
                // The shared rule, so this walk and the return boundary's
                // cannot drift. Walking past a call named the last thing put in
                // the register before it -- for a function whose final act is
                // `warnx(fmt, ...)`, the format string -- as the value
                // returned.
                if crate::reaching_rules::op_ends_reaching_walk(op) {
                    clobbered = true;
                    break;
                }
                let Some(dst) = op.dst() else {
                    continue;
                };
                let Some(storage) = graph.canonical_storage_for_var(dst) else {
                    continue;
                };
                if !contributes_to(storage, return_storage) {
                    continue;
                }
                if let Some(value) = graph.value_id_for_var(dst) {
                    found |= self.values.insert(value);
                }
                if covers_fully(storage, return_storage) {
                    defined_here = true;
                    break;
                }
            }
            for phi in &block.phis {
                let Some(storage) = graph.canonical_storage_for_var(&phi.dst) else {
                    continue;
                };
                if !contributes_to(storage, return_storage) {
                    continue;
                }
                // Only a write that covers the whole return storage replaces the
                // merge. A narrower one leaves the remaining bytes to the phi.
                let overwritten = block.ops.iter().any(|op| {
                    op.dst().is_some_and(|dst| {
                        graph
                            .canonical_storage_for_var(dst)
                            .is_some_and(|written| covers_fully(written, return_storage))
                    })
                });
                if overwritten {
                    continue;
                }
                if let Some(value) = graph.value_id_for_var(&phi.dst) {
                    defined_here |= covers_fully(storage, return_storage);
                    found |= self.values.insert(value);
                }
            }
            if clobbered {
                // The path answers with the callee's value, which is not one of
                // this function's. Its predecessors cannot answer either: they
                // run before the call.
                clobbered_any = true;
                continue;
            }
            if defined_here {
                continue;
            }
            for predecessor in func.predecessors(addr) {
                pending.push_back(predecessor);
            }
        }
        found && !clobbered_any
    }

    /// Whether the caller reads this value once the function returns.
    pub fn contains(&self, value: ValueId) -> bool {
        self.values.contains(&value)
    }

    pub fn iter(&self) -> impl Iterator<Item = ValueId> + '_ {
        self.values.iter().copied()
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Returning blocks whose outgoing register value this pass could not name.
    pub fn unresolved_blocks(&self) -> impl Iterator<Item = u64> + '_ {
        self.unresolved.iter().copied()
    }
}

/// Whether anything at all reads a value: an operation in the body, or the caller.
///
/// Every rule that asks "is this read?" has until now asked the use list alone,
/// which cannot see past the end of the function. Asking both is what makes the
/// question answerable for a value that exists in order to be returned.
pub fn is_read(graph: &SsaGraph, live_out: &FunctionLiveOut, value: ValueId) -> bool {
    !graph.use_sites(value).is_empty() || live_out.contains(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CanonicalStorageSpace;
    use crate::function::SSAFunction;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode::new(SpaceId::Register, offset, size)
    }

    fn x86_64_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("EAX", 0, 4));
        arch.add_register(RegisterDef::new("RCX", 8, 8));
        arch.add_register(RegisterDef::new("RIP", 0x288, 8));
        arch
    }

    /// A body that computes into the return register and returns.
    fn returning_function() -> SSAFunction {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(7, 8),
                },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        SSAFunction::from_blocks_with_arch(&[block], Some(&x86_64_arch())).expect("ssa")
    }

    #[test]
    fn a_value_put_in_the_return_register_before_a_call_does_not_leave_the_function() {
        // `rax = 7; call rcx; ret` -- the callee owns `rax` when it returns, so
        // the seven is not what this function hands back, and nothing in the
        // function names what does.
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(7, 8),
                },
                R2ILOp::CallInd { target: reg(8, 8) },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&x86_64_arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(
            &func,
            &graph,
            &[CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            }],
        );
        assert!(live.is_empty(), "{live:?}");
        assert_eq!(live.unresolved_blocks().collect::<Vec<_>>(), vec![0x1000]);
    }

    #[test]
    fn canonical_return_storage_is_invariant_under_abi_name_collision() {
        let mut renamed = x86_64_arch();
        for register in &mut renamed.registers {
            if register.offset == 0 {
                register.name = if register.size == 8 { "rdi" } else { "edi" }.to_string();
            }
        }
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(7, 8),
                },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let function = SSAFunction::from_blocks_with_arch(&[block], Some(&renamed)).expect("ssa");
        let graph = SsaGraph::from_function(&function);

        let live = FunctionLiveOut::compute(&function, &graph, &x86_64_return_storages());

        assert_eq!(live.len(), 1);
        assert!(live.unresolved_blocks().next().is_none());
    }

    fn x86_64_return_storages() -> [CanonicalStorageId; 1] {
        [CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        }]
    }

    #[test]
    fn the_value_a_function_returns_is_read_even_with_no_use_sites() {
        let func = returning_function();
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &x86_64_return_storages());

        assert_eq!(
            live.len(),
            1,
            "the return register value should be live out"
        );
        let value = live.iter().next().expect("one live value");
        // This is the case the use list alone gets wrong.
        assert!(graph.use_sites(value).is_empty());
        assert!(is_read(&graph, &live, value));
    }

    #[test]
    fn only_the_last_write_to_a_return_storage_is_live_out() {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(1, 8),
                },
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(2, 8),
                },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&x86_64_arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);
        let returned = func.blocks().next().expect("one block").ops[1]
            .dst()
            .and_then(|value| graph.value_id_for_var(value))
            .expect("last return-register definition");

        let live = FunctionLiveOut::compute(&func, &graph, &x86_64_return_storages());

        assert_eq!(live.iter().collect::<Vec<_>>(), vec![returned]);
    }

    #[test]
    fn a_returning_block_that_names_no_return_register_is_reported_not_guessed() {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: reg(0x288, 8),
            }],
            ..R2ILBlock::default()
        };
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&x86_64_arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);

        let live = FunctionLiveOut::compute(&func, &graph, &x86_64_return_storages());

        assert!(live.is_empty());
        assert_eq!(live.unresolved_blocks().collect::<Vec<_>>(), vec![0x1000]);
    }

    #[test]
    fn a_value_no_one_reads_and_no_caller_receives_stays_unread() {
        // RCX is written, read by nothing, and is not a register the caller reads.
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(7, 8),
                },
                R2ILOp::Copy {
                    dst: reg(8, 8),
                    src: Varnode::constant(9, 8),
                },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&x86_64_arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &x86_64_return_storages());

        let returned = graph
            .values
            .iter()
            .position(|value| value.var.name.eq_ignore_ascii_case("rax"))
            .map(|index| ValueId(index as u32))
            .expect("a value in the return register");
        let discarded = graph
            .values
            .iter()
            .position(|value| value.var.name.eq_ignore_ascii_case("rcx"))
            .map(|index| ValueId(index as u32))
            .expect("a value in a register the caller does not read");

        assert!(is_read(&graph, &live, returned));
        assert!(
            !is_read(&graph, &live, discarded),
            "live-out must widen what counts as read, not make everything read"
        );
    }
    // The facts below arrived with dead code elimination, which asserted them by
    // running and checking what survived. The pass is gone; the facts are not.
    // Each is a property of the liveness this module computes -- which writes the
    // caller reads out of a return register, and which a later write shadows --
    // so each now asks that question directly instead of through a transformation
    // nobody runs.

    fn storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    /// A body writing the whole return register and then its low byte.
    fn return_alias_function(whole_name: &str, low_name: &str) -> SSAFunction {
        let mut arch = ArchSpec::new("return-alias-test");
        arch.add_register(RegisterDef::new(whole_name, 0, 8));
        arch.add_register(RegisterDef::sub(low_name, 0, 1, whole_name));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: reg(0, 8),
            src: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::Copy {
            dst: reg(0, 1),
            src: Varnode::constant(1, 1),
        });
        block.push(R2ILOp::Return {
            target: reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("return alias SSA")
    }

    /// A body writing only the low half of the return register.
    fn narrow_return_function() -> SSAFunction {
        let mut arch = ArchSpec::new("narrow-return-test");
        arch.add_register(RegisterDef::new("carrier", 0, 8));
        arch.add_register(RegisterDef::sub("logical_result", 0, 4, "carrier"));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: reg(0, 4),
            src: Varnode::constant(7, 4),
        });
        block.push(R2ILOp::Return {
            target: reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("narrow return SSA")
    }

    /// Two arms writing the whole register, merging, then a low overlay.
    fn return_phi_overlay_function() -> SSAFunction {
        let mut arch = ArchSpec::new("return-phi-overlay-test");
        arch.add_register(RegisterDef::new("carrier", 0, 8));
        arch.add_register(RegisterDef::sub("low_lane", 0, 1, "carrier"));
        arch.add_register(RegisterDef::new("cond", 0x40, 1));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: reg(0x40, 1),
        });
        let mut left = R2ILBlock::new(0x1004, 4);
        left.push(R2ILOp::Copy {
            dst: reg(0, 8),
            src: Varnode::constant(1, 8),
        });
        left.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut right = R2ILBlock::new(0x1008, 4);
        right.push(R2ILOp::Copy {
            dst: reg(0, 8),
            src: Varnode::constant(2, 8),
        });
        right.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });
        let mut merge = R2ILBlock::new(0x100c, 4);
        merge.push(R2ILOp::Copy {
            dst: reg(0, 1),
            src: Varnode::constant(3, 1),
        });
        merge.push(R2ILOp::Return {
            target: reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[entry, left, right, merge], Some(&arch))
            .expect("return phi overlay SSA")
    }

    /// A body writing the low byte twice, so the first is shadowed.
    fn shadowed_overlay_function(whole_name: &str, low_name: &str) -> SSAFunction {
        let mut arch = ArchSpec::new("shadowed-return-overlay-test");
        arch.add_register(RegisterDef::new(whole_name, 0, 8));
        arch.add_register(RegisterDef::sub(low_name, 0, 1, whole_name));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: reg(0, 8),
            src: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::Copy {
            dst: reg(0, 1),
            src: Varnode::constant(1, 1),
        });
        block.push(R2ILOp::Copy {
            dst: reg(0, 1),
            src: Varnode::constant(2, 1),
        });
        block.push(R2ILOp::Return {
            target: reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("shadowed overlay SSA")
    }

    /// A frame pointer restored from the stack before returning.
    fn frame_pop_function(frame_name: &str, frame_offset: u64) -> SSAFunction {
        let mut arch = ArchSpec::new("frame-pop-test");
        arch.add_register(RegisterDef::new(frame_name, frame_offset, 8));
        arch.add_register(RegisterDef::new("stack_base", 0x40, 8));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::new(SpaceId::Unique, 0x100, 8),
            space: SpaceId::Ram,
            addr: reg(0x40, 8),
        });
        block.push(R2ILOp::Copy {
            dst: reg(frame_offset, 8),
            src: Varnode::new(SpaceId::Unique, 0x100, 8),
        });
        // A non-register destination may share the frame pointer's numeric
        // offset, and must not be mistaken for it.
        block.push(R2ILOp::Copy {
            dst: Varnode::new(SpaceId::Unique, frame_offset, 8),
            src: Varnode::constant(0x55, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: reg(0x40, 8),
            a: reg(0x40, 8),
            b: Varnode::constant(16, 8),
        });
        block.push(R2ILOp::Return {
            target: reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("frame pop SSA")
    }

    /// A frame pointer restored in a block that then branches to its returns.
    fn predecessor_frame_restore_function(frame_offset: u64, split: bool) -> SSAFunction {
        let mut arch = ArchSpec::new("predecessor-frame-restore-test");
        arch.add_register(RegisterDef::new("frame_carrier", frame_offset, 8));
        arch.add_register(RegisterDef::new("condition", 0x20, 1));
        arch.add_register(RegisterDef::new("stack_base", 0x40, 8));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut restore = R2ILBlock::new(0x1000, 4);
        restore.push(R2ILOp::Load {
            dst: Varnode::new(SpaceId::Unique, 0x100, 8),
            space: SpaceId::Ram,
            addr: reg(0x40, 8),
        });
        restore.push(R2ILOp::Copy {
            dst: reg(frame_offset, 8),
            src: Varnode::new(SpaceId::Unique, 0x100, 8),
        });
        if split {
            restore.push(R2ILOp::CBranch {
                target: Varnode::constant(0x1008, 8),
                cond: reg(0x20, 1),
            });
        } else {
            restore.push(R2ILOp::Branch {
                target: Varnode::constant(0x1004, 8),
            });
        }
        let mut first_return = R2ILBlock::new(0x1004, 4);
        first_return.push(R2ILOp::Return {
            target: reg(0x80, 8),
        });
        let mut blocks = vec![restore, first_return];
        if split {
            let mut second_return = R2ILBlock::new(0x1008, 4);
            second_return.push(R2ILOp::Return {
                target: reg(0x80, 8),
            });
            blocks.push(second_return);
        }
        SSAFunction::from_blocks_raw(&blocks, Some(&arch)).expect("predecessor frame restore SSA")
    }

    /// The storages of the values the caller reads, in graph order.
    fn live_storages(func: &SSAFunction, read: &[CanonicalStorageId]) -> Vec<CanonicalStorageId> {
        let graph = SsaGraph::from_function(func);
        let live = FunctionLiveOut::compute(func, &graph, read);
        let mut storages = live
            .iter()
            .filter_map(|value| graph.value(value))
            .filter_map(|value| value.canonical_storage)
            .collect::<Vec<_>>();
        storages.sort_by_key(|s| (s.offset, s.size));
        storages
    }

    #[test]
    fn wide_return_base_and_low_overlay_are_both_live() {
        // `xor eax, eax; sete al` -- the caller reads a composition, so the
        // full-width base and the byte laid over it are both what it reads.
        let func = return_alias_function("carrier", "low_lane");
        assert_eq!(
            live_storages(&func, &[storage(0, 8)]),
            vec![storage(0, 1), storage(0, 8)]
        );
    }

    #[test]
    fn a_narrow_write_covering_the_logical_return_is_live() {
        let func = narrow_return_function();
        assert_eq!(live_storages(&func, &[storage(0, 8)]), vec![storage(0, 4)]);
    }

    #[test]
    fn a_return_merge_beneath_a_later_overlay_stays_live() {
        // The overlay does not cover the whole register, so the merge under it
        // still supplies the remaining bytes, and each arm still supplies the
        // merge.
        let func = return_phi_overlay_function();
        assert_eq!(
            live_storages(&func, &[storage(0, 8)]),
            vec![storage(0, 1), storage(0, 8)],
            "the overlay and the merge beneath it"
        );
        // The arms are not live *out*: the merge is the definition the caller
        // reaches, and the walk stops there. They stay alive because the merge
        // reads them, which is an ordinary use, and `is_read` is the question
        // that covers both reasons a value survives.
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &[storage(0, 8)]);
        for arm in [0x1004, 0x1008] {
            let defined = func
                .get_block(arm)
                .expect("arm block")
                .ops
                .iter()
                .filter_map(|op| op.dst())
                .filter(|dst| func.canonical_storage_for_var(dst) == Some(storage(0, 8)))
                .filter_map(|dst| graph.value_id_for_var(dst))
                .collect::<Vec<_>>();
            assert_eq!(defined.len(), 1, "arm {arm:#x}");
            assert!(is_read(&graph, &live, defined[0]), "arm {arm:#x}");
        }
    }

    #[test]
    fn a_shadowed_overlay_is_reported_live_although_the_caller_cannot_read_it() {
        // Two writes to the low byte. The caller reads only the second, so the
        // first supplies nothing, and dead code elimination used to say so.
        // This walk does not: it stops only on a write that covers the whole
        // return storage, so a narrower write never ends the search and every
        // write to the location on the way is reported.
        //
        // The imprecision is in the safe direction -- a value called live is
        // kept, and keeping one that is dead costs a statement rather than an
        // answer -- which is why it is recorded here rather than fixed under a
        // deletion. Making it exact means tracking which bytes a later write
        // has already supplied, the way the removed pass did with its
        // uncovered-range list, and that is a change to what every consumer of
        // `FunctionLiveOut` sees.
        for (whole, low) in [("whole_a", "slice_a"), ("whole_b", "slice_b")] {
            let func = shadowed_overlay_function(whole, low);
            let graph = SsaGraph::from_function(&func);
            let live = FunctionLiveOut::compute(&func, &graph, &[storage(0, 8)]);
            let overlays = func
                .get_block(0x1000)
                .expect("return block")
                .ops
                .iter()
                .filter_map(|op| op.dst())
                .filter(|dst| func.canonical_storage_for_var(dst) == Some(storage(0, 1)))
                .filter_map(|dst| graph.value_id_for_var(dst))
                .collect::<Vec<_>>();
            assert_eq!(overlays.len(), 2, "{whole}");
            assert!(live.contains(overlays[1]), "the surviving write, {whole}");
            assert!(
                live.contains(overlays[0]),
                "the shadowed write is over-approximated as live, {whole}"
            );
        }
    }

    #[test]
    fn return_liveness_is_carrier_name_independent() {
        assert_eq!(
            live_storages(
                &return_alias_function("whole_a", "slice_a"),
                &[storage(0, 8)]
            ),
            live_storages(
                &return_alias_function("whole_b", "slice_b"),
                &[storage(0, 8)]
            )
        );
    }

    #[test]
    fn a_register_named_like_a_return_but_outside_it_is_not_live() {
        // `rax` at an offset the source-owned return storage does not name
        // earns nothing from its spelling.
        let mut arch = ArchSpec::new("spoofed-return-name-test");
        arch.add_register(RegisterDef::new("actual_carrier", 0, 8));
        arch.add_register(RegisterDef::new("rax", 0x40, 8));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: reg(0, 8),
            src: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::Copy {
            dst: reg(0x40, 8),
            src: Varnode::constant(9, 8),
        });
        block.push(R2ILOp::Return {
            target: reg(0x80, 8),
        });
        let func = SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("spoofed SSA");
        assert_eq!(live_storages(&func, &[storage(0, 8)]), vec![storage(0, 8)]);
    }

    #[test]
    fn nothing_is_live_out_when_no_storage_is_named() {
        // Without a source-owned return storage there is no register the caller
        // is entitled to read, and no name in the body may stand in for one.
        let func = return_alias_function("rax", "al");
        assert!(live_storages(&func, &[]).is_empty());
    }

    #[test]
    fn a_frame_pointer_restore_reaching_a_return_is_live() {
        // A callee-saved register put back before returning is read by the
        // caller in exactly the sense a return value is, so the same walk
        // answers for it once the frame storage is named as one the caller
        // reads. Whether it may be named is the interface's question, and
        // `SourceFunctionInterface::exact_frame_pointer_storage` answers it --
        // see the tests beside it in `r2source`.
        let func = frame_pop_function("callee_frame_carrier", 0);
        assert_eq!(live_storages(&func, &[storage(0, 8)]), vec![storage(0, 8)]);
    }

    #[test]
    fn a_frame_pointer_restore_is_live_from_each_return_it_reaches() {
        for split in [false, true] {
            let func = predecessor_frame_restore_function(0, split);
            assert_eq!(
                live_storages(&func, &[storage(0, 8)]),
                vec![storage(0, 8)],
                "one restore in a predecessor answers every return below it"
            );
        }
    }

    #[test]
    fn a_frame_pointer_restore_at_another_storage_is_not_live() {
        // The chain exists but writes a different register, so the storage the
        // interface named has no definition and the block is unresolved.
        let func = frame_pop_function("frame_pointer", 0x20);
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &[storage(0, 8)]);
        assert!(live.is_empty(), "{live:?}");
        assert_eq!(live.unresolved_blocks().collect::<Vec<_>>(), vec![0x1000]);
    }

    #[test]
    fn frame_pointer_liveness_is_carrier_name_independent() {
        assert_eq!(
            live_storages(
                &frame_pop_function("ordinary_saved_base", 0),
                &[storage(0, 8)]
            ),
            live_storages(
                &frame_pop_function("unrelated_display_name", 0),
                &[storage(0, 8)]
            )
        );
    }
}
