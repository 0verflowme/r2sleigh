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

use crate::abi::AbiProfile;
use crate::function::SSAFunction;
use crate::graph::{SsaGraph, ValueId};

/// The values a function hands back to its caller.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionLiveOut {
    values: BTreeSet<ValueId>,
    /// Return blocks where no definition of a return register could be found.
    unresolved: BTreeSet<u64>,
}

impl FunctionLiveOut {
    /// Work out what leaves through the return registers of every returning block.
    pub fn compute(func: &SSAFunction, graph: &SsaGraph, abi: &AbiProfile) -> Self {
        let mut live = Self::default();
        for block in func.blocks() {
            let returns = func
                .cfg()
                .get_block(block.addr)
                .is_some_and(|cfg| cfg.is_return());
            if !returns {
                continue;
            }
            let mut found = false;
            // The last write in the block wins, because that is what the caller
            // sees; a merge at the head only reaches the exit if nothing overwrote it.
            for op in block.ops.iter().rev() {
                let Some(dst) = op.dst() else {
                    continue;
                };
                if !abi.is_return_register(&dst.name.to_ascii_lowercase()) {
                    continue;
                }
                if let Some(value) = graph.value_id_for_var(dst) {
                    found |= live.values.insert(value);
                }
            }
            for phi in &block.phis {
                if !abi.is_return_register(&phi.dst.name.to_ascii_lowercase()) {
                    continue;
                }
                let overwritten = block.ops.iter().any(|op| {
                    op.dst()
                        .is_some_and(|dst| dst.name == phi.dst.name && dst.size == phi.dst.size)
                });
                if overwritten {
                    continue;
                }
                if let Some(value) = graph.value_id_for_var(&phi.dst) {
                    found |= live.values.insert(value);
                }
            }
            // A returning block that neither defines nor merges a return register
            // is answered by a predecessor, which this pass does not walk. Saying
            // so is better than reporting an empty set as though it were an answer.
            if !found {
                live.unresolved.insert(block.addr);
            }
        }
        live
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

    fn x86_64_abi() -> AbiProfile {
        AbiProfile::from_arch(Some(&x86_64_arch()))
    }

    #[test]
    fn the_value_a_function_returns_is_read_even_with_no_use_sites() {
        let func = returning_function();
        let graph = SsaGraph::from_function(&func);
        let abi = x86_64_abi();

        let live = FunctionLiveOut::compute(&func, &graph, &abi);

        assert_eq!(live.len(), 1, "the return register value should be live out");
        let value = live.iter().next().expect("one live value");
        // This is the case the use list alone gets wrong.
        assert!(graph.use_sites(value).is_empty());
        assert!(is_read(&graph, &live, value));
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
        let func =
            SSAFunction::from_blocks_with_arch(&[block], Some(&x86_64_arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);

        let live = FunctionLiveOut::compute(&func, &graph, &x86_64_abi());

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
        let func =
            SSAFunction::from_blocks_with_arch(&[block], Some(&x86_64_arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &x86_64_abi());

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
}
