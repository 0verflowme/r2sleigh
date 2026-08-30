//! Merges that nothing observes.
//!
//! A lifted body merges every storage live across a join, so an exit block ends
//! up holding a phi for each condition-code bit and each Sleigh temporary that
//! happened to be written on either side. A twelve-instruction function produces
//! forty-nine of them, twenty-four at one loop header, and every rule that has to
//! decide what a loop carries, what deserves a name, or what the output owes has
//! to look at all of them and reject the ones that mean nothing.
//!
//! Removing them was not previously safe to attempt, because "nothing reads this"
//! was not a question the SSA could answer: the value a function returns has no
//! reader in its own body either. With [`crate::liveout`] saying what leaves
//! through the calling convention, the question is answerable, and the ordinary
//! answer applies -- a value is observed if something with an effect depends on
//! it, and a merge no observation depends on is not part of the program.
//!
//! This reports what it found rather than editing the function, and that is not
//! caution: the symbolic executor propagates machine state through merges, so a
//! merge no value observation depends on can still be the only thing telling the
//! executor what a register holds at a loop head. Removing them outright loses a
//! VM dispatch summary that depended on exactly such a merge. Two consumers hold
//! different and both-correct views of the same function, so the set is published
//! for the rules that reason about candidates and the function is left alone for
//! the rules that simulate it.

use std::collections::{BTreeSet, VecDeque};

use crate::graph::{InstId, SsaGraph, UseSite, ValueId};
use crate::liveout::FunctionLiveOut;
use crate::obligation::{SemanticInstructionState, SemanticObligationInventory};
use crate::semantic::{PreparedFunctionFacts, SourceBoundaryFacts, SourceCallArgumentValue};

/// Which merges no observation depends on.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DeadPhis {
    values: BTreeSet<ValueId>,
    /// Complete pure value domain on which no program observation depends.
    ///
    /// This includes dead merge inputs such as an entry condition-code value,
    /// not only the merge outputs. Outputs of effectful operations are kept out
    /// even when nobody consumes their result: the operation still owes its
    /// memory/control/call occurrence.
    unobserved_values: BTreeSet<ValueId>,
    unobserved_insts: BTreeSet<InstId>,
    unobserved_uses: BTreeSet<UseSite>,
}

/// Values with positive evidence that the program observes them.
///
/// This is deliberately not the complement of [`DeadPhis::unobserved_values`].
/// An unsupported instruction can prevent a value from being proven dead, but
/// that uncertainty is refusal evidence, not positive proof that the source
/// program reads the value. Consumers such as interface recovery may make a
/// positive claim only from this narrower certificate.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProvenProgramObservations {
    values: BTreeSet<ValueId>,
}

fn dependency_closure(
    graph: &SsaGraph,
    roots: impl IntoIterator<Item = ValueId>,
) -> BTreeSet<ValueId> {
    let mut observed = BTreeSet::new();
    let mut pending = VecDeque::new();
    for value in roots {
        if observed.insert(value) {
            pending.push_back(value);
        }
    }
    while let Some(value) = pending.pop_front() {
        let Some(inst) = graph.def_inst(value).and_then(|inst| graph.inst(inst)) else {
            continue;
        };
        for input in &inst.inputs {
            if observed.insert(*input) {
                pending.push_back(*input);
            }
        }
    }
    observed
}

impl ProvenProgramObservations {
    /// Close exact live outputs and non-refusal obligations over SSA def-use.
    pub fn find(
        graph: &SsaGraph,
        live_out: &FunctionLiveOut,
        facts: &PreparedFunctionFacts,
    ) -> Option<Self> {
        if !facts.obligations.is_complete() {
            return None;
        }
        let roots = live_out.iter().chain(
            facts
                .obligations
                .obligations()
                .values()
                .filter(|obligation| obligation.id.kind.is_positive_observation_root())
                .flat_map(|obligation| obligation.inputs.iter().copied()),
        );
        Some(Self {
            values: dependency_closure(graph, roots),
        })
    }

    pub fn contains(&self, value: ValueId) -> bool {
        self.values.contains(&value)
    }

    pub fn iter(&self) -> impl Iterator<Item = ValueId> + '_ {
        self.values.iter().copied()
    }
}

impl DeadPhis {
    /// Find the merges nothing observes, following what observation depends on.
    pub fn find(
        graph: &SsaGraph,
        live_out: &FunctionLiveOut,
        facts: &PreparedFunctionFacts,
    ) -> Self {
        Self::find_from(graph, live_out, &facts.obligations, &facts.boundaries)
    }

    /// The same answer, from the two fact tables it actually reads.
    ///
    /// Fact collection itself needs this set: a rule that asks whether the
    /// program reads a value must ask it before the certificates that depend
    /// on the answer are formed, and both inputs are complete by then.
    pub(crate) fn find_from(
        graph: &SsaGraph,
        live_out: &FunctionLiveOut,
        obligations: &SemanticObligationInventory,
        boundaries: &SourceBoundaryFacts,
    ) -> Self {
        // The obligation inventory is the canonical answer to whether an
        // instruction is observable. In particular, exact ABI call arguments
        // are boundary inputs rather than graph inputs, so reconstructing the
        // answer here from opcodes would silently delete their producers.
        if !obligations.is_complete() {
            return Self::default();
        }
        let mut roots = BTreeSet::from_iter(live_out.iter());
        for obligation in obligations.obligations().values() {
            roots.extend(obligation.inputs.iter().copied());
        }
        // Parameters are rendered program variables even when the body does
        // not read them, so their canonical entry values remain in the named
        // domain independently of effect liveness.
        for parameter in boundaries.parameters.values() {
            roots.insert(parameter.value);
        }
        for boundary in boundaries.calls.values() {
            for argument in &boundary.arguments {
                if let SourceCallArgumentValue::Value(value) = argument.value {
                    roots.insert(value);
                }
            }
        }
        // Whatever an observation depends on is observed, transitively. The walk
        // is over the graph's own instruction inputs, so it visits each edge once.
        let observed = dependency_closure(graph, roots);

        let unobserved_values = graph
            .values
            .iter()
            .filter(|value| {
                !observed.contains(&value.id)
                    && graph
                        .def_inst(value.id)
                        .and_then(|inst| obligations.instruction_for_inst(inst))
                        .is_none_or(|instruction| {
                            instruction.state == SemanticInstructionState::ProvenDead
                        })
            })
            .map(|value| value.id)
            .collect();
        let mut dead = Self {
            unobserved_values,
            ..Self::default()
        };
        for inst in &graph.insts {
            if !inst
                .output
                .is_some_and(|output| dead.unobserved_values.contains(&output))
            {
                continue;
            }
            dead.unobserved_insts.insert(inst.id);
            dead.unobserved_uses
                .extend((0..inst.inputs.len()).map(|input_idx| UseSite {
                    inst: inst.id,
                    input_idx,
                }));
        }
        for inst in &graph.insts {
            if matches!(inst.payload, crate::graph::InstPayload::Phi { .. })
                && inst
                    .output
                    .is_some_and(|value| dead.unobserved_values.contains(&value))
            {
                dead.values.insert(inst.output.expect("checked phi output"));
            }
        }
        dead
    }

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

    /// Every pure value outside the transitive observation slice.
    pub const fn unobserved_values(&self) -> &BTreeSet<ValueId> {
        &self.unobserved_values
    }

    /// Every pure definition whose output is in [`Self::unobserved_values`].
    pub const fn unobserved_insts(&self) -> &BTreeSet<InstId> {
        &self.unobserved_insts
    }

    /// Complete input-use domain of [`Self::unobserved_insts`].
    pub const fn unobserved_uses(&self) -> &BTreeSet<UseSite> {
        &self.unobserved_uses
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CanonicalStorageId, CanonicalStorageSpace, SSAFunction};
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode::new(SpaceId::Register, offset, size)
    }

    fn return_storages() -> [CanonicalStorageId; 1] {
        [CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        }]
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("RCX", 8, 8));
        arch.add_register(RegisterDef::new("RDX", 16, 8));
        arch.add_register(RegisterDef::new("ZF", 0x206, 1));
        arch.add_register(RegisterDef::new("RIP", 0x288, 8));
        arch
    }

    /// A diamond that merges one effect input and one dead condition code at exit.
    fn merging_function() -> SSAFunction {
        let entry = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntEqual {
                    dst: reg(0x206, 1),
                    a: reg(8, 8),
                    b: Varnode::constant(0, 8),
                },
                R2ILOp::CBranch {
                    cond: reg(0x206, 1),
                    target: Varnode::constant(0x1008, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let left = R2ILBlock {
            addr: 0x1004,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(1, 8),
                },
                R2ILOp::IntEqual {
                    dst: reg(0x206, 1),
                    a: reg(16, 8),
                    b: Varnode::constant(0, 8),
                },
                R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let right = R2ILBlock {
            addr: 0x1008,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: Varnode::constant(2, 8),
                },
                R2ILOp::IntEqual {
                    dst: reg(0x206, 1),
                    a: reg(16, 8),
                    b: Varnode::constant(1, 8),
                },
                R2ILOp::Branch {
                    target: Varnode::constant(0x100c, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let exit = R2ILBlock {
            addr: 0x100c,
            size: 4,
            ops: vec![R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(0x2000, 8),
                val: reg(0, 8),
            }],
            ..R2ILBlock::default()
        };
        SSAFunction::from_blocks_with_arch(&[entry, left, right, exit], Some(&arch())).expect("ssa")
    }

    #[test]
    fn a_flag_merged_at_a_join_and_never_tested_again_is_not_part_of_the_program() {
        let func = merging_function();
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &return_storages());

        let facts = crate::semantic::PreparedFunctionFacts::collect(&func, &graph);
        let dead = DeadPhis::find(&graph, &live, &facts);

        let exit = func.get_block(0x100c).expect("exit block");
        let zf = exit
            .phis
            .iter()
            .find(|phi| phi.dst.name.eq_ignore_ascii_case("zf"))
            .and_then(|phi| graph.value_id_for_var(&phi.dst));
        assert!(
            zf.is_some_and(|value| dead.contains(value)),
            "a condition code merged and never tested is dead"
        );
        let zf = zf.expect("dead condition-code merge");
        let definition = graph
            .def_inst(zf)
            .and_then(|inst| graph.inst(inst))
            .expect("dead merge definition");
        assert!(dead.unobserved_values().contains(&zf));
        assert!(dead.unobserved_insts().contains(&definition.id));
        for (input_idx, input) in definition.inputs.iter().copied().enumerate() {
            assert!(
                dead.unobserved_values().contains(&input),
                "a value used only by the dead merge belongs to its pure support domain"
            );
            assert!(dead.unobserved_uses().contains(&UseSite {
                inst: definition.id,
                input_idx,
            }));
        }
    }

    #[test]
    fn the_merge_consumed_by_an_observable_effect_survives() {
        let func = merging_function();
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &return_storages());

        let facts = crate::semantic::PreparedFunctionFacts::collect(&func, &graph);
        let dead = DeadPhis::find(&graph, &live, &facts);

        let exit = func.get_block(0x100c).expect("exit block");
        let rax = exit
            .phis
            .iter()
            .find(|phi| phi.dst.name.eq_ignore_ascii_case("rax"))
            .and_then(|phi| graph.value_id_for_var(&phi.dst))
            .expect("the return register is merged at the exit");
        assert!(
            !dead.contains(rax),
            "the value written to memory is observed"
        );
        assert_eq!(graph.use_sites(rax).len(), 1, "the store owns its use site");
    }

    #[test]
    fn a_flag_a_branch_still_tests_survives() {
        let func = merging_function();
        let graph = SsaGraph::from_function(&func);
        let live = FunctionLiveOut::compute(&func, &graph, &return_storages());

        let facts = crate::semantic::PreparedFunctionFacts::collect(&func, &graph);
        let dead = DeadPhis::find(&graph, &live, &facts);

        // The entry block's condition is tested by its own CBranch, so nothing
        // about merging flags elsewhere may reach back and call it unobserved.
        let entry = func.get_block(0x1000).expect("entry block");
        let tested = entry
            .ops
            .iter()
            .find_map(|op| op.dst())
            .and_then(|dst| graph.value_id_for_var(dst))
            .expect("a defined condition");
        assert!(!dead.contains(tested));
    }
}
