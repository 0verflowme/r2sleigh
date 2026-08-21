//! Where a storage stops holding one value and starts holding another.
//!
//! A register is not a variable. A compiler will keep an accumulator in `RAX`
//! for one loop and an index in it for the next, and every layer that reasons
//! about "the value in `RAX`" then has to decide which of those it means. Loop
//! carriers make the problem sharp: a carrier is state a storage preserves
//! across a back edge, so a carrier can span a point where the storage changed
//! what it stands for, and naming all of its versions one variable says two
//! different values are one.
//!
//! What separates them is already in the dataflow. A definition that reads the
//! storage it writes is an update -- `x = x + 1` continues whatever `x` was --
//! while a definition that reads none of the storage's own values starts
//! something new, however the machine happens to spell the destination. Grouping
//! definitions by that rule cuts each storage into spans, and a span is the
//! thing a location has to be.
//!
//! The grouping is a disjoint set over values, so building it costs one pass over
//! the instructions and answering costs effectively constant time.

use std::collections::BTreeSet;

use crate::function::SSAFunction;
use crate::graph::{SsaGraph, ValueId};
use crate::var::CanonicalStorageId;

/// One run of definitions over which a storage holds a single value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpanId(u32);

/// Which values belong to the same run of one storage.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StorageSpans {
    parent: Vec<u32>,
    rank: Vec<u8>,
}

impl StorageSpans {
    /// Cut every storage into the runs over which it holds one value.
    pub fn compute(func: &SSAFunction, graph: &SsaGraph) -> Self {
        let mut spans = Self {
            parent: (0..graph.values.len() as u32).collect(),
            rank: vec![0; graph.values.len()],
        };

        let storage_of = |value: ValueId| -> Option<CanonicalStorageId> {
            graph
                .value(value)
                .and_then(|value| value.canonical_storage)
                .filter(|storage| !storage.is_unknown())
        };
        // A definition that reads its own storage continues that storage's run.
        // One that reads none of it begins a new run, whatever it is called.
        let mut join_with_same_storage = |output: ValueId, inputs: &[ValueId], spans: &mut Self| {
            let Some(storage) = storage_of(output) else {
                return;
            };
            for input in inputs {
                if storage_of(*input).is_some_and(|other| same_run(storage, other)) {
                    spans.union(output, *input);
                }
            }
        };

        for block in func.blocks() {
            for phi in &block.phis {
                let Some(output) = graph.value_id_for_var(&phi.dst) else {
                    continue;
                };
                let sources = phi
                    .sources
                    .iter()
                    .filter_map(|(_, source)| graph.value_id_for_var(source))
                    .collect::<Vec<_>>();
                join_with_same_storage(output, &sources, &mut spans);
            }
            for (op_index, _) in block.ops.iter().enumerate() {
                let Some(inst) = graph
                    .inst_id_for_op_site(block.addr, op_index)
                    .and_then(|inst| graph.inst(inst))
                else {
                    continue;
                };
                let Some(output) = inst.output else {
                    continue;
                };
                join_with_same_storage(output, &inst.inputs, &mut spans);
            }
        }
        spans
    }

    fn union(&mut self, left: ValueId, right: ValueId) {
        let mut a = self.find_mut(left.0);
        let mut b = self.find_mut(right.0);
        if a == b {
            return;
        }
        if self.rank[a as usize] < self.rank[b as usize] {
            std::mem::swap(&mut a, &mut b);
        }
        self.parent[b as usize] = a;
        if self.rank[a as usize] == self.rank[b as usize] {
            self.rank[a as usize] += 1;
        }
    }

    /// Find with path compression, so repeated questions stay effectively constant.
    fn find_mut(&mut self, mut index: u32) -> u32 {
        while self.parent[index as usize] != index {
            let grandparent = self.parent[self.parent[index as usize] as usize];
            self.parent[index as usize] = grandparent;
            index = grandparent;
        }
        index
    }

    /// The run this value belongs to.
    pub fn span_of(&self, value: ValueId) -> Option<SpanId> {
        if value.0 as usize >= self.parent.len() {
            return None;
        }
        // Read-only find; the compressing one is used while building.
        let mut index = value.0;
        while self.parent[index as usize] != index {
            index = self.parent[index as usize];
        }
        Some(SpanId(index))
    }

    /// Whether every one of these values is the same storage holding one value.
    pub fn all_one_span(&self, values: impl IntoIterator<Item = ValueId>) -> bool {
        let mut spans = BTreeSet::new();
        for value in values {
            match self.span_of(value) {
                Some(span) => {
                    spans.insert(span);
                }
                None => return false,
            }
            if spans.len() > 1 {
                return false;
            }
        }
        !spans.is_empty()
    }
}

/// Whether two storage identities are the same place read at possibly different widths.
///
/// Sub-register writes land at the same offset in the same space, so the offset
/// and space are what say "same place" and the size says only how much of it was
/// touched.
fn same_run(left: CanonicalStorageId, right: CanonicalStorageId) -> bool {
    left.space == right.space && left.offset == right.offset
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode::new(SpaceId::Register, offset, size)
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("EAX", 0, 4));
        arch.add_register(RegisterDef::new("RCX", 8, 8));
        arch.add_register(RegisterDef::new("RIP", 0x288, 8));
        arch
    }

    fn value_named(graph: &SsaGraph, name: &str, version: u32) -> ValueId {
        graph
            .values
            .iter()
            .position(|value| {
                value.var.name.eq_ignore_ascii_case(name) && value.var.version == version
            })
            .map(|index| ValueId(index as u32))
            .unwrap_or_else(|| panic!("no {name}_{version}"))
    }

    #[test]
    fn updating_a_register_continues_the_value_it_held() {
        // RAX = RAX + 1 reads what it writes, so both are one run.
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: reg(8, 8),
                },
                R2ILOp::IntAdd {
                    dst: reg(0, 8),
                    a: reg(0, 8),
                    b: Varnode::constant(1, 8),
                },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);
        let spans = StorageSpans::compute(&func, &graph);

        let first = value_named(&graph, "RAX", 1);
        let updated = value_named(&graph, "RAX", 2);
        assert_eq!(spans.span_of(first), spans.span_of(updated));
        assert!(spans.all_one_span([first, updated]));
    }

    #[test]
    fn reassigning_a_register_starts_a_different_value() {
        // The second write reads RCX, not RAX, so RAX stops meaning what it did.
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: reg(0x288, 8),
                },
                R2ILOp::IntAdd {
                    dst: reg(0, 8),
                    a: reg(8, 8),
                    b: Varnode::constant(1, 8),
                },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);
        let spans = StorageSpans::compute(&func, &graph);

        let accumulator = value_named(&graph, "RAX", 1);
        let reused = value_named(&graph, "RAX", 2);
        assert_ne!(
            spans.span_of(accumulator),
            spans.span_of(reused),
            "one register holding two values must not read as one"
        );
        assert!(!spans.all_one_span([accumulator, reused]));
    }

    #[test]
    fn a_value_taken_from_elsewhere_starts_a_run_even_at_another_width() {
        // RAX = zext(EAX) looks like a width alias, but once copy propagation has
        // run the narrow read is whatever produced it, so what RAX now holds came
        // from somewhere else and is a new value rather than the old one widened.
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 4),
                    src: reg(8, 4),
                },
                R2ILOp::IntZExt {
                    dst: reg(0, 8),
                    src: reg(0, 4),
                },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);
        let spans = StorageSpans::compute(&func, &graph);

        let narrow = value_named(&graph, "EAX", 1);
        let wide = value_named(&graph, "RAX", 1);
        assert_ne!(spans.span_of(narrow), spans.span_of(wide));
        assert!(!spans.all_one_span([narrow, wide]));
    }

    #[test]
    fn a_run_is_asked_about_as_a_whole() {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: reg(0, 8),
                    src: reg(8, 8),
                },
                R2ILOp::IntAdd {
                    dst: reg(0, 8),
                    a: reg(0, 8),
                    b: Varnode::constant(1, 8),
                },
                R2ILOp::Return {
                    target: reg(0x288, 8),
                },
            ],
            ..R2ILBlock::default()
        };
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&arch())).expect("ssa");
        let graph = SsaGraph::from_function(&func);
        let spans = StorageSpans::compute(&func, &graph);

        let seeded = value_named(&graph, "RAX", 1);
        let updated = value_named(&graph, "RAX", 2);
        let unrelated = value_named(&graph, "RCX", 0);
        assert!(spans.all_one_span([seeded, updated]));
        assert!(
            !spans.all_one_span([seeded, updated, unrelated]),
            "a run must not absorb a value from another storage"
        );
        assert!(!spans.all_one_span([]), "no values name no run");
    }
}
