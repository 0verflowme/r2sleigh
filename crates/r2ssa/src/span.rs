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

use crate::function::SSAFunction;
use crate::graph::{SsaGraph, ValueId};

/// One run of definitions over which a storage holds a single value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpanId(u32);

/// Which values belong to the same run of one storage.
///
/// Construction roots are deliberately not retained: union-by-rank chooses a
/// representative based on traversal order, so exposing that root as a span
/// identity makes otherwise identical artifacts disagree. Finalized IDs are
/// dense and ordered by the minimum stable [`ValueId`] in each component.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StorageSpans {
    span_by_value: Vec<SpanId>,
    members_by_span: Vec<Box<[ValueId]>>,
}

/// Mutable construction state that cannot escape as a semantic artifact.
struct StorageSpanBuilder {
    parent: Vec<u32>,
    rank: Vec<u8>,
}

impl StorageSpans {
    /// Cut every storage into the runs over which it holds one value.
    pub(crate) fn compute(func: &SSAFunction, graph: &SsaGraph) -> Self {
        let mut builder = StorageSpanBuilder::new(graph.values.len());

        let storage_of = |value: ValueId| {
            graph
                .value(value)
                .and_then(|value| value.canonical_storage)
                .filter(|storage| !storage.is_unknown())
        };
        // A definition that reads its own storage continues that storage's run.
        // One that reads none of it begins a new run, whatever it is called.
        let join_with_same_storage =
            |output: ValueId, inputs: &[ValueId], builder: &mut StorageSpanBuilder| {
                let Some(storage) = storage_of(output) else {
                    return;
                };
                for input in inputs {
                    if storage_of(*input)
                        .is_some_and(|other| storage.location() == other.location())
                    {
                        builder.union(output, *input);
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
                join_with_same_storage(output, &sources, &mut builder);
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
                join_with_same_storage(output, &inst.inputs, &mut builder);
            }
        }
        builder.finalize()
    }

    /// The run this value belongs to.
    pub fn span_of(&self, value: ValueId) -> Option<SpanId> {
        self.span_by_value.get(value.0 as usize).copied()
    }

    /// Exact members of one run, sorted by dense [`ValueId`].
    pub fn members(&self, span: SpanId) -> Option<&[ValueId]> {
        self.members_by_span.get(span.0 as usize).map(Box::as_ref)
    }

    /// Whether every one of these values is the same storage holding one value.
    pub fn all_one_span(&self, values: impl IntoIterator<Item = ValueId>) -> bool {
        let mut first = None;
        for value in values {
            let Some(span) = self.span_of(value) else {
                return false;
            };
            if first.is_some_and(|first| first != span) {
                return false;
            }
            first = Some(span);
        }
        first.is_some()
    }
}

impl StorageSpanBuilder {
    fn new(value_count: usize) -> Self {
        Self {
            parent: (0..value_count as u32).collect(),
            rank: vec![0; value_count],
        }
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

    /// Find with path compression, so construction stays effectively linear.
    fn find_mut(&mut self, mut index: u32) -> u32 {
        while self.parent[index as usize] != index {
            let grandparent = self.parent[self.parent[index as usize] as usize];
            self.parent[index as usize] = grandparent;
            index = grandparent;
        }
        index
    }

    fn finalize(mut self) -> StorageSpans {
        let roots = (0..self.parent.len())
            .map(|index| self.find_mut(index as u32))
            .collect::<Vec<_>>();
        let mut minimum_by_root = vec![None::<u32>; roots.len()];
        for (member, root) in roots.iter().copied().enumerate() {
            let minimum = &mut minimum_by_root[root as usize];
            *minimum = Some(minimum.map_or(member as u32, |old| old.min(member as u32)));
        }

        let mut component_starts = vec![false; roots.len()];
        for minimum in minimum_by_root.iter().flatten() {
            component_starts[*minimum as usize] = true;
        }
        let mut next_span = 0;
        let span_by_minimum = component_starts
            .into_iter()
            .map(|is_start| {
                is_start.then(|| {
                    let span = SpanId(next_span);
                    next_span += 1;
                    span
                })
            })
            .collect::<Vec<_>>();
        let span_by_value = roots
            .into_iter()
            .map(|root| {
                let minimum = minimum_by_root[root as usize]
                    .expect("every finalized root has at least one member");
                span_by_minimum[minimum as usize]
                    .expect("every component minimum has a canonical span")
            })
            .collect::<Vec<_>>();
        let mut members_by_span = vec![Vec::new(); next_span as usize];
        for (index, span) in span_by_value.iter().copied().enumerate() {
            members_by_span[span.0 as usize].push(ValueId(index as u32));
        }
        StorageSpans {
            span_by_value,
            members_by_span: members_by_span
                .into_iter()
                .map(Vec::into_boxed_slice)
                .collect(),
        }
    }
}

#[cfg(test)]
impl StorageSpans {
    fn from_unions(value_count: usize, unions: &[(ValueId, ValueId)]) -> Self {
        let mut builder = StorageSpanBuilder::new(value_count);
        for &(left, right) in unions {
            builder.union(left, right);
        }
        builder.finalize()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
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
    fn finalized_span_ids_ignore_union_order_and_direction() {
        let forward = [
            (ValueId(5), ValueId(3)),
            (ValueId(3), ValueId(4)),
            (ValueId(2), ValueId(1)),
        ];
        let reversed = [
            (ValueId(1), ValueId(2)),
            (ValueId(4), ValueId(3)),
            (ValueId(3), ValueId(5)),
        ];

        assert_eq!(
            StorageSpans::from_unions(6, &forward),
            StorageSpans::from_unions(6, &reversed)
        );
    }

    proptest! {
        #[test]
        fn finalized_span_ids_ignore_arbitrary_union_schedules(
            value_count in 1usize..64,
            raw_edges in prop::collection::vec(
                (any::<u8>(), any::<u8>(), any::<u16>(), any::<bool>()),
                0..128,
            ),
        ) {
            let baseline_edges = raw_edges
                .iter()
                .map(|(left, right, _, _)| {
                    (
                        ValueId(u32::from(*left) % value_count as u32),
                        ValueId(u32::from(*right) % value_count as u32),
                    )
                })
                .collect::<Vec<_>>();
            let baseline = StorageSpans::from_unions(value_count, &baseline_edges);

            let mut scheduled = raw_edges
                .iter()
                .enumerate()
                .map(|(index, (left, right, order, reverse))| {
                    let left = ValueId(u32::from(*left) % value_count as u32);
                    let right = ValueId(u32::from(*right) % value_count as u32);
                    let edge = if *reverse { (right, left) } else { (left, right) };
                    (*order, index, edge)
                })
                .collect::<Vec<_>>();
            scheduled.sort_by_key(|(order, index, _)| (*order, *index));
            let scheduled_edges = scheduled
                .into_iter()
                .map(|(_, _, edge)| edge)
                .collect::<Vec<_>>();

            prop_assert_eq!(
                baseline,
                StorageSpans::from_unions(value_count, &scheduled_edges)
            );
        }
    }

    #[test]
    fn finalized_span_ids_are_dense_in_minimum_member_order() {
        let spans = StorageSpans::from_unions(
            6,
            &[
                (ValueId(5), ValueId(0)),
                (ValueId(5), ValueId(4)),
                (ValueId(2), ValueId(1)),
            ],
        );

        assert_eq!(spans.span_of(ValueId(0)), Some(SpanId(0)));
        assert_eq!(spans.span_of(ValueId(4)), Some(SpanId(0)));
        assert_eq!(spans.span_of(ValueId(5)), Some(SpanId(0)));
        assert_eq!(spans.span_of(ValueId(1)), Some(SpanId(1)));
        assert_eq!(spans.span_of(ValueId(2)), Some(SpanId(1)));
        assert_eq!(spans.span_of(ValueId(3)), Some(SpanId(2)));
        assert_eq!(spans.span_of(ValueId(6)), None);
        assert_eq!(
            spans.members(SpanId(0)),
            Some([ValueId(0), ValueId(4), ValueId(5)].as_slice())
        );
        assert_eq!(
            spans.members(SpanId(1)),
            Some([ValueId(1), ValueId(2)].as_slice())
        );
        assert_eq!(spans.members(SpanId(2)), Some([ValueId(3)].as_slice()));
        assert_eq!(spans.members(SpanId(3)), None);
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
