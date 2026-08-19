//! Which entries of a pointer table a call can actually reach.
//!
//! A call through `table[index]` reaches exactly the entries `index` can select,
//! and nothing else. The table's contents are a fact the source carries; the
//! range of the index is not, because it follows from the branches that had to
//! be taken to arrive at the call. Proving that range is what turns an opaque
//! dispatch into a set of real edges.
//!
//! The proof is deliberately narrow. A block that strictly dominates the call
//! and ends in a conditional branch tells us which way that branch went, but
//! only when exactly one of its successors dominates the call: if both do, the
//! condition says nothing about how we got here. Every such branch contributes
//! one bound on one value, the bounds are intersected, and a range that is not
//! fully pinned inside the table yields nothing at all.
//!
//! Failing closed is the point. An unproven target set would be a guess about
//! control flow, and a wrong edge is worse than a missing one.

use crate::block::SSABlock;
use crate::domtree::DomTree;
use crate::{SSAOp, SSAVar};
use std::collections::HashMap;

/// A call site and the table entries it can reach.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedIndirectCall {
    pub block_addr: u64,
    pub op_index: usize,
    pub table_address: u64,
    pub targets: Vec<u64>,
}

/// Inclusive bounds on one value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Interval {
    low: i128,
    high: i128,
}

impl Interval {
    const fn unbounded() -> Self {
        Self {
            low: i128::MIN,
            high: i128::MAX,
        }
    }

    fn meet(self, other: Self) -> Self {
        Self {
            low: self.low.max(other.low),
            high: self.high.min(other.high),
        }
    }

    const fn is_empty(self) -> bool {
        self.low > self.high
    }
}

/// One table of function pointers as the caller sees it.
pub trait PointerTable {
    fn address(&self) -> u64;
    fn targets(&self) -> &[u64];
}

/// The exact value a constant carries.
///
/// Reads the semantic bitvector rather than the printed name: the name is
/// presentation and a proof must not be built on it.
fn constant_of(var: &SSAVar) -> Option<i128> {
    var.constant_bits().map(i128::from)
}

/// Map every defined name to the operation that defines it.
fn definitions(blocks: &[SSABlock]) -> HashMap<String, (&SSAOp, u64)> {
    let mut defs = HashMap::new();
    for block in blocks {
        for op in &block.ops {
            if let Some(dst) = op.dst() {
                defs.insert(dst.display_name(), (op, block.addr));
            }
        }
    }
    defs
}

/// The bound a comparison places on one side when it is known to hold.
///
/// Only a comparison against a literal says anything usable here: two unknown
/// values bound each other and neither is pinned.
fn bound_from_comparison(op: &SSAOp, holds: bool) -> Option<(String, Interval)> {
    let (a, b, strict, signed) = match op {
        SSAOp::IntSLess { a, b, .. } => (a, b, true, true),
        SSAOp::IntSLessEqual { a, b, .. } => (a, b, false, true),
        SSAOp::IntLess { a, b, .. } => (a, b, true, false),
        SSAOp::IntLessEqual { a, b, .. } => (a, b, false, false),
        _ => return None,
    };
    // An unsigned comparison also proves the value is not negative, which is
    // half the bound a table index needs.
    let floor = if signed { i128::MIN } else { 0 };
    if let Some(limit) = constant_of(b) {
        // a < limit, or its negation limit <= a
        let interval = if holds {
            Interval {
                low: floor,
                high: if strict { limit - 1 } else { limit },
            }
        } else {
            Interval {
                low: if strict { limit } else { limit + 1 },
                high: i128::MAX,
            }
        };
        return Some((a.display_name(), interval));
    }
    if let Some(limit) = constant_of(a) {
        // limit < b, or its negation b <= limit
        let interval = if holds {
            Interval {
                low: if strict { limit + 1 } else { limit },
                high: i128::MAX,
            }
        } else {
            Interval {
                low: floor,
                high: if strict { limit } else { limit - 1 },
            }
        };
        return Some((b.display_name(), interval));
    }
    None
}

/// Bounds that hold on every path reaching `call_block`.
fn proven_bounds(
    blocks: &[SSABlock],
    domtree: &DomTree,
    defs: &HashMap<String, (&SSAOp, u64)>,
    call_block: u64,
) -> HashMap<String, Interval> {
    let mut bounds: HashMap<String, Interval> = HashMap::new();
    for block in blocks {
        if block.addr == call_block || !domtree.dominates(block.addr, call_block) {
            continue;
        }
        let Some(SSAOp::CBranch { target, cond }) = block.ops.last() else {
            continue;
        };
        let Some(taken) = constant_of(target).and_then(|value| u64::try_from(value).ok()) else {
            continue;
        };
        // The branch tells us which way we came only when one side leads here
        // and the other cannot. If both reach the call, it says nothing.
        let taken_dominates = domtree.dominates(taken, call_block);
        let fallthrough = block.addr.checked_add(u64::from(block.size));
        let fallthrough_dominates =
            fallthrough.is_some_and(|next| domtree.dominates(next, call_block));
        let holds = match (taken_dominates, fallthrough_dominates) {
            (true, false) => true,
            (false, true) => false,
            _ => continue,
        };
        let Some((op, _)) = defs.get(&cond.display_name()) else {
            continue;
        };
        if let Some((name, interval)) = bound_from_comparison(op, holds) {
            let merged = bounds
                .get(&name)
                .copied()
                .unwrap_or_else(Interval::unbounded)
                .meet(interval);
            bounds.insert(name, merged);
        }
    }
    bounds
}

/// Split an address into the table it indexes and the value indexing it.
fn table_and_index<'a>(
    defs: &HashMap<String, (&'a SSAOp, u64)>,
    addr: &SSAVar,
) -> Option<(u64, String, u64)> {
    let (SSAOp::IntAdd { a, b, .. }, _) = defs.get(&addr.display_name())? else {
        return None;
    };
    // Either operand may carry the base; the other has to scale an index.
    for (base, scaled) in [(a, b), (b, a)] {
        let Some(base_value) = constant_of(base).and_then(|value| u64::try_from(value).ok()) else {
            continue;
        };
        let Some((scale_op, _)) = defs.get(&scaled.display_name()) else {
            continue;
        };
        let (index, scale) = match scale_op {
            SSAOp::IntMult { a, b, .. } => match (constant_of(b), constant_of(a)) {
                (Some(scale), _) => (a, scale),
                (_, Some(scale)) => (b, scale),
                _ => continue,
            },
            SSAOp::IntLeft { a, b, .. } => match constant_of(b) {
                Some(shift) if shift < 8 => (a, 1i128 << shift),
                _ => continue,
            },
            _ => continue,
        };
        let scale = u64::try_from(scale).ok()?;
        if scale == 0 {
            continue;
        }
        return Some((base_value, index.display_name(), scale));
    }
    None
}

/// Resolve every indirect call whose reachable target set can be proven.
pub fn resolve_indirect_calls<T: PointerTable>(
    blocks: &[SSABlock],
    domtree: &DomTree,
    tables: &[T],
) -> Vec<ResolvedIndirectCall> {
    let defs = definitions(blocks);
    let mut resolved = Vec::new();
    for block in blocks {
        for (op_index, op) in block.ops.iter().enumerate() {
            let SSAOp::CallInd { target } = op else {
                continue;
            };
            // The callee is whatever the table held, so the target has to be a
            // load rather than a computed address.
            let Some((SSAOp::Load { addr, .. }, _)) = defs.get(&target.display_name()) else {
                continue;
            };
            let Some((base, index, scale)) = table_and_index(&defs, addr) else {
                continue;
            };
            let Some(table) = tables.iter().find(|table| table.address() == base) else {
                continue;
            };
            let bounds = proven_bounds(blocks, domtree, &defs, block.addr);
            let Some(interval) = bounds.get(&index).copied() else {
                continue;
            };
            if interval.is_empty() || interval.low < 0 {
                continue;
            }
            let entries = i128::try_from(table.targets().len()).unwrap_or(0);
            // A range reaching past the last entry we read is not proven: the
            // table may continue where the read stopped.
            if interval.high >= entries {
                continue;
            }
            let low = usize::try_from(interval.low).unwrap_or(usize::MAX);
            let high = usize::try_from(interval.high).unwrap_or(usize::MAX);
            let Some(selected) = table.targets().get(low..=high) else {
                continue;
            };
            // Scale must match the entries actually read, or the index does not
            // step through this table.
            if scale == 0 || selected.is_empty() {
                continue;
            }
            resolved.push(ResolvedIndirectCall {
                block_addr: block.addr,
                op_index,
                table_address: table.address(),
                targets: selected.to_vec(),
            });
        }
    }
    resolved
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::SSABlock;

    struct Table {
        address: u64,
        targets: Vec<u64>,
    }

    impl PointerTable for Table {
        fn address(&self) -> u64 {
            self.address
        }
        fn targets(&self) -> &[u64] {
            &self.targets
        }
    }

    /// A dominator tree for a straight guard: entry dominates both arms.
    fn domtree_for(blocks: &[SSABlock], taken: u64, fallthrough: Option<u64>) -> DomTree {
        let entry = blocks[0].addr;
        let mut cfg = crate::cfg::CFG::new(entry);
        for block in blocks {
            let mut basic = crate::cfg::BasicBlock::new(block.addr);
            basic.size = block.size;
            basic.terminator = if block.addr != entry {
                crate::cfg::BlockTerminator::Return
            } else if let Some(next) = fallthrough {
                crate::cfg::BlockTerminator::ConditionalBranch {
                    true_target: taken,
                    false_target: next,
                }
            } else {
                crate::cfg::BlockTerminator::Return
            };
            cfg.add_block(basic);
        }
        cfg.rebuild_edges();
        DomTree::compute(&cfg)
    }

    fn var(name: &str) -> SSAVar {
        SSAVar::new(name, 1, 8)
    }

    /// A guarded dispatch: `if (i >= 5) return; call table[i]`.
    ///
    /// Block 0 tests the bound and branches away on failure, so arriving at
    /// block 0x20 proves `i < 5`; the unsigned test proves `i >= 0`.
    fn guarded_dispatch(bound: u64, entries: usize) -> (Vec<SSABlock>, Vec<Table>) {
        let index = var("index");
        let cond = var("cond");
        let scaled = var("scaled");
        let addr = var("addr");
        let callee = var("callee");
        let blocks = vec![
            SSABlock {
                addr: 0,
                size: 0x10,
                ops: vec![
                    SSAOp::IntLess {
                        dst: cond.clone(),
                        a: index.clone(),
                        b: SSAVar::constant(bound, 8),
                    },
                    SSAOp::CBranch {
                        target: SSAVar::constant(0x20, 8),
                        cond: cond.clone(),
                    },
                ],
            },
            SSABlock {
                addr: 0x10,
                size: 0x10,
                ops: vec![SSAOp::Return { target: var("ret") }],
            },
            SSABlock {
                addr: 0x20,
                size: 0x10,
                ops: vec![
                    SSAOp::IntMult {
                        dst: scaled.clone(),
                        a: index.clone(),
                        b: SSAVar::constant(8, 8),
                    },
                    SSAOp::IntAdd {
                        dst: addr.clone(),
                        a: SSAVar::constant(0xc000, 8),
                        b: scaled.clone(),
                    },
                    SSAOp::Load {
                        dst: callee.clone(),
                        space: r2il::SpaceId::Ram,
                        addr: addr.clone(),
                    },
                    SSAOp::CallInd {
                        target: callee.clone(),
                    },
                ],
            },
        ];
        let targets = (0..entries).map(|i| 0x1000 + i as u64 * 0x20).collect();
        (
            blocks,
            vec![Table {
                address: 0xc000,
                targets,
            }],
        )
    }

    #[test]
    fn a_guarded_index_resolves_to_exactly_the_entries_it_can_select() {
        let (blocks, tables) = guarded_dispatch(5, 5);
        let domtree = domtree_for(&blocks, 0x20, Some(0x10));
        let resolved = resolve_indirect_calls(&blocks, &domtree, &tables);
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].table_address, 0xc000);
        assert_eq!(resolved[0].targets, tables[0].targets);
    }

    #[test]
    fn a_guard_wider_than_the_table_proves_nothing() {
        // The index may reach past the entries that were read, so the target
        // set is unknown and must stay unknown rather than be truncated.
        let (blocks, tables) = guarded_dispatch(9, 5);
        let domtree = domtree_for(&blocks, 0x20, Some(0x10));
        assert!(resolve_indirect_calls(&blocks, &domtree, &tables).is_empty());
    }

    #[test]
    fn an_unguarded_index_resolves_to_nothing() {
        let index = var("index");
        let scaled = var("scaled");
        let addr = var("addr");
        let callee = var("callee");
        let blocks = vec![SSABlock {
            addr: 0,
            size: 0x10,
            ops: vec![
                SSAOp::IntMult {
                    dst: scaled.clone(),
                    a: index.clone(),
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::IntAdd {
                    dst: addr.clone(),
                    a: SSAVar::constant(0xc000, 8),
                    b: scaled.clone(),
                },
                SSAOp::Load {
                    dst: callee.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: addr.clone(),
                },
                SSAOp::CallInd {
                    target: callee.clone(),
                },
            ],
        }];
        let domtree = domtree_for(&blocks, 0, None);
        let tables = vec![Table {
            address: 0xc000,
            targets: vec![0x1000, 0x1020],
        }];
        assert!(resolve_indirect_calls(&blocks, &domtree, &tables).is_empty());
    }
}
