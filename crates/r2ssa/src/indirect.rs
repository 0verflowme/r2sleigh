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

use crate::cfg::BlockTerminator;
use crate::function::{SSAFunction, SsaArtifact};
use crate::graph::{GraphInst, InstPayload, SsaGraph, UseSite, ValueId};
use crate::{CanonicalStorageId, CanonicalStorageSpace, SSAOp};
use std::collections::BTreeMap;

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

    /// The smallest interval containing both.
    ///
    /// A disjunction holds when either side does, so what is proven is the
    /// union. Between two intervals the union may have a hole, and covering the
    /// hole is the conservative direction: it claims less about the value.
    fn join(self, other: Self) -> Self {
        Self {
            low: self.low.min(other.low),
            high: self.high.max(other.high),
        }
    }

    const fn is_empty(self) -> bool {
        self.low > self.high
    }
}

/// One table of function pointers as the caller sees it.
pub trait PointerTable {
    fn address(&self) -> u64;
    /// Bytes between consecutive entries, as the table was read.
    fn entry_size(&self) -> u32;
    fn targets(&self) -> &[u64];
}

impl PointerTable for r2source::SourceCodePointerTable {
    fn address(&self) -> u64 {
        Self::address(self)
    }

    fn entry_size(&self) -> u32 {
        Self::entry_size(self)
    }

    fn targets(&self) -> &[u64] {
        Self::targets(self)
    }
}

/// How far a value may be chased back through its definitions.
///
/// Every step is exact, so the limit is not about soundness: it bounds the work
/// on code that defines a value through a long chain, and a chain that runs off
/// the end simply proves nothing.
const MAX_DEFINITION_DEPTH: usize = 32;

pub(crate) fn exact_input(graph: &SsaGraph, inst: &GraphInst, input_idx: usize) -> Option<ValueId> {
    let value = *inst.inputs.get(input_idx)?;
    graph
        .use_sites(value)
        .binary_search(&UseSite {
            inst: inst.id,
            input_idx,
        })
        .is_ok()
        .then_some(value)
}

fn exact_constant(graph: &SsaGraph, value: ValueId) -> Option<u64> {
    let value = graph.value(value)?;
    let bits = value.var.constant_bits()?;
    (value.canonical_storage
        == Some(CanonicalStorageId {
            space: CanonicalStorageSpace::Constant,
            offset: bits,
            size: value.var.size,
        }))
    .then_some(bits)
}

/// Read a folded value as signed at the width it was computed at.
fn signed(value: u64, size: u32) -> i128 {
    let bits = size * 8;
    if bits == 0 || bits >= 64 {
        return i128::from(value as i64);
    }
    i128::from((value as i64) << (64 - bits) >> (64 - bits))
}

/// Keep a folded value inside the width it was computed at.
fn truncate(value: u64, size: u32) -> u64 {
    match size {
        0 | 8.. => value,
        bytes => value & (u64::MAX >> (64 - bytes * 8)),
    }
}

/// The one value a variable can hold, when its definitions leave only one.
///
/// A literal operand is the base case, but real code rarely offers one: an
/// address is materialized across several instructions and moved through
/// temporaries before it is used. Each step folded here is exact -- a copy, a
/// widening, or arithmetic on values already pinned -- so what comes back is
/// the value, not an estimate of it.
pub(crate) fn resolve_constant(graph: &SsaGraph, value: ValueId, depth: usize) -> Option<u64> {
    if let Some(value) = exact_constant(graph, value) {
        return Some(value);
    }
    if depth >= MAX_DEFINITION_DEPTH {
        return None;
    }
    let inst = graph.def_inst(value).and_then(|inst| graph.inst(inst))?;
    let InstPayload::Op(op) = &inst.payload else {
        return None;
    };
    let fold = |input_idx| resolve_constant(graph, exact_input(graph, inst, input_idx)?, depth + 1);
    let folded = match op {
        SSAOp::Copy { .. } | SSAOp::IntZExt { .. } => fold(0)?,
        SSAOp::IntSExt { .. } => {
            let source = exact_input(graph, inst, 0)?;
            let source_value = graph.value(source)?;
            let output = graph.value(value)?;
            let value = fold(0)?;
            // Sign-extending is only exact if we know the width it came from.
            let bits = source_value.var.size * 8;
            if bits == 0 || bits >= 64 || output.var.size <= source_value.var.size {
                return None;
            }
            ((value as i64) << (64 - bits) >> (64 - bits)) as u64
        }
        SSAOp::IntAdd { .. } => fold(0)?.wrapping_add(fold(1)?),
        SSAOp::IntSub { .. } => fold(0)?.wrapping_sub(fold(1)?),
        SSAOp::IntMult { .. } => fold(0)?.wrapping_mul(fold(1)?),
        SSAOp::IntLeft { .. } => {
            let shift = fold(1)?;
            if shift >= 64 {
                return None;
            }
            fold(0)?.wrapping_shl(u32::try_from(shift).ok()?)
        }
        SSAOp::IntOr { .. } => fold(0)? | fold(1)?,
        SSAOp::IntAnd { .. } => fold(0)? & fold(1)?,
        // A condition is decided when the comparison behind it is, which is
        // what makes a branch on it not a branch at all.
        SSAOp::IntEqual { .. } => u64::from(fold(0)? == fold(1)?),
        SSAOp::IntNotEqual { .. } => u64::from(fold(0)? != fold(1)?),
        SSAOp::IntLess { .. } => u64::from(fold(0)? < fold(1)?),
        SSAOp::IntLessEqual { .. } => u64::from(fold(0)? <= fold(1)?),
        SSAOp::IntSLess { .. } => {
            let left = graph.value(exact_input(graph, inst, 0)?)?;
            let right = graph.value(exact_input(graph, inst, 1)?)?;
            u64::from(signed(fold(0)?, left.var.size) < signed(fold(1)?, right.var.size))
        }
        SSAOp::IntSLessEqual { .. } => {
            let left = graph.value(exact_input(graph, inst, 0)?)?;
            let right = graph.value(exact_input(graph, inst, 1)?)?;
            u64::from(signed(fold(0)?, left.var.size) <= signed(fold(1)?, right.var.size))
        }
        SSAOp::BoolNot { .. } => u64::from(fold(0)? == 0),
        SSAOp::BoolAnd { .. } => u64::from(fold(0)? != 0 && fold(1)? != 0),
        SSAOp::BoolOr { .. } => u64::from(fold(0)? != 0 || fold(1)? != 0),
        SSAOp::BoolXor { .. } => u64::from((fold(0)? != 0) != (fold(1)? != 0)),
        _ => return None,
    };
    Some(truncate(folded, graph.value(value)?.var.size))
}

/// The exact SSA value a copied/projected value ultimately stands for.
///
/// A bound is proven against the value one instruction compared, and the index
/// is read several copies later. They are the same value, and the proof only
/// connects them if both are named by where the value came from rather than by
/// which temporary happened to be holding it.
fn canonical_value(graph: &SsaGraph, value: ValueId) -> ValueId {
    let mut current = value;
    for _ in 0..MAX_DEFINITION_DEPTH {
        let Some(inst) = graph.def_inst(current).and_then(|inst| graph.inst(inst)) else {
            return current;
        };
        let next = match &inst.payload {
            InstPayload::Op(SSAOp::Copy { .. } | SSAOp::IntZExt { .. }) => {
                let Some(input) = exact_input(graph, inst, 0) else {
                    return current;
                };
                input
            }
            _ => return current,
        };
        if next == current {
            return current;
        }
        current = next;
    }
    current
}

/// Move a bound off a computed value and onto the value it was computed from.
///
/// Hardware compares by subtracting: the zero flag is not `x == 3` but
/// `x - 3 == 0`. The two say the same thing about `x`, and only the second is
/// written down, so a bound on the difference has to be shifted back onto `x`
/// before it can meet a bound stated about `x` directly.
///
/// Shifting is exact only while it stays inside the width the subtraction was
/// done at. Past that the machine wraps, the true set of values wraps with it,
/// and an interval can no longer describe it -- so the bound is dropped.
fn rebase(graph: &SsaGraph, value: ValueId, interval: Interval) -> Option<(ValueId, Interval)> {
    let mut value = value;
    let mut interval = interval;
    for _ in 0..MAX_DEFINITION_DEPTH {
        let Some(inst) = graph.def_inst(value).and_then(|inst| graph.inst(inst)) else {
            return Some((value, interval));
        };
        let (source, offset) = match &inst.payload {
            InstPayload::Op(SSAOp::IntSub { .. }) => {
                match resolve_constant(graph, exact_input(graph, inst, 1)?, 0) {
                    Some(constant) => (exact_input(graph, inst, 0)?, i128::from(constant)),
                    None => return Some((value, interval)),
                }
            }
            InstPayload::Op(SSAOp::IntAdd { .. }) => {
                let left = exact_input(graph, inst, 0)?;
                let right = exact_input(graph, inst, 1)?;
                match (
                    resolve_constant(graph, right, 0),
                    resolve_constant(graph, left, 0),
                ) {
                    (Some(constant), _) => (left, -i128::from(constant)),
                    (_, Some(constant)) => (right, -i128::from(constant)),
                    _ => return Some((value, interval)),
                }
            }
            _ => return Some((value, interval)),
        };
        let width = graph.value(source)?.var.size * 8;
        if width == 0 || width > 64 {
            return Some((value, interval));
        }
        let ceiling = 1i128 << width;
        let shifted = Interval {
            low: interval.low.checked_add(offset)?,
            high: interval.high.checked_add(offset)?,
        };
        if interval.low < 0
            || interval.high >= ceiling
            || shifted.low < 0
            || shifted.high >= ceiling
        {
            return Some((value, interval));
        }
        let next = canonical_value(graph, source);
        if next == value {
            return Some((value, interval));
        }
        value = next;
        interval = shifted;
    }
    Some((value, interval))
}

/// The bound a comparison places on one side when it is known to hold.
///
/// Only a comparison against a value we can pin says anything usable here: two
/// unknown values bound each other and neither is pinned.
fn bound_from_comparison(
    graph: &SsaGraph,
    inst: &GraphInst,
    holds: bool,
) -> Option<(ValueId, Interval)> {
    let InstPayload::Op(op) = &inst.payload else {
        return None;
    };
    // Equality pins a value exactly when it holds, and says nothing usable when
    // it does not: "anything but seven" is not a range.
    if let SSAOp::IntEqual { .. } | SSAOp::IntNotEqual { .. } = op {
        let equal = matches!(op, SSAOp::IntEqual { .. }) == holds;
        if !equal {
            return None;
        }
        let left = exact_input(graph, inst, 0)?;
        let right = exact_input(graph, inst, 1)?;
        for (value, other) in [(left, right), (right, left)] {
            if let Some(pinned) = resolve_constant(graph, other, 0) {
                let pinned = i128::from(pinned);
                return rebase(
                    graph,
                    canonical_value(graph, value),
                    Interval {
                        low: pinned,
                        high: pinned,
                    },
                );
            }
        }
        return None;
    }
    let (strict, signed) = match op {
        SSAOp::IntSLess { .. } => (true, true),
        SSAOp::IntSLessEqual { .. } => (false, true),
        SSAOp::IntLess { .. } => (true, false),
        SSAOp::IntLessEqual { .. } => (false, false),
        _ => return None,
    };
    let a = exact_input(graph, inst, 0)?;
    let b = exact_input(graph, inst, 1)?;
    // An unsigned comparison also proves the value is not negative, which is
    // half the bound a table index needs.
    let floor = if signed { i128::MIN } else { 0 };
    // A signed comparison reads its literal as signed at the compared width;
    // an unsigned one reads the same bits as a magnitude.
    let literal = |value: ValueId| -> Option<i128> {
        let bits = resolve_constant(graph, value, 0)?;
        let width = graph.value(value)?.var.size * 8;
        if signed && (1..64).contains(&width) {
            Some(i128::from((bits as i64) << (64 - width) >> (64 - width)))
        } else if signed {
            Some(i128::from(bits as i64))
        } else {
            Some(i128::from(bits))
        }
    };
    if let Some(limit) = literal(b) {
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
        return rebase(graph, canonical_value(graph, a), interval);
    }
    if let Some(limit) = literal(a) {
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
        return rebase(graph, canonical_value(graph, b), interval);
    }
    None
}

/// The bound a branch condition places, following how the condition was built.
///
/// Hardware does not compare and branch in one step: the comparison lands in a
/// flag, the flag is copied, and the branch tests it -- often inverted. Each of
/// those is followed here, because the proof is about the comparison and not
/// about which register the answer travelled in.
fn bound_from_condition(
    graph: &SsaGraph,
    condition: ValueId,
    holds: bool,
    depth: usize,
) -> Option<(ValueId, Interval)> {
    if depth >= MAX_DEFINITION_DEPTH {
        return None;
    }
    let inst = graph
        .def_inst(condition)
        .and_then(|inst| graph.inst(inst))?;
    let InstPayload::Op(op) = &inst.payload else {
        return None;
    };
    match op {
        SSAOp::Copy { .. } => {
            bound_from_condition(graph, exact_input(graph, inst, 0)?, holds, depth + 1)
        }
        SSAOp::BoolNot { .. } => {
            bound_from_condition(graph, exact_input(graph, inst, 0)?, !holds, depth + 1)
        }
        // A condition built from two others bounds a value only when both sides
        // bound the same value: otherwise each says something about a different
        // thing and neither survives the combination.
        SSAOp::BoolOr { .. } | SSAOp::BoolAnd { .. } => {
            let disjunction = matches!(op, SSAOp::BoolOr { .. }) == holds;
            let (left_value, left) =
                bound_from_condition(graph, exact_input(graph, inst, 0)?, holds, depth + 1)?;
            let (right_value, right) =
                bound_from_condition(graph, exact_input(graph, inst, 1)?, holds, depth + 1)?;
            if left_value != right_value {
                return None;
            }
            // Either side may hold, so the union; both must hold, so the
            // intersection.
            let combined = if disjunction {
                left.join(right)
            } else {
                left.meet(right)
            };
            Some((left_value, combined))
        }
        _ => bound_from_comparison(graph, inst, holds),
    }
}

/// Bounds that hold on every path reaching `call_block`.
///
/// Control flow is read from the graph rather than re-derived from the branch
/// operand: the graph is what the rest of the analysis agrees on, and a proof
/// that disagreed with it about which edge goes where would be proving
/// something about a different function.
fn proven_bounds(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_block: u64,
) -> BTreeMap<ValueId, Interval> {
    let mut bounds = BTreeMap::new();
    for block in function.blocks() {
        if block.addr == call_block || !function.domtree().dominates(block.addr, call_block) {
            continue;
        }
        let Some((op_index, SSAOp::CBranch { cond, .. })) =
            block.ops.iter().enumerate().next_back()
        else {
            continue;
        };
        let Some(branch_inst) = graph
            .inst_id_for_op_site(block.addr, op_index)
            .and_then(|inst| graph.inst(inst))
        else {
            continue;
        };
        // CBranch input zero is its control target; the predicate is the
        // second exact graph use.
        let Some(condition) = exact_input(graph, branch_inst, 1) else {
            continue;
        };
        if graph.value_id_for_var(cond) != Some(condition) {
            continue;
        }
        let Some(BlockTerminator::ConditionalBranch {
            true_target,
            false_target,
        }) = function
            .cfg()
            .get_block(block.addr)
            .map(|basic| &basic.terminator)
        else {
            continue;
        };
        // The branch tells us which way we came only when one side leads here
        // and the other cannot. If both reach the call, it says nothing.
        let holds = match (
            function.domtree().dominates(*true_target, call_block),
            function.domtree().dominates(*false_target, call_block),
        ) {
            (true, false) => true,
            (false, true) => false,
            _ => continue,
        };
        if let Some((value, interval)) = bound_from_condition(graph, condition, holds, 0) {
            let merged = bounds
                .get(&value)
                .copied()
                .unwrap_or_else(Interval::unbounded)
                .meet(interval);
            bounds.insert(value, merged);
        }
    }
    bounds
}

/// Split an address into the table it indexes and the value indexing it.
fn table_and_index(graph: &SsaGraph, address: ValueId) -> Option<(u64, ValueId, u64)> {
    let address = canonical_value(graph, address);
    let inst = graph.def_inst(address).and_then(|inst| graph.inst(inst))?;
    let InstPayload::Op(SSAOp::IntAdd { .. }) = &inst.payload else {
        return None;
    };
    let left = exact_input(graph, inst, 0)?;
    let right = exact_input(graph, inst, 1)?;
    // Either operand may carry the base; the other has to scale an index.
    for (base, scaled) in [(left, right), (right, left)] {
        let Some(base_value) = resolve_constant(graph, base, 0) else {
            continue;
        };
        let scaled = canonical_value(graph, scaled);
        let Some(scale_inst) = graph.def_inst(scaled).and_then(|inst| graph.inst(inst)) else {
            continue;
        };
        let (index, scale) = match &scale_inst.payload {
            InstPayload::Op(SSAOp::IntMult { .. }) => {
                let a = exact_input(graph, scale_inst, 0)?;
                let b = exact_input(graph, scale_inst, 1)?;
                match (resolve_constant(graph, b, 0), resolve_constant(graph, a, 0)) {
                    (Some(scale), _) => (a, scale),
                    (_, Some(scale)) => (b, scale),
                    _ => continue,
                }
            }
            InstPayload::Op(SSAOp::IntLeft { .. }) => {
                let index = exact_input(graph, scale_inst, 0)?;
                let shift = exact_input(graph, scale_inst, 1)?;
                match resolve_constant(graph, shift, 0) {
                    Some(shift) if shift < 8 => (index, 1u64 << shift),
                    _ => continue,
                }
            }
            _ => continue,
        };
        if scale == 0 {
            continue;
        }
        return Some((base_value, canonical_value(graph, index), scale));
    }
    None
}

/// Resolve every indirect transfer whose reachable target set can be proven.
fn resolve_indirect_calls_in_graph<T: PointerTable>(
    function: &SSAFunction,
    graph: &SsaGraph,
    tables: &[T],
) -> Vec<ResolvedIndirectCall> {
    let mut resolved = Vec::new();
    for block in function.blocks() {
        for (op_index, op) in block.ops.iter().enumerate() {
            // A tail call through a table is a branch, not a call, and it
            // reaches the same set of functions either way.
            let (SSAOp::CallInd { target } | SSAOp::BranchInd { target }) = op else {
                continue;
            };
            let Some(call_inst) = graph
                .inst_id_for_op_site(block.addr, op_index)
                .and_then(|inst| graph.inst(inst))
            else {
                continue;
            };
            let Some(target_value) = exact_input(graph, call_inst, 0) else {
                continue;
            };
            if graph.value_id_for_var(target) != Some(target_value) {
                continue;
            }
            // The callee is whatever the table held, so the target has to be a
            // load rather than a computed address.
            let target_value = canonical_value(graph, target_value);
            let Some(load_inst) = graph
                .def_inst(target_value)
                .and_then(|inst| graph.inst(inst))
            else {
                continue;
            };
            let InstPayload::Op(SSAOp::Load { .. }) = &load_inst.payload else {
                continue;
            };
            let Some(address) = exact_input(graph, load_inst, 0) else {
                continue;
            };
            let Some((base, index, scale)) = table_and_index(graph, address) else {
                continue;
            };
            // The base need not be the address the table was read from: a table
            // read as one run may be indexed from an entry inside it. What it
            // must be is an entry boundary, or the index steps between entries.
            let Some(table) = tables.iter().find(|table| {
                let entry = u64::from(table.entry_size());
                entry != 0
                    && base >= table.address()
                    && (base - table.address()).is_multiple_of(entry)
                    && (base - table.address()) / entry < table.targets().len() as u64
            }) else {
                continue;
            };
            // The index steps through this table only if it steps by one entry.
            // Any other stride selects something the read never described, so
            // the entry it lands on is not a fact about this table.
            if scale != u64::from(table.entry_size()) {
                continue;
            }
            let bounds = proven_bounds(function, graph, block.addr);
            let Some(interval) = bounds.get(&index).copied() else {
                continue;
            };
            if interval.is_empty() || interval.low < 0 {
                continue;
            }
            let first = (base - table.address()) / u64::from(table.entry_size());
            let entries = i128::try_from(table.targets().len()).unwrap_or(0);
            let Some(low) = interval.low.checked_add(i128::from(first)) else {
                continue;
            };
            let Some(high) = interval.high.checked_add(i128::from(first)) else {
                continue;
            };
            // A range reaching past the last entry we read is not proven: the
            // table may continue where the read stopped.
            if high >= entries {
                continue;
            }
            let low = usize::try_from(low).unwrap_or(usize::MAX);
            let high = usize::try_from(high).unwrap_or(usize::MAX);
            let Some(selected) = table.targets().get(low..=high) else {
                continue;
            };
            if selected.is_empty() {
                continue;
            }
            resolved.push(ResolvedIndirectCall {
                block_addr: block.addr,
                op_index,
                table_address: base,
                targets: selected.to_vec(),
            });
        }
    }
    resolved
}

/// Resolve every indirect transfer against the graph retained by the artifact.
/// The function and graph therefore share one `ValueId`/`InstId` universe.
pub fn resolve_indirect_calls<T: PointerTable>(
    artifact: &SsaArtifact,
    tables: &[T],
) -> Vec<ResolvedIndirectCall> {
    resolve_indirect_calls_in_graph(artifact.function(), artifact.graph(), tables)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SSAVar;
    use crate::cfg::CFG;
    use crate::domtree::DomTree;
    use crate::function::SSABlock;

    struct Table {
        address: u64,
        entry_size: u32,
        targets: Vec<u64>,
    }

    impl PointerTable for Table {
        fn address(&self) -> u64 {
            self.address
        }
        fn entry_size(&self) -> u32 {
            self.entry_size
        }
        fn targets(&self) -> &[u64] {
            &self.targets
        }
    }

    fn resolve_test_indirect_calls<T: PointerTable>(
        blocks: &[SSABlock],
        cfg: &CFG,
        _domtree: &DomTree,
        tables: &[T],
    ) -> Vec<ResolvedIndirectCall> {
        let function = SSAFunction::from_exact_test_blocks(blocks, cfg.clone());
        let graph = SsaGraph::from_function(&function);
        resolve_indirect_calls_in_graph(&function, &graph, tables)
    }

    /// The graph for a straight guard: entry dominates both arms.
    fn graph_for(blocks: &[SSABlock], taken: u64, fallthrough: Option<u64>) -> (CFG, DomTree) {
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
        let domtree = DomTree::compute(&cfg);
        (cfg, domtree)
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
                phis: Vec::new(),
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
                phis: Vec::new(),
                size: 0x10,
                ops: vec![SSAOp::Return { target: var("ret") }],
            },
            SSABlock {
                addr: 0x20,
                phis: Vec::new(),
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
                entry_size: 8,
                targets,
            }],
        )
    }

    #[test]
    fn a_guarded_index_resolves_to_exactly_the_entries_it_can_select() {
        let (blocks, tables) = guarded_dispatch(5, 5);
        let (cfg, domtree) = graph_for(&blocks, 0x20, Some(0x10));
        let resolved = resolve_test_indirect_calls(&blocks, &cfg, &domtree, &tables);
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].table_address, 0xc000);
        assert_eq!(resolved[0].targets, tables[0].targets);
    }

    #[test]
    fn a_guard_wider_than_the_table_proves_nothing() {
        // The index may reach past the entries that were read, so the target
        // set is unknown and must stay unknown rather than be truncated.
        let (blocks, tables) = guarded_dispatch(9, 5);
        let (cfg, domtree) = graph_for(&blocks, 0x20, Some(0x10));
        assert!(resolve_test_indirect_calls(&blocks, &cfg, &domtree, &tables).is_empty());
    }

    #[test]
    fn a_stride_the_table_was_not_read_at_proves_nothing() {
        // Reading 8-byte entries and stepping by 4 lands halfway into each one,
        // so the target set the read describes is not the set the call reaches.
        let (blocks, mut tables) = guarded_dispatch(5, 5);
        tables[0].entry_size = 4;
        let (cfg, domtree) = graph_for(&blocks, 0x20, Some(0x10));
        assert!(resolve_test_indirect_calls(&blocks, &cfg, &domtree, &tables).is_empty());
    }

    /// The shape hardware actually emits, taken from an arm64 -O1 dispatch.
    ///
    /// `cmp w0, 3` lands in a flag, `b.ls` tests its negation, the table base
    /// is built by `adrp`+`add`, and the transfer is a tail-call branch. None
    /// of it is a literal operand, and all of it is exact.
    fn hardware_dispatch(entries: usize) -> (Vec<SSABlock>, Vec<Table>) {
        let index = var("w0");
        let flag = var("cy");
        let zero = var("zr");
        let negated = var("tmp:b00");
        let lower_or_same = var("tmp:1000");
        let page = var("x8_page");
        let base = var("x8");
        let widened = var("x9");
        let scaled = var("tmp:7100");
        let addr = var("tmp:7580");
        let callee = var("x3");
        let blocks = vec![
            SSABlock {
                addr: 0,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![
                    // arm64 `cmp w0, 3` then `b.ls`: the branch tests
                    // `!cy || zr`, where cy is `3 <= w0` and zr is `w0 == 3`.
                    // Together they prove `w0 <= 3` and nothing narrower.
                    SSAOp::IntLessEqual {
                        dst: flag.clone(),
                        a: SSAVar::constant(3, 4),
                        b: index.clone(),
                    },
                    SSAOp::IntEqual {
                        dst: zero.clone(),
                        a: index.clone(),
                        b: SSAVar::constant(3, 4),
                    },
                    SSAOp::BoolNot {
                        dst: negated.clone(),
                        src: flag.clone(),
                    },
                    SSAOp::BoolOr {
                        dst: lower_or_same.clone(),
                        a: negated.clone(),
                        b: zero.clone(),
                    },
                    SSAOp::CBranch {
                        target: SSAVar::new("ram:20", 0, 8),
                        cond: lower_or_same.clone(),
                    },
                ],
            },
            SSABlock {
                addr: 0x10,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![SSAOp::Return { target: var("ret") }],
            },
            SSABlock {
                addr: 0x20,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![
                    // adrp x8, 0xc000 ; add x8, x8, 0x10
                    SSAOp::Copy {
                        dst: page.clone(),
                        src: SSAVar::constant(0xc000, 8),
                    },
                    SSAOp::IntAdd {
                        dst: base.clone(),
                        a: page.clone(),
                        b: SSAVar::constant(0x10, 8),
                    },
                    SSAOp::IntZExt {
                        dst: widened.clone(),
                        src: index.clone(),
                    },
                    SSAOp::IntLeft {
                        dst: scaled.clone(),
                        a: widened.clone(),
                        b: SSAVar::constant(3, 8),
                    },
                    SSAOp::IntAdd {
                        dst: addr.clone(),
                        a: base.clone(),
                        b: scaled.clone(),
                    },
                    SSAOp::Load {
                        dst: callee.clone(),
                        space: r2il::SpaceId::Ram,
                        addr: addr.clone(),
                    },
                    SSAOp::BranchInd {
                        target: callee.clone(),
                    },
                ],
            },
        ];
        // The table was read from 0xc000, but the code indexes from 0xc010.
        let targets = (0..entries).map(|i| 0x1000 + i as u64 * 0x20).collect();
        (
            blocks,
            vec![Table {
                address: 0xc000,
                entry_size: 8,
                targets,
            }],
        )
    }

    #[test]
    fn a_flag_tested_by_its_negation_still_bounds_the_index() {
        // Two entries precede the base the code indexes from, and four follow.
        let (blocks, tables) = hardware_dispatch(6);
        let (cfg, domtree) = graph_for(&blocks, 0x20, Some(0x10));
        let resolved = resolve_test_indirect_calls(&blocks, &cfg, &domtree, &tables);
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].table_address, 0xc010);
        assert_eq!(resolved[0].targets, tables[0].targets[2..6]);
    }

    #[test]
    fn a_base_inside_a_table_still_has_to_fit_the_entries_that_were_read() {
        // Indexing from entry two of a five-entry table can select four, and
        // the read only describes three of them.
        let (blocks, tables) = hardware_dispatch(5);
        let (cfg, domtree) = graph_for(&blocks, 0x20, Some(0x10));
        assert!(resolve_test_indirect_calls(&blocks, &cfg, &domtree, &tables).is_empty());
    }

    #[test]
    fn an_unguarded_index_resolves_to_nothing() {
        let index = var("index");
        let scaled = var("scaled");
        let addr = var("addr");
        let callee = var("callee");
        let blocks = vec![SSABlock {
            addr: 0,
            phis: Vec::new(),
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
        let (cfg, domtree) = graph_for(&blocks, 0, None);
        let tables = vec![Table {
            address: 0xc000,
            entry_size: 8,
            targets: vec![0x1000, 0x1020],
        }];
        assert!(resolve_test_indirect_calls(&blocks, &cfg, &domtree, &tables).is_empty());
    }

    #[test]
    fn colliding_display_spelling_cannot_transfer_a_bound_between_values() {
        let narrow_index = SSAVar::new("index", 1, 4);
        let wide_index = SSAVar::new("index", 1, 8);
        assert_eq!(narrow_index.display_name(), wide_index.display_name());
        let condition = var("condition");
        let scaled = var("scaled");
        let address = var("address");
        let callee = var("callee");
        let blocks = vec![
            SSABlock {
                addr: 0,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![
                    SSAOp::IntLess {
                        dst: condition.clone(),
                        a: narrow_index,
                        b: SSAVar::constant(2, 4),
                    },
                    SSAOp::CBranch {
                        target: SSAVar::constant(0x20, 8),
                        cond: condition,
                    },
                ],
            },
            SSABlock {
                addr: 0x10,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![SSAOp::Return { target: var("ret") }],
            },
            SSABlock {
                addr: 0x20,
                phis: Vec::new(),
                size: 0x10,
                ops: vec![
                    SSAOp::IntMult {
                        dst: scaled.clone(),
                        a: wide_index,
                        b: SSAVar::constant(8, 8),
                    },
                    SSAOp::IntAdd {
                        dst: address.clone(),
                        a: SSAVar::constant(0xc000, 8),
                        b: scaled,
                    },
                    SSAOp::Load {
                        dst: callee.clone(),
                        space: r2il::SpaceId::Ram,
                        addr: address,
                    },
                    SSAOp::CallInd { target: callee },
                ],
            },
        ];
        let (cfg, domtree) = graph_for(&blocks, 0x20, Some(0x10));
        let tables = [Table {
            address: 0xc000,
            entry_size: 8,
            targets: vec![0x1000, 0x1020],
        }];

        assert!(resolve_test_indirect_calls(&blocks, &cfg, &domtree, &tables).is_empty());
    }
}
