use crate::analysis::PredicateAnalysisView;
use crate::ast::CExpr;
use crate::control::{DecompileExecutionStop, DecompileWorkControl, DecompileWorkPhase};
use r2ssa::{SSAFunction, SSAOp, SsaExecutionControl};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum NormalizeMode {
    General,
    Predicate,
}

pub(crate) fn normalize_expr(
    view: &(impl PredicateAnalysisView + ?Sized),
    expr: CExpr,
    mode: NormalizeMode,
) -> CExpr {
    match mode {
        NormalizeMode::General | NormalizeMode::Predicate => view.simplify_predicate_expr(expr),
    }
}

fn is_block_terminator(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. }
    )
}

/// Lower only certified loop-carrier phis into mutable edge assignments.
///
/// Other phis remain immutable semantic expressions. Lowering every machine
/// temporary or flag phi creates artificial C effects and obscures the proof
/// boundary between SSA values and mutable loop state.
#[allow(dead_code)]
pub(crate) fn materialize_certified_loop_carriers(
    func: &SSAFunction,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
) -> SSAFunction {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
    materialize_certified_loop_carriers_with_control(func, prepared, render_facts, control)
        .expect("default decompiler work control cannot stop")
        .0
}

pub(crate) fn materialize_certified_loop_carriers_with_control(
    func: &SSAFunction,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
    control: DecompileWorkControl<'_>,
) -> Result<(SSAFunction, MaterializedEdgeCopies), DecompileExecutionStop> {
    // A merge whose destination is read has to be placed, whether or not it is
    // a certified loop carrier. Admitting carriers alone left every other merge
    // with no definition anywhere in the rendered body, and the fold cannot
    // spell a value nothing wrote: it drops the term and renders the rest, so
    // the output compiles and runs and is quietly wrong.
    //
    // `DeadPhis` already says which merges nothing observes; those stay merges
    // and cost nothing.
    let graph = prepared.graph();
    let live = prepared.live_out();
    let dead = r2ssa::deadphi::DeadPhis::find(func, graph, &live);
    materialize_phis_where_with_control(func, control, |phi| {
        let Some(value) = graph.value_id_for_var(&phi.dst) else {
            return false;
        };
        if render_facts.loop_carrier_for_value(value).is_some() {
            return true;
        }
        // A merge nothing observes costs nothing to leave alone, and a merge at
        // a plain join -- every predecessor leading only here -- the fold can
        // render as an expression, which is what keeps ordinary merges
        // immutable.
        //
        // A merge reached from a *branching* predecessor is different: its copy
        // has to sit on one edge of a two-way branch, and the fold has no way to
        // spell that. It rendered nothing at all, and the reader never saw that
        // a value went missing -- `djb2` at x86-64 -O2 dropped the `+ rdx` its
        // remainder loop starts from and returned a plausible wrong hash.
        !dead.contains(value)
            && phi
                .sources
                .iter()
                .any(|(pred, _)| func.successors(*pred).len() > 1)
    })
}

/// A copy materialisation put on a control-flow edge, by the block holding it.
///
/// Named so a later pass can ask whether a statement is one of these rather than
/// inferring it from a name table computed against a different function, which
/// is what two earlier attempts did and why both measured inert.
pub(crate) type MaterializedEdgeCopies = HashSet<(u64, r2ssa::SSAVar, r2ssa::SSAVar)>;

/// A shared empty set, for a fold that ran no materialisation.
pub(crate) fn no_materialized_edge_copies() -> &'static MaterializedEdgeCopies {
    static EMPTY: std::sync::OnceLock<MaterializedEdgeCopies> = std::sync::OnceLock::new();
    EMPTY.get_or_init(MaterializedEdgeCopies::new)
}

fn materialize_phis_where_with_control(
    func: &SSAFunction,
    control: DecompileWorkControl<'_>,
    mut eligible: impl FnMut(&r2ssa::PhiNode) -> bool,
) -> Result<(SSAFunction, MaterializedEdgeCopies), DecompileExecutionStop> {
    control.poll()?;
    let mut inserted: MaterializedEdgeCopies = HashSet::new();
    let mut normalized = func.clone();
    let liveness = PhiEdgeLiveness::compute_with_control(func, control)?;
    let mut copies_by_pred: HashMap<u64, Vec<SSAOp>> = HashMap::new();
    let mut materialized_by_block = HashMap::<u64, HashSet<r2ssa::SSAVar>>::new();

    for block in func.blocks() {
        control.poll()?;
        let mut moves_by_pred = HashMap::<u64, Vec<PhiMove>>::new();
        let mut complete = true;
        let selected = widest_per_storage(
            block
                .phis
                .iter()
                .filter(|phi| eligible(phi))
                .collect::<Vec<_>>(),
        );
        if selected.is_empty() {
            continue;
        }
        // One merge that cannot be placed used to abandon every merge in its
        // block. They are independent -- each writes its own destination -- so
        // the failure belongs to the one merge, and taking its block-mates down
        // with it left them with no definition at all.
        //
        // `djb2` at x86-64 -O2 is where this showed: a Unique-space temp merge
        // in the loop-exit block could not be placed, so the counter merge
        // beside it was dropped too, and the remainder loop's `arg0 + rdx`
        // became `arg0` -- re-reading the front of the buffer instead of the
        // bytes the unrolled loop had not reached. It compiled, ran, and
        // returned a plausible wrong hash.
        let mut materialized_dsts = Vec::new();
        for phi in &selected {
            control.poll()?;
            let mut staged = Vec::new();
            let mut placed = true;
            for (pred, src) in &phi.sources {
                control.poll()?;
                if src == &phi.dst {
                    continue;
                }
                let Some(op) =
                    materialized_phi_edge_op(func, &liveness, *pred, block.addr, &phi.dst, src)
                else {
                    if std::env::var_os("R2SLEIGH_TRACE_MAT").is_some() {
                        eprintln!(
                            "MATFAIL block={:#x} pred={pred:#x} dst={} src={}",
                            block.addr,
                            phi.dst.display_name(),
                            src.display_name()
                        );
                    }
                    placed = false;
                    break;
                };
                staged.push((
                    *pred,
                    PhiMove {
                        dst: phi.dst.clone(),
                        src: src.clone(),
                        op,
                    },
                ));
            }
            if !placed {
                continue;
            }
            for (pred, planned) in staged {
                moves_by_pred.entry(pred).or_default().push(planned);
            }
            materialized_dsts.push(phi.dst.clone());
        }
        if materialized_dsts.is_empty() {
            continue;
        }
        let mut scheduled = Vec::new();
        for (pred, moves) in moves_by_pred {
            control.poll()?;
            let Some(moves) = schedule_parallel_phi_moves_with_control(moves, control)? else {
                complete = false;
                break;
            };
            scheduled.push((pred, moves));
        }
        if complete {
            materialized_by_block.insert(block.addr, materialized_dsts.into_iter().collect());
            for (pred, moves) in scheduled {
                for planned in &moves {
                    if let r2ssa::SSAOp::Copy { dst, src } = &planned.op {
                        inserted.insert((pred, dst.clone(), src.clone()));
                    }
                }
                copies_by_pred
                    .entry(pred)
                    .or_default()
                    .extend(moves.into_iter().map(|planned| planned.op));
            }
        }
    }

    for (addr, materialized) in materialized_by_block {
        control.poll()?;
        if let Some(block) = normalized.get_block_mut(addr) {
            block.phis.retain(|phi| !materialized.contains(&phi.dst));
        }
    }

    for (pred, copies) in copies_by_pred {
        control.poll()?;
        if copies.is_empty() {
            continue;
        }
        if let Some(block) = normalized.get_block_mut(pred) {
            let insert_at = block
                .ops
                .iter()
                .rposition(is_block_terminator)
                .unwrap_or(block.ops.len());
            block.ops.splice(insert_at..insert_at, copies);
        }
    }

    control.poll()?;
    Ok((normalized, inserted))
}

#[cfg(test)]
fn materialize_all_phis(func: &SSAFunction) -> SSAFunction {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
    materialize_phis_where_with_control(func, control, |_| true)
        .expect("default decompiler work control cannot stop")
        .0
}

struct PhiMove {
    dst: r2ssa::SSAVar,
    src: r2ssa::SSAVar,
    op: SSAOp,
}

/// Keep one merge per register, not one per width the machine wrote it at.
///
/// A header that merges both `RAX` and `EAX` is merging one register twice, and
/// materialising both gives the rendering two mutable variables for one value.
/// They then share a name and the body reads `x = x` beside the update that
/// already wrote it. The widest slice contains the others, so it is the one that
/// carries the value; anything at a different offset is a different place and is
/// kept.
fn widest_per_storage<'a>(phis: Vec<&'a r2ssa::PhiNode>) -> Vec<&'a r2ssa::PhiNode> {
    use r2ssa::CanonicalStorageSpace;
    // Ordered, because what the fold emits has to be the same on every run and
    // a hash map hands its values back in whatever order it likes.
    let mut widest_by_slot: std::collections::BTreeMap<
        (CanonicalStorageSpace, u64),
        &r2ssa::PhiNode,
    > = std::collections::BTreeMap::new();
    let mut kept = Vec::with_capacity(phis.len());
    for phi in phis {
        let Some(storage) = phi.canonical_storage else {
            kept.push(phi);
            continue;
        };
        if !matches!(storage.space, CanonicalStorageSpace::Register) {
            kept.push(phi);
            continue;
        }
        match widest_by_slot.entry((storage.space, storage.offset)) {
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(phi);
            }
            std::collections::btree_map::Entry::Occupied(mut slot) => {
                let held = slot.get().canonical_storage.map_or(0, |held| held.size);
                if storage.size > held {
                    slot.insert(phi);
                }
            }
        }
    }
    kept.extend(widest_by_slot.into_values());
    kept
}

fn materialized_phi_edge_op(
    func: &SSAFunction,
    liveness: &PhiEdgeLiveness,
    pred: u64,
    target: u64,
    dst: &r2ssa::SSAVar,
    src: &r2ssa::SSAVar,
) -> Option<SSAOp> {
    let successors = func.successors(pred);
    if successors.as_slice() == [target] {
        return Some(SSAOp::Copy {
            dst: dst.clone(),
            src: src.clone(),
        });
    }
    if can_materialize_on_branch_edge(func, liveness, pred, target, dst) {
        return Some(SSAOp::Copy {
            dst: dst.clone(),
            src: src.clone(),
        });
    }
    guarded_loop_backedge_phi_op(func, pred, target, dst, src)
}

fn guarded_loop_backedge_phi_op(
    func: &SSAFunction,
    pred: u64,
    target: u64,
    dst: &r2ssa::SSAVar,
    src: &r2ssa::SSAVar,
) -> Option<SSAOp> {
    let successors = func.successors(pred);
    if successors.len() != 2 || !successors.contains(&target) || !func.dominates(target, pred) {
        return None;
    }
    let cond = match func.get_block(pred)?.ops.last()? {
        SSAOp::CBranch { cond, .. } if cond != dst => cond.clone(),
        _ => return None,
    };
    let (if_true, if_false) = match func.edge_type(pred, target)? {
        r2ssa::CFGEdge::True => (src.clone(), dst.clone()),
        r2ssa::CFGEdge::False => (dst.clone(), src.clone()),
        r2ssa::CFGEdge::Normal | r2ssa::CFGEdge::Back => return None,
    };
    Some(SSAOp::Select {
        dst: dst.clone(),
        cond,
        if_true,
        if_false,
    })
}

/// Order out-of-SSA moves without changing the simultaneous semantics of a
/// phi bundle. Cyclic bundles stay in SSA until a temporary-backed lowering
/// can represent them exactly.
fn schedule_parallel_phi_moves_with_control(
    mut moves: Vec<PhiMove>,
    control: DecompileWorkControl<'_>,
) -> Result<Option<Vec<PhiMove>>, DecompileExecutionStop> {
    let mut scheduled = Vec::with_capacity(moves.len());
    while !moves.is_empty() {
        control.poll()?;
        let ready = moves.iter().position(|candidate| {
            !moves
                .iter()
                .any(|other| other.dst != candidate.dst && other.src == candidate.dst)
        });
        let Some(ready) = ready else {
            return Ok(None);
        };
        scheduled.push(moves.remove(ready));
    }
    Ok(Some(scheduled))
}

pub(crate) struct PhiEdgeLiveness {
    live_in: HashMap<u64, HashSet<r2ssa::SSAVar>>,
    phi_defs: HashMap<u64, HashSet<r2ssa::SSAVar>>,
    edge_phi_uses: HashMap<(u64, u64), HashSet<r2ssa::SSAVar>>,
}

impl PhiEdgeLiveness {
    pub(crate) fn compute_with_control(
        func: &SSAFunction,
        control: DecompileWorkControl<'_>,
    ) -> Result<Self, DecompileExecutionStop> {
        control.poll()?;
        let mut defs_by_block = HashMap::<u64, HashSet<r2ssa::SSAVar>>::new();
        let mut uses_by_block = HashMap::<u64, HashSet<r2ssa::SSAVar>>::new();
        let mut phi_defs = HashMap::<u64, HashSet<r2ssa::SSAVar>>::new();
        let mut edge_phi_uses = HashMap::<(u64, u64), HashSet<r2ssa::SSAVar>>::new();

        for block in func.blocks() {
            control.poll()?;
            let mut defs = HashSet::new();
            let mut uses = HashSet::new();
            let mut defined = HashSet::new();
            for phi in &block.phis {
                control.poll()?;
                defs.insert(phi.dst.clone());
                defined.insert(phi.dst.clone());
                phi_defs
                    .entry(block.addr)
                    .or_default()
                    .insert(phi.dst.clone());
                for (pred, src) in &phi.sources {
                    edge_phi_uses
                        .entry((*pred, block.addr))
                        .or_default()
                        .insert(src.clone());
                }
            }
            for op in &block.ops {
                control.poll()?;
                for src in op.sources() {
                    if !defined.contains(src) {
                        uses.insert(src.clone());
                    }
                }
                if let Some(dst) = op.dst() {
                    defs.insert(dst.clone());
                    defined.insert(dst.clone());
                }
            }
            defs_by_block.insert(block.addr, defs);
            uses_by_block.insert(block.addr, uses);
        }

        let mut live_in = func
            .block_addrs()
            .iter()
            .copied()
            .map(|addr| (addr, HashSet::new()))
            .collect::<HashMap<_, _>>();
        let mut live_out = live_in.clone();
        let mut changed = true;
        while changed {
            control.poll()?;
            changed = false;
            for &addr in func.block_addrs().iter().rev() {
                control.poll()?;
                let mut next_out = HashSet::new();
                for successor in func.successors(addr) {
                    control.poll()?;
                    next_out.extend(edge_live_in(
                        live_in.get(&successor),
                        phi_defs.get(&successor),
                        edge_phi_uses.get(&(addr, successor)),
                    ));
                }
                let mut next_in = uses_by_block.get(&addr).cloned().unwrap_or_default();
                let defs = defs_by_block.get(&addr).cloned().unwrap_or_default();
                next_in.extend(
                    next_out
                        .iter()
                        .filter(|value| !defs.contains(*value))
                        .cloned(),
                );
                if live_out.get(&addr) != Some(&next_out) {
                    live_out.insert(addr, next_out);
                    changed = true;
                }
                if live_in.get(&addr) != Some(&next_in) {
                    live_in.insert(addr, next_in);
                    changed = true;
                }
            }
        }
        control.poll()?;
        Ok(Self {
            live_in,
            phi_defs,
            edge_phi_uses,
        })
    }

    fn live_on_edge(&self, pred: u64, successor: u64) -> HashSet<r2ssa::SSAVar> {
        edge_live_in(
            self.live_in.get(&successor),
            self.phi_defs.get(&successor),
            self.edge_phi_uses.get(&(pred, successor)),
        )
    }
}

fn edge_live_in(
    successor_live_in: Option<&HashSet<r2ssa::SSAVar>>,
    successor_phi_defs: Option<&HashSet<r2ssa::SSAVar>>,
    edge_phi_uses: Option<&HashSet<r2ssa::SSAVar>>,
) -> HashSet<r2ssa::SSAVar> {
    let mut live = HashSet::new();
    if let Some(successor_live_in) = successor_live_in {
        live.extend(
            successor_live_in
                .iter()
                .filter(|value| successor_phi_defs.is_none_or(|defs| !defs.contains(*value)))
                .cloned(),
        );
    }
    if let Some(edge_phi_uses) = edge_phi_uses {
        live.extend(edge_phi_uses.iter().cloned());
    }
    live
}

/// Whether a merge's copy can sit at the end of a two-way predecessor.
///
/// The copy runs on every edge out of the block, not only the one the merge
/// came in on, so it is sound exactly when nothing on the other edges can tell:
/// the terminator must not read the destination, and the destination must not
/// be live along any other successor.
///
/// This once also required the target to dominate the predecessor, which
/// confined it to loop backedges. Soundness never depended on that, and the
/// restriction refused every merge on a loop *exit* edge -- leaving those
/// destinations with no definition at all, which is how `djb2` at x86-64 -O2
/// lost the counter its remainder loop starts from.
fn can_materialize_on_branch_edge(
    func: &SSAFunction,
    liveness: &PhiEdgeLiveness,
    pred: u64,
    target: u64,
    dst: &r2ssa::SSAVar,
) -> bool {
    let successors = func.successors(pred);
    successors.len() > 1
        && successors.contains(&target)
        && !func
            .get_block(pred)
            .and_then(|block| block.ops.last())
            .is_some_and(|op| op.sources().contains(&dst))
        && successors
            .into_iter()
            .filter(|successor| *successor != target)
            .all(|successor| !liveness.live_on_edge(pred, successor).contains(dst))
}

/// Coalesce certified loop carriers across zero-iteration exits.
///
/// Prepared SSA proves the carrier identity and a dominating entry-valued
/// edge. The renderer only performs the corresponding SSA destruction: one
/// initialization before the loop decision replaces redundant copies on the
/// loop-entry edges, while latch updates remain at their original program
/// point.
#[allow(dead_code)]
pub(crate) fn materialize_certified_loop_carrier_initializers(
    func: &mut SSAFunction,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
) {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
    materialize_certified_loop_carrier_initializers_with_control(
        func,
        prepared,
        render_facts,
        control,
    )
    .expect("default decompiler work control cannot stop");
}

pub(crate) fn materialize_certified_loop_carrier_initializers_with_control(
    func: &mut SSAFunction,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
    control: DecompileWorkControl<'_>,
) -> Result<(), DecompileExecutionStop> {
    control.poll()?;
    for entity in render_facts.loop_carriers() {
        control.poll()?;
        let r2types::CertifiedEntity::LoopCarrier {
            phi,
            identity_values,
            entries,
            dominating_initializers,
            ..
        } = entity
        else {
            continue;
        };
        if identity_values.len() < 2 {
            continue;
        }
        let [initializer] = dominating_initializers.as_slice() else {
            continue;
        };
        if !entries.iter().any(|entry| entry.value == initializer.value) {
            continue;
        }
        let Some(dst) = prepared.value_var(*phi).cloned() else {
            continue;
        };
        let Some(src) = prepared.value_var(initializer.value).cloned() else {
            continue;
        };
        if dst.size != src.size {
            continue;
        }

        for entry in entries {
            control.poll()?;
            if entry.value != initializer.value
                || entry.predecessor == initializer.predecessor
                || !prepared
                    .function()
                    .dominates(initializer.predecessor, entry.predecessor)
            {
                continue;
            }
            if let Some(block) = func.get_block_mut(entry.predecessor) {
                block.ops.retain(|op| {
                    !matches!(op, SSAOp::Copy { dst: copy_dst, src: copy_src }
                        if copy_dst == &dst && copy_src == &src)
                });
            }
        }

        let Some(block) = func.get_block_mut(initializer.predecessor) else {
            continue;
        };
        if block.ops.iter().any(|op| {
            matches!(op, SSAOp::Copy { dst: copy_dst, src: copy_src }
                if copy_dst == &dst && copy_src == &src)
        }) {
            continue;
        }
        let insert_at = block
            .ops
            .iter()
            .rposition(is_block_terminator)
            .unwrap_or(block.ops.len());
        block.ops.insert(insert_at, SSAOp::Copy { dst, src });
    }
    control.poll()?;
    Ok(())
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::ast::{BinaryOp, UnaryOp};
    use crate::fold::FoldingContext;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::{PhiNode, SSAFunction, SSAVar};

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    #[test]
    fn normalization_is_idempotent_for_predicates() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::binary(BinaryOp::Sub, ctx.name_ref("x"), CExpr::IntLit(0)),
                CExpr::IntLit(0),
            ),
        );

        let once = normalize_expr(&ctx, expr.clone(), NormalizeMode::Predicate);
        let twice = normalize_expr(&ctx, once.clone(), NormalizeMode::Predicate);
        assert_eq!(once, twice, "Predicate normalization must be idempotent");
    }

    #[test]
    fn materialize_phis_on_single_successor_pred() {
        // 0x1000: cbranch to 0x1008 else 0x1004
        // 0x1004: define reg0 = 1, branch 0x100c
        // 0x1008: define reg0 = 2, branch 0x100c
        // 0x100c: return reg0 (forces phi at join)
        let mut b0 = R2ILBlock::new(0x1000, 4);
        b0.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1008, 8),
        });

        let mut b1 = R2ILBlock::new(0x1004, 4);
        b1.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(1, 8),
        });
        b1.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });

        let mut b2 = R2ILBlock::new(0x1008, 4);
        b2.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(2, 8),
        });
        b2.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });

        let mut b3 = R2ILBlock::new(0x100c, 4);
        b3.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let func = SSAFunction::from_blocks_raw_no_arch(&[b0, b1, b2, b3]).expect("ssa function");
        let with_phis = func.blocks().any(|b| !b.phis.is_empty());
        assert!(with_phis, "fixture should include phi nodes");

        let normalized = materialize_all_phis(&func);
        let any_phi = normalized.blocks().any(|b| !b.phis.is_empty());
        assert!(
            !any_phi,
            "phis should be removed when all edges materialize"
        );
    }

    #[test]
    fn lower_loop_backedge_unconditionally_when_dst_is_dead_on_exit_edge() {
        let hash_1 = SSAVar::new("RAX", 1, 8);
        let hash_2 = SSAVar::new("RAX", 2, 8);
        let hash_4 = SSAVar::new("RAX", 4, 8);
        let cond = SSAVar::new("tmp:cond", 1, 1);

        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: hash_1.clone(),
                src: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::Branch {
                target: SSAVar::new("ram:1004", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("header").phis = vec![PhiNode {
            dst: hash_2.clone(),
            sources: vec![(0x1000, hash_1), (0x1008, hash_4.clone())],
            canonical_storage: None,
        }];
        func.get_block_mut(0x1004).expect("header").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("latch").ops = vec![
            SSAOp::IntAdd {
                dst: hash_4.clone(),
                a: hash_2.clone(),
                b: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: cond.clone(),
                a: SSAVar::new("RSI", 0, 8),
                b: SSAVar::new("const:0", 0, 8),
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1004", 0, 8),
                cond: cond.clone(),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![SSAOp::Return {
            target: SSAVar::new("RIP", 1, 8),
        }];

        let normalized = materialize_all_phis(&func);
        assert!(
            normalized
                .get_block(0x1004)
                .is_some_and(|block| block.phis.is_empty()),
            "loop header phi should be eliminated when all edge moves are exact"
        );
        let latch = normalized.get_block(0x1008).expect("latch");
        assert!(
            latch.ops.iter().any(|op| matches!(
                op,
                SSAOp::Copy { dst, src } if dst == &hash_2 && src == &hash_4
            )),
            "a value dead on every exit edge may be updated before the branch"
        );
    }

    #[test]
    fn guard_loop_backedge_phi_when_dst_live_on_exit_edge() {
        let hash_1 = SSAVar::new("RAX", 1, 8);
        let hash_2 = SSAVar::new("RAX", 2, 8);
        let hash_4 = SSAVar::new("RAX", 4, 8);
        let cond = SSAVar::new("tmp:cond", 1, 1);

        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: hash_1.clone(),
                src: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::Branch {
                target: SSAVar::new("ram:1004", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("header").phis = vec![PhiNode {
            dst: hash_2.clone(),
            sources: vec![(0x1000, hash_1), (0x1008, hash_4.clone())],
            canonical_storage: None,
        }];
        func.get_block_mut(0x1004).expect("header").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("latch").ops = vec![
            SSAOp::IntAdd {
                dst: hash_4.clone(),
                a: hash_2.clone(),
                b: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: cond.clone(),
                a: SSAVar::new("RSI", 0, 8),
                b: SSAVar::new("const:0", 0, 8),
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1004", 0, 8),
                cond: cond.clone(),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("RBX", 1, 8),
                src: hash_2.clone(),
            },
            SSAOp::Return {
                target: SSAVar::new("RIP", 1, 8),
            },
        ];

        let normalized = materialize_all_phis(&func);
        assert!(
            normalized
                .get_block(0x1004)
                .is_some_and(|block| block.phis.is_empty()),
            "an exact guarded backedge move should eliminate the loop-header phi"
        );
        let latch = normalized.get_block(0x1008).expect("latch");
        assert!(
            latch.ops.iter().any(|op| matches!(
                op,
                SSAOp::Select {
                    dst,
                    cond: select_cond,
                    if_true,
                    if_false,
                } if dst == &hash_2
                    && select_cond == &cond
                    && if_true == &hash_4
                    && if_false == &hash_2
            )),
            "the backedge update must execute only when its branch edge is taken"
        );
    }

    #[test]
    fn keep_loop_phi_when_edge_guard_reads_its_destination() {
        let value_1 = SSAVar::new("RAX", 1, 8);
        let value_2 = SSAVar::new("RAX", 2, 8);
        let value_4 = SSAVar::new("RAX", 4, 8);
        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1004", 0, 8),
        }];
        func.get_block_mut(0x1004).expect("header").phis = vec![PhiNode {
            dst: value_2.clone(),
            sources: vec![(0x1000, value_1), (0x1008, value_4.clone())],
            canonical_storage: None,
        }];
        func.get_block_mut(0x1004).expect("header").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("latch").ops = vec![
            SSAOp::IntAdd {
                dst: value_4,
                a: value_2.clone(),
                b: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1004", 0, 8),
                cond: value_2.clone(),
            },
        ];

        let normalized = materialize_all_phis(&func);

        assert_eq!(
            normalized.get_block(0x1004).expect("header").phis.len(),
            1,
            "lowering before the branch would overwrite its condition"
        );
        assert!(
            !normalized
                .get_block(0x1000)
                .expect("entry")
                .ops
                .iter()
                .any(|op| matches!(op, SSAOp::Copy { dst, .. } if dst == &value_2)),
            "a rejected phi bundle must not leak its entry-edge copy"
        );
    }

    #[test]
    fn keep_parallel_phi_bundle_when_moves_are_cyclic() {
        let a = SSAVar::new("RAX", 2, 8);
        let b = SSAVar::new("RBX", 2, 8);
        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1004).expect("header").phis = vec![
            PhiNode {
                dst: a.clone(),
                sources: vec![(0x1000, SSAVar::new("RAX", 1, 8)), (0x1008, b.clone())],
                canonical_storage: None,
            },
            PhiNode {
                dst: b.clone(),
                sources: vec![(0x1000, SSAVar::new("RBX", 1, 8)), (0x1008, a.clone())],
                canonical_storage: None,
            },
        ];

        let normalized = materialize_all_phis(&func);

        assert_eq!(
            normalized.get_block(0x1004).expect("header").phis.len(),
            2,
            "cyclic parallel moves must remain as phis until temporaries are certified"
        );
        assert!(
            !normalized
                .get_block(0x1000)
                .expect("entry")
                .ops
                .iter()
                .any(|op| matches!(op, SSAOp::Copy { dst, .. } if dst == &a || dst == &b)),
            "an incomplete phi bundle must not leak partial edge copies"
        );
    }

    #[test]
    fn certified_carrier_initializer_moves_before_zero_iteration_branch() {
        let mut entry = R2ILBlock::new(0x2000, 4);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x200c, 8),
        });
        let mut preheader = R2ILBlock::new(0x2004, 4);
        preheader.push(R2ILOp::Branch {
            target: Varnode::constant(0x2008, 8),
        });
        let mut loop_block = R2ILBlock::new(0x2008, 4);
        loop_block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(1, 8),
        });
        loop_block.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x2008, 8),
        });
        let mut exit = R2ILBlock::new(0x200c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("RSP", 8, 8));
        arch.add_register(RegisterDef::new("RIP", 16, 8));
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2dec-normalize-loop-owner".to_vec(),
            "sysv64",
            std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(8)))
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .expect("exact zero-iteration loop interface");
        let prepared = std::sync::Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(
                &[entry, preheader, loop_block, exit],
                Some(&arch),
                interface,
            )
            .expect("zero-iteration loop fixture"),
        );
        let carrier = prepared
            .structured()
            .loops
            .values()
            .flat_map(|loop_fact| loop_fact.carriers.iter())
            .find(|carrier| !carrier.dominating_initializers.is_empty())
            .expect("certified loop carrier");
        let phi = prepared
            .value_var(carrier.phi)
            .expect("carrier phi")
            .clone();
        let init = prepared
            .value_var(carrier.dominating_initializers[0].value)
            .expect("carrier initializer")
            .clone();
        let analysis = r2types::build_source_owned_type_writeback_analysis(
            r2types::TypeWritebackAnalysisRequest::new(
                std::sync::Arc::clone(&prepared),
                r2types::ParsedExternalContext::default(),
            )
            .expect("matching source assumptions"),
        )
        .expect("source-owned loop analysis");
        let render_facts = analysis.function_facts().render_facts();
        let mut normalized = materialize_certified_loop_carriers(
            prepared.function(),
            prepared.as_ref(),
            render_facts,
        );
        materialize_certified_loop_carrier_initializers(
            &mut normalized,
            prepared.as_ref(),
            render_facts,
        );

        let entry = normalized.get_block(0x2000).expect("entry");
        assert!(entry.ops.iter().any(|op| matches!(
            op,
            SSAOp::Copy { dst, src } if dst == &phi && src == &init
        )));
        let preheader = normalized.get_block(0x2004).expect("preheader");
        assert!(!preheader.ops.iter().any(|op| matches!(
            op,
            SSAOp::Copy { dst, src } if dst == &phi && src == &init
        )));
    }

    fn loop_backedge_phi_fixture() -> SSAFunction {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::constant(0x1004, 8),
        });

        let mut header = R2ILBlock::new(0x1004, 4);
        header.push(R2ILOp::Branch {
            target: Varnode::constant(0x1008, 8),
        });

        let mut latch = R2ILBlock::new(0x1008, 4);
        latch.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1004, 8),
        });

        let mut exit = R2ILBlock::new(0x100c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        SSAFunction::from_blocks_raw_no_arch(&[entry, header, latch, exit]).expect("loop fixture")
    }
}

/// One name for every value a certified loop carrier passes through.
///
/// A carrier is one mutable variable the machine spells differently on each
/// edge: an entry value, a phi, a latch update and a post-loop merge are four
/// SSA values and one C local. Naming is per-version, so the same variable
/// reached the page as `rax_1`, `rax_2` and `rax_3`, with the loop assigning two
/// of them and the return reading a fourth that still held the entry value.
///
/// Two kinds of carrier are left alone, and both were found by rendering rather
/// than reasoning. One the loop reloads from a frame slot is a copy of that
/// slot, so naming it puts a second variable on the page for one value. One
/// whose values are not all the same storage holding one value is a register the
/// machine reused, and naming it would say two different values are one.
///
/// Constants are skipped. An entry edge arriving as a literal is the
/// initializer, not another spelling of the variable.
/// A carrier read at a width other than the one it is carried at.
///
/// `eax` and `rax` are one place at two widths, and a loop that carries the
/// place at one of them is still the source of a read at the other. The name is
/// the carrier's; the width is the width of *this* view of it, which is what
/// makes the difference between the two expressible at all -- an alias maps a
/// name to a name and cannot say "the low four bytes of".
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CarrierMemberView {
    /// The carrier this value is a view of.
    pub(crate) carrier: String,
    /// Width of this view, in bytes.
    pub(crate) width: u32,
    /// Width the carrier itself is held at, in bytes.
    pub(crate) carrier_width: u32,
}

/// Values that are one of a carrier's other widths.
///
/// A loop header carries a place once, but Sleigh gives each width its own phi:
/// adler32 at x86-64 -O1 has `RAX_2` certified as the carrier and `EAX_2`
/// beside it in the same block, over `{ Register, offset 0 }` at four bytes
/// instead of eight. Without the pairing the narrow phi belongs to no carrier,
/// so the tail that reads it after the loop is dropped and the return is left
/// quoting a name nothing defines.
///
/// Only a phi in the carrier's own header block counts. Every value at the place
/// is *not* the carrier -- that is the whole-function renaming that was measured
/// at 34 correct down to 13 -- and a phi in the header is the narrow point where
/// the two widths are provably the same run of the same storage.
pub(crate) fn carrier_member_views(
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
    aliases: &HashMap<String, String>,
) -> HashMap<String, CarrierMemberView> {
    use r2types::CertifiedEntity;

    // The pairing is only sound where the machine guarantees it: after a narrow
    // write the wide value is the narrow one zero-extended, so one answers for
    // the other. Where it does not hold, the upper bytes are whatever they were.
    if !prepared.narrow_write_clears_register() {
        return HashMap::new();
    }

    let graph = prepared.graph();
    let mut views = HashMap::new();
    for carrier in render_facts.loop_carriers() {
        let CertifiedEntity::LoopCarrier { phi, .. } = carrier else {
            continue;
        };
        let Some(carrier_var) = graph.value(*phi).map(|value| value.var.clone()) else {
            continue;
        };
        let Some(name) = aliases.get(&carrier_var.display_name()).cloned() else {
            continue;
        };
        let Some(storage) = graph.canonical_storage_for_var(&carrier_var) else {
            continue;
        };
        for block in prepared.function().blocks() {
            if !block.phis.iter().any(|phi| phi.dst == carrier_var) {
                continue;
            }
            for peer in &block.phis {
                if peer.dst == carrier_var || peer.dst.size == carrier_var.size {
                    continue;
                }
                // A peer that is a carrier in its own right keeps its own name.
                if aliases.contains_key(&peer.dst.display_name()) {
                    continue;
                }
                let Some(peer_storage) = graph.canonical_storage_for_var(&peer.dst) else {
                    continue;
                };
                if peer_storage.space != storage.space || peer_storage.offset != storage.offset {
                    continue;
                }
                views.insert(
                    peer.dst.display_name(),
                    CarrierMemberView {
                        carrier: name.clone(),
                        width: peer.dst.size,
                        carrier_width: carrier_var.size,
                    },
                );
            }
        }
    }
    views
}

pub(crate) fn carrier_name_aliases(
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
) -> HashMap<String, String> {
    use r2types::CertifiedEntity;

    let graph = prepared.graph();
    let mirrored = prepared.memory_mirrored_carriers();
    let reused = prepared.carriers_spanning_a_reuse();
    let mut aliases = HashMap::new();
    let mut taken = HashSet::new();
    let spans = prepared.storage_spans();
    let mut names_by_span: HashMap<r2ssa::span::SpanId, String> = HashMap::new();
    for carrier in render_facts.loop_carriers() {
        let CertifiedEntity::LoopCarrier {
            id,
            header,
            phi,
            identity_values,
            entries,
            updates,
            ..
        } = carrier
        else {
            continue;
        };
        if mirrored.contains(id) || reused.contains(id) {
            continue;
        }
        let Some(base) = graph
            .value(*phi)
            .map(|value| crate::analysis::utils::ssa_render_base_name(&value.var))
        else {
            continue;
        };
        // Two loops carrying the same register are two variables *unless the
        // register holds one value across both*, which is what a storage span
        // says. A four-way unrolled loop followed by a remainder loop carries one
        // accumulator through both, and naming them apart left the remainder
        // starting from nothing: `fnv1a32` at x86-64 -O2 ran its tail over
        // `rax_1000005f0`, which no statement ever gave the value `rax` reached.
        //
        // `StorageSpans` computes where a storage stops holding one value, so it
        // answers this directly and the header suffix is kept for the case it was
        // written for: two carriers over one register in genuinely separate runs.
        let span = spans.span_of(*phi);
        let name = match span.and_then(|span| names_by_span.get(&span).cloned()) {
            Some(existing) => existing,
            None => {
                let name = if taken.insert(base.clone()) {
                    base
                } else {
                    format!("{base}_{header:x}")
                };
                if let Some(span) = span {
                    names_by_span.insert(span, name.clone());
                }
                name
            }
        };
        let members = identity_values
            .iter()
            .copied()
            .chain(entries.iter().map(|edge| edge.value))
            .chain(updates.iter().flat_map(|update| {
                std::iter::once(update.value).chain(update.identity_values.iter().copied())
            }));
        let update_values: HashSet<_> = updates.iter().map(|update| update.value).collect();
        for member in members {
            let Some(var) = graph.value(member).map(|value| &value.var) else {
                continue;
            };
            if var.is_const() {
                continue;
            }
            aliases.insert(var.display_name(), name.clone());
        }
        for merge in exit_merges_for_carrier(prepared, *phi, &update_values) {
            aliases.insert(merge, name.clone());
        }
    }
    aliases
}

/// Merges that join a carrier's entry value with its update value.
///
/// A loop with a bypass has a second merge after it, joining "the loop never
/// ran", which carries the entry value, with "the loop ran", which carries the
/// update. That merge is the carrier: materialising places the carrier's
/// initialiser where it dominates both edges, so the variable already holds the
/// right value whichever way control arrived.
///
/// The carrier is a third name rather than either source, so this cannot be
/// found by looking at the merge's sources; the certified entries and updates
/// are what identify it.
fn exit_merges_for_carrier(
    prepared: &r2ssa::SsaArtifact,
    phi: r2ssa::ValueId,
    update_values: &HashSet<r2ssa::ValueId>,
) -> Vec<String> {
    let graph = prepared.graph();
    let Some(carrier) = graph.value(phi).map(|value| value.var.clone()) else {
        return Vec::new();
    };
    let mut merges = Vec::new();
    for block in prepared.function().blocks() {
        for merge in &block.phis {
            if merge.dst == carrier || merge.dst.size != carrier.size {
                continue;
            }
            let Some(values) = merge
                .sources
                .iter()
                .map(|(_, src)| graph.value_id_for_var(src))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            // Every edge must carry a value this carrier holds, and both sides
            // must be present: a merge of two entry values is a different merge
            // that happens to be over the same storage.
            // The bypass edge carries "the loop never ran", and that is not
            // always the header phi's own entry value: in pearson the merge is
            // `phi(RCX_4 = update, RCX_5)` where `RCX_5` is the value the
            // carrier was initialised with before the loop, a different
            // `ValueId` from the certified entry. Requiring a certified entry
            // there left the exit merge unaliased and pearson returned `rcx_6`,
            // a name nothing declares. The carrier's own dominating
            // initialisers are the same variable by construction, so they
            // count.
            // A phi over this storage that takes one of the carrier's updates
            // on one edge is the carrier leaving the loop, whatever the other
            // edge carries: the bypass value is "the loop never ran", and it is
            // not required to be a value the carrier certified. Requiring that
            // left pearson's exit merge unaliased and its return printed
            // `rcx_6`, a name nothing declares.
            if values.iter().any(|value| update_values.contains(value))
                && values.iter().any(|value| !update_values.contains(value))
            {
                merges.push(merge.dst.display_name());
            }
        }
    }
    merges
}
