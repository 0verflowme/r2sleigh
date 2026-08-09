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
}

pub(crate) fn materialize_certified_loop_carriers_with_control(
    func: &SSAFunction,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
    control: DecompileWorkControl<'_>,
) -> Result<SSAFunction, DecompileExecutionStop> {
    materialize_phis_where_with_control(func, control, |phi| {
        prepared
            .graph()
            .value_id_for_var(&phi.dst)
            .is_some_and(|value| render_facts.loop_carrier_for_value(value).is_some())
    })
}

fn materialize_phis_where_with_control(
    func: &SSAFunction,
    control: DecompileWorkControl<'_>,
    mut eligible: impl FnMut(&r2ssa::PhiNode) -> bool,
) -> Result<SSAFunction, DecompileExecutionStop> {
    control.poll()?;
    let mut normalized = func.clone();
    let liveness = PhiEdgeLiveness::compute_with_control(func, control)?;
    let mut copies_by_pred: HashMap<u64, Vec<SSAOp>> = HashMap::new();
    let mut materialized_by_block = HashMap::<u64, HashSet<r2ssa::SSAVar>>::new();

    for block in func.blocks() {
        control.poll()?;
        let mut moves_by_pred = HashMap::<u64, Vec<PhiMove>>::new();
        let mut complete = true;
        let selected = block
            .phis
            .iter()
            .filter(|phi| eligible(phi))
            .collect::<Vec<_>>();
        if selected.is_empty() {
            continue;
        }
        for phi in &selected {
            control.poll()?;
            for (pred, src) in &phi.sources {
                control.poll()?;
                if src == &phi.dst {
                    continue;
                }
                let Some(op) =
                    materialized_phi_edge_op(func, &liveness, *pred, block.addr, &phi.dst, src)
                else {
                    complete = false;
                    break;
                };
                moves_by_pred.entry(*pred).or_default().push(PhiMove {
                    dst: phi.dst.clone(),
                    src: src.clone(),
                    op,
                });
            }
            if !complete {
                break;
            }
        }
        if !complete {
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
            materialized_by_block.insert(
                block.addr,
                selected.iter().map(|phi| phi.dst.clone()).collect(),
            );
            for (pred, moves) in scheduled {
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
    Ok(normalized)
}

#[cfg(test)]
fn materialize_all_phis(func: &SSAFunction) -> SSAFunction {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
    materialize_phis_where_with_control(func, control, |_| true)
        .expect("default decompiler work control cannot stop")
}

struct PhiMove {
    dst: r2ssa::SSAVar,
    src: r2ssa::SSAVar,
    op: SSAOp,
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
    if can_materialize_unconditional_loop_backedge(func, liveness, pred, target, dst) {
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
    pub(crate) fn compute(func: &SSAFunction) -> Self {
        let execution = SsaExecutionControl::default();
        let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
        Self::compute_with_control(func, control)
            .expect("default decompiler work control cannot stop")
    }

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

    pub(crate) fn dst_is_dead_on_other_loop_edges(
        &self,
        func: &SSAFunction,
        pred: u64,
        target: u64,
        dst: &r2ssa::SSAVar,
    ) -> bool {
        can_materialize_unconditional_loop_backedge(func, self, pred, target, dst)
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

fn can_materialize_unconditional_loop_backedge(
    func: &SSAFunction,
    liveness: &PhiEdgeLiveness,
    pred: u64,
    target: u64,
    dst: &r2ssa::SSAVar,
) -> bool {
    let successors = func.successors(pred);
    successors.len() > 1
        && successors.contains(&target)
        && func.dominates(target, pred)
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
    use r2il::{R2ILBlock, R2ILOp, Varnode};
    use r2ssa::{PhiNode, SSAFunction, SSAVar};

    #[test]
    fn normalization_is_idempotent_for_predicates() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::binary(BinaryOp::Sub, CExpr::Var("x".to_string()), CExpr::IntLit(0)),
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
        let prepared = r2ssa::SsaArtifact::raw(&[entry, preheader, loop_block, exit], None)
            .expect("zero-iteration loop fixture");
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
        let render_facts = r2types::FunctionRenderFacts::from_prepared(&prepared);
        let mut normalized =
            materialize_certified_loop_carriers(prepared.function(), &prepared, &render_facts);
        materialize_certified_loop_carrier_initializers(&mut normalized, &prepared, &render_facts);

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
