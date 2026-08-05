use crate::analysis::PredicateAnalysisView;
use crate::ast::CExpr;
use r2ssa::{SSAFunction, SSAOp};
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

/// Materialize phi moves on single-successor predecessor edges.
///
/// For `phi(dst <- src@pred)`, insert `dst = src` at the end of `pred` when
/// `pred` has only one successor. This keeps semantics without CFG rewriting
/// and reduces emitted phi artifacts in structured output.
pub(crate) fn materialize_phis(func: &SSAFunction) -> SSAFunction {
    let mut normalized = func.clone();
    let liveness = EdgeLiveness::compute(func);
    let mut copies_by_pred: HashMap<u64, Vec<SSAOp>> = HashMap::new();
    let mut kept_phis_by_block: HashMap<u64, Vec<r2ssa::PhiNode>> = HashMap::new();

    for block in func.blocks() {
        let mut kept = Vec::new();

        for phi in &block.phis {
            let mut all_materialized = true;
            for (pred, src) in &phi.sources {
                if src == &phi.dst {
                    continue;
                }
                if func.successors(*pred).len() == 1
                    || can_materialize_loop_backedge_phi(
                        func, &liveness, *pred, block.addr, &phi.dst,
                    )
                {
                    copies_by_pred.entry(*pred).or_default().push(SSAOp::Copy {
                        dst: phi.dst.clone(),
                        src: src.clone(),
                    });
                } else {
                    all_materialized = false;
                }
            }
            if !all_materialized {
                kept.push(phi.clone());
            }
        }

        if kept.len() != block.phis.len() {
            kept_phis_by_block.insert(block.addr, kept);
        }
    }

    for (addr, kept) in kept_phis_by_block {
        if let Some(block) = normalized.get_block_mut(addr) {
            block.phis = kept;
        }
    }

    for (pred, copies) in copies_by_pred {
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

    normalized
}

/// Coalesce certified loop carriers across zero-iteration exits.
///
/// Prepared SSA proves the carrier identity and a dominating entry-valued
/// edge. The renderer only performs the corresponding SSA destruction: one
/// initialization before the loop decision replaces redundant copies on the
/// loop-entry edges, while latch updates remain at their original program
/// point.
pub(crate) fn materialize_certified_loop_carrier_initializers(
    func: &mut SSAFunction,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
) {
    for entity in render_facts.loop_carriers() {
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
}

struct EdgeLiveness {
    live_in: HashMap<u64, HashSet<String>>,
    phi_defs: HashMap<u64, HashSet<String>>,
    edge_phi_uses: HashMap<(u64, u64), HashSet<String>>,
}

impl EdgeLiveness {
    fn compute(func: &SSAFunction) -> Self {
        let mut defs_by_block = HashMap::<u64, HashSet<String>>::new();
        let mut uses_by_block = HashMap::<u64, HashSet<String>>::new();
        let mut phi_defs = HashMap::<u64, HashSet<String>>::new();
        let mut edge_phi_uses = HashMap::<(u64, u64), HashSet<String>>::new();

        for block in func.blocks() {
            let mut defs = HashSet::new();
            let mut uses = HashSet::new();
            let mut defined = HashSet::new();

            for phi in &block.phis {
                let dst = phi.dst.display_name();
                defs.insert(dst.clone());
                defined.insert(dst.clone());
                phi_defs.entry(block.addr).or_default().insert(dst);
                for (pred, src) in &phi.sources {
                    edge_phi_uses
                        .entry((*pred, block.addr))
                        .or_default()
                        .insert(src.display_name());
                }
            }

            for op in &block.ops {
                for src in op.sources() {
                    let src = src.display_name();
                    if !defined.contains(&src) {
                        uses.insert(src);
                    }
                }
                if let Some(dst) = op.dst() {
                    let dst = dst.display_name();
                    defs.insert(dst.clone());
                    defined.insert(dst);
                }
            }

            defs_by_block.insert(block.addr, defs);
            uses_by_block.insert(block.addr, uses);
        }

        let mut live_in = HashMap::<u64, HashSet<String>>::new();
        let mut live_out = HashMap::<u64, HashSet<String>>::new();
        for &addr in func.block_addrs() {
            live_in.insert(addr, HashSet::new());
            live_out.insert(addr, HashSet::new());
        }

        let mut changed = true;
        while changed {
            changed = false;
            for &addr in func.block_addrs().iter().rev() {
                let mut next_out = HashSet::new();
                for succ in func.successors(addr) {
                    next_out.extend(edge_live_in(
                        live_in.get(&succ),
                        phi_defs.get(&succ),
                        edge_phi_uses.get(&(addr, succ)),
                    ));
                }

                let mut next_in = uses_by_block.get(&addr).cloned().unwrap_or_default();
                let defs = defs_by_block.get(&addr).cloned().unwrap_or_default();
                next_in.extend(
                    next_out
                        .iter()
                        .filter(|name| !defs.contains(*name))
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

        Self {
            live_in,
            phi_defs,
            edge_phi_uses,
        }
    }

    fn edge_live_in(&self, pred: u64, succ: u64) -> HashSet<String> {
        edge_live_in(
            self.live_in.get(&succ),
            self.phi_defs.get(&succ),
            self.edge_phi_uses.get(&(pred, succ)),
        )
    }
}

fn edge_live_in(
    succ_live_in: Option<&HashSet<String>>,
    succ_phi_defs: Option<&HashSet<String>>,
    edge_phi_uses: Option<&HashSet<String>>,
) -> HashSet<String> {
    let mut live = HashSet::new();
    if let Some(succ_live_in) = succ_live_in {
        live.extend(
            succ_live_in
                .iter()
                .filter(|name| succ_phi_defs.is_none_or(|defs| !defs.contains(*name)))
                .cloned(),
        );
    }
    if let Some(edge_phi_uses) = edge_phi_uses {
        live.extend(edge_phi_uses.iter().cloned());
    }
    live
}

fn can_materialize_loop_backedge_phi(
    func: &SSAFunction,
    liveness: &EdgeLiveness,
    pred: u64,
    target: u64,
    dst: &r2ssa::SSAVar,
) -> bool {
    let successors = func.successors(pred);
    if successors.len() <= 1 || !successors.contains(&target) || !func.dominates(target, pred) {
        return false;
    }

    if func
        .get_block(pred)
        .and_then(|block| block.ops.last())
        .is_some_and(|op| op.sources().contains(&dst))
    {
        return false;
    }

    let dst_key = dst.display_name();
    successors
        .into_iter()
        .filter(|succ| *succ != target)
        .all(|succ| !liveness.edge_live_in(pred, succ).contains(&dst_key))
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

        let normalized = materialize_phis(&func);
        let any_phi = normalized.blocks().any(|b| !b.phis.is_empty());
        assert!(
            !any_phi,
            "phis should be removed when all edges materialize"
        );
    }

    #[test]
    fn materialize_loop_backedge_phi_when_dst_dead_on_exit_edge() {
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
                cond,
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![SSAOp::Return {
            target: SSAVar::new("RIP", 1, 8),
        }];

        let normalized = materialize_phis(&func);
        assert!(
            normalized
                .get_block(0x1004)
                .is_some_and(|block| block.phis.is_empty()),
            "loop header phi should be eliminated when all incoming copies are safe"
        );
        let latch = normalized.get_block(0x1008).expect("latch");
        assert!(
            latch.ops.iter().any(|op| matches!(
                op,
                SSAOp::Copy { dst, src } if dst == &hash_2 && src == &hash_4
            )),
            "safe critical backedge must materialize the loop-carried copy"
        );
    }

    #[test]
    fn keep_loop_backedge_phi_when_dst_live_on_exit_edge() {
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
                cond,
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

        let normalized = materialize_phis(&func);
        assert!(
            normalized
                .get_block(0x1004)
                .is_some_and(|block| !block.phis.is_empty()),
            "critical-edge phi must remain when its destination is live on the exit edge"
        );
        let latch = normalized.get_block(0x1008).expect("latch");
        assert!(
            !latch.ops.iter().any(|op| matches!(
                op,
                SSAOp::Copy { dst, src } if dst == &hash_2 && src == &hash_4
            )),
            "unsafe critical-edge copy must not be inserted before the branch"
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
        let mut normalized = materialize_phis(prepared.function());
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
