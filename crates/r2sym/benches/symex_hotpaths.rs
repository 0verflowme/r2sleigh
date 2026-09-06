use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};
use r2ssa::SsaArtifact;
use r2sym::path::ExploreStrategy;
use r2sym::{ExploreConfig, PathExplorer, SymSolver, SymState, SymValue};
use z3::Context;
use z3::ast::BV;

const RAX: u64 = 0;
const RCX: u64 = 16;
const RDI: u64 = 56;

fn leaked_ctx() -> &'static Context {
    // Criterion re-runs `iter_batched` setup once per batch element, so leaking
    // here per call leaked a whole z3 context per measured iteration and grew
    // the process across a run. `Context::thread_local()` is thread-affine, so
    // the leak is kept but made once per thread.
    thread_local! {
        static CTX: &'static Context = Box::leak(Box::new(Context::thread_local()));
    }
    CTX.with(|ctx| *ctx)
}

fn make_reg(offset: u64, size: u32) -> Varnode {
    Varnode {
        space: SpaceId::Register,
        offset,
        size,
        meta: None,
    }
}

fn make_const(val: u64, size: u32) -> Varnode {
    Varnode {
        space: SpaceId::Const,
        offset: val,
        size,
        meta: None,
    }
}

fn build_branching_function() -> SsaArtifact {
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1),
                    a: make_reg(RDI, 8),
                    b: make_const(0x1337, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(RCX, 1),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x1010,
            size: 4,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
    ];

    SsaArtifact::for_symbolic(&blocks, None).expect("branching benchmark SSA should build")
}

fn build_join_heavy_function(levels: u64) -> SsaArtifact {
    let mut blocks = Vec::new();
    let mut addr = 0x2000;

    for level in 0..levels {
        let branch_addr = addr;
        let false_addr = addr + 0x4;
        let true_addr = addr + 0x8;
        let join_addr = addr + 0xc;

        blocks.push(R2ILBlock {
            addr: branch_addr,
            size: 4,
            ops: vec![
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1),
                    a: make_reg(RDI, 8),
                    b: make_const(level, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(true_addr, 8),
                    cond: make_reg(RCX, 1),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        });
        blocks.push(R2ILBlock {
            addr: false_addr,
            size: 4,
            ops: vec![R2ILOp::Branch {
                target: make_const(join_addr, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        });
        blocks.push(R2ILBlock {
            addr: true_addr,
            size: 4,
            ops: vec![R2ILOp::Branch {
                target: make_const(join_addr, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        });
        blocks.push(R2ILBlock {
            addr: join_addr,
            size: 4,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_reg(RAX, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        });

        addr += 0x10;
    }

    blocks.push(R2ILBlock {
        addr,
        size: 4,
        ops: vec![R2ILOp::Copy {
            dst: make_reg(RAX, 8),
            src: make_const(0x1337, 8),
        }],
        switch_info: None,
        op_metadata: Default::default(),
    });

    blocks.sort_by_key(|block| block.addr);
    SsaArtifact::for_symbolic(&blocks, None).expect("join-heavy benchmark SSA should build")
}

fn emit_branch_tree(
    blocks: &mut Vec<R2ILBlock>,
    next_addr: &mut u64,
    depth: u32,
    seed: &mut u64,
) -> u64 {
    let entry = *next_addr;
    *next_addr += 4;

    if depth == 0 {
        let leaf_value = *seed;
        *seed += 1;
        blocks.push(R2ILBlock {
            addr: entry,
            size: 4,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(leaf_value, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        });
        return entry;
    }

    let false_entry = emit_branch_tree(blocks, next_addr, depth - 1, seed);
    let true_entry = emit_branch_tree(blocks, next_addr, depth - 1, seed);
    let compare_value = *seed;
    *seed += 1;

    debug_assert_eq!(false_entry, entry + 4);

    blocks.push(R2ILBlock {
        addr: entry,
        size: 4,
        ops: vec![
            R2ILOp::IntEqual {
                dst: make_reg(RCX, 1),
                a: make_reg(RDI, 8),
                b: make_const(compare_value, 8),
            },
            R2ILOp::CBranch {
                target: make_const(true_entry, 8),
                cond: make_reg(RCX, 1),
            },
        ],
        switch_info: None,
        op_metadata: Default::default(),
    });

    entry
}

fn build_branch_tree_function(levels: u32) -> SsaArtifact {
    let mut blocks = Vec::new();
    let mut next_addr = 0x3000;
    let mut seed = 0;

    emit_branch_tree(&mut blocks, &mut next_addr, levels, &mut seed);
    blocks.sort_by_key(|block| block.addr);
    SsaArtifact::for_symbolic(&blocks, None).expect("branch-tree benchmark SSA should build")
}

fn bench_solver_sat_cache(c: &mut Criterion) {
    c.bench_function("r2sym/solver_is_sat_cached_cold", |b| {
        b.iter(|| {
            let ctx = Context::thread_local();
            let solver = SymSolver::new(&ctx);
            let mut state = SymState::new(&ctx, 0x1000);
            state.make_symbolic("x", 32);
            let x = state.get_register("x");
            state.add_true_constraint(&x.ult(&ctx, &SymValue::concrete(5, 32)));

            black_box(solver.is_sat(&state));
            black_box(solver.is_sat(&state));
            black_box(solver.stats())
        });
    });

    c.bench_function("r2sym/solver_is_sat_cached_hot", |b| {
        b.iter_batched(
            || {
                let ctx = leaked_ctx();
                let solver = SymSolver::new(ctx);
                let mut state = SymState::new(ctx, 0x1000);
                state.make_symbolic("x", 32);
                let x = state.get_register("x");
                state.add_true_constraint(&x.ult(ctx, &SymValue::concrete(5, 32)));
                black_box(solver.is_sat(&state));
                (solver, state)
            },
            |(solver, state)| {
                black_box(solver.is_sat(&state));
                black_box(solver.stats())
            },
            BatchSize::SmallInput,
        );
    });
}

fn bench_solver_prefix_reuse(c: &mut Criterion) {
    c.bench_function("r2sym/solver_prefix_reuse_cold", |b| {
        b.iter(|| {
            let ctx = Context::thread_local();
            let solver = SymSolver::new(&ctx);

            let mut root = SymState::new(&ctx, 0x1000);
            root.make_symbolic("x", 32);
            root.make_symbolic("y", 32);

            let x = root.get_register("x");
            let y = root.get_register("y");

            let mut left = root.fork();
            left.add_true_constraint(&x.ult(&ctx, &SymValue::concrete(20, 32)));

            let mut left_deep = left.fork();
            left_deep.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(7, 32)));

            let mut right = root.fork();
            right.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(99, 32)));

            black_box(solver.is_sat(&left_deep));
            black_box(solver.is_sat(&left));
            black_box(solver.is_sat(&right));
            black_box(solver.stats())
        });
    });

    c.bench_function("r2sym/solver_prefix_reuse_hot", |b| {
        b.iter_batched(
            || {
                let ctx = leaked_ctx();
                let solver = SymSolver::new(ctx);

                let mut root = SymState::new(ctx, 0x1000);
                root.make_symbolic("x", 32);
                root.make_symbolic("y", 32);

                let x = root.get_register("x");
                let y = root.get_register("y");

                let mut left = root.fork();
                left.add_true_constraint(&x.ult(ctx, &SymValue::concrete(20, 32)));

                let mut left_deep = left.fork();
                left_deep.add_true_constraint(&y.eq(ctx, &SymValue::concrete(7, 32)));

                let mut right = root.fork();
                right.add_true_constraint(&x.eq(ctx, &SymValue::concrete(99, 32)));
                (solver, left_deep, left, right)
            },
            |(solver, left_deep, left, right)| {
                black_box(solver.is_sat(&left_deep));
                black_box(solver.is_sat(&left));
                black_box(solver.is_sat(&right));
                black_box(solver.stats())
            },
            BatchSize::SmallInput,
        );
    });
}

fn bench_solver_sliced_find_value(c: &mut Criterion) {
    c.bench_function("r2sym/solver_sliced_find_value_cold", |b| {
        b.iter(|| {
            let ctx = Context::thread_local();
            let solver = SymSolver::new(&ctx);
            let mut state = SymState::new(&ctx, 0x1000);

            for idx in 0..24 {
                let reg = format!("u{idx}");
                let sym = format!("sym_u{idx}");
                state.make_symbolic_named(&reg, &sym, 32);
                let value = state.get_register(&reg);
                state.add_true_constraint(&value.eq(&ctx, &SymValue::concrete(idx as u64, 32)));
            }

            state.make_symbolic("y", 32);
            let y = state.get_register("y");
            let y_is_seven = y.to_bv(&ctx).eq(BV::from_u64(7, 32));

            black_box(solver.find_value(&state, &y, &y_is_seven))
        });
    });

    c.bench_function("r2sym/solver_sliced_find_value_hot", |b| {
        b.iter_batched(
            || {
                let ctx = leaked_ctx();
                let solver = SymSolver::new(ctx);
                let mut state = SymState::new(ctx, 0x1000);

                for idx in 0..24 {
                    let reg = format!("u{idx}");
                    let sym = format!("sym_u{idx}");
                    state.make_symbolic_named(&reg, &sym, 32);
                    let value = state.get_register(&reg);
                    state.add_true_constraint(&value.eq(ctx, &SymValue::concrete(idx as u64, 32)));
                }

                state.make_symbolic("y", 32);
                let y = state.get_register("y");
                let y_is_seven = y.to_bv(ctx).eq(BV::from_u64(7, 32));
                (solver, state, y, y_is_seven)
            },
            |(solver, state, y, y_is_seven)| black_box(solver.find_value(&state, &y, &y_is_seven)),
            BatchSize::SmallInput,
        );
    });
}

fn bench_solver_small_connected_query(c: &mut Criterion) {
    c.bench_function("r2sym/solver_small_connected_query_hot", |b| {
        b.iter_batched(
            || {
                let ctx = leaked_ctx();
                let solver = SymSolver::new(ctx);
                let mut state = SymState::new(ctx, 0x1000);
                state.make_symbolic("x", 32);
                let x = state.get_register("x");
                state.constrain_range(&x, 3, 9);
                let x_is_seven = x.to_bv(ctx).eq(BV::from_u64(7, 32));
                (solver, state, x, x_is_seven)
            },
            |(solver, state, x, x_is_seven)| black_box(solver.find_value(&state, &x, &x_is_seven)),
            BatchSize::SmallInput,
        );
    });
}

fn bench_solver_partitioned_is_sat(c: &mut Criterion) {
    c.bench_function("r2sym/solver_partitioned_is_sat_cold", |b| {
        b.iter(|| {
            let ctx = Context::thread_local();
            let solver = SymSolver::new(&ctx);
            let mut state = SymState::new(&ctx, 0x1000);

            for idx in 0..24 {
                let reg = format!("p{idx}");
                let sym = format!("sym_p{idx}");
                state.make_symbolic_named(&reg, &sym, 32);
                let value = state.get_register(&reg);
                state.add_true_constraint(&value.eq(&ctx, &SymValue::concrete(idx as u64, 32)));
            }

            state.make_symbolic("x", 32);
            let x = state.get_register("x");
            state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(1, 32)));
            state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(2, 32)));

            black_box(solver.is_sat(&state));
            black_box(solver.stats())
        });
    });

    c.bench_function("r2sym/solver_partitioned_is_sat_hot", |b| {
        b.iter_batched(
            || {
                let ctx = leaked_ctx();
                let solver = SymSolver::new(ctx);
                let mut state = SymState::new(ctx, 0x1000);

                for idx in 0..24 {
                    let reg = format!("p{idx}");
                    let sym = format!("sym_p{idx}");
                    state.make_symbolic_named(&reg, &sym, 32);
                    let value = state.get_register(&reg);
                    state.add_true_constraint(&value.eq(ctx, &SymValue::concrete(idx as u64, 32)));
                }

                state.make_symbolic("x", 32);
                let x = state.get_register("x");
                state.add_true_constraint(&x.eq(ctx, &SymValue::concrete(1, 32)));
                state.add_true_constraint(&x.eq(ctx, &SymValue::concrete(2, 32)));
                (solver, state)
            },
            |(solver, state)| {
                black_box(solver.is_sat(&state));
                black_box(solver.stats())
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("r2sym/solver_partitioned_prefilter_unsat_hot", |b| {
        b.iter_batched(
            || {
                let ctx = leaked_ctx();
                let solver = SymSolver::new(ctx);
                let mut state = SymState::new(ctx, 0x1000);
                state.make_symbolic("x", 32);
                let x = state.get_register("x");
                state.constrain_range(&x, 3, 9);
                let zero = x.to_bv(ctx).eq(BV::from_u64(0, 32));
                (solver, state, zero)
            },
            |(solver, state, zero)| black_box(solver.sat_with_constraint(&state, &zero)),
            BatchSize::SmallInput,
        );
    });
}

fn bench_solver_cursor_fact_reuse(c: &mut Criterion) {
    c.bench_function("r2sym/solver_cursor_fact_reuse_hot", |b| {
        b.iter_batched(
            || {
                let ctx = leaked_ctx();
                let solver = SymSolver::new(ctx);
                let mut base = SymState::new(ctx, 0x1000);

                for idx in 0..6 {
                    let reg = format!("p{idx}");
                    let sym = format!("sym_p{idx}");
                    base.make_symbolic_named(&reg, &sym, 32);
                    let value = base.get_register(&reg);
                    base.add_true_constraint(&value.eq(ctx, &SymValue::concrete(idx as u64, 32)));
                }

                let prefix_value = base.get_register("p0");
                let prefix_eq = prefix_value.to_bv(ctx).eq(BV::from_u64(0, 32));
                black_box(solver.find_value(&base, &prefix_value, &prefix_eq));

                let mut child = base.fork();
                child.make_symbolic("x", 32);
                let x = child.get_register("x");
                child.constrain_range(&x, 3, 9);
                let x_is_seven = x.to_bv(ctx).eq(BV::from_u64(7, 32));
                (solver, child, x, x_is_seven)
            },
            |(solver, child, x, x_is_seven)| black_box(solver.find_value(&child, &x, &x_is_seven)),
            BatchSize::SmallInput,
        );
    });
}

fn bench_value_normalization_identities(c: &mut Criterion) {
    c.bench_function("r2sym/value_normalization_identities", |b| {
        b.iter(|| {
            let ctx = Context::thread_local();
            let x = SymValue::new_symbolic(&ctx, "x", 32);
            let zero = SymValue::concrete(0, 32);
            let one = SymValue::concrete(1, 32);
            let all_ones = SymValue::concrete(u32::MAX as u64, 32);

            black_box(x.add(&ctx, &zero));
            black_box(x.mul(&ctx, &one));
            black_box(x.and(&ctx, &all_ones));
            black_box(x.xor(&ctx, &x));
            black_box(x.eq(&ctx, &x));
        });
    });
}

fn bench_explore_symbolic_branching(c: &mut Criterion) {
    let func = build_branching_function();
    let config = ExploreConfig {
        max_states: 64,
        max_depth: 32,
        ..Default::default()
    };

    c.bench_function("r2sym/explore_symbolic_branching", |b| {
        b.iter(|| {
            let ctx = Context::thread_local();
            let mut state = SymState::new(&ctx, 0x1000);
            state.make_symbolic("reg:56_0", 64);

            let mut explorer = PathExplorer::with_config(&ctx, config.clone());
            let results = explorer.explore(black_box(&func), state);
            black_box(results.len());
            black_box(explorer.solver().stats())
        });
    });
}

fn bench_explore_branch_tree(c: &mut Criterion) {
    let func = build_branch_tree_function(5);
    let config = ExploreConfig {
        max_states: 256,
        max_depth: 64,
        strategy: ExploreStrategy::Bfs,
        ..Default::default()
    };

    c.bench_function("r2sym/explore_branch_tree", |b| {
        b.iter(|| {
            let ctx = Context::thread_local();
            let mut state = SymState::new(&ctx, 0x3000);
            state.make_symbolic("reg:56_0", 64);

            let mut explorer = PathExplorer::with_config(&ctx, config.clone());
            let results = explorer.explore(black_box(&func), state);
            black_box(results.len());
            black_box(explorer.stats().clone())
        });
    });
}

fn bench_explore_same_pc_merge(c: &mut Criterion) {
    let func = build_join_heavy_function(6);
    let mut group = c.benchmark_group("r2sym/explore_same_pc_merge");

    for (name, merge_states) in [("merge_off", false), ("merge_on", true)] {
        let config = ExploreConfig {
            max_states: 256,
            max_depth: 96,
            strategy: ExploreStrategy::Bfs,
            merge_states,
            ..Default::default()
        };

        group.bench_function(name, |b| {
            b.iter(|| {
                let ctx = Context::thread_local();
                let mut state = SymState::new(&ctx, 0x2000);
                state.make_symbolic("reg:56_0", 64);

                let mut explorer = PathExplorer::with_config(&ctx, config.clone());
                let results = explorer.explore(black_box(&func), state);
                black_box(results.len());
                black_box(explorer.stats().clone())
            });
        });
    }

    group.finish();
}

criterion_group!(
    symex_hotpaths,
    bench_solver_sat_cache,
    bench_solver_prefix_reuse,
    bench_solver_sliced_find_value,
    bench_solver_partitioned_is_sat,
    bench_value_normalization_identities,
    bench_explore_symbolic_branching,
    bench_explore_branch_tree,
    bench_explore_same_pc_merge,
    bench_solver_small_connected_query,
    bench_solver_cursor_fact_reuse
);
criterion_main!(symex_hotpaths);
