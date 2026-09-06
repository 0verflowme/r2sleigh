//! Integration tests for r2sym symbolic execution.
//!
//! These tests verify the symbolic execution engine works correctly
//! with real SSA functions and Z3 constraint solving.

use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
use r2ssa::SsaArtifact;
use r2sym::SymSolver;
use r2sym::path::ExploreStrategy;
use r2sym::sim::{
    CallInfo, FunctionSummary, MemcmpSummary, MemsetSummary, PrintfSummaryBasic, PutsSummary,
    SummaryRegistry,
};
use r2sym::{
    ExploreConfig, PathExplorer, SymState, SymValue, SymbolicReachabilityStatus,
    compile_function_semantics,
};
use std::sync::Arc;
use z3::Context;

// Helper functions for creating varnodes
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

fn region_for_anchor(artifact: &r2sym::SemanticArtifact, anchor: u64) -> &r2sym::SemanticRegion {
    artifact
        .native_body()
        .expect("native artifact")
        .regions
        .values()
        .find(|region| region.anchor == anchor)
        .expect("semantic region")
}

fn make_x86_64_arch() -> ArchSpec {
    let mut arch = ArchSpec::new("x86-64");
    arch.addr_size = 8;
    arch.add_register(RegisterDef::new("RAX", RAX, 8));
    arch.add_register(RegisterDef::new("EAX", RAX, 4));
    arch.add_register(RegisterDef::new("RCX", RCX, 8));
    arch.add_register(RegisterDef::new("EDI", RDI, 4));
    arch.add_register(RegisterDef::new("RDI", RDI, 8));
    arch.add_register(RegisterDef::new("RSI", RSI, 8));
    arch.add_register(RegisterDef::new("RDX", RDX, 8));
    arch
}

// Simulated x86-64 register offsets
const RAX: u64 = 0;
const RBX: u64 = 8;
const RCX: u64 = 16;
const RDI: u64 = 56;
const RSI: u64 = 64;
const RDX: u64 = 72;
const TMP0: u64 = 0x80;

fn make_self_xor_guard_blocks() -> Vec<R2ILBlock> {
    vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntXor {
                    dst: make_reg(TMP0, 8),
                    a: make_reg(RDI, 8),
                    b: make_reg(RDI, 8),
                },
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1),
                    a: make_reg(TMP0, 8),
                    b: make_const(0, 8),
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
    ]
}

#[test]
fn test_symbolic_execution_linear_block() {
    // Test: Simple linear sequence of operations
    // rax = 10
    // rbx = rax + 5
    // Result: rbx should be 15

    let blocks = vec![R2ILBlock {
        addr: 0x1000,
        size: 10,
        ops: vec![
            R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(10, 8),
            },
            R2ILOp::IntAdd {
                dst: make_reg(RBX, 8),
                a: make_reg(RAX, 8),
                b: make_const(5, 8),
            },
        ],
        switch_info: None,
        op_metadata: Default::default(),
    }];

    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");

    let ctx = Context::thread_local();

    let state = SymState::new(&ctx, 0x1000);
    let mut explorer = PathExplorer::new(&ctx);

    let results = explorer.explore(&func, state);

    assert!(!results.is_empty(), "Should have at least one path");

    // Check that we can solve the path
    for path in &results {
        if path.feasible {
            let solved = explorer.solve_path(path);
            assert!(solved.is_some(), "Should be able to solve feasible path");
        }
    }
}

#[test]
fn test_symbolic_execution_with_symbolic_input() {
    // Test: Symbolic input with constraint
    // rax = symbolic
    // rbx = rax + 10
    // constraint: rax < 100

    let blocks = vec![R2ILBlock {
        addr: 0x1000,
        size: 10,
        ops: vec![
            // rax is already symbolic (set in state)
            R2ILOp::IntAdd {
                dst: make_reg(RBX, 8),
                a: make_reg(RAX, 8),
                b: make_const(10, 8),
            },
        ],
        switch_info: None,
        op_metadata: Default::default(),
    }];

    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");

    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    // Make RAX symbolic
    state.make_symbolic("reg:0_0", 64);

    let mut explorer = PathExplorer::new(&ctx);
    let results = explorer.explore(&func, state);

    assert!(!results.is_empty(), "Should have at least one path");

    // The path should be feasible (no constraints yet)
    for path in &results {
        assert!(path.feasible, "Path should be feasible");
    }
}

#[test]
fn test_symbolic_execution_conditional_branch() {
    // Test: Conditional branch with symbolic condition
    // if (rdi == 0x1337) goto 0x1010 else fallthrough
    // 0x1000: cbranch 0x1010, rdi == 0x1337
    // 0x1004: rax = 0  (failure path)
    // 0x1010: rax = 1  (success path)

    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                // Compare: tmp = (rdi == 0x1337)
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1), // Use RCX as temp for condition
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
            size: 6,
            ops: vec![
                // Failure path: rax = 0
                R2ILOp::Copy {
                    dst: make_reg(RAX, 8),
                    src: make_const(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x1010,
            size: 6,
            ops: vec![
                // Success path: rax = 1
                R2ILOp::Copy {
                    dst: make_reg(RAX, 8),
                    src: make_const(1, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        },
    ];

    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");

    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    // Make RDI symbolic (simulating user input)
    state.make_symbolic("reg:56_0", 64);

    let config = ExploreConfig {
        max_states: 100,
        max_completed_paths: None,
        max_depth: 50,
        max_steps: None,
        strategy: ExploreStrategy::Dfs,
        prune_infeasible: true,
        merge_states: false,
        ..ExploreConfig::default()
    };

    let mut explorer = PathExplorer::with_config(&ctx, config);
    let results = explorer.explore(&func, state);

    // Should have explored multiple paths (true and false branches)
    let stats = explorer.stats();
    assert!(
        stats.states_explored > 0,
        "Should have explored some states"
    );

    // Check that we found feasible paths
    let feasible_paths: Vec<_> = results.iter().filter(|p| p.feasible).collect();
    assert!(
        !feasible_paths.is_empty(),
        "Should have at least one feasible path"
    );
}

#[test]
fn compile_function_semantics_prunes_self_xor_dead_branch() {
    let arch = make_x86_64_arch();
    let func = Arc::new(
        SsaArtifact::for_symbolic(&make_self_xor_guard_blocks(), Some(&arch))
            .expect("symbolic ssa"),
    );
    let ctx = Context::thread_local();

    let artifact = compile_function_semantics(&ctx, &func, r2sym::SummaryProfile::Default);
    let region = region_for_anchor(&artifact, 0x1000);

    assert_eq!(
        region.frontier,
        std::collections::BTreeSet::from([0x1004, 0x1010])
    );
    assert!(region.control.iter().any(|fact| {
        fact.value.target == 0x1010
            && fact.value.status == SymbolicReachabilityStatus::Reachable
            && fact.value.branch_truth == Some(true)
    }));
    assert!(region.control.iter().any(|fact| {
        fact.value.target == 0x1004
            && fact.value.status == SymbolicReachabilityStatus::Unreachable
            && fact.value.branch_truth == Some(false)
    }));
    assert_eq!(artifact.diagnostics.branches_pruned, 1);
}

#[test]
fn test_find_paths_to_collects_multiple_matches() {
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
            ops: vec![R2ILOp::Branch {
                target: make_const(0x1010, 8),
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

    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let mut explorer = PathExplorer::new(&ctx);
    let paths = explorer.find_paths_to(&func, state, 0x1010);
    assert!(
        paths.len() >= 2,
        "Expected multiple target-reaching paths, got {}",
        paths.len()
    );
}

#[test]
fn test_find_paths_to_unreachable_returns_empty() {
    let blocks = vec![R2ILBlock {
        addr: 0x1000,
        size: 4,
        ops: vec![R2ILOp::Copy {
            dst: make_reg(RAX, 8),
            src: make_const(1, 8),
        }],
        switch_info: None,
        op_metadata: Default::default(),
    }];

    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();
    let state = SymState::new(&ctx, 0x1000);
    let mut explorer = PathExplorer::new(&ctx);
    let paths = explorer.find_paths_to(&func, state, 0x2000);
    assert!(
        paths.is_empty(),
        "Expected no paths for unreachable target, got {}",
        paths.len()
    );
}

#[test]
fn test_find_paths_to_honors_limits() {
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1),
                    a: make_reg(RDI, 8),
                    b: make_const(0, 8),
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

    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let config = ExploreConfig {
        max_states: 0,
        max_completed_paths: None,
        max_depth: 50,
        max_steps: None,
        strategy: ExploreStrategy::Dfs,
        prune_infeasible: true,
        merge_states: false,
        ..ExploreConfig::default()
    };
    let mut explorer = PathExplorer::with_config(&ctx, config);
    let paths = explorer.find_paths_to(&func, state, 0x1010);
    assert!(
        paths.is_empty(),
        "Expected no matches when max_states=0, got {}",
        paths.len()
    );
}

#[test]
fn test_find_paths_to_with_same_pc_merge_still_reaches_target() {
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
            ops: vec![R2ILOp::Branch {
                target: make_const(0x1010, 8),
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

    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let config = ExploreConfig {
        max_states: 100,
        max_completed_paths: None,
        max_depth: 50,
        max_steps: None,
        strategy: ExploreStrategy::Bfs,
        prune_infeasible: true,
        merge_states: true,
        ..ExploreConfig::default()
    };
    let mut explorer = PathExplorer::with_config(&ctx, config);
    let paths = explorer.find_paths_to(&func, state, 0x1010);

    assert!(
        !paths.is_empty(),
        "Expected at least one feasible merged path to target"
    );
    assert!(paths.iter().all(|path| path.final_pc() == 0x1010));
    assert!(paths.iter().all(|path| path.feasible));
}

#[test]
fn test_explore_honors_max_completed_paths() {
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

    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let config = ExploreConfig {
        max_states: 100,
        max_completed_paths: Some(1),
        max_depth: 50,
        max_steps: None,
        strategy: ExploreStrategy::Bfs,
        prune_infeasible: true,
        merge_states: false,
        ..ExploreConfig::default()
    };
    let mut explorer = PathExplorer::with_config(&ctx, config);
    let paths = explorer.explore(&func, state);

    assert_eq!(
        paths.len(),
        1,
        "explore should stop after the configured cap"
    );
}

#[test]
fn test_symbolic_arithmetic_operations() {
    // Test all arithmetic operations with symbolic values
    let ctx = Context::thread_local();

    let _state = SymState::new(&ctx, 0x1000);

    // Create symbolic values
    let x = SymValue::new_symbolic(&ctx, "x", 64);
    let y = SymValue::new_symbolic(&ctx, "y", 64);

    // Test addition
    let sum = x.add(&ctx, &y);
    assert!(sum.is_symbolic(), "Sum should be symbolic");

    // Test subtraction
    let diff = x.sub(&ctx, &y);
    assert!(diff.is_symbolic(), "Diff should be symbolic");

    // Test multiplication
    let prod = x.mul(&ctx, &y);
    assert!(prod.is_symbolic(), "Product should be symbolic");

    // Test concrete operations
    let a = SymValue::concrete(10, 64);
    let b = SymValue::concrete(3, 64);

    let sum_concrete = a.add(&ctx, &b);
    assert_eq!(sum_concrete.as_concrete(), Some(13));

    let diff_concrete = a.sub(&ctx, &b);
    assert_eq!(diff_concrete.as_concrete(), Some(7));

    let prod_concrete = a.mul(&ctx, &b);
    assert_eq!(prod_concrete.as_concrete(), Some(30));

    let div_concrete = a.udiv(&ctx, &b);
    assert_eq!(div_concrete.as_concrete(), Some(3));

    let rem_concrete = a.urem(&ctx, &b);
    assert_eq!(rem_concrete.as_concrete(), Some(1));
}

#[test]
fn test_symbolic_bitwise_operations() {
    let ctx = Context::thread_local();

    // Test concrete bitwise
    let a = SymValue::concrete(0b1100, 8);
    let b = SymValue::concrete(0b1010, 8);

    assert_eq!(a.and(&ctx, &b).as_concrete(), Some(0b1000));
    assert_eq!(a.or(&ctx, &b).as_concrete(), Some(0b1110));
    assert_eq!(a.xor(&ctx, &b).as_concrete(), Some(0b0110));

    // Test shifts
    let amt = SymValue::concrete(2, 8);
    assert_eq!(a.shl(&ctx, &amt).as_concrete(), Some(0b110000));
    assert_eq!(a.lshr(&ctx, &amt).as_concrete(), Some(0b0011));

    // Test symbolic bitwise
    let x = SymValue::new_symbolic(&ctx, "x", 64);
    let y = SymValue::new_symbolic(&ctx, "y", 64);

    assert!(x.and(&ctx, &y).is_symbolic());
    assert!(x.or(&ctx, &y).is_symbolic());
    assert!(x.xor(&ctx, &y).is_symbolic());
}

#[test]
fn test_symbolic_comparisons() {
    let ctx = Context::thread_local();

    let a = SymValue::concrete(10, 32);
    let b = SymValue::concrete(20, 32);

    // Equality
    assert_eq!(a.eq(&ctx, &a).as_concrete(), Some(1));
    assert_eq!(a.eq(&ctx, &b).as_concrete(), Some(0));

    // Unsigned less than
    assert_eq!(a.ult(&ctx, &b).as_concrete(), Some(1));
    assert_eq!(b.ult(&ctx, &a).as_concrete(), Some(0));

    // Unsigned less than or equal
    assert_eq!(a.ule(&ctx, &b).as_concrete(), Some(1));
    assert_eq!(a.ule(&ctx, &a).as_concrete(), Some(1));
    assert_eq!(b.ule(&ctx, &a).as_concrete(), Some(0));
}

#[test]
fn test_symbolic_memory_operations() {
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);

    // Write concrete value to concrete address
    let addr = SymValue::concrete(0x2000, 64);
    let value = SymValue::concrete(0xDEADBEEF, 32);
    state.mem_write(&addr, &value, 4);

    // Read it back
    let read_value = state.mem_read(&addr, 4);
    assert_eq!(read_value.as_concrete(), Some(0xDEADBEEF));

    // Write symbolic value
    let sym_value = SymValue::new_symbolic(&ctx, "mem_data", 64);
    let addr2 = SymValue::concrete(0x3000, 64);
    state.mem_write(&addr2, &sym_value, 8);

    // Read symbolic value
    let read_sym = state.mem_read(&addr2, 8);
    assert!(read_sym.is_symbolic());
}

#[test]
fn test_state_forking() {
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.set_concrete("rax", 42, 64);
    state.make_symbolic("rbx", 64);

    // Fork the state
    let forked = state.fork();

    // Original and fork should have same values
    assert_eq!(forked.pc(), state.pc());
    assert_eq!(
        forked.get_register("rax").as_concrete(),
        state.get_register("rax").as_concrete()
    );

    // Modifications to one shouldn't affect the other
    state.set_concrete("rax", 100, 64);
    assert_eq!(state.get_register("rax").as_concrete(), Some(100));
    assert_eq!(forked.get_register("rax").as_concrete(), Some(42));
}

#[test]
fn test_constraint_solving() {
    use r2sym::SymSolver;

    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("x", 32);

    let x = state.get_register("x");

    // Add constraint: x < 100
    let hundred = SymValue::concrete(100, 32);
    let cond = x.ult(&ctx, &hundred);
    state.add_true_constraint(&cond);

    // Solve
    let solver = SymSolver::new(&ctx);
    assert!(solver.is_sat(&state), "Constraints should be satisfiable");

    let model = solver.solve(&state);
    assert!(model.is_some(), "Should get a model");

    // The model should give us a value for x that is < 100
    let model = model.unwrap();
    if let Some(x_val) = model.eval(&x) {
        assert!(x_val < 100, "x should be less than 100, got {}", x_val);
    }
}

#[test]
fn test_unsatisfiable_constraints() {
    use r2sym::SymSolver;

    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("x", 32);

    let x = state.get_register("x");

    // Add contradictory constraints: x > 100 AND x < 50
    let hundred = SymValue::concrete(100, 32);
    let fifty = SymValue::concrete(50, 32);

    // x > 100 (equivalent to 100 < x, or NOT(x <= 100))
    let gt_100 = hundred.ult(&ctx, &x);
    state.add_true_constraint(&gt_100);

    // x < 50
    let lt_50 = x.ult(&ctx, &fifty);
    state.add_true_constraint(&lt_50);

    // Should be unsatisfiable
    let solver = SymSolver::new(&ctx);
    assert!(
        !solver.is_sat(&state),
        "Contradictory constraints should be unsatisfiable"
    );
}

#[test]
fn test_explore_config() {
    let config = ExploreConfig::default();
    assert_eq!(config.max_states, 1000);
    assert_eq!(config.max_depth, 100);
    assert!(config.prune_infeasible);
    assert!(!config.merge_states);
    assert_eq!(config.strategy, ExploreStrategy::Dfs);
}

#[test]
fn test_path_result_properties() {
    use r2sym::PathResult;

    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.set_register("rax", SymValue::concrete(42, 64));
    state.make_symbolic("rbx", 64);

    let result = PathResult::new(state, true);

    assert_eq!(result.final_pc(), 0x1000);
    assert_eq!(result.num_constraints(), 0);
    assert!(result.register_names().contains(&"rax".to_string()));
    assert_eq!(result.get_concrete_register("rax"), Some(42));
    assert!(result.is_register_symbolic("rbx"));
}

#[test]
fn test_different_bitwidth_operations() {
    // Test that operations with different bit widths work correctly
    let ctx = Context::thread_local();

    // 8-bit and 64-bit values
    let val8 = SymValue::concrete(5, 8);
    let val64 = SymValue::concrete(10, 64);

    // Should handle mismatch gracefully
    let result = val8.add(&ctx, &val64);
    assert_eq!(result.as_concrete(), Some(15));
    assert_eq!(result.bits(), 64); // Result uses larger width

    // Symbolic with different widths
    let sym8 = SymValue::new_symbolic(&ctx, "x", 8);
    let sym64 = SymValue::new_symbolic(&ctx, "y", 64);

    let sym_result = sym8.add(&ctx, &sym64);
    assert!(sym_result.is_symbolic());
    assert_eq!(sym_result.bits(), 64);
}

#[test]
fn memset_summary_writes_bounded_bytes() {
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    let summary = MemsetSummary::new(4);
    let call = CallInfo {
        args: vec![
            SymValue::concrete(0x2000, 64),
            SymValue::concrete(0x41, 64),
            SymValue::concrete(10, 64),
        ],
        arg_bits: 64,
        ret_bits: 64,
    };

    let effect = summary.execute(&mut state, &call);
    match effect {
        r2sym::SummaryEffect::Return(Some(ret)) => {
            assert_eq!(ret.as_concrete(), Some(0x2000));
        }
        _ => panic!("memset summary should return destination pointer"),
    }

    let bytes = state
        .memory
        .read_bytes(0x2000, 4)
        .expect("memset should materialize concrete bytes");
    assert_eq!(bytes, vec![0x41, 0x41, 0x41, 0x41]);
    assert!(
        state.memory.read_bytes(0x2004, 1).is_none(),
        "memset should be bounded by configured max"
    );
}

#[test]
fn memcmp_summary_returns_trivalued_result() {
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    let summary = MemcmpSummary::new(32);
    let call = CallInfo {
        args: vec![
            SymValue::concrete(0x3000, 64),
            SymValue::concrete(0x4000, 64),
            SymValue::concrete(8, 64),
        ],
        arg_bits: 64,
        ret_bits: 64,
    };

    let ret = match summary.execute(&mut state, &call) {
        r2sym::SummaryEffect::Return(Some(ret)) => ret,
        _ => panic!("memcmp summary should return a value"),
    };

    let solver = SymSolver::new(&ctx);
    for allowed in [u64::MAX, 0, 1] {
        let mut candidate = state.fork();
        candidate.constrain_eq(&ret, allowed);
        assert!(
            solver.is_sat(&candidate),
            "memcmp return should allow value {allowed:#x}"
        );
    }

    let mut disallowed = state.fork();
    disallowed.constrain_eq(&ret, 2);
    assert!(
        !solver.is_sat(&disallowed),
        "memcmp return must be constrained to -1/0/1"
    );
}

#[test]
fn printf_summary_does_not_terminate_path() {
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    let summary = PrintfSummaryBasic::new(32);
    let call = CallInfo {
        args: vec![SymValue::concrete(0x5000, 64)],
        arg_bits: 64,
        ret_bits: 64,
    };

    let effect = summary.execute(&mut state, &call);
    assert!(matches!(effect, r2sym::SummaryEffect::Return(Some(_))));
    assert!(
        state.active,
        "printf summary should not terminate the state"
    );
}

#[test]
fn puts_summary_does_not_terminate_path() {
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    let summary = PutsSummary::new(32);
    let call = CallInfo {
        args: vec![SymValue::concrete(0x6000, 64)],
        arg_bits: 64,
        ret_bits: 64,
    };

    let effect = summary.execute(&mut state, &call);
    assert!(matches!(effect, r2sym::SummaryEffect::Return(Some(_))));
    assert!(state.active, "puts summary should not terminate the state");
}

#[test]
fn registry_with_core_contains_new_summaries() {
    let ctx = Context::thread_local();
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let mut explorer = PathExplorer::new(&ctx);

    assert!(registry.install_for_explorer(&mut explorer, 0x1000, "memcmp"));
    assert!(registry.install_for_explorer(&mut explorer, 0x1001, "memset"));
    assert!(registry.install_for_explorer(&mut explorer, 0x1002, "puts"));
    assert!(registry.install_for_explorer(&mut explorer, 0x1003, "printf"));
}

#[test]
fn symbolic_n_constraints_bounded_for_memset_memcmp() {
    let ctx = Context::thread_local();

    let mut state_memset = SymState::new(&ctx, 0x1000);
    let memset = MemsetSummary::new(8);
    let n_memset = SymValue::new_symbolic(&ctx, "sym_memset_n", 64);
    let call_memset = CallInfo {
        args: vec![
            SymValue::concrete(0x7000, 64),
            SymValue::concrete(0x7f, 64),
            n_memset,
        ],
        arg_bits: 64,
        ret_bits: 64,
    };
    let before_memset = state_memset.num_constraints();
    let _ = memset.execute(&mut state_memset, &call_memset);
    assert!(
        state_memset.num_constraints() > before_memset,
        "symbolic memset length should add bounds constraints"
    );

    let mut state_memcmp = SymState::new(&ctx, 0x1000);
    let memcmp = MemcmpSummary::new(8);
    let n_memcmp = SymValue::new_symbolic(&ctx, "sym_memcmp_n", 64);
    let call_memcmp = CallInfo {
        args: vec![
            SymValue::concrete(0x7100, 64),
            SymValue::concrete(0x7200, 64),
            n_memcmp,
        ],
        arg_bits: 64,
        ret_bits: 64,
    };
    let before_memcmp = state_memcmp.num_constraints();
    let _ = memcmp.execute(&mut state_memcmp, &call_memcmp);
    assert!(
        state_memcmp.num_constraints() > before_memcmp,
        "symbolic memcmp length should add bounds constraints"
    );
}
