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
use r2sym::spec::{AddressValue, ExplorationSpec, InputSpec, PredicateSpec};
use r2sym::{
    BackwardConditionPrecision, BackwardMemoryCondition, BackwardMemoryRegion, ExploreConfig,
    PathExplorer, QueryCompletion, ReachabilityStatus, RefinementStage, ReplayRegisterOverlay,
    ReplayRegisterValue, ReplaySeed, SolveStatus, SymQueryConfig, SymState, SymValue,
    SymbolicReachabilityStatus, compile_derived_summary_return_postcondition,
    compile_function_semantics_with_scope,
};
use z3::Context;
use z3::ast::{BV, Bool};

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

fn assert_argument_memory_term(
    term: &BackwardMemoryCondition,
    index: usize,
    offset_lo: i64,
    offset_hi: i64,
    exact_offset: bool,
    size: u32,
) {
    assert!(matches!(
        &term.region,
        BackwardMemoryRegion::Argument { index: actual } if *actual == index
    ));
    assert_eq!(term.address.offset_lo(), offset_lo);
    assert_eq!(term.address.offset_hi(), offset_hi);
    assert_eq!(term.address.is_exact_offset(), exact_offset);
    assert_eq!(term.size, size);
}

fn assert_region_memory_term(
    term: &BackwardMemoryCondition,
    kind: r2sym::MemoryRegionKind,
    name: &str,
    offset_lo: i64,
    offset_hi: i64,
    exact_offset: bool,
    size: u32,
) {
    match &term.region {
        BackwardMemoryRegion::Region(region) => {
            assert_eq!(region.kind, kind);
            assert_eq!(region.name, name);
        }
        other => panic!("expected concrete region-backed term, got {other:?}"),
    }
    assert_eq!(term.address.offset_lo(), offset_lo);
    assert_eq!(term.address.offset_hi(), offset_hi);
    assert_eq!(term.address.is_exact_offset(), exact_offset);
    assert_eq!(term.size, size);
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
const TMP1: u64 = 0x88;

fn make_conditional_branch_blocks() -> Vec<R2ILBlock> {
    vec![
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
            size: 6,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x1010,
            size: 6,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
    ]
}

fn make_conditional_branch_blocks_low32_arg() -> Vec<R2ILBlock> {
    vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1),
                    a: make_reg(RDI, 4),
                    b: make_const(0xdead, 4),
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
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x1010,
            size: 6,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
    ]
}

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

fn make_target_guided_budget_blocks() -> Vec<R2ILBlock> {
    vec![
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
                    target: make_const(0x2000, 8),
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
                target: make_const(0x1008, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x1008,
            size: 4,
            ops: vec![R2ILOp::Branch {
                target: make_const(0x100c, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x100c,
            size: 4,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x2000,
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
        timeout: None,
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
fn test_query_defaults_enable_subsumption() {
    let config = SymQueryConfig::default();
    assert!(config.explore.subsumption_states);
}

#[test]
fn test_query_target_guided_mode_enables_ranked_query_search() {
    let ctx = Context::thread_local();
    let explorer = SymQueryConfig {
        mode: r2sym::QueryMode::TargetGuided,
        ..SymQueryConfig::default()
    }
    .make_explorer(&ctx);
    assert!(explorer.target_guided_queries_enabled());
}

#[test]
fn test_query_can_reach_reports_reachable_and_unreachable() {
    let blocks = make_conditional_branch_blocks();
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();

    let mut reachable_state = SymState::new(&ctx, 0x1000);
    reachable_state.make_symbolic("reg:56_0", 64);
    let mut explorer = SymQueryConfig {
        mode: r2sym::QueryMode::TargetGuided,
        ..SymQueryConfig::default()
    }
    .make_explorer(&ctx);
    let reachable = explorer.can_reach(&func, reachable_state, 0x1010);
    assert_eq!(reachable.status, ReachabilityStatus::Reachable);
    assert!(!reachable.paths.is_empty());

    let mut unreachable_state = SymState::new(&ctx, 0x1000);
    unreachable_state.make_symbolic("reg:56_0", 64);
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let unreachable = explorer.can_reach(&func, unreachable_state, 0x2000);
    assert_eq!(unreachable.status, ReachabilityStatus::Unreachable);
    assert!(unreachable.paths.is_empty());
}

#[test]
fn test_query_solve_for_target_returns_solution() {
    let blocks = make_conditional_branch_blocks();
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let solve = explorer.solve_for_target(&func, state, 0x1010);
    assert_eq!(solve.status, SolveStatus::Solved);
    assert_eq!(
        solve
            .compiled_precondition
            .as_ref()
            .map(|compiled| compiled.precision),
        Some(BackwardConditionPrecision::Exact)
    );
    assert!(solve.selected_path_index.is_some());
    assert!(solve.solution.is_some());
    assert!(solve.verification.candidate_solution_verified);
    assert!(matches!(
        solve.verification.model_validation,
        r2sym::ModelValidation::Verified
    ));
    assert!(solve.witness.is_proven());
}

#[test]
fn test_query_path_conditions_at_collects_conditions() {
    let blocks = make_conditional_branch_blocks();
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let conditions = explorer.path_conditions_at(&func, state, 0x1010);
    assert_eq!(
        conditions
            .compiled_precondition
            .as_ref()
            .map(|compiled| compiled.precision),
        Some(BackwardConditionPrecision::Exact)
    );
    assert!(!conditions.conditions.is_empty());
    assert!(
        conditions
            .conditions
            .iter()
            .all(|condition| condition.final_pc == 0x1010)
    );
    assert!(
        conditions
            .conditions
            .iter()
            .all(|condition| condition.num_constraints > 0)
    );
    assert!(conditions.conditions.iter().all(|condition| {
        condition.condition == condition.path_condition.simplified
            && condition.path_condition.num_constraints == condition.num_constraints
            && condition.path_condition.terms.len() == condition.num_constraints
    }));
}

#[test]
fn test_query_compiled_precondition_shortcuts_exact_unsat() {
    let blocks = make_conditional_branch_blocks();
    let arch = make_x86_64_arch();
    let func =
        SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("Failed to build SSA function");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic_named("RDI_0", "rdi", 64);
    let rdi = state.get_register_sized("RDI_0", 64);
    state.constrain_ne(&rdi, 0x1337);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let solve = explorer.solve_for_target(&func, state, 0x1010);
    assert_eq!(solve.status, SolveStatus::Unsat);
    assert!(solve.matched_paths.is_empty());
    assert_eq!(
        solve
            .compiled_precondition
            .as_ref()
            .map(|compiled| compiled.precision),
        Some(BackwardConditionPrecision::Exact)
    );
}

#[test]
fn test_query_load_dependent_precondition_compiles_through_local_store() {
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Store {
                    addr: make_const(0x2000, 8),
                    val: make_reg(RDI, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::Load {
                    dst: make_reg(TMP0, 8),
                    addr: make_const(0x2000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 8),
                    b: make_const(0x1337, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(1, 8),
            }],
        },
    ];
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let solve = explorer.solve_for_target(&func, state, 0x1010);
    assert_eq!(solve.status, SolveStatus::Solved);
    assert_eq!(
        solve
            .compiled_precondition
            .as_ref()
            .map(|compiled| compiled.precision),
        Some(BackwardConditionPrecision::Exact)
    );
    assert!(!solve.matched_paths.is_empty());
    assert!(solve.solution.is_some());
}

#[test]
fn test_query_load_dependent_precondition_emits_region_backed_global_term() {
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 8),
                    addr: make_const(0x2000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 8),
                    b: make_const(0x41, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(1, 8),
            }],
        },
    ];
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    let region = state.define_memory_region(
        r2sym::MemoryRegionKind::Global,
        "global_2000",
        Some(0x2000),
        Some(8),
    );
    state.seed_region_bytes(region, 0, &[0x41, 0, 0, 0, 0, 0, 0, 0]);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let conditions = explorer.path_conditions_at(&func, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");

    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_region_memory_term(
        &compiled.memory_terms[0],
        r2sym::MemoryRegionKind::Global,
        "global_2000",
        0,
        0,
        true,
        8,
    );
}

#[test]
fn test_query_load_dependent_precondition_emits_region_backed_stack_term() {
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 8),
                    addr: make_const(0x7008, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 8),
                    b: make_const(0x41, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(1, 8),
            }],
        },
    ];
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    let region = state.define_memory_region(
        r2sym::MemoryRegionKind::Stack,
        "stack_window",
        Some(0x7000),
        Some(0x100),
    );
    state.seed_region_bytes(region, 8, &[0x41, 0, 0, 0, 0, 0, 0, 0]);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let conditions = explorer.path_conditions_at(&func, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");

    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_region_memory_term(
        &compiled.memory_terms[0],
        r2sym::MemoryRegionKind::Stack,
        "stack_window",
        8,
        8,
        true,
        8,
    );
}

#[test]
fn test_query_load_dependent_precondition_emits_region_backed_replay_term() {
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 8),
                    addr: make_const(0x9004, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 8),
                    b: make_const(0x41, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(1, 8),
            }],
        },
    ];
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    let region = state.define_memory_region(
        r2sym::MemoryRegionKind::Replay,
        "replay_window",
        Some(0x9000),
        Some(0x100),
    );
    state.seed_region_bytes(region, 4, &[0x41, 0, 0, 0, 0, 0, 0, 0]);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let conditions = explorer.path_conditions_at(&func, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");

    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_region_memory_term(
        &compiled.memory_terms[0],
        r2sym::MemoryRegionKind::Replay,
        "replay_window",
        4,
        4,
        true,
        8,
    );
}

#[test]
fn test_query_load_dependent_precondition_emits_region_backed_heap_term() {
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 8),
                    addr: make_const(0xa004, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 8),
                    b: make_const(0x41, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(1, 8),
            }],
        },
    ];
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    let region = state.define_memory_region(
        r2sym::MemoryRegionKind::Heap,
        "heap_window",
        Some(0xa000),
        Some(0x100),
    );
    state.seed_region_bytes(region, 4, &[0x41, 0, 0, 0, 0, 0, 0, 0]);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let conditions = explorer.path_conditions_at(&func, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");

    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_region_memory_term(
        &compiled.memory_terms[0],
        r2sym::MemoryRegionKind::Heap,
        "heap_window",
        4,
        4,
        true,
        8,
    );
}

#[test]
fn test_replay_seeded_query_solve_with_register_overlay() {
    let blocks = make_conditional_branch_blocks();
    let arch = make_x86_64_arch();
    let func =
        SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("Failed to build SSA function");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    let seed = ReplaySeed {
        checkpoint_id: Some(2),
        entry_pc: Some(0x1000),
        registers: vec![ReplayRegisterValue {
            name: "rdi".to_string(),
            value: 0,
        }],
        register_overlays: vec![ReplayRegisterOverlay {
            name: "rdi".to_string(),
            symbol: "rdi".to_string(),
        }],
        ..ReplaySeed::default()
    };
    r2sym::seed_replay_state_for_arch(&mut state, Some(&func), Some(&arch), &seed);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let solve = explorer.solve_for_target(&func, state, 0x1010);
    assert_eq!(solve.status, SolveStatus::Solved);
    assert_eq!(
        solve
            .compiled_precondition
            .as_ref()
            .map(|compiled| compiled.precision),
        Some(BackwardConditionPrecision::Exact)
    );
    let solution = solve.solution.expect("solution");
    assert_eq!(solution.inputs.get("rdi").copied(), Some(0x1337));
}

#[test]
fn test_query_compiles_bounded_indexed_memory_range() {
    let arch = make_x86_64_arch();
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: make_reg(TMP0, 8),
                    a: make_reg(RDI, 8),
                    b: make_reg(RCX, 8),
                },
                R2ILOp::Load {
                    dst: make_reg(TMP1, 1),
                    addr: make_reg(TMP0, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(RDX, 1),
                    a: make_reg(TMP1, 1),
                    b: make_const(0x41, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(RDX, 1),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x1004,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(1, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        },
    ];
    let func = SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("ssa");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    r2sym::seed_default_state_for_arch(&mut state, &func, Some(&arch));
    let rcx = state.get_register_sized("RCX_0", 64);
    let is_zero = rcx.to_bv(&ctx).eq(BV::from_u64(0, 64));
    let is_one = rcx.to_bv(&ctx).eq(BV::from_u64(1, 64));
    state.add_constraint(Bool::or(&[&is_zero, &is_one]));

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let conditions = explorer.path_conditions_at(&func, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");

    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    if matches!(
        &compiled.memory_terms[0].region,
        BackwardMemoryRegion::Argument { .. }
    ) {
        assert_eq!(compiled.memory_terms[0].address.offset_lo(), 0);
        assert_eq!(compiled.memory_terms[0].address.offset_hi(), 1);
    } else {
        assert!(
            compiled.memory_terms[0].address.offset_hi()
                >= compiled.memory_terms[0].address.offset_lo()
        );
    }
    assert!(!compiled.memory_terms[0].address.is_exact_offset());
    assert_eq!(compiled.memory_terms[0].size, 1);
    assert!(compiled.backward_memory_candidate_enumerations > 0);
    assert_eq!(compiled.backward_memory_residual_fallbacks, 0);
}

#[test]
fn test_replay_seeded_query_solve_with_register_alias_overlay() {
    let blocks = make_conditional_branch_blocks_low32_arg();
    let arch = make_x86_64_arch();
    let func =
        SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("Failed to build SSA function");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    let seed = ReplaySeed {
        checkpoint_id: Some(2),
        entry_pc: Some(0x1000),
        registers: vec![ReplayRegisterValue {
            name: "rdi".to_string(),
            value: 0,
        }],
        register_overlays: vec![ReplayRegisterOverlay {
            name: "rdi".to_string(),
            symbol: "rdi".to_string(),
        }],
        ..ReplaySeed::default()
    };
    r2sym::seed_replay_state_for_arch(&mut state, Some(&func), Some(&arch), &seed);

    assert!(state.get_register("EDI_0").is_symbolic());
    assert!(!state.registers().contains_key("RDI"));

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let solve = explorer.solve_for_target(&func, state, 0x1010);
    assert_eq!(solve.status, SolveStatus::Solved);
    let solution = solve.solution.expect("solution");
    assert_eq!(solution.inputs.get("rdi").copied(), Some(0xdead));
}

#[test]
fn test_query_target_guided_can_reach_finds_target_under_tight_budget() {
    let blocks = make_target_guided_budget_blocks();
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let forward_config = SymQueryConfig {
        explore: ExploreConfig {
            max_states: 2,
            ..ExploreConfig::default()
        },
        mode: r2sym::QueryMode::ForwardOnly,
        ..SymQueryConfig::default()
    };
    let mut forward = forward_config.make_explorer(&ctx);
    let forward_result = forward.can_reach(&func, state.fork(), 0x2000);
    assert!(
        matches!(
            forward_result.status,
            ReachabilityStatus::BudgetExhausted | ReachabilityStatus::Reachable
        ),
        "forward query should stay honest under tight budgets"
    );

    let guided_config = SymQueryConfig {
        explore: ExploreConfig {
            max_states: 2,
            ..ExploreConfig::default()
        },
        mode: r2sym::QueryMode::TargetGuided,
        ..SymQueryConfig::default()
    };
    let mut guided = guided_config.make_explorer(&ctx);
    let guided_result = guided.can_reach(&func, state, 0x2000);
    assert_eq!(guided_result.status, ReachabilityStatus::Reachable);
    assert_eq!(guided_result.paths.len(), 1);
}

#[test]
fn compile_function_semantics_prunes_self_xor_dead_branch() {
    let arch = make_x86_64_arch();
    let func = SsaArtifact::for_symbolic(&make_self_xor_guard_blocks(), Some(&arch))
        .expect("symbolic ssa");
    let ctx = Context::thread_local();

    let artifact = compile_function_semantics_with_scope(
        &ctx,
        &func,
        None,
        Some(&arch),
        &r2sym::FunctionSymbolSnapshot::default(),
        r2sym::SummaryProfile::Default,
    );
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
fn compile_function_semantics_with_scope_prunes_helper_return_dead_branch() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Call {
                target: make_const(0x2000, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::IntNotEqual {
                    dst: make_reg(TMP0, 1),
                    a: make_reg(RAX, 8),
                    b: make_const(0, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP0, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntXor {
                dst: make_reg(RAX, 8),
                a: make_reg(RDI, 8),
                b: make_reg(RDI, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_decompile(&root_blocks, Some(&arch)).expect("root decompile function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_zero".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let artifact = compile_function_semantics_with_scope(
        &ctx,
        &root,
        Some(&scope),
        Some(&arch),
        &r2sym::FunctionSymbolSnapshot::default(),
        r2sym::SummaryProfile::Default,
    );
    let region = region_for_anchor(&artifact, 0x1004);
    assert_eq!(
        region.frontier,
        std::collections::BTreeSet::from([0x1008, 0x1010])
    );
    assert!(region.control.iter().any(|fact| {
        fact.value.target == 0x1010
            && fact.value.status == SymbolicReachabilityStatus::Unreachable
            && fact.value.branch_truth == Some(true)
    }));
    assert!(region.control.iter().any(|fact| {
        fact.value.target == 0x1008
            && fact.value.status == SymbolicReachabilityStatus::Reachable
            && fact.value.branch_truth == Some(false)
    }));
    assert_eq!(artifact.diagnostics.branches_pruned, 1);
}

#[test]
fn compile_function_semantics_with_scope_marks_helper_scope_compiled() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Call {
                target: make_const(0x2000, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::IntNotEqual {
                    dst: make_reg(TMP0, 1),
                    a: make_reg(RAX, 8),
                    b: make_const(0, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP0, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntXor {
                dst: make_reg(RAX, 8),
                a: make_reg(RDI, 8),
                b: make_reg(RDI, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_decompile(&root_blocks, Some(&arch)).expect("root decompile function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_zero".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let compiled = compile_function_semantics_with_scope(
        &ctx,
        &root,
        Some(&scope),
        Some(&arch),
        &r2sym::FunctionSymbolSnapshot::default(),
        r2sym::SummaryProfile::Default,
    );

    let summary = &compiled
        .native_body()
        .expect("native artifact body")
        .summary;

    assert_eq!(compiled.stage, RefinementStage::Compiled);
    assert_eq!(summary.closure_functions, 2);
    assert_eq!(summary.helper_functions, 1);
    assert!(summary.derived_summaries >= 1);
    assert_eq!(compiled.diagnostics.branches_pruned, 1);
}

#[test]
fn compile_function_semantics_with_scope_prunes_helper_return_spilled_dead_branch() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Call {
                target: make_const(0x2000, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: Varnode {
                        space: SpaceId::Ram,
                        offset: 0x4000,
                        size: 8,
                        meta: None,
                    },
                    val: make_reg(RAX, 8),
                },
                R2ILOp::Load {
                    dst: make_reg(TMP0, 8),
                    space: SpaceId::Ram,
                    addr: Varnode {
                        space: SpaceId::Ram,
                        offset: 0x4000,
                        size: 8,
                        meta: None,
                    },
                },
                R2ILOp::IntNotEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 8),
                    b: make_const(0, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntXor {
                dst: make_reg(RAX, 8),
                a: make_reg(RDI, 8),
                b: make_reg(RDI, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_decompile(&root_blocks, Some(&arch)).expect("root decompile function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_zero".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let artifact = compile_function_semantics_with_scope(
        &ctx,
        &root,
        Some(&scope),
        Some(&arch),
        &r2sym::FunctionSymbolSnapshot::default(),
        r2sym::SummaryProfile::Default,
    );
    let region = region_for_anchor(&artifact, 0x1004);
    assert_eq!(
        region.frontier,
        std::collections::BTreeSet::from([0x1008, 0x1010])
    );
    assert!(region.control.iter().any(|fact| {
        fact.value.target == 0x1010
            && fact.value.status == SymbolicReachabilityStatus::Unreachable
            && fact.value.branch_truth == Some(true)
    }));
    assert!(region.control.iter().any(|fact| {
        fact.value.target == 0x1008
            && fact.value.status == SymbolicReachabilityStatus::Reachable
            && fact.value.branch_truth == Some(false)
    }));
    assert_eq!(artifact.diagnostics.branches_pruned, 1);
}

#[test]
fn compile_function_semantics_with_scope_prunes_helper_return_dead_branch_via_eax_alias() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Call {
                target: make_const(0x2000, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::IntEqual {
                    dst: make_reg(TMP0, 1),
                    a: make_reg(RAX, 4),
                    b: make_const(0, 4),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP0, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntXor {
                dst: make_reg(RAX, 8),
                a: make_reg(RDI, 8),
                b: make_reg(RDI, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_decompile(&root_blocks, Some(&arch)).expect("root decompile function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_zero".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let artifact = compile_function_semantics_with_scope(
        &ctx,
        &root,
        Some(&scope),
        Some(&arch),
        &r2sym::FunctionSymbolSnapshot::default(),
        r2sym::SummaryProfile::Default,
    );
    let region = region_for_anchor(&artifact, 0x1004);
    assert_eq!(
        region.frontier,
        std::collections::BTreeSet::from([0x1008, 0x1010])
    );
    assert!(region.control.iter().any(|fact| {
        fact.value.target == 0x1010
            && fact.value.status == SymbolicReachabilityStatus::Reachable
            && fact.value.branch_truth == Some(true)
    }));
    assert!(region.control.iter().any(|fact| {
        fact.value.target == 0x1008
            && fact.value.status == SymbolicReachabilityStatus::Unreachable
            && fact.value.branch_truth == Some(false)
    }));
    assert_eq!(artifact.diagnostics.branches_pruned, 1);
}

#[test]
fn test_query_summarize_function_marks_budget_exhausted() {
    let blocks = make_conditional_branch_blocks();
    let func = SsaArtifact::for_symbolic(&blocks, None).expect("Failed to build SSA function");
    let ctx = Context::thread_local();

    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let query_config = SymQueryConfig {
        explore: ExploreConfig {
            max_states: 0,
            ..ExploreConfig::default()
        },
        ..SymQueryConfig::default()
    };
    let mut explorer = query_config.make_explorer(&ctx);
    let summary = explorer.summarize_function(&func, state);
    assert_eq!(summary.completion, QueryCompletion::BudgetExhausted);
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
        timeout: None,
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
        timeout: None,
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
        timeout: None,
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
fn run_spec_fd_read_flows_into_load_compare_and_solution() {
    let blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 8),
                    src: make_const(0x2000, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RDX, 8),
                    src: make_const(1, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x5000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 1),
                    addr: make_const(0x2000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 1),
                    b: make_const(b'k' as u64, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0x1337, 8),
            }],
        },
    ];

    let arch = make_x86_64_arch();
    let func =
        SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("Failed to build SSA function");
    let ctx = Context::thread_local();
    let mut initial_state = SymState::new(&ctx, 0x1000);
    let mut explorer = PathExplorer::new(&ctx);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    assert!(registry.install_for_explorer(&mut explorer, 0x5000, "read"));

    let spec = ExplorationSpec {
        find: vec![PredicateSpec::Address {
            addr: AddressValue::Integer(0x1010),
        }],
        inputs: vec![InputSpec::Fd {
            fd: 0,
            len: 1,
            name: Some("stdin0".to_string()),
            alphabet: Some("k".to_string()),
        }],
        ..Default::default()
    };
    spec.apply_to_state(&mut initial_state);

    let result = explorer
        .run_spec(&func, initial_state, &spec)
        .expect("spec exploration should succeed");
    assert_eq!(result.found_paths.len(), 1, "expected one matching path");

    let solved = explorer
        .solve_path(&result.found_paths[0])
        .expect("found path should solve");
    assert_eq!(solved.final_pc, 0x1010);
    assert_eq!(
        solved.input_buffers.get("stdin0"),
        Some(&vec![b'k']),
        "solver should recover the byte that drives the branch"
    );
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

#[test]
fn derived_helper_summary_solves_return_transform() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Call {
                target: make_const(0x2000, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::IntEqual {
                    dst: make_reg(TMP0, 1),
                    a: make_reg(RAX, 8),
                    b: make_const(0x6a, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP0, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntXor {
                dst: make_reg(RAX, 8),
                a: make_reg(RDI, 8),
                b: make_const(0x55, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_xor".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    r2sym::seed_default_state_for_arch(&mut state, &root, Some(&arch));
    state.make_symbolic_named("RDI_0", "rdi", 64);
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let solve = explorer.solve_for_target(&root, state, 0x1010);
    assert_eq!(solve.status, SolveStatus::Solved);
    let solution = solve.solution.expect("solution");
    assert_eq!(solution.inputs.get("rdi").copied(), Some(0x3f));
}

#[test]
fn derived_helper_summary_solves_transitive_return_chain() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Call {
                target: make_const(0x2000, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::IntEqual {
                    dst: make_reg(TMP0, 1),
                    a: make_reg(RAX, 8),
                    b: make_const(0x6a, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP0, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(1, 8),
            }],
        },
    ];
    let helper1_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Call {
                target: make_const(0x3000, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];
    let helper2_blocks = vec![R2ILBlock {
        addr: 0x3000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntXor {
                dst: make_reg(RAX, 8),
                a: make_reg(RDI, 8),
                b: make_const(0x55, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper1 =
        SsaArtifact::for_symbolic(&helper1_blocks, Some(&arch)).expect("helper1 symbolic function");
    let helper2 =
        SsaArtifact::for_symbolic(&helper2_blocks, Some(&arch)).expect("helper2 symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_wrapper".to_string()),
                prepared: helper1,
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x3000),
                name: Some("helper_xor".to_string()),
                prepared: helper2,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    r2sym::seed_default_state_for_arch(&mut state, &root, Some(&arch));
    state.make_symbolic_named("RDI_0", "rdi", 64);
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );
    let wrapper_return = derived
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .and_then(|summary| summary.cases.first())
        .and_then(|case| case.return_value.as_ref())
        .map(|value| value.to_bv(&ctx).to_string())
        .expect("wrapper return relation");
    assert!(wrapper_return.contains("helper_wrapper_arg0"));
    assert!(wrapper_return.contains("0055"));
    let diagnostics = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let solve = explorer.solve_for_target(&root, state, 0x1010);
    assert_eq!(solve.status, SolveStatus::Solved);
    assert_eq!(
        solve
            .compiled_precondition
            .as_ref()
            .map(|compiled| compiled.precision),
        Some(BackwardConditionPrecision::Exact)
    );
    let solution = solve.solution.expect("solution");
    assert_eq!(solution.inputs.get("rdi").copied(), Some(0x3f));
    assert_eq!(diagnostics.scc_count, 2);
    assert_eq!(diagnostics.max_scc_size, 1);
}

#[test]
fn derived_helper_summary_preserves_pointer_write_value() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x3000, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 1),
                    src: make_const(0x41, 1),
                },
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 1),
                    addr: make_const(0x3000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 1),
                    b: make_const(0x41, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Store {
                addr: make_reg(RDI, 8),
                val: make_reg(RSI, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_store".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let state = SymState::new(&ctx, 0x1000);
    let mut explorer = PathExplorer::new(&ctx);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let paths = explorer.find_paths_to(&root, state, 0x1010);
    assert_eq!(paths.len(), 1);
}

#[test]
fn derived_helper_summary_compiles_backward_memory_terms() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x3000, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 1),
                    src: make_const(0x41, 1),
                },
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 1),
                    addr: make_const(0x3000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 1),
                    b: make_const(0x41, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Store {
                addr: make_reg(RDI, 8),
                val: make_reg(RSI, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_store".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let state = SymState::new(&ctx, 0x1000);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );
    let static_summary = derived
        .interproc
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("static helper summary");
    assert!(
        static_summary.memory_effects.iter().any(|effect| {
            matches!(
                effect.location.region,
                r2ssa::SummaryMemoryRegion::Arg { index: 0 }
            ) && effect
                .location
                .range
                .is_some_and(|range| range.offset_lo == 0 && range.width.unwrap_or(0) >= 1)
        }),
        "expected static summary to record arg0 write, got {:?}",
        static_summary.memory_effects
    );
    let helper_summary = derived
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("derived helper summary");
    assert!(
        helper_summary.cases.iter().any(|case| {
            case.memory_writes
                .iter()
                .any(|write| write.arg_index == 0 && write.offset == 0 && write.size >= 1)
        }),
        "expected derived summary to record arg0 write, got {:?}",
        helper_summary
            .cases
            .iter()
            .flat_map(|case| case.memory_writes.iter().map(|write| (
                write.arg_index,
                write.offset,
                write.size
            )))
            .collect::<Vec<_>>()
    );
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert!(!compiled.memory_terms.is_empty());
    assert_argument_memory_term(&compiled.memory_terms[0], 0, 0, 0, true, 1);
}

#[test]
fn derived_helper_summary_compiles_backward_memory_terms_through_cast_pointer() {
    let arch = make_x86_64_arch();
    let cast_ptr = make_reg(0x90, 8);
    let loaded = make_reg(0x98, 1);
    let cond = make_reg(0xa0, 1);
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Cast {
                    dst: cast_ptr.clone(),
                    src: make_reg(RDI, 8),
                },
                R2ILOp::Load {
                    dst: loaded.clone(),
                    addr: cast_ptr,
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: cond.clone(),
                    a: loaded,
                    b: make_const(0x41, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond,
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.make_symbolic("reg:56_0", 64);

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_argument_memory_term(&compiled.memory_terms[0], 0, 0, 0, true, 1);
}

#[test]
fn derived_helper_summary_compiles_region_backed_global_memory_terms() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x2000, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 1),
                    src: make_const(0x41, 1),
                },
                R2ILOp::Call {
                    target: make_const(0x3000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 1),
                    addr: make_const(0x2000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 1),
                    b: make_const(0x41, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x3000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Store {
                addr: make_reg(RDI, 8),
                val: make_reg(RSI, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x3000),
                name: Some("helper_store".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.define_memory_region(
        r2sym::MemoryRegionKind::Global,
        "global_2000",
        Some(0x2000),
        Some(8),
    );
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_region_memory_term(
        &compiled.memory_terms[0],
        r2sym::MemoryRegionKind::Global,
        "global_2000",
        0,
        0,
        true,
        1,
    );
}

#[test]
fn derived_helper_summary_compiles_region_backed_stack_memory_terms() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x7008, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 1),
                    src: make_const(0x41, 1),
                },
                R2ILOp::Call {
                    target: make_const(0x3000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 1),
                    addr: make_const(0x7008, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 1),
                    b: make_const(0x41, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x3000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Store {
                addr: make_reg(RDI, 8),
                val: make_reg(RSI, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x3000),
                name: Some("helper_store".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.define_memory_region(
        r2sym::MemoryRegionKind::Stack,
        "stack_window",
        Some(0x7000),
        Some(0x100),
    );
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_region_memory_term(
        &compiled.memory_terms[0],
        r2sym::MemoryRegionKind::Stack,
        "stack_window",
        8,
        8,
        true,
        1,
    );
}

#[test]
fn derived_helper_summary_compiles_region_backed_replay_memory_terms() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x9004, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 1),
                    src: make_const(0x41, 1),
                },
                R2ILOp::Call {
                    target: make_const(0x3000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 1),
                    addr: make_const(0x9004, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 1),
                    b: make_const(0x41, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x3000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Store {
                addr: make_reg(RDI, 8),
                val: make_reg(RSI, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x3000),
                name: Some("helper_store".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.define_memory_region(
        r2sym::MemoryRegionKind::Replay,
        "replay_window",
        Some(0x9000),
        Some(0x100),
    );
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_region_memory_term(
        &compiled.memory_terms[0],
        r2sym::MemoryRegionKind::Replay,
        "replay_window",
        4,
        4,
        true,
        1,
    );
}

#[test]
fn derived_helper_summary_region_alias_falls_back_to_residual() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x2000, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 8),
                    src: make_const(0x2000, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x3000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 1),
                    addr: make_const(0x2000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 1),
                    b: make_const(0x42, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x3000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Store {
                addr: make_reg(RDI, 8),
                val: make_const(0x41, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Store {
                addr: make_reg(RSI, 8),
                val: make_const(0x42, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x3000),
                name: Some("helper_alias_store".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let mut state = SymState::new(&ctx, 0x1000);
    state.define_memory_region(
        r2sym::MemoryRegionKind::Global,
        "global_2000",
        Some(0x2000),
        Some(8),
    );
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(
        compiled.precision,
        BackwardConditionPrecision::ResidualSearchRequired
    );
    assert!(compiled.backward_memory_residual_fallbacks > 0);
    assert!(!compiled.memory_terms.is_empty());
    assert_region_memory_term(
        &compiled.memory_terms[0],
        r2sym::MemoryRegionKind::Global,
        "global_2000",
        0,
        0,
        true,
        1,
    );
}

#[test]
fn derived_helper_summary_coalesces_adjacent_byte_writes_into_slice() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x3000, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 2),
                    addr: make_const(0x3000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 2),
                    b: make_const(0x4241, 2),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Store {
                addr: make_reg(RDI, 8),
                val: make_const(0x41, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::IntAdd {
                dst: make_reg(TMP0, 8),
                a: make_reg(RDI, 8),
                b: make_const(1, 8),
            },
            R2ILOp::Store {
                addr: make_reg(TMP0, 8),
                val: make_const(0x42, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_store_pair".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let state = SymState::new(&ctx, 0x1000);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );
    let helper_summary = derived
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("derived helper summary");
    assert!(
        helper_summary.cases.iter().any(|case| {
            case.memory_writes
                .iter()
                .any(|write| write.arg_index == 0 && write.offset == 0 && write.size == 2)
        }),
        "expected derived summary to coalesce adjacent byte writes into one 2-byte slice, got {:?}",
        helper_summary
            .cases
            .iter()
            .flat_map(|case| case.memory_writes.iter().map(|write| (
                write.arg_index,
                write.offset,
                write.size
            )))
            .collect::<Vec<_>>()
    );

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_argument_memory_term(&compiled.memory_terms[0], 0, 0, 0, true, 2);
}

#[test]
fn derived_helper_summary_compiles_backward_memory_slice_at_offset() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x3000, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 8),
                    src: make_const(0x4142, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP1, 2),
                    addr: make_const(0x3002, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1),
                    a: make_reg(TMP1, 2),
                    b: make_const(0x4142, 2),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(RCX, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntAdd {
                dst: make_reg(TMP0, 8),
                a: make_reg(RDI, 8),
                b: make_const(2, 8),
            },
            R2ILOp::Store {
                addr: make_reg(TMP0, 8),
                val: make_reg(RSI, 2),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_store_offset".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let state = SymState::new(&ctx, 0x1000);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );
    let static_summary = derived
        .interproc
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("static helper summary");
    assert!(
        static_summary.memory_effects.iter().any(|effect| {
            matches!(
                effect.location.region,
                r2ssa::SummaryMemoryRegion::Arg { index: 0 }
            ) && effect
                .location
                .range
                .is_some_and(|range| range.offset_lo == 2 && range.width.unwrap_or(0) >= 2)
        }),
        "expected static summary to record arg0+2 write, got {:?}",
        static_summary.memory_effects
    );
    let helper_summary = derived
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("derived helper summary");
    assert!(
        helper_summary.cases.iter().any(|case| {
            case.memory_writes
                .iter()
                .any(|write| write.arg_index == 0 && write.offset == 2 && write.size >= 2)
        }),
        "expected derived summary to record arg0+2 write"
    );
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_argument_memory_term(&compiled.memory_terms[0], 0, 2, 2, true, 2);
}

#[test]
fn derived_helper_summary_compiles_backward_memory_slice_via_ptradd() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x3000, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 8),
                    src: make_const(0x4142, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP1, 2),
                    addr: make_const(0x3002, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1),
                    a: make_reg(TMP1, 2),
                    b: make_const(0x4142, 2),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(RCX, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::PtrAdd {
                dst: make_reg(TMP0, 8),
                base: make_reg(RDI, 8),
                index: make_const(1, 8),
                element_size: 2,
            },
            R2ILOp::Store {
                addr: make_reg(TMP0, 8),
                val: make_reg(RSI, 2),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_store_ptradd".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let state = SymState::new(&ctx, 0x1000);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );
    let helper_summary = derived
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("derived helper summary");
    assert!(
        helper_summary.cases.iter().any(|case| {
            case.memory_writes
                .iter()
                .any(|write| write.arg_index == 0 && write.offset == 2 && write.size >= 2)
        }),
        "expected derived summary to record arg0+2 write"
    );

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_argument_memory_term(&compiled.memory_terms[0], 0, 2, 2, true, 2);
}

#[test]
fn derived_helper_summary_preserves_negative_pointer_write_value() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x3001, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 1),
                    src: make_const(0x41, 1),
                },
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP0, 1),
                    addr: make_const(0x3000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(TMP1, 1),
                    a: make_reg(TMP0, 1),
                    b: make_const(0x41, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(TMP1, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntSub {
                dst: make_reg(TMP0, 8),
                a: make_reg(RDI, 8),
                b: make_const(1, 8),
            },
            R2ILOp::Store {
                addr: make_reg(TMP0, 8),
                val: make_reg(RSI, 1),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_store_prev".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let state = SymState::new(&ctx, 0x1000);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );
    let static_summary = derived
        .interproc
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("static helper summary");
    assert!(
        static_summary.memory_effects.iter().any(|effect| {
            matches!(
                effect.location.region,
                r2ssa::SummaryMemoryRegion::Arg { index: 0 }
            ) && effect
                .location
                .range
                .is_some_and(|range| range.offset_lo == -1 && range.width.unwrap_or(0) >= 1)
        }),
        "expected static summary to record arg0-1 write, got {:?}",
        static_summary.memory_effects
    );
    let helper_summary = derived
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("derived helper summary");
    assert!(
        helper_summary.cases.iter().any(|case| {
            case.memory_writes
                .iter()
                .any(|write| write.arg_index == 0 && write.offset == -1 && write.size >= 1)
        }),
        "expected derived summary to record arg0-1 write, got {:?}",
        helper_summary
            .cases
            .iter()
            .flat_map(|case| case.memory_writes.iter().map(|write| (
                write.arg_index,
                write.offset,
                write.size
            )))
            .collect::<Vec<_>>()
    );
    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_argument_memory_term(&compiled.memory_terms[0], 0, -1, -1, true, 1);

    let paths = explorer.find_paths_to(&root, SymState::new(&ctx, 0x1000), 0x1010);
    assert_eq!(paths.len(), 1);
}

#[test]
fn derived_helper_summary_compiles_backward_memory_slice_via_ptrsub() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RDI, 8),
                    src: make_const(0x3002, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(RSI, 8),
                    src: make_const(0x4142, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(TMP1, 2),
                    addr: make_const(0x3000, 8),
                    space: SpaceId::Ram,
                },
                R2ILOp::IntEqual {
                    dst: make_reg(RCX, 1),
                    a: make_reg(TMP1, 2),
                    b: make_const(0x4142, 2),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(RCX, 1),
                },
            ],
        },
        R2ILBlock {
            addr: 0x1008,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1010,
            size: 1,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::PtrSub {
                dst: make_reg(TMP0, 8),
                base: make_reg(RDI, 8),
                index: make_const(1, 8),
                element_size: 2,
            },
            R2ILOp::Store {
                addr: make_reg(TMP0, 8),
                val: make_reg(RSI, 2),
                space: SpaceId::Ram,
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_store_ptrsub".to_string()),
                prepared: helper,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let state = SymState::new(&ctx, 0x1000);
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );
    let helper_summary = derived
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("derived helper summary");
    assert!(
        helper_summary.cases.iter().any(|case| {
            case.memory_writes
                .iter()
                .any(|write| write.arg_index == 0 && write.offset == -2 && write.size >= 2)
        }),
        "expected derived summary to record arg0-2 write"
    );

    let mut explorer = SymQueryConfig::default().make_explorer(&ctx);
    let _ = registry.install_scope_summaries_for_explorer(
        &mut explorer,
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    let conditions = explorer.path_conditions_at(&root, state, 0x1010);
    let compiled = conditions
        .compiled_precondition
        .as_ref()
        .expect("compiled precondition");
    assert_eq!(compiled.precision, BackwardConditionPrecision::Exact);
    assert!(!compiled.memory_terms.is_empty());
    assert_argument_memory_term(&compiled.memory_terms[0], 0, -2, -2, true, 2);
}

#[test]
fn derived_helper_summary_compiles_backward_return_precondition() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![
        R2ILBlock {
            addr: 0x1000,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Call {
                target: make_const(0x2000, 8),
            }],
        },
        R2ILBlock {
            addr: 0x1004,
            size: 4,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
        },
    ];
    let helper_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::IntXor {
                dst: make_reg(RAX, 8),
                a: make_reg(RDI, 8),
                b: make_const(0x55, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];
    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper =
        SsaArtifact::for_symbolic(&helper_blocks, Some(&arch)).expect("helper symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root,
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_xor".to_string()),
                prepared: helper.clone(),
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );
    let summary = derived
        .summaries
        .get(&r2ssa::InterprocFunctionId(0x2000))
        .expect("derived summary");
    let mut state = SymState::new(&ctx, 0x2000);
    r2sym::seed_default_state_for_arch(&mut state, &helper, Some(&arch));
    state.make_symbolic_named("RDI_0", "rdi", 64);

    let compiled = compile_derived_summary_return_postcondition(
        &state,
        summary,
        &r2sym::CallConv::x86_64_sysv(),
        |ret| {
            ret.eq(&ctx, &SymValue::concrete(0x6a, 64))
                .to_bv(&ctx)
                .eq(z3::ast::BV::from_u64(1, 1))
        },
    )
    .expect("compiled backward precondition");

    assert_eq!(
        compiled.summary.precision,
        BackwardConditionPrecision::Exact
    );
    let solver = SymSolver::new(&ctx);
    assert_eq!(
        solver.sat_with_constraint(&state, &compiled.predicate),
        r2sym::SatResult::Sat
    );
}

#[test]
fn derived_helper_summary_reports_recursive_scc_diagnostics() {
    let arch = make_x86_64_arch();
    let root_blocks = vec![R2ILBlock {
        addr: 0x1000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Call {
                target: make_const(0x2000, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];
    let helper_a_blocks = vec![R2ILBlock {
        addr: 0x2000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Call {
                target: make_const(0x3000, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];
    let helper_b_blocks = vec![R2ILBlock {
        addr: 0x3000,
        size: 1,
        switch_info: None,
        op_metadata: Default::default(),
        ops: vec![
            R2ILOp::Call {
                target: make_const(0x2000, 8),
            },
            R2ILOp::Return {
                target: make_const(0, 8),
            },
        ],
    }];

    let root =
        SsaArtifact::for_symbolic(&root_blocks, Some(&arch)).expect("root symbolic function");
    let helper_a = SsaArtifact::for_symbolic(&helper_a_blocks, Some(&arch))
        .expect("helper_a symbolic function");
    let helper_b = SsaArtifact::for_symbolic(&helper_b_blocks, Some(&arch))
        .expect("helper_b symbolic function");
    let scope = r2sym::PreparedFunctionScope::new(
        0x1000,
        vec![
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root,
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x2000),
                name: Some("helper_a".to_string()),
                prepared: helper_a,
            },
            r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x3000),
                name: Some("helper_b".to_string()),
                prepared: helper_b,
            },
        ],
    )
    .expect("scope");

    let ctx = Context::thread_local();
    let registry = SummaryRegistry::with_core(r2sym::CallConv::x86_64_sysv());
    let derived = registry.derive_symbolic_summaries(
        &ctx,
        &scope,
        Some(&arch),
        &std::collections::HashMap::new(),
    );

    assert_eq!(derived.diagnostics.scc_count, 1);
    assert_eq!(derived.diagnostics.max_scc_size, 2);
    assert_eq!(
        derived.diagnostics.scc_converged + derived.diagnostics.scc_budget_exhausted,
        1
    );
    assert!(
        derived
            .summaries
            .contains_key(&r2ssa::InterprocFunctionId(0x2000))
    );
    assert!(
        derived
            .summaries
            .contains_key(&r2ssa::InterprocFunctionId(0x3000))
    );
}
