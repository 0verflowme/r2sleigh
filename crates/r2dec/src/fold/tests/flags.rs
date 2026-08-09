use super::*;
use crate::fold::FoldingContext;
use crate::fold::context::{FoldArchConfig, FoldInputs, empty_function_facts};
use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

fn make_test_arch_x86_64() -> ArchSpec {
    let mut arch = ArchSpec::new("x86-64");
    arch.add_register(RegisterDef::new("RAX", 0x00, 8));
    arch.add_register(RegisterDef::new("RDI", 0x10, 8));
    arch.add_register(RegisterDef::new("RSI", 0x18, 8));
    arch.add_register(RegisterDef::new("RBP", 0x20, 8));
    arch.add_register(RegisterDef::new("RSP", 0x28, 8));
    arch
}

fn prepared_from_r2il_blocks(blocks: &[R2ILBlock], arch: &ArchSpec) -> r2ssa::SsaArtifact {
    r2ssa::SsaArtifact::for_decompile(blocks, Some(arch)).expect("prepared SSA should build")
}

fn make_x86_64_ctx_with_prepared<'a>(prepared_ssa: &'a r2ssa::SsaArtifact) -> FoldingContext<'a> {
    let arch = Box::leak(Box::new(FoldArchConfig {
        ptr_size: 64,
        sp_name: "rsp".to_string(),
        fp_name: "rbp".to_string(),
        ret_reg_name: "rax".to_string(),
        arg_regs: vec![
            "rdi".to_string(),
            "rsi".to_string(),
            "rdx".to_string(),
            "rcx".to_string(),
            "r8".to_string(),
            "r9".to_string(),
        ],
        caller_saved_regs: HashSet::new(),
    }));
    let empty_u64 = Box::leak(Box::new(HashMap::new()));
    let empty_stack = Box::leak(Box::new(HashMap::new()));
    let empty_stack_slots = Box::leak(Box::new(BTreeMap::new()));
    let empty_visible = Box::leak(Box::new(Vec::new()));
    let empty_str = Box::leak(Box::new(HashMap::new()));
    let empty_ty = Box::leak(Box::new(HashMap::new()));

    let mut ctx = FoldingContext::from_inputs(FoldInputs {
        arch,
        function_names: empty_u64,
        strings: empty_u64,
        symbols: empty_u64,
        function_facts: empty_function_facts(),
        certified_rendering_required: false,
        stack_slots: empty_stack_slots,
        field_access_certificates: &[],
        external_stack_vars: empty_stack,
        visible_bindings: empty_visible,
        external_type_db: Box::leak(Box::new(r2types::ExternalTypeDb::default())),
        param_register_aliases: empty_str,
        type_hints: empty_ty,
        type_oracle: None,
        function_return_type: None,
        prepared_ssa: None,
        prepared_semantic_view: None,
        prepared_objects: None,
        prepared_memory: None,
    });
    ctx.inputs.prepared_ssa = Some(prepared_ssa);
    ctx
}

fn install_semantic_artifact(ctx: &mut FoldingContext<'_>, artifact: r2sym::SemanticArtifact) {
    let mut function_facts = ctx.inputs.function_facts.clone();
    function_facts.set_semantics(Some(artifact));
    ctx.inputs.function_facts = Box::leak(Box::new(function_facts));
}

fn install_typed_rendering_for_test(ctx: &mut FoldingContext<'_>) {
    let mut function_facts = ctx.inputs.function_facts.clone();
    function_facts = function_facts.with_decompile_route(r2types::DecompileRouteFacts {
        kind: r2types::DecompileRouteKind::Standard,
        reason: Some("test typed rendering".to_string()),
        fallback_comment: None,
        skip_runtime_type_inference: true,
        use_prepared_semantic_view: true,
        proof_coverage: r2sym::ProofCoverage::default(),
        render_permission: r2sym::RenderPermission::residual(
            r2sym::ProofOwner::R2engine,
            "test typed rendering",
        ),
    });
    ctx.inputs.function_facts = Box::leak(Box::new(function_facts));
    ctx.inputs.certified_rendering_required = true;
}

fn install_call_owner(
    ctx: &mut FoldingContext<'_>,
    source_call: (u64, usize),
    owner_name: &str,
    alias: &str,
) {
    let source_id = analysis::CallSiteId::from(source_call);
    ctx.state.analysis_ctx.ownership.call_ownership.insert(
        source_id,
        analysis::CallOwnershipFact {
            source: source_id,
            owner: Some(analysis::CallOwner {
                visible_name: owner_name.to_string(),
                kind: analysis::CallOwnerKind::StableLocal,
            }),
            aliases: BTreeSet::from([alias.to_string()]),
            direct_aliases: BTreeSet::from([alias.to_string()]),
        },
    );
    ctx.state
        .analysis_ctx
        .ownership
        .alias_sources
        .insert(alias.to_string(), source_id);
    ctx.state
        .analysis_ctx
        .use_info
        .call_result_source_by_alias
        .insert(alias.to_string(), source_call);
}

fn wrap_parens(mut expr: CExpr, count: usize) -> CExpr {
    for _ in 0..count {
        expr = CExpr::Paren(Box::new(expr));
    }
    expr
}

#[test]
fn expr_contains_opaque_temp_uses_visit_over_nested_nodes() {
    let ctx = FoldingContext::new(64);

    let nested = CExpr::binary(
        BinaryOp::And,
        CExpr::Var("zf_1".to_string()),
        CExpr::Paren(Box::new(CExpr::Var("var_12".to_string()))),
    );
    assert!(ctx.expr_contains_opaque_temp(&nested));

    let sleigh_tmp = CExpr::Var("tmp_ldxn_1".to_string());
    assert!(ctx.expr_contains_opaque_temp(&sleigh_tmp));

    let raw_tmp = CExpr::Var("tmp:2a000".to_string());
    assert!(ctx.expr_contains_opaque_temp(&raw_tmp));

    let upper_raw_tmp = CExpr::Var("TMP:2a000".to_string());
    assert!(ctx.expr_contains_opaque_temp(&upper_raw_tmp));

    let clean = CExpr::binary(
        BinaryOp::Eq,
        CExpr::Var("eax_1".to_string()),
        CExpr::IntLit(0),
    );
    assert!(!ctx.expr_contains_opaque_temp(&clean));
}

#[test]
fn call_result_predicate_owner_rewrite_depth_guard_is_inclusive() {
    let mut ctx = FoldingContext::new(64);
    install_call_owner(&mut ctx, (0x1000, 2), "loc", "rax_1");

    let at_max = wrap_parens(
        CExpr::Var("rax_1".to_string()),
        MAX_PREDICATE_OPERAND_DEPTH as usize,
    );
    assert_eq!(
        ctx.rewrite_call_result_predicate_owners(at_max, 0),
        wrap_parens(
            CExpr::Var("loc".to_string()),
            MAX_PREDICATE_OPERAND_DEPTH as usize,
        ),
        "owner aliases at exactly MAX_PREDICATE_OPERAND_DEPTH must still rewrite"
    );

    let beyond_max = wrap_parens(
        CExpr::Var("rax_1".to_string()),
        MAX_PREDICATE_OPERAND_DEPTH as usize + 1,
    );
    assert_eq!(
        ctx.rewrite_call_result_predicate_owners(beyond_max.clone(), 0),
        beyond_max,
        "owner aliases beyond MAX_PREDICATE_OPERAND_DEPTH must be left untouched"
    );
}

#[test]
fn expr_contains_unresolved_memory_uses_visit_over_nested_nodes() {
    let ctx = FoldingContext::new(64);

    let deref_nested = CExpr::binary(
        BinaryOp::Or,
        CExpr::Var("zf_1".to_string()),
        CExpr::Paren(Box::new(CExpr::Deref(Box::new(CExpr::Var(
            "tmp:20_1".to_string(),
        ))))),
    );
    assert!(ctx.expr_contains_unresolved_memory(&deref_nested));

    let no_deref = CExpr::binary(
        BinaryOp::Ne,
        CExpr::Var("x_1".to_string()),
        CExpr::Var("y_1".to_string()),
    );
    assert!(!ctx.expr_contains_unresolved_memory(&no_deref));
}

#[test]
fn tmp_flag_aliases_reconstruct_signed_ge_condition() {
    let mut ctx = FoldingContext::new(64);
    ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
        "tmpng_1".to_string(),
        analysis::FlagCompareProvenance {
            lhs: "argc".to_string(),
            rhs: "2".to_string(),
            kind: analysis::FlagCompareKind::SignedNegative,
        },
    );
    ctx.state.analysis_ctx.flag_info.compare_provenance.insert(
        "tmpov_1".to_string(),
        analysis::FlagCompareProvenance {
            lhs: "argc".to_string(),
            rhs: "2".to_string(),
            kind: analysis::FlagCompareKind::Overflow,
        },
    );

    let expr = CExpr::binary(
        BinaryOp::Eq,
        CExpr::Var("tmpng_1".to_string()),
        CExpr::Var("tmpov_1".to_string()),
    );

    assert_eq!(
        ctx.simplify_condition_expr(expr),
        CExpr::binary(
            BinaryOp::Ge,
            CExpr::Var("argc".to_string()),
            CExpr::IntLit(2),
        )
    );
}

#[test]
fn symbolic_condition_parser_accepts_boolean_and_deref_terms() {
    let ctx = FoldingContext::new(64);

    assert_eq!(
        super::SymbolicConditionExprParser::new(&ctx, "false")
            .and_then(super::SymbolicConditionExprParser::parse),
        Some(CExpr::IntLit(0))
    );
    assert_eq!(
        super::SymbolicConditionExprParser::new(&ctx, "*(arg0 + 0x8) == 0x2a")
            .and_then(super::SymbolicConditionExprParser::parse),
        Some(CExpr::binary(
            BinaryOp::Eq,
            CExpr::deref(CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("arg0".to_string()),
                CExpr::IntLit(0x8),
            )),
            CExpr::IntLit(0x2a),
        ))
    );
}

#[test]
fn exact_compiled_condition_shortcuts_to_literal_condition() {
    let arch = make_test_arch_x86_64();
    let mut entry = R2ILBlock::new(0x1000, 4);
    entry.push(R2ILOp::IntNotEqual {
        dst: Varnode::unique(1, 1),
        a: Varnode::register(0x10, 4),
        b: Varnode::constant(0, 4),
    });
    entry.push(R2ILOp::CBranch {
        target: Varnode::constant(0x1008, 8),
        cond: Varnode::unique(1, 1),
    });
    let mut fallthrough = R2ILBlock::new(0x1004, 4);
    fallthrough.push(R2ILOp::Return {
        target: Varnode::constant(0, 8),
    });
    let mut taken = R2ILBlock::new(0x1008, 4);
    taken.push(R2ILOp::Return {
        target: Varnode::constant(1, 8),
    });

    let prepared =
        prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch).with_name("exact_compiled");
    let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
    let region = crate::test_semantic_region(
        0x1000,
        std::collections::BTreeSet::from([0x1004, 0x1008]),
        vec![crate::test_control_fact(
            0x1004,
            r2sym::SymbolicReachabilityStatus::Reachable,
            Some(false),
            Some("false"),
            Some(r2sym::BackwardConditionSummary {
                simplified: "false".to_string(),
                terms: vec!["false".to_string()],
                memory_terms: Vec::new(),
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 0,
                precision: r2sym::BackwardConditionPrecision::Exact,
                supported_paths: 1,
                total_paths: 1,
            }),
            r2sym::SemanticEvidence::exact(),
        )],
        Vec::new(),
    );
    let artifact = crate::test_native_semantic_artifact(
        r2sym::RefinementStage::Compiled,
        r2sym::ArtifactGranularity::WholeFunction,
        r2sym::SliceClass::Worker,
        false,
        Vec::new(),
        vec![region],
    );
    assert!(
        artifact
            .actionable_compiled_condition_for_block(0x1000)
            .is_some(),
        "test artifact should carry an actionable compiled condition at the branch anchor"
    );
    install_semantic_artifact(&mut ctx, artifact);

    let entry = prepared.function().get_block(0x1000).expect("entry");
    assert_eq!(
        ctx.symbolic_actionable_compiled_condition_expr(entry.addr),
        Some(CExpr::IntLit(0))
    );
    assert_eq!(
        ctx.extract_condition_from_block(entry),
        None,
        "prepared branch rendering must require FunctionFacts control evidence instead of summary-only compiled conditions"
    );
}

#[test]
fn actionable_control_island_shortcuts_when_branch_fact_is_not_decisive() {
    let arch = make_test_arch_x86_64();
    let mut entry = R2ILBlock::new(0x2000, 4);
    entry.push(R2ILOp::IntNotEqual {
        dst: Varnode::unique(1, 1),
        a: Varnode::register(0x10, 4),
        b: Varnode::constant(0, 4),
    });
    entry.push(R2ILOp::CBranch {
        target: Varnode::constant(0x2008, 8),
        cond: Varnode::unique(1, 1),
    });
    let mut fallthrough = R2ILBlock::new(0x2004, 4);
    fallthrough.push(R2ILOp::Return {
        target: Varnode::constant(0, 8),
    });
    let mut taken = R2ILBlock::new(0x2008, 4);
    taken.push(R2ILOp::Return {
        target: Varnode::constant(1, 8),
    });

    let prepared =
        prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch).with_name("control_island");
    let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
    let frontier = std::collections::BTreeSet::from([0x2004, 0x2008]);
    let region = r2sym::SemanticRegion {
        anchor: 0x2000,
        frontier: frontier.clone(),
        control: vec![r2sym::Judged::new(
            r2sym::ControlFact {
                target: 0x2008,
                status: r2sym::SymbolicReachabilityStatus::Unknown,
                branch_truth: Some(true),
                condition: Some("false".to_string()),
                compiled: Some(r2sym::BackwardConditionSummary {
                    simplified: "false".to_string(),
                    terms: vec!["false".to_string()],
                    memory_terms: Vec::new(),
                    backward_memory_substitutions: 0,
                    backward_memory_candidate_enumerations: 0,
                    backward_memory_residual_fallbacks: 0,
                    precision: r2sym::BackwardConditionPrecision::Exact,
                    supported_paths: 1,
                    total_paths: 1,
                }),
            },
            r2sym::SemanticEvidence::exact(),
        )],
        memory: Vec::new(),
        pre: Vec::new(),
        post: Vec::new(),
        targets: Vec::new(),
    };
    let artifact = r2sym::SemanticArtifact {
        stage: r2sym::RefinementStage::Compiled,
        granularity: r2sym::ArtifactGranularity::Regioned,
        execution: r2sym::ExecutionModel::Native,
        body: r2sym::SemanticArtifactBody::Native(r2sym::NativeArtifactBody {
            summary: r2sym::NativeFunctionSummary {
                slice_class: r2sym::SliceClass::Worker,
                role_identity: None,
                closure_functions: 1,
                helper_functions: 0,
                derived_summaries: 0,
                derived_diagnostics: Default::default(),
                region_summaries: Vec::new(),
                worker_summaries: Vec::new(),
            },
            regions: std::collections::BTreeMap::from([(region.key(), region)]),
        }),
        diagnostics: r2sym::SemanticArtifactDiagnostics {
            branches_evaluated: 0,
            branches_pruned: 0,
            branches_unknown: 0,
            skipped_missing_arch: false,
            skipped_large_cfg: false,
            residual_reasons: Vec::new(),
            interpreter: None,
            ambiguous_targets: Vec::new(),
            cache_hit: false,
        },
    };
    install_semantic_artifact(&mut ctx, artifact);

    let entry = prepared.function().get_block(0x2000).expect("entry");
    assert_eq!(
        ctx.symbolic_actionable_compiled_condition_expr(entry.addr),
        Some(CExpr::IntLit(0))
    );
}

#[test]
fn actionable_control_island_parses_non_literal_compiled_condition_expr() {
    let arch = make_test_arch_x86_64();
    let mut entry = R2ILBlock::new(0x3000, 4);
    entry.push(R2ILOp::IntNotEqual {
        dst: Varnode::unique(1, 1),
        a: Varnode::register(0x10, 4),
        b: Varnode::constant(0, 4),
    });
    entry.push(R2ILOp::CBranch {
        target: Varnode::constant(0x3008, 8),
        cond: Varnode::unique(1, 1),
    });
    let mut fallthrough = R2ILBlock::new(0x3004, 4);
    fallthrough.push(R2ILOp::Return {
        target: Varnode::constant(0, 8),
    });
    let mut taken = R2ILBlock::new(0x3008, 4);
    taken.push(R2ILOp::Return {
        target: Varnode::constant(1, 8),
    });

    let prepared = prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch)
        .with_name("parsed_control_island");
    let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
    let region = crate::test_semantic_region(
        0x3000,
        std::collections::BTreeSet::from([0x3008]),
        vec![crate::test_control_fact(
            0x3008,
            r2sym::SymbolicReachabilityStatus::Reachable,
            None,
            Some("x == 0"),
            Some(r2sym::BackwardConditionSummary {
                simplified: "x == 0".to_string(),
                terms: vec!["x == 0".to_string()],
                memory_terms: Vec::new(),
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 0,
                precision: r2sym::BackwardConditionPrecision::Exact,
                supported_paths: 1,
                total_paths: 1,
            }),
            r2sym::SemanticEvidence::exact(),
        )],
        Vec::new(),
    );
    install_semantic_artifact(
        &mut ctx,
        crate::test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::Regioned,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            vec![region],
        ),
    );

    assert_eq!(
        ctx.symbolic_actionable_compiled_condition_expr(0x3000),
        Some(CExpr::binary(
            BinaryOp::Eq,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(0),
        ))
    );
}

#[test]
fn actionable_memory_island_parses_memory_condition_expr() {
    let arch = make_test_arch_x86_64();
    let mut entry = R2ILBlock::new(0x4000, 4);
    entry.push(R2ILOp::IntNotEqual {
        dst: Varnode::unique(1, 1),
        a: Varnode::register(0x10, 4),
        b: Varnode::constant(0, 4),
    });
    entry.push(R2ILOp::CBranch {
        target: Varnode::constant(0x4008, 8),
        cond: Varnode::unique(1, 1),
    });
    let mut fallthrough = R2ILBlock::new(0x4004, 4);
    fallthrough.push(R2ILOp::Return {
        target: Varnode::constant(0, 8),
    });
    let mut taken = R2ILBlock::new(0x4008, 4);
    taken.push(R2ILOp::Return {
        target: Varnode::constant(1, 8),
    });

    let prepared =
        prepared_from_r2il_blocks(&[entry, fallthrough, taken], &arch).with_name("memory_island");
    let mut ctx = make_x86_64_ctx_with_prepared(&prepared);
    install_typed_rendering_for_test(&mut ctx);
    let region = crate::test_semantic_region(
        0x4000,
        std::collections::BTreeSet::new(),
        Vec::new(),
        vec![crate::test_memory_fact(
            r2sym::BackwardMemoryCondition {
                region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
                address: r2sym::SemanticMemoryAddress::exact(8),
                size: 4,
                evidence: r2sym::SemanticEvidence::exact(),
                binding: None,
                expr: "*(arg0 + 0x8)".to_string(),
                value_expr: Some("0x2a".to_string()),
                exact_value: true,
            },
            r2sym::SemanticEvidence::exact(),
        )],
    );
    let artifact = crate::test_native_semantic_artifact(
        r2sym::RefinementStage::Residual,
        r2sym::ArtifactGranularity::Regioned,
        r2sym::SliceClass::Worker,
        true,
        vec![r2sym::ResidualReason::LargeCfg],
        vec![region],
    );
    assert!(
        !artifact
            .actionable_memory_terms_for_block(0x4000)
            .is_empty(),
        "test artifact should carry actionable memory terms at the branch anchor"
    );
    install_semantic_artifact(&mut ctx, artifact);

    let expected = CExpr::binary(
        BinaryOp::Eq,
        CExpr::deref(CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("arg0".to_string()),
            CExpr::IntLit(0x8),
        )),
        CExpr::IntLit(0x2a),
    );
    assert_eq!(
        ctx.symbolic_actionable_memory_condition_expr(0x4000),
        Some(expected)
    );
    assert_eq!(
        ctx.extract_condition_from_block(prepared.function().get_block(0x4000).expect("entry")),
        None,
        "prepared branch rendering must require FunctionFacts control evidence instead of summary-only memory conditions"
    );
}
