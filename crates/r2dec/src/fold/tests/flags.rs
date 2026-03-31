use super::*;
use crate::fold::FoldingContext;
use crate::fold::context::{FoldArchConfig, FoldInputs};
use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
use r2types::{
    SymbolicBranchFact, SymbolicCompiledCondition, SymbolicConditionPrecision, SymbolicControlFact,
    SymbolicControlIsland, SymbolicControlIslandKind, SymbolicReachabilityStatus,
    SymbolicSemanticFacts,
};
use std::collections::{BTreeMap, HashMap, HashSet};

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
    let empty_fn = Box::leak(Box::new(HashMap::new()));
    let empty_callee = Box::leak(Box::new(BTreeMap::new()));
    let empty_ty = Box::leak(Box::new(HashMap::new()));

    let mut ctx = FoldingContext::from_inputs(FoldInputs {
        arch,
        function_names: empty_u64,
        strings: empty_u64,
        symbols: empty_u64,
        known_function_signatures: empty_fn,
        callee_facts: empty_callee,
        stack_slots: empty_stack_slots,
        external_stack_vars: empty_stack,
        visible_bindings: empty_visible,
        external_type_db: Box::leak(Box::new(r2types::ExternalTypeDb::default())),
        symbolic_facts: Box::leak(Box::new(r2types::SymbolicSemanticFacts::default())),
        param_register_aliases: empty_str,
        type_hints: empty_ty,
        type_oracle: None,
        function_return_type: None,
        prepared_ssa: None,
        interproc_summary_set: None,
        prepared_semantic_view: None,
        prepared_objects: None,
        prepared_memory: None,
        prepared_predicates: None,
        prepared_call_sites: None,
    });
    ctx.inputs.prepared_ssa = Some(prepared_ssa);
    ctx
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

    let clean = CExpr::binary(
        BinaryOp::Eq,
        CExpr::Var("eax_1".to_string()),
        CExpr::IntLit(0),
    );
    assert!(!ctx.expr_contains_opaque_temp(&clean));
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
    let mut facts = SymbolicSemanticFacts::default();
    facts.branch_facts.push(SymbolicBranchFact {
        block_addr: 0x1000,
        true_target: 0x1008,
        false_target: 0x1004,
        true_status: SymbolicReachabilityStatus::Unreachable,
        false_status: SymbolicReachabilityStatus::Reachable,
        true_condition: None,
        false_condition: Some("false".to_string()),
        true_compiled: None,
        false_compiled: Some(SymbolicCompiledCondition {
            simplified: "false".to_string(),
            terms: vec!["false".to_string()],
            memory_terms: vec![],
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: SymbolicConditionPrecision::Exact,
            evidence: r2types::SymbolicSemanticEvidence::exact(),
            confidence: r2types::SymbolicSemanticConfidence::Exact,
            supported_paths: 1,
            total_paths: 1,
        }),
    });
    ctx.inputs.symbolic_facts = Box::leak(Box::new(facts));

    let entry = prepared.function().get_block(0x1000).expect("entry");
    assert_eq!(
        ctx.symbolic_actionable_compiled_condition_expr(entry.addr),
        Some(CExpr::IntLit(0))
    );
    assert_eq!(
        ctx.extract_condition_from_block(entry),
        Some(CExpr::IntLit(0))
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
    let mut facts = SymbolicSemanticFacts::default();
    facts.branch_facts.push(SymbolicBranchFact {
        block_addr: 0x2000,
        true_target: 0x2008,
        false_target: 0x2004,
        true_status: SymbolicReachabilityStatus::Unknown,
        false_status: SymbolicReachabilityStatus::Unknown,
        true_condition: Some("false".to_string()),
        false_condition: None,
        true_compiled: Some(SymbolicCompiledCondition {
            simplified: "false".to_string(),
            terms: vec!["false".to_string()],
            memory_terms: vec![],
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: SymbolicConditionPrecision::OverApprox,
            evidence: r2types::SymbolicSemanticEvidence::likely(
                r2types::SymbolicSemanticEvidenceReason::PartialPathCoverage,
            ),
            confidence: r2types::SymbolicSemanticConfidence::Likely,
            supported_paths: 1,
            total_paths: 2,
        }),
        false_compiled: None,
    });
    facts.control_islands.push(SymbolicControlIsland {
        kind: SymbolicControlIslandKind::LargeCfgBranchFrontier,
        anchor_block: 0x2000,
        frontier_targets: vec![0x2008, 0x2004],
        facts: vec![
            SymbolicControlFact {
                target: 0x2008,
                status: SymbolicReachabilityStatus::Unknown,
                condition: Some("false".to_string()),
                compiled: facts.branch_facts[0].true_compiled.clone(),
                evidence: r2types::SymbolicSemanticEvidence::likely(
                    r2types::SymbolicSemanticEvidenceReason::PartialPathCoverage,
                ),
                confidence: r2types::SymbolicSemanticConfidence::Likely,
            },
            SymbolicControlFact {
                target: 0x2004,
                status: SymbolicReachabilityStatus::Unknown,
                condition: None,
                compiled: None,
                evidence: r2types::SymbolicSemanticEvidence::residual(
                    r2types::SymbolicSemanticEvidenceReason::GuardOpaque,
                ),
                confidence: r2types::SymbolicSemanticConfidence::Residual,
            },
        ],
        evidence: r2types::SymbolicSemanticEvidence::likely(
            r2types::SymbolicSemanticEvidenceReason::PartialPathCoverage,
        ),
        confidence: r2types::SymbolicSemanticConfidence::Likely,
    });
    ctx.inputs.symbolic_facts = Box::leak(Box::new(facts));

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
    let mut facts = SymbolicSemanticFacts::default();
    facts.control_islands.push(SymbolicControlIsland {
        kind: SymbolicControlIslandKind::LargeCfgBranchFrontier,
        anchor_block: 0x3000,
        frontier_targets: vec![0x3008],
        facts: vec![SymbolicControlFact {
            target: 0x3008,
            status: SymbolicReachabilityStatus::Reachable,
            condition: Some("x == 0".to_string()),
            compiled: Some(SymbolicCompiledCondition {
                simplified: "x == 0".to_string(),
                terms: vec!["x == 0".to_string()],
                memory_terms: vec![],
                backward_memory_substitutions: 0,
                backward_memory_candidate_enumerations: 0,
                backward_memory_residual_fallbacks: 0,
                precision: SymbolicConditionPrecision::Exact,
                evidence: r2types::SymbolicSemanticEvidence::exact(),
                confidence: r2types::SymbolicSemanticConfidence::Exact,
                supported_paths: 1,
                total_paths: 1,
            }),
            evidence: r2types::SymbolicSemanticEvidence::exact(),
            confidence: r2types::SymbolicSemanticConfidence::Exact,
        }],
        evidence: r2types::SymbolicSemanticEvidence::exact(),
        confidence: r2types::SymbolicSemanticConfidence::Exact,
    });
    ctx.inputs.symbolic_facts = Box::leak(Box::new(facts));

    assert_eq!(
        ctx.symbolic_actionable_compiled_condition_expr(0x3000),
        Some(CExpr::binary(
            BinaryOp::Eq,
            CExpr::Var("x".to_string()),
            CExpr::IntLit(0),
        ))
    );
}
