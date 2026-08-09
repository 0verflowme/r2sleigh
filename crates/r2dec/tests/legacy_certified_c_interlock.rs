use r2dec::{CStmt, Decompiler, DecompilerConfig, DecompilerContext, DecompilerInput};
use r2il::{R2ILBlock, R2ILOp, Varnode};
use r2ssa::{CFGRiskSummary, SsaArtifact};
use r2sym::{ProofCoverage, ProofOwner, RenderPermission};
use r2types::{DecompileRouteFacts, DecompileRouteKind, FunctionFacts, FunctionTypeFacts};

fn prepared_return_fixture() -> SsaArtifact {
    let mut block = R2ILBlock::new(0x1000, 4);
    block.push(R2ILOp::Return {
        target: Varnode::constant(7, 8),
    });
    SsaArtifact::for_decompile(&[block], None).expect("prepared return fixture")
}

fn standard_input(permission: RenderPermission, coverage: ProofCoverage) -> DecompilerInput {
    let route = DecompileRouteFacts {
        kind: DecompileRouteKind::Standard,
        reason: Some("legacy authorization fixture".to_string()),
        fallback_comment: None,
        skip_runtime_type_inference: false,
        use_prepared_semantic_view: true,
        proof_coverage: coverage,
        render_permission: permission,
    };
    let facts = FunctionFacts::new(FunctionTypeFacts::default(), None).with_decompile_route(route);
    DecompilerInput::new(
        prepared_return_fixture(),
        DecompilerContext::from_function_facts(facts),
    )
}

fn contains_return(statement: &CStmt) -> bool {
    match statement {
        CStmt::Return(_) => true,
        CStmt::Block(statements) => statements.iter().any(contains_return),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => contains_return(then_body) || else_body.as_deref().is_some_and(contains_return),
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } | CStmt::For { body, .. } => {
            contains_return(body)
        }
        CStmt::Switch { cases, default, .. } => {
            cases
                .iter()
                .flat_map(|case| &case.body)
                .any(contains_return)
                || default.iter().flatten().any(contains_return)
        }
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => false,
    }
}

fn assert_legacy_permission_is_inert(input: DecompilerInput) {
    let decompiler = Decompiler::new(DecompilerConfig::x86_64());
    let output = decompiler.decompile_input(&input);
    assert!(
        output.contains("legacy CertifiedC claims cannot authorize production output"),
        "legacy permission must residualize explicitly, got:\n{output}"
    );
    assert!(!output.contains("return 7;"), "got:\n{output}");

    let function = decompiler.build_function_from_input(&input);
    assert!(
        function
            .body
            .iter()
            .all(|statement| !contains_return(statement))
    );
}

#[test]
fn direct_legacy_certified_permission_cannot_authorize_production_c() {
    assert_legacy_permission_is_inert(standard_input(
        RenderPermission::certified(ProofOwner::R2engine, "legacy direct claim"),
        ProofCoverage::default(),
    ));
}

#[test]
fn counter_derived_legacy_certified_permission_cannot_authorize_production_c() {
    let coverage = ProofCoverage {
        certified_signatures: 1,
        certified_returns: 1,
        ..ProofCoverage::default()
    };
    let permission = coverage.standard_control_render_permission(
        &CFGRiskSummary {
            block_count: 1,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        },
        true,
    );
    assert_legacy_permission_is_inert(standard_input(permission, coverage));
}
