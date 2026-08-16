use r2engine::{EngineFunctionDecompileRequestInput, EngineFunctionInput, EngineSession};
use r2il::{R2ILBlock, R2ILOp, Varnode};

#[test]
fn detached_production_input_refuses_before_source_owned_certified_c() {
    let mut block = R2ILBlock::new(0x401000, 4);
    block.push(R2ILOp::Return {
        target: Varnode::constant(0, 8),
    });
    let response = EngineSession::new().decompile_function_from_input(
        EngineFunctionDecompileRequestInput::single_function(
            EngineFunctionInput {
                function_name: "legacy_route_interlock".to_string(),
                function_addr: 0x401000,
                blocks: vec![block],
                arch: None,
                semantic_metadata_enabled: false,
                source_snapshot: None,
            },
            Some(64),
            r2types::ParsedExternalContext::default(),
        ),
    );
    let route = response
        .function_facts
        .decompile_route()
        .expect("engine response route");
    assert_eq!(route.kind, r2types::DecompileRouteKind::FallbackComment);
    assert!(
        route
            .reason
            .as_deref()
            .unwrap_or_default()
            .contains("engine analysis requires an immutable source snapshot")
    );
    assert!(response.output.contains("r2dec fallback:"));
    assert!(!response.output.contains("legacy_route_interlock(void)"));
}
