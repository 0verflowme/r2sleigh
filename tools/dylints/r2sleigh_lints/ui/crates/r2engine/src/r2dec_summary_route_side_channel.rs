struct FunctionFacts;
struct DecompilerConfig;
struct EngineRenderTarget;
struct SemanticRoutePlan;

enum EngineSemanticRoutePlan {
    LinearWorker,
    VmSummary,
}

impl EngineSemanticRoutePlan {
    fn to_decompiler_route(&self) -> SemanticRoutePlan {
        SemanticRoutePlan
    }
}

impl EngineRenderTarget {
    fn to_decompiler_config(&self) -> DecompilerConfig {
        DecompilerConfig
    }
}

mod r2dec {
    use super::{DecompilerConfig, FunctionFacts, SemanticRoutePlan};

    pub fn render_semantic_worker_summary(
        _name: &str,
        _facts: &FunctionFacts,
        _route: &SemanticRoutePlan,
        _config: DecompilerConfig,
    ) -> Option<String> {
        Some("summary".to_string())
    }

    pub fn render_vm_semantic_summary(
        _name: &str,
        _facts: &FunctionFacts,
        _route: &SemanticRoutePlan,
    ) -> Option<String> {
        Some("vm".to_string())
    }
}

fn render_semantic_route(
    function_name: &str,
    function_facts: &FunctionFacts,
    route: &EngineSemanticRoutePlan,
    config: &EngineRenderTarget,
) -> Option<String> {
    match route {
        EngineSemanticRoutePlan::LinearWorker => r2dec::render_semantic_worker_summary(
            function_name,
            function_facts,
            &route.to_decompiler_route(),
            config.to_decompiler_config(),
        ),
        EngineSemanticRoutePlan::VmSummary => {
            r2dec::render_vm_semantic_summary(
                function_name,
                function_facts,
                &route.to_decompiler_route(),
            )
        }
    }
}

fn main() {
    let facts = FunctionFacts;
    let config = EngineRenderTarget;
    let _ = render_semantic_route(
        "sym.worker",
        &facts,
        &EngineSemanticRoutePlan::LinearWorker,
        &config,
    );
}
