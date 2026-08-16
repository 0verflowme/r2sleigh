struct EngineTypeAnalysisRequest {
    caller_prefers_bounded_type_plan: bool,
}

struct EngineFunctionDecompileRequest;
struct EngineAnalyzeRequest;

impl EngineFunctionDecompileRequest {
    fn full_semantics_for_function() -> Self {
        Self
    }
}

impl EngineAnalyzeRequest {
    fn from_input_with_compile_missing_semantics() -> Self {
        Self
    }
}

struct EngineSession;

impl EngineSession {
    fn type_function(&self, _: EngineTypeAnalysisRequest) {}
}

enum EngineSemanticMode {
    Full,
    Optional,
}

fn caller_prefers_bounded_type_plan() -> bool {
    true
}

fn analysis_policy_for_depth(_: u32) -> usize {
    0
}

fn function_exceeds_auto_callback_budget() -> bool {
    true
}

fn sleigh_mode_allows_deep_auto_callbacks() -> bool {
    true
}

fn auto_callback_policy_for_depth(_: u32) -> bool {
    true
}

fn r2sleigh_interproc_helper_scope_budget_allows(_: usize, _: u32) -> i32 {
    0
}

fn build_prepared_interproc_summary_set() {}

mod r2dec {
    pub fn render_semantic_worker_linearization() -> String {
        String::new()
    }
}

mod r2sym {
    pub fn compile_summary_dense_worker_artifact_from_interproc_summary() {}
    pub fn compile_semantic_artifact_default_with_scope() {}
    pub fn augment_semantic_artifact_with_interproc_summary() {}
}

mod r2engine {
    pub fn decompile_route_decision() {}

    pub fn auto_callback_plan_for_policy() {}
}

mod benign {
    pub struct EngineTypeAnalysisRequest {
        pub harmless: bool,
    }

    pub struct PluginGlueRequest {
        pub caller_prefers_bounded_type_plan: bool,
    }
}

fn main() {
    let _ = caller_prefers_bounded_type_plan();
    let _ = analysis_policy_for_depth(0);
    let _ = function_exceeds_auto_callback_budget();
    let _ = sleigh_mode_allows_deep_auto_callbacks();
    let _ = auto_callback_policy_for_depth(2);
    let _ = r2sleigh_interproc_helper_scope_budget_allows(1, 1);
    let _ = EngineTypeAnalysisRequest {
        caller_prefers_bounded_type_plan: true,
    };
    let benign_type = benign::EngineTypeAnalysisRequest { harmless: true };
    let benign_glue = benign::PluginGlueRequest {
        caller_prefers_bounded_type_plan: false,
    };
    let _ = (
        benign_type.harmless,
        benign_glue.caller_prefers_bounded_type_plan,
    );
    let _ = r2dec::render_semantic_worker_linearization();
    r2sym::compile_summary_dense_worker_artifact_from_interproc_summary();
    r2sym::compile_semantic_artifact_default_with_scope();
    r2sym::augment_semantic_artifact_with_interproc_summary();
    r2engine::decompile_route_decision();
    r2engine::auto_callback_plan_for_policy();
    let session = EngineSession;
    session.type_function(EngineTypeAnalysisRequest {
        caller_prefers_bounded_type_plan: true,
    });
    let _ = EngineFunctionDecompileRequest::full_semantics_for_function();
    let _ = EngineAnalyzeRequest::from_input_with_compile_missing_semantics();
    build_prepared_interproc_summary_set();
    let _ = EngineSemanticMode::Full;
    let _ = EngineSemanticMode::Optional;
}
