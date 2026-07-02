use std::sync::{LazyLock, RwLock};

struct EngineTypeAnalysisRequest {
    caller_prefers_bounded_type_plan: bool,
}

struct EngineSummaryDecompileRequest {
    fallback_comment: Option<String>,
}

struct EngineFunctionDecompileRequest;
struct EngineAnalyzeRequest;

impl EngineSummaryDecompileRequest {
    fn guarded_worker_summary() -> Self {
        Self {
            fallback_comment: None,
        }
    }
}

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
    fn new(_: usize) -> Self {
        Self
    }

    fn decompile_summary(&self, _: EngineSummaryDecompileRequest) {}
    fn cached_analyze(&self) {}
}

enum EngineSemanticMode {
    Full,
    Optional,
}

static TYPE_WRITEBACK_CACHE: LazyLock<RwLock<usize>> = LazyLock::new(|| RwLock::new(0));

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

fn build_interproc_summary_set_with_scope_facts() {}

mod r2dec {
    pub fn render_semantic_worker_linearization() -> String {
        String::new()
    }

    pub fn render_direct_named_native_worker_summary() -> Option<String> {
        None
    }
}

mod r2sym {
    pub fn function_semantic_summary_seed_for_name() {}
    pub fn function_semantic_summary_seed_for_name_with_linkage() {}
    pub fn has_native_worker_summary_family() -> bool {
        true
    }
    pub fn compile_summary_dense_worker_artifact_from_interproc_summary() {}
    pub fn compile_semantic_artifact_default_with_scope() {}
    pub fn augment_semantic_artifact_with_interproc_summary() {}
}

mod r2types {
    pub fn build_semantic_type_fallback_plan() {}
}

mod r2engine {
    pub struct EngineSemanticRoutePlan;

    pub fn decompile_route_decision() {}

    pub fn should_use_direct_named_native_worker_decompile() -> bool {
        false
    }

    pub fn should_use_direct_named_native_worker_type_projection() -> bool {
        false
    }

    pub fn auto_callback_plan_for_policy() {}
}

mod benign {
    pub struct EngineTypeAnalysisRequest {
        pub harmless: bool,
    }

    pub struct EngineSummaryDecompileRequest {
        pub harmless: bool,
    }

    pub struct PluginGlueRequest {
        pub caller_prefers_bounded_type_plan: bool,
        pub fallback_comment: Option<String>,
    }
}

fn main() {
    let _ = &*TYPE_WRITEBACK_CACHE;
    let _ = caller_prefers_bounded_type_plan();
    let _ = analysis_policy_for_depth(0);
    let _ = function_exceeds_auto_callback_budget();
    let _ = sleigh_mode_allows_deep_auto_callbacks();
    let _ = auto_callback_policy_for_depth(2);
    let _ = r2sleigh_interproc_helper_scope_budget_allows(1, 1);
    let _ = EngineTypeAnalysisRequest {
        caller_prefers_bounded_type_plan: true,
    };
    let _ = EngineSummaryDecompileRequest {
        fallback_comment: Some("fallback".to_string()),
    };
    let benign_type = benign::EngineTypeAnalysisRequest { harmless: true };
    let benign_summary = benign::EngineSummaryDecompileRequest { harmless: true };
    let benign_glue = benign::PluginGlueRequest {
        caller_prefers_bounded_type_plan: false,
        fallback_comment: None,
    };
    let _ = (
        benign_type.harmless,
        benign_summary.harmless,
        benign_glue.caller_prefers_bounded_type_plan,
        benign_glue.fallback_comment,
    );
    let _ = r2dec::render_semantic_worker_linearization();
    let _ = r2dec::render_direct_named_native_worker_summary();
    r2sym::function_semantic_summary_seed_for_name();
    r2sym::function_semantic_summary_seed_for_name_with_linkage();
    let _ = r2sym::has_native_worker_summary_family();
    r2sym::compile_summary_dense_worker_artifact_from_interproc_summary();
    r2sym::compile_semantic_artifact_default_with_scope();
    r2sym::augment_semantic_artifact_with_interproc_summary();
    r2types::build_semantic_type_fallback_plan();
    r2engine::decompile_route_decision();
    let _ = r2engine::EngineSemanticRoutePlan;
    let _ = r2engine::should_use_direct_named_native_worker_decompile();
    let _ = r2engine::should_use_direct_named_native_worker_type_projection();
    r2engine::auto_callback_plan_for_policy();
    let session = EngineSession;
    let _ = EngineSession::new(256);
    session.decompile_summary(EngineSummaryDecompileRequest::guarded_worker_summary());
    session.cached_analyze();
    let _ = EngineFunctionDecompileRequest::full_semantics_for_function();
    let _ = EngineAnalyzeRequest::from_input_with_compile_missing_semantics();
    build_interproc_summary_set_with_scope_facts();
    let _ = EngineSemanticMode::Full;
    let _ = EngineSemanticMode::Optional;
}

mod tests {
    fn tests_can_construct_adversarial_summary_seed_fixtures() {
        super::r2sym::function_semantic_summary_seed_for_name();
    }
}

#[test]
fn test_items_can_construct_adversarial_summary_seed_fixtures() {
    r2sym::function_semantic_summary_seed_for_name();
}
