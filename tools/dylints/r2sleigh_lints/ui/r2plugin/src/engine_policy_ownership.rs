use std::sync::{LazyLock, RwLock};

struct EngineTypeAnalysisRequest {
    caller_prefers_bounded_type_plan: bool,
}

struct EngineSummaryDecompileRequest {
    fallback_comment: Option<String>,
}

impl EngineSummaryDecompileRequest {
    fn guarded_worker_summary() -> Self {
        Self {
            fallback_comment: None,
        }
    }
}

struct EngineSession;

impl EngineSession {
    fn decompile_summary(&self, _: EngineSummaryDecompileRequest) {}
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
    pub fn should_use_direct_named_native_worker_decompile() -> bool {
        false
    }

    pub fn should_use_direct_named_native_worker_type_projection() -> bool {
        false
    }
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
    let _ = r2engine::should_use_direct_named_native_worker_decompile();
    let _ = r2engine::should_use_direct_named_native_worker_type_projection();
    let session = EngineSession;
    session.decompile_summary(EngineSummaryDecompileRequest::guarded_worker_summary());
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
