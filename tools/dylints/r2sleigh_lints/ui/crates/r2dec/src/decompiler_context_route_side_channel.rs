struct SemanticRoutePlan;
struct RenderPermission;

struct DecompilerContext {
    semantic_route: Option<SemanticRoutePlan>,
    skip_runtime_type_inference: Option<bool>,
    use_prepared_semantic_view: Option<bool>,
    render_permission: Option<RenderPermission>,
}

impl DecompilerContext {
    fn with_semantic_route(self, _route: Option<SemanticRoutePlan>) -> Self {
        self
    }

    fn with_render_permission(self, _permission: Option<RenderPermission>) -> Self {
        self
    }

    fn with_runtime_type_inference_policy(self, _skip: Option<bool>) -> Self {
        self
    }

    fn with_prepared_semantic_view_policy(self, _use_view: Option<bool>) -> Self {
        self
    }
}

fn main() {
    let ctx = DecompilerContext {
        semantic_route: None,
        skip_runtime_type_inference: None,
        use_prepared_semantic_view: None,
        render_permission: None,
    };
    let ctx = ctx.with_semantic_route(None);
    let ctx = ctx.with_render_permission(None);
    let ctx = ctx.with_runtime_type_inference_policy(None);
    let _ = ctx.with_prepared_semantic_view_policy(None);
}
