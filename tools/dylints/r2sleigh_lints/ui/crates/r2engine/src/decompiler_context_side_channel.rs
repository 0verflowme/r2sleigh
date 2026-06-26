struct Context;

impl Context {
    fn with_semantic_route(self) -> Self {
        self
    }

    fn with_render_permission(self) -> Self {
        self
    }

    fn with_runtime_type_inference_policy(self) -> Self {
        self
    }

    fn with_prepared_semantic_view_policy(self) -> Self {
        self
    }
}

fn main() {
    let ctx = Context;
    let ctx = ctx.with_semantic_route();
    let ctx = ctx.with_render_permission();
    let ctx = ctx.with_runtime_type_inference_policy();
    let _ = ctx.with_prepared_semantic_view_policy();
}
