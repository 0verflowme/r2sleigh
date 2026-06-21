struct Structurer;

impl Structurer {
    fn structure_semantic_worker_islands(&mut self, _: usize) -> Option<()> {
        Some(())
    }

    fn structure(&mut self) {}
}

enum SemanticRoutePlan {
    StructuredWorker { reason: String },
    Standard,
}

fn semantic_worker_structured_body(_: &str, _: ()) {}

fn semantic_worker_comment_only_body(_: &str, _: &str) {}

fn primary_body_for_semantic_route(route: &SemanticRoutePlan, structurer: &mut Structurer) {
    match route {
        SemanticRoutePlan::StructuredWorker { reason } => {
            if let Some(structured) = structurer.structure_semantic_worker_islands(6) {
                semantic_worker_structured_body(reason, structured);
            }
            semantic_worker_comment_only_body("structured_worker", reason);
        }
        SemanticRoutePlan::Standard => structurer.structure(),
    }
}

fn main() {
    let mut structurer = Structurer;
    primary_body_for_semantic_route(
        &SemanticRoutePlan::StructuredWorker {
            reason: "summary permission".to_string(),
        },
        &mut structurer,
    );
}
