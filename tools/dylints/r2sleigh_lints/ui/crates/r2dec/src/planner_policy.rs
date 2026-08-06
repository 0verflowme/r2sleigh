enum SemanticRoutePlan {
    Standard,
    SummaryIslands { reason: String },
}

fn cfg_guard_reason_from_summary(block_count: usize) -> Option<String> {
    (block_count > 32).then(|| "large cfg".to_string())
}

fn preferred_semantic_summary_islands_reason(block_count: usize) -> Option<String> {
    cfg_guard_reason_from_summary(block_count)
}

fn semantic_route_plan(block_count: usize) -> SemanticRoutePlan {
    if let Some(reason) = preferred_semantic_summary_islands_reason(block_count) {
        return SemanticRoutePlan::SummaryIslands { reason };
    }
    SemanticRoutePlan::Standard
}

#[cfg(test)]
fn semantic_route_plan_fixture(block_count: usize) -> SemanticRoutePlan {
    semantic_route_plan(block_count)
}

fn render_only(route: &SemanticRoutePlan) -> &'static str {
    match route {
        SemanticRoutePlan::Standard => "standard",
        SemanticRoutePlan::SummaryIslands { .. } => "summary",
    }
}

fn main() {
    let route = semantic_route_plan(64);
    let _ = render_only(&route);
}
