#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticRoutePlan {
    Standard,
    StructuredWorker { reason: String },
    SummaryIslands { reason: String },
    LinearWorker { reason: String },
    VmSummary { reason: String },
    FallbackComment { comment: String },
}

pub fn block_guard_fallback_comment(func_name: &str, blocks: usize, max_blocks: usize) -> String {
    format!(
        "/* r2dec budget: skipped decompilation for {} ({} blocks > limit {}). */",
        func_name, blocks, max_blocks
    )
}

pub fn artifact_guard_fallback_comment(func_name: &str, reason: &str) -> String {
    format!(
        "/* r2dec fallback: skipped decompilation for {} ({}) */",
        func_name, reason
    )
}
