pub fn block_guard_fallback_comment(func_name: &str, blocks: usize, max_blocks: usize) -> String {
    let func_name = crate::sanitize_comment_text(func_name);
    format!(
        "/* r2dec budget: skipped decompilation for {} ({} blocks > limit {}). */",
        func_name, blocks, max_blocks
    )
}

pub fn artifact_guard_fallback_comment(func_name: &str, reason: &str) -> String {
    let func_name = crate::sanitize_comment_text(func_name);
    let reason = crate::sanitize_comment_text(reason);
    format!(
        "/* r2dec fallback: skipped decompilation for {} ({}) */",
        func_name, reason
    )
}
