use crate::ast::CStmt;

pub(crate) struct EmptyStructuringFallback {
    pub(crate) body_stmt: CStmt,
    pub(crate) use_conservative_locals: bool,
    pub(crate) is_linear_fallback: bool,
}

pub(crate) fn recover_empty_structuring(folded_reason: String) -> EmptyStructuringFallback {
    EmptyStructuringFallback {
        body_stmt: CStmt::Block(vec![
            CStmt::comment(format!("r2dec residual: {}", folded_reason)),
            CStmt::comment(
                "render contract: failed structuring has no certified executable C body"
                    .to_string(),
            ),
        ]),
        use_conservative_locals: false,
        is_linear_fallback: false,
    }
}

pub(crate) fn semantic_fallback_comment(
    func_name: &str,
    function_facts: &r2types::FunctionFacts,
) -> Option<String> {
    let semantic_artifact = function_facts.semantic_artifact()?;
    if let Some(comment) =
        crate::consumer_vm::render_vm_semantic_fallback_comment(func_name, semantic_artifact)
    {
        return Some(comment);
    }
    let slice_class = semantic_artifact.slice_class()?;
    let mut reason = format!(
        "semantic fallback: {} slice in {} mode",
        crate::semantic_slice_class_label(slice_class),
        crate::semantic_mode_label(semantic_artifact)
    );
    if !semantic_artifact.diagnostics.residual_reasons.is_empty() {
        reason.push_str(" (");
        reason.push_str(
            &semantic_artifact
                .diagnostics
                .residual_reasons
                .iter()
                .map(|reason| crate::semantic_residual_reason_label(*reason))
                .collect::<Vec<_>>()
                .join(", "),
        );
        reason.push(')');
    }
    if !semantic_artifact.ambiguous_targets().is_empty() {
        reason.push_str("; ambiguous_targets=[");
        reason.push_str(
            &semantic_artifact
                .ambiguous_targets()
                .into_iter()
                .map(|target| format!("0x{target:x}"))
                .collect::<Vec<_>>()
                .join(", "),
        );
        reason.push(']');
    }
    if let Some(native) = semantic_artifact.native_body()
        && !native.regions.is_empty()
    {
        reason.push_str(&format!(
            "; regions={}, actionable_conditions={}, exact_conditions={}",
            native.regions.len(),
            native.actionable_control_count(),
            native.exact_control_count(),
        ));
    }
    let actionable_preview = semantic_artifact
        .actionable_regions()
        .into_iter()
        .filter_map(|region| {
            region
                .actionable_compiled_condition()
                .map(|condition| format!("0x{:x}: {}", region.anchor, condition.simplified))
        })
        .take(3)
        .collect::<Vec<_>>();
    if !actionable_preview.is_empty() {
        reason.push_str("; actionable_preview=[");
        reason.push_str(&actionable_preview.join(" | "));
        reason.push(']');
    }
    if function_facts.has_assumption_conflicts() {
        reason.push_str(&format!(
            "; assumption_conflicts={}",
            function_facts.assumption_usage().conflicts.len()
        ));
    }
    if let Some(rollup) = function_facts.summary_rollup() {
        if let Some(return_relation) = rollup.root_return_relation.as_ref() {
            reason.push_str(&format!("; summary_return={return_relation:?}"));
        }
        let certified_out_params =
            crate::consumer_summary::certified_out_param_labels(function_facts.type_facts());
        if !certified_out_params.is_empty() {
            reason.push_str("; out_params=[");
            reason.push_str(&certified_out_params.join(", "));
            reason.push(']');
        }
    }
    Some(format!(
        "/* r2dec fallback: skipped decompilation for {} ({}) */",
        func_name, reason
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_structuring_fallback_is_comment_only() {
        let fallback =
            recover_empty_structuring("folded structuring produced empty output".to_string());

        assert!(!fallback.use_conservative_locals);
        assert!(!fallback.is_linear_fallback);
        let CStmt::Block(stmts) = fallback.body_stmt else {
            panic!("fallback must be a comment block");
        };
        assert!(!stmts.is_empty());
        assert!(
            stmts.iter().all(|stmt| matches!(stmt, CStmt::Comment(_))),
            "empty structuring fallback must not emit executable C: {stmts:?}"
        );
        assert!(stmts.iter().any(|stmt| {
            matches!(stmt, CStmt::Comment(text) if text.contains("no certified executable C body"))
        }));
    }
}
