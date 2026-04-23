use crate::ast::CStmt;

pub(crate) struct EmptyStructuringFallback {
    pub(crate) body_stmt: CStmt,
    pub(crate) use_conservative_locals: bool,
    pub(crate) is_linear_fallback: bool,
}

pub(crate) fn recover_empty_structuring<'o, F>(
    func: &r2ssa::SSAFunction,
    fold_ctx: &'o crate::fold::FoldingContext<'o>,
    folded_reason: String,
    semantic_worker_linear_reason: Option<&str>,
    mut linearize: F,
) -> EmptyStructuringFallback
where
    F: FnMut() -> Vec<CStmt>,
{
    let mut unfolded = crate::ControlFlowStructurer::new_unfolded(func, fold_ctx);
    let unfolded_stmt = unfolded.structure();

    if crate::Decompiler::stmt_has_content(&unfolded_stmt) {
        return EmptyStructuringFallback {
            body_stmt: crate::Decompiler::prepend_comment(
                unfolded_stmt,
                format!("r2dec fallback: {}", folded_reason),
            ),
            use_conservative_locals: true,
            is_linear_fallback: false,
        };
    }

    let unfolded_reason = unfolded
        .safety_reason()
        .map(str::to_string)
        .unwrap_or_else(|| "unfolded structuring produced empty output".to_string());
    let fallback_reason = format!("{}; {}", folded_reason, unfolded_reason);
    let mut linear_stmts = linearize();

    if let Some(reason) = semantic_worker_linear_reason {
        return EmptyStructuringFallback {
            body_stmt: crate::consumer_structured::semantic_worker_linear_body(
                reason,
                linear_stmts,
            ),
            use_conservative_locals: true,
            is_linear_fallback: true,
        };
    }

    let body_stmt = if linear_stmts.is_empty() {
        CStmt::Block(vec![CStmt::comment(format!(
            "r2dec fallback: {} -> no statements recovered",
            fallback_reason
        ))])
    } else {
        linear_stmts.insert(
            0,
            CStmt::comment(format!(
                "r2dec fallback: {} -> linear block emission",
                fallback_reason
            )),
        );
        CStmt::Block(linear_stmts)
    };

    EmptyStructuringFallback {
        body_stmt,
        use_conservative_locals: true,
        is_linear_fallback: true,
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
            function_facts.assumption_usage.conflicts.len()
        ));
    }
    if let Some(rollup) = function_facts.summary_rollup() {
        if let Some(return_relation) = rollup.root_return_relation.as_ref() {
            reason.push_str(&format!("; summary_return={return_relation:?}"));
        }
        if !rollup.out_param_indices.is_empty() {
            reason.push_str("; out_params=[");
            reason.push_str(
                &rollup
                    .out_param_indices
                    .iter()
                    .map(|idx| idx.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            reason.push(']');
        }
    }
    Some(format!(
        "/* r2dec fallback: skipped decompilation for {} ({}) */",
        func_name, reason
    ))
}
