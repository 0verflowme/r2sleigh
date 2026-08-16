use std::fmt::Write as _;

pub(crate) fn render_semantic_worker_linearization(
    plan: &r2types::TypeWritebackPlan,
    semantic_artifact: Option<&r2sym::SemanticArtifactReport>,
    reason: &str,
) -> String {
    let mut out = String::new();
    let _ = writeln!(
        &mut out,
        "/* r2dec residual: semantic worker linearization for {} */",
        crate::sanitize_comment_text(reason)
    );
    let _ = writeln!(
        &mut out,
        "/* function: {} */",
        crate::sanitize_comment_text(&plan.signature.function_name)
    );
    let _ = writeln!(
        &mut out,
        "/* render contract: summary facts only; no executable native C reconstructed */"
    );
    if !plan.struct_decls.is_empty() {
        let _ = writeln!(
            &mut out,
            "/* type writeback declarations suppressed: {} */",
            plan.struct_decls.len()
        );
    }
    if !plan.signature.params.is_empty() || plan.signature.confidence > 0 {
        let _ = writeln!(
            &mut out,
            "/* type writeback signature suppressed: confidence={} params={} */",
            plan.signature.confidence,
            plan.signature.params.len()
        );
    }
    if !plan.global_type_links.is_empty() {
        let _ = writeln!(
            &mut out,
            "/* global type links suppressed: {} */",
            plan.global_type_links.len()
        );
    }
    if !plan.var_type_candidates.is_empty() || !plan.var_rename_candidates.is_empty() {
        let _ = writeln!(
            &mut out,
            "/* local type writeback candidates suppressed: types={} renames={} */",
            plan.var_type_candidates.len(),
            plan.var_rename_candidates.len()
        );
    }
    for warning in plan.diagnostics.warnings.iter().take(2) {
        let _ = writeln!(&mut out, "/* {} */", crate::sanitize_comment_text(warning));
    }
    if plan.diagnostics.warnings.len() > 2 {
        let _ = writeln!(
            &mut out,
            "/* type writeback warnings: {} more omitted */",
            plan.diagnostics.warnings.len() - 2
        );
    }
    for warning in plan.diagnostics.solver_warnings.iter().take(2) {
        let _ = writeln!(
            &mut out,
            "/* solver warning: {} */",
            crate::sanitize_comment_text(warning)
        );
    }
    if plan.diagnostics.solver_warnings.len() > 2 {
        let _ = writeln!(
            &mut out,
            "/* solver warnings: {} more omitted */",
            plan.diagnostics.solver_warnings.len() - 2
        );
    }
    for conflict in plan.diagnostics.conflicts.iter().take(2) {
        let _ = writeln!(
            &mut out,
            "/* type conflict: {} */",
            crate::sanitize_comment_text(conflict)
        );
    }
    if plan.diagnostics.conflicts.len() > 2 {
        let _ = writeln!(
            &mut out,
            "/* type conflicts: {} more omitted */",
            plan.diagnostics.conflicts.len() - 2
        );
    }

    let mut emitted_any = false;
    for region in semantic_artifact
        .map(r2sym::SemanticArtifactReport::actionable_regions)
        .unwrap_or_default()
        .into_iter()
        .take(6)
    {
        if let (Some(target), Some(condition)) = (
            region.actionable_reachable_target(),
            region.actionable_compiled_condition(),
        ) {
            let _ = writeln!(
                &mut out,
                "/* 0x{:x}: conditional target 0x{:x}; predicate={} [{:?}] */",
                region.anchor,
                target,
                crate::sanitize_comment_text(&condition.simplified),
                condition.evidence().tier
            );
            emitted_any = true;
        }
        for term in region.actionable_memory_terms().into_iter().take(2) {
            let _ = writeln!(
                &mut out,
                "/* 0x{:x}: memory fact {} [{:?}] */",
                region.anchor,
                crate::sanitize_comment_text(&term.expr),
                term.evidence().tier
            );
            emitted_any = true;
        }
    }
    if !emitted_any {
        let _ = writeln!(
            &mut out,
            "/* no actionable worker-island statements recovered */"
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn writeback_plan_with_source_shaped_artifacts() -> r2types::TypeWritebackPlan {
        r2types::TypeWritebackPlan {
            signature: r2types::InferredSignature {
                function_name: "sym.worker".to_string(),
                signature: "int sym.worker(int argc, char **argv)".to_string(),
                ret_type: "int".to_string(),
                params: vec![
                    r2types::InferredSignatureParam {
                        name: "argc".to_string(),
                        param_type: "int".to_string(),
                    },
                    r2types::InferredSignatureParam {
                        name: "argv".to_string(),
                        param_type: "char **".to_string(),
                    },
                ],
                callconv: "sysv".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 90,
            },
            var_type_candidates: Vec::new(),
            var_rename_candidates: Vec::new(),
            struct_decls: vec![r2types::StructDeclCandidate {
                name: "struct_ai_shape".to_string(),
                decl: "struct struct_ai_shape { int fake; };".to_string(),
                confidence: 90,
                source: r2types::StructDeclSource::LocalInferred,
                fields: Vec::new(),
            }],
            global_type_links: Vec::new(),
            diagnostics: r2types::TypeWritebackDiagnostics {
                warnings: vec!["summary-derived signature is display-only".to_string()],
                ..r2types::TypeWritebackDiagnostics::default()
            },
        }
    }

    #[test]
    fn semantic_worker_linearization_suppresses_writeback_c_artifacts() {
        let plan = writeback_plan_with_source_shaped_artifacts();
        let output = render_semantic_worker_linearization(&plan, None, "bounded worker");

        assert!(output.starts_with("/* r2dec residual: semantic worker linearization"));
        assert!(output.contains("render contract: summary facts only"));
        assert!(output.contains("type writeback signature suppressed"));
        assert!(output.contains("type writeback declarations suppressed: 1"));
        assert!(
            !output.contains("int sym.worker(int argc"),
            "summary fallback must not print inferred signatures as C:\n{output}"
        );
        assert!(
            !output.contains("struct struct_ai_shape {"),
            "summary fallback must not print inferred struct declarations as C:\n{output}"
        );
        assert!(
            !output.contains("{\n") && !output.trim_end().ends_with('}'),
            "summary fallback must remain comment-only, got:\n{output}"
        );
    }
}
