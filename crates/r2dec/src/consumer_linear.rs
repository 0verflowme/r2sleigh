use std::fmt::Write as _;

pub(crate) fn render_semantic_worker_linearization(
    plan: &r2types::TypeWritebackPlan,
    semantic_artifact: Option<&r2sym::SemanticArtifact>,
    reason: &str,
) -> String {
    let mut out = String::new();
    for decl in &plan.struct_decls {
        let _ = writeln!(&mut out, "{}", decl.decl);
    }
    if !plan.struct_decls.is_empty() {
        out.push('\n');
    }
    let _ = writeln!(&mut out, "{} {{", plan.signature.signature);
    let _ = writeln!(
        &mut out,
        "    /* r2dec semantic worker linearization: {} */",
        reason
    );
    for warning in plan.diagnostics.warnings.iter().take(2) {
        let _ = writeln!(&mut out, "    /* {} */", warning);
    }

    let mut emitted_any = false;
    for region in semantic_artifact
        .map(r2sym::SemanticArtifact::actionable_regions)
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
                "    /* 0x{:x}: if ({}) => 0x{:x} [{:?}] */",
                region.anchor,
                condition.simplified,
                target,
                condition.evidence().tier
            );
            emitted_any = true;
        }
        for term in region.actionable_memory_terms().into_iter().take(2) {
            let _ = writeln!(
                &mut out,
                "    /* 0x{:x}: {} [{:?}] */",
                region.anchor,
                term.expr,
                term.evidence().tier
            );
            emitted_any = true;
        }
    }
    if !emitted_any {
        let _ = writeln!(
            &mut out,
            "    /* no actionable worker-island statements recovered */"
        );
    }
    let _ = writeln!(&mut out, "}}");
    out
}
