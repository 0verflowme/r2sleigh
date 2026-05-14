use crate::ast::{self, CFunction, CStmt, CType};
use crate::codegen::{CodeGenConfig, CodeGenerator};
use r2types::{FunctionFacts, FunctionTypeFacts};

pub(crate) fn render_for_route(
    func_name: &str,
    function_facts: &FunctionFacts,
    route: &crate::planner::SemanticRoutePlan,
    codegen_config: CodeGenConfig,
) -> Option<String> {
    let reason = match route {
        crate::planner::SemanticRoutePlan::LinearWorker { reason }
        | crate::planner::SemanticRoutePlan::SummaryIslands { reason } => reason,
        _ => return None,
    };
    let semantic_artifact = function_facts.semantic_artifact()?;
    let is_summary_island_route = matches!(
        route,
        crate::planner::SemanticRoutePlan::SummaryIslands { .. }
    );
    let is_residual_route = !is_summary_island_route
        && (matches!(semantic_artifact.stage, r2sym::RefinementStage::Residual)
            || !semantic_artifact.diagnostics.residual_reasons.is_empty());

    let mut body = Vec::new();
    if is_summary_island_route {
        body.push(CStmt::comment(format!(
            "r2dec summary: semantic worker islands for {}",
            crate::sanitize_comment_text(reason)
        )));
        body.push(CStmt::comment(format!(
            "semantic route: summary_islands; source_mode={}; slice={}",
            if semantic_artifact.diagnostics.skipped_large_cfg {
                "bounded"
            } else {
                crate::semantic_mode_label(semantic_artifact)
            },
            semantic_artifact
                .slice_class()
                .map(crate::semantic_slice_class_label)
                .unwrap_or("unknown")
        )));
    } else if is_residual_route {
        body.push(CStmt::comment(format!(
            "r2dec residual: semantic worker summary for {}",
            crate::sanitize_comment_text(reason)
        )));
        body.push(CStmt::comment(format!(
            "semantic mode: {}; slice={}",
            crate::semantic_mode_label(semantic_artifact),
            semantic_artifact
                .slice_class()
                .map(crate::semantic_slice_class_label)
                .unwrap_or("unknown")
        )));
    } else {
        body.push(CStmt::comment(format!(
            "r2dec summary: semantic worker linear summary for {}",
            crate::sanitize_comment_text(reason)
        )));
        body.push(CStmt::comment(format!(
            "semantic route: native_linear_summary; source_mode={}; slice={}",
            crate::semantic_mode_label(semantic_artifact),
            semantic_artifact
                .slice_class()
                .map(crate::semantic_slice_class_label)
                .unwrap_or("unknown")
        )));
    }

    if !semantic_artifact.diagnostics.residual_reasons.is_empty() {
        let reasons = semantic_artifact
            .diagnostics
            .residual_reasons
            .iter()
            .map(|reason| crate::semantic_residual_reason_label(*reason))
            .collect::<Vec<_>>()
            .join(", ");
        if is_summary_island_route || !is_residual_route {
            body.push(CStmt::comment(format!("bounded reasons: {reasons}")));
        } else {
            body.push(CStmt::comment(format!("residual reasons: {reasons}")));
        }
    }

    if let Some(native) = semantic_artifact.native_body() {
        if let Some(role) = native.summary.role_identity.as_ref() {
            body.push(CStmt::comment(format!(
                "semantic role: {}; source={:?}; confidence={:?}",
                crate::sanitize_comment_text(&role.role_name),
                role.source,
                role.confidence
            )));
        }
        let memory_fact_count = native
            .regions
            .values()
            .map(|region| region.memory.len())
            .sum::<usize>();
        body.push(CStmt::comment(format!(
            "native regions: regions={}, actionable_conditions={}, exact_conditions={}, memory_facts={}",
            native.regions.len(),
            native.actionable_control_count(),
            native.exact_control_count(),
            memory_fact_count
        )));
        if !native.summary.region_summaries.is_empty() {
            body.push(CStmt::comment(format!(
                "native summary islands: {}",
                native.summary.region_summaries.len()
            )));
            for summary in native.summary.region_summaries.iter().take(12) {
                if let Some(stmt) = crate::native_region_summary_structured_stmt(summary) {
                    body.push(stmt);
                }
                if let Some(pseudocode) = crate::native_region_summary_pseudocode(summary) {
                    body.push(CStmt::comment(format!(
                        "summary island: {}",
                        crate::sanitize_comment_text(&pseudocode)
                    )));
                }
                body.push(CStmt::comment(format!(
                    "island summary: {}",
                    crate::sanitize_comment_text(&crate::native_region_summary_detail(summary))
                )));
            }
            if native.summary.region_summaries.len() > 12 {
                body.push(CStmt::comment(format!(
                    "island summary: {} more omitted",
                    native.summary.region_summaries.len() - 12
                )));
            }
        } else if !native.summary.worker_summaries.is_empty() {
            body.push(CStmt::comment(format!(
                "native worker summaries: {}",
                native.summary.worker_summaries.len()
            )));
            for summary in native.summary.worker_summaries.iter().take(6) {
                if let Some(stmt) = crate::native_worker_summary_structured_stmt(summary) {
                    body.push(stmt);
                }
                if let Some(pseudocode) = crate::native_worker_summary_pseudocode(summary) {
                    body.push(CStmt::comment(format!(
                        "worker loop: {}",
                        crate::sanitize_comment_text(&pseudocode)
                    )));
                }
                body.push(CStmt::comment(format!(
                    "worker summary: {}",
                    crate::sanitize_comment_text(&crate::native_worker_summary_detail(summary))
                )));
            }
            if native.summary.worker_summaries.len() > 6 {
                body.push(CStmt::comment(format!(
                    "worker summary: {} more omitted",
                    native.summary.worker_summaries.len() - 6
                )));
            }
        }
    }

    if function_facts.has_assumption_conflicts() {
        body.push(CStmt::comment(format!(
            "assumption conflicts: {}",
            function_facts.assumption_usage.conflicts.len()
        )));
    }
    if function_facts.has_summary_conflicts() {
        body.push(CStmt::comment(
            "summary conflicts: interprocedural summaries did not converge".to_string(),
        ));
    }

    if let Some(rollup) = function_facts.summary_rollup() {
        if let Some(return_relation) = rollup.root_return_relation.as_ref() {
            body.push(CStmt::comment(format!(
                "summary return: {return_relation:?}"
            )));
        }
        if !rollup.out_param_indices.is_empty() {
            body.push(CStmt::comment(format!(
                "summary out params: {}",
                rollup
                    .out_param_indices
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )));
        }
        if rollup.transfer_count
            + rollup.allocation_count
            + rollup.lifetime_count
            + rollup.sync_count
            + rollup.atomic_count
            > 0
        {
            body.push(CStmt::comment(format!(
                "summary effects: transfers={}, allocations={}, lifetimes={}, sync={}, atomics={}",
                rollup.transfer_count,
                rollup.allocation_count,
                rollup.lifetime_count,
                rollup.sync_count,
                rollup.atomic_count
            )));
        }
        if rollup.helper_summary_count > 0 {
            body.push(CStmt::comment(format!(
                "helper summaries: {}",
                rollup.helper_summary_count
            )));
        }
        if rollup.has_unknown_calls || rollup.touches_unknown_memory {
            if is_summary_island_route || !is_residual_route {
                body.push(CStmt::comment(format!(
                    "summary uncertainty: unknown_calls={}, unknown_memory={}",
                    rollup.has_unknown_calls, rollup.touches_unknown_memory
                )));
            } else {
                body.push(CStmt::comment(format!(
                    "residual effects: unknown_calls={}, unknown_memory={}",
                    rollup.has_unknown_calls, rollup.touches_unknown_memory
                )));
            }
        }
    }

    crate::append_summary_return_if_needed(&mut body, function_facts, semantic_artifact);

    let c_func = semantic_worker_summary_function(func_name, &function_facts.types, body);
    let mut codegen = CodeGenerator::new(codegen_config);
    Some(crate::rewrite_summary_arg_labels(
        codegen.generate_function(&c_func),
        &function_facts.types,
    ))
}

fn semantic_worker_summary_function(
    func_name: &str,
    type_facts: &FunctionTypeFacts,
    body: Vec<CStmt>,
) -> CFunction {
    let ret_type = type_facts
        .merged_signature
        .as_ref()
        .and_then(|sig| sig.ret_type.as_ref().map(crate::type_like_to_ctype))
        .unwrap_or(CType::Unknown);
    let has_merged_signature = type_facts.merged_signature.is_some();
    let mut params = crate::merge_params_with_external_signature(
        Vec::new(),
        type_facts.merged_signature.as_ref(),
    );
    if params.is_empty() && !has_merged_signature {
        params = type_facts
            .register_params
            .iter()
            .enumerate()
            .map(|(idx, param)| ast::CParam {
                ty: param
                    .ty
                    .as_ref()
                    .map(crate::type_like_to_ctype)
                    .unwrap_or(CType::Unknown),
                name: if crate::is_generic_arg_name(&param.name) || param.name.trim().is_empty() {
                    format!("arg{}", idx + 1)
                } else {
                    param.name.clone()
                },
            })
            .collect();
    }

    CFunction {
        name: func_name.to_string(),
        ret_type,
        params,
        locals: Vec::new(),
        body,
    }
}
