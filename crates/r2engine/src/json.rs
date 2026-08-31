//! JSON payloads the engine hands to its callers.
//!
//! These are a presentation layer: every type here exists to be serialized,
//! and none of them decides anything. They lived in `lib.rs` among the policy
//! and the planning, which is most of why that file reached eleven thousand
//! lines.

use serde::{Deserialize, Serialize};

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineInferredParamJson {
    pub name: String,
    #[serde(rename = "type")]
    pub param_type: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineVarTypeCandidateJson {
    pub name: String,
    pub kind: String,
    pub delta: i64,
    #[serde(rename = "type")]
    pub var_type: String,
    pub isarg: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reg: Option<String>,
    pub size: u32,
    pub confidence: u8,
    pub source: String,
    pub evidence: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineVarRenameCandidateJson {
    pub name: String,
    pub target_name: String,
    pub confidence: u8,
    pub source: String,
    pub evidence: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineStructFieldCandidateJson {
    pub name: String,
    pub offset: u64,
    #[serde(rename = "type")]
    pub field_type: String,
    pub confidence: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineStructDeclCandidateJson {
    pub name: String,
    pub decl: String,
    pub confidence: u8,
    pub source: String,
    pub fields: Vec<EngineStructFieldCandidateJson>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineGlobalTypeLinkCandidateJson {
    pub addr: u64,
    #[serde(rename = "type")]
    pub target_type: String,
    pub confidence: u8,
    pub source: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct EngineTypeWritebackDiagnosticsJson {
    pub conflicts: Vec<String>,
    pub warnings: Vec<String>,
    pub solver_warnings: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct EngineTypeWritebackFactCountsJson {
    pub register_params: usize,
    pub stack_slots: usize,
    pub param_home_stack_slots: usize,
    pub hidden_home_bindings: usize,
    pub field_access_certificates: usize,
    pub array_index_certificates: usize,
    pub scalar_array_render_candidates: usize,
    pub render_member_accesses: usize,
    pub render_array_accesses: usize,
    pub certified_expressions: usize,
    pub certified_parameters: usize,
    pub certified_stack_slots: usize,
    pub certified_memory_accesses: usize,
    pub certified_returns: usize,
    pub certified_control_domains: usize,
    pub incomplete_control_domains: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineTypeWritebackJsonCore {
    pub function_name: String,
    pub signature: String,
    pub ret_type: String,
    pub params: Vec<EngineInferredParamJson>,
    pub callconv: String,
    pub arch: String,
    pub confidence: u8,
    pub callconv_confidence: u8,
    pub signature_render_authorized: bool,
    pub signature_writeback_authorized: bool,
    pub signature_action_decision: u32,
    pub callconv_action_decision: u32,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub signature_certificate_sources: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature_writeback_refusal: Option<String>,
    pub var_type_candidates: Vec<EngineVarTypeCandidateJson>,
    pub var_rename_candidates: Vec<EngineVarRenameCandidateJson>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub external_struct_names: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub field_access_certificate_names: Vec<String>,
    #[serde(
        default,
        skip_serializing_if = "EngineTypeWritebackFactCountsJson::is_empty"
    )]
    pub fact_counts: EngineTypeWritebackFactCountsJson,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub param_home_stack_slot_offsets: Vec<i64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub certified_stack_slot_offsets: Vec<i64>,
    pub struct_decls: Vec<EngineStructDeclCandidateJson>,
    pub global_type_links: Vec<EngineGlobalTypeLinkCandidateJson>,
    pub plans: r2types::AnalysisPlans,
    #[serde(skip_serializing_if = "r2ssa::AssumptionSet::is_empty")]
    pub assumptions: r2ssa::AssumptionSet,
    #[serde(skip_serializing_if = "r2types::AssumptionUsageReport::is_empty")]
    pub assumption_usage: r2types::AssumptionUsageReport,
    pub mutation_plan: r2types::TypeWritebackMutationPlan,
    pub diagnostics: EngineTypeWritebackDiagnosticsJson,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineCfgRiskSummaryJson {
    pub block_count: usize,
    pub loop_count: usize,
    pub back_edge_count: usize,
    pub switch_block_count: usize,
    pub max_switch_cases: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineDecompileRouteJson {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineFunctionAnalysisReportJsonCore {
    pub function_name: String,
    pub function_addr: u64,
    pub cfg_risk: EngineCfgRiskSummaryJson,
    pub plans: r2types::AnalysisPlans,
    #[serde(skip_serializing_if = "r2ssa::AssumptionSet::is_empty")]
    pub assumptions: r2ssa::AssumptionSet,
    #[serde(skip_serializing_if = "r2types::AssumptionUsageReport::is_empty")]
    pub assumption_usage: r2types::AssumptionUsageReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_build_plan: Option<r2sym::ArtifactBuildPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_route: Option<EngineDecompileRouteJson>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary_diagnostics: Option<r2ssa::InterprocSummaryDiagnostics>,
    pub prefer_bounded_type_plan: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineInterprocSummaryJson {
    pub callsite_count: usize,
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary: Option<r2ssa::FunctionSemanticSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary_json: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub scope: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Copy)]
pub struct EngineInterprocSummaryJsonInput<'a> {
    pub callsite_count: usize,
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub summary: Option<&'a r2ssa::FunctionSemanticSummary>,
    pub scope_report: Option<&'a serde_json::Value>,
    pub symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnginePhaseTimingJson {
    pub phase: EnginePhase,
    pub status: EnginePhaseStatus,
    pub elapsed_us: u64,
}

#[derive(Debug, Clone, Serialize)]
pub struct EngineSemanticStatusJson {
    pub available: bool,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct EngineInferredTypeWritebackJson {
    #[serde(flatten)]
    pub core: EngineTypeWritebackJsonCore,
    pub interproc: EngineInterprocSummaryJson,
    pub semantic_status: EngineSemanticStatusJson,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantics: Option<r2sym::SemanticArtifactReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiled_semantics: Option<r2sym::CompiledSemanticInfo>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub phase_timings: Vec<EnginePhaseTimingJson>,
}

#[derive(Debug, Clone, Serialize)]
pub struct EngineFunctionAnalysisSessionReportJson {
    #[serde(flatten)]
    pub core: EngineFunctionAnalysisReportJsonCore,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic: Option<r2sym::CompiledSemanticInfo>,
    pub type_writeback: EngineInferredTypeWritebackJson,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub phase_timings: Vec<EnginePhaseTimingJson>,
}

#[derive(Debug, Clone, Copy)]
pub struct EngineFunctionAnalysisTypeWritebackJsonRequest<'a> {
    pub report: &'a EngineFunctionAnalysisReportPayload,
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub scope_report: Option<&'a serde_json::Value>,
    pub symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
}

fn writeback_evidence_json(evidence: &[r2types::WritebackEvidence]) -> Vec<String> {
    evidence
        .iter()
        .map(|tag| tag.as_str().to_string())
        .collect()
}

fn struct_fields_json(
    fields: &[r2types::StructFieldCandidate],
) -> Vec<EngineStructFieldCandidateJson> {
    fields
        .iter()
        .map(|field| EngineStructFieldCandidateJson {
            name: field.name.clone(),
            offset: field.offset,
            field_type: field.field_type.clone(),
            confidence: field.confidence,
        })
        .collect()
}

pub fn type_writeback_json_core(
    payload: EngineTypeWritebackPayload,
) -> EngineTypeWritebackJsonCore {
    let ptr_bits = payload.ptr_bits;
    EngineTypeWritebackJsonCore {
        function_name: payload.signature.function_name,
        signature: payload.signature.signature,
        ret_type: payload.signature.ret_type,
        params: payload
            .signature
            .params
            .into_iter()
            .map(|param| EngineInferredParamJson {
                name: param.name,
                param_type: param.param_type,
            })
            .collect(),
        callconv: payload.signature.callconv,
        arch: payload.signature.arch,
        confidence: payload.signature.confidence,
        callconv_confidence: payload.signature.callconv_confidence,
        signature_render_authorized: payload.signature_render_authorized,
        signature_writeback_authorized: payload.signature_writeback_authorized,
        signature_action_decision: payload.signature_action_decision as u32,
        callconv_action_decision: payload.callconv_action_decision as u32,
        signature_certificate_sources: payload.signature_certificate_sources,
        signature_writeback_refusal: payload.signature_writeback_refusal,
        var_type_candidates: payload
            .var_type_candidates
            .into_iter()
            .map(|candidate| EngineVarTypeCandidateJson {
                name: candidate.name,
                kind: candidate.kind,
                delta: candidate.delta,
                var_type: candidate.var_type,
                isarg: candidate.isarg,
                reg: candidate.reg,
                size: candidate.size,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: writeback_evidence_json(&candidate.evidence),
            })
            .collect(),
        var_rename_candidates: payload
            .var_rename_candidates
            .into_iter()
            .map(|candidate| EngineVarRenameCandidateJson {
                name: candidate.name,
                target_name: candidate.target_name,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: writeback_evidence_json(&candidate.evidence),
            })
            .collect(),
        external_struct_names: payload.external_struct_names,
        field_access_certificate_names: payload.field_access_certificate_names,
        fact_counts: EngineTypeWritebackFactCountsJson {
            register_params: payload.fact_counts.register_params,
            stack_slots: payload.fact_counts.stack_slots,
            param_home_stack_slots: payload.fact_counts.param_home_stack_slots,
            hidden_home_bindings: payload.fact_counts.hidden_home_bindings,
            field_access_certificates: payload.fact_counts.field_access_certificates,
            array_index_certificates: payload.fact_counts.array_index_certificates,
            scalar_array_render_candidates: payload.fact_counts.scalar_array_render_candidates,
            render_member_accesses: payload.fact_counts.render_member_accesses,
            render_array_accesses: payload.fact_counts.render_array_accesses,
            certified_expressions: payload.fact_counts.certified_expressions,
            certified_parameters: payload.fact_counts.certified_parameters,
            certified_stack_slots: payload.fact_counts.certified_stack_slots,
            certified_memory_accesses: payload.fact_counts.certified_memory_accesses,
            certified_returns: payload.fact_counts.certified_returns,
            certified_control_domains: payload.fact_counts.certified_control_domains,
            incomplete_control_domains: payload.fact_counts.incomplete_control_domains,
        },
        param_home_stack_slot_offsets: payload.param_home_stack_slot_offsets,
        certified_stack_slot_offsets: payload.certified_stack_slot_offsets,
        struct_decls: payload
            .struct_decls
            .into_iter()
            .map(|decl| EngineStructDeclCandidateJson {
                name: decl.name,
                decl: decl.decl,
                confidence: decl.confidence,
                source: decl.source.as_str().to_string(),
                fields: struct_fields_json(&decl.fields),
            })
            .collect(),
        global_type_links: payload
            .global_type_links
            .into_iter()
            .map(|candidate| EngineGlobalTypeLinkCandidateJson {
                addr: candidate.addr,
                target_type: r2types::render_writeback_apply_type(&candidate.target_type, ptr_bits),
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
            })
            .collect(),
        plans: payload.plans,
        assumptions: payload.assumptions,
        assumption_usage: payload.assumption_usage,
        mutation_plan: payload.mutation_plan,
        diagnostics: EngineTypeWritebackDiagnosticsJson {
            conflicts: payload.diagnostics.conflicts,
            warnings: payload.diagnostics.warnings,
            solver_warnings: payload.diagnostics.solver_warnings,
        },
    }
}

pub fn type_writeback_report_json(
    payload: EngineTypeWritebackPayload,
    interproc: EngineInterprocSummaryJson,
    semantics: Option<r2sym::SemanticArtifactReport>,
    compiled_semantics: Option<r2sym::CompiledSemanticInfo>,
) -> EngineInferredTypeWritebackJson {
    let semantic_status = semantic_status_json(semantics.as_ref(), None);
    EngineInferredTypeWritebackJson {
        core: type_writeback_json_core(payload),
        interproc,
        semantic_status,
        semantics,
        compiled_semantics,
        phase_timings: empty_engine_phase_timings(),
    }
}

fn semantic_status_json(
    semantics: Option<&r2sym::SemanticArtifactReport>,
    fallback_reason: Option<String>,
) -> EngineSemanticStatusJson {
    match semantics {
        Some(artifact) => EngineSemanticStatusJson {
            available: true,
            reason: format!(
                "{} {}",
                semantic_granularity_label(artifact.granularity),
                semantic_report_mode_label(artifact)
            ),
        },
        None => EngineSemanticStatusJson {
            available: false,
            reason: fallback_reason.unwrap_or_else(|| "semantic artifact unavailable".to_string()),
        },
    }
}

pub fn type_writeback_report_json_from_function_analysis(
    request: EngineFunctionAnalysisTypeWritebackJsonRequest<'_>,
) -> EngineInferredTypeWritebackJson {
    let semantics = request.report.semantic_report.clone();
    let compiled_semantics = request.report.compiled_semantics.clone();
    let mut report = type_writeback_report_json(
        request.report.type_writeback.clone(),
        interproc_summary_json(EngineInterprocSummaryJsonInput {
            callsite_count: request.report.callsite_count,
            iterations: request.iterations,
            max_iterations: request.max_iterations,
            converged: request.converged,
            summary: request.report.current_summary.as_ref(),
            scope_report: request.scope_report,
            symbolic_scope: request.symbolic_scope,
        }),
        semantics,
        compiled_semantics,
    );
    report.semantic_status = semantic_status_json(
        report.semantics.as_ref(),
        request
            .report
            .semantic_route
            .as_ref()
            .and_then(|route| route.reason.clone())
            .or_else(|| {
                request
                    .report
                    .summary_diagnostics
                    .as_ref()
                    .map(|diagnostics| format!("summary diagnostics: {diagnostics:?}"))
            }),
    );
    report
}

pub fn symbolic_scope_report_json(
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<serde_json::Value> {
    let scope = symbolic_scope?;
    let payloads = scope
        .helper_functions()
        .filter_map(|function| {
            function.name.as_ref().map(|name| {
                serde_json::json!({
                    "function_addr": function.id.0,
                    "function_name": name,
                })
            })
        })
        .collect::<Vec<_>>();
    let seeds = scope
        .helper_functions()
        .filter_map(|function| {
            function.name.as_ref().map(|name| {
                serde_json::json!({
                    "id": function.id.0,
                    "name": name,
                })
            })
        })
        .collect::<Vec<_>>();
    if seeds.is_empty() && payloads.is_empty() {
        return None;
    }
    Some(serde_json::json!({
        "phase": "symbolic_scope",
        "payloads": payloads,
        "seeds": seeds,
    }))
}

pub fn merged_interproc_scope_report_json(
    scope_report: Option<&serde_json::Value>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<serde_json::Value> {
    let Some(symbolic_scope_json) = symbolic_scope_report_json(symbolic_scope) else {
        return scope_report.cloned();
    };
    let Some(mut merged) = scope_report.cloned() else {
        return Some(symbolic_scope_json);
    };
    let (Some(merged_obj), Some(symbolic_obj)) =
        (merged.as_object_mut(), symbolic_scope_json.as_object())
    else {
        return Some(merged);
    };

    if !merged_obj.contains_key("phase")
        && let Some(phase) = symbolic_obj.get("phase")
    {
        merged_obj.insert("phase".to_string(), phase.clone());
    }
    for key in ["payloads", "seeds"] {
        let Some(serde_json::Value::Array(symbolic_items)) = symbolic_obj.get(key) else {
            continue;
        };
        let entry = merged_obj
            .entry(key.to_string())
            .or_insert_with(|| serde_json::Value::Array(Vec::new()));
        if let serde_json::Value::Array(items) = entry {
            items.extend(symbolic_items.iter().cloned());
        }
    }

    Some(merged)
}

pub fn interproc_summary_json(
    input: EngineInterprocSummaryJsonInput<'_>,
) -> EngineInterprocSummaryJson {
    let iterations = input.iterations.max(1);
    EngineInterprocSummaryJson {
        callsite_count: input.callsite_count,
        iterations,
        max_iterations: input.max_iterations.max(iterations),
        converged: input.converged,
        summary: input.summary.cloned(),
        summary_json: input
            .summary
            .and_then(|summary| serde_json::to_string(summary).ok()),
        scope: merged_interproc_scope_report_json(input.scope_report, input.symbolic_scope),
    }
}

fn cfg_risk_summary_json(summary: CFGRiskSummary) -> EngineCfgRiskSummaryJson {
    EngineCfgRiskSummaryJson {
        block_count: summary.block_count,
        loop_count: summary.loop_count,
        back_edge_count: summary.back_edge_count,
        switch_block_count: summary.switch_block_count,
        max_switch_cases: summary.max_switch_cases,
    }
}

pub fn decompile_route_json(route: &r2types::DecompileRouteFacts) -> EngineDecompileRouteJson {
    match route.kind {
        r2types::DecompileRouteKind::Standard => EngineDecompileRouteJson {
            kind: "standard".to_string(),
            reason: None,
            comment: None,
        },
        r2types::DecompileRouteKind::StructuredWorker => EngineDecompileRouteJson {
            kind: "structured_worker".to_string(),
            reason: route.reason.clone(),
            comment: None,
        },
        r2types::DecompileRouteKind::LinearWorker => EngineDecompileRouteJson {
            kind: "linear_worker".to_string(),
            reason: route.reason.clone(),
            comment: None,
        },
        r2types::DecompileRouteKind::SummaryIslands => EngineDecompileRouteJson {
            kind: "summary_islands".to_string(),
            reason: route.reason.clone(),
            comment: None,
        },
        r2types::DecompileRouteKind::VmSummary => EngineDecompileRouteJson {
            kind: "vm_summary".to_string(),
            reason: route.reason.clone(),
            comment: None,
        },
        r2types::DecompileRouteKind::FallbackComment => EngineDecompileRouteJson {
            kind: "fallback_comment".to_string(),
            reason: route.reason.clone(),
            comment: route.fallback_comment.clone(),
        },
    }
}

pub fn function_analysis_report_json_core(
    payload: &EngineFunctionAnalysisReportPayload,
) -> EngineFunctionAnalysisReportJsonCore {
    EngineFunctionAnalysisReportJsonCore {
        function_name: payload.function_name.clone(),
        function_addr: payload.function_addr,
        cfg_risk: cfg_risk_summary_json(payload.cfg_summary),
        plans: payload.plans.clone(),
        assumptions: payload.assumptions.clone(),
        assumption_usage: payload.assumption_usage.clone(),
        semantic_build_plan: payload.semantic_build_plan.clone(),
        semantic_route: payload.semantic_route.as_ref().map(decompile_route_json),
        summary_diagnostics: payload.summary_diagnostics.clone(),
        prefer_bounded_type_plan: payload.prefer_bounded_type_plan,
    }
}

pub fn function_analysis_session_report_json(
    payload: &EngineFunctionAnalysisReportPayload,
    mut type_writeback: EngineInferredTypeWritebackJson,
    phase_timings: Vec<EnginePhaseTimingJson>,
) -> EngineFunctionAnalysisSessionReportJson {
    type_writeback.phase_timings = normalize_engine_phase_timings(type_writeback.phase_timings);
    EngineFunctionAnalysisSessionReportJson {
        core: function_analysis_report_json_core(payload),
        semantic: payload.compiled_semantics.clone(),
        type_writeback,
        phase_timings: normalize_engine_phase_timings(phase_timings),
    }
}
