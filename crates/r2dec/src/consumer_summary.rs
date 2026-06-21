use crate::ast::{CFunction, CStmt, CType};
use crate::codegen::{CodeGenConfig, CodeGenerator};
use r2types::{CTypeLike, FunctionFacts, FunctionTypeFacts};
use std::collections::BTreeSet;

fn worker_summary_display_selection(
    summaries: &[r2sym::NativeWorkerSummary],
    limit: usize,
) -> Vec<&r2sym::NativeWorkerSummary> {
    let mut selected = (0..summaries.len().min(limit)).collect::<BTreeSet<_>>();

    for pred in [
        worker_summary_is_out_parser as fn(&r2sym::NativeWorkerSummary) -> bool,
        worker_summary_is_memory_write,
    ] {
        if selected.iter().any(|idx| pred(&summaries[*idx])) {
            continue;
        }
        if let Some(idx) = summaries.iter().position(pred) {
            selected.insert(idx);
        }
    }

    selected
        .into_iter()
        .map(|idx| &summaries[idx])
        .collect::<Vec<_>>()
}

fn append_worker_summary_evidence_comments(
    body: &mut Vec<CStmt>,
    summaries: &[r2sym::NativeWorkerSummary],
) {
    body.push(CStmt::comment(format!(
        "native worker summaries: {}",
        summaries.len()
    )));
    let displayed_worker_summaries = worker_summary_display_selection(summaries, 6);
    for summary in &displayed_worker_summaries {
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
    if summaries.len() > displayed_worker_summaries.len() {
        body.push(CStmt::comment(format!(
            "worker summary: {} more omitted",
            summaries.len() - displayed_worker_summaries.len()
        )));
    }
}

fn worker_summary_is_out_parser(summary: &r2sym::NativeWorkerSummary) -> bool {
    summary.kind == r2sym::NativeWorkerSummaryKind::Parser && summary.dst.is_some()
}

fn worker_summary_is_memory_write(summary: &r2sym::NativeWorkerSummary) -> bool {
    summary.kind == r2sym::NativeWorkerSummaryKind::MemoryWrite
}

pub(crate) fn certified_out_param_labels(type_facts: &FunctionTypeFacts) -> Vec<String> {
    type_facts
        .source_authorized_out_param_certificates()
        .map(|cert| {
            if cert.param_name.trim().is_empty() {
                cert.param_index.to_string()
            } else {
                format!("{}:{}", cert.param_index, cert.param_name)
            }
        })
        .collect()
}

pub(crate) fn certified_field_access_labels(type_facts: &FunctionTypeFacts) -> Vec<String> {
    let mut certificates = type_facts
        .field_access_certificates
        .iter()
        .collect::<Vec<_>>();
    certificates.sort();

    let mut labels = certificates
        .into_iter()
        .map(|cert| {
            let param = type_facts
                .merged_signature
                .as_ref()
                .and_then(|signature| signature.params.get(cert.slot));
            let base = param
                .map(|param| param.name.trim().to_string())
                .filter(|name| !name.is_empty())
                .unwrap_or_else(|| format!("arg{}", cert.slot + 1));
            let separator = if param
                .and_then(|param| param.ty.as_ref())
                .is_some_and(|ty| matches!(ty, CTypeLike::Pointer(_)))
            {
                "->"
            } else {
                "."
            };
            format!("{base}{separator}{}", cert.field_name)
        })
        .collect::<Vec<_>>();
    labels.dedup();
    labels
}

pub(crate) fn render_for_route(
    func_name: &str,
    function_facts: &FunctionFacts,
    route: &crate::planner::SemanticRoutePlan,
    codegen_config: CodeGenConfig,
) -> Option<String> {
    let (reason, route_kind) = match route {
        crate::planner::SemanticRoutePlan::StructuredWorker { reason } => {
            (reason, "structured_worker_summary")
        }
        crate::planner::SemanticRoutePlan::LinearWorker { reason } => {
            (reason, "native_linear_summary")
        }
        crate::planner::SemanticRoutePlan::SummaryIslands { reason } => (reason, "summary_islands"),
        _ => return None,
    };
    let semantic_artifact = function_facts.semantic_artifact()?;
    let is_summary_island_route = matches!(
        route,
        crate::planner::SemanticRoutePlan::SummaryIslands { .. }
    );
    let is_structured_worker_route = matches!(
        route,
        crate::planner::SemanticRoutePlan::StructuredWorker { .. }
    );
    let is_residual_route = !is_summary_island_route
        && (matches!(semantic_artifact.stage, r2sym::RefinementStage::Residual)
            || !semantic_artifact.diagnostics.residual_reasons.is_empty());
    let claim_summary = semantic_artifact.semantic_claim_summary();
    let certified_out_param_count = function_facts
        .types
        .source_authorized_out_param_certificates()
        .count();

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
        body.push(CStmt::comment(
            "render contract: summary facts only; no executable native C reconstructed".to_string(),
        ));
    } else if is_structured_worker_route {
        body.push(CStmt::comment(format!(
            "r2dec summary: semantic worker structured summary for {}",
            crate::sanitize_comment_text(reason)
        )));
        body.push(CStmt::comment(format!(
            "semantic route: {route_kind}; source_mode={}; slice={}",
            crate::semantic_mode_label(semantic_artifact),
            semantic_artifact
                .slice_class()
                .map(crate::semantic_slice_class_label)
                .unwrap_or("unknown")
        )));
        body.push(CStmt::comment(
            "render contract: summary facts only; no executable native C reconstructed".to_string(),
        ));
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
        body.push(CStmt::comment(
            "render contract: residual summary only; no certified native C".to_string(),
        ));
    } else {
        body.push(CStmt::comment(format!(
            "r2dec summary: semantic worker linear summary for {}",
            crate::sanitize_comment_text(reason)
        )));
        body.push(CStmt::comment(format!(
            "semantic route: {route_kind}; source_mode={}; slice={}",
            crate::semantic_mode_label(semantic_artifact),
            semantic_artifact
                .slice_class()
                .map(crate::semantic_slice_class_label)
                .unwrap_or("unknown")
        )));
        body.push(CStmt::comment(
            "render contract: summary facts only; no executable native C reconstructed".to_string(),
        ));
    }

    body.push(CStmt::comment(format!(
        "semantic claims: renderable={}, control={}, memory={}, value={}, summary_roles={}, type_args={}, out_args={}, name_hint={}, residual={}",
        claim_summary.renderable_summary_claims,
        claim_summary.structural_control_claims,
        claim_summary.structural_memory_claims,
        claim_summary.structural_value_claims,
        claim_summary.summary_role_certificates.len(),
        claim_summary.pointer_param_indices.len(),
        certified_out_param_count,
        claim_summary.name_hint_claims,
        claim_summary.residual_claims
    )));

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
                "summary role hint: {}; source={:?}; confidence={:?}",
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
            if is_summary_island_route && !native.summary.worker_summaries.is_empty() {
                append_worker_summary_evidence_comments(
                    &mut body,
                    &native.summary.worker_summaries,
                );
            }
        } else if !native.summary.worker_summaries.is_empty() {
            body.push(CStmt::comment(format!(
                "native worker summaries: {}",
                native.summary.worker_summaries.len()
            )));
            let displayed_worker_summaries =
                worker_summary_display_selection(&native.summary.worker_summaries, 6);
            for summary in &displayed_worker_summaries {
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
            if native.summary.worker_summaries.len() > displayed_worker_summaries.len() {
                body.push(CStmt::comment(format!(
                    "worker summary: {} more omitted",
                    native.summary.worker_summaries.len() - displayed_worker_summaries.len()
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

    let certified_fields = certified_field_access_labels(&function_facts.types);
    if !certified_fields.is_empty() {
        body.push(CStmt::comment(format!(
            "certified field accesses: {}",
            certified_fields.join(", ")
        )));
    }

    if let Some(rollup) = function_facts.summary_rollup() {
        if let Some(return_relation) = rollup.root_return_relation.as_ref() {
            body.push(CStmt::comment(format!(
                "summary return: {return_relation:?}"
            )));
        }
        let certified_out_params = certified_out_param_labels(&function_facts.types);
        if !certified_out_params.is_empty() {
            body.push(CStmt::comment(format!(
                "certified out params: {}",
                certified_out_params.join(", ")
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

    let c_func = semantic_worker_summary_function(func_name, body);
    let mut codegen = CodeGenerator::new(codegen_config);
    Some(crate::rewrite_summary_arg_labels(
        codegen.generate_function(&c_func),
        &function_facts.types,
    ))
}

fn semantic_worker_summary_function(func_name: &str, body: Vec<CStmt>) -> CFunction {
    CFunction {
        name: func_name.to_string(),
        ret_type: CType::Void,
        params: Vec::new(),
        locals: Vec::new(),
        body,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn certified_out_param_labels_require_source_identity() {
        let type_facts = FunctionTypeFacts {
            out_param_certificates: vec![
                r2types::OutParamCertificate {
                    param_index: 0,
                    param_name: "raw".to_string(),
                    pointee_type: None,
                    evidence: vec![r2types::OutParamCertificateEvidence::InterprocArgWrite],
                    sources: Vec::new(),
                },
                r2types::OutParamCertificate {
                    param_index: 1,
                    param_name: "out".to_string(),
                    pointee_type: None,
                    evidence: vec![r2types::OutParamCertificateEvidence::NativeWorkerWrite],
                    sources: vec![r2types::OutParamCertificateSource::NativeWorkerSummary {
                        stable_id: 0x55,
                        anchor: 0x401000,
                        summary_kind: r2sym::NativeWorkerSummaryKind::MemoryWrite,
                        param_index: 1,
                    }],
                },
            ],
            ..FunctionTypeFacts::default()
        };

        assert_eq!(certified_out_param_labels(&type_facts), vec!["1:out"]);
    }

    #[test]
    fn certified_field_access_labels_use_signature_parameter_names() {
        let type_facts = FunctionTypeFacts {
            merged_signature: Some(r2types::FunctionSignatureSpec {
                ret_type: None,
                params: vec![r2types::FunctionParamSpec {
                    name: "out".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Typedef(
                        "Result".to_string(),
                    )))),
                }],
            }),
            field_access_certificates: vec![r2types::FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "hash".to_string(),
                field_type: Some("uint64_t".to_string()),
            }],
            ..FunctionTypeFacts::default()
        };

        assert_eq!(
            certified_field_access_labels(&type_facts),
            vec!["out->hash"]
        );
    }

    #[test]
    fn summary_comment_out_args_count_requires_certified_type_facts() {
        let mut semantic_artifact = crate::test_native_semantic_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::ArtifactGranularity::Regioned,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut semantic_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::MemoryWrite,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(semantic_artifact));

        let output = render_for_route(
            "dbg.write_out",
            &function_facts,
            &crate::planner::SemanticRoutePlan::LinearWorker {
                reason: "test summary".to_string(),
            },
            CodeGenConfig::default(),
        )
        .expect("summary output");

        assert!(output.contains("out_args=0"));
        assert!(!output.contains("out_params=["));
    }

    fn test_worker_summary(
        anchor: u64,
        kind: r2sym::NativeWorkerSummaryKind,
    ) -> r2sym::NativeWorkerSummary {
        r2sym::NativeWorkerSummary {
            anchor,
            kind,
            dst: if kind == r2sym::NativeWorkerSummaryKind::Parser {
                Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                })
            } else {
                None
            },
            src: None,
            memory: if matches!(
                kind,
                r2sym::NativeWorkerSummaryKind::Parser
                    | r2sym::NativeWorkerSummaryKind::MemoryWrite
            ) {
                Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                })
            } else {
                None
            },
            len: None,
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: if kind == r2sym::NativeWorkerSummaryKind::Parser {
                Some(r2sym::NativeParserSummary {
                    kind: r2sym::NativeParserKind::Numeric,
                    cursor_arg: Some(0),
                    base: Some(10),
                    digit_min: Some(b'0'),
                    digit_max: Some(b'9'),
                    accepts_sign: true,
                    return_predicate: None,
                })
            } else {
                None
            },
            loop_summary: None,
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
        }
    }

    #[test]
    fn worker_summary_display_keeps_late_out_parser_and_memory_write() {
        let mut summaries = Vec::new();
        for idx in 0..6 {
            summaries.push(test_worker_summary(
                0x401000 + idx,
                r2sym::NativeWorkerSummaryKind::MemoryRead,
            ));
        }
        summaries.push(test_worker_summary(
            0x401100,
            r2sym::NativeWorkerSummaryKind::Parser,
        ));
        summaries.push(test_worker_summary(
            0x401108,
            r2sym::NativeWorkerSummaryKind::MemoryWrite,
        ));

        let selected = worker_summary_display_selection(&summaries, 6)
            .into_iter()
            .map(|summary| summary.anchor)
            .collect::<Vec<_>>();

        assert!(selected.contains(&0x401100));
        assert!(selected.contains(&0x401108));
    }
}
