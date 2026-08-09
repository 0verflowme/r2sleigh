use std::fmt::Write as _;

use crate::ast::CType;
use r2types::FunctionFacts;

fn vm_summary_stats_comment(func_name: &str, vm_step: &r2sym::VmStepSummary) -> String {
    let kind = crate::format_vm_summary_kind(vm_step.kind);
    let selector = vm_step.selector.as_deref().unwrap_or("unknown");
    let exact_transfers = vm_step
        .transfers
        .iter()
        .filter(|transfer| transfer.exact)
        .count();
    let likely_transfers = vm_step
        .transfers
        .iter()
        .filter(|transfer| matches!(transfer.confidence(), r2sym::SemanticConfidence::Likely))
        .count();
    let heuristic_transfers = vm_step
        .transfers
        .iter()
        .filter(|transfer| matches!(transfer.confidence(), r2sym::SemanticConfidence::Heuristic))
        .count();
    let redispatch_transfers = vm_step
        .transfers
        .iter()
        .filter(|transfer| transfer.redispatch)
        .count();
    let returning_transfers = vm_step
        .transfers
        .iter()
        .filter(|transfer| transfer.may_return)
        .count();
    let selector_updates = vm_step
        .transfers
        .iter()
        .filter(|transfer| transfer.selector_update.is_some())
        .count();
    let exit_guards = vm_step
        .transfers
        .iter()
        .map(|transfer| transfer.exit_guards.len())
        .sum::<usize>();
    let residual_guards = vm_step
        .transfers
        .iter()
        .filter(|transfer| transfer.residual_guards)
        .count();
    let residual_memory = vm_step
        .transfers
        .iter()
        .filter(|transfer| transfer.residual_memory_effects)
        .count();
    let read_effects = vm_step
        .handler_memory_read_effects
        .values()
        .map(Vec::len)
        .sum::<usize>();
    let write_effects = vm_step
        .handler_memory_write_effects
        .values()
        .map(Vec::len)
        .sum::<usize>();
    let total_reads: usize = vm_step.handler_memory_reads.values().copied().sum();
    let total_writes: usize = vm_step.handler_memory_writes.values().copied().sum();
    format!(
        "r2dec semantic summary: vm_summary for {} ({} @ 0x{:x}, loop_header=0x{:x}, selector={}, targets={}, redispatch={}, exact_transfers={}, likely_transfers={}, heuristic_transfers={}, redispatch_transfers={}, returning_transfers={}, selector_updates={}, exact_exit_guards={}, guard_gaps={}, memory_gaps={}, total_reads={}, total_writes={}, read_effects={}, write_effects={})",
        func_name,
        kind,
        vm_step.dispatch_header,
        vm_step.loop_header,
        selector,
        vm_step.dispatch_targets.len(),
        vm_step.redispatch_handlers.len(),
        exact_transfers,
        likely_transfers,
        heuristic_transfers,
        redispatch_transfers,
        returning_transfers,
        selector_updates,
        exit_guards,
        residual_guards,
        residual_memory,
        total_reads,
        total_writes,
        read_effects,
        write_effects,
    )
}

fn render_vm_handler_comment_block(out: &mut String, vm_step: &r2sym::VmStepSummary, target: u64) {
    let case_values = vm_step
        .case_values_by_target
        .get(&target)
        .cloned()
        .unwrap_or_default();
    let region_blocks = vm_step
        .handler_regions
        .get(&target)
        .map(|blocks| crate::format_vm_target_list(blocks))
        .unwrap_or_else(|| "[]".to_string());
    let labels = if case_values.is_empty() {
        "unlabeled".to_string()
    } else {
        format!(
            "[{}]",
            case_values
                .iter()
                .map(|value| format!("0x{value:x}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let _ = writeln!(
        out,
        "    /* handler 0x{:x}: labels={} default={} blocks={} */",
        target,
        labels,
        vm_step.default_target == Some(target),
        region_blocks
    );

    let mut emitted_body = false;
    for transfer in vm_step
        .transfers
        .iter()
        .filter(|transfer| transfer.handler_target == target)
    {
        let _ = writeln!(
            out,
            "    /* transfer exits={} guards={} updates={} reads={} writes={} confidence={:?} */",
            transfer.exit_targets.len(),
            transfer.exit_guards.len(),
            transfer.state_updates.len() + usize::from(transfer.selector_update.is_some()),
            transfer.memory_reads.len(),
            transfer.memory_writes.len(),
            transfer.confidence()
        );
        emitted_body = true;
        if transfer.selector_update.is_some() {
            let _ = writeln!(out, "    /* selector updated */");
            emitted_body = true;
        }
        if transfer.redispatch {
            let _ = writeln!(out, "    /* redispatch */");
            emitted_body = true;
        }
        if transfer.may_return {
            let _ = writeln!(out, "    /* may return */");
            emitted_body = true;
        }
        if transfer.truncated {
            let _ = writeln!(out, "    /* truncated handler summary */");
            emitted_body = true;
        }
    }

    if !emitted_body {
        let _ = writeln!(out, "    /* no exact handler body recovered */");
    }
}

fn c_identifier_from_function_name(func_name: &str) -> String {
    let mut name = func_name.trim();
    for prefix in ["dbg.", "sym.", "fcn."] {
        if let Some(stripped) = name.strip_prefix(prefix) {
            name = stripped;
            break;
        }
    }

    let mut out = String::with_capacity(name.len().max(1));
    for (idx, ch) in name.chars().enumerate() {
        if ch == '_' || ch.is_ascii_alphabetic() || ch.is_ascii_digit() && idx > 0 {
            out.push(ch);
        } else if idx == 0 && ch.is_ascii_digit() {
            out.push_str("sub_");
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        "vm_summary".to_string()
    } else {
        out
    }
}

fn vm_summary_signature_comment(func_name: &str, function_facts: &FunctionFacts) -> Option<String> {
    let type_facts = function_facts.type_facts();
    let signature = type_facts.render_authorized_signature()?;
    let ret = signature
        .ret_type
        .as_ref()
        .map(crate::type_like_to_ctype)
        .filter(|ty| !matches!(ty, CType::Unknown))?;
    let mut params = Vec::new();
    for (index, param) in signature.params.iter().enumerate() {
        let name = param.name.trim();
        if name.is_empty()
            || crate::is_generic_arg_name(name)
                && !function_facts
                    .render()
                    .is_some_and(|render| render.has_certified_parameter(index))
        {
            continue;
        }
        let Some(ty) = param.ty.as_ref().map(crate::type_like_to_ctype) else {
            continue;
        };
        if matches!(ty, CType::Unknown | CType::Void) {
            continue;
        }
        params.push(format!("{} {}", ty, c_identifier_from_function_name(name)));
    }
    let params = if params.is_empty() {
        "void".to_string()
    } else {
        params.join(", ")
    };
    Some(format!("{ret} {func_name}({params})"))
}

fn render_vm_case_labels(out: &mut String, vm_step: &r2sym::VmStepSummary, target: u64) -> bool {
    let Some(case_values) = vm_step.case_values_by_target.get(&target) else {
        return false;
    };
    if case_values.is_empty() {
        return false;
    }
    for value in case_values {
        let _ = writeln!(out, "    /* case 0x{value:x}: */");
    }
    true
}

pub(crate) fn render_vm_semantic_summary(
    func_name: &str,
    function_facts: &FunctionFacts,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<String> {
    let vm_body = semantic_artifact.vm_body()?;
    let vm_step = vm_body
        .step_summary
        .as_ref()
        .or(vm_body.transfer_summary.as_ref())?;
    let selector = vm_step.selector.as_deref().unwrap_or("dispatch_selector");
    let display_name = c_identifier_from_function_name(func_name);
    let mut out = String::new();

    if let Some(signature) = vm_summary_signature_comment(&display_name, function_facts) {
        let _ = writeln!(out, "/* {signature} */");
    }
    let _ = writeln!(
        out,
        "/* VM summary-only route for {}; executable native C not reconstructed */",
        crate::sanitize_comment_text(&display_name)
    );
    let _ = writeln!(
        out,
        "/* {} */",
        vm_summary_stats_comment(&display_name, vm_step)
    );
    let _ = writeln!(out, "/* selector: {selector} */");
    let _ = writeln!(out, "/* switch ({selector}) */");
    for target in &vm_step.dispatch_targets {
        if !render_vm_case_labels(&mut out, vm_step, *target) {
            continue;
        }
        render_vm_handler_comment_block(&mut out, vm_step, *target);
    }
    if let Some(default_target) = vm_step.default_target {
        let _ = writeln!(out, "    /* default: */");
        render_vm_handler_comment_block(&mut out, vm_step, default_target);
    } else if vm_step.default_target.is_none() {
        let _ = writeln!(out, "/* no default target recovered */");
    }
    for target in &vm_step.dispatch_targets {
        if vm_step.default_target == Some(*target)
            || vm_step
                .case_values_by_target
                .get(target)
                .is_some_and(|values| !values.is_empty())
        {
            continue;
        }
        let _ = writeln!(out, "    /* unlabeled handler 0x{target:x}: */");
        render_vm_handler_comment_block(&mut out, vm_step, *target);
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use r2types::{
        CTypeLike, CertifiedEntity, FunctionParamSpec, FunctionRenderFacts, FunctionSignatureSpec,
        FunctionTypeFacts, SignatureCertificate, SignatureCertificateSource, Signedness,
    };

    fn signed_int(bits: u32) -> CTypeLike {
        CTypeLike::Int {
            bits,
            signedness: Signedness::Signed,
        }
    }

    #[test]
    fn vm_signature_keeps_only_certified_generic_parameters() {
        let signature = FunctionSignatureSpec {
            ret_type: Some(signed_int(32)),
            params: vec![
                FunctionParamSpec {
                    name: "arg0".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(signed_int(8)))),
                },
                FunctionParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(signed_int(32)),
                },
                FunctionParamSpec {
                    name: "arg2".to_string(),
                    ty: Some(signed_int(64)),
                },
            ],
        };
        let mut render = FunctionRenderFacts::default();
        for slot in 0..2 {
            let id = r2ssa::SemanticId::parameter(slot).expect("parameter id");
            render.certified_entities.insert(
                id,
                CertifiedEntity::Parameter {
                    id,
                    slot: slot as u32,
                    entry_values: BTreeSet::new(),
                    carrier_width: 64,
                },
            );
        }
        let facts = FunctionFacts::new(
            FunctionTypeFacts {
                signature_certificate: SignatureCertificate::from_signature(
                    &signature,
                    [SignatureCertificateSource::LocalInference],
                ),
                merged_signature: Some(signature),
                ..FunctionTypeFacts::default()
            },
            None,
        )
        .with_render(render);

        assert_eq!(
            vm_summary_signature_comment("tiny_vm_dispatch", &facts).as_deref(),
            Some("int32_t tiny_vm_dispatch(int8_t* arg0, int32_t arg1)")
        );
    }
}
