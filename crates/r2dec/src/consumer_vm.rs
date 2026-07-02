use std::fmt::Write as _;

use r2types::FunctionTypeFacts;

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

pub(crate) fn render_vm_semantic_summary(
    func_name: &str,
    _type_facts: &FunctionTypeFacts,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<String> {
    let vm_body = semantic_artifact.vm_body()?;
    let vm_step = vm_body
        .step_summary
        .as_ref()
        .or(vm_body.transfer_summary.as_ref())?;
    let selector = vm_step.selector.as_deref().unwrap_or("dispatch_selector");
    let mut out = String::new();

    let _ = writeln!(
        out,
        "/* VM summary-only route for {}; executable C refused: missing native render proof */",
        crate::sanitize_comment_text(func_name)
    );
    let _ = writeln!(
        out,
        "/* {} */",
        vm_summary_stats_comment(func_name, vm_step)
    );
    let _ = writeln!(out, "/* selector: {selector} */");
    for target in &vm_step.dispatch_targets {
        render_vm_handler_comment_block(&mut out, vm_step, *target);
    }
    if let Some(default_target) = vm_step.default_target
        && !vm_step.dispatch_targets.contains(&default_target)
    {
        let _ = writeln!(out, "/* default_target=0x{:x} */", default_target);
    } else if vm_step.default_target.is_none() {
        let _ = writeln!(out, "/* no default target recovered */");
    }
    Some(out)
}

pub(crate) fn render_vm_semantic_fallback_comment(
    func_name: &str,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<String> {
    let vm_body = semantic_artifact.vm_body()?;
    let vm_step = vm_body
        .step_summary
        .as_ref()
        .or(vm_body.transfer_summary.as_ref())?;
    Some(format!(
        "/* {} */",
        vm_summary_stats_comment(func_name, vm_step)
    ))
}
