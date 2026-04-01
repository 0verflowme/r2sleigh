pub(crate) fn render_vm_semantic_fallback_comment(
    func_name: &str,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<String> {
    let vm_body = semantic_artifact.vm_body()?;
    let vm_step = vm_body
        .step_summary
        .as_ref()
        .or(vm_body.transfer_summary.as_ref())?;
    let kind = crate::format_vm_summary_kind(vm_step.kind);
    let selector = vm_step.selector.as_deref().unwrap_or("unknown");
    let inputs = if vm_step.state_inputs.is_empty() {
        "none".to_string()
    } else {
        vm_step.state_inputs.join(", ")
    };
    let outputs = if vm_step.state_outputs.is_empty() {
        "none".to_string()
    } else {
        vm_step.state_outputs.join(", ")
    };
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
    let handler_preview = vm_step
        .dispatch_targets
        .iter()
        .take(3)
        .map(|target| {
            let values = vm_step
                .case_values_by_target
                .get(target)
                .map(|values| {
                    values
                        .iter()
                        .map(|value| format!("0x{value:x}"))
                        .collect::<Vec<_>>()
                        .join("|")
                })
                .unwrap_or_else(|| "default".to_string());
            let updates = vm_step
                .handler_state_updates
                .get(target)
                .map(|updates| {
                    updates
                        .iter()
                        .take(3)
                        .map(|update| format!("{}={}", update.output, update.expr))
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .filter(|text| !text.is_empty())
                .unwrap_or_else(|| "no_state_updates".to_string());
            format!("0x{target:x}[{values}] => {updates}")
        })
        .collect::<Vec<_>>()
        .join("; ");
    Some(format!(
        "/* r2dec semantic summary: vm_summary for {} ({kind} @ 0x{:x}, loop_header=0x{:x}, selector={}, targets={}, redispatch={}, exact_transfers={}, likely_transfers={}, heuristic_transfers={}, redispatch_transfers={}, returning_transfers={}, selector_updates={}, exact_exit_guards={}, residual_guards={}, residual_memory={}, total_reads={}, total_writes={}, read_effects={}, write_effects={}, state_inputs=[{}], state_outputs=[{}], handlers={}) */",
        func_name,
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
        inputs,
        outputs,
        handler_preview,
    ))
}
