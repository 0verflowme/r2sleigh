use std::fmt::Write as _;

use r2types::FunctionTypeFacts;

fn vm_summary_stats_comment(func_name: &str, vm_step: &r2sym::VmStepSummary) -> String {
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
    format!(
        "r2dec semantic summary: vm_summary for {} ({} @ 0x{:x}, loop_header=0x{:x}, selector={}, targets={}, redispatch={}, exact_transfers={}, likely_transfers={}, heuristic_transfers={}, redispatch_transfers={}, returning_transfers={}, selector_updates={}, exact_exit_guards={}, residual_guards={}, residual_memory={}, total_reads={}, total_writes={}, read_effects={}, write_effects={}, state_inputs=[{}], state_outputs=[{}], handlers={})",
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
        inputs,
        outputs,
        handler_preview,
    )
}

fn render_vm_signature(type_facts: &FunctionTypeFacts, func_name: &str) -> String {
    let Some(signature) = type_facts.merged_signature.as_ref() else {
        return format!("void {func_name}(void)");
    };
    let ret_ty = signature
        .ret_type
        .as_ref()
        .map(crate::type_like_to_ctype)
        .unwrap_or(crate::CType::Void);
    let params = if signature.params.is_empty() {
        "void".to_string()
    } else {
        signature
            .params
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let ty = param
                    .ty
                    .as_ref()
                    .map(crate::type_like_to_ctype)
                    .unwrap_or(crate::CType::Unknown);
                let name = if param.name.trim().is_empty() {
                    format!("arg{}", idx + 1)
                } else {
                    param.name.clone()
                };
                format!("{ty} {name}")
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!("{ret_ty} {func_name}({params})")
}

fn render_vm_memory_condition(effect: &r2sym::VmMemoryCondition) -> String {
    let binding = effect.binding.as_deref().unwrap_or("value");
    let range = if effect.offset_lo == effect.offset_hi {
        format!("{:+#x}", effect.offset_lo)
    } else {
        format!("{:+#x}..{:+#x}", effect.offset_lo, effect.offset_hi)
    };
    let value = effect
        .value_expr
        .as_deref()
        .or(Some(effect.expr.as_str()))
        .unwrap_or(binding);
    format!(
        "{}[{:?} {}] size={} {}",
        effect.region.name, effect.region.kind, range, effect.size, value
    )
}

fn render_vm_case_block(
    out: &mut String,
    vm_step: &r2sym::VmStepSummary,
    target: u64,
    default_emitted: &mut bool,
) {
    let case_values = vm_step
        .case_values_by_target
        .get(&target)
        .cloned()
        .unwrap_or_default();
    if case_values.is_empty() && vm_step.default_target == Some(target) {
        let _ = writeln!(out, "    default:");
        *default_emitted = true;
    } else if case_values.is_empty() {
        if !*default_emitted {
            let _ = writeln!(out, "    default:");
            *default_emitted = true;
        } else {
            let _ = writeln!(
                out,
                "    /* unlabeled handler 0x{:x} omitted from switch surface */",
                target
            );
            return;
        }
    } else {
        for value in case_values {
            let _ = writeln!(out, "    case 0x{value:x}:");
        }
    }

    let region_blocks = vm_step
        .handler_regions
        .get(&target)
        .map(|blocks| crate::format_vm_target_list(blocks))
        .unwrap_or_else(|| "[]".to_string());
    let _ = writeln!(
        out,
        "        /* handler 0x{:x} blocks={} */",
        target, region_blocks
    );

    let mut emitted_body = false;
    for transfer in vm_step
        .transfers
        .iter()
        .filter(|transfer| transfer.handler_target == target)
    {
        for update in transfer.state_updates.iter().take(4) {
            let _ = writeln!(out, "        {} = {};", update.output, update.expr);
            emitted_body = true;
        }
        if let Some(selector_update) = transfer.selector_update.as_ref() {
            let _ = writeln!(
                out,
                "        {} = {};",
                selector_update.output, selector_update.expr
            );
            emitted_body = true;
        }
        for guard in transfer.exit_guards.iter().take(3) {
            let _ = writeln!(
                out,
                "        /* if ({}) -> 0x{:x} [{:?}] */",
                guard.guard.expr,
                guard.target,
                guard.guard.confidence()
            );
            emitted_body = true;
        }
        for effect in transfer.memory_reads.iter().take(2) {
            let _ = writeln!(
                out,
                "        /* read {} [{:?}] */",
                render_vm_memory_condition(effect),
                effect.confidence()
            );
            emitted_body = true;
        }
        for effect in transfer.memory_writes.iter().take(2) {
            let _ = writeln!(
                out,
                "        /* write {} [{:?}] */",
                render_vm_memory_condition(effect),
                effect.confidence()
            );
            emitted_body = true;
        }
        if transfer.redispatch {
            let _ = writeln!(out, "        /* redispatch */");
            emitted_body = true;
        }
        if transfer.may_return {
            let _ = writeln!(out, "        /* may return */");
            emitted_body = true;
        }
        if transfer.truncated {
            let _ = writeln!(out, "        /* truncated handler summary */");
            emitted_body = true;
        }
    }

    if !emitted_body {
        let _ = writeln!(out, "        /* no exact handler body recovered */");
    }
    let _ = writeln!(out, "        break;");
}

pub(crate) fn render_vm_semantic_summary(
    func_name: &str,
    type_facts: &FunctionTypeFacts,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<String> {
    let vm_body = semantic_artifact.vm_body()?;
    let vm_step = vm_body
        .step_summary
        .as_ref()
        .or(vm_body.transfer_summary.as_ref())?;
    let selector = vm_step.selector.as_deref().unwrap_or("dispatch_selector");
    let mut out = String::new();

    let _ = writeln!(out, "{} {{", render_vm_signature(type_facts, func_name));
    let _ = writeln!(
        out,
        "    /* {} */",
        vm_summary_stats_comment(func_name, vm_step)
    );
    if !vm_step.state_inputs.is_empty() || !vm_step.state_outputs.is_empty() {
        let _ = writeln!(
            out,
            "    /* state_inputs=[{}] state_outputs=[{}] */",
            if vm_step.state_inputs.is_empty() {
                "none".to_string()
            } else {
                vm_step.state_inputs.join(", ")
            },
            if vm_step.state_outputs.is_empty() {
                "none".to_string()
            } else {
                vm_step.state_outputs.join(", ")
            },
        );
    }
    let _ = writeln!(out, "    switch ({selector}) {{");
    let mut default_emitted = false;
    for target in &vm_step.dispatch_targets {
        render_vm_case_block(&mut out, vm_step, *target, &mut default_emitted);
    }
    if !default_emitted {
        let _ = writeln!(out, "    default:");
        if let Some(default_target) = vm_step.default_target {
            let _ = writeln!(out, "        /* default_target=0x{:x} */", default_target);
        } else {
            let _ = writeln!(out, "        /* no default target recovered */");
        }
        let _ = writeln!(out, "        break;");
    }
    let _ = writeln!(out, "    }}");
    let _ = writeln!(out, "}}");
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
