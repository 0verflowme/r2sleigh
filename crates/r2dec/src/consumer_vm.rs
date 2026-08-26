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
    semantic_artifact: &r2sym::SemanticArtifactReport,
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
    use std::sync::Arc;

    use super::*;
    use r2il::{
        ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
        RegisterProjectionDisposition, RegisterStorage, Varnode,
    };

    fn source_owned_vm_facts() -> r2types::SourceOwnedFunctionFacts {
        let mut arch = ArchSpec::new("x86-64");
        for (name, offset, size) in [
            ("RAX", 0x00, 8),
            ("EAX", 0x00, 4),
            ("RDI", 0x10, 8),
            ("RSI", 0x18, 8),
            ("ESI", 0x18, 4),
            ("RDX", 0x20, 8),
            ("RSP", 0x28, 8),
            ("RIP", 0x30, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        let projection = |written: RegisterStorage,
                          carrier: RegisterStorage,
                          size_bits: u64| RegisterProjection {
            written,
            disposition: RegisterProjectionDisposition::Bound {
                carrier,
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits,
                },
            },
        };
        arch.register_projections = vec![
            projection(
                RegisterStorage { offset: 0, size: 8 },
                RegisterStorage { offset: 0, size: 8 },
                64,
            ),
            projection(
                RegisterStorage { offset: 0, size: 4 },
                RegisterStorage { offset: 0, size: 8 },
                32,
            ),
            projection(
                RegisterStorage {
                    offset: 0x10,
                    size: 8,
                },
                RegisterStorage {
                    offset: 0x10,
                    size: 8,
                },
                64,
            ),
            projection(
                RegisterStorage {
                    offset: 0x18,
                    size: 8,
                },
                RegisterStorage {
                    offset: 0x18,
                    size: 8,
                },
                64,
            ),
            projection(
                RegisterStorage {
                    offset: 0x18,
                    size: 4,
                },
                RegisterStorage {
                    offset: 0x18,
                    size: 8,
                },
                32,
            ),
            projection(
                RegisterStorage {
                    offset: 0x20,
                    size: 8,
                },
                RegisterStorage {
                    offset: 0x20,
                    size: 8,
                },
                64,
            ),
            projection(
                RegisterStorage {
                    offset: 0x28,
                    size: 8,
                },
                RegisterStorage {
                    offset: 0x28,
                    size: 8,
                },
                64,
            ),
            projection(
                RegisterStorage {
                    offset: 0x30,
                    size: 8,
                },
                RegisterStorage {
                    offset: 0x30,
                    size: 8,
                },
                64,
            ),
        ];
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x100, 1),
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(0x10, 8),
        });
        block.push(R2ILOp::IntSExt {
            dst: Varnode::unique(0x108, 8),
            src: Varnode::unique(0x100, 1),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x110, 4),
            src: Varnode::register(0x18, 4),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0x00, 4),
            src: Varnode::constant(0, 4),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        });

        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let full64 = r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64);
        let low32 = r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::LowBits, 0, 32);
        let type_graph = r2ssa::SourceTypeGraph::new(
            [
                r2ssa::SourceType::new(0, r2ssa::SourceTypeKind::SignedInteger, 8, 8),
                r2ssa::SourceType::new(
                    1,
                    r2ssa::SourceTypeKind::Pointer { target_type_id: 0 },
                    64,
                    64,
                ),
                r2ssa::SourceType::new(2, r2ssa::SourceTypeKind::SignedInteger, 32, 32),
                r2ssa::SourceType::new(3, r2ssa::SourceTypeKind::SignedInteger, 64, 64),
            ],
            [],
        )
        .expect("exact VM signature types");
        let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
            b"vm-signature-certified-parameters".to_vec(),
            "sysv64",
            [
                r2ssa::SourceAbiParameterSpec::new(0, storage(0x10)),
                r2ssa::SourceAbiParameterSpec::new(1, storage(0x18)),
                r2ssa::SourceAbiParameterSpec::new(2, storage(0x20)),
            ],
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
            [
                r2ssa::SourceLogicalValue::new(1, full64),
                r2ssa::SourceLogicalValue::new(2, low32),
                r2ssa::SourceLogicalValue::new(3, full64),
            ],
            Some(r2ssa::SourceLogicalValue::new(2, low32)),
            Some(type_graph),
        )
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .expect("exact VM source interface");
        let source = Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
                .expect("prepared VM source owner")
                .with_name("tiny_vm_dispatch"),
        );
        let request = r2types::TypeWritebackAnalysisRequest::new(
            Arc::clone(&source),
            r2types::ParsedExternalContext::default(),
        )
        .expect("matching VM source assumptions");
        let owner = r2types::build_source_owned_type_writeback_analysis(request)
            .expect("source-owned VM type analysis")
            .finalize_for_decompile(r2types::DecompileFinalization {
                kind: r2types::DecompileRouteKind::Standard,
                reason: "test VM signature".to_string(),
                fallback_comment: None,
            })
            .expect("source-owned VM decompile facts");
        assert!(owner.shares_source(&source));
        owner
    }

    #[test]
    fn vm_signature_keeps_only_certified_generic_parameters() {
        let source_owned = source_owned_vm_facts();

        assert_eq!(
            vm_summary_signature_comment("tiny_vm_dispatch", source_owned.report()).as_deref(),
            Some("int32_t tiny_vm_dispatch(int8_t* arg0, int32_t arg1)")
        );
    }
}
