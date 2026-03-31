use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use r2il::ArchSpec;
use r2ssa::{InterprocFunctionId, SsaArtifact};
use z3::Context;

use crate::sim::{
    DerivedSummaryDiagnostics, PreparedFunctionScope, SummaryProfile, SummaryRegistry,
};

use super::artifact::{
    CompiledFunctionSemantics, CompiledSemanticArtifact, ResidualReason, SemanticCapability,
    SemanticMode,
};
use super::cache::{
    SemanticCompilationResult, SemanticSeedMode, cache_insert_bounded,
    coarse_large_slice_cache_key, lookup_semantic_cache, semantic_cache_key,
};
use super::classify::classify_slice;
use super::facts::{
    SymbolicFunctionFacts, collect_large_cfg_symbolic_function_facts_with_limit,
    collect_symbolic_function_facts_with_derived,
    collect_symbolic_function_facts_with_scope_and_profile,
};
use super::vm::{build_vm_step_summary, classify_interpreter_like};

fn residual_reasons(
    diagnostics: &DerivedSummaryDiagnostics,
    facts: &SymbolicFunctionFacts,
    interpreter_detected: bool,
    vm_step_ready: bool,
) -> Vec<ResidualReason> {
    let mut reasons = Vec::new();
    if facts.diagnostics.skipped_missing_arch {
        reasons.push(ResidualReason::MissingArch);
    }
    if facts.diagnostics.skipped_large_cfg {
        reasons.push(ResidualReason::LargeCfg);
    }
    if diagnostics.budget_exhausted > 0 {
        reasons.push(ResidualReason::SummaryBudgetExhausted);
    }
    if diagnostics.scc_budget_exhausted > 0 {
        reasons.push(ResidualReason::SccBudgetExhausted);
    }
    if interpreter_detected && !vm_step_ready {
        reasons.push(ResidualReason::InterpreterRequiresStepSummary);
    }
    reasons
}

fn semantic_mode_for(
    helper_functions: usize,
    derived_summaries: usize,
    diagnostics: &DerivedSummaryDiagnostics,
    facts: &SymbolicFunctionFacts,
    interpreter_detected: bool,
    vm_step_ready: bool,
) -> SemanticMode {
    if vm_step_ready {
        return SemanticMode::VmSummary;
    }
    if interpreter_detected {
        return SemanticMode::Residual;
    }
    if derived_summaries > 0 && !facts.diagnostics.skipped_large_cfg {
        return SemanticMode::Compiled;
    }
    if helper_functions > 0
        || facts.diagnostics.skipped_large_cfg
        || diagnostics.budget_exhausted > 0
        || diagnostics.scc_budget_exhausted > 0
    {
        return SemanticMode::Residual;
    }
    if facts.diagnostics.skipped_missing_arch {
        return SemanticMode::Residual;
    }
    SemanticMode::Raw
}

fn semantic_capability(mode: SemanticMode, facts: &SymbolicFunctionFacts) -> SemanticCapability {
    let has_bounded_branch_facts = !facts.branch_facts.is_empty();
    let has_actionable_branch_frontier = facts
        .branch_facts
        .iter()
        .any(|fact| fact.true_compiled.is_some() || fact.false_compiled.is_some());
    let has_actionable_control_islands = facts
        .control_islands
        .iter()
        .any(|island| island.actionable_compiled_condition().is_some());
    let large_cfg_actionable_decompile = facts.diagnostics.skipped_large_cfg
        && (has_actionable_branch_frontier || has_actionable_control_islands)
        && facts.branch_facts.len() <= 4;
    match mode {
        SemanticMode::Raw | SemanticMode::Compiled => SemanticCapability {
            query_ready: true,
            type_ready: true,
            decompile_ready: true,
        },
        SemanticMode::Residual => SemanticCapability {
            query_ready: true,
            type_ready: !facts.diagnostics.skipped_large_cfg || has_bounded_branch_facts,
            decompile_ready: large_cfg_actionable_decompile,
        },
        SemanticMode::VmSummary => SemanticCapability {
            query_ready: true,
            type_ready: true,
            decompile_ready: false,
        },
    }
}

fn bounded_large_cfg_branch_limit(func: &SsaArtifact) -> usize {
    let summary = func.function().cfg_risk_summary();
    if summary.block_count > 160 || summary.back_edge_count > 8 || summary.switch_block_count > 8 {
        2
    } else if summary.block_count > 96 || summary.back_edge_count > 6 {
        3
    } else {
        4
    }
}

fn bounded_large_cfg_helper_limit(func: &SsaArtifact) -> usize {
    let summary = func.function().cfg_risk_summary();
    if summary.block_count > 160 || summary.back_edge_count > 8 || summary.switch_block_count > 8 {
        1
    } else if summary.block_count > 96 || summary.back_edge_count > 6 {
        2
    } else {
        3
    }
}

fn bounded_large_cfg_scope(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
) -> Option<PreparedFunctionScope> {
    let scope = scope?;
    let root = scope.root()?.clone();
    let helper_limit = bounded_large_cfg_helper_limit(func);
    if helper_limit == 0 {
        return PreparedFunctionScope::new(scope.root_id().0, vec![root]);
    }

    let mut functions = vec![root];
    let mut seen = BTreeSet::from([scope.root_id()]);

    for call in func.call_sites().by_id.values() {
        if functions.len().saturating_sub(1) >= helper_limit {
            break;
        }
        let Some(target) = call.direct_target else {
            continue;
        };
        let function_id = InterprocFunctionId(target);
        if !seen.insert(function_id) {
            continue;
        }
        let Some(helper) = scope.functions().get(&function_id).cloned() else {
            continue;
        };
        functions.push(helper);
    }

    PreparedFunctionScope::new(scope.root_id().0, functions)
}

fn compile_function_semantics_uncached(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> CompiledSemanticArtifact {
    let closure_functions = scope.map(|scope| scope.functions().len()).unwrap_or(1);
    let helper_functions = scope
        .map(|scope| scope.helper_functions().count())
        .unwrap_or(0);
    let mut derived_diagnostics = DerivedSummaryDiagnostics::default();
    let mut derived_summaries = 0usize;
    let mut symbolic_facts = SymbolicFunctionFacts::default();
    let interpreter = classify_interpreter_like(func);
    let vm_step = interpreter
        .as_ref()
        .and_then(|dispatch| build_vm_step_summary(func, dispatch));
    let vm_transfer = vm_step.clone();

    if let Some(arch) = arch {
        let cfg_summary = func.function().cfg_risk_summary();
        let skip_expensive_branch_compilation = cfg_summary.block_count > 48
            || cfg_summary.back_edge_count > 4
            || cfg_summary.switch_block_count > 4;

        if skip_expensive_branch_compilation {
            if interpreter.is_none() {
                let bounded_scope = bounded_large_cfg_scope(func, scope);
                symbolic_facts = collect_large_cfg_symbolic_function_facts_with_limit(
                    ctx,
                    func,
                    bounded_scope.as_ref(),
                    arch,
                    symbol_map,
                    summary_profile,
                    bounded_large_cfg_branch_limit(func),
                );
                symbolic_facts.diagnostics.skipped_large_cfg = true;
            } else {
                symbolic_facts.diagnostics.skipped_large_cfg = true;
            }

            let mode = semantic_mode_for(
                helper_functions,
                derived_summaries,
                &derived_diagnostics,
                &symbolic_facts,
                interpreter.is_some(),
                vm_transfer.is_some(),
            );
            let slice_class = classify_slice(
                func,
                helper_functions,
                &derived_diagnostics,
                interpreter.as_ref(),
            );

            return CompiledSemanticArtifact {
                mode,
                slice_class,
                capability: semantic_capability(mode, &symbolic_facts),
                residual_reasons: residual_reasons(
                    &derived_diagnostics,
                    &symbolic_facts,
                    interpreter.is_some(),
                    vm_step.is_some(),
                ),
                closure_functions,
                helper_functions,
                derived_summaries,
                derived_diagnostics,
                symbolic_facts,
                interpreter,
                vm_step,
                vm_transfer,
                cache_hit: false,
            };
        }

        if let Some(scope) = scope
            && let Some(registry) = SummaryRegistry::with_profile_for_arch(arch, summary_profile)
        {
            let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
            derived_summaries = derived.summaries.len();
            derived_diagnostics = derived.diagnostics.clone();
            symbolic_facts = collect_symbolic_function_facts_with_derived(
                ctx,
                func,
                Some(scope),
                arch,
                symbol_map,
                summary_profile,
                &registry,
                &derived,
            );
        } else {
            symbolic_facts = collect_symbolic_function_facts_with_scope_and_profile(
                ctx,
                func,
                None,
                Some(arch),
                symbol_map,
                summary_profile,
            );
        }
    } else {
        symbolic_facts.diagnostics.skipped_missing_arch = true;
    }
    let mode = semantic_mode_for(
        helper_functions,
        derived_summaries,
        &derived_diagnostics,
        &symbolic_facts,
        interpreter.is_some(),
        vm_transfer.is_some(),
    );
    let slice_class = classify_slice(
        func,
        helper_functions,
        &derived_diagnostics,
        interpreter.as_ref(),
    );

    CompiledSemanticArtifact {
        mode,
        slice_class,
        capability: semantic_capability(mode, &symbolic_facts),
        residual_reasons: residual_reasons(
            &derived_diagnostics,
            &symbolic_facts,
            interpreter.is_some(),
            vm_step.is_some(),
        ),
        closure_functions,
        helper_functions,
        derived_summaries,
        derived_diagnostics,
        symbolic_facts,
        interpreter,
        vm_step,
        vm_transfer,
        cache_hit: false,
    }
}

pub(crate) fn compile_function_semantics_cached_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> SemanticCompilationResult {
    let key = semantic_cache_key(func, scope, arch, summary_profile, SemanticSeedMode::Static);
    if let Some(existing) = lookup_semantic_cache(&key) {
        return SemanticCompilationResult {
            artifact: existing,
            cache_hit: true,
        };
    }
    let coarse_key = scope.map(|_| {
        coarse_large_slice_cache_key(func.entry, arch, summary_profile, SemanticSeedMode::Static)
    });
    if let Some(coarse_key) = coarse_key.as_ref()
        && let Some(existing) = lookup_semantic_cache(coarse_key)
    {
        return SemanticCompilationResult {
            artifact: existing,
            cache_hit: true,
        };
    }

    let artifact = Arc::new(compile_function_semantics_uncached(
        ctx,
        func,
        scope,
        arch,
        symbol_map,
        summary_profile,
    ));
    let artifact = cache_insert_bounded(key, artifact);
    let should_cache_coarsely = scope.is_some()
        && (matches!(artifact.mode, SemanticMode::VmSummary)
            || artifact.symbolic_facts.diagnostics.skipped_large_cfg);
    let artifact = if should_cache_coarsely {
        let coarse_key =
            coarse_key.expect("coarse large-slice cache key should exist when scope is present");
        cache_insert_bounded(coarse_key, artifact)
    } else {
        artifact
    };
    SemanticCompilationResult {
        artifact,
        cache_hit: false,
    }
}

pub fn compile_function_semantics_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> CompiledFunctionSemantics {
    let result = compile_function_semantics_cached_with_scope(
        ctx,
        func,
        scope,
        arch,
        symbol_map,
        summary_profile,
    );
    let mut artifact = (*result.artifact).clone();
    artifact.cache_hit = result.cache_hit;
    artifact
}

pub fn compile_semantic_artifact_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> CompiledSemanticArtifact {
    compile_function_semantics_with_scope(ctx, func, scope, arch, symbol_map, summary_profile)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use r2il::{
        ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, SwitchCase, SwitchInfo, Varnode,
    };
    use r2ssa::SsaArtifact;
    use z3::Context;

    use super::*;

    const RAX: u64 = 0;

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", RAX, 8));
        arch
    }

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn make_const(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    #[test]
    fn compile_semantics_cache_hits_on_repeat() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let ctx = Context::thread_local();
        let first = compile_function_semantics_cached_with_scope(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );
        let second = compile_function_semantics_cached_with_scope(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );
        assert!(!first.cache_hit);
        assert!(second.cache_hit);
    }

    #[test]
    fn compile_semantics_cache_ignores_scope_display_names() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let scope_a = crate::PreparedFunctionScope::new(
            0x1000,
            vec![crate::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("sym.display_a".to_string()),
                prepared: func.clone(),
            }],
        )
        .expect("scope a");
        let scope_b = crate::PreparedFunctionScope::new(
            0x1000,
            vec![crate::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("dbg.display_b".to_string()),
                prepared: func.clone(),
            }],
        )
        .expect("scope b");
        let ctx = Context::thread_local();

        let first = compile_function_semantics_cached_with_scope(
            &ctx,
            &func,
            Some(&scope_a),
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );
        let second = compile_function_semantics_cached_with_scope(
            &ctx,
            &func,
            Some(&scope_b),
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );

        assert!(!first.cache_hit);
        assert!(second.cache_hit);
    }

    #[test]
    fn interpreter_classifier_marks_switch_loop_vm_summary() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(RAX, 8),
                    src: make_const(1, 8),
                }],
                switch_info: Some(SwitchInfo {
                    switch_addr: 0x1004,
                    min_val: 0,
                    max_val: 4,
                    default_target: Some(0x1018),
                    cases: vec![
                        SwitchCase {
                            value: 0,
                            target: 0x1008,
                        },
                        SwitchCase {
                            value: 1,
                            target: 0x100c,
                        },
                        SwitchCase {
                            value: 2,
                            target: 0x1010,
                        },
                        SwitchCase {
                            value: 3,
                            target: 0x1014,
                        },
                    ],
                }),
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![
                    R2ILOp::IntAdd {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![
                    R2ILOp::IntSub {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                ops: vec![
                    R2ILOp::IntXor {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(0x55, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1014,
                size: 4,
                ops: vec![
                    R2ILOp::IntLeft {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1018,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let ctx = Context::thread_local();
        let artifact = compile_function_semantics_with_scope(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );
        assert_eq!(artifact.mode, SemanticMode::VmSummary);
        assert_eq!(
            artifact.slice_class,
            super::super::artifact::SliceClass::InterpreterSwitch
        );
        assert!(artifact.capability.query_ready);
        assert!(artifact.interpreter.is_some());
        let vm_step = artifact.vm_step.expect("vm step");
        assert_eq!(vm_step.loop_header, 0x1004);
        assert_eq!(vm_step.default_target, Some(0x1018));
        assert_eq!(vm_step.case_values_by_target.get(&0x1008), Some(&vec![0]));
        assert!(!vm_step.handler_state_updates.is_empty());
        assert!(!vm_step.transfers.is_empty());
        assert!(
            vm_step
                .handler_state_updates
                .values()
                .flat_map(|updates| updates.iter())
                .any(|update| update.output.starts_with("RAX_"))
        );
        assert!(
            vm_step
                .transfers
                .iter()
                .any(|transfer| !transfer.case_values.is_empty())
        );
    }

    #[test]
    fn interpreter_without_step_summary_stays_residual() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x2000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2004,
                size: 4,
                ops: vec![],
                switch_info: Some(SwitchInfo {
                    switch_addr: 0x2004,
                    min_val: 0,
                    max_val: 4,
                    default_target: Some(0x2018),
                    cases: vec![
                        SwitchCase {
                            value: 0,
                            target: 0x2008,
                        },
                        SwitchCase {
                            value: 1,
                            target: 0x200c,
                        },
                        SwitchCase {
                            value: 2,
                            target: 0x2010,
                        },
                        SwitchCase {
                            value: 3,
                            target: 0x2014,
                        },
                    ],
                }),
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2008,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x200c,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2010,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2014,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2018,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let ctx = Context::thread_local();
        let artifact = compile_function_semantics_with_scope(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );
        assert_eq!(artifact.mode, SemanticMode::Residual);
        assert!(artifact.interpreter.is_some());
        assert!(artifact.vm_step.is_none());
        assert!(
            artifact
                .residual_reasons
                .contains(&ResidualReason::InterpreterRequiresStepSummary)
        );
    }

    #[test]
    fn vm_step_summary_tracks_case_values_and_handler_regions() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x3000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x3004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3004,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(RAX, 8),
                    src: make_const(1, 8),
                }],
                switch_info: Some(SwitchInfo {
                    switch_addr: 0x3004,
                    min_val: 0,
                    max_val: 4,
                    default_target: Some(0x3018),
                    cases: vec![
                        SwitchCase {
                            value: 0,
                            target: 0x3008,
                        },
                        SwitchCase {
                            value: 1,
                            target: 0x300c,
                        },
                        SwitchCase {
                            value: 2,
                            target: 0x3010,
                        },
                        SwitchCase {
                            value: 3,
                            target: 0x3014,
                        },
                    ],
                }),
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3008,
                size: 4,
                ops: vec![
                    R2ILOp::Load {
                        dst: make_reg(RAX, 8),
                        space: SpaceId::Ram,
                        addr: make_reg(RAX, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x3004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x300c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(RAX, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3010,
                size: 4,
                ops: vec![
                    R2ILOp::IntAdd {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x3004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3014,
                size: 4,
                ops: vec![
                    R2ILOp::IntSub {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x3004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x3018,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x3004, 8),
                    cond: make_reg(RAX, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x301c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(RAX, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let ctx = Context::thread_local();
        let artifact = compile_function_semantics_with_scope(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );

        let vm_step = artifact.vm_step.expect("vm step summary");
        assert_eq!(artifact.mode, SemanticMode::VmSummary);
        assert!(artifact.capability.query_ready);
        assert_eq!(vm_step.loop_header, 0x3004);
        assert_eq!(vm_step.dispatch_header, 0x3004);
        assert_eq!(vm_step.default_target, Some(0x3018));
        assert_eq!(vm_step.case_values_by_target.get(&0x3008), Some(&vec![0]));
        assert_eq!(vm_step.case_values_by_target.get(&0x300c), Some(&vec![1]));
        assert_eq!(vm_step.case_values_by_target.get(&0x3010), Some(&vec![2]));
        assert_eq!(vm_step.case_values_by_target.get(&0x3014), Some(&vec![3]));
        assert_eq!(vm_step.handler_regions.get(&0x3008), Some(&vec![0x3008]));
        assert_eq!(vm_step.handler_memory_reads.get(&0x3008), Some(&1));
        assert_eq!(vm_step.handler_memory_writes.get(&0x3008), Some(&0));
        assert!(
            vm_step
                .handler_memory_read_effects
                .get(&0x3008)
                .is_some_and(|effects| !effects.is_empty())
        );
        assert!(
            vm_step
                .handler_state_updates
                .get(&0x3008)
                .is_some_and(|updates| !updates.is_empty())
        );
        assert!(vm_step.redispatch_handlers.contains(&0x3008));
        assert!(vm_step.redispatch_handlers.contains(&0x3010));
        assert!(vm_step.redispatch_handlers.contains(&0x3014));
        assert!(vm_step.redispatch_handlers.contains(&0x3018));
        assert!(vm_step.returning_handlers.contains(&0x300c));
        assert!(vm_step.returning_handlers.contains(&0x3018));
        assert_eq!(vm_step.handler_conditional_branches.get(&0x3018), Some(&1));
        assert_eq!(
            vm_step.handler_regions.get(&0x3018),
            Some(&vec![0x3018, 0x301c])
        );
        assert_eq!(
            vm_step.handler_exit_targets.get(&0x3018),
            Some(&vec![0x3004])
        );
        assert!(
            vm_step
                .handler_exit_guards
                .get(&0x3018)
                .is_some_and(|guards| !guards.is_empty())
        );
        assert!(vm_step.truncated_handlers.is_empty());
        assert_eq!(vm_step.transfers.len(), 5);
        assert!(
            vm_step
                .transfers
                .iter()
                .any(|transfer| transfer.handler_target == 0x3008 && transfer.redispatch)
        );
        assert!(
            vm_step
                .transfers
                .iter()
                .any(|transfer| !transfer.state_updates.is_empty())
        );
        assert!(
            vm_step
                .transfers
                .iter()
                .any(|transfer| !transfer.exit_guards.is_empty())
        );
        assert!(
            vm_step
                .transfers
                .iter()
                .any(|transfer| !transfer.memory_reads.is_empty())
        );
    }

    #[test]
    fn large_cfg_shortcuts_to_bounded_residual_artifact() {
        let mut blocks = vec![
            R2ILBlock {
                addr: 0x4000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x4008, 8),
                    cond: make_reg(RAX, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x4004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x400c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x4008,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x400c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut addr = 0x400c;
        for _ in 0..64 {
            blocks.push(R2ILBlock {
                addr,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(addr + 4, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            });
            addr += 4;
        }
        blocks.push(R2ILBlock {
            addr,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_reg(RAX, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        });

        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let ctx = Context::thread_local();
        let artifact = compile_function_semantics_with_scope(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );

        assert_eq!(artifact.mode, SemanticMode::Residual);
        assert!(artifact.symbolic_facts.diagnostics.skipped_large_cfg);
        assert_eq!(artifact.symbolic_facts.branch_facts.len(), 1);
        assert!(artifact.capability.type_ready);
        assert!(artifact.capability.decompile_ready);
        assert_eq!(artifact.symbolic_facts.diagnostics.branches_evaluated, 1);
    }
}
