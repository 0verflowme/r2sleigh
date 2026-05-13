use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use r2il::ArchSpec;
use r2ssa::{FunctionSemanticSummary, InterprocFunctionId, SsaArtifact};
use z3::Context;

use crate::replay::{ReplaySeed, stable_replay_seed_fingerprint};
use crate::sim::{
    DerivedSummaryDiagnostics, PreparedFunctionScope, SummaryProfile, SummaryRegistry,
};

use super::artifact::{ResidualReason, SemanticArtifact, SemanticArtifactBody};
use super::cache::{
    SemanticCompilationResult, SemanticSeedMode, cache_insert_bounded,
    coarse_large_slice_cache_key, lookup_semantic_cache, semantic_cache_key,
};
use super::classify::classify_slice;
use super::facts::{
    CollectedNativeSemanticRegions, SymbolicFunctionFactDiagnostics,
    collect_canonical_semantic_regions_with_derived,
    collect_canonical_semantic_regions_with_scope_and_profile,
    collect_large_cfg_canonical_semantic_regions_with_limit,
};
use super::region::{
    ArtifactGranularity, ExecutionModel, NativeArtifactBody, NativeFunctionSummary,
    NativeWorkerSummary, RefinementStage, SemanticArtifactDiagnostics,
};
use super::vm::{build_vm_step_summary, classify_interpreter_like};

fn residual_reasons(
    diagnostics: &DerivedSummaryDiagnostics,
    fact_diagnostics: &SymbolicFunctionFactDiagnostics,
) -> Vec<ResidualReason> {
    let mut reasons = Vec::new();
    if fact_diagnostics.skipped_missing_arch {
        reasons.push(ResidualReason::MissingArch);
    }
    if fact_diagnostics.skipped_large_cfg {
        reasons.push(ResidualReason::LargeCfg);
    }
    if diagnostics.budget_exhausted > 0 {
        reasons.push(ResidualReason::SummaryBudgetExhausted);
    }
    if diagnostics.scc_budget_exhausted > 0 {
        reasons.push(ResidualReason::SccBudgetExhausted);
    }
    reasons
}

fn normalized_residual_reasons(
    suppress_large_cfg_reason: bool,
    reasons: Vec<ResidualReason>,
) -> Vec<ResidualReason> {
    if suppress_large_cfg_reason {
        reasons
            .into_iter()
            .filter(|reason| !matches!(reason, ResidualReason::LargeCfg))
            .collect()
    } else {
        reasons
    }
}

fn semantic_stage_for(
    helper_functions: usize,
    derived_summaries: usize,
    diagnostics: &DerivedSummaryDiagnostics,
    collected: &CollectedNativeSemanticRegions,
    vm_step_ready: bool,
) -> RefinementStage {
    if vm_step_ready {
        return RefinementStage::Compiled;
    }
    if derived_summaries > 0 && !collected.diagnostics.skipped_large_cfg {
        return RefinementStage::Compiled;
    }
    if collected.diagnostics.skipped_large_cfg && has_island_compiled_semantics(collected) {
        return RefinementStage::Compiled;
    }
    if helper_functions > 0
        || collected.diagnostics.skipped_large_cfg
        || diagnostics.budget_exhausted > 0
        || diagnostics.scc_budget_exhausted > 0
    {
        return RefinementStage::Residual;
    }
    if collected.diagnostics.skipped_missing_arch {
        return RefinementStage::Residual;
    }
    RefinementStage::Raw
}

fn has_island_compiled_semantics(collected: &CollectedNativeSemanticRegions) -> bool {
    collected
        .regions
        .values()
        .any(|region| region.supports_guarded_structuring())
}

fn semantic_granularity_for(
    stage: RefinementStage,
    execution: ExecutionModel,
    regions: &std::collections::BTreeMap<super::region::RegionKey, super::region::SemanticRegion>,
    has_island_compiled_regions: bool,
) -> ArtifactGranularity {
    if matches!(execution, ExecutionModel::Vm) {
        return ArtifactGranularity::SummaryOnly;
    }
    if has_island_compiled_regions {
        return ArtifactGranularity::Regioned;
    }
    if matches!(stage, RefinementStage::Residual) && !regions.is_empty() {
        ArtifactGranularity::Regioned
    } else {
        ArtifactGranularity::WholeFunction
    }
}

const SUMMARY_DENSE_WORKER_ISLAND_MIN: usize = 16;

fn has_named_worker_family(summaries: &[NativeWorkerSummary]) -> bool {
    summaries.iter().any(|summary| {
        matches!(
            summary.kind,
            crate::NativeWorkerSummaryKind::ProgramOrchestrator
                | crate::NativeWorkerSummaryKind::DiagnosticWrapper
                | crate::NativeWorkerSummaryKind::FormatArgumentFetch
                | crate::NativeWorkerSummaryKind::FileTransfer
                | crate::NativeWorkerSummaryKind::StringScan
                | crate::NativeWorkerSummaryKind::HashFold
                | crate::NativeWorkerSummaryKind::TableWalk
                | crate::NativeWorkerSummaryKind::PathWalk
                | crate::NativeWorkerSummaryKind::DirectoryTraversal
                | crate::NativeWorkerSummaryKind::RecordStream
                | crate::NativeWorkerSummaryKind::FieldSelection
                | crate::NativeWorkerSummaryKind::OutputStream
                | crate::NativeWorkerSummaryKind::FormatRender
                | crate::NativeWorkerSummaryKind::MetadataProbe
                | crate::NativeWorkerSummaryKind::SortMerge
                | crate::NativeWorkerSummaryKind::NumericTransform
                | crate::NativeWorkerSummaryKind::Parser
        )
    })
}

pub fn compile_summary_dense_worker_artifact_from_interproc_summary(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    summary: &FunctionSemanticSummary,
) -> Option<SemanticArtifact> {
    let worker_summaries =
        super::native_worker::summaries_from_interproc_summary_unbounded(func.entry, summary);
    let worker_summaries = super::native_worker::bounded_worker_summaries(worker_summaries);
    let named_worker_family = has_named_worker_family(&worker_summaries);
    if worker_summaries.len() < SUMMARY_DENSE_WORKER_ISLAND_MIN && !named_worker_family {
        return None;
    }

    let cfg = func.function().cfg_risk_summary();
    if cfg.loop_count == 0
        && cfg.back_edge_count == 0
        && cfg.block_count <= 64
        && !named_worker_family
    {
        return None;
    }

    let helper_functions = scope
        .map(|scope| scope.helper_functions().count())
        .unwrap_or(summary.direct_callees.len());
    let derived_diagnostics = DerivedSummaryDiagnostics::default();
    let slice_class = classify_slice(func, helper_functions, &derived_diagnostics, None, false);
    let slice_class = if named_worker_family
        && !matches!(
            slice_class,
            crate::SliceClass::Worker | crate::SliceClass::GenericLarge
        ) {
        crate::SliceClass::Worker
    } else {
        slice_class
    };
    if !matches!(
        slice_class,
        crate::SliceClass::Worker | crate::SliceClass::GenericLarge
    ) {
        return None;
    }

    let closure_functions = scope.map(|scope| scope.functions().len()).unwrap_or(1);
    SemanticArtifact {
        stage: RefinementStage::Compiled,
        granularity: ArtifactGranularity::SummaryOnly,
        execution: ExecutionModel::Native,
        body: SemanticArtifactBody::Native(NativeArtifactBody {
            summary: NativeFunctionSummary {
                slice_class,
                role_identity: super::native_worker::role_identity_from_worker_summaries(
                    summary.name.as_deref(),
                    &worker_summaries,
                ),
                closure_functions,
                helper_functions,
                derived_summaries: 0,
                derived_diagnostics,
                region_summaries: Vec::new(),
                worker_summaries,
            },
            regions: Default::default(),
        }),
        diagnostics: SemanticArtifactDiagnostics {
            branches_evaluated: 0,
            branches_pruned: 0,
            branches_unknown: 0,
            skipped_missing_arch: false,
            skipped_large_cfg: false,
            residual_reasons: Vec::new(),
            interpreter: None,
            ambiguous_targets: Vec::new(),
            cache_hit: false,
        },
    }
    .normalized()
    .into()
}

pub fn compile_named_native_worker_summary_artifact(
    summary: &FunctionSemanticSummary,
    skipped_large_cfg: bool,
) -> Option<SemanticArtifact> {
    if !summary
        .name
        .as_deref()
        .is_some_and(super::native_worker::has_native_worker_summary_family)
    {
        return None;
    }
    let worker_summaries =
        super::native_worker::summaries_from_interproc_summary_unbounded(summary.id.0, summary);
    let worker_summaries = super::native_worker::bounded_worker_summaries(worker_summaries);
    let named_worker_family = has_named_worker_family(&worker_summaries);
    if worker_summaries.is_empty() || !named_worker_family {
        return None;
    }
    let derived_diagnostics = DerivedSummaryDiagnostics::default();
    let collected = CollectedNativeSemanticRegions {
        regions: Default::default(),
        diagnostics: SymbolicFunctionFactDiagnostics {
            skipped_large_cfg,
            ..SymbolicFunctionFactDiagnostics::default()
        },
        region_summaries: Vec::new(),
        worker_summaries,
    };
    Some(build_semantic_artifact(BuildSemanticArtifactInput {
        stage: RefinementStage::Compiled,
        granularity: ArtifactGranularity::SummaryOnly,
        execution: ExecutionModel::Native,
        suppress_large_cfg_reason: true,
        role_name_hint: summary.name.clone(),
        slice_class: crate::SliceClass::Worker,
        closure_functions: 1,
        helper_functions: summary.direct_callees.len(),
        derived_summaries: 0,
        derived_diagnostics,
        collected,
        interpreter: None,
        vm_step: None,
        vm_transfer: None,
    }))
}

pub fn compile_native_worker_summary_artifact(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    summary: Option<&FunctionSemanticSummary>,
    skipped_large_cfg: bool,
) -> Option<SemanticArtifact> {
    let mut worker_summaries = Vec::new();
    if let Some(summary) = summary {
        worker_summaries.extend(
            super::native_worker::summaries_from_interproc_summary_unbounded(func.entry, summary),
        );
    }
    let has_primary_interproc_summary = worker_summaries
        .iter()
        .any(NativeWorkerSummary::is_primary_render_summary);
    let cfg_summary = func.function().cfg_risk_summary();
    let op_count = func
        .function()
        .blocks()
        .map(|block| block.ops.len())
        .sum::<usize>();
    let cheap_native_worker_classification =
        !skipped_large_cfg || (cfg_summary.block_count <= 64 && op_count <= 256);
    if !has_primary_interproc_summary && cheap_native_worker_classification {
        worker_summaries
            .extend(super::native_worker::classify_function_worker_summaries_unbounded(func));
    }
    let worker_summaries = super::native_worker::bounded_worker_summaries(worker_summaries);
    let named_worker_family = has_named_worker_family(&worker_summaries);
    let summary_owned_worker = summary
        .and_then(|summary| summary.name.as_deref())
        .is_some_and(super::native_worker::has_native_worker_summary_family);
    let region_summaries = if summary_owned_worker && has_primary_interproc_summary {
        Vec::new()
    } else {
        super::native_worker::classify_native_region_summaries(func, &worker_summaries)
    };
    if worker_summaries.is_empty() && region_summaries.is_empty() {
        return None;
    }

    let derived_diagnostics = DerivedSummaryDiagnostics::default();
    let helper_functions = scope
        .map(|scope| scope.helper_functions().count())
        .or_else(|| summary.map(|summary| summary.direct_callees.len()))
        .unwrap_or(0);
    let slice_class = classify_slice(func, helper_functions, &derived_diagnostics, None, false);
    let slice_class = if named_worker_family
        && !matches!(
            slice_class,
            crate::SliceClass::Worker | crate::SliceClass::GenericLarge
        ) {
        crate::SliceClass::Worker
    } else {
        slice_class
    };
    let has_primary_summary = worker_summaries
        .iter()
        .any(NativeWorkerSummary::is_primary_render_summary)
        || region_summaries
            .iter()
            .any(crate::NativeRegionSummary::is_primary_render_summary);
    let stage = if has_primary_summary {
        RefinementStage::Compiled
    } else {
        RefinementStage::Residual
    };
    let closure_functions = scope.map(|scope| scope.functions().len()).unwrap_or(1);
    let collected = CollectedNativeSemanticRegions {
        regions: Default::default(),
        diagnostics: SymbolicFunctionFactDiagnostics {
            skipped_large_cfg,
            ..SymbolicFunctionFactDiagnostics::default()
        },
        region_summaries,
        worker_summaries,
    };

    Some(build_semantic_artifact(BuildSemanticArtifactInput {
        stage,
        granularity: ArtifactGranularity::SummaryOnly,
        execution: ExecutionModel::Native,
        suppress_large_cfg_reason: has_primary_summary,
        role_name_hint: summary.and_then(|summary| summary.name.clone()),
        slice_class,
        closure_functions,
        helper_functions,
        derived_summaries: 0,
        derived_diagnostics,
        collected,
        interpreter: None,
        vm_step: None,
        vm_transfer: None,
    }))
}

struct BuildSemanticArtifactInput {
    stage: RefinementStage,
    granularity: ArtifactGranularity,
    execution: ExecutionModel,
    suppress_large_cfg_reason: bool,
    role_name_hint: Option<String>,
    slice_class: crate::SliceClass,
    closure_functions: usize,
    helper_functions: usize,
    derived_summaries: usize,
    derived_diagnostics: DerivedSummaryDiagnostics,
    collected: CollectedNativeSemanticRegions,
    interpreter: Option<super::vm::InterpreterDispatchSummary>,
    vm_step: Option<super::vm::VmStepSummary>,
    vm_transfer: Option<super::vm::VmStepSummary>,
}

fn build_semantic_artifact(input: BuildSemanticArtifactInput) -> SemanticArtifact {
    let BuildSemanticArtifactInput {
        stage,
        granularity,
        execution,
        suppress_large_cfg_reason,
        role_name_hint,
        slice_class,
        closure_functions,
        helper_functions,
        derived_summaries,
        derived_diagnostics,
        collected,
        interpreter,
        vm_step,
        vm_transfer,
    } = input;
    let interpreter_diagnostic = interpreter.clone();
    let role_identity = if matches!(execution, ExecutionModel::Native) {
        super::native_worker::role_identity_from_worker_summaries(
            role_name_hint.as_deref(),
            &collected.worker_summaries,
        )
    } else {
        None
    };
    let body = match execution {
        ExecutionModel::Vm => SemanticArtifactBody::Vm(Box::new(super::region::VmArtifactBody {
            interpreter,
            step_summary: vm_step,
            transfer_summary: vm_transfer,
        })),
        ExecutionModel::Native => SemanticArtifactBody::Native(NativeArtifactBody {
            summary: NativeFunctionSummary {
                slice_class,
                role_identity,
                closure_functions,
                helper_functions,
                derived_summaries,
                derived_diagnostics: derived_diagnostics.clone(),
                region_summaries: collected.region_summaries,
                worker_summaries: collected.worker_summaries,
            },
            regions: collected.regions,
        }),
    };
    let ambiguous_targets = match &body {
        SemanticArtifactBody::Native(body) => body.conflicting_targets(false).into_iter().collect(),
        SemanticArtifactBody::Vm(_) => Vec::new(),
    };
    SemanticArtifact {
        stage,
        granularity,
        execution,
        body,
        diagnostics: SemanticArtifactDiagnostics {
            branches_evaluated: collected.diagnostics.branches_evaluated,
            branches_pruned: collected.diagnostics.branches_pruned,
            branches_unknown: collected.diagnostics.branches_unknown,
            skipped_missing_arch: collected.diagnostics.skipped_missing_arch,
            skipped_large_cfg: collected.diagnostics.skipped_large_cfg,
            residual_reasons: normalized_residual_reasons(
                suppress_large_cfg_reason,
                residual_reasons(&derived_diagnostics, &collected.diagnostics),
            ),
            interpreter: interpreter_diagnostic,
            ambiguous_targets,
            cache_hit: false,
        },
    }
    .normalized()
}

fn bounded_large_cfg_branch_limit(func: &SsaArtifact) -> usize {
    let summary = func.function().cfg_risk_summary();
    let branch_count = func.predicates().predicates.len();
    if summary.block_count > 160
        || branch_count > 160
        || summary.back_edge_count > 8
        || summary.switch_block_count > 8
    {
        2
    } else if summary.block_count > 96 || branch_count > 96 || summary.back_edge_count > 6 {
        3
    } else {
        4
    }
}

fn bounded_large_cfg_helper_limit(func: &SsaArtifact) -> usize {
    let summary = func.function().cfg_risk_summary();
    let branch_count = func.predicates().predicates.len();
    if summary.block_count > 160
        || branch_count > 160
        || summary.back_edge_count > 8
        || summary.switch_block_count > 8
    {
        1
    } else if summary.block_count > 96 || branch_count > 96 || summary.back_edge_count > 6 {
        2
    } else {
        3
    }
}

fn bounded_default_scope(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
) -> Option<PreparedFunctionScope> {
    let scope = scope?;
    let helper_limit = bounded_large_cfg_helper_limit(func).max(4);
    if scope.helper_functions().count() > helper_limit {
        None
    } else {
        scope.with_prepared_root(func)
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

fn bounded_query_scope(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    target_addr: u64,
) -> Option<PreparedFunctionScope> {
    let scope = scope?;
    let target_is_cross_function = scope
        .function_containing_block(target_addr)
        .is_some_and(|function| function.id != scope.root_id());
    let helper_limit = bounded_large_cfg_helper_limit(func);
    let has_many_helpers = scope.helper_functions().count() > helper_limit;

    if !(target_is_cross_function || has_many_helpers) {
        return None;
    }

    bounded_large_cfg_scope(func, Some(scope))
}

fn compile_function_semantics_uncached(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> SemanticArtifact {
    let closure_functions = scope.map(|scope| scope.functions().len()).unwrap_or(1);
    let helper_functions = scope
        .map(|scope| scope.helper_functions().count())
        .unwrap_or(0);
    let mut derived_diagnostics = DerivedSummaryDiagnostics::default();
    let mut derived_summaries = 0usize;
    let mut collected = CollectedNativeSemanticRegions::default();
    let interpreter = classify_interpreter_like(func);
    let vm_step_candidate = interpreter
        .as_ref()
        .and_then(|dispatch| build_vm_step_summary(func, dispatch));
    let vm_step = vm_step_candidate.filter(super::vm::VmStepSummary::has_strong_vm_evidence);
    let vm_transfer = vm_step.clone();
    let vm_step_ready = vm_step.is_some();

    if let Some(arch) = arch {
        let cfg_summary = func.function().cfg_risk_summary();
        let branch_count = func.predicates().predicates.len();
        let skip_expensive_branch_compilation = cfg_summary.block_count > 48
            || branch_count > 48
            || cfg_summary.back_edge_count > 4
            || cfg_summary.switch_block_count > 4;

        if skip_expensive_branch_compilation {
            if !vm_step_ready {
                let bounded_scope = bounded_large_cfg_scope(func, scope);
                collected = collect_large_cfg_canonical_semantic_regions_with_limit(
                    ctx,
                    func,
                    bounded_scope.as_ref(),
                    arch,
                    symbol_map,
                    summary_profile,
                    bounded_large_cfg_branch_limit(func),
                );
            } else {
                collected.diagnostics.skipped_large_cfg = true;
            }

            let execution = if vm_step_ready {
                ExecutionModel::Vm
            } else {
                ExecutionModel::Native
            };
            let stage = semantic_stage_for(
                helper_functions,
                derived_summaries,
                &derived_diagnostics,
                &collected,
                vm_step_ready,
            );
            let has_island_compiled_regions = matches!(execution, ExecutionModel::Native)
                && collected.diagnostics.skipped_large_cfg
                && has_island_compiled_semantics(&collected);
            let granularity = semantic_granularity_for(
                stage,
                execution,
                &collected.regions,
                has_island_compiled_regions,
            );
            let slice_class = classify_slice(
                func,
                helper_functions,
                &derived_diagnostics,
                interpreter.as_ref(),
                vm_step_ready,
            );
            return build_semantic_artifact(BuildSemanticArtifactInput {
                stage,
                granularity,
                execution,
                suppress_large_cfg_reason: matches!(execution, ExecutionModel::Vm)
                    || has_island_compiled_regions,
                role_name_hint: func.function().name.clone(),
                slice_class,
                closure_functions,
                helper_functions,
                derived_summaries,
                derived_diagnostics: derived_diagnostics.clone(),
                collected,
                interpreter: interpreter.clone(),
                vm_step: vm_step.clone(),
                vm_transfer: vm_transfer.clone(),
            });
        }

        if let Some(scope) = scope
            && let Some(registry) = SummaryRegistry::with_profile_for_arch_and_symbols(
                arch,
                symbol_map,
                summary_profile,
            )
        {
            let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
            derived_summaries = derived.summaries.len();
            derived_diagnostics = derived.diagnostics.clone();
            collected = collect_canonical_semantic_regions_with_derived(
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
            collected = collect_canonical_semantic_regions_with_scope_and_profile(
                ctx,
                func,
                None,
                Some(arch),
                symbol_map,
                summary_profile,
            );
        }
    } else {
        collected.diagnostics.skipped_missing_arch = true;
    }
    let execution = if vm_step_ready {
        ExecutionModel::Vm
    } else {
        ExecutionModel::Native
    };
    let stage = semantic_stage_for(
        helper_functions,
        derived_summaries,
        &derived_diagnostics,
        &collected,
        vm_step_ready,
    );
    let has_island_compiled_regions = matches!(execution, ExecutionModel::Native)
        && collected.diagnostics.skipped_large_cfg
        && has_island_compiled_semantics(&collected);
    let granularity = semantic_granularity_for(
        stage,
        execution,
        &collected.regions,
        has_island_compiled_regions,
    );
    let slice_class = classify_slice(
        func,
        helper_functions,
        &derived_diagnostics,
        interpreter.as_ref(),
        vm_step_ready,
    );
    build_semantic_artifact(BuildSemanticArtifactInput {
        stage,
        granularity,
        execution,
        suppress_large_cfg_reason: matches!(execution, ExecutionModel::Vm)
            || has_island_compiled_regions,
        role_name_hint: func.function().name.clone(),
        slice_class,
        closure_functions,
        helper_functions,
        derived_summaries,
        derived_diagnostics: derived_diagnostics.clone(),
        collected,
        interpreter,
        vm_step,
        vm_transfer,
    })
}

fn semantic_seed_identity(replay_seed: Option<&ReplaySeed>) -> (SemanticSeedMode, u64) {
    match replay_seed {
        Some(seed) => (
            SemanticSeedMode::Replay,
            stable_replay_seed_fingerprint(seed),
        ),
        None => (SemanticSeedMode::Static, 0),
    }
}

fn compile_function_semantics_cached_with_scope_impl(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    replay_seed: Option<&ReplaySeed>,
) -> SemanticCompilationResult {
    let (seed_mode, replay_seed_fingerprint) = semantic_seed_identity(replay_seed);
    let key = semantic_cache_key(
        func,
        scope,
        arch,
        summary_profile,
        seed_mode,
        replay_seed_fingerprint,
    );
    if let Some(existing) = lookup_semantic_cache(&key) {
        return SemanticCompilationResult {
            artifact: existing,
            cache_hit: true,
            seed_mode,
            replay_seed_fingerprint,
        };
    }
    let coarse_key = scope.map(|scope| {
        coarse_large_slice_cache_key(
            func.entry,
            scope,
            arch,
            summary_profile,
            seed_mode,
            replay_seed_fingerprint,
        )
    });
    if let Some(coarse_key) = coarse_key.as_ref()
        && let Some(existing) = lookup_semantic_cache(coarse_key)
    {
        return SemanticCompilationResult {
            artifact: existing,
            cache_hit: true,
            seed_mode,
            replay_seed_fingerprint,
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
        && (matches!(artifact.execution, ExecutionModel::Vm)
            || artifact.diagnostics.skipped_large_cfg);
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
        seed_mode,
        replay_seed_fingerprint,
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
    compile_function_semantics_cached_with_scope_impl(
        ctx,
        func,
        scope,
        arch,
        symbol_map,
        summary_profile,
        None,
    )
}

pub fn compile_function_semantics_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> SemanticArtifact {
    let result = compile_function_semantics_cached_with_scope(
        ctx,
        func,
        scope,
        arch,
        symbol_map,
        summary_profile,
    );
    let mut artifact = (*result.artifact).clone();
    artifact.diagnostics.cache_hit = result.cache_hit;
    artifact
}

pub fn compile_function_semantics_with_scope_and_replay_seed(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    replay_seed: Option<&ReplaySeed>,
) -> SemanticArtifact {
    let result = compile_function_semantics_cached_with_scope_impl(
        ctx,
        func,
        scope,
        arch,
        symbol_map,
        summary_profile,
        replay_seed,
    );
    let mut artifact = (*result.artifact).clone();
    artifact.diagnostics.cache_hit = result.cache_hit;
    artifact
}

pub fn compile_semantic_artifact_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> SemanticArtifact {
    compile_function_semantics_with_scope(ctx, func, scope, arch, symbol_map, summary_profile)
}

pub fn compile_semantic_artifact_with_scope_and_replay_seed(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    replay_seed: Option<&ReplaySeed>,
) -> SemanticArtifact {
    compile_function_semantics_with_scope_and_replay_seed(
        ctx,
        func,
        scope,
        arch,
        symbol_map,
        summary_profile,
        replay_seed,
    )
}

pub fn compile_query_semantic_artifact_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    target_addr: u64,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> SemanticArtifact {
    let bounded_scope = bounded_query_scope(func, scope, target_addr);
    compile_function_semantics_with_scope(
        ctx,
        func,
        bounded_scope.as_ref().or(scope),
        arch,
        symbol_map,
        summary_profile,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn compile_query_semantic_artifact_with_scope_and_replay_seed(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    target_addr: u64,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    replay_seed: Option<&ReplaySeed>,
) -> SemanticArtifact {
    let bounded_scope = bounded_query_scope(func, scope, target_addr);
    compile_function_semantics_with_scope_and_replay_seed(
        ctx,
        func,
        bounded_scope.as_ref().or(scope),
        arch,
        symbol_map,
        summary_profile,
        replay_seed,
    )
}

pub fn compile_semantic_artifact_default_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
) -> SemanticArtifact {
    let rebound_scope = bounded_default_scope(func, scope);
    compile_semantic_artifact_with_scope(
        ctx,
        func,
        rebound_scope.as_ref(),
        arch,
        &HashMap::new(),
        SummaryProfile::Default,
    )
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use r2il::{
        ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, SwitchCase, SwitchInfo, Varnode,
    };
    use r2ssa::SsaArtifact;
    use z3::Context;

    use crate::replay::{ReplayRegisterValue, ReplaySeed};

    use super::*;
    const RAX: u64 = 0;
    const RBP: u64 = 8;
    const RDI: u64 = 0x20;

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", RAX, 8));
        arch.add_register(RegisterDef::new("RBP", RBP, 8));
        arch.add_register(RegisterDef::new("RDI", RDI, 8));
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

    fn make_selector_dispatch_ops() -> Vec<R2ILOp> {
        vec![
            R2ILOp::Load {
                dst: make_reg(RAX, 8),
                space: SpaceId::Ram,
                addr: make_reg(RBP, 8),
            },
            R2ILOp::IntMult {
                dst: make_reg(RAX, 8),
                a: make_reg(RAX, 8),
                b: make_const(8, 8),
            },
            R2ILOp::BranchInd {
                target: make_reg(RAX, 8),
            },
        ]
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
    fn summary_dense_worker_artifact_uses_interproc_summaries_without_branch_regions() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1000, 8),
                    cond: make_reg(RAX, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(RAX, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(r2ssa::InterprocFunctionId(0x1000), None);
        for offset in 0..SUMMARY_DENSE_WORKER_ISLAND_MIN {
            summary.memory_effects.push(r2ssa::SummaryMemoryEffect {
                kind: r2ssa::SummaryMemoryEffectKind::Read,
                location: r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Unknown,
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: offset as i64,
                        offset_hi: offset as i64,
                        width: Some(1),
                    }),
                },
            });
        }

        let artifact =
            compile_summary_dense_worker_artifact_from_interproc_summary(&func, None, &summary)
                .expect("summary-dense worker artifact");

        let native = artifact.native_body().expect("native artifact");
        assert_eq!(artifact.stage, RefinementStage::Compiled);
        assert_eq!(artifact.granularity, ArtifactGranularity::SummaryOnly);
        assert_eq!(artifact.diagnostics.branches_evaluated, 0);
        assert!(!artifact.diagnostics.skipped_large_cfg);
        assert!(native.regions.is_empty());
        assert_eq!(
            native.summary.worker_summaries.len(),
            SUMMARY_DENSE_WORKER_ISLAND_MIN
        );
        assert!(matches!(
            artifact.decompile_plan(),
            crate::DecompilePlan::NativeLinear { .. }
        ));
    }

    #[test]
    fn native_worker_summary_artifact_classifies_loops_without_branch_symex() {
        let loaded = Varnode::unique(0x10, 1);
        let pred = Varnode::unique(0x11, 1);
        let blocks = vec![R2ILBlock {
            addr: 0x1100,
            size: 4,
            ops: vec![
                R2ILOp::Load {
                    dst: loaded.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: make_reg(RDI, 8),
                },
                R2ILOp::IntEqual {
                    dst: pred.clone(),
                    a: loaded,
                    b: make_const(0, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1100, 8),
                    cond: pred,
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");

        let artifact =
            compile_native_worker_summary_artifact(&func, None, None, true).expect("summary");

        let native = artifact.native_body().expect("native artifact");
        assert_eq!(artifact.granularity, ArtifactGranularity::SummaryOnly);
        assert_eq!(artifact.diagnostics.branches_evaluated, 0);
        assert!(artifact.diagnostics.skipped_large_cfg);
        assert!(native.has_primary_summary_islands());
        assert!(
            native.summary.worker_summaries.iter().any(|summary| {
                matches!(summary.kind, crate::NativeWorkerSummaryKind::StringScan)
            })
        );
        assert!(matches!(
            artifact.decompile_plan(),
            crate::DecompilePlan::NativeSummaryIslands { .. }
        ));
    }

    #[test]
    fn native_worker_summary_artifact_trusts_primary_interproc_summary() {
        let loaded = Varnode::unique(0x10, 1);
        let pred = Varnode::unique(0x11, 1);
        let blocks = vec![R2ILBlock {
            addr: 0x1100,
            size: 4,
            ops: vec![
                R2ILOp::Load {
                    dst: loaded.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: make_reg(RDI, 8),
                },
                R2ILOp::IntEqual {
                    dst: pred.clone(),
                    a: loaded,
                    b: make_const(0, 1),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1100, 8),
                    cond: pred,
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(func.entry),
            Some("sym.printf_fetchargs".to_string()),
        );

        let artifact = compile_native_worker_summary_artifact(&func, None, Some(&summary), true)
            .expect("named worker summary");

        let native = artifact.native_body().expect("native artifact");
        assert!(native.summary.worker_summaries.iter().any(|summary| {
            matches!(
                summary.kind,
                crate::NativeWorkerSummaryKind::FormatArgumentFetch
            )
        }));
        assert!(
            !native.summary.worker_summaries.iter().any(|summary| {
                matches!(summary.kind, crate::NativeWorkerSummaryKind::StringScan)
            })
        );
        assert_eq!(artifact.slice_class(), Some(crate::SliceClass::Worker));
        assert!(matches!(
            artifact.decompile_plan(),
            crate::DecompilePlan::NativeSummaryIslands { .. }
                | crate::DecompilePlan::NativeLinear { .. }
        ));
    }

    #[test]
    fn compile_semantics_replay_seeds_partition_cache_identity() {
        let blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");
        let ctx = Context::thread_local();
        let replay_a = ReplaySeed {
            checkpoint_id: Some(1),
            entry_pc: Some(0x2000),
            registers: vec![ReplayRegisterValue {
                name: "rax".to_string(),
                value: 0x1111,
            }],
            ..ReplaySeed::default()
        };
        let replay_b = ReplaySeed {
            checkpoint_id: Some(2),
            entry_pc: Some(0x2000),
            registers: vec![ReplayRegisterValue {
                name: "rax".to_string(),
                value: 0x2222,
            }],
            ..ReplaySeed::default()
        };

        let first = compile_function_semantics_cached_with_scope_impl(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
            Some(&replay_a),
        );
        let second = compile_function_semantics_cached_with_scope_impl(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
            Some(&replay_a),
        );
        let third = compile_function_semantics_cached_with_scope_impl(
            &ctx,
            &func,
            None,
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
            Some(&replay_b),
        );

        assert_eq!(first.seed_mode, SemanticSeedMode::Replay);
        assert_eq!(second.seed_mode, SemanticSeedMode::Replay);
        assert_eq!(third.seed_mode, SemanticSeedMode::Replay);
        assert_eq!(
            first.replay_seed_fingerprint,
            second.replay_seed_fingerprint
        );
        assert_ne!(first.replay_seed_fingerprint, third.replay_seed_fingerprint);
        assert!(!first.cache_hit);
        assert!(second.cache_hit);
        assert!(!third.cache_hit);
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
    fn large_cfg_cache_does_not_alias_distinct_scopes() {
        let mut blocks = vec![R2ILBlock {
            addr: 0x3000,
            size: 4,
            ops: vec![R2ILOp::Copy {
                dst: make_reg(RAX, 8),
                src: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut addr = 0x3004;
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
        let root = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("root");
        let helper = SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x5000,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&test_arch()),
        )
        .expect("helper");
        let scope_a = crate::PreparedFunctionScope::new(
            0x3000,
            vec![crate::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x3000),
                name: Some("sym.root".to_string()),
                prepared: root.clone(),
            }],
        )
        .expect("scope a");
        let scope_b = crate::PreparedFunctionScope::new(
            0x3000,
            vec![
                crate::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x3000),
                    name: Some("sym.root".to_string()),
                    prepared: root.clone(),
                },
                crate::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x5000),
                    name: Some("sym.helper".to_string()),
                    prepared: helper,
                },
            ],
        )
        .expect("scope b");
        let ctx = Context::thread_local();

        let first = compile_function_semantics_cached_with_scope(
            &ctx,
            &root,
            Some(&scope_a),
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );
        let second = compile_function_semantics_cached_with_scope(
            &ctx,
            &root,
            Some(&scope_b),
            Some(&test_arch()),
            &HashMap::new(),
            SummaryProfile::Default,
        );

        assert!(first.artifact.diagnostics.skipped_large_cfg);
        assert!(second.artifact.diagnostics.skipped_large_cfg);
        assert!(!first.cache_hit);
        assert!(!second.cache_hit);
    }

    #[test]
    fn bounded_query_scope_omits_cross_function_target_helpers() {
        let root = SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x1000,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&test_arch()),
        )
        .expect("root");
        let helper = SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x2000,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&test_arch()),
        )
        .expect("helper");
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![
                crate::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: root.clone(),
                },
                crate::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x2000),
                    name: Some("helper".to_string()),
                    prepared: helper,
                },
            ],
        )
        .expect("scope");

        let bounded = bounded_query_scope(&root, Some(&scope), 0x2000).expect("bounded scope");
        assert_eq!(bounded.functions().len(), 1);
        assert_eq!(bounded.root_id(), r2ssa::InterprocFunctionId(0x1000));
        assert!(
            bounded
                .functions()
                .contains_key(&r2ssa::InterprocFunctionId(0x1000))
        );
        assert!(
            !bounded
                .functions()
                .contains_key(&r2ssa::InterprocFunctionId(0x2000))
        );
    }

    #[test]
    fn bounded_query_scope_keeps_same_function_targets_unbounded() {
        let root = SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x1000,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&test_arch()),
        )
        .expect("root");
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![crate::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: root.clone(),
            }],
        )
        .expect("scope");

        assert!(bounded_query_scope(&root, Some(&scope), 0x1000).is_none());
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
                ops: make_selector_dispatch_ops(),
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
        assert_eq!(artifact.execution, ExecutionModel::Vm);
        assert_eq!(
            artifact.stage,
            super::super::region::RefinementStage::Compiled
        );
        assert_eq!(
            artifact.granularity,
            super::super::region::ArtifactGranularity::SummaryOnly
        );
        assert!(matches!(artifact.query_plan(), crate::QueryPlan::Ready));
        let vm_body = artifact.vm_body().expect("vm artifact body");
        assert!(vm_body.interpreter.is_some());
        let vm_step = vm_body.step_summary.as_ref().expect("vm step");
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
    fn weak_switch_without_step_summary_stays_native() {
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
        assert_eq!(artifact.execution, ExecutionModel::Native);
        assert!(artifact.vm_body().is_none());
        assert_ne!(
            artifact.slice_class(),
            Some(crate::SliceClass::InterpreterSwitch)
        );
        assert!(
            !artifact
                .diagnostics
                .residual_reasons
                .contains(&ResidualReason::InterpreterRequiresStepSummary)
        );
    }

    #[test]
    fn switch_loop_with_state_updates_but_no_selector_stays_native() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x2100,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2104, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2104,
                size: 4,
                ops: vec![],
                switch_info: Some(SwitchInfo {
                    switch_addr: 0x2104,
                    min_val: 0,
                    max_val: 4,
                    default_target: Some(0x2118),
                    cases: vec![
                        SwitchCase {
                            value: 0,
                            target: 0x2108,
                        },
                        SwitchCase {
                            value: 1,
                            target: 0x210c,
                        },
                        SwitchCase {
                            value: 2,
                            target: 0x2110,
                        },
                        SwitchCase {
                            value: 3,
                            target: 0x2114,
                        },
                    ],
                }),
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2108,
                size: 4,
                ops: vec![
                    R2ILOp::IntAdd {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x2104, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x210c,
                size: 4,
                ops: vec![
                    R2ILOp::IntSub {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x2104, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2110,
                size: 4,
                ops: vec![
                    R2ILOp::IntXor {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(0x55, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x2104, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2114,
                size: 4,
                ops: vec![
                    R2ILOp::IntLeft {
                        dst: make_reg(RAX, 8),
                        a: make_reg(RAX, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x2104, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2118,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x2104, 8),
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

        assert_eq!(artifact.execution, ExecutionModel::Native);
        assert!(artifact.vm_body().is_none());
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
                ops: make_selector_dispatch_ops(),
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
                        addr: make_reg(RBP, 8),
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

        let vm_step = artifact
            .vm_body()
            .and_then(|body| body.step_summary.as_ref())
            .expect("vm step summary");
        assert_eq!(artifact.execution, ExecutionModel::Vm);
        assert_eq!(
            artifact.stage,
            super::super::region::RefinementStage::Compiled
        );
        assert!(matches!(artifact.query_plan(), crate::QueryPlan::Ready));
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
        assert!(
            vm_step
                .handler_state_updates
                .get(&0x3008)
                .is_some_and(|updates| updates.iter().any(|update| {
                    update.exact
                        && matches!(update.value, crate::semantics::vm::VmValueExpr::Var(_))
                }))
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
        assert!(vm_step.transfers.iter().any(|transfer| {
            transfer.handler_target == 0x3008
                && transfer.state_updates.iter().any(|update| {
                    update.exact
                        && matches!(update.value, crate::semantics::vm::VmValueExpr::Var(_))
                })
        }));
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

        let native = artifact.native_body().expect("native body");
        assert_eq!(
            artifact.stage,
            super::super::region::RefinementStage::Residual
        );
        assert!(artifact.diagnostics.skipped_large_cfg);
        assert_eq!(native.regions.len(), 1);
        assert_eq!(native.actionable_control_count(), 2);
        assert!(matches!(
            artifact.type_plan(),
            crate::TypePlan::NativeAugmentation
        ));
        assert!(matches!(
            artifact.decompile_plan(),
            crate::DecompilePlan::NativeStructured
                | crate::DecompilePlan::NativeSummaryIslands { .. }
                | crate::DecompilePlan::NativeLinear { .. }
        ));
        assert_eq!(artifact.diagnostics.branches_evaluated, 1);
    }

    #[test]
    fn large_cfg_exact_branch_frontier_with_memory_support_is_decompile_ready() {
        let compiled = crate::backward::BackwardConditionSummary {
            simplified: "flag == 0".to_string(),
            terms: vec!["flag == 0".to_string()],
            memory_terms: vec![crate::backward::BackwardMemoryCondition {
                region: crate::backward::BackwardMemoryRegion::Argument { index: 0 },
                offset_lo: 0,
                offset_hi: 0,
                size: 1,
                exact_offset: true,
                evidence: crate::SemanticEvidence::exact(),
                binding: None,
                expr: "*arg0".to_string(),
                value_expr: Some("0x0:8".to_string()),
                exact_value: true,
            }],
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: crate::backward::BackwardConditionPrecision::Exact,
            supported_paths: 1,
            total_paths: 1,
        };
        let collected = CollectedNativeSemanticRegions {
            regions: std::iter::once({
                let region = crate::SemanticRegion {
                    anchor: 0x401000,
                    frontier: std::collections::BTreeSet::from([0x401010, 0x401020]),
                    control: vec![
                        crate::Judged::new(
                            crate::ControlFact {
                                target: 0x401010,
                                status: crate::SymbolicReachabilityStatus::Reachable,
                                branch_truth: Some(true),
                                condition: Some("flag == 0".to_string()),
                                compiled: Some(compiled.clone()),
                            },
                            crate::SemanticEvidence::exact(),
                        ),
                        crate::Judged::new(
                            crate::ControlFact {
                                target: 0x401020,
                                status: crate::SymbolicReachabilityStatus::Unreachable,
                                branch_truth: Some(false),
                                condition: Some("flag != 0".to_string()),
                                compiled: None,
                            },
                            crate::SemanticEvidence::exact(),
                        ),
                    ],
                    memory: vec![crate::Judged::new(
                        crate::MemoryFact {
                            term: compiled.memory_terms[0].clone(),
                        },
                        crate::SemanticEvidence::exact(),
                    )],
                    pre: Vec::new(),
                    post: Vec::new(),
                    targets: vec![
                        crate::Judged::new(
                            crate::TargetFact {
                                target: 0x401010,
                                status: crate::SymbolicReachabilityStatus::Reachable,
                                branch_truth: Some(true),
                            },
                            crate::SemanticEvidence::exact(),
                        ),
                        crate::Judged::new(
                            crate::TargetFact {
                                target: 0x401020,
                                status: crate::SymbolicReachabilityStatus::Unreachable,
                                branch_truth: Some(false),
                            },
                            crate::SemanticEvidence::exact(),
                        ),
                    ],
                };
                (region.key(), region)
            })
            .collect(),
            diagnostics: SymbolicFunctionFactDiagnostics {
                skipped_large_cfg: true,
                ..Default::default()
            },
            region_summaries: Vec::new(),
            worker_summaries: Vec::new(),
        };

        let stage = semantic_stage_for(
            0,
            0,
            &DerivedSummaryDiagnostics::default(),
            &collected,
            false,
        );
        let artifact = build_semantic_artifact(BuildSemanticArtifactInput {
            stage,
            granularity: ArtifactGranularity::Regioned,
            execution: ExecutionModel::Native,
            suppress_large_cfg_reason: true,
            role_name_hint: None,
            slice_class: crate::SliceClass::Worker,
            closure_functions: 0,
            helper_functions: 0,
            derived_summaries: 0,
            derived_diagnostics: DerivedSummaryDiagnostics::default(),
            collected,
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        });
        assert!(matches!(artifact.query_plan(), crate::QueryPlan::Ready));
        assert!(matches!(
            artifact.type_plan(),
            crate::TypePlan::NativeAugmentation
        ));
        assert!(matches!(
            artifact.decompile_plan(),
            crate::DecompilePlan::NativeStructured
        ));
        let reasons = artifact.diagnostics.residual_reasons;
        assert!(
            !reasons.contains(&ResidualReason::LargeCfg),
            "island-compiled workers should keep large_cfg as provenance, not a residual reason"
        );
    }
}
