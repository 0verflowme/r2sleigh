use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use r2ssa::{
    CFGRiskSummary, FunctionSemanticSummary, InterprocFunctionId, PreparedInterprocSummarySet,
    SsaArtifact,
};
use z3::Context;

use crate::sim::{
    DerivedSummaryDiagnostics, PreparedFunctionScope, SummaryProfile, SummaryRegistry,
    source_arch_spec,
};

use super::artifact::{
    ResidualReason, SemanticArtifact, SemanticArtifactBody, SemanticArtifactReport,
};
use super::cache::SEMANTIC_ARTIFACT_SCHEMA_VERSION;
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

fn should_skip_expensive_branch_compilation(
    cfg_summary: &CFGRiskSummary,
    branch_count: usize,
) -> bool {
    cfg_summary.block_count > 48
        || branch_count > 48
        || cfg_summary.back_edge_count > 4
        || cfg_summary.switch_block_count > 4
}

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
    func: &Arc<SsaArtifact>,
    scope: Option<&PreparedFunctionScope>,
    summaries: &PreparedInterprocSummarySet,
) -> Option<SemanticArtifact> {
    let summary = prepared_root_summary(func, summaries)?;
    let scope = match scope {
        Some(scope) => Some(scope.source_authorized_for_semantics(func)?),
        None => None,
    };
    let scope = scope.as_ref();
    if scope.is_some_and(|scope| !scope.matches_interproc_owners(summaries)) {
        return None;
    }
    let worker_summaries =
        super::native_worker::summaries_from_interproc_summary_unbounded(func.entry, summary);
    let worker_summaries = super::native_worker::bounded_worker_summaries(worker_summaries);
    let named_worker_family = has_named_worker_family(&worker_summaries);
    let route_policy =
        super::native_worker::native_worker_summary_route_policy_for_summary(func.entry, summary);
    if route_policy.should_prefer_full() {
        return None;
    }
    let direct_named_worker = route_policy.should_use_direct_summary();
    if worker_summaries.len() < SUMMARY_DENSE_WORKER_ISLAND_MIN
        && !(named_worker_family && direct_named_worker)
    {
        return None;
    }

    let cfg = func.function().cfg_risk_summary();
    if cfg.loop_count == 0
        && cfg.back_edge_count == 0
        && cfg.block_count <= 64
        && !(named_worker_family && direct_named_worker)
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
    let report = SemanticArtifactReport {
        schema_version: SEMANTIC_ARTIFACT_SCHEMA_VERSION,
        stage: RefinementStage::Compiled,
        granularity: ArtifactGranularity::SummaryOnly,
        execution: ExecutionModel::Native,
        body: SemanticArtifactBody::Native(NativeArtifactBody {
            summary: NativeFunctionSummary {
                slice_class,
                role_identity: super::native_worker::role_identity_from_worker_summaries(
                    summary.name.as_deref(),
                    summary.linkage,
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
        },
    }
    .normalized();
    let mut artifact =
        SemanticArtifact::new_with_interproc_provenance(Arc::clone(func), report, summaries)?;
    if let Some(scope) = scope
        && !artifact.retain_scope_provenance(scope)
    {
        return None;
    }
    Some(artifact)
}

pub fn compile_named_native_worker_summary_report(
    summary: &FunctionSemanticSummary,
    skipped_large_cfg: bool,
) -> Option<SemanticArtifactReport> {
    if !summary.has_current_schema()
        || summary.linkage != r2ssa::FunctionSemanticLinkage::Imported
        || !summary
            .name
            .as_deref()
            .is_some_and(super::native_worker::has_native_worker_summary_family)
    {
        return None;
    }
    let worker_summaries =
        super::native_worker::summaries_from_interproc_summary_unbounded(summary.id.0, summary);
    let worker_summaries = super::native_worker::bounded_worker_summaries(worker_summaries);
    let route_policy =
        super::native_worker::native_worker_summary_route_policy_for_summary(summary.id.0, summary);
    if !route_policy.has_route_certificate() {
        return None;
    }
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
    Some(build_semantic_artifact_report(BuildSemanticArtifactInput {
        stage: RefinementStage::Compiled,
        granularity: ArtifactGranularity::SummaryOnly,
        execution: ExecutionModel::Native,
        suppress_large_cfg_reason: true,
        role_name_hint: summary.name.clone(),
        role_linkage: summary.linkage,
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
    func: &Arc<SsaArtifact>,
    scope: Option<&PreparedFunctionScope>,
    summaries: Option<&PreparedInterprocSummarySet>,
    skipped_large_cfg: bool,
) -> Option<SemanticArtifact> {
    let summary = match summaries {
        Some(summaries) => Some(prepared_root_summary(func, summaries)?),
        None => None,
    };
    let scope = match scope {
        Some(scope) => Some(scope.source_authorized_for_semantics(func)?),
        None => None,
    };
    let scope = scope.as_ref();
    if let (Some(scope), Some(summaries)) = (scope, summaries)
        && !scope.matches_interproc_owners(summaries)
    {
        return None;
    }
    if let Some(summary) = summary
        && super::native_worker::native_worker_summary_route_policy_for_summary(func.entry, summary)
            .should_prefer_full()
    {
        return None;
    }
    let mut worker_summaries = Vec::new();
    if let Some(summary) = summary {
        worker_summaries.extend(
            super::native_worker::summaries_from_interproc_summary_unbounded(func.entry, summary),
        );
    }
    let has_primary_interproc_summary = worker_summaries
        .iter()
        .any(NativeWorkerSummary::is_primary_non_name_summary);
    let cfg_summary = func.function().cfg_risk_summary();
    let op_count = func
        .function()
        .blocks()
        .map(|block| block.ops.len())
        .sum::<usize>();
    let cheap_native_worker_classification =
        !skipped_large_cfg || (cfg_summary.block_count <= 64 && op_count <= 256);
    if cheap_native_worker_classification {
        if has_primary_interproc_summary {
            worker_summaries.extend(
                super::native_worker::classify_function_worker_enrichment_summaries_unbounded(func),
            );
        } else {
            worker_summaries
                .extend(super::native_worker::classify_function_worker_summaries_unbounded(func));
        }
    }
    let worker_summaries = super::native_worker::bounded_worker_summaries(worker_summaries);
    let named_worker_family = has_named_worker_family(
        &worker_summaries
            .iter()
            .filter(|summary| !summary.has_name_hint_evidence())
            .cloned()
            .collect::<Vec<_>>(),
    );
    let summary_owned_worker = summary.is_some_and(|summary| {
        summary.linkage == r2ssa::FunctionSemanticLinkage::Imported
            && summary
                .name
                .as_deref()
                .is_some_and(super::native_worker::has_native_worker_summary_family)
    });
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
        .any(NativeWorkerSummary::is_primary_non_name_summary)
        || region_summaries
            .iter()
            .any(crate::NativeRegionSummary::is_primary_non_name_summary);
    let stage = if has_primary_summary {
        RefinementStage::Compiled
    } else {
        RefinementStage::Residual
    };
    let role_name_hint = if has_primary_interproc_summary {
        summary
            .filter(|summary| summary.linkage == r2ssa::FunctionSemanticLinkage::Imported)
            .and_then(|summary| summary.name.clone())
    } else {
        None
    };
    let role_linkage = if has_primary_interproc_summary {
        summary
            .map(|summary| summary.linkage)
            .unwrap_or(r2ssa::FunctionSemanticLinkage::Unknown)
    } else {
        r2ssa::FunctionSemanticLinkage::Unknown
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

    let report = build_semantic_artifact_report(BuildSemanticArtifactInput {
        stage,
        granularity: ArtifactGranularity::SummaryOnly,
        execution: ExecutionModel::Native,
        suppress_large_cfg_reason: has_primary_summary,
        role_name_hint,
        role_linkage,
        slice_class,
        closure_functions,
        helper_functions,
        derived_summaries: 0,
        derived_diagnostics,
        collected,
        interpreter: None,
        vm_step: None,
        vm_transfer: None,
    });
    let mut artifact = match summaries {
        Some(summaries) => {
            SemanticArtifact::new_with_interproc_provenance(Arc::clone(func), report, summaries)?
        }
        None => SemanticArtifact::new(Arc::clone(func), report)?,
    };
    if let Some(scope) = scope
        && !artifact.retain_scope_provenance(scope)
    {
        return None;
    }
    Some(artifact)
}

fn prepared_root_summary<'a>(
    func: &Arc<SsaArtifact>,
    summaries: &'a PreparedInterprocSummarySet,
) -> Option<&'a FunctionSemanticSummary> {
    if !summaries.matches_root(func) {
        return None;
    }
    let root = summaries.report().root?;
    if root != InterprocFunctionId(func.entry) {
        return None;
    }
    summaries
        .report()
        .summaries
        .get(&root)
        .filter(|summary| summary.id == root)
}

struct BuildSemanticArtifactInput {
    stage: RefinementStage,
    granularity: ArtifactGranularity,
    execution: ExecutionModel,
    suppress_large_cfg_reason: bool,
    role_name_hint: Option<String>,
    role_linkage: r2ssa::FunctionSemanticLinkage,
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

fn build_semantic_artifact_report(input: BuildSemanticArtifactInput) -> SemanticArtifactReport {
    let BuildSemanticArtifactInput {
        stage,
        granularity,
        execution,
        suppress_large_cfg_reason,
        role_name_hint,
        role_linkage,
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
            role_linkage,
            &collected.worker_summaries,
        )
    } else {
        None
    };
    let body = match execution {
        // The same native analysis ran either way, and recognising a dispatch loop
        // says what the function does rather than that its regions are unusable.
        // Discarding them left a VM function with nothing to structure from and no
        // route but a block of comments.
        ExecutionModel::Vm => SemanticArtifactBody::Vm(Box::new(super::region::VmArtifactBody {
            interpreter,
            step_summary: vm_step,
            transfer_summary: vm_transfer,
            native: Some(Box::new(NativeArtifactBody {
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
            })),
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
    SemanticArtifactReport {
        schema_version: SEMANTIC_ARTIFACT_SCHEMA_VERSION,
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
        },
    }
    .normalized()
}

fn build_semantic_artifact(
    prepared: Arc<SsaArtifact>,
    input: BuildSemanticArtifactInput,
    scope: Option<&PreparedFunctionScope>,
) -> SemanticArtifact {
    let report = build_semantic_artifact_report(input);
    match scope {
        Some(scope) => SemanticArtifact::new_with_scope_provenance(prepared, report, scope)
            .expect("compiler scope must retain the exact prepared root"),
        None => SemanticArtifact::new(prepared, report)
            .expect("compiler report must use the current semantic artifact schema"),
    }
}

fn bounded_large_cfg_branch_limit(func: &SsaArtifact) -> usize {
    let summary = func.function().cfg_risk_summary();
    let branch_count = func.predicates().predicates.len();
    if branch_count >= 8 || summary.back_edge_count > 4 || summary.switch_block_count > 4 {
        return 0;
    }
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
    let scope = scope.and_then(|scope| scope.exact_for_artifact(func))?;
    let root = scope.root()?;
    let helper_limit = bounded_large_cfg_helper_limit(func).max(4);
    if scope.helper_functions().count() > helper_limit {
        None
    } else {
        scope.with_prepared_root(Arc::clone(&root.prepared))
    }
}

fn bounded_large_cfg_scope(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
) -> Option<PreparedFunctionScope> {
    let scope = scope.and_then(|scope| scope.exact_for_artifact(func))?;
    let root = scope.root()?;
    let root = root.clone();
    let helper_limit = bounded_large_cfg_helper_limit(func);
    if helper_limit == 0 {
        return prepared_scope_subset(scope, vec![root]);
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

    prepared_scope_subset(scope, functions)
}

fn prepared_scope_subset(
    source: &PreparedFunctionScope,
    functions: Vec<crate::ScopedPreparedFunction>,
) -> Option<PreparedFunctionScope> {
    let provenance = functions
        .iter()
        .map(|function| {
            source
                .provenance_of(function)
                .map(|provenance| (function.id, provenance))
        })
        .collect::<Option<std::collections::BTreeMap<_, _>>>()?;
    PreparedFunctionScope::new_with_provenance(source.root_id().0, functions, provenance)
}

fn bounded_query_scope(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    target_addr: u64,
) -> Option<PreparedFunctionScope> {
    let scope = scope.and_then(|scope| scope.exact_for_artifact(func))?;
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

fn compile_function_semantics_from_current_inputs(
    ctx: &Context,
    func: &Arc<SsaArtifact>,
    scope: Option<&PreparedFunctionScope>,
    summary_profile: SummaryProfile,
) -> SemanticArtifact {
    let arch = source_arch_spec(func.as_ref());
    let symbol_map = HashMap::new();
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

    if let Some(arch) = arch.as_ref() {
        let cfg_summary = func.function().cfg_risk_summary();
        let branch_count = func.predicates().predicates.len();
        let skip_expensive_branch_compilation =
            should_skip_expensive_branch_compilation(&cfg_summary, branch_count);

        if skip_expensive_branch_compilation {
            // The bounded collection is bounded whatever the function turns out to
            // be, so a dispatch loop has no more reason to skip it than anything
            // else expensive does. Skipping it left a VM function with no regions
            // at all, which is why nothing downstream could structure one.
            let bounded_scope = bounded_large_cfg_scope(func, scope);
            collected = collect_large_cfg_canonical_semantic_regions_with_limit(
                ctx,
                func,
                bounded_scope.as_ref(),
                arch,
                &symbol_map,
                summary_profile,
                bounded_large_cfg_branch_limit(func),
            );

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
            return build_semantic_artifact(
                Arc::clone(func),
                BuildSemanticArtifactInput {
                    stage,
                    granularity,
                    execution,
                    suppress_large_cfg_reason: matches!(execution, ExecutionModel::Vm)
                        || has_island_compiled_regions,
                    role_name_hint: None,
                    role_linkage: r2ssa::FunctionSemanticLinkage::Internal,
                    slice_class,
                    closure_functions,
                    helper_functions,
                    derived_summaries,
                    derived_diagnostics: derived_diagnostics.clone(),
                    collected,
                    interpreter: interpreter.clone(),
                    vm_step: vm_step.clone(),
                    vm_transfer: vm_transfer.clone(),
                },
                scope,
            );
        }

        if let Some(scope) = scope
            && let Some(registry) =
                SummaryRegistry::with_profile_for_prepared(func, summary_profile)
            && let Ok(derived) =
                registry.derive_source_owned_symbolic_summaries(ctx, scope, Some(arch), &symbol_map)
        {
            derived_summaries = derived.summaries.len();
            derived_diagnostics = derived.diagnostics.clone();
            collected = collect_canonical_semantic_regions_with_derived(
                ctx,
                func,
                Some(scope),
                arch,
                &symbol_map,
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
                &symbol_map,
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
    build_semantic_artifact(
        Arc::clone(func),
        BuildSemanticArtifactInput {
            stage,
            granularity,
            execution,
            suppress_large_cfg_reason: matches!(execution, ExecutionModel::Vm)
                || has_island_compiled_regions,
            role_name_hint: func.function().name.clone(),
            role_linkage: r2ssa::FunctionSemanticLinkage::Internal,
            slice_class,
            closure_functions,
            helper_functions,
            derived_summaries,
            derived_diagnostics: derived_diagnostics.clone(),
            collected,
            interpreter,
            vm_step,
            vm_transfer,
        },
        scope,
    )
}

pub fn compile_function_semantics_with_scope(
    ctx: &Context,
    func: &Arc<SsaArtifact>,
    scope: Option<&PreparedFunctionScope>,
    summary_profile: SummaryProfile,
) -> SemanticArtifact {
    let scope = scope.and_then(|scope| scope.source_authorized_for_semantics(func));
    compile_function_semantics_from_current_inputs(ctx, func, scope.as_ref(), summary_profile)
}

pub fn compile_semantic_artifact_with_scope(
    ctx: &Context,
    func: &Arc<SsaArtifact>,
    scope: Option<&PreparedFunctionScope>,
    summary_profile: SummaryProfile,
) -> SemanticArtifact {
    compile_function_semantics_with_scope(ctx, func, scope, summary_profile)
}

pub fn compile_query_semantic_artifact_with_scope(
    ctx: &Context,
    func: &Arc<SsaArtifact>,
    scope: Option<&PreparedFunctionScope>,
    target_addr: u64,
    summary_profile: SummaryProfile,
) -> SemanticArtifact {
    let scope = scope.and_then(|scope| scope.source_authorized_for_semantics(func));
    let bounded_scope = bounded_query_scope(func, scope.as_ref(), target_addr);
    let selected_scope = bounded_scope.as_ref().or(scope.as_ref());
    compile_function_semantics_with_scope(ctx, func, selected_scope, summary_profile)
}

pub fn compile_semantic_artifact_default_with_scope(
    ctx: &Context,
    func: &Arc<SsaArtifact>,
    scope: Option<&PreparedFunctionScope>,
) -> SemanticArtifact {
    let scope = scope.and_then(|scope| scope.source_authorized_for_semantics(func));
    let rebound_scope = bounded_default_scope(func, scope.as_ref());
    compile_semantic_artifact_with_scope(ctx, func, rebound_scope.as_ref(), SummaryProfile::Default)
}

#[cfg(test)]
mod tests {
    use r2il::{
        ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, SwitchCase, SwitchInfo, Varnode,
    };
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn, SourceStackSlotSpec, SsaArtifact, StackAddressBase,
    };
    use z3::Context;

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

    fn prepared_summaries(func: &Arc<SsaArtifact>) -> PreparedInterprocSummarySet {
        r2ssa::solve_prepared_interproc_summary_set(
            Arc::clone(func),
            &[r2ssa::PreparedInterprocFunctionInput {
                id: InterprocFunctionId(func.entry),
                name: func.function().name.clone(),
                prepared: func,
            }],
            r2ssa::InterprocSolveConfig::default(),
        )
        .expect("prepared summaries")
    }

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn exact_vm_memory_fixture() -> (ArchSpec, SourceFunctionInterface) {
        const RSP: u64 = 0x28;
        const RIP: u64 = 0x30;

        let mut arch = test_arch();
        arch.add_register(RegisterDef::new("RSP", RSP, 8));
        arch.add_register(RegisterDef::new("RIP", RIP, 8));
        let interface = SourceFunctionInterface::new_exact(
            b"vm-handler-memory-evidence-v1".to_vec(),
            "x86-64",
            [SourceAbiParameterSpec::new(0, register_storage(RDI, 8))],
            SourceFunctionReturn::Register {
                storage: register_storage(RAX, 8),
            },
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                register_storage(RBP, 8),
                0,
                8,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(RIP, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(RSP, 8)))
        .expect("coherent VM handler memory interface");
        (arch, interface)
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
    fn repeated_compilation_is_request_local() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));
        let ctx = Context::thread_local();
        let mut first =
            compile_function_semantics_with_scope(&ctx, &func, None, SummaryProfile::Default);
        first.report_mut().diagnostics.branches_evaluated = usize::MAX;
        let second =
            compile_function_semantics_with_scope(&ctx, &func, None, SummaryProfile::Default);

        assert_eq!(first.diagnostics.branches_evaluated, usize::MAX);
        assert_ne!(second.diagnostics.branches_evaluated, usize::MAX);
    }

    #[test]
    fn compiled_artifact_retains_exact_owner_and_rejects_rebuilt_identical_ssa() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let prepared =
            Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("prepared SSA"));
        let rebuilt =
            Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("rebuilt SSA"));
        let weak = Arc::downgrade(&prepared);
        let artifact = compile_function_semantics_with_scope(
            &Context::thread_local(),
            &prepared,
            None,
            SummaryProfile::Default,
        );

        assert!(artifact.shares_artifact(&prepared));
        assert!(!artifact.shares_artifact(&rebuilt));
        drop(prepared);
        assert!(weak.upgrade().is_some());
        drop(artifact);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn bound_compiler_uses_same_owner_machine_context_not_foreign_arch_advice() {
        let (arch, interface) = exact_vm_memory_fixture();
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let prepared = Arc::new(
            SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
                .expect("source-owned prepared SSA"),
        );
        let mut foreign_arch = ArchSpec::new("aarch64");
        foreign_arch.addr_size = 8;

        let projected = source_arch_spec(&prepared).expect("retained source architecture");
        let artifact = compile_function_semantics_with_scope(
            &Context::thread_local(),
            &prepared,
            None,
            SummaryProfile::Default,
        );

        assert_eq!(projected.name, "x86-64");
        assert_ne!(projected.name, foreign_arch.name);
        assert!(!artifact.diagnostics.skipped_missing_arch);
        assert!(artifact.shares_artifact(&prepared));
    }

    #[test]
    fn bound_compilation_is_invariant_to_imported_name_advice() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Call {
                    target: make_const(0x5000, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![
                    R2ILOp::IntEqual {
                        dst: make_reg(RDI, 1),
                        a: make_reg(RAX, 8),
                        b: make_const(0, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(RDI, 1),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));
        let helper = Arc::new(
            SsaArtifact::for_symbolic(
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
            .expect("helper"),
        );
        let scope = PreparedFunctionScope::new(
            func.entry,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(func.entry),
                    name: Some("root".to_string()),
                    prepared: Arc::clone(&func),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(helper.entry),
                    name: Some("external".to_string()),
                    prepared: helper,
                },
            ],
        )
        .expect("scope");
        let ctx = Context::thread_local();
        let before = compile_function_semantics_with_scope(
            &ctx,
            &func,
            Some(&scope),
            SummaryProfile::Default,
        );
        let imported_name_report = compile_named_native_worker_summary_report(
            &r2ssa::FunctionSemanticSummary::unknown(
                InterprocFunctionId(0x5000),
                Some("sym.imp.malloc".to_string()),
            ),
            false,
        );
        let after = compile_function_semantics_with_scope(
            &ctx,
            &func,
            Some(&scope),
            SummaryProfile::Default,
        );

        assert!(imported_name_report.is_none());
        assert_eq!(before, after);
    }

    #[test]
    fn looped_branch_fanout_uses_bounded_semantic_compilation() {
        let looped = CFGRiskSummary {
            block_count: 23,
            loop_count: 1,
            back_edge_count: 1,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let straight = CFGRiskSummary {
            block_count: 23,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        // Branch fanout alone no longer forces the bounded path: it dropped the
        // effects the source needs, and a function of this size compiles fully.
        assert!(!should_skip_expensive_branch_compilation(&straight, 8));
        assert!(!should_skip_expensive_branch_compilation(&looped, 8));
        // Size and loop complexity still do
        assert!(should_skip_expensive_branch_compilation(&straight, 49));
        assert!(should_skip_expensive_branch_compilation(
            &CFGRiskSummary {
                back_edge_count: 5,
                ..looped
            },
            8
        ));
    }

    #[test]
    fn bounded_large_cfg_branch_fanout_uses_solver_free_budget() {
        let mut blocks = Vec::new();
        // Enough branches to exceed the fanout bound, which is what puts a function
        // on the bounded path now that fanout alone no longer does
        for idx in 0..50u64 {
            blocks.push(R2ILBlock {
                addr: 0x3000 + idx * 8,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x4000, 8),
                    cond: make_reg(RAX, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            });
            blocks.push(R2ILBlock {
                addr: 0x3004 + idx * 8,
                size: 4,
                ops: if idx + 1 < 50 {
                    vec![R2ILOp::Branch {
                        target: make_const(0x3008 + idx * 8, 8),
                    }]
                } else {
                    vec![R2ILOp::Return {
                        target: make_reg(RAX, 8),
                    }]
                },
                switch_info: None,
                op_metadata: Default::default(),
            });
        }
        blocks.push(R2ILBlock {
            addr: 0x4000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_reg(RAX, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        });
        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));

        assert_eq!(bounded_large_cfg_branch_limit(&func), 0);
        let ctx = Context::thread_local();
        let artifact =
            compile_function_semantics_with_scope(&ctx, &func, None, SummaryProfile::Default);
        let native = artifact.native_body().expect("native body");
        assert!(artifact.diagnostics.skipped_large_cfg);
        assert_eq!(artifact.diagnostics.branches_evaluated, 0);
        assert!(native.regions.is_empty());
    }

    #[test]
    fn summary_dense_worker_artifact_uses_interproc_summaries_without_branch_regions() {
        let mut entry_ops = (0..SUMMARY_DENSE_WORKER_ISLAND_MIN / 2)
            .map(|offset| R2ILOp::Load {
                dst: Varnode::unique(0x100 + offset as u64, 1),
                space: SpaceId::Ram,
                addr: make_const(0x8000 + offset as u64, 8),
            })
            .collect::<Vec<_>>();
        entry_ops.push(R2ILOp::CBranch {
            target: make_const(0x1000, 8),
            cond: make_reg(RAX, 1),
        });
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: entry_ops,
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
        let (arch, interface) = exact_vm_memory_fixture();
        let func = Arc::new(
            SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface.clone())
                .expect("source-owned SSA"),
        );
        let summaries = prepared_summaries(&func);
        let root_summary = summaries
            .report()
            .summaries
            .get(&InterprocFunctionId(func.entry))
            .expect("root summary");
        assert!(root_summary.has_unknown_calls);
        assert_eq!(
            root_summary.return_relation,
            r2ssa::SummaryReturnRelation::Unknown
        );
        let root_scope = PreparedFunctionScope::new(
            func.entry,
            vec![crate::ScopedPreparedFunction {
                id: InterprocFunctionId(func.entry),
                name: None,
                prepared: Arc::clone(&func),
            }],
        )
        .expect("root scope");
        assert!(root_scope.matches_interproc_owners(&summaries));

        let detached_helper = Arc::new(
            SsaArtifact::for_decompile_with_interface(
                &[R2ILBlock {
                    addr: 0x5000,
                    size: 1,
                    ops: vec![R2ILOp::Return {
                        target: make_const(0, 8),
                    }],
                    switch_info: None,
                    op_metadata: Default::default(),
                }],
                Some(&arch),
                interface,
            )
            .expect("detached helper"),
        );
        let mismatched_scope = PreparedFunctionScope::new(
            func.entry,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(func.entry),
                    name: None,
                    prepared: Arc::clone(&func),
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(detached_helper.entry),
                    name: None,
                    prepared: detached_helper,
                },
            ],
        )
        .expect("detached helper scope");
        assert!(!mismatched_scope.matches_interproc_owners(&summaries));
        assert!(
            compile_summary_dense_worker_artifact_from_interproc_summary(
                &func,
                Some(&mismatched_scope),
                &summaries,
            )
            .is_none()
        );

        let artifact = compile_summary_dense_worker_artifact_from_interproc_summary(
            &func,
            Some(&root_scope),
            &summaries,
        )
        .expect("summary-dense worker artifact");

        let native = artifact.native_body().expect("native artifact");
        assert_eq!(artifact.stage, RefinementStage::Compiled);
        assert_eq!(artifact.granularity, ArtifactGranularity::SummaryOnly);
        assert_eq!(artifact.diagnostics.branches_evaluated, 0);
        assert!(!artifact.diagnostics.skipped_large_cfg);
        assert!(native.regions.is_empty());
        assert_eq!(
            native.summary.worker_summaries.len(),
            SUMMARY_DENSE_WORKER_ISLAND_MIN + 6
        );
        assert!(matches!(
            artifact.decompile_plan(),
            crate::DecompilePlan::NativeLinear { .. }
        ));
        assert!(!artifact.has_helper_provenance());
    }

    #[test]
    fn summary_artifact_compilers_reject_foreign_rebuilt_owner() {
        let (arch, interface) = exact_vm_memory_fixture();
        let blocks = [R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let requested = Arc::new(
            SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface.clone())
                .expect("requested source"),
        );
        let foreign = Arc::new(
            SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
                .expect("foreign rebuilt source"),
        );
        let foreign_summaries = prepared_summaries(&foreign);

        assert!(
            compile_summary_dense_worker_artifact_from_interproc_summary(
                &requested,
                None,
                &foreign_summaries,
            )
            .is_none()
        );
        assert!(
            compile_native_worker_summary_artifact(
                &requested,
                None,
                Some(&foreign_summaries),
                true,
            )
            .is_none()
        );
    }

    #[test]
    fn summary_artifact_compilers_cannot_receive_rebuilt_helper_provenance() {
        let (arch, interface) = exact_vm_memory_fixture();
        let root = Arc::new(
            SsaArtifact::for_decompile_with_interface(
                &[R2ILBlock {
                    addr: 0x1000,
                    size: 4,
                    ops: vec![R2ILOp::Return {
                        target: make_const(0, 8),
                    }],
                    switch_info: None,
                    op_metadata: Default::default(),
                }],
                Some(&arch),
                interface,
            )
            .expect("root source"),
        );
        let (helper_arch, rebuilt_interface) = exact_vm_memory_fixture();
        let helper = Arc::new(
            SsaArtifact::for_decompile_with_interface(
                &[R2ILBlock {
                    addr: 0x2000,
                    size: 4,
                    ops: vec![R2ILOp::Return {
                        target: make_const(0, 8),
                    }],
                    switch_info: None,
                    op_metadata: Default::default(),
                }],
                Some(&helper_arch),
                rebuilt_interface,
            )
            .expect("rebuilt helper source"),
        );

        let error = r2ssa::solve_prepared_interproc_summary_set(
            Arc::clone(&root),
            &[
                r2ssa::PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(root.entry),
                    name: None,
                    prepared: &root,
                },
                r2ssa::PreparedInterprocFunctionInput {
                    id: InterprocFunctionId(helper.entry),
                    name: None,
                    prepared: &helper,
                },
            ],
            r2ssa::InterprocSolveConfig::default(),
        )
        .expect_err("rebuilt helper provenance must remain unsealable");

        assert_eq!(error, r2ssa::PreparedInterprocSummaryError::ManualFunction);
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
        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));

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
    fn internal_native_worker_artifacts_and_routes_ignore_names() {
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
        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));
        let summaries = [Some("dbg.xnmalloc"), Some("renamed_worker"), None]
            .into_iter()
            .map(|name| {
                let mut summary = r2ssa::FunctionSemanticSummary::unknown(
                    r2ssa::InterprocFunctionId(func.entry),
                    name.map(str::to_string),
                );
                summary.linkage = r2ssa::FunctionSemanticLinkage::Internal;
                summary
                    .allocation_effects
                    .push(r2ssa::SummaryAllocationEffect {
                        size_arg: Some(0),
                        zeroed: false,
                    });
                summary.return_relation = r2ssa::SummaryReturnRelation::HeapAlloc;
                summary
            })
            .collect::<Vec<_>>();
        let policies = summaries
            .iter()
            .map(|summary| {
                super::super::native_worker::native_worker_summary_route_policy_for_summary(
                    func.entry, summary,
                )
            })
            .collect::<Vec<_>>();
        for (summary, policy) in summaries.iter().zip(&policies) {
            assert_eq!(
                policy.kind,
                super::super::native_worker::NativeWorkerSummaryRouteKind::Standard
            );
            assert!(policy.certificate.is_some());
            assert!(compile_named_native_worker_summary_report(summary, true).is_none());
        }
        assert!(
            policies
                .windows(2)
                .all(|pair| pair[0].certificate == pair[1].certificate)
        );
        let artifact = compile_native_worker_summary_artifact(&func, None, None, true)
            .expect("source-derived worker summary");
        let native = artifact.native_body().expect("native artifact");
        assert!(native.summary.worker_summaries.iter().all(|summary| {
            !matches!(
                summary.kind,
                crate::NativeWorkerSummaryKind::FormatArgumentFetch
            )
        }));
        assert!(
            native.summary.worker_summaries.iter().any(|summary| {
                matches!(summary.kind, crate::NativeWorkerSummaryKind::StringScan)
            })
        );
        let role = native
            .summary
            .role_identity
            .as_ref()
            .expect("role identity");
        assert_eq!(role.role_name, "string_scan");
        assert_eq!(role.source, crate::NativeWorkerRoleSource::Structural);
        assert_eq!(role.linkage, r2ssa::FunctionSemanticLinkage::Unknown);
        assert!(
            role.source_names.is_empty(),
            "structural worker evidence must not inherit an arbitrary summary name"
        );
        assert_eq!(artifact.slice_class(), Some(crate::SliceClass::Worker));
        assert!(matches!(
            artifact.decompile_plan(),
            crate::DecompilePlan::NativeSummaryIslands { .. }
                | crate::DecompilePlan::NativeLinear { .. }
        ));
    }

    #[test]
    fn named_native_worker_compilation_requires_imported_linkage() {
        let mut summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x2200),
            Some("sym.copy_file_data".to_string()),
        );
        summary.linkage = r2ssa::FunctionSemanticLinkage::Imported;
        summary.transfer_effects.push(r2ssa::SummaryTransferEffect {
            dst: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 4 },
                range: None,
            },
            src: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                range: None,
            },
            len: r2ssa::SummaryTransferLength::Const(8),
        });

        let report = compile_named_native_worker_summary_report(&summary, true)
            .expect("explicit imported worker report");
        let SemanticArtifactBody::Native(native) = &report.body else {
            panic!("native report");
        };
        let role = native
            .summary
            .role_identity
            .as_ref()
            .expect("imported role identity");
        assert_eq!(role.linkage, r2ssa::FunctionSemanticLinkage::Imported);
        assert_eq!(role.source, crate::NativeWorkerRoleSource::SummarySeed);
        assert_eq!(role.source_names, vec!["copy_file_data".to_string()]);
        assert!(role.evidence.allows_narrowing());
        assert!(native.summary.worker_summaries.iter().any(|worker| {
            worker.kind == crate::NativeWorkerSummaryKind::FileTransfer
                && worker.src
                    == Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: None,
                    })
                && worker.dst
                    == Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 4 },
                        range: None,
                    })
        }));

        let current_schema = summary.schema_version;
        for schema_version in [
            current_schema.saturating_sub(1),
            current_schema.saturating_add(1),
        ] {
            let mut invalid = summary.clone();
            invalid.schema_version = schema_version;
            assert!(compile_named_native_worker_summary_report(&invalid, true).is_none());
        }

        summary.linkage = r2ssa::FunctionSemanticLinkage::Internal;
        assert!(compile_named_native_worker_summary_report(&summary, true).is_none());
    }

    #[test]
    fn bound_compilation_drops_manual_helper_scope_and_lifetime() {
        let mut blocks = vec![R2ILBlock {
            addr: 0x3000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(RAX, 8),
                    src: make_const(0, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x5000, 8),
                },
            ],
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
        let root = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("root"));
        let helper = Arc::new(
            SsaArtifact::for_symbolic(
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
            .expect("helper"),
        );
        let helper_weak = Arc::downgrade(&helper);
        let scope_a = crate::PreparedFunctionScope::new(
            0x3000,
            vec![crate::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x3000),
                name: Some("sym.root".to_string()),
                prepared: Arc::clone(&root),
            }],
        )
        .expect("scope a");
        let scope_b = crate::PreparedFunctionScope::new(
            0x3000,
            vec![
                crate::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x3000),
                    name: Some("sym.root".to_string()),
                    prepared: Arc::clone(&root),
                },
                crate::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x5000),
                    name: Some("sym.helper".to_string()),
                    prepared: Arc::clone(&helper),
                },
            ],
        )
        .expect("scope b");
        drop(helper);
        let ctx = Context::thread_local();

        let first = compile_function_semantics_with_scope(
            &ctx,
            &root,
            Some(&scope_a),
            SummaryProfile::Default,
        );
        let second = compile_function_semantics_with_scope(
            &ctx,
            &root,
            Some(&scope_b),
            SummaryProfile::Default,
        );

        assert!(first.diagnostics.skipped_large_cfg);
        assert!(second.diagnostics.skipped_large_cfg);
        let first_summary = &first.native_body().expect("native body").summary;
        let second_summary = &second.native_body().expect("native body").summary;
        assert_eq!(first_summary.closure_functions, 1);
        assert_eq!(second_summary.closure_functions, 1);
        assert_eq!(first_summary.helper_functions, 0);
        assert_eq!(second_summary.helper_functions, 0);
        assert!(!first.has_helper_provenance());
        assert!(!second.has_helper_provenance());
        let rejected_helper = helper_weak.upgrade().expect("scope still retains helper");
        assert!(!second.retains_helper_provenance_owner(&rejected_helper));
        drop(rejected_helper);
        drop(scope_b);
        assert!(helper_weak.upgrade().is_none());
    }

    #[test]
    fn bounded_query_scope_omits_cross_function_target_helpers() {
        let root = Arc::new(
            SsaArtifact::for_symbolic(
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
            .expect("root"),
        );
        let helper = Arc::new(
            SsaArtifact::for_symbolic(
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
            .expect("helper"),
        );
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![
                crate::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x1000),
                    name: Some("root".to_string()),
                    prepared: Arc::clone(&root),
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
        let root = Arc::new(
            SsaArtifact::for_symbolic(
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
            .expect("root"),
        );
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![crate::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: Arc::clone(&root),
            }],
        )
        .expect("scope");

        assert!(bounded_query_scope(&root, Some(&scope), 0x1000).is_none());
    }

    #[test]
    fn bounded_scopes_refuse_foreign_root_authority() {
        let blocks = [R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let requested = Arc::new(
            SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("requested root"),
        );
        let scoped =
            Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("scoped root"));
        let scope = crate::PreparedFunctionScope::new(
            0x1000,
            vec![crate::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x1000),
                name: Some("root".to_string()),
                prepared: scoped,
            }],
        )
        .expect("scope");

        assert!(bounded_default_scope(&requested, Some(&scope)).is_none());
        assert!(bounded_large_cfg_scope(&requested, Some(&scope)).is_none());
    }

    fn foreign_same_content_scope() -> (Arc<SsaArtifact>, PreparedFunctionScope) {
        let root_blocks = [R2ILBlock {
            addr: 0x1000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let helper_blocks = [R2ILBlock {
            addr: 0x2000,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(1, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let requested = Arc::new(
            SsaArtifact::for_symbolic(&root_blocks, None).expect("requested root artifact"),
        );
        let foreign =
            Arc::new(SsaArtifact::for_symbolic(&root_blocks, None).expect("foreign root artifact"));
        let helper =
            Arc::new(SsaArtifact::for_symbolic(&helper_blocks, None).expect("helper artifact"));
        let scope = PreparedFunctionScope::new(
            requested.entry,
            vec![
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(requested.entry),
                    name: Some("root".to_string()),
                    prepared: foreign,
                },
                crate::ScopedPreparedFunction {
                    id: InterprocFunctionId(helper.entry),
                    name: Some("helper".to_string()),
                    prepared: helper,
                },
            ],
        )
        .expect("foreign scope");
        (requested, scope)
    }

    fn assert_foreign_scope_was_dropped(artifact: &SemanticArtifact) {
        let summary = &artifact.native_body().expect("native artifact").summary;
        assert_eq!(summary.closure_functions, 1);
        assert_eq!(summary.helper_functions, 0);
    }

    #[test]
    fn standard_compile_drops_foreign_same_content_scope() {
        let (requested, scope) = foreign_same_content_scope();
        let artifact = compile_function_semantics_with_scope(
            &Context::thread_local(),
            &requested,
            Some(&scope),
            SummaryProfile::Default,
        );

        assert_foreign_scope_was_dropped(&artifact);
    }

    #[test]
    fn query_compile_drops_foreign_same_content_cross_function_scope() {
        let (requested, scope) = foreign_same_content_scope();
        let artifact = compile_query_semantic_artifact_with_scope(
            &Context::thread_local(),
            &requested,
            Some(&scope),
            0x2000,
            SummaryProfile::Default,
        );

        assert_foreign_scope_was_dropped(&artifact);
    }

    #[test]
    fn query_fallback_does_not_reintroduce_foreign_same_content_scope() {
        let (requested, scope) = foreign_same_content_scope();
        let artifact = compile_query_semantic_artifact_with_scope(
            &Context::thread_local(),
            &requested,
            Some(&scope),
            requested.entry,
            SummaryProfile::Default,
        );

        assert_foreign_scope_was_dropped(&artifact);
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
        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));
        let ctx = Context::thread_local();
        let artifact =
            compile_function_semantics_with_scope(&ctx, &func, None, SummaryProfile::Default);
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
        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));
        let ctx = Context::thread_local();
        let artifact =
            compile_function_semantics_with_scope(&ctx, &func, None, SummaryProfile::Default);
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
        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));
        let ctx = Context::thread_local();
        let artifact =
            compile_function_semantics_with_scope(&ctx, &func, None, SummaryProfile::Default);

        assert_eq!(artifact.execution, ExecutionModel::Native);
        assert!(artifact.vm_body().is_none());
    }

    #[test]
    fn vm_step_summary_tracks_case_values_and_handler_regions() {
        let (arch, interface) = exact_vm_memory_fixture();
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
        let func = Arc::new(
            SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
                .expect("ssa"),
        );
        assert_eq!(
            func.provenance_kind(),
            r2ssa::SsaArtifactProvenanceKind::Manual
        );
        let ctx = Context::thread_local();
        let artifact =
            compile_function_semantics_with_scope(&ctx, &func, None, SummaryProfile::Default);

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

        let func = Arc::new(SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa"));
        let ctx = Context::thread_local();
        let artifact =
            compile_function_semantics_with_scope(&ctx, &func, None, SummaryProfile::Default);

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
                address: crate::SemanticMemoryAddress::exact(0),
                size: 1,
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
        let prepared = Arc::new(
            SsaArtifact::for_symbolic(
                &[R2ILBlock {
                    addr: 0x401000,
                    size: 1,
                    ops: vec![R2ILOp::Return {
                        target: make_const(0, 8),
                    }],
                    switch_info: None,
                    op_metadata: Default::default(),
                }],
                None,
            )
            .expect("test SSA"),
        );
        let artifact = build_semantic_artifact(
            prepared,
            BuildSemanticArtifactInput {
                stage,
                granularity: ArtifactGranularity::Regioned,
                execution: ExecutionModel::Native,
                suppress_large_cfg_reason: true,
                role_name_hint: None,
                role_linkage: r2ssa::FunctionSemanticLinkage::Internal,
                slice_class: crate::SliceClass::Worker,
                closure_functions: 0,
                helper_functions: 0,
                derived_summaries: 0,
                derived_diagnostics: DerivedSummaryDiagnostics::default(),
                collected,
                interpreter: None,
                vm_step: None,
                vm_transfer: None,
            },
            None,
        );
        assert!(matches!(artifact.query_plan(), crate::QueryPlan::Ready));
        assert!(matches!(
            artifact.type_plan(),
            crate::TypePlan::NativeAugmentation
        ));
        assert!(matches!(
            artifact.decompile_plan(),
            crate::DecompilePlan::NativeStructured
        ));
        let reasons = &artifact.diagnostics.residual_reasons;
        assert!(
            !reasons.contains(&ResidualReason::LargeCfg),
            "island-compiled workers should keep large_cfg as provenance, not a residual reason"
        );
    }
}
