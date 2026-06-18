//! r2engine owns cross-crate analysis orchestration.
//!
//! Fact ownership stays in the lower crates: SSA in `r2ssa`, semantic artifacts
//! in `r2sym`, type facts in `r2types`, and rendering in `r2dec`. This crate is
//! the session-level scheduler/cache boundary that decides which artifacts are
//! needed for a request and how they are reused.

use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;
use std::time::Duration;

use r2il::R2ILBlock;
use r2ssa::{CFGRiskSummary, SsaArtifact};
use r2types::{
    FunctionFacts, FunctionSignatureProjection, FunctionTypeFactInputs, FunctionTypeFacts,
    SignatureCertificateSource, TypeWritebackPlan,
};
use serde::{Deserialize, Serialize};

mod cache;
mod route;
mod stable_hash;

pub use cache::{CacheCounters, EngineSessionCacheMetrics, SessionCache};
pub use route::{
    DecompileProbeDecision, EngineDiagnostics, EngineFunctionIdentity, EnginePlan,
    EngineProfileRouteDecision, EngineProfileRouteKind, EngineRequestKind, EngineRequestPlan,
    EngineRouteContext, EngineRouteDecision, EngineTypeRouteDecision, EngineTypeRouteKind,
    EngineTypedRouteDecision, cfg_guard_reason, cfg_guard_reason_from_summary,
    decompile_probe_decision, decompile_probe_decision_for_identity, decompile_route_decision,
    decompiler_context_with_route_decision, detached_semantic_linearization_reason,
    detached_semantic_route_plan, has_primary_summary_only_native_worker,
    has_renderable_primary_summary_only_native_worker, named_worker_summary_route,
    plan_decompile_request, plan_profile_request, plan_type_request,
    prefer_symbolic_large_worker_decompile, profile_route_decision, select_engine_plan,
    semantic_artifact_needs_fallback_type_payload, semantic_or_cfg_prefers_bounded_type_plan,
    semantic_route_from_artifact_plan, semantic_route_plan, semantic_route_plan_from_context,
    semantic_route_reason, should_guard_program_orchestrator_decompile,
    should_skip_runtime_type_inference, should_use_direct_named_native_worker_decompile,
    should_use_direct_named_native_worker_type_projection, should_use_prepared_semantic_view,
    type_cfg_allows_semantic_plan, type_cfg_bounded_reason, type_cfg_forces_bounded_plan,
    type_cfg_prefers_bounded_plan, type_route_decision,
};
use route::{
    direct_named_worker_summary_applicability_for_identity,
    has_renderable_native_linear_worker_summary, native_body_has_renderable_worker_summary,
    prefers_standard_native_for_summary_only_worker, proof_coverage_from_type_facts,
    raw_cfg_risk_summary_for_preprobe, should_prefer_full_decompile_for_named_worker,
};
pub use stable_hash::{
    stable_blocks_hash, stable_fnv1a_bytes, stable_fnv1a_debug_hash, stable_fnv1a_hash,
};

pub const ENGINE_SCHEMA_VERSION: u32 = 2;
pub const DEFAULT_ENGINE_CACHE_LIMIT: usize = 256;
pub const SYMBOLIC_PATHS_LIMIT: usize = 32;
pub const SYMBOLIC_PATHS_CALL_FREE_MAX_STATES: usize = 16;
pub const SYMBOLIC_PATHS_CALL_FREE_MAX_DEPTH: usize = 64;
pub const SYMBOLIC_PATHS_CALL_HEAVY_MAX_STATES: usize = 8;
pub const SYMBOLIC_PATHS_CALL_HEAVY_MAX_DEPTH: usize = 32;
pub const SYMBOLIC_PATHS_TIMEOUT_MS: u64 = 500;
pub const SYMBOLIC_PATHS_SOLUTION_LIMIT: usize = 4;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AnalysisCacheKey {
    pub schema_version: u32,
    pub function_addr: u64,
    pub function_name_hash: u64,
    pub arch_hash: u64,
    pub blocks_hash: u64,
    pub typed_context_hash: u64,
    pub assumptions_hash: u64,
    pub analysis_depth_hash: u64,
}

impl AnalysisCacheKey {
    pub fn from_parts(
        function_addr: u64,
        function_name: &str,
        arch: Option<&r2il::ArchSpec>,
        blocks: &[R2ILBlock],
        typed_context_hash: u64,
        assumptions_hash: u64,
        analysis_depth: &str,
    ) -> Self {
        Self {
            schema_version: ENGINE_SCHEMA_VERSION,
            function_addr,
            function_name_hash: stable_fnv1a_hash(&function_name),
            arch_hash: stable_fnv1a_debug_hash(&arch),
            blocks_hash: stable_blocks_hash(blocks),
            typed_context_hash,
            assumptions_hash,
            analysis_depth_hash: stable_fnv1a_hash(&analysis_depth),
        }
    }

    pub fn from_hashes(
        function_addr: u64,
        function_name_hash: u64,
        arch_hash: u64,
        blocks_hash: u64,
        typed_context_hash: u64,
        assumptions_hash: u64,
        analysis_depth_hash: u64,
    ) -> Self {
        Self {
            schema_version: ENGINE_SCHEMA_VERSION,
            function_addr,
            function_name_hash,
            arch_hash,
            blocks_hash,
            typed_context_hash,
            assumptions_hash,
            analysis_depth_hash,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EngineCacheLayer {
    Analysis,
    Artifact,
    Render,
    MetricsSnapshot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EngineCacheReuse {
    Disabled,
    Miss,
    Hit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EngineCachePlan {
    pub request: EngineRequestKind,
    pub layer: EngineCacheLayer,
    pub lookup: bool,
    pub store_on_miss: bool,
}

impl EngineCachePlan {
    pub fn lookup_store(request: EngineRequestKind, layer: EngineCacheLayer) -> Self {
        Self {
            request,
            layer,
            lookup: true,
            store_on_miss: true,
        }
    }

    pub fn disabled(request: EngineRequestKind, layer: EngineCacheLayer) -> Self {
        Self {
            request,
            layer,
            lookup: false,
            store_on_miss: false,
        }
    }

    pub fn for_request(request: EngineRequestKind) -> Self {
        match request {
            EngineRequestKind::Decompile => Self::lookup_store(request, EngineCacheLayer::Render),
            EngineRequestKind::Types | EngineRequestKind::SymbolicQuery => {
                Self::lookup_store(request, EngineCacheLayer::Artifact)
            }
            EngineRequestKind::DebugFacts => {
                Self::lookup_store(request, EngineCacheLayer::Analysis)
            }
            EngineRequestKind::Profile => {
                Self::disabled(request, EngineCacheLayer::MetricsSnapshot)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineCacheReuseDecision {
    pub request: EngineRequestKind,
    pub layer: EngineCacheLayer,
    pub reuse: EngineCacheReuse,
    pub reason: Option<String>,
}

impl EngineCacheReuseDecision {
    pub fn disabled(
        request: EngineRequestKind,
        layer: EngineCacheLayer,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            request,
            layer,
            reuse: EngineCacheReuse::Disabled,
            reason: Some(reason.into()),
        }
    }

    pub fn from_lookup(
        request: EngineRequestKind,
        layer: EngineCacheLayer,
        cache_hit: bool,
    ) -> Self {
        Self {
            request,
            layer,
            reuse: if cache_hit {
                EngineCacheReuse::Hit
            } else {
                EngineCacheReuse::Miss
            },
            reason: None,
        }
    }

    pub fn is_hit(&self) -> bool {
        matches!(self.reuse, EngineCacheReuse::Hit)
    }
}

#[derive(Debug, Clone)]
pub struct EngineCacheLookup<T> {
    pub value: Option<T>,
    pub decision: EngineCacheReuseDecision,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ArtifactCacheKey {
    pub analysis: AnalysisCacheKey,
    pub interproc_budget_hash: u64,
    pub symbolic_scope_hash: u64,
    pub semantic_schema_version: u32,
    pub semantic_claim_schema_version: u32,
}

pub type EngineFunctionKey = ArtifactCacheKey;

impl ArtifactCacheKey {
    #[allow(clippy::too_many_arguments)]
    pub fn from_parts(
        function_addr: u64,
        function_name: &str,
        arch: Option<&r2il::ArchSpec>,
        blocks: &[R2ILBlock],
        typed_context_hash: u64,
        assumptions_hash: u64,
        interproc_budget_hash: u64,
        symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
        analysis_depth: &str,
    ) -> Self {
        let analysis = AnalysisCacheKey::from_parts(
            function_addr,
            function_name,
            arch,
            blocks,
            typed_context_hash,
            assumptions_hash,
            analysis_depth,
        );
        Self::from_analysis(analysis, interproc_budget_hash, symbolic_scope)
    }

    pub fn from_analysis(
        analysis: AnalysisCacheKey,
        interproc_budget_hash: u64,
        symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    ) -> Self {
        Self::from_hashes(
            analysis,
            interproc_budget_hash,
            r2sym::stable_scope_hash(symbolic_scope),
        )
    }

    pub fn from_hashes(
        analysis: AnalysisCacheKey,
        interproc_budget_hash: u64,
        symbolic_scope_hash: u64,
    ) -> Self {
        Self {
            analysis,
            interproc_budget_hash,
            symbolic_scope_hash,
            semantic_schema_version: r2sym::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
            semantic_claim_schema_version: r2sym::SEMANTIC_CLAIM_SCHEMA_VERSION,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RenderCacheKey {
    pub artifact: ArtifactCacheKey,
    pub render_payload_hash: u64,
    pub render_config_hash: u64,
    pub render_schema_version: u32,
}

impl RenderCacheKey {
    pub fn from_artifact(
        artifact: ArtifactCacheKey,
        render_payload_hash: u64,
        render_config_hash: u64,
    ) -> Self {
        Self {
            artifact,
            render_payload_hash,
            render_config_hash,
            render_schema_version: ENGINE_SCHEMA_VERSION,
        }
    }

    pub fn from_payload<P, C>(
        artifact: ArtifactCacheKey,
        render_payload: &P,
        render_config: &C,
    ) -> Self
    where
        P: Hash + ?Sized,
        C: Hash + ?Sized,
    {
        Self::from_artifact(
            artifact,
            stable_fnv1a_hash(render_payload),
            stable_fnv1a_hash(render_config),
        )
    }
}

pub struct DecompileRenderCacheKeyInput<'a> {
    pub blocks: &'a [R2ILBlock],
    pub function_name: &'a str,
    pub arch: Option<&'a r2il::ArchSpec>,
    pub ptr_bits: u32,
    pub function_facts: &'a FunctionFacts,
    pub func_names_payload: &'a str,
    pub strings_payload: &'a str,
    pub symbols_payload: &'a str,
}

pub fn decompile_render_cache_key(input: DecompileRenderCacheKeyInput<'_>) -> RenderCacheKey {
    let analysis = AnalysisCacheKey::from_hashes(
        0,
        stable_fnv1a_hash(input.function_name),
        stable_fnv1a_debug_hash(&input.arch),
        stable_blocks_hash(input.blocks),
        stable_fnv1a_debug_hash(input.function_facts),
        u64::from(input.ptr_bits),
        stable_fnv1a_hash("decompile-render-v2-claim-schema"),
    );
    let artifact = ArtifactCacheKey::from_hashes(analysis, 0, 0);
    let render_payload_hash = stable_fnv1a_hash(&(
        "decompile-render-payload-v1",
        stable_fnv1a_hash(input.func_names_payload),
        stable_fnv1a_hash(input.strings_payload),
        stable_fnv1a_hash(input.symbols_payload),
    ));
    let render_config_hash = stable_fnv1a_hash(&(
        "decompile-render-config-v1",
        stable_fnv1a_debug_hash(&input.arch),
        input.ptr_bits,
        r2sym::SEMANTIC_CLAIM_SCHEMA_VERSION,
        r2sym::PROOF_COVERAGE_SCHEMA_VERSION,
    ));
    RenderCacheKey::from_artifact(artifact, render_payload_hash, render_config_hash)
}

#[derive(Debug, Clone, Default)]
pub struct EngineMetrics {
    pub cache_hit: bool,
    pub planning_time: Duration,
    pub ssa_time: Duration,
    pub semantic_time: Duration,
    pub type_time: Duration,
    pub render_time: Duration,
}

#[derive(Debug, Clone, Default)]
pub struct EngineArtifacts {
    pub prepared_ssa: Option<SsaArtifact>,
    pub pattern_ssa: Option<SsaArtifact>,
    pub semantic_artifact: Option<r2sym::SemanticArtifact>,
    pub function_facts: Option<FunctionFacts>,
    pub writeback_plan: Option<TypeWritebackPlan>,
    pub route: Option<r2dec::SemanticRoutePlan>,
    pub rendered: Option<String>,
    pub metrics: EngineMetrics,
    pub diagnostics: EngineDiagnostics,
}

#[derive(Debug, Clone)]
pub struct EngineAnalysis {
    pub ssa_func: SsaArtifact,
    pub pattern_ssa_func: SsaArtifact,
}

#[derive(Debug, Clone)]
pub struct EngineAnalysisArtifact {
    pub ssa_func: SsaArtifact,
    pub pattern_ssa_func: SsaArtifact,
    pub function_facts: FunctionFacts,
    pub writeback_plan: TypeWritebackPlan,
}

#[derive(Debug, Clone, Default)]
pub struct InterprocScopeFacts {
    summaries: BTreeMap<r2ssa::InterprocFunctionId, r2ssa::FunctionSemanticSummary>,
    identity_hash: u64,
}

impl InterprocScopeFacts {
    pub fn new(
        summaries: BTreeMap<r2ssa::InterprocFunctionId, r2ssa::FunctionSemanticSummary>,
    ) -> Self {
        Self {
            identity_hash: interproc_scope_identity_hash(&summaries),
            summaries,
        }
    }

    pub fn empty() -> Self {
        Self::new(BTreeMap::new())
    }

    pub fn identity_hash(&self) -> u64 {
        self.identity_hash
    }

    pub fn summaries(
        &self,
    ) -> &BTreeMap<r2ssa::InterprocFunctionId, r2ssa::FunctionSemanticSummary> {
        &self.summaries
    }
}

pub fn interproc_scope_facts_from_seed_entries<I>(entries: I) -> InterprocScopeFacts
where
    I: IntoIterator<Item = (u64, Option<String>, Option<usize>)>,
{
    let mut summaries = BTreeMap::new();
    for (addr, name, arg_count_hint) in entries {
        let id = r2ssa::InterprocFunctionId(addr);
        let Some(mut summary) = name
            .as_deref()
            .and_then(|name| r2sym::function_semantic_summary_seed_for_name(id, name))
            .or_else(|| {
                arg_count_hint.map(|_| r2ssa::FunctionSemanticSummary::unknown(id, name.clone()))
            })
        else {
            continue;
        };
        if arg_count_hint.is_some() {
            summary.arg_count_hint = arg_count_hint;
        }
        summaries.insert(id, summary);
    }
    InterprocScopeFacts::new(summaries)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EngineSemanticMode {
    Full,
    Optional,
}

#[derive(Debug, Clone)]
pub struct EngineAnalyzeRequest {
    pub function_name: String,
    pub function_addr: u64,
    pub blocks: Vec<R2ILBlock>,
    pub arch: Option<r2il::ArchSpec>,
    pub ptr_bits: u32,
    pub semantic_metadata_enabled: bool,
    pub reg_type_hints: HashMap<String, r2types::TypeHint>,
    pub parsed_context: r2types::ParsedExternalContext,
    pub external_context_fallback_hash: u64,
    pub scope_facts: InterprocScopeFacts,
    pub interproc_max_iterations: usize,
    pub symbolic_scope: Option<r2sym::PreparedFunctionScope>,
    pub precomputed_semantic_artifact: Option<r2sym::SemanticArtifact>,
    pub semantic_mode: EngineSemanticMode,
    pub include_interproc_summary_set: bool,
}

#[derive(Debug, Clone)]
pub struct EngineAnalyzeResponse {
    pub artifact: EngineAnalysisArtifact,
    pub analysis_cache_hit: bool,
    pub artifact_cache_hit: bool,
    pub artifact_key: ArtifactCacheKey,
    pub metrics: EngineMetrics,
    pub diagnostics: EngineDiagnostics,
}

#[derive(Debug, Clone)]
pub struct EngineDecompileRequest {
    pub function_name: String,
    pub prepared_ssa: SsaArtifact,
    pub function_facts: FunctionFacts,
    pub function_names: HashMap<u64, String>,
    pub strings: HashMap<u64, String>,
    pub symbols: HashMap<u64, String>,
    pub ptr_bits: u32,
    pub config: r2dec::DecompilerConfig,
    pub render_cache_key: Option<RenderCacheKey>,
    pub fallback_comment: Option<String>,
}

#[derive(Debug, Clone)]
pub struct EngineFunctionDecompileRequest {
    pub analysis: EngineAnalyzeRequest,
    pub display_name: String,
    pub function_names: HashMap<u64, String>,
    pub strings: HashMap<u64, String>,
    pub symbols: HashMap<u64, String>,
    pub config: r2dec::DecompilerConfig,
    pub func_names_payload: String,
    pub strings_payload: String,
    pub symbols_payload: String,
}

pub struct EngineTargetQueryRouteRequest<'ctx, 'a> {
    pub z3_ctx: &'ctx z3::Context,
    pub prepared: &'a SsaArtifact,
    pub scope: Option<&'a r2sym::PreparedFunctionScope>,
    pub compiled: &'a r2sym::SemanticArtifact,
    pub target_addr: u64,
    pub arch: Option<&'a r2il::ArchSpec>,
    pub symbol_map: &'a HashMap<u64, String>,
    pub explore_config: r2sym::ExploreConfig,
    pub summary_profile: r2sym::SummaryProfile,
    pub assumption_conflicted: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EngineSymbolicConfigProfile {
    DefaultQuery,
    PathListing,
}

pub enum EngineSymbolicStateSeed<'a> {
    Default {
        entry_addr: u64,
    },
    Scope {
        entry_addr: u64,
    },
    Replay {
        entry_addr: u64,
        seed: &'a r2sym::ReplaySeed,
    },
}

impl EngineSymbolicStateSeed<'_> {
    pub fn entry_addr(&self) -> u64 {
        match self {
            Self::Default { entry_addr }
            | Self::Scope { entry_addr }
            | Self::Replay { entry_addr, .. } => *entry_addr,
        }
    }

    pub fn display_entry_addr(&self) -> u64 {
        match self {
            Self::Replay { entry_addr, seed } => seed.entry_pc.unwrap_or(*entry_addr),
            Self::Default { entry_addr } | Self::Scope { entry_addr } => *entry_addr,
        }
    }
}

pub struct EngineSymbolicContextRequest<'ctx, 'a> {
    pub z3_ctx: &'ctx z3::Context,
    pub prepared: &'a SsaArtifact,
    pub scope: Option<&'a r2sym::PreparedFunctionScope>,
    pub arch: Option<&'a r2il::ArchSpec>,
    pub symbol_map: &'a HashMap<u64, String>,
    pub merge_states: bool,
    pub config_profile: EngineSymbolicConfigProfile,
    pub seed: EngineSymbolicStateSeed<'a>,
}

pub struct EngineSymbolicSummaryRequest<'ctx, 'a> {
    pub context: EngineSymbolicContextRequest<'ctx, 'a>,
    pub compile_semantics: bool,
}

pub struct EngineSymbolicSummaryResponse<'ctx> {
    pub summary: r2sym::SymbolicFunctionSummary<'ctx>,
    pub compiled: Option<r2sym::SemanticArtifact>,
    pub query_policy: r2sym::QueryExecutionPolicy,
    pub assumption_usage: r2ssa::AssumptionUsageReport,
    pub assumption_conditioned: bool,
}

pub struct EngineSymbolicPathsRequest<'ctx, 'a> {
    pub context: EngineSymbolicContextRequest<'ctx, 'a>,
}

pub struct EngineSymbolicPathsResponse<'ctx> {
    pub summary: r2sym::SymbolicFunctionSummary<'ctx>,
    pub explorer: r2sym::PathExplorer<'ctx>,
    pub solution_limit: usize,
    pub query_policy: r2sym::QueryExecutionPolicy,
    pub assumption_usage: r2ssa::AssumptionUsageReport,
    pub assumption_conditioned: bool,
}

pub struct EngineTargetExploreRequest<'ctx, 'a> {
    pub context: EngineSymbolicContextRequest<'ctx, 'a>,
    pub target_addr: u64,
}

pub struct EngineTargetExploreResponse<'ctx> {
    pub reach: r2sym::ReachabilityResult<'ctx>,
    pub explorer: r2sym::PathExplorer<'ctx>,
    pub compiled: r2sym::SemanticArtifact,
    pub selected_route: r2sym::TargetQueryRoutePlan,
    pub query_policy: r2sym::QueryExecutionPolicy,
}

pub struct EngineTargetSolveRequest<'ctx, 'a> {
    pub context: EngineSymbolicContextRequest<'ctx, 'a>,
    pub target_addr: u64,
}

pub struct EngineTargetSolveResponse<'ctx> {
    pub solve: r2sym::SolveResult<'ctx>,
    pub explorer: r2sym::PathExplorer<'ctx>,
    pub compiled: r2sym::SemanticArtifact,
    pub selected_route: r2sym::TargetQueryRoutePlan,
    pub query_policy: r2sym::QueryExecutionPolicy,
}

pub struct EngineRunSpecRequest<'ctx, 'a> {
    pub context: EngineSymbolicContextRequest<'ctx, 'a>,
    pub spec: &'a r2sym::ExplorationSpec,
}

pub struct EngineRunSpecResponse<'ctx> {
    pub result: r2sym::path::SpecExploreResult<'ctx>,
    pub explorer: r2sym::PathExplorer<'ctx>,
    pub stats: r2sym::path::ExploreStats,
    pub solver_stats: r2sym::SolverStats,
    pub query_policy: r2sym::QueryExecutionPolicy,
    pub assumption_usage: r2ssa::AssumptionUsageReport,
    pub assumption_conditioned: bool,
}

#[derive(Debug, Clone)]
pub struct EngineConditionedSymbolicScope {
    pub scope: r2sym::PreparedFunctionScope,
    pub prepared: r2ssa::SsaArtifact,
    pub assumption_usage: r2ssa::AssumptionUsageReport,
    pub assumption_conditioned: bool,
}

#[derive(Debug, Clone)]
pub struct EngineSummaryDecompileRequest {
    pub function_name: String,
    pub cfg_summary: CFGRiskSummary,
    pub function_facts: FunctionFacts,
    pub named_worker_guarded: bool,
    pub config: r2dec::DecompilerConfig,
    pub render_cache_key: Option<RenderCacheKey>,
    pub fallback_comment: Option<String>,
}

pub struct EngineSummaryPreprobeRequest<'a> {
    pub blocks: &'a [R2ILBlock],
    pub function_addr: u64,
    pub canonical_name: &'a str,
    pub display_name: &'a str,
    pub arch: Option<&'a r2il::ArchSpec>,
    pub ptr_bits: u32,
    pub parsed_context: &'a r2types::ParsedExternalContext,
    pub symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
    pub type_seed: Option<FunctionTypeFacts>,
    pub config: r2dec::DecompilerConfig,
    pub func_names_payload: &'a str,
    pub strings_payload: &'a str,
    pub symbols_payload: &'a str,
    pub fallback_if_guarded_without_summary: bool,
}

pub struct EngineDirectNamedWorkerDecompileRequest<'a> {
    pub function_addr: u64,
    pub function_name: &'a str,
    pub arch: Option<&'a r2il::ArchSpec>,
    pub ptr_bits: u32,
    pub parsed_context: &'a r2types::ParsedExternalContext,
    pub config: r2dec::DecompilerConfig,
}

pub struct EngineTypePreprobeRequest<'a> {
    pub blocks: &'a [R2ILBlock],
    pub function_addr: u64,
    pub canonical_name: &'a str,
    pub display_name: &'a str,
    pub arch: Option<&'a r2il::ArchSpec>,
    pub ptr_bits: u32,
    pub parsed_context: &'a r2types::ParsedExternalContext,
    pub symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
    pub type_seed: Option<FunctionTypeFacts>,
    pub caller_prefers_bounded_type_plan: bool,
    pub fallback_if_guarded_without_summary: bool,
}

pub struct EngineTypePreprobeResponse {
    pub cfg_summary: CFGRiskSummary,
    pub function_facts: FunctionFacts,
    pub route_decision: EngineTypeRouteDecision,
}

#[derive(Debug, Clone)]
pub struct EngineTypeAnalysisRequest {
    pub analysis: EngineAnalyzeRequest,
    pub caller_prefers_bounded_type_plan: bool,
}

#[derive(Debug, Clone)]
pub struct EngineTypeAnalysisResponse {
    pub cfg_summary: CFGRiskSummary,
    pub function_facts: FunctionFacts,
    pub writeback_plan: TypeWritebackPlan,
    pub route_decision: EngineTypeRouteDecision,
    pub semantic_route: Option<r2dec::SemanticRoutePlan>,
    pub callsite_count: usize,
    pub current_summary: Option<r2ssa::FunctionSemanticSummary>,
    pub artifact_cache_hit: bool,
    pub artifact_key: Option<ArtifactCacheKey>,
    pub metrics: EngineMetrics,
    pub diagnostics: EngineDiagnostics,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct EngineProfileRequest {
    pub reset_after_read: bool,
}

#[derive(Debug, Clone)]
pub struct EngineProfileResponse {
    pub route_decision: EngineProfileRouteDecision,
    pub metrics: EngineSessionCacheMetrics,
    pub total: CacheCounters,
    pub diagnostics: EngineDiagnostics,
}

#[derive(Debug, Clone)]
pub struct EngineDecompileResponse {
    pub output: String,
    pub decision: EngineRouteDecision,
    pub metrics: EngineMetrics,
    pub diagnostics: EngineDiagnostics,
}

pub struct EngineSession {
    analysis_cache: SessionCache<AnalysisCacheKey, EngineArtifacts>,
    artifact_cache: SessionCache<ArtifactCacheKey, EngineArtifacts>,
    render_cache: SessionCache<RenderCacheKey, String>,
}

impl Default for EngineSession {
    fn default() -> Self {
        Self::new(DEFAULT_ENGINE_CACHE_LIMIT)
    }
}

impl EngineSession {
    pub fn new(cache_limit: usize) -> Self {
        Self {
            analysis_cache: SessionCache::new(cache_limit),
            artifact_cache: SessionCache::new(cache_limit),
            render_cache: SessionCache::new(cache_limit),
        }
    }

    pub fn cached_analysis(&self, key: &AnalysisCacheKey) -> Option<EngineArtifacts> {
        self.cached_analysis_with_decision(EngineRequestKind::DebugFacts, key)
            .value
    }

    pub fn cached_analysis_with_decision(
        &self,
        request: EngineRequestKind,
        key: &AnalysisCacheKey,
    ) -> EngineCacheLookup<EngineArtifacts> {
        let value = self.analysis_cache.get_cloned(key);
        let decision = EngineCacheReuseDecision::from_lookup(
            request,
            EngineCacheLayer::Analysis,
            value.is_some(),
        );
        EngineCacheLookup { value, decision }
    }

    pub fn insert_analysis(
        &self,
        key: AnalysisCacheKey,
        artifacts: EngineArtifacts,
    ) -> EngineArtifacts {
        self.analysis_cache.insert_cloned(key, artifacts)
    }

    pub fn cached_artifacts(&self, key: &EngineFunctionKey) -> Option<EngineArtifacts> {
        self.cached_artifacts_with_decision(EngineRequestKind::Types, key)
            .value
    }

    pub fn cached_artifacts_with_decision(
        &self,
        request: EngineRequestKind,
        key: &EngineFunctionKey,
    ) -> EngineCacheLookup<EngineArtifacts> {
        let value = self.artifact_cache.get_cloned(key);
        let decision = EngineCacheReuseDecision::from_lookup(
            request,
            EngineCacheLayer::Artifact,
            value.is_some(),
        );
        EngineCacheLookup { value, decision }
    }

    pub fn insert_artifacts(
        &self,
        key: EngineFunctionKey,
        artifacts: EngineArtifacts,
    ) -> EngineArtifacts {
        self.artifact_cache.insert_cloned(key, artifacts)
    }

    pub fn clear_analysis_artifacts_for_function(
        &self,
        analysis_key: &AnalysisCacheKey,
        function_name_hash: u64,
    ) -> bool {
        self.artifact_cache.retain(|key, _| {
            key.analysis.arch_hash != analysis_key.arch_hash
                || key.analysis.blocks_hash != analysis_key.blocks_hash
                || key.analysis.function_name_hash != function_name_hash
        })
    }

    pub fn cached_render(&self, key: &RenderCacheKey) -> Option<String> {
        self.cached_render_with_decision(EngineRequestKind::Decompile, Some(key))
            .value
    }

    pub fn cached_render_with_decision(
        &self,
        request: EngineRequestKind,
        key: Option<&RenderCacheKey>,
    ) -> EngineCacheLookup<String> {
        let Some(key) = key else {
            return EngineCacheLookup {
                value: None,
                decision: EngineCacheReuseDecision::disabled(
                    request,
                    EngineCacheLayer::Render,
                    "render cache key unavailable",
                ),
            };
        };
        let value = self.render_cache.get_cloned(key);
        let decision = EngineCacheReuseDecision::from_lookup(
            request,
            EngineCacheLayer::Render,
            value.is_some(),
        );
        EngineCacheLookup { value, decision }
    }

    pub fn insert_render(&self, key: RenderCacheKey, rendered: String) -> String {
        self.render_cache.insert_cloned(key, rendered)
    }

    pub fn cache_metrics(&self) -> EngineSessionCacheMetrics {
        EngineSessionCacheMetrics {
            analysis: self.analysis_cache.counters(),
            artifacts: self.artifact_cache.counters(),
            renders: self.render_cache.counters(),
        }
    }

    pub fn reset_cache_metrics(&self) {
        self.analysis_cache.reset_counters();
        self.artifact_cache.reset_counters();
        self.render_cache.reset_counters();
    }

    pub fn profile(&self, request: EngineProfileRequest) -> EngineProfileResponse {
        let route_decision = profile_route_decision();
        let metrics = self.cache_metrics();
        let response = EngineProfileResponse {
            route_decision: route_decision.clone(),
            total: metrics.total(),
            metrics,
            diagnostics: EngineRequestPlan::profile(route_decision).diagnostics(),
        };
        if request.reset_after_read {
            self.reset_cache_metrics();
        }
        response
    }

    pub fn prepare_analysis(
        &self,
        function_name: &str,
        blocks: &[R2ILBlock],
        arch: Option<&r2il::ArchSpec>,
    ) -> Option<EngineAnalysis> {
        let key = function_analysis_cache_key(function_name, arch, blocks);
        if let Some(cached) = self
            .cached_analysis(&key)
            .and_then(engine_artifacts_to_analysis)
        {
            return Some(rename_engine_analysis(cached, function_name));
        }
        let analysis = build_engine_analysis_from_parts(function_name, blocks, arch)?;
        self.insert_analysis(key, engine_analysis_to_artifacts(analysis.clone()));
        Some(rename_engine_analysis(analysis, function_name))
    }

    pub fn analyze(&self, request: EngineAnalyzeRequest) -> Option<EngineAnalyzeResponse> {
        let started = std::time::Instant::now();
        let artifact_key = function_artifact_cache_key(&request);
        if let Some(response) = self.cached_analyze_with_key(&artifact_key, started.elapsed()) {
            return Some(response);
        }

        self.analyze_uncached_with_key(request, artifact_key, started)
    }

    fn analyze_uncached_with_key(
        &self,
        request: EngineAnalyzeRequest,
        artifact_key: ArtifactCacheKey,
        started: std::time::Instant,
    ) -> Option<EngineAnalyzeResponse> {
        let function_name = request.function_name.clone();

        let analysis_key = function_analysis_cache_key(
            &request.function_name,
            request.arch.as_ref(),
            &request.blocks,
        );
        let (analysis, analysis_cache_hit) = if let Some(cached) = self
            .cached_analysis(&analysis_key)
            .and_then(engine_artifacts_to_analysis)
        {
            (rename_engine_analysis(cached, &function_name), true)
        } else {
            let analysis = build_engine_analysis_from_parts(
                &function_name,
                &request.blocks,
                request.arch.as_ref(),
            )?;
            self.insert_analysis(analysis_key, engine_analysis_to_artifacts(analysis.clone()));
            (analysis, false)
        };

        let artifact = build_engine_analysis_artifact(&request, analysis)?;
        self.insert_artifacts(
            artifact_key.clone(),
            engine_analysis_artifact_to_artifacts(artifact.clone()),
        );
        Some(EngineAnalyzeResponse {
            artifact,
            analysis_cache_hit,
            artifact_cache_hit: false,
            artifact_key,
            metrics: EngineMetrics {
                cache_hit: false,
                planning_time: started.elapsed(),
                ..EngineMetrics::default()
            },
            diagnostics: EngineDiagnostics::default(),
        })
    }

    pub fn type_function(
        &self,
        request: EngineTypeAnalysisRequest,
    ) -> Option<EngineTypeAnalysisResponse> {
        let started = std::time::Instant::now();
        let analysis_request = request.analysis;
        let (arch_name, _, _) = r2dec::DecompilerConfig::for_arch(analysis_request.arch.as_ref());
        let type_seed = r2types::function_type_facts_from_parsed_context(
            &analysis_request.function_name,
            &analysis_request.parsed_context,
        );

        let preprobe = type_summary_preprobe(EngineTypePreprobeRequest {
            blocks: analysis_request.blocks.as_slice(),
            function_addr: analysis_request.function_addr,
            canonical_name: &analysis_request.function_name,
            display_name: &analysis_request.function_name,
            arch: analysis_request.arch.as_ref(),
            ptr_bits: analysis_request.ptr_bits,
            parsed_context: &analysis_request.parsed_context,
            symbolic_scope: analysis_request.symbolic_scope.as_ref(),
            type_seed: Some(type_seed),
            caller_prefers_bounded_type_plan: request.caller_prefers_bounded_type_plan,
            fallback_if_guarded_without_summary: false,
        })
        .filter(|preprobe| {
            !matches!(
                preprobe.route_decision.kind,
                EngineTypeRouteKind::FullWriteback
            )
        });
        if let Some(preprobe) = preprobe {
            let writeback_plan = type_writeback_plan_for_route(TypeWritebackPlanRouteInput {
                function_name: &analysis_request.function_name,
                arch_name: &arch_name,
                ptr_bits: analysis_request.ptr_bits,
                callconv: analysis_request.parsed_context.callconv.as_deref(),
                function_facts: &preprobe.function_facts,
                cfg_summary: &preprobe.cfg_summary,
                route: &preprobe.route_decision,
                full_writeback_plan: None,
            })?;
            let semantic_route = detached_semantic_route_plan(
                &analysis_request.function_name,
                analysis_request.blocks.as_slice(),
                &preprobe.function_facts,
            );
            return Some(EngineTypeAnalysisResponse {
                cfg_summary: preprobe.cfg_summary,
                function_facts: preprobe.function_facts,
                writeback_plan,
                route_decision: preprobe.route_decision,
                semantic_route,
                callsite_count: 0,
                current_summary: None,
                artifact_cache_hit: false,
                artifact_key: None,
                metrics: EngineMetrics {
                    cache_hit: false,
                    planning_time: started.elapsed(),
                    ..EngineMetrics::default()
                },
                diagnostics: EngineDiagnostics::default(),
            });
        }

        let analyze_response = self.analyze(analysis_request.clone())?;
        let artifact = analyze_response.artifact;
        let cfg_summary = artifact.ssa_func.function().cfg_risk_summary();
        let route_decision = type_route_decision(
            &artifact.function_facts,
            &cfg_summary,
            request.caller_prefers_bounded_type_plan,
        );
        let writeback_plan = type_writeback_plan_for_route(TypeWritebackPlanRouteInput {
            function_name: &analysis_request.function_name,
            arch_name: &arch_name,
            ptr_bits: analysis_request.ptr_bits,
            callconv: analysis_request.parsed_context.callconv.as_deref(),
            function_facts: &artifact.function_facts,
            cfg_summary: &cfg_summary,
            route: &route_decision,
            full_writeback_plan: Some(artifact.writeback_plan),
        })?;
        let semantic_route = detached_semantic_route_plan(
            &analysis_request.function_name,
            analysis_request.blocks.as_slice(),
            &artifact.function_facts,
        );
        let callsite_count =
            count_prepared_callsites(&artifact.pattern_ssa_func.local_ssa_blocks());
        let current_summary = current_interproc_summary(&artifact.function_facts);

        Some(EngineTypeAnalysisResponse {
            cfg_summary,
            function_facts: artifact.function_facts,
            writeback_plan,
            route_decision,
            semantic_route,
            callsite_count,
            current_summary,
            artifact_cache_hit: analyze_response.artifact_cache_hit,
            artifact_key: Some(analyze_response.artifact_key),
            metrics: EngineMetrics {
                cache_hit: analyze_response.metrics.cache_hit,
                planning_time: started.elapsed(),
                ..analyze_response.metrics
            },
            diagnostics: analyze_response.diagnostics,
        })
    }

    pub fn cached_analyze(&self, request: &EngineAnalyzeRequest) -> Option<EngineAnalyzeResponse> {
        let artifact_key = function_artifact_cache_key(request);
        self.cached_analyze_with_key(&artifact_key, Duration::default())
    }

    fn cached_analyze_with_key(
        &self,
        artifact_key: &ArtifactCacheKey,
        planning_time: Duration,
    ) -> Option<EngineAnalyzeResponse> {
        let artifact = self
            .cached_artifacts(artifact_key)
            .and_then(engine_artifacts_to_analysis_artifact)?;
        Some(EngineAnalyzeResponse {
            artifact,
            analysis_cache_hit: false,
            artifact_cache_hit: true,
            artifact_key: artifact_key.clone(),
            metrics: EngineMetrics {
                cache_hit: true,
                planning_time,
                ..EngineMetrics::default()
            },
            diagnostics: EngineDiagnostics::default(),
        })
    }

    pub fn decompile_function(
        &self,
        request: EngineFunctionDecompileRequest,
    ) -> EngineDecompileResponse {
        let started = std::time::Instant::now();
        let EngineFunctionDecompileRequest {
            analysis: analysis_request,
            display_name,
            function_names,
            strings,
            symbols,
            config,
            func_names_payload,
            strings_payload,
            symbols_payload,
        } = request;
        let canonical_name = analysis_request.function_name.clone();
        let display_name = if display_name.trim().is_empty() {
            canonical_name.clone()
        } else {
            display_name
        };
        let identity_aliases = [
            function_names
                .get(&analysis_request.function_addr)
                .map(String::as_str),
            symbols
                .get(&analysis_request.function_addr)
                .map(String::as_str),
        ];
        let identity = EngineFunctionIdentity::with_aliases(
            analysis_request.function_addr,
            &canonical_name,
            &display_name,
            identity_aliases.into_iter().flatten(),
        );
        let probe = decompile_probe_decision_for_identity(&analysis_request.blocks, &identity);
        let artifact_key = function_artifact_cache_key(&analysis_request);
        let cached = self.cached_analyze_with_key(&artifact_key, Duration::default());

        if cached.is_none()
            || should_prefer_full_decompile_for_named_worker(&probe.summary_probe_name)
        {
            let type_seed = r2types::function_type_facts_from_parsed_context(
                &display_name,
                &analysis_request.parsed_context,
            );
            if let Some(response) = self.decompile_summary_preprobe(EngineSummaryPreprobeRequest {
                blocks: &analysis_request.blocks,
                function_addr: analysis_request.function_addr,
                canonical_name: &canonical_name,
                display_name: &display_name,
                arch: analysis_request.arch.as_ref(),
                ptr_bits: analysis_request.ptr_bits,
                parsed_context: &analysis_request.parsed_context,
                symbolic_scope: analysis_request.symbolic_scope.as_ref(),
                type_seed: Some(type_seed),
                config: config.clone(),
                func_names_payload: &func_names_payload,
                strings_payload: &strings_payload,
                symbols_payload: &symbols_payload,
                fallback_if_guarded_without_summary: false,
            }) {
                return response;
            }
        }

        let analyze_response = if let Some(response) = cached {
            response
        } else if let Some(response) =
            self.analyze_uncached_with_key(analysis_request.clone(), artifact_key, started)
        {
            response
        } else {
            let type_seed = r2types::function_type_facts_from_parsed_context(
                &display_name,
                &analysis_request.parsed_context,
            );
            if let Some(response) = self.decompile_summary_preprobe(EngineSummaryPreprobeRequest {
                blocks: &analysis_request.blocks,
                function_addr: analysis_request.function_addr,
                canonical_name: &canonical_name,
                display_name: &display_name,
                arch: analysis_request.arch.as_ref(),
                ptr_bits: analysis_request.ptr_bits,
                parsed_context: &analysis_request.parsed_context,
                symbolic_scope: analysis_request.symbolic_scope.as_ref(),
                type_seed: Some(type_seed),
                config: config.clone(),
                func_names_payload: &func_names_payload,
                strings_payload: &strings_payload,
                symbols_payload: &symbols_payload,
                fallback_if_guarded_without_summary: true,
            }) {
                return response;
            }
            let reason = if probe.block_guarded {
                if probe.summary_probe_skipped_large_cfg {
                    probe
                        .cfg_guard_reason
                        .as_deref()
                        .unwrap_or("large native worker without canonical summary")
                } else {
                    "bounded native-worker preprobe without canonical summary"
                }
            } else {
                "failed to build detached analysis artifact"
            };
            return refused_decompile_response(&display_name, reason, started.elapsed());
        };

        let mut artifact =
            rename_engine_analysis_artifact(analyze_response.artifact, &display_name);
        if let Some(type_override) =
            decompile_type_override(&identity, &analysis_request, &artifact)
            && let Some(signature) = type_override.render_authorized_signature().cloned()
        {
            artifact.function_facts.types.merged_signature = Some(signature);
            artifact.function_facts.types.signature_certificate =
                type_override.signature_certificate;
        }

        let render_cache_key = decompile_render_cache_key(DecompileRenderCacheKeyInput {
            blocks: &analysis_request.blocks,
            function_name: &display_name,
            arch: analysis_request.arch.as_ref(),
            ptr_bits: analysis_request.ptr_bits,
            function_facts: &artifact.function_facts,
            func_names_payload: &func_names_payload,
            strings_payload: &strings_payload,
            symbols_payload: &symbols_payload,
        });
        let fallback_comment = r2dec::semantic_fallback_comment(
            &display_name,
            artifact.function_facts.semantics.as_ref(),
        )
        .or_else(|| {
            probe
                .cfg_guard_reason
                .as_ref()
                .map(|reason| r2dec::artifact_guard_fallback_comment(&display_name, reason))
        });

        self.decompile(EngineDecompileRequest {
            function_name: display_name,
            prepared_ssa: artifact.ssa_func,
            function_facts: artifact.function_facts,
            function_names,
            strings,
            symbols,
            ptr_bits: analysis_request.ptr_bits,
            config,
            render_cache_key: Some(render_cache_key),
            fallback_comment,
        })
    }

    pub fn decompile(&self, request: EngineDecompileRequest) -> EngineDecompileResponse {
        let started = std::time::Instant::now();
        let cfg_summary = request.prepared_ssa.function().cfg_risk_summary();
        let request_plan = plan_decompile_request(
            &request.function_name,
            &request.function_facts,
            Some(&request.prepared_ssa),
            &request.function_facts.types,
            &cfg_summary,
        );
        let diagnostics = request_plan.diagnostics();
        let EngineTypedRouteDecision::Decompile(decision) = request_plan.decision else {
            unreachable!("decompile request planning returned non-decompile decision");
        };
        let decision = *decision;
        let planning_time = started.elapsed();

        let cache_lookup = self.cached_render_with_decision(
            EngineRequestKind::Decompile,
            request.render_cache_key.as_ref(),
        );
        if let Some(output) = cache_lookup.value {
            return EngineDecompileResponse {
                output,
                decision,
                metrics: EngineMetrics {
                    cache_hit: true,
                    planning_time,
                    ..EngineMetrics::default()
                },
                diagnostics,
            };
        }

        let render_started = std::time::Instant::now();
        let output = render_engine_decompile_request(&request, &decision);
        let render_time = render_started.elapsed();
        if let Some(cache_key) = request.render_cache_key {
            self.insert_render(cache_key, output.clone());
        }

        EngineDecompileResponse {
            output,
            decision,
            metrics: EngineMetrics {
                cache_hit: false,
                planning_time,
                render_time,
                ..EngineMetrics::default()
            },
            diagnostics,
        }
    }

    pub fn decompile_summary(
        &self,
        request: EngineSummaryDecompileRequest,
    ) -> Option<EngineDecompileResponse> {
        let started = std::time::Instant::now();
        let mut decision = decompile_route_decision(
            &request.function_name,
            &request.function_facts,
            None,
            &request.function_facts.types,
            &request.cfg_summary,
        );
        if let Some(route) =
            named_worker_summary_route(request.named_worker_guarded, &request.function_facts)
        {
            decision.route = route;
            decision.plan =
                select_engine_plan(EngineRequestKind::Decompile, Some(&decision.route), None);
            decision.route_reason = semantic_route_reason(&decision.route);
            decision.refusal = match &decision.route {
                r2dec::SemanticRoutePlan::FallbackComment { comment } => Some(comment.clone()),
                _ => None,
            };
        }
        let request_plan = EngineRequestPlan::decompile(decision);
        let diagnostics = request_plan.diagnostics();
        let EngineTypedRouteDecision::Decompile(decision) = request_plan.decision else {
            unreachable!("decompile request planning returned non-decompile decision");
        };
        let decision = *decision;
        let planning_time = started.elapsed();
        if matches!(decision.route, r2dec::SemanticRoutePlan::Standard)
            && (request.fallback_comment.is_none()
                || prefers_standard_native_for_summary_only_worker(
                    &request.function_facts,
                    &request.cfg_summary,
                ))
        {
            return None;
        }

        let cache_lookup = self.cached_render_with_decision(
            EngineRequestKind::Decompile,
            request.render_cache_key.as_ref(),
        );
        if let Some(output) = cache_lookup.value {
            return Some(EngineDecompileResponse {
                output,
                decision,
                metrics: EngineMetrics {
                    cache_hit: true,
                    planning_time,
                    ..EngineMetrics::default()
                },
                diagnostics,
            });
        }

        let render_started = std::time::Instant::now();
        let output = render_engine_summary_decompile_request(&request, &decision)?;
        let render_time = render_started.elapsed();
        if let Some(cache_key) = request.render_cache_key {
            self.insert_render(cache_key, output.clone());
        }

        Some(EngineDecompileResponse {
            output,
            decision,
            metrics: EngineMetrics {
                cache_hit: false,
                planning_time,
                render_time,
                ..EngineMetrics::default()
            },
            diagnostics,
        })
    }

    pub fn decompile_summary_preprobe(
        &self,
        request: EngineSummaryPreprobeRequest<'_>,
    ) -> Option<EngineDecompileResponse> {
        let identity = EngineFunctionIdentity::new(
            request.function_addr,
            request.canonical_name,
            request.display_name,
        );
        let probe = decompile_probe_decision_for_identity(request.blocks, &identity);
        if !probe.summary_probe_needed {
            return None;
        }

        let cfg_summary = raw_cfg_risk_summary_for_preprobe(request.blocks);
        let semantic_artifact = native_worker_summary_artifact(
            request.blocks,
            &probe.summary_probe_name,
            request.arch,
            request.symbolic_scope,
            probe.summary_probe_skipped_large_cfg,
        );
        let type_seed = request
            .type_seed
            .unwrap_or_else(|| type_facts_from_parsed_context(request.parsed_context));
        let (arch_name, _, _) = r2dec::DecompilerConfig::for_arch(request.arch);
        let function_facts = if let Some(semantic_artifact) = semantic_artifact {
            let type_facts = type_facts_with_summary_projection_for_candidates_with_options(
                type_seed,
                request.display_name,
                identity.name_candidates(),
                &arch_name,
                request.ptr_bits,
                &semantic_artifact,
                SummaryProjectionOptions {
                    preserve_authoritative_context_signature:
                        parsed_context_current_signature_is_authoritative(request.parsed_context),
                },
            );
            r2types::FunctionFacts::new(type_facts, Some(semantic_artifact))
                .with_assumptions(request.parsed_context.assumptions.clone())
        } else if request.fallback_if_guarded_without_summary && probe.block_guarded {
            r2types::FunctionFacts::new(type_seed, None)
                .with_assumptions(request.parsed_context.assumptions.clone())
        } else {
            return None;
        };
        let fallback_comment = function_facts
            .semantic_artifact()
            .filter(|_| {
                has_renderable_primary_summary_only_native_worker(&function_facts)
                    && (probe.summary_probe_skipped_large_cfg
                        || has_renderable_native_linear_worker_summary(&function_facts))
            })
            .map(|artifact| summary_only_native_worker_fallback(request.display_name, artifact))
            .or_else(|| {
                (request.fallback_if_guarded_without_summary
                    && function_facts.semantic_artifact().is_none()
                    && probe.block_guarded)
                    .then(|| {
                        let reason = if probe.summary_probe_skipped_large_cfg {
                            probe
                                .cfg_guard_reason
                                .as_deref()
                                .unwrap_or("large native worker without canonical summary")
                        } else {
                            "bounded native-worker preprobe without canonical summary"
                        };
                        r2dec::artifact_guard_fallback_comment(request.display_name, reason)
                    })
            });
        let render_cache_key = decompile_render_cache_key(DecompileRenderCacheKeyInput {
            blocks: request.blocks,
            function_name: request.display_name,
            arch: request.arch,
            ptr_bits: request.ptr_bits,
            function_facts: &function_facts,
            func_names_payload: request.func_names_payload,
            strings_payload: request.strings_payload,
            symbols_payload: request.symbols_payload,
        });

        self.decompile_summary(EngineSummaryDecompileRequest {
            function_name: request.display_name.to_string(),
            cfg_summary,
            function_facts,
            named_worker_guarded: probe.named_worker_guarded,
            config: request.config,
            render_cache_key: Some(render_cache_key),
            fallback_comment,
        })
    }

    pub fn decompile_direct_named_worker_summary(
        &self,
        request: EngineDirectNamedWorkerDecompileRequest<'_>,
    ) -> Option<EngineDecompileResponse> {
        let identity =
            EngineFunctionIdentity::from_name(request.function_addr, request.function_name);
        let _applicability = direct_named_worker_summary_applicability_for_identity(&identity)?;

        let (arch_name, _, _) = r2dec::DecompilerConfig::for_arch(request.arch);
        let projection = native_worker_type_projection_for_identity(
            &identity,
            &arch_name,
            request.ptr_bits,
            request.parsed_context,
            true,
        )?;
        let cfg_summary = CFGRiskSummary {
            block_count: 0,
            loop_count: 0,
            back_edge_count: 0,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let render_cache_key = decompile_render_cache_key(DecompileRenderCacheKeyInput {
            blocks: &[],
            function_name: identity.primary_name(),
            arch: request.arch,
            ptr_bits: request.ptr_bits,
            function_facts: &projection.function_facts,
            func_names_payload: "direct-named-worker-summary-v1",
            strings_payload: "",
            symbols_payload: "",
        });

        self.decompile_summary(EngineSummaryDecompileRequest {
            function_name: identity.primary_name().to_string(),
            cfg_summary,
            function_facts: projection.function_facts,
            named_worker_guarded: true,
            config: request.config,
            render_cache_key: Some(render_cache_key),
            fallback_comment: None,
        })
    }

    pub fn symbolic_summary<'ctx>(
        &self,
        request: EngineSymbolicSummaryRequest<'ctx, '_>,
    ) -> EngineSymbolicSummaryResponse<'ctx> {
        let context = request.context;
        let (assumption_usage, assumption_conditioned) =
            prepared_assumption_conditioning(context.prepared);
        let mut query_config = symbolic_query_config_for_context(&context);
        let compiled = request.compile_semantics.then(|| {
            r2sym::compile_semantic_artifact_with_scope(
                context.z3_ctx,
                context.prepared,
                context.scope,
                context.arch,
                context.symbol_map,
                query_config.summary_profile,
            )
        });
        if compiled.as_ref().is_some_and(|compiled| {
            should_skip_expensive_symbolic_summary(compiled, context.prepared)
        }) {
            let initial_state = symbolic_initial_state(&context);
            let query_policy = symbolic_query_policy_for_state(
                &mut query_config,
                context.prepared,
                &initial_state,
                None,
            );
            return EngineSymbolicSummaryResponse {
                summary: empty_symbolic_summary(),
                compiled,
                query_policy,
                assumption_usage,
                assumption_conditioned,
            };
        }

        let initial_state = symbolic_initial_state(&context);
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            context.prepared,
            &initial_state,
            None,
        );
        let mut explorer = query_config.make_explorer(context.z3_ctx);
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let summary = explorer.summarize_function(context.prepared, initial_state);
        EngineSymbolicSummaryResponse {
            summary,
            compiled,
            query_policy,
            assumption_usage,
            assumption_conditioned,
        }
    }

    pub fn symbolic_paths<'ctx>(
        &self,
        request: EngineSymbolicPathsRequest<'ctx, '_>,
    ) -> EngineSymbolicPathsResponse<'ctx> {
        let context = request.context;
        let (assumption_usage, assumption_conditioned) =
            prepared_assumption_conditioning(context.prepared);
        let mut query_config = symbolic_query_config_for_context(&context);
        let initial_state = symbolic_initial_state(&context);
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            context.prepared,
            &initial_state,
            None,
        );
        let mut explorer = query_config.make_explorer(context.z3_ctx);
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let summary = explorer.summarize_function(context.prepared, initial_state);
        let solution_limit = path_listing_solution_limit(summary.paths.len(), context.prepared);
        EngineSymbolicPathsResponse {
            summary,
            explorer,
            solution_limit,
            query_policy,
            assumption_usage,
            assumption_conditioned,
        }
    }

    pub fn symbolic_target_explore<'ctx>(
        &self,
        request: EngineTargetExploreRequest<'ctx, '_>,
    ) -> EngineTargetExploreResponse<'ctx> {
        let context = request.context;
        let mut query_config = symbolic_query_config_for_context(&context);
        let compiled = r2sym::compile_query_semantic_artifact_with_scope(
            context.z3_ctx,
            context.prepared,
            context.scope,
            request.target_addr,
            context.arch,
            context.symbol_map,
            query_config.summary_profile,
        );
        let initial_state = symbolic_initial_state(&context);
        let selected_route = target_query_route_decision(EngineTargetQueryRouteRequest {
            z3_ctx: context.z3_ctx,
            prepared: context.prepared,
            scope: context.scope,
            compiled: &compiled,
            target_addr: request.target_addr,
            arch: context.arch,
            symbol_map: context.symbol_map,
            explore_config: query_config.explore.clone(),
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(context.prepared),
        });
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            context.prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer = query_config.make_explorer(context.z3_ctx);
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let reach = explorer.can_reach_with_artifact_in_scope(
            context.prepared,
            context.scope,
            Some(&compiled),
            initial_state,
            request.target_addr,
        );
        let selected_route = reach.selected_route.clone();
        EngineTargetExploreResponse {
            reach,
            explorer,
            compiled,
            selected_route,
            query_policy,
        }
    }

    pub fn symbolic_target_solve<'ctx>(
        &self,
        request: EngineTargetSolveRequest<'ctx, '_>,
    ) -> EngineTargetSolveResponse<'ctx> {
        let context = request.context;
        let mut query_config = symbolic_query_config_for_context(&context);
        let compiled = match context.seed {
            EngineSymbolicStateSeed::Replay { seed, .. } => {
                r2sym::compile_query_semantic_artifact_with_scope_and_replay_seed(
                    context.z3_ctx,
                    context.prepared,
                    context.scope,
                    request.target_addr,
                    context.arch,
                    context.symbol_map,
                    query_config.summary_profile,
                    Some(seed),
                )
            }
            EngineSymbolicStateSeed::Default { .. } | EngineSymbolicStateSeed::Scope { .. } => {
                r2sym::compile_query_semantic_artifact_with_scope(
                    context.z3_ctx,
                    context.prepared,
                    context.scope,
                    request.target_addr,
                    context.arch,
                    context.symbol_map,
                    query_config.summary_profile,
                )
            }
        };
        let initial_state = symbolic_initial_state(&context);
        let selected_route = target_query_route_decision(EngineTargetQueryRouteRequest {
            z3_ctx: context.z3_ctx,
            prepared: context.prepared,
            scope: context.scope,
            compiled: &compiled,
            target_addr: request.target_addr,
            arch: context.arch,
            symbol_map: context.symbol_map,
            explore_config: query_config.explore.clone(),
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(context.prepared),
        });
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            context.prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer = query_config.make_explorer(context.z3_ctx);
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let solve = explorer.solve_for_target_with_artifact_in_scope(
            context.prepared,
            context.scope,
            Some(&compiled),
            initial_state,
            request.target_addr,
        );
        let selected_route = solve.selected_route.clone();
        EngineTargetSolveResponse {
            solve,
            explorer,
            compiled,
            selected_route,
            query_policy,
        }
    }

    pub fn symbolic_run_spec<'ctx>(
        &self,
        request: EngineRunSpecRequest<'ctx, '_>,
    ) -> Result<EngineRunSpecResponse<'ctx>, String> {
        let context = request.context;
        let (assumption_usage, assumption_conditioned) =
            prepared_assumption_conditioning(context.prepared);
        let mut query_config = symbolic_query_config_for_context(&context);
        let start_pc = request.spec.start_pc(context.seed.entry_addr())?;
        let mut initial_state = symbolic_initial_state_at(&context, start_pc);
        request.spec.apply_to_state(&mut initial_state);
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            context.prepared,
            &initial_state,
            None,
        );
        let mut explorer = r2sym::PathExplorer::with_config(
            context.z3_ctx,
            request.spec.to_explore_config(&query_config.explore),
        );
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let result = explorer.run_spec(context.prepared, initial_state, request.spec)?;
        let stats = explorer.stats().clone();
        let solver_stats = explorer.solver().stats();
        Ok(EngineRunSpecResponse {
            result,
            explorer,
            stats,
            solver_stats,
            query_policy,
            assumption_usage,
            assumption_conditioned,
        })
    }
}

pub fn default_symbolic_query_config(merge_states: bool) -> r2sym::SymQueryConfig {
    r2sym::SymQueryConfig {
        explore: r2sym::ExploreConfig {
            max_states: 200,
            max_depth: 800,
            merge_states,
            timeout: Some(Duration::from_secs(20)),
            ..Default::default()
        },
        mode: r2sym::QueryMode::TargetGuided,
        summary_profile: r2sym::SummaryProfile::Default,
        solve_tactics: r2sym::SolveTacticConfig::default(),
    }
}

pub fn path_listing_query_config(
    prepared: &r2ssa::SsaArtifact,
    merge_states: bool,
) -> r2sym::SymQueryConfig {
    let mut config = default_symbolic_query_config(merge_states);
    if prepared.call_sites().by_id.is_empty() {
        config.explore.max_states = SYMBOLIC_PATHS_CALL_FREE_MAX_STATES;
        config.explore.max_depth = SYMBOLIC_PATHS_CALL_FREE_MAX_DEPTH;
    } else {
        config.explore.max_states = SYMBOLIC_PATHS_CALL_HEAVY_MAX_STATES;
        config.explore.max_depth = SYMBOLIC_PATHS_CALL_HEAVY_MAX_DEPTH;
    }
    config.explore.timeout = Some(Duration::from_millis(SYMBOLIC_PATHS_TIMEOUT_MS));
    config.explore.max_completed_paths = Some(SYMBOLIC_PATHS_LIMIT);
    config.summary_profile = r2sym::SummaryProfile::PathListing;
    config
}

pub fn path_listing_solution_limit(result_count: usize, prepared: &r2ssa::SsaArtifact) -> usize {
    if !prepared.call_sites().by_id.is_empty() {
        return 0;
    }
    if result_count <= SYMBOLIC_PATHS_SOLUTION_LIMIT {
        result_count
    } else {
        0
    }
}

pub fn symbolic_query_policy_for_state(
    config: &mut r2sym::SymQueryConfig,
    prepared: &r2ssa::SsaArtifact,
    initial_state: &r2sym::SymState<'_>,
    route: Option<&r2sym::TargetQueryRoutePlan>,
) -> r2sym::QueryExecutionPolicy {
    let route = route
        .cloned()
        .unwrap_or_else(r2sym::TargetQueryRoutePlan::dynamic_fallback);
    let policy = r2sym::QueryExecutionPolicy::for_route(config, prepared, initial_state, route);
    r2sym::apply_query_execution_policy(config, &policy);
    policy
}

pub fn prepared_assumption_conflicted(prepared: &r2ssa::SsaArtifact) -> bool {
    !prepared.facts().assumption_usage.conflicts.is_empty()
}

pub fn prepared_assumption_conditioning(
    prepared: &r2ssa::SsaArtifact,
) -> (r2ssa::AssumptionUsageReport, bool) {
    let usage = prepared.facts().assumption_usage.clone();
    let conditioned = !usage.applied.is_empty() || !usage.conflicts.is_empty();
    (usage, conditioned)
}

pub fn condition_symbolic_scope_with_assumptions(
    scope: &r2sym::PreparedFunctionScope,
    assumptions: &r2ssa::AssumptionSet,
) -> Result<EngineConditionedSymbolicScope, &'static str> {
    let root = scope.root().ok_or("failed to build root SSA function")?;
    let prepared = if assumptions.is_empty() {
        root.prepared.clone()
    } else {
        root.prepared.with_assumptions(assumptions)
    };
    let scope = if assumptions.is_empty() {
        scope.clone()
    } else {
        scope
            .with_prepared_root(&prepared)
            .ok_or("failed to build symbolic scope")?
    };
    let (assumption_usage, assumption_conditioned) = prepared_assumption_conditioning(&prepared);
    Ok(EngineConditionedSymbolicScope {
        scope,
        prepared,
        assumption_usage,
        assumption_conditioned,
    })
}

fn symbolic_query_config_for_context(
    context: &EngineSymbolicContextRequest<'_, '_>,
) -> r2sym::SymQueryConfig {
    match context.config_profile {
        EngineSymbolicConfigProfile::DefaultQuery => {
            default_symbolic_query_config(context.merge_states)
        }
        EngineSymbolicConfigProfile::PathListing => {
            path_listing_query_config(context.prepared, context.merge_states)
        }
    }
}

fn symbolic_initial_state<'ctx>(
    context: &EngineSymbolicContextRequest<'ctx, '_>,
) -> r2sym::SymState<'ctx> {
    symbolic_initial_state_at(context, context.seed.display_entry_addr())
}

fn symbolic_initial_state_at<'ctx>(
    context: &EngineSymbolicContextRequest<'ctx, '_>,
    entry_addr: u64,
) -> r2sym::SymState<'ctx> {
    let mut initial_state = r2sym::SymState::new(context.z3_ctx, entry_addr);
    match context.seed {
        EngineSymbolicStateSeed::Default { .. } => {
            r2sym::seed_default_state_for_arch(&mut initial_state, context.prepared, context.arch);
        }
        EngineSymbolicStateSeed::Scope { .. } => {
            if let Some(scope) = context.scope {
                r2sym::seed_scope_state_for_arch(
                    &mut initial_state,
                    context.prepared,
                    scope,
                    context.arch,
                );
            } else {
                r2sym::seed_default_state_for_arch(
                    &mut initial_state,
                    context.prepared,
                    context.arch,
                );
            }
        }
        EngineSymbolicStateSeed::Replay { seed, .. } => {
            r2sym::seed_replay_state_for_arch(
                &mut initial_state,
                Some(context.prepared),
                context.arch,
                seed,
            );
        }
    }
    initial_state
}

fn install_symbolic_hooks_for_context<'ctx>(
    explorer: &mut r2sym::PathExplorer<'ctx>,
    context: &EngineSymbolicContextRequest<'ctx, '_>,
    policy: &r2sym::QueryExecutionPolicy,
) {
    if let Some(scope) = context.scope {
        r2sym::install_symbolic_hooks_for_query_policy(
            explorer,
            context.z3_ctx,
            scope,
            context.arch,
            context.symbol_map,
            symbolic_query_config_for_context(context).summary_profile,
            policy,
        );
    }
}

fn empty_symbolic_summary<'ctx>() -> r2sym::SymbolicFunctionSummary<'ctx> {
    r2sym::SymbolicFunctionSummary {
        completion: r2sym::QueryCompletion::Complete,
        paths: Vec::new(),
        feasible_paths: 0,
        stats: r2sym::path::ExploreStats::default(),
        solver_stats: r2sym::SolverStats::default(),
    }
}

fn should_skip_expensive_symbolic_summary(
    compiled: &r2sym::SemanticArtifact,
    prepared: &r2ssa::SsaArtifact,
) -> bool {
    compiled.diagnostics.skipped_large_cfg
        || prepared.function().cfg_risk_summary().block_count > 96
}

fn render_engine_decompile_request(
    request: &EngineDecompileRequest,
    decision: &EngineRouteDecision,
) -> String {
    if let Some(output) = render_semantic_route(
        &request.function_name,
        &request.function_facts,
        &decision.route,
        request.config.clone(),
    ) {
        return output;
    }

    let suppress_unrenderable_summary = should_suppress_unrenderable_standard_summary_artifact(
        &decision.route,
        &request.function_facts,
    );
    let mut function_facts = request.function_facts.clone();
    if suppress_unrenderable_summary {
        function_facts.set_semantics(None);
    }
    let context = r2dec::DecompilerContext::from_function_facts(
        function_facts,
        request.function_names.clone(),
        request.strings.clone(),
        request.symbols.clone(),
        request.ptr_bits,
    );
    let context = decompiler_context_with_route_decision(context, decision);
    let input = r2dec::DecompilerInput::new(request.prepared_ssa.clone(), context);
    let output = r2dec::Decompiler::new(request.config.clone()).decompile_input(&input);
    if !output.trim().is_empty() {
        return output;
    }

    request
        .fallback_comment
        .clone()
        .filter(|_| !suppress_unrenderable_summary)
        .unwrap_or_else(|| {
            format!(
                "/* r2dec fallback: skipped decompilation for {} (empty output) */",
                request.function_name
            )
        })
}

fn should_suppress_unrenderable_standard_summary_artifact(
    route: &r2dec::SemanticRoutePlan,
    function_facts: &FunctionFacts,
) -> bool {
    if !matches!(route, r2dec::SemanticRoutePlan::Standard) {
        return false;
    }
    let Some(artifact) = function_facts.semantic_artifact() else {
        return false;
    };
    if artifact.granularity != r2sym::ArtifactGranularity::SummaryOnly
        || artifact.diagnostics.skipped_large_cfg
        || !matches!(
            artifact.decompile_plan(),
            r2sym::DecompilePlan::NativeLinear { .. }
        )
    {
        return false;
    }
    artifact
        .native_body()
        .is_some_and(|native| !native_body_has_renderable_worker_summary(native))
}

fn decompile_type_override(
    identity: &EngineFunctionIdentity,
    request: &EngineAnalyzeRequest,
    artifact: &EngineAnalysisArtifact,
) -> Option<FunctionTypeFacts> {
    let facts = r2types::function_type_facts_from_parsed_context(
        &request.function_name,
        &request.parsed_context,
    );
    if facts.render_authorized_signature().is_some() {
        return Some(facts);
    }

    let (arch_name, _, _) = r2dec::DecompilerConfig::for_arch(request.arch.as_ref());
    if let Some(projection) = native_worker_type_projection_for_identity(
        identity,
        &arch_name,
        request.ptr_bits,
        &request.parsed_context,
        true,
    ) {
        let facts = projection.function_facts.types;
        if facts.render_authorized_signature().is_some() {
            return Some(facts);
        }
    }

    let facts = r2types::inferred_signature_to_function_type_facts(
        &artifact.writeback_plan.signature,
        request.ptr_bits,
    );
    facts
        .render_authorized_signature()
        .is_some()
        .then_some(facts)
}

fn refused_decompile_response(
    function_name: &str,
    reason: &str,
    planning_time: Duration,
) -> EngineDecompileResponse {
    let output = r2dec::artifact_guard_fallback_comment(function_name, reason);
    let render_permission =
        r2sym::RenderPermission::refuse(r2sym::ProofOwner::R2engine, reason.to_string());
    EngineDecompileResponse {
        output: output.clone(),
        decision: EngineRouteDecision {
            request: EngineRequestKind::Decompile,
            plan: EnginePlan::RefuseWithEvidence,
            route: r2dec::SemanticRoutePlan::FallbackComment {
                comment: output.clone(),
            },
            route_reason: Some(reason.to_string()),
            skip_runtime_type_inference: true,
            use_prepared_semantic_view: false,
            proof_coverage: r2sym::ProofCoverage {
                refusals: 1,
                ..r2sym::ProofCoverage::default()
            },
            render_permission: render_permission.clone(),
            refusal: Some(output.clone()),
        },
        metrics: EngineMetrics {
            cache_hit: false,
            planning_time,
            ..EngineMetrics::default()
        },
        diagnostics: EngineDiagnostics {
            plan: Some(EnginePlan::RefuseWithEvidence),
            route_reason: Some(reason.to_string()),
            proof_coverage: Some(r2sym::ProofCoverage {
                refusals: 1,
                ..r2sym::ProofCoverage::default()
            }),
            render_permission: Some(render_permission),
            warnings: Vec::new(),
            refusal: Some(output),
        },
    }
}

fn render_engine_summary_decompile_request(
    request: &EngineSummaryDecompileRequest,
    decision: &EngineRouteDecision,
) -> Option<String> {
    render_semantic_route(
        &request.function_name,
        &request.function_facts,
        &decision.route,
        request.config.clone(),
    )
    .or_else(|| request.fallback_comment.clone())
    .filter(|output| !output.trim().is_empty())
}

pub fn function_analysis_cache_key(
    _function_name: &str,
    arch: Option<&r2il::ArchSpec>,
    blocks: &[R2ILBlock],
) -> AnalysisCacheKey {
    AnalysisCacheKey::from_hashes(
        0,
        0,
        arch.map(stable_fnv1a_debug_hash).unwrap_or(0),
        stable_blocks_hash(blocks),
        0,
        0,
        0,
    )
}

pub fn function_artifact_cache_key(request: &EngineAnalyzeRequest) -> ArtifactCacheKey {
    let analysis = AnalysisCacheKey::from_hashes(
        request.function_addr,
        stable_fnv1a_hash(request.function_name.as_str()),
        request
            .arch
            .as_ref()
            .map(stable_fnv1a_debug_hash)
            .unwrap_or(0),
        stable_blocks_hash(&request.blocks),
        session_context_identity_hash_from_parsed(
            &request.parsed_context,
            request.external_context_fallback_hash,
        ),
        assumptions_identity_hash(&request.parsed_context.assumptions),
        function_analysis_depth_hash(request.semantic_metadata_enabled),
    );
    ArtifactCacheKey::from_hashes(
        analysis,
        stable_fnv1a_hash(&(
            "interproc-scope-budget-v1",
            request.scope_facts.identity_hash(),
            request.interproc_max_iterations,
            request.include_interproc_summary_set,
            request.semantic_mode,
            request
                .precomputed_semantic_artifact
                .as_ref()
                .map(stable_fnv1a_debug_hash),
        )),
        r2sym::stable_scope_hash(request.symbolic_scope.as_ref()),
    )
}

pub fn assumptions_identity_hash(assumptions: &r2ssa::AssumptionSet) -> u64 {
    if assumptions.is_empty() {
        return 0;
    }
    let mut item_hashes = assumptions
        .iter()
        .map(stable_fnv1a_debug_hash)
        .collect::<Vec<_>>();
    item_hashes.sort_unstable();
    stable_fnv1a_hash(&("r2ssa-assumptions-v1", item_hashes))
}

pub fn function_analysis_depth_hash(semantic_metadata_enabled: bool) -> u64 {
    stable_fnv1a_hash(&("function-analysis-artifact-v2", semantic_metadata_enabled))
}

pub fn session_context_identity_hash_from_parsed(
    parsed: &r2types::ParsedExternalContext,
    fallback_hash: u64,
) -> u64 {
    match (
        parsed.context_hash,
        parsed.context_dirty_epoch,
        parsed.type_dirty_epoch,
    ) {
        (None, None, None) => fallback_hash,
        (context_hash, dirty_epoch, type_dirty_epoch) => stable_fnv1a_hash(&(
            "radare2-typed-context",
            parsed.context_schema_version,
            context_hash.unwrap_or(fallback_hash),
            dirty_epoch,
            type_dirty_epoch,
        )),
    }
}

fn engine_analysis_to_artifacts(analysis: EngineAnalysis) -> EngineArtifacts {
    EngineArtifacts {
        prepared_ssa: Some(analysis.ssa_func),
        pattern_ssa: Some(analysis.pattern_ssa_func),
        ..EngineArtifacts::default()
    }
}

fn engine_artifacts_to_analysis(artifacts: EngineArtifacts) -> Option<EngineAnalysis> {
    Some(EngineAnalysis {
        ssa_func: artifacts.prepared_ssa?,
        pattern_ssa_func: artifacts.pattern_ssa?,
    })
}

fn engine_analysis_artifact_to_artifacts(artifact: EngineAnalysisArtifact) -> EngineArtifacts {
    EngineArtifacts {
        prepared_ssa: Some(artifact.ssa_func),
        pattern_ssa: Some(artifact.pattern_ssa_func),
        semantic_artifact: artifact.function_facts.semantics.clone(),
        function_facts: Some(artifact.function_facts),
        writeback_plan: Some(artifact.writeback_plan),
        ..EngineArtifacts::default()
    }
}

fn engine_artifacts_to_analysis_artifact(
    artifacts: EngineArtifacts,
) -> Option<EngineAnalysisArtifact> {
    Some(EngineAnalysisArtifact {
        ssa_func: artifacts.prepared_ssa?,
        pattern_ssa_func: artifacts.pattern_ssa?,
        function_facts: artifacts.function_facts?,
        writeback_plan: artifacts.writeback_plan?,
    })
}

fn rename_engine_analysis(analysis: EngineAnalysis, function_name: &str) -> EngineAnalysis {
    EngineAnalysis {
        ssa_func: analysis.ssa_func.with_name(function_name),
        pattern_ssa_func: analysis.pattern_ssa_func.with_name(function_name),
    }
}

pub fn rename_engine_analysis_artifact(
    artifact: EngineAnalysisArtifact,
    function_name: &str,
) -> EngineAnalysisArtifact {
    EngineAnalysisArtifact {
        ssa_func: artifact.ssa_func.with_name(function_name),
        pattern_ssa_func: artifact.pattern_ssa_func.with_name(function_name),
        function_facts: artifact.function_facts,
        writeback_plan: artifact.writeback_plan,
    }
}

fn build_engine_analysis_from_parts(
    function_name: &str,
    blocks: &[R2ILBlock],
    arch: Option<&r2il::ArchSpec>,
) -> Option<EngineAnalysis> {
    let ssa_func = r2ssa::SsaArtifact::for_decompile(blocks, arch)?.with_name(function_name);
    let pattern_ssa_func = if should_reuse_decompile_ssa_for_pattern_analysis(&ssa_func) {
        ssa_func.clone()
    } else {
        r2ssa::SsaArtifact::for_patterns(blocks, arch)?.with_name(function_name)
    };
    Some(EngineAnalysis {
        ssa_func,
        pattern_ssa_func,
    })
}

fn should_reuse_decompile_ssa_for_pattern_analysis(prepared: &r2ssa::SsaArtifact) -> bool {
    let summary = prepared.function().cfg_risk_summary();
    summary.block_count >= 96
        && summary.switch_block_count > 0
        && summary.max_switch_cases >= 32
        && summary.back_edge_count == 0
}

pub fn build_interproc_summary_set_with_scope_facts(
    function_name: &str,
    function_addr: u64,
    arch: Option<&r2il::ArchSpec>,
    analysis: &EngineAnalysis,
    scope_facts: &InterprocScopeFacts,
    max_iterations: usize,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> r2ssa::InterprocSummarySet {
    let root = r2ssa::InterprocFunctionId(function_addr);
    let mut seeds = scope_facts.summaries.clone();
    if let Some(scope) = symbolic_scope {
        for function in scope.functions().values() {
            let Some(name) = function.name.as_deref() else {
                continue;
            };
            if let Some(summary) = r2sym::function_semantic_summary_seed_for_name(function.id, name)
            {
                seeds.entry(function.id).or_insert(summary);
            }
        }
    }
    let seeded_helpers = seeds
        .keys()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    let mut functions = vec![r2ssa::InterprocFunctionInput {
        id: root,
        name: Some(function_name.to_string()),
        prepared: &analysis.ssa_func,
    }];
    if let Some(scope) = symbolic_scope {
        for function in scope.functions().values() {
            if function.id == root || seeded_helpers.contains(&function.id) {
                continue;
            }
            functions.push(r2ssa::InterprocFunctionInput {
                id: function.id,
                name: function.name.clone(),
                prepared: &function.prepared,
            });
        }
    }
    r2ssa::solve_interproc_summary_set(
        &functions,
        arch,
        Some(root),
        &seeds,
        r2ssa::InterprocSolveConfig {
            max_iterations: max_iterations.max(1),
        },
    )
}

fn build_engine_analysis_artifact(
    request: &EngineAnalyzeRequest,
    analysis: EngineAnalysis,
) -> Option<EngineAnalysisArtifact> {
    let interproc_summary_set = request.include_interproc_summary_set.then(|| {
        build_interproc_summary_set_with_scope_facts(
            &request.function_name,
            request.function_addr,
            request.arch.as_ref(),
            &analysis,
            &request.scope_facts,
            request.interproc_max_iterations,
            request.symbolic_scope.as_ref(),
        )
    });
    let semantic_analysis = if request.parsed_context.assumptions.is_empty() {
        analysis.clone()
    } else {
        EngineAnalysis {
            ssa_func: analysis
                .ssa_func
                .with_assumptions(&request.parsed_context.assumptions),
            pattern_ssa_func: analysis
                .pattern_ssa_func
                .with_assumptions(&request.parsed_context.assumptions),
        }
    };
    let pattern_ssa_blocks = semantic_analysis.pattern_ssa_func.local_ssa_blocks();
    let (arch_name, _, _) = r2dec::DecompilerConfig::for_arch(request.arch.as_ref());
    let signature = infer_signature_from_engine_analysis(
        &request.function_name,
        &arch_name,
        request.ptr_bits,
        request.arch.as_ref(),
        request.semantic_metadata_enabled,
        &request.reg_type_hints,
        &analysis,
    )?;
    let mut diagnostics = r2types::TypeWritebackDiagnostics::default();
    let local_structs = r2types::infer_local_struct_artifacts_from_ssa(
        &pattern_ssa_blocks,
        Some(arch_name.as_str()),
        request.ptr_bits,
        &mut diagnostics,
    );
    let local_field_accesses = r2types::local_field_accesses_from_struct_artifacts(&local_structs);
    let optional_semantics_required = optional_semantics_required_for_analysis(
        &request.parsed_context,
        &semantic_analysis.ssa_func,
        &pattern_ssa_blocks,
        !local_field_accesses.is_empty(),
    );
    let root_summary = interproc_summary_set.as_ref().and_then(|summary_set| {
        summary_set
            .root
            .and_then(|root| summary_set.summaries.get(&root))
    });
    let semantic_artifact = request.precomputed_semantic_artifact.clone().or_else(|| {
        if matches!(request.semantic_mode, EngineSemanticMode::Full) {
            if should_skip_full_semantics_for_layout_backed_prepared_proofs(
                &request.parsed_context,
                &semantic_analysis.ssa_func,
                &pattern_ssa_blocks,
            ) {
                return None;
            }
            if should_skip_full_semantics_for_opaque_layout(
                &request.parsed_context,
                &semantic_analysis.ssa_func,
            ) {
                return None;
            }
            return maybe_compile_semantic_artifact_for_analysis(
                &semantic_analysis.ssa_func,
                request.function_addr,
                &request.function_name,
                request.symbolic_scope.as_ref(),
                request.arch.as_ref(),
                root_summary,
            );
        }
        optional_semantics_required.then(|| {
            r2sym::compile_semantic_artifact_default_with_scope(
                &z3::Context::thread_local(),
                &semantic_analysis.ssa_func,
                request.symbolic_scope.as_ref(),
                request.arch.as_ref(),
            )
        })
    });
    let recovered_vars = r2types::recover_vars_from_ssa(
        &pattern_ssa_blocks,
        request.arch.as_ref().map(|spec| spec.name.as_str()),
        &request.reg_type_hints,
        request.semantic_metadata_enabled,
    );
    let recovered_vars = recovered_vars.to_vec();
    let writeback_input = r2types::TypeWritebackAnalysisInput {
        function_name: &request.function_name,
        ptr_bits: request.ptr_bits,
        inferred_signature: signature,
        recovered_vars: &recovered_vars,
        ssa_blocks: &pattern_ssa_blocks,
        parsed_context: request.parsed_context.clone(),
        local_structs,
        interproc_summary_set,
        diagnostics,
    };
    let writeback = if let Some(semantic_artifact) = semantic_artifact.as_ref() {
        r2types::build_type_writeback_analysis_with_semantics(
            writeback_input,
            r2types::TypeWritebackSemanticInputs {
                artifact: semantic_artifact,
                local_field_accesses: &local_field_accesses,
            },
        )
    } else {
        r2types::build_type_writeback_analysis(writeback_input)
    };
    let mut function_facts = writeback.function_facts;
    let mut usage = semantic_analysis.ssa_func.facts().assumption_usage.clone();
    usage.extend(&function_facts.assumption_usage);
    function_facts.assumption_usage = usage;
    function_facts.merge_proof_coverage(r2sym::ProofCoverage::from_prepared_certificates(
        semantic_analysis.ssa_func.certificates(),
    ));
    function_facts.merge_proof_coverage(proof_coverage_from_type_facts(&function_facts.types));
    Some(EngineAnalysisArtifact {
        ssa_func: semantic_analysis.ssa_func,
        pattern_ssa_func: semantic_analysis.pattern_ssa_func,
        function_facts,
        writeback_plan: writeback.plan,
    })
}

fn maybe_compile_semantic_artifact_for_analysis(
    ssa_func: &SsaArtifact,
    function_addr: u64,
    function_name: &str,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    arch: Option<&r2il::ArchSpec>,
    root_summary: Option<&r2ssa::FunctionSemanticSummary>,
) -> Option<r2sym::SemanticArtifact> {
    let summary_seed = root_summary
        .cloned()
        .or_else(|| native_worker_summary_seed(function_addr, function_name));
    let summary_seed = summary_seed.as_ref();
    if should_probe_native_worker_summary_before_full_semantics(ssa_func, summary_seed) {
        let vm_route_evidence = r2sym::has_strong_vm_evidence(ssa_func);
        if !vm_route_evidence
            && should_skip_unbounded_semantic_artifact_after_worker_preprobe(ssa_func, summary_seed)
        {
            return None;
        }
        if !vm_route_evidence
            && let Some(artifact) = r2sym::compile_native_worker_summary_artifact(
                ssa_func,
                symbolic_scope,
                summary_seed,
                false,
            )
            && artifact
                .native_body()
                .is_some_and(r2sym::NativeArtifactBody::has_primary_summary_islands)
        {
            return Some(artifact);
        }
    }
    Some(compile_semantic_artifact_for_analysis(
        ssa_func,
        function_addr,
        function_name,
        symbolic_scope,
        arch,
        root_summary,
    ))
}

fn should_skip_unbounded_semantic_artifact_after_worker_preprobe(
    ssa_func: &SsaArtifact,
    root_summary: Option<&r2ssa::FunctionSemanticSummary>,
) -> bool {
    if root_summary.is_some_and(|summary| {
        let policy = r2sym::native_worker_summary_route_policy_for_summary(summary.id.0, summary);
        policy.should_use_direct_summary() || policy.should_prefer_full()
    }) {
        return false;
    }
    if r2sym::has_strong_vm_evidence(ssa_func) {
        return false;
    }
    let cfg = ssa_func.function().cfg_risk_summary();
    let branch_count = ssa_func.predicates().predicates.len();
    cfg.loop_count > 0 || cfg.back_edge_count > 0 || cfg.switch_block_count > 0 || branch_count >= 8
}

fn compile_semantic_artifact_for_analysis(
    ssa_func: &SsaArtifact,
    function_addr: u64,
    function_name: &str,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    arch: Option<&r2il::ArchSpec>,
    root_summary: Option<&r2ssa::FunctionSemanticSummary>,
) -> r2sym::SemanticArtifact {
    let summary_seed = root_summary
        .cloned()
        .or_else(|| native_worker_summary_seed(function_addr, function_name));
    let summary_seed = summary_seed.as_ref();
    let vm_route_evidence = r2sym::has_strong_vm_evidence(ssa_func);
    if !vm_route_evidence
        && let Some(summary) = summary_seed
        && let Some(artifact) = r2sym::compile_summary_dense_worker_artifact_from_interproc_summary(
            ssa_func,
            symbolic_scope,
            summary,
        )
    {
        return artifact;
    }
    if !vm_route_evidence
        && should_probe_native_worker_summary_before_full_semantics(ssa_func, summary_seed)
        && let Some(artifact) = r2sym::compile_native_worker_summary_artifact(
            ssa_func,
            symbolic_scope,
            summary_seed,
            false,
        )
        && artifact
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_primary_summary_islands)
    {
        return artifact;
    }
    let mut artifact = r2sym::compile_semantic_artifact_default_with_scope(
        &z3::Context::thread_local(),
        ssa_func,
        symbolic_scope,
        arch,
    );
    if let Some(summary) = summary_seed {
        r2sym::augment_semantic_artifact_with_interproc_summary(
            &mut artifact,
            ssa_func.entry,
            summary,
        );
    }
    artifact
}

fn should_probe_native_worker_summary_before_full_semantics(
    ssa_func: &SsaArtifact,
    root_summary: Option<&r2ssa::FunctionSemanticSummary>,
) -> bool {
    if root_summary.is_some_and(|summary| {
        let policy = r2sym::native_worker_summary_route_policy_for_summary(summary.id.0, summary);
        policy.should_use_direct_summary() || policy.should_prefer_full()
    }) {
        return true;
    }

    let cfg = ssa_func.function().cfg_risk_summary();
    if cfg.block_count == 0 || cfg.block_count > 64 {
        return false;
    }
    let branch_count = ssa_func.predicates().predicates.len();
    cfg.loop_count > 0 || cfg.back_edge_count > 0 || cfg.switch_block_count > 0 || branch_count >= 8
}

fn infer_signature_from_engine_analysis(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    arch: Option<&r2il::ArchSpec>,
    semantic_metadata_enabled: bool,
    reg_type_hints: &HashMap<String, r2types::TypeHint>,
    analysis: &EngineAnalysis,
) -> Option<r2types::InferredSignature> {
    let (_, _, cfg) = r2dec::DecompilerConfig::for_arch(arch);
    let pattern_ssa_blocks = analysis.pattern_ssa_func.local_ssa_blocks();
    let mut var_recovery = r2dec::VariableRecovery::new(&cfg.sp_name, &cfg.fp_name, cfg.ptr_size);
    var_recovery.recover(&analysis.ssa_func);
    let pointer_arg_slots = if semantic_metadata_enabled {
        let recovered_vars = r2types::recover_vars_from_ssa(
            &pattern_ssa_blocks,
            arch.map(|spec| spec.name.as_str()),
            reg_type_hints,
            true,
        );
        r2types::collect_pointer_arg_slots(&recovered_vars)
    } else {
        std::collections::BTreeSet::new()
    };
    let recovered_params = var_recovery
        .parameters()
        .into_iter()
        .map(|param| r2types::RecoveredSignatureParam {
            name: param.name.clone(),
            ssa_var: param.ssa_var.clone(),
            initial_ty: ctype_to_type_like(&param.ty),
        })
        .collect::<Vec<_>>();
    Some(r2types::infer_signature_from_prepared_ssa(
        function_name,
        arch_name,
        ptr_bits,
        &analysis.ssa_func,
        &pattern_ssa_blocks,
        &recovered_params,
        &pointer_arg_slots,
    ))
}

fn parsed_context_has_layout_hints(parsed_context: &r2types::ParsedExternalContext) -> bool {
    let external_type_db = &parsed_context.external_type_db;
    parsed_context
        .current_signature
        .as_ref()
        .into_iter()
        .chain(parsed_context.merged_signature.as_ref())
        .any(|signature| {
            signature
                .ret_type
                .as_ref()
                .is_some_and(|ty| type_like_has_layout_hint(ty, external_type_db))
                || signature
                    .params
                    .iter()
                    .filter_map(|param| param.ty.as_ref())
                    .any(|ty| type_like_has_layout_hint(ty, external_type_db))
        })
        || parsed_context
            .register_params
            .iter()
            .filter_map(|param| param.ty.as_ref())
            .any(|ty| type_like_has_layout_hint(ty, external_type_db))
        || parsed_context
            .stack_slots
            .values()
            .filter_map(|slot| slot.ty.as_ref())
            .any(|ty| type_like_has_layout_hint(ty, external_type_db))
}

fn optional_semantics_required_for_analysis(
    parsed_context: &r2types::ParsedExternalContext,
    ssa_func: &SsaArtifact,
    pattern_ssa_blocks: &[r2ssa::SSABlock],
    _has_local_field_accesses: bool,
) -> bool {
    if parsed_context_has_layout_hints(parsed_context) {
        return true;
    }
    let has_typed_stack_memory = parsed_context_has_typed_stack_memory_hints(parsed_context);
    if !has_typed_stack_memory {
        return false;
    }
    optional_semantic_proof_budget_allows(ssa_func, pattern_ssa_blocks)
}

fn should_skip_full_semantics_for_opaque_layout(
    parsed_context: &r2types::ParsedExternalContext,
    ssa_func: &SsaArtifact,
) -> bool {
    !r2sym::has_strong_vm_evidence(ssa_func)
        && parsed_context_has_opaque_aggregate_signature(parsed_context)
        && !parsed_context_has_layout_hints(parsed_context)
        && !parsed_context_has_typed_stack_memory_hints(parsed_context)
}

fn should_skip_full_semantics_for_layout_backed_prepared_proofs(
    parsed_context: &r2types::ParsedExternalContext,
    ssa_func: &SsaArtifact,
    pattern_ssa_blocks: &[r2ssa::SSABlock],
) -> bool {
    parsed_context_has_layout_hints(parsed_context)
        && !r2sym::has_strong_vm_evidence(ssa_func)
        && prepared_layout_route_has_no_semantic_side_effect_need(ssa_func, pattern_ssa_blocks)
}

fn prepared_layout_route_has_no_semantic_side_effect_need(
    ssa_func: &SsaArtifact,
    pattern_ssa_blocks: &[r2ssa::SSABlock],
) -> bool {
    let cfg = ssa_func.function().cfg_risk_summary();
    cfg.loop_count == 0
        && cfg.back_edge_count == 0
        && cfg.switch_block_count == 0
        && pattern_ssa_blocks.iter().all(|block| {
            block
                .ops
                .iter()
                .all(|op| !matches!(op, r2ssa::SSAOp::Call { .. } | r2ssa::SSAOp::CallInd { .. }))
        })
}

fn parsed_context_has_opaque_aggregate_signature(
    parsed_context: &r2types::ParsedExternalContext,
) -> bool {
    parsed_context
        .current_signature
        .as_ref()
        .into_iter()
        .chain(parsed_context.merged_signature.as_ref())
        .any(signature_has_opaque_aggregate)
}

fn signature_has_opaque_aggregate(signature: &r2types::FunctionSignatureSpec) -> bool {
    signature
        .ret_type
        .as_ref()
        .is_some_and(type_like_is_opaque_aggregate)
        || signature
            .params
            .iter()
            .filter_map(|param| param.ty.as_ref())
            .any(type_like_is_opaque_aggregate)
}

fn optional_semantic_proof_budget_allows(
    ssa_func: &SsaArtifact,
    pattern_ssa_blocks: &[r2ssa::SSABlock],
) -> bool {
    let cfg = ssa_func.function().cfg_risk_summary();
    let op_count = pattern_ssa_blocks
        .iter()
        .map(|block| block.ops.len())
        .sum::<usize>();
    let predicate_count = ssa_func.predicates().predicates.len();
    cfg.block_count <= 8
        && cfg.loop_count == 0
        && cfg.back_edge_count == 0
        && cfg.switch_block_count == 0
        && op_count <= 160
        && predicate_count <= 4
}

fn parsed_context_has_typed_stack_memory_hints(
    parsed_context: &r2types::ParsedExternalContext,
) -> bool {
    parsed_context
        .stack_slots
        .values()
        .filter_map(|slot| slot.ty.as_ref())
        .any(type_like_is_memory_hint)
}

fn type_like_has_layout_hint(
    ty: &r2types::CTypeLike,
    external_type_db: &r2types::ExternalTypeDb,
) -> bool {
    match ty {
        r2types::CTypeLike::Pointer(inner) | r2types::CTypeLike::Array(inner, _) => {
            type_like_has_layout_hint(inner, external_type_db)
        }
        r2types::CTypeLike::Struct(name) => external_struct_has_fields(external_type_db, name),
        r2types::CTypeLike::Union(name) => external_union_has_fields(external_type_db, name),
        r2types::CTypeLike::Enum(name) => external_enum_has_variants(external_type_db, name),
        r2types::CTypeLike::Typedef(name) => {
            let normalized = name.trim().to_ascii_lowercase();
            !is_scalar_typedef_name(&normalized)
                && (external_struct_has_fields(external_type_db, name)
                    || external_union_has_fields(external_type_db, name)
                    || external_enum_has_variants(external_type_db, name))
        }
        _ => false,
    }
}

fn type_like_is_memory_hint(ty: &r2types::CTypeLike) -> bool {
    match ty {
        r2types::CTypeLike::Pointer(inner) | r2types::CTypeLike::Array(inner, _) => {
            !matches!(
                inner.as_ref(),
                r2types::CTypeLike::Unknown | r2types::CTypeLike::Void
            ) || type_like_is_memory_hint(inner)
        }
        r2types::CTypeLike::Struct(_)
        | r2types::CTypeLike::Union(_)
        | r2types::CTypeLike::Typedef(_) => true,
        _ => false,
    }
}

fn type_like_is_opaque_aggregate(ty: &r2types::CTypeLike) -> bool {
    match ty {
        r2types::CTypeLike::Pointer(inner) | r2types::CTypeLike::Array(inner, _) => {
            type_like_is_opaque_aggregate(inner)
        }
        r2types::CTypeLike::Struct(_)
        | r2types::CTypeLike::Union(_)
        | r2types::CTypeLike::Enum(_) => true,
        r2types::CTypeLike::Typedef(name) => {
            !is_scalar_typedef_name(&name.trim().to_ascii_lowercase())
        }
        _ => false,
    }
}

fn is_scalar_typedef_name(normalized: &str) -> bool {
    matches!(
        normalized,
        "bool"
            | "char"
            | "signed char"
            | "unsigned char"
            | "short"
            | "unsigned short"
            | "int"
            | "unsigned int"
            | "long"
            | "unsigned long"
            | "long long"
            | "unsigned long long"
            | "int8_t"
            | "uint8_t"
            | "int16_t"
            | "uint16_t"
            | "int32_t"
            | "uint32_t"
            | "int64_t"
            | "uint64_t"
            | "size_t"
            | "ssize_t"
            | "void"
    )
}

fn external_layout_keys(name: &str) -> Vec<String> {
    let normalized = r2types::normalize_external_type_name(name);
    let mut keys = Vec::new();
    for candidate in [name.trim(), normalized.as_str()] {
        let lower = candidate.to_ascii_lowercase();
        if lower.is_empty() {
            continue;
        }
        keys.push(lower.clone());
        for prefix in ["struct ", "union ", "enum "] {
            if let Some(stripped) = lower.strip_prefix(prefix) {
                keys.push(stripped.trim().to_string());
            }
        }
    }
    keys.sort();
    keys.dedup();
    keys
}

fn external_struct_has_fields(external_type_db: &r2types::ExternalTypeDb, name: &str) -> bool {
    external_layout_keys(name).into_iter().any(|key| {
        external_type_db
            .structs
            .get(&key)
            .is_some_and(|st| !st.fields.is_empty())
    })
}

fn external_union_has_fields(external_type_db: &r2types::ExternalTypeDb, name: &str) -> bool {
    external_layout_keys(name).into_iter().any(|key| {
        external_type_db
            .unions
            .get(&key)
            .is_some_and(|un| !un.fields.is_empty())
    })
}

fn external_enum_has_variants(external_type_db: &r2types::ExternalTypeDb, name: &str) -> bool {
    external_layout_keys(name).into_iter().any(|key| {
        external_type_db
            .enums
            .get(&key)
            .is_some_and(|en| !en.variants.is_empty())
    })
}

fn ctype_to_type_like(ty: &r2dec::CType) -> r2types::CTypeLike {
    match ty {
        r2dec::CType::Void => r2types::CTypeLike::Void,
        r2dec::CType::Bool => r2types::CTypeLike::Bool,
        r2dec::CType::Int(bits) => r2types::CTypeLike::Int {
            bits: *bits,
            signedness: r2types::Signedness::Signed,
        },
        r2dec::CType::UInt(bits) => r2types::CTypeLike::Int {
            bits: *bits,
            signedness: r2types::Signedness::Unsigned,
        },
        r2dec::CType::Float(bits) => r2types::CTypeLike::Float(*bits),
        r2dec::CType::Pointer(inner) => {
            r2types::CTypeLike::Pointer(Box::new(ctype_to_type_like(inner)))
        }
        r2dec::CType::Array(inner, len) => {
            r2types::CTypeLike::Array(Box::new(ctype_to_type_like(inner)), *len)
        }
        r2dec::CType::Struct(name) => r2types::CTypeLike::Struct(name.clone()),
        r2dec::CType::Union(name) => r2types::CTypeLike::Union(name.clone()),
        r2dec::CType::Enum(name) => r2types::CTypeLike::Enum(name.clone()),
        r2dec::CType::Typedef(name) => r2types::CTypeLike::Typedef(name.clone()),
        r2dec::CType::Function { .. } | r2dec::CType::Unknown => r2types::CTypeLike::Unknown,
    }
}

fn interproc_scope_identity_hash(
    summaries: &BTreeMap<r2ssa::InterprocFunctionId, r2ssa::FunctionSemanticSummary>,
) -> u64 {
    stable_fnv1a_debug_hash(summaries)
}

pub fn summary_only_native_worker_fallback(
    function_name: &str,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> String {
    r2dec::semantic_fallback_comment(function_name, Some(semantic_artifact)).unwrap_or_else(|| {
        r2dec::artifact_guard_fallback_comment(
            function_name,
            "summary-only native worker without full decompile route",
        )
    })
}

pub fn type_facts_with_summary_projection(
    type_facts: FunctionTypeFacts,
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> FunctionTypeFacts {
    type_facts_with_summary_projection_for_candidates(
        type_facts,
        function_name,
        [function_name],
        arch_name,
        ptr_bits,
        semantic_artifact,
    )
}

pub fn type_facts_with_summary_projection_for_candidates<'a>(
    type_facts: FunctionTypeFacts,
    function_name: &str,
    name_candidates: impl IntoIterator<Item = &'a str>,
    arch_name: &str,
    ptr_bits: u32,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> FunctionTypeFacts {
    type_facts_with_summary_projection_for_candidates_with_options(
        type_facts,
        function_name,
        name_candidates,
        arch_name,
        ptr_bits,
        semantic_artifact,
        SummaryProjectionOptions::default(),
    )
}

#[derive(Clone, Copy, Default)]
struct SummaryProjectionOptions {
    preserve_authoritative_context_signature: bool,
}

fn type_facts_with_summary_projection_for_candidates_with_options<'a>(
    mut type_facts: FunctionTypeFacts,
    function_name: &str,
    _name_candidates: impl IntoIterator<Item = &'a str>,
    arch_name: &str,
    ptr_bits: u32,
    semantic_artifact: &r2sym::SemanticArtifact,
    options: SummaryProjectionOptions,
) -> FunctionTypeFacts {
    let signature_param_count = type_facts
        .render_authorized_signature()
        .map(|signature| signature.params.len())
        .unwrap_or_default();
    let current_param_count = signature_param_count.max(type_facts.register_params.len());
    let artifact_projection =
        r2types::signature_projection_for_semantic_artifact(semantic_artifact, current_param_count);
    let name_signature = artifact_projection
        .as_ref()
        .filter(|projection| {
            matches!(
                projection.source,
                r2types::SignatureProjectionSource::SummaryRole
            )
        })
        .map(|projection| projection.signature.clone());
    let fallback_plan = r2types::build_semantic_type_fallback_plan(
        function_name,
        arch_name,
        ptr_bits,
        semantic_artifact,
    );
    let fallback_signature =
        if fallback_plan.signature.confidence >= r2types::SIGNATURE_PROJECTION_WEAK_CONFIDENCE {
            r2types::inferred_signature_to_function_type_facts(&fallback_plan.signature, ptr_bits)
                .merged_signature
        } else {
            None
        };
    let projection = if let Some(mut projection) = artifact_projection {
        if projection.signature.ret_type.is_none()
            && let Some(fallback_signature) = fallback_signature.as_ref()
        {
            projection.signature.ret_type = fallback_signature.ret_type.clone();
        }
        Some(projection)
    } else {
        fallback_signature.map(FunctionSignatureProjection::weak_summary_kind)
    };
    let Some(projection) = projection else {
        r2types::augment_function_type_facts_with_summary_evidence(
            &mut type_facts,
            semantic_artifact,
            ptr_bits,
        );
        return type_facts;
    };
    if options.preserve_authoritative_context_signature
        && name_signature.is_none()
        && type_facts
            .render_authorized_signature()
            .is_some_and(signature_is_authoritative_context_seed)
    {
        r2types::augment_function_type_facts_with_summary_evidence(
            &mut type_facts,
            semantic_artifact,
            ptr_bits,
        );
        return type_facts;
    }
    let name_owned_exact_arity = name_signature.is_some()
        && projection.signature.ret_type.is_some()
        && projection
            .signature
            .params
            .iter()
            .all(|param| !param.name.is_empty() && param.ty.is_some());
    let projected_param_count = projection.signature.params.len();
    let projection_source = SignatureCertificateSource::from(projection.source);
    let projection_result =
        type_facts.apply_signature_projection(function_name, projection.clone(), ptr_bits);
    if projection_result.was_applied()
        && projection.has_strong_signature_confidence()
        && !matches!(
            projection.source,
            r2types::SignatureProjectionSource::SummaryKind
        )
    {
        type_facts.certify_current_signature_with_source(projection_source);
    }
    if name_owned_exact_arity && type_facts.register_params.len() > projected_param_count {
        type_facts.register_params.truncate(projected_param_count);
    }
    r2types::augment_function_type_facts_with_summary_evidence(
        &mut type_facts,
        semantic_artifact,
        ptr_bits,
    );
    type_facts
}

fn parsed_context_current_signature_is_authoritative(
    parsed_context: &r2types::ParsedExternalContext,
) -> bool {
    parsed_context
        .current_signature
        .as_ref()
        .is_some_and(signature_is_authoritative_context_seed)
}

fn signature_is_authoritative_context_seed(signature: &r2types::FunctionSignatureSpec) -> bool {
    r2types::signature_param_count_is_authoritative(signature)
        && signature.params.iter().any(|param| {
            !r2types::is_generic_arg_name(&param.name)
                && !r2types::is_generic_signature_type(param.ty.as_ref())
        })
        && signature
            .params
            .iter()
            .all(|param| !r2types::is_generic_signature_type(param.ty.as_ref()))
}

#[derive(Debug, Clone)]
pub struct NativeWorkerTypeProjection {
    pub function_facts: FunctionFacts,
    pub semantic_artifact: r2sym::SemanticArtifact,
    pub name_owned_signature: bool,
    pub context_owned_signature: bool,
}

pub fn native_worker_summary_seed(
    function_addr: u64,
    function_name: &str,
) -> Option<r2ssa::FunctionSemanticSummary> {
    r2sym::function_semantic_summary_seed_for_name(
        r2ssa::InterprocFunctionId(function_addr),
        function_name,
    )
}

pub fn native_worker_summary_artifact(
    blocks: &[R2ILBlock],
    function_name: &str,
    arch: Option<&r2il::ArchSpec>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    skipped_large_cfg: bool,
) -> Option<r2sym::SemanticArtifact> {
    let ssa_func = r2ssa::SsaArtifact::for_symbolic(blocks, arch)?.with_name(function_name);
    if r2sym::has_strong_vm_evidence(&ssa_func) {
        return None;
    }
    let summary_id =
        r2ssa::InterprocFunctionId(blocks.first().map(|block| block.addr).unwrap_or_default());
    let root_summary = native_worker_summary_seed(summary_id.0, function_name);
    if let Some(artifact) = r2sym::compile_native_worker_summary_artifact(
        &ssa_func,
        symbolic_scope,
        root_summary.as_ref(),
        skipped_large_cfg,
    ) {
        return Some(artifact);
    }
    root_summary.as_ref().and_then(|summary| {
        r2sym::compile_named_native_worker_summary_artifact(summary, skipped_large_cfg)
    })
}

fn fast_program_orchestrator_summary_artifact(
    function_addr: u64,
    function_name: &str,
    skipped_large_cfg: bool,
) -> Option<r2sym::SemanticArtifact> {
    if !r2sym::has_program_orchestrator_summary_family(function_name) {
        return None;
    }
    let summary = native_worker_summary_seed(function_addr, function_name)?;
    r2sym::compile_named_native_worker_summary_artifact(&summary, skipped_large_cfg)
}

pub fn type_facts_from_parsed_context(
    parsed_context: &r2types::ParsedExternalContext,
) -> FunctionTypeFacts {
    let merged_signature = parsed_context
        .merged_signature
        .clone()
        .or_else(|| parsed_context.current_signature.clone());
    let signature_certificate = merged_signature.as_ref().and_then(|signature| {
        r2types::SignatureCertificate::from_signature(
            signature,
            [r2types::SignatureCertificateSource::ExternalContext],
        )
    });
    FunctionTypeFacts::builder(FunctionTypeFactInputs {
        merged_signature,
        signature_certificate,
        known_function_signatures: parsed_context.known_function_signatures.clone(),
        register_params: parsed_context.register_params.clone(),
        stack_slots: parsed_context.stack_slots.clone(),
        external_stack_vars: parsed_context.external_stack_vars.clone(),
        external_type_db: parsed_context.external_type_db.clone(),
        diagnostics: parsed_context.diagnostics.clone(),
        ..FunctionTypeFactInputs::default()
    })
    .build()
}

pub fn native_worker_type_projection(
    function_addr: u64,
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    parsed_context: &r2types::ParsedExternalContext,
    skipped_large_cfg: bool,
) -> Option<NativeWorkerTypeProjection> {
    let identity = EngineFunctionIdentity::from_name(function_addr, function_name);
    native_worker_type_projection_for_identity(
        &identity,
        arch_name,
        ptr_bits,
        parsed_context,
        skipped_large_cfg,
    )
}

pub fn native_worker_type_projection_for_identity(
    identity: &EngineFunctionIdentity,
    arch_name: &str,
    ptr_bits: u32,
    parsed_context: &r2types::ParsedExternalContext,
    skipped_large_cfg: bool,
) -> Option<NativeWorkerTypeProjection> {
    let summary_name = identity.summary_probe_name();
    let summary = native_worker_summary_seed(identity.function_addr, &summary_name)?;
    let semantic_artifact =
        r2sym::compile_named_native_worker_summary_artifact(&summary, skipped_large_cfg)?;
    if !semantic_artifact
        .native_body()
        .is_some_and(|native| native.has_primary_non_name_summary_islands())
    {
        return None;
    }
    let type_facts = type_facts_from_parsed_context(parsed_context);
    let current_param_count = type_facts
        .render_authorized_signature()
        .map(|signature| signature.params.len())
        .unwrap_or_default();
    let name_owned_signature = r2types::signature_projection_for_semantic_artifact(
        &semantic_artifact,
        current_param_count,
    )
    .is_some_and(|projection| {
        matches!(
            projection.source,
            r2types::SignatureProjectionSource::SummaryRole
        )
    });
    let context_owned_signature =
        parsed_context_current_signature_is_authoritative(parsed_context) && !name_owned_signature;
    let type_facts = type_facts_with_summary_projection_for_candidates_with_options(
        type_facts,
        identity.primary_name(),
        identity.name_candidates(),
        arch_name,
        ptr_bits,
        &semantic_artifact,
        SummaryProjectionOptions {
            preserve_authoritative_context_signature: context_owned_signature,
        },
    );
    let function_facts = FunctionFacts::new(type_facts, Some(semantic_artifact.clone()))
        .with_assumptions(parsed_context.assumptions.clone());
    Some(NativeWorkerTypeProjection {
        function_facts,
        semantic_artifact,
        name_owned_signature,
        context_owned_signature,
    })
}

pub fn type_summary_preprobe(
    request: EngineTypePreprobeRequest<'_>,
) -> Option<EngineTypePreprobeResponse> {
    let identity = EngineFunctionIdentity::new(
        request.function_addr,
        request.canonical_name,
        request.display_name,
    );
    let probe = decompile_probe_decision_for_identity(request.blocks, &identity);
    if !probe.summary_probe_needed {
        return None;
    }

    let cfg_summary = raw_cfg_risk_summary_for_preprobe(request.blocks);
    let semantic_artifact = fast_program_orchestrator_summary_artifact(
        request.function_addr,
        &probe.summary_probe_name,
        probe.summary_probe_skipped_large_cfg,
    )
    .or_else(|| {
        native_worker_summary_artifact(
            request.blocks,
            &probe.summary_probe_name,
            request.arch,
            request.symbolic_scope,
            probe.summary_probe_skipped_large_cfg,
        )
    });
    let type_seed = request
        .type_seed
        .unwrap_or_else(|| type_facts_from_parsed_context(request.parsed_context));
    let (arch_name, _, _) = r2dec::DecompilerConfig::for_arch(request.arch);
    let function_facts = if let Some(semantic_artifact) = semantic_artifact {
        let type_facts = type_facts_with_summary_projection_for_candidates_with_options(
            type_seed,
            request.display_name,
            identity.name_candidates(),
            &arch_name,
            request.ptr_bits,
            &semantic_artifact,
            SummaryProjectionOptions {
                preserve_authoritative_context_signature:
                    parsed_context_current_signature_is_authoritative(request.parsed_context),
            },
        );
        r2types::FunctionFacts::new(type_facts, Some(semantic_artifact))
            .with_assumptions(request.parsed_context.assumptions.clone())
    } else if request.fallback_if_guarded_without_summary && probe.block_guarded {
        r2types::FunctionFacts::new(type_seed, None)
            .with_assumptions(request.parsed_context.assumptions.clone())
    } else {
        return None;
    };

    let route_decision = if let Some(artifact) = function_facts.semantic_artifact()
        && summary_preprobe_type_payload_prefers_semantic_fallback(artifact)
    {
        EngineTypeRouteDecision {
            request: EngineRequestKind::Types,
            plan: EnginePlan::SemanticSummary,
            kind: EngineTypeRouteKind::SemanticFallback,
            prefer_bounded_type_plan: true,
            reason: Some("summary preprobe type projection".to_string()),
            apply_artifact_signature_hint: false,
        }
    } else {
        let decision = type_route_decision(
            &function_facts,
            &cfg_summary,
            request.caller_prefers_bounded_type_plan,
        );
        if !matches!(decision.kind, EngineTypeRouteKind::FullWriteback) {
            decision
        } else if request.fallback_if_guarded_without_summary
            && function_facts.semantic_artifact().is_none()
            && probe.block_guarded
        {
            let reason = if probe.summary_probe_skipped_large_cfg {
                type_cfg_bounded_reason(&cfg_summary)
            } else {
                "bounded native-worker preprobe without canonical summary".to_string()
            };
            EngineTypeRouteDecision {
                request: EngineRequestKind::Types,
                plan: EnginePlan::BoundedType,
                kind: EngineTypeRouteKind::BoundedCfg,
                prefer_bounded_type_plan: true,
                reason: Some(reason),
                apply_artifact_signature_hint: false,
            }
        } else {
            return None;
        }
    };

    Some(EngineTypePreprobeResponse {
        cfg_summary,
        function_facts,
        route_decision,
    })
}

fn summary_preprobe_type_payload_prefers_semantic_fallback(
    artifact: &r2sym::SemanticArtifact,
) -> bool {
    matches!(artifact.stage, r2sym::RefinementStage::Compiled)
        && matches!(
            artifact.granularity,
            r2sym::ArtifactGranularity::SummaryOnly
        )
        && artifact
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_primary_non_name_summary_islands)
        && matches!(
            artifact.slice_class(),
            Some(r2sym::SliceClass::Worker | r2sym::SliceClass::GenericLarge)
        )
}

pub fn render_semantic_route(
    function_name: &str,
    function_facts: &FunctionFacts,
    route: &r2dec::SemanticRoutePlan,
    config: r2dec::DecompilerConfig,
) -> Option<String> {
    match route {
        r2dec::SemanticRoutePlan::LinearWorker { .. }
        | r2dec::SemanticRoutePlan::SummaryIslands { .. }
        | r2dec::SemanticRoutePlan::StructuredWorker { .. } => {
            r2dec::render_semantic_worker_summary(function_name, function_facts, route, config)
        }
        r2dec::SemanticRoutePlan::VmSummary { .. } => {
            r2dec::render_vm_semantic_summary(function_name, function_facts)
        }
        r2dec::SemanticRoutePlan::FallbackComment { comment } => Some(comment.clone()),
        r2dec::SemanticRoutePlan::Standard => None,
    }
}

pub fn target_query_route_decision(
    request: EngineTargetQueryRouteRequest<'_, '_>,
) -> r2sym::TargetQueryRoutePlan {
    let probe_config = r2sym::SymQueryConfig {
        explore: request.explore_config,
        mode: r2sym::QueryMode::TargetGuided,
        summary_profile: request.summary_profile,
        solve_tactics: r2sym::SolveTacticConfig::default(),
    };
    let mut explorer = probe_config.make_explorer(request.z3_ctx);
    if let Some(scope) = request.scope {
        r2sym::install_runtime_hooks_for_scope(
            &mut explorer,
            scope,
            request.arch,
            request.symbol_map,
        );
    }
    r2sym::selected_target_query_route_in_scope(
        &mut explorer,
        request.prepared,
        request.scope,
        Some(request.compiled),
        request.target_addr,
        request.assumption_conflicted,
    )
}

pub fn signature_override_from_type_facts(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    callconv: Option<&str>,
    type_facts: &r2types::FunctionTypeFacts,
) -> Option<r2types::InferredSignature> {
    type_facts
        .writeback_authorized_signature()
        .map(|signature| {
            r2types::inferred_signature_from_signature_spec(
                function_name,
                arch_name,
                ptr_bits,
                callconv,
                signature,
            )
        })
}

pub fn bounded_cfg_type_writeback_plan(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    callconv: Option<&str>,
    function_facts: &FunctionFacts,
    reason: String,
) -> TypeWritebackPlan {
    let signature = signature_override_from_type_facts(
        function_name,
        arch_name,
        ptr_bits,
        callconv,
        &function_facts.types,
    )
    .unwrap_or_else(|| r2types::InferredSignature {
        function_name: function_name.to_string(),
        signature: format!("void {}(void)", function_name),
        ret_type: "void".to_string(),
        params: Vec::new(),
        callconv: "unknown".to_string(),
        arch: arch_name.to_string(),
        confidence: 0,
        callconv_confidence: 0,
    });
    TypeWritebackPlan {
        signature,
        var_type_candidates: Vec::new(),
        var_rename_candidates: Vec::new(),
        struct_decls: Vec::new(),
        global_type_links: Vec::new(),
        diagnostics: r2types::TypeWritebackDiagnostics {
            warnings: vec![reason],
            ..r2types::TypeWritebackDiagnostics::default()
        },
    }
}

pub fn semantic_fallback_type_writeback_plan(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    callconv: Option<&str>,
    artifact: &r2sym::SemanticArtifact,
    function_facts: &FunctionFacts,
    apply_artifact_signature_hint: bool,
) -> TypeWritebackPlan {
    let mut plan =
        r2types::build_semantic_type_fallback_plan(function_name, arch_name, ptr_bits, artifact);
    let mut signature_override = signature_override_from_type_facts(
        function_name,
        arch_name,
        ptr_bits,
        callconv,
        &function_facts.types,
    );
    if apply_artifact_signature_hint && let Some(signature) = signature_override.as_mut() {
        r2types::apply_semantic_artifact_signature_hint_to_inferred(signature, artifact, ptr_bits);
    }
    if let Some(signature) = signature_override {
        plan.signature = signature;
    }
    plan
}

struct TypeWritebackPlanRouteInput<'a> {
    function_name: &'a str,
    arch_name: &'a str,
    ptr_bits: u32,
    callconv: Option<&'a str>,
    function_facts: &'a FunctionFacts,
    cfg_summary: &'a CFGRiskSummary,
    route: &'a EngineTypeRouteDecision,
    full_writeback_plan: Option<TypeWritebackPlan>,
}

fn type_writeback_plan_for_route(
    input: TypeWritebackPlanRouteInput<'_>,
) -> Option<TypeWritebackPlan> {
    match input.route.kind {
        EngineTypeRouteKind::FullWriteback => input.full_writeback_plan,
        EngineTypeRouteKind::BoundedCfg => Some(bounded_cfg_type_writeback_plan(
            input.function_name,
            input.arch_name,
            input.ptr_bits,
            input.callconv,
            input.function_facts,
            input
                .route
                .reason
                .clone()
                .unwrap_or_else(|| type_cfg_bounded_reason(input.cfg_summary)),
        )),
        EngineTypeRouteKind::SemanticFallback => {
            let artifact = input.function_facts.semantic_artifact()?;
            Some(semantic_fallback_type_writeback_plan(
                input.function_name,
                input.arch_name,
                input.ptr_bits,
                input.callconv,
                artifact,
                input.function_facts,
                input.route.apply_artifact_signature_hint,
            ))
        }
    }
}

fn current_interproc_summary(
    function_facts: &FunctionFacts,
) -> Option<r2ssa::FunctionSemanticSummary> {
    function_facts
        .interproc_summary_set()
        .and_then(|summary_set| {
            summary_set
                .root
                .and_then(|root| summary_set.summaries.get(&root).cloned())
        })
}

fn count_prepared_callsites(ssa_blocks: &[r2ssa::SSABlock]) -> usize {
    ssa_blocks
        .iter()
        .flat_map(|block| block.ops.iter())
        .filter(|op| matches!(op, r2ssa::SSAOp::Call { .. } | r2ssa::SSAOp::CallInd { .. }))
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    fn const_return_blocks(addr: u64, value: u64) -> Vec<R2ILBlock> {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(value, 8),
        });
        vec![block]
    }

    const VM_TEST_RAX: u64 = 0;
    const VM_TEST_RBP: u64 = 8;

    fn vm_test_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("RAX", VM_TEST_RAX, 8));
        arch.add_register(r2il::RegisterDef::new("RBP", VM_TEST_RBP, 8));
        arch
    }

    fn vm_reg(offset: u64, size: u32) -> r2il::Varnode {
        r2il::Varnode::register(offset, size)
    }

    fn vm_const(value: u64, size: u32) -> r2il::Varnode {
        r2il::Varnode::constant(value, size)
    }

    fn symbolic_register_branch_blocks(addr: u64) -> Vec<R2ILBlock> {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(r2il::R2ILOp::IntEqual {
            dst: vm_reg(0x80, 1),
            a: vm_reg(0x38, 8),
            b: vm_const(1, 8),
        });
        block.push(r2il::R2ILOp::CBranch {
            target: vm_const(addr + 0x10, 8),
            cond: vm_reg(0x80, 1),
        });

        let mut fallthrough = R2ILBlock::new(addr + 4, 1);
        fallthrough.push(r2il::R2ILOp::Return {
            target: vm_const(0, 8),
        });

        let mut target = R2ILBlock::new(addr + 0x10, 1);
        target.push(r2il::R2ILOp::Return {
            target: vm_const(1, 8),
        });

        vec![block, fallthrough, target]
    }

    fn symbolic_register_assumption(prepared: &r2ssa::SsaArtifact) -> r2ssa::AnalysisAssumption {
        let reg_name = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.version == 0 && value.var.is_register() && value.var.size == 8)
            .expect("version-zero input register")
            .var
            .name
            .clone();
        r2ssa::AnalysisAssumption {
            id: Some("force-input-register".to_string()),
            subject: r2ssa::AssumptionSubject::Register { name: reg_name },
            value: r2ssa::AssumptionValue::Constant { value: 1 },
            scope: r2ssa::AssumptionScope::Query,
            provenance: r2ssa::AssumptionProvenance::User,
        }
    }

    fn conflicting_predicate_assumption(
        prepared: &r2ssa::SsaArtifact,
    ) -> r2ssa::AnalysisAssumption {
        let (predicate, fact) = prepared
            .facts()
            .predicates
            .predicates
            .iter()
            .next()
            .expect("predicate fact");
        r2ssa::AnalysisAssumption {
            id: Some("conflicting-branch".to_string()),
            subject: r2ssa::AssumptionSubject::Predicate {
                predicate: *predicate,
                block_addr: fact.block_addr + 0x1000,
                predecessor: None,
            },
            value: r2ssa::AssumptionValue::Branch { truth: true },
            scope: r2ssa::AssumptionScope::Query,
            provenance: r2ssa::AssumptionProvenance::User,
        }
    }

    fn cache_register_assumption(id: &str, name: &str, value: u64) -> r2ssa::AnalysisAssumption {
        r2ssa::AnalysisAssumption {
            id: Some(id.to_string()),
            subject: r2ssa::AssumptionSubject::Register {
                name: name.to_string(),
            },
            value: r2ssa::AssumptionValue::Constant { value },
            scope: r2ssa::AssumptionScope::Query,
            provenance: r2ssa::AssumptionProvenance::User,
        }
    }

    #[test]
    fn opaque_typedef_signature_is_not_a_concrete_layout_hint() {
        let mut parsed = r2types::ParsedExternalContext {
            current_signature: Some(r2types::FunctionSignatureSpec {
                ret_type: Some(r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                }),
                params: vec![r2types::FunctionParamSpec {
                    name: "items".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Typedef("Item".to_string()),
                    ))),
                }],
            }),
            ..r2types::ParsedExternalContext::default()
        };

        assert!(!parsed_context_has_layout_hints(&parsed));
        let ssa = r2ssa::SsaArtifact::for_decompile(&const_return_blocks(0x401000, 0), None)
            .expect("ssa");
        assert!(should_skip_full_semantics_for_opaque_layout(&parsed, &ssa));

        parsed.external_type_db.structs.insert(
            "item".to_string(),
            r2types::ExternalStruct {
                name: "Item".to_string(),
                fields: BTreeMap::from([(
                    0,
                    r2types::ExternalField {
                        name: "id".to_string(),
                        offset: 0,
                        ty: Some("int32_t".to_string()),
                    },
                )]),
            },
        );

        assert!(parsed_context_has_layout_hints(&parsed));
        assert!(!should_skip_full_semantics_for_opaque_layout(&parsed, &ssa));
    }

    #[test]
    fn concrete_layout_acyclic_call_free_route_skips_full_semantics() {
        let parsed = concrete_item_context();
        let ssa = r2ssa::SsaArtifact::for_decompile(&const_return_blocks(0x401000, 0), None)
            .expect("ssa");
        let pattern_blocks = ssa.local_ssa_blocks();

        assert!(parsed_context_has_layout_hints(&parsed));
        assert!(
            should_skip_full_semantics_for_layout_backed_prepared_proofs(
                &parsed,
                &ssa,
                &pattern_blocks,
            )
        );
    }

    #[test]
    fn concrete_layout_loop_route_keeps_semantic_owner_available() {
        let parsed = concrete_item_context();
        let mut entry = R2ILBlock::new(0x401000, 4);
        entry.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x401000, 8),
            cond: r2il::Varnode::constant(1, 1),
        });
        let ssa = r2ssa::SsaArtifact::for_decompile(&[entry], None).expect("ssa");
        let pattern_blocks = ssa.local_ssa_blocks();

        assert!(
            !should_skip_full_semantics_for_layout_backed_prepared_proofs(
                &parsed,
                &ssa,
                &pattern_blocks,
            )
        );
    }

    #[test]
    fn optional_semantics_needs_bounded_local_memory_evidence() {
        let mut parsed = r2types::ParsedExternalContext {
            current_signature: Some(r2types::FunctionSignatureSpec {
                ret_type: Some(r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                }),
                params: vec![r2types::FunctionParamSpec {
                    name: "items".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Typedef("Item".to_string()),
                    ))),
                }],
            }),
            ..r2types::ParsedExternalContext::default()
        };
        let ssa = r2ssa::SsaArtifact::for_decompile(&const_return_blocks(0x401000, 0), None)
            .expect("ssa");
        let pattern_blocks = ssa.local_ssa_blocks();

        assert!(!optional_semantics_required_for_analysis(
            &parsed,
            &ssa,
            &pattern_blocks,
            true,
        ));

        parsed.stack_slots.insert(
            r2types::StackSlotKey {
                base: r2types::ExternalStackBase::FramePointer,
                offset: -8,
            },
            r2types::ExternalStackSlotSpec {
                name: "loc".to_string(),
                ty: Some(r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Signed,
                    },
                ))),
                base: r2types::ExternalStackBase::FramePointer,
                role: r2types::ExternalStackSlotRole::Local,
                ..r2types::ExternalStackSlotSpec::default()
            },
        );

        assert!(optional_semantics_required_for_analysis(
            &parsed,
            &ssa,
            &pattern_blocks,
            false,
        ));
    }

    fn concrete_item_context() -> r2types::ParsedExternalContext {
        let mut parsed = r2types::ParsedExternalContext {
            current_signature: Some(r2types::FunctionSignatureSpec {
                ret_type: Some(r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                }),
                params: vec![r2types::FunctionParamSpec {
                    name: "items".to_string(),
                    ty: Some(r2types::CTypeLike::Pointer(Box::new(
                        r2types::CTypeLike::Typedef("Item".to_string()),
                    ))),
                }],
            }),
            ..r2types::ParsedExternalContext::default()
        };
        parsed.external_type_db.structs.insert(
            "item".to_string(),
            r2types::ExternalStruct {
                name: "Item".to_string(),
                fields: BTreeMap::from([(
                    0,
                    r2types::ExternalField {
                        name: "id".to_string(),
                        offset: 0,
                        ty: Some("int32_t".to_string()),
                    },
                )]),
            },
        );
        parsed
    }

    fn vm_selector_dispatch_ops() -> Vec<r2il::R2ILOp> {
        vec![
            r2il::R2ILOp::Load {
                dst: vm_reg(VM_TEST_RAX, 8),
                space: r2il::SpaceId::Ram,
                addr: vm_reg(VM_TEST_RBP, 8),
            },
            r2il::R2ILOp::IntMult {
                dst: vm_reg(VM_TEST_RAX, 8),
                a: vm_reg(VM_TEST_RAX, 8),
                b: vm_const(8, 8),
            },
            r2il::R2ILOp::BranchInd {
                target: vm_reg(VM_TEST_RAX, 8),
            },
        ]
    }

    fn switch_loop_vm_blocks() -> Vec<R2ILBlock> {
        let mut entry = R2ILBlock::new(0x9300, 4);
        entry.push(r2il::R2ILOp::Branch {
            target: vm_const(0x9304, 8),
        });

        let mut dispatch = R2ILBlock::new(0x9304, 4);
        for op in vm_selector_dispatch_ops() {
            dispatch.push(op);
        }
        dispatch.switch_info = Some(r2il::SwitchInfo {
            switch_addr: 0x9304,
            min_val: 0,
            max_val: 4,
            default_target: Some(0x9318),
            cases: vec![
                r2il::SwitchCase {
                    value: 0,
                    target: 0x9308,
                },
                r2il::SwitchCase {
                    value: 1,
                    target: 0x930c,
                },
                r2il::SwitchCase {
                    value: 2,
                    target: 0x9310,
                },
                r2il::SwitchCase {
                    value: 3,
                    target: 0x9314,
                },
            ],
        });

        let mut add = R2ILBlock::new(0x9308, 4);
        add.push(r2il::R2ILOp::IntAdd {
            dst: vm_reg(VM_TEST_RAX, 8),
            a: vm_reg(VM_TEST_RAX, 8),
            b: vm_const(1, 8),
        });
        add.push(r2il::R2ILOp::Branch {
            target: vm_const(0x9304, 8),
        });

        let mut sub = R2ILBlock::new(0x930c, 4);
        sub.push(r2il::R2ILOp::IntSub {
            dst: vm_reg(VM_TEST_RAX, 8),
            a: vm_reg(VM_TEST_RAX, 8),
            b: vm_const(1, 8),
        });
        sub.push(r2il::R2ILOp::Branch {
            target: vm_const(0x9304, 8),
        });

        let mut xor = R2ILBlock::new(0x9310, 4);
        xor.push(r2il::R2ILOp::IntXor {
            dst: vm_reg(VM_TEST_RAX, 8),
            a: vm_reg(VM_TEST_RAX, 8),
            b: vm_const(0x55, 8),
        });
        xor.push(r2il::R2ILOp::Branch {
            target: vm_const(0x9304, 8),
        });

        let mut shl = R2ILBlock::new(0x9314, 4);
        shl.push(r2il::R2ILOp::IntLeft {
            dst: vm_reg(VM_TEST_RAX, 8),
            a: vm_reg(VM_TEST_RAX, 8),
            b: vm_const(1, 8),
        });
        shl.push(r2il::R2ILOp::Branch {
            target: vm_const(0x9304, 8),
        });

        let mut default = R2ILBlock::new(0x9318, 4);
        default.push(r2il::R2ILOp::Branch {
            target: vm_const(0x9304, 8),
        });

        vec![entry, dispatch, add, sub, xor, shl, default]
    }

    #[test]
    fn raw_cfg_preprobe_summary_counts_back_edges_without_ssa() {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x1000, 8),
            cond: r2il::Varnode::constant(1, 1),
        });
        let mut switch = R2ILBlock::new(0x1004, 4);
        switch.switch_info = Some(r2il::SwitchInfo {
            switch_addr: 0x1004,
            min_val: 0,
            max_val: 1,
            default_target: Some(0x1008),
            cases: vec![r2il::SwitchCase {
                value: 0,
                target: 0x1000,
            }],
        });

        let summary = raw_cfg_risk_summary_for_preprobe(&[entry, switch]);

        assert_eq!(summary.block_count, 2);
        assert_eq!(summary.loop_count, 1);
        assert_eq!(summary.back_edge_count, 2);
        assert_eq!(summary.switch_block_count, 1);
        assert_eq!(summary.max_switch_cases, 2);
    }

    fn native_linear_artifact(slice_class: r2sym::SliceClass) -> r2sym::SemanticArtifact {
        let region = r2sym::SemanticRegion {
            anchor: 0x401000,
            frontier: BTreeSet::from([0x401010]),
            control: Vec::new(),
            memory: Vec::new(),
            pre: Vec::new(),
            post: Vec::new(),
            targets: Vec::new(),
        };
        let regions = BTreeMap::from([(region.key(), region)]);
        let mut worker_summaries = Vec::new();
        for idx in 0..8 {
            worker_summaries.push(r2sym::NativeWorkerSummary {
                anchor: 0x401100 + idx,
                kind: if idx % 2 == 0 {
                    r2sym::NativeWorkerSummaryKind::MemoryRead
                } else {
                    r2sym::NativeWorkerSummaryKind::MemoryWrite
                },
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
        }
        r2sym::SemanticArtifact {
            stage: r2sym::RefinementStage::Compiled,
            granularity: r2sym::ArtifactGranularity::Regioned,
            execution: r2sym::ExecutionModel::Native,
            body: r2sym::SemanticArtifactBody::Native(r2sym::NativeArtifactBody {
                summary: r2sym::NativeFunctionSummary {
                    slice_class,
                    role_identity: None,
                    closure_functions: 1,
                    helper_functions: 0,
                    derived_summaries: 0,
                    derived_diagnostics: Default::default(),
                    region_summaries: Vec::new(),
                    worker_summaries,
                },
                regions,
            }),
            diagnostics: r2sym::SemanticArtifactDiagnostics {
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
    }

    fn native_linear_predicated_count_artifact() -> r2sym::SemanticArtifact {
        let mut artifact = native_linear_artifact(r2sym::SliceClass::Worker);
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            unreachable!("native artifact helper must build native body");
        };
        native.summary.worker_summaries = vec![r2sym::NativeWorkerSummary {
            anchor: 0x401100,
            kind: r2sym::NativeWorkerSummaryKind::NumericTransform,
            dst: None,
            src: None,
            memory: Some(r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                range: None,
            }),
            len: Some(r2ssa::SummaryTransferLength::Arg(1)),
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                header: 0x401100,
                exit_target: Some(0x401140),
                iterations: None,
                length_arg: Some(1),
                stride: Some(1),
                terminator: Some(r2sym::NativeWorkerTerminator::LengthBound),
                table_walk: None,
                fold: Some(r2sym::NativeWorkerFold {
                    accumulator: "count".to_string(),
                    bits: 64,
                    operation: r2sym::NativeWorkerFoldOperation::Add,
                    predicate: Some(r2sym::NativeWorkerPredicate::ByteEqArg { arg: 2 }),
                    init: None,
                    multiplier: None,
                    byte_transform: None,
                }),
            }),
            evidence: r2sym::SemanticEvidence::likely(
                r2sym::SemanticEvidenceReason::DerivedFromRanking,
            ),
        }];
        artifact
    }

    fn native_linear_table_walk_artifact() -> r2sym::SemanticArtifact {
        let mut artifact = native_linear_artifact(r2sym::SliceClass::Worker);
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            unreachable!("native artifact helper must build native body");
        };
        native.summary.worker_summaries = vec![r2sym::NativeWorkerSummary {
            anchor: 0x401100,
            kind: r2sym::NativeWorkerSummaryKind::TableWalk,
            dst: None,
            src: None,
            memory: Some(r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                range: Some(r2ssa::SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 0,
                    width: Some(8),
                }),
            }),
            len: None,
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                header: 0x401100,
                exit_target: Some(0x401140),
                iterations: None,
                length_arg: None,
                stride: Some(1),
                terminator: Some(r2sym::NativeWorkerTerminator::ZeroByte),
                fold: None,
                table_walk: None,
            }),
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
        }];
        artifact
    }

    fn summary_only_table_walk_artifact() -> r2sym::SemanticArtifact {
        let mut artifact = native_linear_table_walk_artifact();
        artifact.granularity = r2sym::ArtifactGranularity::SummaryOnly;
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            unreachable!("native artifact helper must build native body");
        };
        native.regions.clear();
        artifact
    }

    fn summary_only_complete_table_walk_artifact() -> r2sym::SemanticArtifact {
        let mut artifact = summary_only_table_walk_artifact();
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            unreachable!("native artifact helper must build native body");
        };
        let loop_summary = native.summary.worker_summaries[0]
            .loop_summary
            .as_mut()
            .expect("table walk loop summary");
        loop_summary.table_walk = Some(r2sym::NativeTableWalkSummary {
            table_arg: 0,
            needle_arg: Some(1),
            id_offset: Some(0),
            len_offset: Some(6),
            name_offset: Some(24),
            next_offset: Some(32),
            count_accumulator: Some("seen".to_string()),
            match_returns_field_plus_count: true,
            exhausted_returns_negative_count: true,
        });
        artifact
    }

    fn summary_only_exact_hash_fold_artifact() -> r2sym::SemanticArtifact {
        let mut artifact = native_linear_artifact(r2sym::SliceClass::Worker);
        artifact.granularity = r2sym::ArtifactGranularity::SummaryOnly;
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            unreachable!("native artifact helper must build native body");
        };
        native.regions.clear();
        native.summary.worker_summaries = vec![r2sym::NativeWorkerSummary {
            anchor: 0x401100,
            kind: r2sym::NativeWorkerSummaryKind::HashFold,
            dst: None,
            src: None,
            memory: Some(r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                range: Some(r2ssa::SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 0,
                    width: Some(1),
                }),
            }),
            len: Some(r2ssa::SummaryTransferLength::Arg(1)),
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                header: 0x401100,
                exit_target: Some(0x401140),
                iterations: None,
                length_arg: Some(1),
                stride: Some(1),
                terminator: Some(r2sym::NativeWorkerTerminator::LengthBound),
                fold: Some(r2sym::NativeWorkerFold {
                    accumulator: "hash".to_string(),
                    bits: 64,
                    operation: r2sym::NativeWorkerFoldOperation::Xor,
                    predicate: None,
                    init: Some(0x14650fb0739d0383),
                    multiplier: Some(0x100000001b3),
                    byte_transform: Some(r2sym::NativeWorkerByteTransform::AsciiLowercase),
                }),
                table_walk: None,
            }),
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
        }];
        artifact
    }

    fn pad_summary_only_artifact_to_dense(
        mut artifact: r2sym::SemanticArtifact,
    ) -> r2sym::SemanticArtifact {
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            unreachable!("native artifact helper must build native body");
        };
        let template = native.summary.worker_summaries[0].clone();
        while native.summary.worker_summaries.len() < 8 {
            let mut summary = template.clone();
            summary.anchor += native.summary.worker_summaries.len() as u64 * 0x10;
            summary.kind = r2sym::NativeWorkerSummaryKind::Unknown;
            summary.memory = None;
            summary.len = None;
            summary.loop_summary = None;
            native.summary.worker_summaries.push(summary);
        }
        artifact
    }

    #[test]
    fn engine_cache_key_tracks_typed_context_and_assumptions() {
        let arch = r2il::ArchSpec::new("x86-64");
        let blocks = const_return_blocks(0x401000, 0);
        let first = EngineFunctionKey::from_parts(
            0x401000,
            "sym.main",
            Some(&arch),
            &blocks,
            1,
            2,
            3,
            None,
            "aaa",
        );
        let changed_assumption = EngineFunctionKey::from_parts(
            0x401000,
            "sym.main",
            Some(&arch),
            &blocks,
            1,
            9,
            3,
            None,
            "aaa",
        );
        let changed_context = EngineFunctionKey::from_parts(
            0x401000,
            "sym.main",
            Some(&arch),
            &blocks,
            8,
            2,
            3,
            None,
            "aaa",
        );

        assert_ne!(first, changed_assumption);
        assert_ne!(first, changed_context);
    }

    #[test]
    fn function_artifact_cache_key_hashes_parsed_assumptions_separately() {
        let blocks = const_return_blocks(0x401000, 0);
        let parsed_context = r2types::ParsedExternalContext {
            context_schema_version: Some(1),
            context_dirty_epoch: Some(7),
            type_dirty_epoch: Some(3),
            context_hash: Some(42),
            ..r2types::ParsedExternalContext::default()
        };
        let base_request = EngineAnalyzeRequest {
            function_name: "sym.main".to_string(),
            function_addr: 0x401000,
            blocks,
            arch: None,
            ptr_bits: 64,
            semantic_metadata_enabled: false,
            reg_type_hints: HashMap::new(),
            parsed_context,
            external_context_fallback_hash: 0xfeed,
            scope_facts: InterprocScopeFacts::empty(),
            interproc_max_iterations: 1,
            symbolic_scope: None,
            precomputed_semantic_artifact: None,
            semantic_mode: EngineSemanticMode::Full,
            include_interproc_summary_set: true,
        };
        let base = function_artifact_cache_key(&base_request);

        let mut changed_assumption_request = base_request.clone();
        changed_assumption_request.parsed_context.assumptions =
            r2ssa::AssumptionSet::new(vec![cache_register_assumption("rdi-one", "rdi", 1)]);
        let changed_assumption = function_artifact_cache_key(&changed_assumption_request);

        assert_eq!(
            base.analysis.typed_context_hash,
            changed_assumption.analysis.typed_context_hash
        );
        assert_ne!(
            base.analysis.assumptions_hash,
            changed_assumption.analysis.assumptions_hash
        );
        assert_ne!(base, changed_assumption);

        let mut reordered_first = base_request.clone();
        reordered_first.parsed_context.assumptions = r2ssa::AssumptionSet::new(vec![
            cache_register_assumption("rdi-one", "rdi", 1),
            cache_register_assumption("rsi-two", "rsi", 2),
        ]);
        let mut reordered_second = base_request.clone();
        reordered_second.parsed_context.assumptions = r2ssa::AssumptionSet::new(vec![
            cache_register_assumption("rsi-two", "rsi", 2),
            cache_register_assumption("rdi-one", "rdi", 1),
        ]);
        assert_eq!(
            function_artifact_cache_key(&reordered_first),
            function_artifact_cache_key(&reordered_second),
            "assumption identity should be deterministic and order-insensitive"
        );

        let mut changed_config_request = base_request;
        changed_config_request.semantic_metadata_enabled = true;
        let changed_config = function_artifact_cache_key(&changed_config_request);
        assert_eq!(
            base.analysis.assumptions_hash,
            changed_config.analysis.assumptions_hash
        );
        assert_ne!(
            base.analysis.analysis_depth_hash,
            changed_config.analysis.analysis_depth_hash
        );
    }

    #[test]
    fn cache_keys_partition_analysis_artifact_and_render_inputs() {
        let arch = r2il::ArchSpec::new("x86-64");
        let blocks = const_return_blocks(0x401000, 0);
        let analysis = AnalysisCacheKey::from_parts(
            0x401000,
            "sym.main",
            Some(&arch),
            &blocks,
            0x10,
            0x20,
            "aaa",
        );
        let changed_typed_context = AnalysisCacheKey::from_parts(
            0x401000,
            "sym.main",
            Some(&arch),
            &blocks,
            0x11,
            0x20,
            "aaa",
        );
        let changed_assumptions = AnalysisCacheKey::from_parts(
            0x401000,
            "sym.main",
            Some(&arch),
            &blocks,
            0x10,
            0x21,
            "aaa",
        );

        assert_ne!(analysis, changed_typed_context);
        assert_ne!(analysis, changed_assumptions);

        let artifact = ArtifactCacheKey::from_hashes(analysis.clone(), 0x30, 0x40);
        let changed_interproc_budget = ArtifactCacheKey::from_hashes(analysis.clone(), 0x31, 0x40);
        let changed_symbolic_scope = ArtifactCacheKey::from_hashes(analysis.clone(), 0x30, 0x41);

        assert_ne!(artifact, changed_interproc_budget);
        assert_ne!(artifact, changed_symbolic_scope);

        let render = RenderCacheKey::from_artifact(artifact.clone(), 0x50, 0x60);
        let changed_render_payload = RenderCacheKey::from_artifact(artifact.clone(), 0x51, 0x60);
        let changed_render_config = RenderCacheKey::from_artifact(artifact, 0x50, 0x61);

        assert_ne!(render, changed_render_payload);
        assert_ne!(render, changed_render_config);
    }

    #[test]
    fn session_cache_metrics_track_hits_misses_and_evictions() {
        let session = EngineSession::new(2);
        let blocks = const_return_blocks(0x1000, 0);
        let key1 = EngineFunctionKey::from_parts(0x1000, "a", None, &blocks, 0, 0, 0, None, "aa");
        let key2 = EngineFunctionKey::from_parts(0x1001, "b", None, &blocks, 0, 0, 0, None, "aa");
        let key3 = EngineFunctionKey::from_parts(0x1002, "c", None, &blocks, 0, 0, 0, None, "aa");

        assert!(session.cached_artifacts(&key1).is_none());
        session.insert_artifacts(
            key1.clone(),
            EngineArtifacts {
                rendered: Some("one".to_string()),
                ..EngineArtifacts::default()
            },
        );
        session.insert_artifacts(
            key2.clone(),
            EngineArtifacts {
                rendered: Some("two".to_string()),
                ..EngineArtifacts::default()
            },
        );
        assert!(session.cached_artifacts(&key1).is_some());
        session.insert_artifacts(
            key3,
            EngineArtifacts {
                rendered: Some("three".to_string()),
                ..EngineArtifacts::default()
            },
        );
        assert!(session.cached_artifacts(&key2).is_none());

        let metrics = session.cache_metrics();
        assert_eq!(
            metrics.artifacts,
            CacheCounters {
                hits: 1,
                misses: 2,
                insertions: 3,
                evictions: 1,
            }
        );
        assert_eq!(metrics.total().total_lookups(), 3);
    }

    #[test]
    fn session_cache_metrics_are_partitioned_by_cache_kind() {
        let session = EngineSession::new(4);
        let blocks = const_return_blocks(0x2000, 0);
        let analysis = AnalysisCacheKey::from_parts(0x2000, "a", None, &blocks, 1, 2, "types-only");
        let artifact = ArtifactCacheKey::from_hashes(analysis.clone(), 3, 4);
        let render = RenderCacheKey::from_artifact(artifact.clone(), 5, 6);

        assert!(session.cached_analysis(&analysis).is_none());
        session.insert_analysis(
            analysis.clone(),
            EngineArtifacts {
                rendered: Some("analysis".to_string()),
                ..EngineArtifacts::default()
            },
        );
        assert!(session.cached_analysis(&analysis).is_some());

        assert!(session.cached_artifacts(&artifact).is_none());
        session.insert_artifacts(
            artifact,
            EngineArtifacts {
                rendered: Some("artifact".to_string()),
                ..EngineArtifacts::default()
            },
        );

        assert!(session.cached_render(&render).is_none());
        session.insert_render(render.clone(), "rendered".to_string());
        assert_eq!(session.cached_render(&render), Some("rendered".to_string()));

        let metrics = session.cache_metrics();
        assert_eq!(metrics.analysis.hits, 1);
        assert_eq!(metrics.analysis.misses, 1);
        assert_eq!(metrics.artifacts.hits, 0);
        assert_eq!(metrics.artifacts.misses, 1);
        assert_eq!(metrics.renders.hits, 1);
        assert_eq!(metrics.renders.misses, 1);
    }

    #[test]
    fn engine_session_decompile_owns_render_cache() {
        let session = EngineSession::new(4);
        let blocks = const_return_blocks(0x401000, 0);
        let prepared = r2ssa::SsaArtifact::for_decompile(&blocks, None)
            .expect("prepared")
            .with_name("sym.zero");
        let analysis =
            AnalysisCacheKey::from_parts(0x401000, "sym.zero", None, &blocks, 1, 2, "aa");
        let artifact = ArtifactCacheKey::from_hashes(analysis, 3, 4);
        let render = RenderCacheKey::from_artifact(artifact, 5, 6);
        let request = EngineDecompileRequest {
            function_name: "sym.zero".to_string(),
            prepared_ssa: prepared,
            function_facts: FunctionFacts::default(),
            function_names: HashMap::new(),
            strings: HashMap::new(),
            symbols: HashMap::new(),
            ptr_bits: 64,
            config: r2dec::DecompilerConfig::x86_64(),
            render_cache_key: Some(render),
            fallback_comment: None,
        };

        let first = session.decompile(request.clone());
        let second = session.decompile(request);

        assert!(!first.metrics.cache_hit);
        assert!(second.metrics.cache_hit);
        assert_eq!(first.output, second.output);
        assert_eq!(first.decision.plan, second.decision.plan);
        let metrics = session.cache_metrics();
        assert_eq!(metrics.renders.hits, 1);
        assert_eq!(metrics.renders.misses, 1);
        assert_eq!(metrics.renders.insertions, 1);
    }

    #[test]
    fn decompile_route_decision_reports_prepared_proof_coverage() {
        let mut entry = R2ILBlock::new(0x401000, 4);
        entry.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x401000, 8),
            cond: r2il::Varnode::constant(1, 1),
        });
        let blocks = vec![entry];
        let prepared = r2ssa::SsaArtifact::for_decompile(&blocks, None)
            .expect("prepared")
            .with_name("sym.loop");
        let cfg_summary = prepared.function().cfg_risk_summary();
        let function_facts = FunctionFacts::default();

        let decision = decompile_route_decision(
            "sym.loop",
            &function_facts,
            Some(&prepared),
            &function_facts.types,
            &cfg_summary,
        );

        assert!(decision.proof_coverage.certified_loops > 0);
        assert_eq!(
            decision.render_permission.kind,
            r2sym::RenderPermissionKind::CertifiedC
        );
        assert_eq!(
            EngineRequestPlan::decompile(decision)
                .diagnostics()
                .proof_coverage
                .expect("proof coverage")
                .certified_loops,
            1
        );
    }

    #[test]
    fn type_fact_proof_coverage_counts_only_source_authorized_out_params() {
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

        assert_eq!(
            proof_coverage_from_type_facts(&type_facts).certified_out_params,
            1
        );
    }

    #[test]
    fn type_fact_proof_coverage_counts_only_render_authorized_signature() {
        let current_signature = r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Typedef("size_t".to_string())),
            params: vec![r2types::FunctionParamSpec {
                name: "buf".to_string(),
                ty: r2types::parse_type_like_spec("uint8_t*", 64),
            }],
        };
        let stale_signature = r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Typedef("int".to_string())),
            params: vec![r2types::FunctionParamSpec {
                name: "other".to_string(),
                ty: Some(r2types::CTypeLike::Typedef("int".to_string())),
            }],
        };
        let stale_certified = FunctionTypeFacts {
            merged_signature: Some(current_signature.clone()),
            signature_certificate: r2types::SignatureCertificate::from_signature(
                &stale_signature,
                [r2types::SignatureCertificateSource::ExternalContext],
            ),
            ..FunctionTypeFacts::default()
        };
        let current_certified = FunctionTypeFacts {
            merged_signature: Some(current_signature.clone()),
            signature_certificate: r2types::SignatureCertificate::from_signature(
                &current_signature,
                [r2types::SignatureCertificateSource::ExternalContext],
            ),
            ..FunctionTypeFacts::default()
        };

        assert_eq!(
            proof_coverage_from_type_facts(&stale_certified).certified_signatures,
            0
        );
        assert_eq!(
            proof_coverage_from_type_facts(&current_certified).certified_signatures,
            1
        );
    }

    #[test]
    fn decompile_route_decision_residualizes_loop_cfg_without_prepared_proof() {
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 2,
            loop_count: 1,
            back_edge_count: 1,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let function_facts = FunctionFacts::default();

        let decision = decompile_route_decision(
            "sym.loop",
            &function_facts,
            None,
            &function_facts.types,
            &cfg_summary,
        );

        assert_eq!(
            decision.render_permission.kind,
            r2sym::RenderPermissionKind::Residual
        );
        assert!(
            decision
                .render_permission
                .reason
                .contains("missing prepared SSA certificates")
        );
    }

    #[test]
    fn engine_session_summary_decompile_owns_render_cache() {
        let session = EngineSession::new(4);
        let blocks = const_return_blocks(0x402000, 0);
        let prepared = r2ssa::SsaArtifact::for_decompile(&blocks, None).expect("prepared");
        let analysis =
            AnalysisCacheKey::from_parts(0x402000, "sym.summary", None, &blocks, 1, 2, "aa");
        let artifact = ArtifactCacheKey::from_hashes(analysis, 3, 4);
        let render = RenderCacheKey::from_artifact(artifact, 5, 6);
        let request = EngineSummaryDecompileRequest {
            function_name: "sym.summary".to_string(),
            cfg_summary: prepared.function().cfg_risk_summary(),
            function_facts: FunctionFacts::default(),
            named_worker_guarded: false,
            config: r2dec::DecompilerConfig::x86_64(),
            render_cache_key: Some(render),
            fallback_comment: Some("/* summary fallback */".to_string()),
        };

        let first = session.decompile_summary(request.clone()).expect("first");
        let second = session.decompile_summary(request).expect("second");

        assert!(!first.metrics.cache_hit);
        assert!(second.metrics.cache_hit);
        assert_eq!(first.output, "/* summary fallback */");
        assert_eq!(first.output, second.output);
        let metrics = session.cache_metrics();
        assert_eq!(metrics.renders.hits, 1);
        assert_eq!(metrics.renders.misses, 1);
        assert_eq!(metrics.renders.insertions, 1);
    }

    #[test]
    fn summary_preprobe_standard_exact_worker_defers_to_full_native_decompile() {
        let session = EngineSession::new(4);
        let blocks = const_return_blocks(0x402000, 0);
        let prepared = r2ssa::SsaArtifact::for_decompile(&blocks, None).expect("prepared");
        let artifact = pad_summary_only_artifact_to_dense(summary_only_exact_hash_fold_artifact());
        let request = EngineSummaryDecompileRequest {
            function_name: "dbg.fnv_fold".to_string(),
            cfg_summary: prepared.function().cfg_risk_summary(),
            function_facts: FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact)),
            named_worker_guarded: false,
            config: r2dec::DecompilerConfig::x86_64(),
            render_cache_key: None,
            fallback_comment: Some("/* summary fallback */".to_string()),
        };

        assert!(session.decompile_summary(request).is_none());
    }

    #[test]
    fn session_cache_refreshes_recency_and_evicts_oldest() {
        let session = EngineSession::new(2);
        let blocks = const_return_blocks(0x1000, 0);
        let key1 = EngineFunctionKey::from_parts(0x1000, "a", None, &blocks, 0, 0, 0, None, "aa");
        let key2 = EngineFunctionKey::from_parts(0x1001, "b", None, &blocks, 0, 0, 0, None, "aa");
        let key3 = EngineFunctionKey::from_parts(0x1002, "c", None, &blocks, 0, 0, 0, None, "aa");

        session.insert_artifacts(
            key1.clone(),
            EngineArtifacts {
                rendered: Some("one".to_string()),
                ..EngineArtifacts::default()
            },
        );
        session.insert_artifacts(
            key2.clone(),
            EngineArtifacts {
                rendered: Some("two".to_string()),
                ..EngineArtifacts::default()
            },
        );
        assert_eq!(
            session.cached_artifacts(&key1).and_then(|a| a.rendered),
            Some("one".to_string())
        );
        session.insert_artifacts(
            key3.clone(),
            EngineArtifacts {
                rendered: Some("three".to_string()),
                ..EngineArtifacts::default()
            },
        );

        assert_eq!(
            session.cached_artifacts(&key1).and_then(|a| a.rendered),
            Some("one".to_string())
        );
        assert!(session.cached_artifacts(&key2).is_none());
        assert_eq!(
            session.cached_artifacts(&key3).and_then(|a| a.rendered),
            Some("three".to_string())
        );
    }

    #[test]
    fn decompile_probe_decision_guards_named_large_worker() {
        let mut blocks = const_return_blocks(0x4b30, 0);
        for idx in 0..210 {
            blocks.push(R2ILBlock::new(0x5000 + idx, 1));
        }
        let decision =
            decompile_probe_decision(&blocks, 0x4b30, "fcn.00004b30", "readlinebuffer_delim");

        assert!(!decision.display_summary_family);
        assert!(!decision.named_worker_guarded);
        assert!(decision.block_guarded);
        assert!(decision.summary_probe_needed);
        assert!(decision.summary_probe_skipped_large_cfg);
        assert_eq!(decision.summary_probe_name, "readlinebuffer_delim");
    }

    #[test]
    fn decompile_probe_decision_keeps_medium_non_workers_on_full_route() {
        let mut blocks = (0..8)
            .map(|idx| R2ILBlock::new(0x6000 + idx, 1))
            .collect::<Vec<_>>();
        for idx in 0..129 {
            blocks[0].push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x100 + idx, 8),
                src: r2il::Varnode::constant(idx, 8),
            });
        }

        let decision =
            decompile_probe_decision(&blocks, 0x6000, "dbg.medium_helper", "dbg.medium_helper");

        assert!(!decision.block_guarded);
        assert!(!decision.summary_probe_needed);
        assert!(!decision.summary_probe_skipped_large_cfg);
        assert_eq!(decision.summary_probe_name, "dbg.medium_helper");
        assert!(!decision.named_worker_guarded);
    }

    #[test]
    fn decompile_probe_decision_does_not_prefer_full_diagnostic_name_without_evidence() {
        let mut blocks = const_return_blocks(0x4bc0, 0);
        for idx in 0..600 {
            blocks[0].push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x200 + idx, 8),
                src: r2il::Varnode::constant(idx, 8),
            });
        }

        let decision = decompile_probe_decision(&blocks, 0x4bc0, "sym.diagnose", "sym.diagnose");

        assert!(!decision.display_summary_family);
        assert!(decision.block_guarded);
        assert!(decision.summary_probe_needed);
        assert!(decision.summary_probe_skipped_large_cfg);
    }

    #[test]
    fn decompile_probe_decision_uses_strict_block_count_guard_boundary() {
        let exactly_limit = (0..200)
            .map(|idx| R2ILBlock::new(0x7000 + idx, 1))
            .collect::<Vec<_>>();
        let over_limit = (0..201)
            .map(|idx| R2ILBlock::new(0x8000 + idx, 1))
            .collect::<Vec<_>>();

        let at_limit = decompile_probe_decision(&exactly_limit, 0x7000, "dbg.helper", "dbg.helper");
        let over_limit = decompile_probe_decision(&over_limit, 0x8000, "dbg.helper", "dbg.helper");

        assert!(!at_limit.summary_probe_skipped_large_cfg);
        assert!(!at_limit.block_guarded);
        assert!(over_limit.summary_probe_skipped_large_cfg);
        assert!(over_limit.block_guarded);
    }

    #[test]
    fn decompile_probe_decision_uses_strict_op_count_guard_boundary() {
        let mut exactly_limit = R2ILBlock::new(0x9000, 1);
        let mut over_limit = R2ILBlock::new(0xa000, 1);
        for idx in 0..512 {
            exactly_limit.push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x300 + idx, 8),
                src: r2il::Varnode::constant(idx, 8),
            });
            over_limit.push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x600 + idx, 8),
                src: r2il::Varnode::constant(idx, 8),
            });
        }
        over_limit.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::unique(0x900, 8),
            src: r2il::Varnode::constant(0x900, 8),
        });

        let at_limit =
            decompile_probe_decision(&[exactly_limit], 0x9000, "dbg.helper", "dbg.helper");
        let over_limit =
            decompile_probe_decision(&[over_limit], 0xa000, "dbg.helper", "dbg.helper");

        assert!(!at_limit.summary_probe_skipped_large_cfg);
        assert!(!at_limit.block_guarded);
        assert!(over_limit.summary_probe_skipped_large_cfg);
        assert!(over_limit.block_guarded);
    }

    #[test]
    fn decompile_probe_decision_probes_small_switch_cfg() {
        let mut switch_block = R2ILBlock::new(0xb000, 4);
        switch_block.switch_info = Some(r2il::SwitchInfo {
            switch_addr: 0xb000,
            min_val: 0,
            max_val: 0,
            default_target: None,
            cases: vec![r2il::SwitchCase {
                value: 0,
                target: 0xb010,
            }],
        });
        let blocks = vec![switch_block, R2ILBlock::new(0xb010, 1)];

        let decision = decompile_probe_decision(&blocks, 0xb000, "dbg.helper", "dbg.helper");

        assert!(!decision.summary_probe_skipped_large_cfg);
        assert!(!decision.block_guarded);
        assert!(decision.summary_probe_needed);
    }

    #[test]
    fn function_identity_keeps_ordered_aliases_for_summary_and_type_routes() {
        let identity = EngineFunctionIdentity::with_aliases(
            0x7000,
            "fcn.00007000",
            "sym.limfield.isra.0",
            ["dbg.limfield", "sym.limfield.isra.0"],
        );
        let candidates = identity.name_candidates().collect::<Vec<_>>();

        assert_eq!(
            candidates,
            vec![
                "fcn.00007000",
                "00007000",
                "sym.limfield.isra.0",
                "limfield",
                "dbg.limfield"
            ]
        );
        assert_eq!(identity.summary_probe_name(), "sym.limfield.isra.0");
        assert!(
            !identity.has_summary_family(),
            "name aliases alone must not create summary-family applicability"
        );
    }

    #[test]
    fn function_identity_reports_evidence_backed_summary_family() {
        let identity = EngineFunctionIdentity::with_aliases(
            0x401000,
            "sym.imp.memcpy",
            "sym.imp.memcpy",
            ["fcn.00401000", "memcpy"],
        );

        assert!(identity.has_summary_family());
        assert_eq!(identity.summary_probe_name(), "sym.imp.memcpy");
    }

    #[test]
    fn function_identity_uses_address_name_aliases_for_route_policy() {
        let identity = EngineFunctionIdentity::with_aliases(
            0x8b50,
            "fcn.00008b50",
            "fcn.00008b50",
            ["dbg.init_node"],
        );

        assert!(identity.name_candidates().all(|name| {
            !r2sym::native_worker_summary_applicability_for_name(identity.function_addr, name)
                .is_supported()
        }));
        assert!(
            !identity
                .name_candidates()
                .any(should_use_direct_named_native_worker_decompile)
        );
        assert_eq!(identity.summary_probe_name(), "fcn.00008b50");
    }

    #[test]
    fn name_only_worker_families_do_not_select_direct_decompile() {
        for name in [
            "dbg.init_node",
            "sym.rpl_nanosleep",
            "dbg.xnanosleep",
            "dbg.mergefiles",
            "dbg.xnrealloc",
            "dbg.xnmalloc",
            "dbg.xinmalloc",
            "dbg.init_node.isra.0",
            "dbg.cycle_check",
            "dbg.file_prefixlen",
            "sym.operand_matches",
            "dbg.xstrcoll_df_version",
            "dbg.rev_strcmp_df_mtime",
            "entry0",
            "sym.register_tm_clones",
            "dbg.save_token",
            "dbg.filename_unescape",
            "sym.compare",
            "dbg.close_stream",
            "dbg.rpl_fseeko",
            "dbg.reap",
            "dbg.record_file",
            "dbg.quotearg_free",
            "dbg.num_processors_via_affinity_mask",
            "sym.format_user_or_group",
            "entry.fini0",
            "sym.xmalloc",
            "dbg.rpl_reallocarray",
            "dbg.hash_clear",
            "sym.hash_get_max_bucket_length",
            "sym.hash_lookup",
            "dbg.hash_get_entries",
            "dbg.hash_do_for_each",
            "dbg.heap_insert",
            "sym.version_etc_va",
            "dbg.mdir_name",
            "dbg.last_component",
            "dbg.restore_initial_cwd",
            "sym.cwd_advance_fd",
            "dbg.parse_field_count",
            "dbg.yesno",
            "dbg.get_root_dev_ino",
            "dbg.getuser",
            "dbg.getgroup",
            "dbg.open_safer",
            "sym.calc_req_mask",
            "dbg.clear_files",
            "dbg.fts_sort",
            "dbg.write_bytes",
            "dbg.is_utf8_charset",
            "dbg.mcel_tocmp",
            "dbg.re_string_reconstruct",
            "dbg.parse_datetime_body",
            "dbg.posixtime",
            "dbg.randperm_new",
            "dbg.readtoken",
            "dbg.readtokens",
            "dbg.re_search_internal",
            "dbg.re_compile_internal",
            "dbg.parse_expression",
            "dbg.build_trtable",
            "dbg.update_cur_sifted_state",
            "dbg.transit_state_bkref",
            "dbg.build_charclass",
            "dbg.check_arrival",
            "dbg.peek_token",
            "dbg.build_wcs_upper_buffer",
            "dbg.yyparse",
            "dbg.install_file_in_file",
            "dbg.chown_files",
            "dbg.read_utmp",
            "dbg.dopass",
            "sym.factor_up.part.0.constprop.0",
            "dbg.mp_factor_using_pollard_rho",
            "dbg.seq_fast",
            "dbg.tsort",
            "dbg.error_tail",
            "dbg.argmatch_to_argument",
            "dbg.opendirat",
            "dbg.fd_safer",
            "dbg.emit_verbose",
            "dbg.posix2_version",
        ] {
            let applicability = r2sym::native_worker_summary_applicability_for_name(0, name);
            assert!(
                !applicability.is_supported(),
                "name-only worker families must not create applicability for {name}: {applicability:?}"
            );
            assert!(
                !should_use_direct_named_native_worker_decompile(name),
                "name-only hint must not select direct decompile for {name}"
            );
        }

        assert!(!should_use_direct_named_native_worker_decompile(
            "dbg.key_to_opts"
        ));
        assert!(!should_use_direct_named_native_worker_decompile(
            "dbg.hash_initialize"
        ));
        assert!(!should_use_direct_named_native_worker_decompile(
            "dbg.canonicalize_filename_mode"
        ));
        for name in [
            "sym.blake2b_compress",
            "sym.sm3_process_block",
            "sym.sha256_process_block",
        ] {
            let applicability = r2sym::native_worker_summary_applicability_for_name(0, name);
            assert!(
                !applicability.is_supported(),
                "crypto/hash names alone must not create worker applicability for {name}: {applicability:?}"
            );
            assert!(
                !should_use_direct_named_native_worker_decompile(name),
                "unsupported hash name must not select direct decompile for {name}"
            );
        }
        assert!(!should_prefer_full_decompile_for_named_worker(
            "sym.diagnose"
        ));
    }

    #[test]
    fn direct_named_worker_type_projection_rejects_program_orchestrator_name_hints() {
        assert!(!should_use_direct_named_native_worker_type_projection(
            "dbg.main"
        ));
        for name in [
            "dbg.xnmalloc",
            "randread",
            "sym.sha256_process_block",
            "sym.blake2b_compress",
            "dbg.posixtime",
            "dbg.randperm_new",
            "dbg.readtoken",
            "dbg.readtokens",
        ] {
            assert!(
                !should_use_direct_named_native_worker_type_projection(name),
                "name-only hint must not select type projection for {name}"
            );
        }
    }

    #[test]
    fn direct_named_worker_decompile_summary_rejects_name_only_workers() {
        let (_, ptr_bits, config) = r2dec::DecompilerConfig::for_arch(None);
        let parsed_context = r2types::ParsedExternalContext::default();
        let response = EngineSession::new(4).decompile_direct_named_worker_summary(
            EngineDirectNamedWorkerDecompileRequest {
                function_addr: 0x8b50,
                function_name: "dbg.init_node",
                arch: None,
                ptr_bits,
                parsed_context: &parsed_context,
                config,
            },
        );

        assert!(response.is_none());
    }

    #[test]
    fn direct_named_worker_decompile_summary_rejects_full_route_names() {
        let (_, ptr_bits, config) = r2dec::DecompilerConfig::for_arch(None);
        let parsed_context = r2types::ParsedExternalContext::default();
        let response = EngineSession::new(4).decompile_direct_named_worker_summary(
            EngineDirectNamedWorkerDecompileRequest {
                function_addr: 0x401000,
                function_name: "sym.diagnose",
                arch: None,
                ptr_bits,
                parsed_context: &parsed_context,
                config,
            },
        );

        assert!(response.is_none());
    }

    #[test]
    fn semantic_compile_does_not_prefer_name_only_worker_seed_before_full_semantics() {
        let blocks = const_return_blocks(0x8b50, 0);
        let ssa_func = r2ssa::SsaArtifact::for_decompile(&blocks, None)
            .expect("prepared ssa")
            .with_name("dbg.init_node");

        let artifact = compile_semantic_artifact_for_analysis(
            &ssa_func,
            0x8b50,
            "dbg.init_node",
            None,
            None,
            None,
        );

        assert_ne!(
            artifact.granularity,
            r2sym::ArtifactGranularity::SummaryOnly
        );
        assert!(!matches!(
            artifact.decompile_plan(),
            r2sym::DecompilePlan::NativeSummaryIslands { .. }
        ));
    }

    #[test]
    fn semantic_compile_preprobes_small_loop_workers_before_solver() {
        let mut entry = R2ILBlock::new(0x9000, 4);
        entry.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x9000, 8),
            cond: r2il::Varnode::constant(1, 1),
        });
        let loop_ssa = r2ssa::SsaArtifact::for_decompile(&[entry], None)
            .expect("loop ssa")
            .with_name("dbg.loop_worker");
        let straight_ssa = r2ssa::SsaArtifact::for_decompile(&const_return_blocks(0x9100, 0), None)
            .expect("straight-line ssa")
            .with_name("dbg.straight_worker");

        assert!(should_probe_native_worker_summary_before_full_semantics(
            &loop_ssa, None
        ));
        assert!(!should_probe_native_worker_summary_before_full_semantics(
            &straight_ssa,
            None
        ));
    }

    #[test]
    fn semantic_compile_preprobes_flag_expanded_loop_workers_before_solver() {
        let mut entry = R2ILBlock::new(0x9050, 4);
        for index in 0..300 {
            entry.push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(index, 1),
                src: r2il::Varnode::constant(index, 1),
            });
        }
        entry.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x9050, 8),
            cond: r2il::Varnode::constant(1, 1),
        });
        let loop_ssa = r2ssa::SsaArtifact::for_decompile(&[entry.clone()], None)
            .expect("loop ssa")
            .with_name("dbg.flag_expanded_loop_worker");
        let decision = decompile_probe_decision(
            &[entry],
            0x9050,
            "dbg.flag_expanded_loop_worker",
            "dbg.flag_expanded_loop_worker",
        );

        assert!(should_probe_native_worker_summary_before_full_semantics(
            &loop_ssa, None
        ));
        assert!(decision.summary_probe_needed);
    }

    #[test]
    fn prefer_full_named_workers_need_evidence_before_decompile_preprobe() {
        let blocks = const_return_blocks(0x401000, 0);
        let decision = decompile_probe_decision(&blocks, 0x401000, "dbg.diagnose", "dbg.diagnose");

        assert!(!decision.summary_probe_needed);
        assert!(!decision.summary_probe_skipped_large_cfg);
    }

    #[test]
    fn semantic_compile_skips_unbounded_solver_after_empty_loop_preprobe() {
        let mut entry = R2ILBlock::new(0x9200, 4);
        entry.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x9200, 8),
            cond: r2il::Varnode::constant(1, 1),
        });
        let loop_ssa = r2ssa::SsaArtifact::for_decompile(&[entry], None)
            .expect("loop ssa")
            .with_name("dbg.loop_worker_without_summary");

        assert!(should_skip_unbounded_semantic_artifact_after_worker_preprobe(&loop_ssa, None));
        assert!(
            maybe_compile_semantic_artifact_for_analysis(
                &loop_ssa,
                0x9200,
                "dbg.loop_worker_without_summary",
                None,
                None,
                None
            )
            .is_none()
        );
    }

    #[test]
    fn semantic_compile_keeps_vm_evidence_after_loop_preprobe() {
        let blocks = switch_loop_vm_blocks();
        let arch = vm_test_arch();
        let vm_ssa = r2ssa::SsaArtifact::for_decompile(&blocks, Some(&arch))
            .expect("vm ssa")
            .with_name("dbg.vm_loop_worker");

        assert!(should_probe_native_worker_summary_before_full_semantics(
            &vm_ssa, None
        ));
        assert!(
            r2sym::has_strong_vm_evidence(&vm_ssa),
            "test fixture must carry enough structural VM evidence to justify bypassing the refusal gate"
        );
        assert!(!should_skip_unbounded_semantic_artifact_after_worker_preprobe(&vm_ssa, None));

        let artifact = maybe_compile_semantic_artifact_for_analysis(
            &vm_ssa,
            0x9300,
            "dbg.vm_loop_worker",
            None,
            Some(&arch),
            None,
        )
        .expect("vm artifact should not be refused before classification");

        assert_eq!(artifact.execution, r2sym::ExecutionModel::Vm);
        assert!(artifact.vm_body().is_some());
    }

    #[test]
    fn native_worker_type_projection_rejects_name_only_params_and_summary_return() {
        let parsed_context = r2types::parse_external_context_json(
            r#"{
                "signature":{
                    "ret":"int32_t",
                    "params":[
                        {"name":"a","type":"int32_t"},
                        {"name":"b","type":"int32_t"}
                    ]
                }
            }"#,
            64,
        );

        assert!(
            native_worker_type_projection(0x11a9, "randread", "x86-64", 64, &parsed_context, true)
                .is_none(),
            "name-only worker hints must not create authoritative type projection"
        );
    }

    #[test]
    fn summary_fallback_projection_preserves_authoritative_context_signature() {
        let artifact = native_linear_artifact(r2sym::SliceClass::Worker);
        let source_signature = r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Typedef("size_t".to_string())),
            params: vec![
                r2types::FunctionParamSpec {
                    name: "buf".to_string(),
                    ty: r2types::parse_type_like_spec("uint8_t*", 64),
                },
                r2types::FunctionParamSpec {
                    name: "n".to_string(),
                    ty: Some(r2types::CTypeLike::Typedef("size_t".to_string())),
                },
                r2types::FunctionParamSpec {
                    name: "a".to_string(),
                    ty: r2types::parse_type_like_spec("uint8_t", 64),
                },
                r2types::FunctionParamSpec {
                    name: "b".to_string(),
                    ty: r2types::parse_type_like_spec("uint8_t", 64),
                },
            ],
        };
        let projected = type_facts_with_summary_projection_for_candidates_with_options(
            FunctionTypeFacts {
                signature_certificate: r2types::SignatureCertificate::from_signature(
                    &source_signature,
                    [r2types::SignatureCertificateSource::ExternalContext],
                ),
                merged_signature: Some(source_signature),
                ..FunctionTypeFacts::default()
            },
            "dbg.scan_example",
            ["dbg.scan_example"],
            "x86-64",
            64,
            &artifact,
            SummaryProjectionOptions {
                preserve_authoritative_context_signature: true,
            },
        );
        let signature = projected
            .merged_signature
            .expect("source signature should remain available");

        assert_eq!(
            signature
                .ret_type
                .as_ref()
                .map(|ty| r2types::render_signature_type(ty, 64))
                .as_deref(),
            Some("size_t")
        );
        assert_eq!(signature.params[1].name, "n");
        assert_eq!(
            signature.params[1]
                .ty
                .as_ref()
                .map(|ty| r2types::render_signature_type(ty, 64))
                .as_deref(),
            Some("size_t")
        );
    }

    #[test]
    fn name_only_native_worker_seed_is_not_created() {
        for name in [
            "sym.diagnose",
            "dbg.parse_field_count",
            "randread",
            "dbg.print_current_files",
        ] {
            assert!(
                native_worker_summary_seed(0x401000, name).is_none(),
                "name-only worker seed must not be created for {name}"
            );
        }
    }

    #[test]
    fn libc_summary_seed_still_represents_known_import_semantics() {
        let summary = native_worker_summary_seed(0x401000, "sym.imp.memcpy").expect("memcpy seed");

        assert!(!summary.transfer_effects.is_empty());
        assert_eq!(summary.arg_count_hint, Some(3));
    }

    #[test]
    fn type_route_decision_allows_moderate_dense_semantic_plan() {
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 55,
            loop_count: 1,
            back_edge_count: 1,
            switch_block_count: 1,
            max_switch_cases: 48,
        };
        let function_facts = FunctionFacts::default();

        assert!(type_cfg_forces_bounded_plan(&cfg_summary));
        assert!(type_cfg_allows_semantic_plan(&cfg_summary));
        assert_eq!(
            type_route_decision(&function_facts, &cfg_summary, false).kind,
            EngineTypeRouteKind::FullWriteback
        );
    }

    #[test]
    fn type_route_decision_bounds_large_loop_cfg() {
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 1977,
            loop_count: 9,
            back_edge_count: 17,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let function_facts = FunctionFacts::default();
        let decision = type_route_decision(&function_facts, &cfg_summary, false);

        assert_eq!(decision.kind, EngineTypeRouteKind::BoundedCfg);
        assert_eq!(decision.plan, EnginePlan::BoundedType);
        assert!(decision.prefer_bounded_type_plan);
        assert!(
            decision
                .reason
                .as_deref()
                .is_some_and(|reason| reason.contains("complex loop graph"))
        );
    }

    #[test]
    fn type_route_decision_does_not_treat_name_only_workers_as_type_input() {
        let summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x11a9),
            Some("randread".to_string()),
        );
        let artifact = r2sym::compile_named_native_worker_summary_artifact(&summary, true);
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 200,
            loop_count: 8,
            back_edge_count: 12,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let function_facts = FunctionFacts::default();

        assert!(artifact.is_none());
        assert_eq!(
            type_route_decision(&function_facts, &cfg_summary, false).kind,
            EngineTypeRouteKind::FullWriteback
        );
    }

    #[test]
    fn bounded_cfg_writeback_plan_preserves_signature_context() {
        let signature = r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Void),
            params: vec![r2types::FunctionParamSpec {
                name: "status".to_string(),
                ty: Some(r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                }),
            }],
        };
        let type_facts = FunctionTypeFacts {
            signature_certificate: r2types::SignatureCertificate::from_signature(
                &signature,
                [r2types::SignatureCertificateSource::ExternalContext],
            ),
            merged_signature: Some(signature),
            ..FunctionTypeFacts::default()
        };
        let function_facts = FunctionFacts::new(type_facts, None);
        let plan = bounded_cfg_type_writeback_plan(
            "fcn.401000",
            "x86-64",
            64,
            Some("amd64"),
            &function_facts,
            "bounded type plan for large CFG".to_string(),
        );

        assert_eq!(plan.signature.signature, "void fcn.401000 (int32_t status)");
        assert_eq!(plan.signature.callconv, "amd64");
        assert_eq!(
            plan.diagnostics.warnings,
            vec!["bounded type plan for large CFG"]
        );
    }

    #[test]
    fn decompile_type_override_prefers_authoritative_context_signature() {
        let blocks = const_return_blocks(0x401000, 0);
        let signature = r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Int {
                bits: 64,
                signedness: r2types::Signedness::Unsigned,
            }),
            params: vec![r2types::FunctionParamSpec {
                name: "buf".to_string(),
                ty: Some(r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Int {
                        bits: 8,
                        signedness: r2types::Signedness::Unsigned,
                    },
                ))),
            }],
        };
        let request = EngineAnalyzeRequest {
            function_name: "dbg.fnv_fold".to_string(),
            function_addr: 0x401000,
            blocks: blocks.clone(),
            arch: None,
            ptr_bits: 64,
            semantic_metadata_enabled: false,
            reg_type_hints: HashMap::new(),
            parsed_context: r2types::ParsedExternalContext {
                current_signature: Some(signature.clone()),
                merged_signature: Some(signature),
                ..r2types::ParsedExternalContext::default()
            },
            external_context_fallback_hash: 0,
            scope_facts: InterprocScopeFacts::empty(),
            interproc_max_iterations: 1,
            symbolic_scope: None,
            precomputed_semantic_artifact: None,
            semantic_mode: EngineSemanticMode::Full,
            include_interproc_summary_set: true,
        };
        let ssa = r2ssa::SsaArtifact::for_decompile(&blocks, None).expect("ssa");
        let artifact = EngineAnalysisArtifact {
            ssa_func: ssa.clone(),
            pattern_ssa_func: ssa,
            function_facts: FunctionFacts::default(),
            writeback_plan: r2types::TypeWritebackPlan {
                signature: r2types::InferredSignature {
                    function_name: "dbg.fnv_fold".to_string(),
                    signature: "int64_t dbg.fnv_fold (int64_t arg1)".to_string(),
                    ret_type: "int64_t".to_string(),
                    params: vec![r2types::InferredSignatureParam {
                        name: "arg1".to_string(),
                        param_type: "int64_t".to_string(),
                    }],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                var_type_candidates: Vec::new(),
                var_rename_candidates: Vec::new(),
                struct_decls: Vec::new(),
                global_type_links: Vec::new(),
                diagnostics: r2types::TypeWritebackDiagnostics::default(),
            },
        };
        let identity = EngineFunctionIdentity::new(0x401000, "dbg.fnv_fold", "fnv_fold");

        let type_facts =
            decompile_type_override(&identity, &request, &artifact).expect("type override");
        let render_signature = type_facts
            .render_authorized_signature()
            .expect("render-authorized signature");

        assert_eq!(
            render_signature.ret_type,
            request.parsed_context.current_signature.unwrap().ret_type
        );
        assert_eq!(render_signature.params[0].name, "buf");
    }

    #[test]
    fn compile_named_summary_rejects_name_owned_role_signature() {
        let summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x11a9),
            Some("verror_at_line".to_string()),
        );

        assert!(r2sym::compile_named_native_worker_summary_artifact(&summary, true).is_none());
    }

    #[test]
    fn type_summary_preprobe_rejects_name_only_program_orchestrator() {
        let mut blocks = const_return_blocks(0x55a0, 0);
        for idx in 0..210 {
            blocks.push(R2ILBlock::new(0x5600 + idx, 1));
        }
        let parsed_context = r2types::parse_external_context_json("{}", 64);

        let response = type_summary_preprobe(EngineTypePreprobeRequest {
            blocks: &blocks,
            function_addr: 0x55a0,
            canonical_name: "dbg.main",
            display_name: "dbg.main",
            arch: None,
            ptr_bits: 64,
            parsed_context: &parsed_context,
            symbolic_scope: None,
            type_seed: Some(FunctionTypeFacts::default()),
            caller_prefers_bounded_type_plan: false,
            fallback_if_guarded_without_summary: false,
        });

        assert!(response.is_none());
    }

    #[test]
    fn type_function_uses_engine_summary_preprobe_without_artifact_cache_key() {
        let mut blocks = const_return_blocks(0x55a0, 0);
        for idx in 0..210 {
            blocks.push(R2ILBlock::new(0x5600 + idx, 1));
        }
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new(8);

        let response = session
            .type_function(EngineTypeAnalysisRequest {
                analysis: EngineAnalyzeRequest {
                    function_name: "dbg.main".to_string(),
                    function_addr: 0x55a0,
                    blocks,
                    arch: None,
                    ptr_bits: 64,
                    semantic_metadata_enabled: false,
                    reg_type_hints: HashMap::new(),
                    parsed_context,
                    external_context_fallback_hash: 0,
                    scope_facts: InterprocScopeFacts::empty(),
                    interproc_max_iterations: 1,
                    symbolic_scope: None,
                    precomputed_semantic_artifact: None,
                    semantic_mode: EngineSemanticMode::Full,
                    include_interproc_summary_set: true,
                },
                caller_prefers_bounded_type_plan: false,
            })
            .expect("large main should be typed without name-owned program orchestrator route");

        assert_eq!(
            response.route_decision.kind,
            EngineTypeRouteKind::SemanticFallback
        );
        assert_eq!(response.writeback_plan.signature.params[0].name, "argc");
        assert_eq!(response.writeback_plan.signature.params[1].name, "argv");
    }

    #[test]
    fn decompile_function_uses_engine_summary_preprobe_without_plugin_policy() {
        let blocks = const_return_blocks(0x401000, 0);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new(8);

        let response = session.decompile_function(EngineFunctionDecompileRequest {
            analysis: EngineAnalyzeRequest {
                function_name: "dbg.init_node".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                external_context_fallback_hash: 0,
                scope_facts: InterprocScopeFacts::empty(),
                interproc_max_iterations: 1,
                symbolic_scope: None,
                precomputed_semantic_artifact: None,
                semantic_mode: EngineSemanticMode::Full,
                include_interproc_summary_set: true,
            },
            display_name: "init_node".to_string(),
            function_names: HashMap::new(),
            strings: HashMap::new(),
            symbols: HashMap::new(),
            config: r2dec::DecompilerConfig::default(),
            func_names_payload: "{}".to_string(),
            strings_payload: "{}".to_string(),
            symbols_payload: "{}".to_string(),
        });

        assert!(response.output.contains("init_node"));
        assert!(!matches!(
            response.decision.route,
            r2dec::SemanticRoutePlan::SummaryIslands { .. }
        ));
    }

    #[test]
    fn engine_plan_maps_routes_to_work_levels() {
        let route = r2dec::SemanticRoutePlan::SummaryIslands {
            reason: "summary".to_string(),
        };
        assert_eq!(
            select_engine_plan(EngineRequestKind::Decompile, Some(&route), None),
            EnginePlan::SemanticSummary
        );
        assert_eq!(
            select_engine_plan(EngineRequestKind::Decompile, None, None),
            EnginePlan::FastLocal
        );
    }

    #[test]
    fn request_plans_cover_decompile_types_and_profile_cache_layers() {
        let blocks = const_return_blocks(0x3010, 0);
        let prepared = r2ssa::SsaArtifact::for_decompile(&blocks, None).expect("prepared");
        let cfg_summary = prepared.function().cfg_risk_summary();
        let function_facts = FunctionFacts::default();

        let decompile = plan_decompile_request(
            "sym.simple",
            &function_facts,
            Some(&prepared),
            &function_facts.types,
            &cfg_summary,
        );
        assert_eq!(decompile.request(), EngineRequestKind::Decompile);
        assert_eq!(decompile.engine_plan(), EnginePlan::FastLocal);
        assert_eq!(decompile.cache.layer, EngineCacheLayer::Render);
        assert!(decompile.cache.lookup);
        assert!(decompile.cache.store_on_miss);
        assert_eq!(decompile.diagnostics().plan, Some(EnginePlan::FastLocal));

        let types = plan_type_request(&function_facts, &cfg_summary, false);
        assert_eq!(types.request(), EngineRequestKind::Types);
        assert_eq!(types.engine_plan(), EnginePlan::PreparedOnly);
        assert_eq!(types.cache.layer, EngineCacheLayer::Artifact);
        assert!(types.cache.lookup);

        let profile = plan_profile_request();
        assert_eq!(profile.request(), EngineRequestKind::Profile);
        assert_eq!(profile.engine_plan(), EnginePlan::PreparedOnly);
        assert_eq!(profile.cache.layer, EngineCacheLayer::MetricsSnapshot);
        assert!(!profile.cache.lookup);
        assert!(!profile.cache.store_on_miss);
    }

    #[test]
    fn symbolic_path_listing_runs_through_engine_policy() {
        let blocks = const_return_blocks(0x401000, 0);
        let prepared = r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared");
        let scope = r2sym::PreparedFunctionScope::new(
            0x401000,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x401000),
                name: Some("sym.simple".to_string()),
                prepared: prepared.clone(),
            }],
        )
        .expect("scope");
        let z3_ctx = z3::Context::thread_local();
        let symbols = HashMap::new();
        let session = EngineSession::new(4);

        let response = session.symbolic_paths(EngineSymbolicPathsRequest {
            context: EngineSymbolicContextRequest {
                z3_ctx: &z3_ctx,
                prepared: &prepared,
                scope: Some(&scope),
                arch: None,
                symbol_map: &symbols,
                merge_states: false,
                config_profile: EngineSymbolicConfigProfile::PathListing,
                seed: EngineSymbolicStateSeed::Default {
                    entry_addr: 0x401000,
                },
            },
        });

        assert_eq!(
            response.query_policy.route,
            r2sym::TargetQueryRoutePlan::dynamic_fallback()
        );
        assert!(response.summary.stats.states_explored <= SYMBOLIC_PATHS_CALL_FREE_MAX_STATES);
        assert_eq!(
            response.solution_limit,
            path_listing_solution_limit(response.summary.paths.len(), &prepared)
        );
    }

    #[test]
    fn engine_conditions_symbolic_scope_with_root_assumptions() {
        let blocks = symbolic_register_branch_blocks(0x501000);
        let prepared = r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared");
        let scope = r2sym::PreparedFunctionScope::new(
            0x501000,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x501000),
                name: Some("sym.branch".to_string()),
                prepared: prepared.clone(),
            }],
        )
        .expect("scope");
        let assumption = symbolic_register_assumption(&prepared);
        let assumptions = r2ssa::AssumptionSet::new(vec![assumption.clone()]);

        let conditioned = condition_symbolic_scope_with_assumptions(&scope, &assumptions)
            .expect("conditioned scope");

        assert!(conditioned.assumption_conditioned);
        assert_eq!(
            conditioned.assumption_usage.applied,
            vec![assumption.clone()]
        );
        assert!(conditioned.assumption_usage.ignored.is_empty());
        assert!(conditioned.assumption_usage.conflicts.is_empty());
        assert_eq!(
            conditioned.prepared.facts().assumption_usage.applied,
            vec![assumption.clone()]
        );
        assert!(prepared.facts().assumption_usage.applied.is_empty());
        assert!(
            scope
                .root()
                .expect("scope root")
                .prepared
                .facts()
                .assumption_usage
                .applied
                .is_empty()
        );
        assert_eq!(
            conditioned
                .scope
                .root()
                .expect("conditioned scope root")
                .prepared
                .facts()
                .assumption_usage
                .applied,
            vec![assumption]
        );
    }

    #[test]
    fn engine_reports_conflicting_assumptions_as_conditioning() {
        let blocks = symbolic_register_branch_blocks(0x501800);
        let prepared = r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared");
        let scope = r2sym::PreparedFunctionScope::new(
            0x501800,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x501800),
                name: Some("sym.branch".to_string()),
                prepared: prepared.clone(),
            }],
        )
        .expect("scope");
        let assumption = conflicting_predicate_assumption(&prepared);
        let assumptions = r2ssa::AssumptionSet::new(vec![assumption.clone()]);

        let conditioned = condition_symbolic_scope_with_assumptions(&scope, &assumptions)
            .expect("conditioned scope");

        assert!(conditioned.assumption_conditioned);
        assert!(conditioned.assumption_usage.applied.is_empty());
        assert!(conditioned.assumption_usage.ignored.is_empty());
        assert_eq!(conditioned.assumption_usage.conflicts.len(), 1);
        assert_eq!(
            conditioned.assumption_usage.conflicts[0].assumption,
            assumption
        );
    }

    #[test]
    fn symbolic_summary_reports_prepared_assumption_usage() {
        let blocks = symbolic_register_branch_blocks(0x502000);
        let prepared = r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared");
        let scope = r2sym::PreparedFunctionScope::new(
            0x502000,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x502000),
                name: Some("sym.branch".to_string()),
                prepared: prepared.clone(),
            }],
        )
        .expect("scope");
        let assumption = symbolic_register_assumption(&prepared);
        let assumptions = r2ssa::AssumptionSet::new(vec![assumption.clone()]);
        let conditioned = condition_symbolic_scope_with_assumptions(&scope, &assumptions)
            .expect("conditioned scope");
        let z3_ctx = z3::Context::thread_local();
        let symbols = HashMap::new();
        let session = EngineSession::new(4);

        let response = session.symbolic_summary(EngineSymbolicSummaryRequest {
            context: EngineSymbolicContextRequest {
                z3_ctx: &z3_ctx,
                prepared: &conditioned.prepared,
                scope: Some(&conditioned.scope),
                arch: None,
                symbol_map: &symbols,
                merge_states: false,
                config_profile: EngineSymbolicConfigProfile::PathListing,
                seed: EngineSymbolicStateSeed::Scope {
                    entry_addr: 0x502000,
                },
            },
            compile_semantics: false,
        });

        assert!(response.assumption_conditioned);
        assert_eq!(response.assumption_usage.applied, vec![assumption]);
        assert!(response.assumption_usage.ignored.is_empty());
        assert!(response.assumption_usage.conflicts.is_empty());
    }

    #[test]
    fn engine_profile_snapshots_cache_metrics_with_route_decision() {
        let session = EngineSession::new(4);
        let blocks = const_return_blocks(0x403000, 0);
        let analysis =
            AnalysisCacheKey::from_parts(0x403000, "sym.profile", None, &blocks, 1, 2, "aa");
        let artifact = ArtifactCacheKey::from_hashes(analysis, 3, 4);
        let render = RenderCacheKey::from_artifact(artifact, 5, 6);

        let _ = session.cached_render_with_decision(EngineRequestKind::Decompile, Some(&render));
        let profile = session.profile(EngineProfileRequest {
            reset_after_read: true,
        });

        assert_eq!(
            profile.route_decision.kind,
            EngineProfileRouteKind::MetricsSnapshot
        );
        assert_eq!(profile.metrics.renders.misses, 1);
        assert_eq!(profile.total.misses, 1);
        assert_eq!(
            session
                .profile(EngineProfileRequest::default())
                .total
                .misses,
            0
        );
    }

    #[test]
    fn request_plan_preserves_refusal_diagnostics() {
        let comment = "/* r2dec fallback: semantic evidence unavailable */".to_string();
        let route = r2dec::SemanticRoutePlan::FallbackComment {
            comment: comment.clone(),
        };
        let decision = EngineRouteDecision {
            request: EngineRequestKind::Decompile,
            plan: select_engine_plan(EngineRequestKind::Decompile, Some(&route), None),
            route,
            route_reason: Some(comment.clone()),
            skip_runtime_type_inference: false,
            use_prepared_semantic_view: false,
            proof_coverage: r2sym::ProofCoverage::default(),
            render_permission: r2sym::RenderPermission::refuse(
                r2sym::ProofOwner::R2engine,
                comment.clone(),
            ),
            refusal: Some(comment.clone()),
        };

        let request_plan = EngineRequestPlan::decompile(decision);
        let diagnostics = request_plan.diagnostics();

        assert_eq!(request_plan.engine_plan(), EnginePlan::RefuseWithEvidence);
        assert_eq!(request_plan.cache.layer, EngineCacheLayer::Render);
        assert_eq!(diagnostics.refusal, Some(comment.clone()));
        assert_eq!(diagnostics.route_reason, Some(comment.clone()));
        assert_eq!(
            diagnostics
                .render_permission
                .as_ref()
                .map(|permission| permission.kind),
            Some(r2sym::RenderPermissionKind::Refuse)
        );
    }

    #[test]
    fn native_linear_artifact_plan_keeps_regioned_unrenderable_workers_standard_by_default() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();

        for slice_class in [
            r2sym::SliceClass::Worker,
            r2sym::SliceClass::GenericLarge,
            r2sym::SliceClass::Wrapper,
        ] {
            let artifact = native_linear_artifact(slice_class);
            assert!(matches!(
                artifact.decompile_plan(),
                r2sym::DecompilePlan::NativeLinear { .. }
            ));
            let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact));

            let route = semantic_route_plan("dbg.worker", &function_facts, &cfg_summary);
            assert!(matches!(route, r2dec::SemanticRoutePlan::Standard));
            assert_eq!(
                detached_semantic_route_plan("dbg.worker", &blocks, &function_facts),
                Some(route)
            );
        }
    }

    #[test]
    fn compact_renderable_worker_summary_can_route_to_linear_summary() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();
        let artifact = native_linear_predicated_count_artifact();
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact));

        let route = semantic_route_plan("dbg.mem_scan2", &function_facts, &cfg_summary);

        assert!(matches!(
            route,
            r2dec::SemanticRoutePlan::LinearWorker { .. }
        ));
    }

    #[test]
    fn compact_table_walk_worker_summary_can_route_to_linear_summary() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();
        let artifact = native_linear_table_walk_artifact();
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact));

        let route = semantic_route_plan("dbg.table_walk", &function_facts, &cfg_summary);

        assert!(matches!(
            route,
            r2dec::SemanticRoutePlan::LinearWorker { .. }
        ));
    }

    #[test]
    fn summary_only_scan_table_worker_routes_to_summary_islands() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();
        let artifact = summary_only_table_walk_artifact();
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact));

        let route = semantic_route_plan("dbg.table_walk", &function_facts, &cfg_summary);

        assert!(matches!(
            route,
            r2dec::SemanticRoutePlan::SummaryIslands { .. }
        ));
    }

    #[test]
    fn summary_only_exact_hash_fold_prefers_standard_native_render() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();
        let artifact = summary_only_exact_hash_fold_artifact();
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact));

        let route = semantic_route_plan("dbg.fnv_fold", &function_facts, &cfg_summary);

        assert!(matches!(route, r2dec::SemanticRoutePlan::Standard));
    }

    #[test]
    fn dense_summary_only_exact_hash_fold_still_prefers_standard_native_render() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();
        let artifact = pad_summary_only_artifact_to_dense(summary_only_exact_hash_fold_artifact());
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact));

        let route = semantic_route_plan("dbg.fnv_fold", &function_facts, &cfg_summary);

        assert!(matches!(route, r2dec::SemanticRoutePlan::Standard));
    }

    #[test]
    fn summary_only_complete_table_walk_prefers_standard_native_render() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();
        let artifact = summary_only_complete_table_walk_artifact();
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact));

        let route = semantic_route_plan("dbg.table_walk", &function_facts, &cfg_summary);

        assert!(matches!(route, r2dec::SemanticRoutePlan::Standard));
    }

    #[test]
    fn dense_summary_only_complete_table_walk_still_prefers_standard_native_render() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();
        let artifact =
            pad_summary_only_artifact_to_dense(summary_only_complete_table_walk_artifact());
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact));

        let route = semantic_route_plan("dbg.table_walk", &function_facts, &cfg_summary);

        assert!(matches!(route, r2dec::SemanticRoutePlan::Standard));
    }

    #[test]
    fn cache_lookup_decisions_report_repeated_request_reuse() {
        let session = EngineSession::new(4);
        let blocks = const_return_blocks(0x403000, 0);
        let analysis =
            AnalysisCacheKey::from_parts(0x403000, "sym.cache", None, &blocks, 1, 2, "aa");
        let artifact = ArtifactCacheKey::from_hashes(analysis, 3, 4);
        let render = RenderCacheKey::from_artifact(artifact, 5, 6);

        let disabled = session.cached_render_with_decision(EngineRequestKind::Decompile, None);
        assert_eq!(disabled.value, None);
        assert_eq!(disabled.decision.reuse, EngineCacheReuse::Disabled);

        let miss = session.cached_render_with_decision(EngineRequestKind::Decompile, Some(&render));
        assert_eq!(miss.value, None);
        assert_eq!(miss.decision.reuse, EngineCacheReuse::Miss);

        session.insert_render(render.clone(), "cached output".to_string());
        let hit = session.cached_render_with_decision(EngineRequestKind::Decompile, Some(&render));
        assert_eq!(hit.value.as_deref(), Some("cached output"));
        assert!(hit.decision.is_hit());

        let metrics = session.cache_metrics();
        assert_eq!(
            metrics.counters_for_layer(EngineCacheLayer::Render),
            CacheCounters {
                hits: 1,
                misses: 1,
                insertions: 1,
                evictions: 0,
            }
        );
        assert_eq!(
            metrics.counters_for_layer(EngineCacheLayer::MetricsSnapshot),
            metrics.total()
        );
    }

    #[test]
    fn named_summary_route_rejects_name_only_summary_worker() {
        let summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0xe0a0),
            Some("dbg.print_current_files".to_string()),
        );
        let artifact = r2sym::compile_named_native_worker_summary_artifact(&summary, true);
        let function_facts = FunctionFacts::new(FunctionTypeFacts::default(), None);

        assert!(artifact.is_none());
        assert!(!has_renderable_primary_summary_only_native_worker(
            &function_facts
        ));
        assert!(named_worker_summary_route(true, &function_facts).is_none());
    }

    #[test]
    fn route_decision_can_be_applied_to_decompiler_context() {
        let blocks = const_return_blocks(0x3000, 0);
        let prepared = r2ssa::SsaArtifact::for_decompile(&blocks, None).expect("prepared");
        let function_facts = FunctionFacts::default();
        let cfg_summary = prepared.function().cfg_risk_summary();
        let decision = decompile_route_decision(
            "sym.simple",
            &function_facts,
            Some(&prepared),
            &function_facts.types,
            &cfg_summary,
        );
        let context =
            decompiler_context_with_route_decision(r2dec::DecompilerContext::default(), &decision);

        assert_eq!(context.semantic_route, Some(decision.route));
        assert_eq!(
            context.skip_runtime_type_inference,
            Some(decision.skip_runtime_type_inference)
        );
        assert_eq!(
            context.use_prepared_semantic_view,
            Some(decision.use_prepared_semantic_view)
        );
    }
}
