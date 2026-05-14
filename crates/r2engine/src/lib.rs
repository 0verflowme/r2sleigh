//! r2engine owns cross-crate analysis orchestration.
//!
//! Fact ownership stays in the lower crates: SSA in `r2ssa`, semantic artifacts
//! in `r2sym`, type facts in `r2types`, and rendering in `r2dec`. This crate is
//! the session-level scheduler/cache boundary that decides which artifacts are
//! needed for a request and how they are reused.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Write as _};
use std::hash::{Hash, Hasher};
use std::sync::{Arc, RwLock};
use std::time::Duration;

use r2il::R2ILBlock;
use r2ssa::{CFGRiskSummary, SSAFunction, SsaArtifact};
use r2types::{
    DecompileCapabilityView, FunctionFacts, FunctionSignatureProjection, FunctionTypeFactInputs,
    FunctionTypeFacts, TypeWritebackPlan,
};
use serde::{Deserialize, Serialize};

pub const ENGINE_SCHEMA_VERSION: u32 = 1;
pub const DEFAULT_ENGINE_CACHE_LIMIT: usize = 256;
pub const SYMBOLIC_PATHS_LIMIT: usize = 32;
pub const SYMBOLIC_PATHS_CALL_FREE_MAX_STATES: usize = 16;
pub const SYMBOLIC_PATHS_CALL_FREE_MAX_DEPTH: usize = 64;
pub const SYMBOLIC_PATHS_CALL_HEAVY_MAX_STATES: usize = 8;
pub const SYMBOLIC_PATHS_CALL_HEAVY_MAX_DEPTH: usize = 32;
pub const SYMBOLIC_PATHS_TIMEOUT_MS: u64 = 500;
pub const SYMBOLIC_PATHS_SOLUTION_LIMIT: usize = 4;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EngineFunctionIdentity {
    pub function_addr: u64,
    pub canonical_name: String,
    pub display_name: String,
    pub aliases: Vec<String>,
}

impl EngineFunctionIdentity {
    pub fn new(function_addr: u64, canonical_name: &str, display_name: &str) -> Self {
        Self::with_aliases(
            function_addr,
            canonical_name,
            display_name,
            std::iter::empty::<&str>(),
        )
    }

    pub fn with_aliases<'a>(
        function_addr: u64,
        canonical_name: &str,
        display_name: &str,
        aliases: impl IntoIterator<Item = &'a str>,
    ) -> Self {
        let mut identity = Self {
            function_addr,
            canonical_name: canonical_name.to_string(),
            display_name: display_name.to_string(),
            aliases: Vec::new(),
        };
        identity.push_alias(canonical_name);
        identity.push_alias(display_name);
        for alias in aliases {
            identity.push_alias(alias);
        }
        identity
    }

    pub fn from_name(function_addr: u64, name: &str) -> Self {
        Self::new(function_addr, name, name)
    }

    pub fn push_alias(&mut self, alias: &str) {
        let alias = alias.trim();
        if alias.is_empty() {
            return;
        }
        if !self.aliases.iter().any(|existing| existing == alias) {
            self.aliases.push(alias.to_string());
        }
        let normalized = normalize_engine_route_name(alias);
        if !normalized.is_empty() && !self.aliases.iter().any(|existing| existing == &normalized) {
            self.aliases.push(normalized);
        }
    }

    pub fn name_candidates(&self) -> impl Iterator<Item = &str> {
        self.aliases.iter().map(String::as_str)
    }

    pub fn primary_name(&self) -> &str {
        if !self.display_name.trim().is_empty() {
            &self.display_name
        } else {
            &self.canonical_name
        }
    }

    pub fn summary_probe_name(&self) -> &str {
        self.aliases
            .iter()
            .find(|alias| {
                should_use_direct_named_native_worker_decompile(alias)
                    || (has_seeded_summary_family(self.function_addr, alias)
                        && !is_anonymous_engine_route_name(alias))
            })
            .or_else(|| {
                self.aliases
                    .iter()
                    .find(|alias| has_seeded_summary_family(self.function_addr, alias))
            })
            .map(String::as_str)
            .unwrap_or_else(|| self.primary_name())
    }

    pub fn has_summary_family(&self) -> bool {
        self.name_candidates()
            .any(|name| has_seeded_summary_family(self.function_addr, name))
    }

    pub fn has_program_orchestrator_family(&self) -> bool {
        self.name_candidates()
            .any(r2sym::has_program_orchestrator_summary_family)
    }
}

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
pub enum EngineRequestKind {
    Decompile,
    Types,
    SymbolicQuery,
    Profile,
    DebugFacts,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EnginePlan {
    FastLocal,
    PreparedOnly,
    BoundedType,
    SemanticSummary,
    SemanticStructured,
    ReplayValidated,
    RefuseWithEvidence,
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
        stable_fnv1a_hash("decompile-render-v1"),
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
pub struct EngineDiagnostics {
    pub plan: Option<EnginePlan>,
    pub route_reason: Option<String>,
    pub warnings: Vec<String>,
    pub refusal: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineRouteDecision {
    pub request: EngineRequestKind,
    pub plan: EnginePlan,
    pub route: r2dec::SemanticRoutePlan,
    pub route_reason: Option<String>,
    pub skip_runtime_type_inference: bool,
    pub use_prepared_semantic_view: bool,
    pub refusal: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EngineTypeRouteKind {
    FullWriteback,
    BoundedCfg,
    SemanticFallback,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineTypeRouteDecision {
    pub request: EngineRequestKind,
    pub plan: EnginePlan,
    pub kind: EngineTypeRouteKind,
    pub prefer_bounded_type_plan: bool,
    pub reason: Option<String>,
    pub apply_artifact_signature_hint: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EngineProfileRouteKind {
    MetricsSnapshot,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineProfileRouteDecision {
    pub request: EngineRequestKind,
    pub plan: EnginePlan,
    pub kind: EngineProfileRouteKind,
    pub reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineTypedRouteDecision {
    Decompile(EngineRouteDecision),
    Types(EngineTypeRouteDecision),
    Profile(EngineProfileRouteDecision),
}

impl EngineTypedRouteDecision {
    pub fn request(&self) -> EngineRequestKind {
        match self {
            Self::Decompile(decision) => decision.request,
            Self::Types(decision) => decision.request,
            Self::Profile(decision) => decision.request,
        }
    }

    pub fn plan(&self) -> EnginePlan {
        match self {
            Self::Decompile(decision) => decision.plan,
            Self::Types(decision) => decision.plan,
            Self::Profile(decision) => decision.plan,
        }
    }

    pub fn reason(&self) -> Option<String> {
        match self {
            Self::Decompile(decision) => decision.route_reason.clone(),
            Self::Types(decision) => decision.reason.clone(),
            Self::Profile(decision) => decision.reason.clone(),
        }
    }

    pub fn refusal(&self) -> Option<String> {
        match self {
            Self::Decompile(decision) => decision.refusal.clone(),
            Self::Types(_) | Self::Profile(_) => None,
        }
    }

    pub fn diagnostics(&self) -> EngineDiagnostics {
        EngineDiagnostics {
            plan: Some(self.plan()),
            route_reason: self.reason(),
            refusal: self.refusal(),
            warnings: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineRequestPlan {
    pub decision: EngineTypedRouteDecision,
    pub cache: EngineCachePlan,
}

impl EngineRequestPlan {
    pub fn new(decision: EngineTypedRouteDecision) -> Self {
        let request = decision.request();
        Self {
            decision,
            cache: EngineCachePlan::for_request(request),
        }
    }

    pub fn decompile(decision: EngineRouteDecision) -> Self {
        Self::new(EngineTypedRouteDecision::Decompile(decision))
    }

    pub fn types(decision: EngineTypeRouteDecision) -> Self {
        Self::new(EngineTypedRouteDecision::Types(decision))
    }

    pub fn profile(decision: EngineProfileRouteDecision) -> Self {
        Self::new(EngineTypedRouteDecision::Profile(decision))
    }

    pub fn request(&self) -> EngineRequestKind {
        self.decision.request()
    }

    pub fn engine_plan(&self) -> EnginePlan {
        self.decision.plan()
    }

    pub fn diagnostics(&self) -> EngineDiagnostics {
        self.decision.diagnostics()
    }
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
            .and_then(|name| r2ssa::FunctionSemanticSummary::seed_for_name(id, name))
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
}

pub struct EngineSymbolicPathsRequest<'ctx, 'a> {
    pub context: EngineSymbolicContextRequest<'ctx, 'a>,
}

pub struct EngineSymbolicPathsResponse<'ctx> {
    pub summary: r2sym::SymbolicFunctionSummary<'ctx>,
    pub explorer: r2sym::PathExplorer<'ctx>,
    pub solution_limit: usize,
    pub query_policy: r2sym::QueryExecutionPolicy,
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

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CacheCounters {
    pub hits: u64,
    pub misses: u64,
    pub insertions: u64,
    pub evictions: u64,
}

impl CacheCounters {
    pub fn total_lookups(self) -> u64 {
        self.hits + self.misses
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineSessionCacheMetrics {
    pub analysis: CacheCounters,
    pub artifacts: CacheCounters,
    pub renders: CacheCounters,
}

impl EngineSessionCacheMetrics {
    pub fn total(self) -> CacheCounters {
        CacheCounters {
            hits: self.analysis.hits + self.artifacts.hits + self.renders.hits,
            misses: self.analysis.misses + self.artifacts.misses + self.renders.misses,
            insertions: self.analysis.insertions
                + self.artifacts.insertions
                + self.renders.insertions,
            evictions: self.analysis.evictions + self.artifacts.evictions + self.renders.evictions,
        }
    }

    pub fn counters_for_layer(self, layer: EngineCacheLayer) -> CacheCounters {
        match layer {
            EngineCacheLayer::Analysis => self.analysis,
            EngineCacheLayer::Artifact => self.artifacts,
            EngineCacheLayer::Render => self.renders,
            EngineCacheLayer::MetricsSnapshot => self.total(),
        }
    }
}

pub struct SessionCache<K, V> {
    inner: RwLock<BoundedArcCache<K, V>>,
    counters: RwLock<CacheCounters>,
}

impl<K, V> SessionCache<K, V>
where
    K: Clone + Eq + Hash,
{
    pub fn new(limit: usize) -> Self {
        Self {
            inner: RwLock::new(BoundedArcCache::new(limit)),
            counters: RwLock::new(CacheCounters::default()),
        }
    }

    pub fn get_arc(&self, key: &K) -> Option<Arc<V>> {
        let value = self
            .inner
            .write()
            .expect("engine cache write lock poisoned")
            .get(key);
        let mut counters = self
            .counters
            .write()
            .expect("engine cache counters write lock poisoned");
        if value.is_some() {
            counters.hits += 1;
        } else {
            counters.misses += 1;
        }
        value
    }

    pub fn insert_arc(&self, key: K, value: Arc<V>) -> Arc<V> {
        let result = self
            .inner
            .write()
            .expect("engine cache write lock poisoned")
            .insert(key, value);
        let mut counters = self
            .counters
            .write()
            .expect("engine cache counters write lock poisoned");
        counters.insertions += 1;
        counters.evictions += result.evicted_count;
        result.value
    }

    pub fn insert(&self, key: K, value: V) -> Arc<V> {
        self.insert_arc(key, Arc::new(value))
    }

    pub fn retain<F>(&self, keep: F) -> bool
    where
        F: FnMut(&K, &Arc<V>) -> bool,
    {
        self.inner
            .write()
            .expect("engine cache write lock poisoned")
            .retain(keep)
    }

    pub fn counters(&self) -> CacheCounters {
        *self
            .counters
            .read()
            .expect("engine cache counters read lock poisoned")
    }

    pub fn reset_counters(&self) {
        *self
            .counters
            .write()
            .expect("engine cache counters write lock poisoned") = CacheCounters::default();
    }

    pub fn len(&self) -> usize {
        self.inner
            .read()
            .expect("engine cache read lock poisoned")
            .len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<K, V> SessionCache<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    pub fn get_cloned(&self, key: &K) -> Option<V> {
        self.get_arc(key).map(|value| (*value).clone())
    }

    pub fn insert_cloned(&self, key: K, value: V) -> V {
        self.insert(key, value).as_ref().clone()
    }
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

        if cached.is_none() {
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
        if let Some(signature) = decompile_type_override(&identity, &analysis_request, &artifact)
            .and_then(|facts| facts.merged_signature)
        {
            artifact.function_facts.types.merged_signature = Some(signature);
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
        let planning_time = started.elapsed();
        if matches!(decision.route, r2dec::SemanticRoutePlan::Standard)
            && request.fallback_comment.is_none()
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
            let type_facts = type_facts_with_summary_projection_for_candidates(
                type_seed,
                request.display_name,
                identity.name_candidates(),
                &arch_name,
                request.ptr_bits,
                &semantic_artifact,
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
            .filter(|_| has_renderable_primary_summary_only_native_worker(&function_facts))
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
        if !identity
            .name_candidates()
            .any(should_use_direct_named_native_worker_decompile)
        {
            return None;
        }

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

        self.decompile_summary(EngineSummaryDecompileRequest {
            function_name: identity.primary_name().to_string(),
            cfg_summary,
            function_facts: projection.function_facts,
            named_worker_guarded: true,
            config: request.config,
            render_cache_key: None,
            fallback_comment: None,
        })
    }

    pub fn symbolic_summary<'ctx>(
        &self,
        request: EngineSymbolicSummaryRequest<'ctx, '_>,
    ) -> EngineSymbolicSummaryResponse<'ctx> {
        let context = request.context;
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
        }
    }

    pub fn symbolic_paths<'ctx>(
        &self,
        request: EngineSymbolicPathsRequest<'ctx, '_>,
    ) -> EngineSymbolicPathsResponse<'ctx> {
        let context = request.context;
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

    let context = r2dec::DecompilerContext::from_function_facts(
        request.function_facts.clone(),
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

    request.fallback_comment.clone().unwrap_or_else(|| {
        format!(
            "/* r2dec fallback: skipped decompilation for {} (empty output) */",
            request.function_name
        )
    })
}

fn decompile_type_override(
    identity: &EngineFunctionIdentity,
    request: &EngineAnalyzeRequest,
    artifact: &EngineAnalysisArtifact,
) -> Option<FunctionTypeFacts> {
    let (arch_name, _, _) = r2dec::DecompilerConfig::for_arch(request.arch.as_ref());
    native_worker_type_projection_for_identity(
        identity,
        &arch_name,
        request.ptr_bits,
        &request.parsed_context,
        true,
    )
    .map(|projection| projection.function_facts.types)
    .or_else(|| {
        let facts = r2types::inferred_signature_to_function_type_facts(
            &artifact.writeback_plan.signature,
            request.ptr_bits,
        );
        facts.merged_signature.is_some().then_some(facts)
    })
    .or_else(|| {
        let facts = r2types::function_type_facts_from_parsed_context(
            &request.function_name,
            &request.parsed_context,
        );
        facts.merged_signature.is_some().then_some(facts)
    })
}

fn refused_decompile_response(
    function_name: &str,
    reason: &str,
    planning_time: Duration,
) -> EngineDecompileResponse {
    let output = r2dec::artifact_guard_fallback_comment(function_name, reason);
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
        stable_fnv1a_hash(&(
            "semantic-metadata-enabled",
            request.semantic_metadata_enabled,
        )),
        stable_fnv1a_hash("function-analysis-artifact-v1"),
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
            if let Some(summary) = r2ssa::FunctionSemanticSummary::seed_for_name(function.id, name)
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
    let (arch_name, _, decompiler_cfg) = r2dec::DecompilerConfig::for_arch(request.arch.as_ref());
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
    let local_field_accesses =
        local_field_accesses_to_writeback(r2dec::infer_local_struct_field_accesses(
            &semantic_analysis.pattern_ssa_func,
            &decompiler_cfg,
        ));
    let local_struct_semantics_required = !local_field_accesses.is_empty()
        && parsed_context_has_layout_hints(&request.parsed_context);
    let root_summary = interproc_summary_set.as_ref().and_then(|summary_set| {
        summary_set
            .root
            .and_then(|root| summary_set.summaries.get(&root))
    });
    let semantic_artifact = request.precomputed_semantic_artifact.clone().or_else(|| {
        if matches!(request.semantic_mode, EngineSemanticMode::Full) {
            return Some(compile_semantic_artifact_for_analysis(
                &semantic_analysis.ssa_func,
                request.function_addr,
                &request.function_name,
                request.symbolic_scope.as_ref(),
                request.arch.as_ref(),
                root_summary,
            ));
        }
        local_struct_semantics_required.then(|| {
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
    Some(EngineAnalysisArtifact {
        ssa_func: semantic_analysis.ssa_func,
        pattern_ssa_func: semantic_analysis.pattern_ssa_func,
        function_facts,
        writeback_plan: writeback.plan,
    })
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
    if let Some(summary) = summary_seed
        && let Some(artifact) = r2sym::compile_summary_dense_worker_artifact_from_interproc_summary(
            ssa_func,
            symbolic_scope,
            summary,
        )
    {
        return artifact;
    }
    if should_probe_native_worker_summary_before_full_semantics(ssa_func, summary_seed)
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
    _ssa_func: &SsaArtifact,
    root_summary: Option<&r2ssa::FunctionSemanticSummary>,
) -> bool {
    root_summary
        .and_then(|summary| summary.name.as_deref())
        .is_some_and(should_use_direct_named_native_worker_decompile)
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

fn local_field_accesses_to_writeback(
    accesses: Vec<r2dec::LocalStructFieldAccess>,
) -> Vec<r2types::LocalFieldAccessFact> {
    accesses
        .into_iter()
        .map(|access| r2types::LocalFieldAccessFact {
            slot: access.arg_index,
            field_offset: access.field_offset,
            field_name: format!("f_{:x}", access.field_offset),
            field_type: Some(r2types::size_to_type(access.access_size)),
        })
        .collect()
}

fn parsed_context_has_layout_hints(parsed_context: &r2types::ParsedExternalContext) -> bool {
    parsed_context
        .current_signature
        .as_ref()
        .into_iter()
        .chain(parsed_context.merged_signature.as_ref())
        .any(|signature| {
            signature
                .ret_type
                .as_ref()
                .is_some_and(type_like_has_layout_hint)
                || signature
                    .params
                    .iter()
                    .filter_map(|param| param.ty.as_ref())
                    .any(type_like_has_layout_hint)
        })
        || parsed_context
            .register_params
            .iter()
            .filter_map(|param| param.ty.as_ref())
            .any(type_like_has_layout_hint)
        || parsed_context
            .stack_slots
            .values()
            .filter_map(|slot| slot.ty.as_ref())
            .any(type_like_has_layout_hint)
}

fn type_like_has_layout_hint(ty: &r2types::CTypeLike) -> bool {
    match ty {
        r2types::CTypeLike::Pointer(inner) | r2types::CTypeLike::Array(inner, _) => {
            type_like_has_layout_hint(inner)
        }
        r2types::CTypeLike::Struct(_) | r2types::CTypeLike::Union(_) => true,
        r2types::CTypeLike::Typedef(name) => {
            let normalized = name.trim().to_ascii_lowercase();
            !matches!(
                normalized.as_str(),
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
        _ => false,
    }
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

fn raw_cfg_risk_summary_for_preprobe(blocks: &[R2ILBlock]) -> CFGRiskSummary {
    let block_addrs = blocks
        .iter()
        .map(|block| block.addr)
        .collect::<BTreeSet<_>>();
    let mut loop_headers = BTreeSet::new();
    let mut back_edge_count = 0usize;
    let mut switch_block_count = 0usize;
    let mut max_switch_cases = 0usize;

    for block in blocks {
        if let Some(switch_info) = block.switch_info.as_ref() {
            switch_block_count += 1;
            max_switch_cases = max_switch_cases
                .max(switch_info.cases.len() + usize::from(switch_info.default_target.is_some()));
            for target in switch_info
                .cases
                .iter()
                .map(|case| case.target)
                .chain(switch_info.default_target)
            {
                if target <= block.addr && block_addrs.contains(&target) {
                    back_edge_count += 1;
                    loop_headers.insert(target);
                }
            }
        }

        for target in raw_block_successors_for_preprobe(block) {
            if target <= block.addr && block_addrs.contains(&target) {
                back_edge_count += 1;
                loop_headers.insert(target);
            }
        }
    }

    CFGRiskSummary {
        block_count: blocks.len(),
        loop_count: loop_headers.len(),
        back_edge_count,
        switch_block_count,
        max_switch_cases,
    }
}

fn raw_block_successors_for_preprobe(block: &R2ILBlock) -> Vec<u64> {
    let fallthrough = block.addr.saturating_add(block.size as u64);
    for op in block.ops.iter().rev() {
        match op {
            r2il::R2ILOp::Branch { target } => {
                return raw_const_addr_for_preprobe(target).into_iter().collect();
            }
            r2il::R2ILOp::CBranch { target, .. } => {
                let mut successors = Vec::with_capacity(2);
                if let Some(target) = raw_const_addr_for_preprobe(target) {
                    successors.push(target);
                }
                successors.push(fallthrough);
                return successors;
            }
            r2il::R2ILOp::Call { .. } | r2il::R2ILOp::CallInd { .. } => {
                return vec![fallthrough];
            }
            r2il::R2ILOp::BranchInd { .. } | r2il::R2ILOp::Return { .. } => {
                return Vec::new();
            }
            _ => {}
        }
    }
    vec![fallthrough]
}

fn raw_const_addr_for_preprobe(varnode: &r2il::Varnode) -> Option<u64> {
    matches!(varnode.space, r2il::SpaceId::Const | r2il::SpaceId::Ram).then_some(varnode.offset)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecompileProbeDecision {
    pub op_count: usize,
    pub cfg_guard_reason: Option<String>,
    pub display_summary_family: bool,
    pub canonical_summary_family: bool,
    pub display_program_orchestrator_family: bool,
    pub canonical_program_orchestrator_family: bool,
    pub program_orchestrator_guarded: bool,
    pub named_worker_guarded: bool,
    pub summary_probe_name: String,
    pub summary_probe_needed: bool,
    pub summary_probe_skipped_large_cfg: bool,
    pub block_guarded: bool,
}

pub fn decompile_probe_decision(
    blocks: &[R2ILBlock],
    function_addr: u64,
    canonical_name: &str,
    display_name: &str,
) -> DecompileProbeDecision {
    let identity = EngineFunctionIdentity::new(function_addr, canonical_name, display_name);
    decompile_probe_decision_for_identity(blocks, &identity)
}

pub fn decompile_probe_decision_for_identity(
    blocks: &[R2ILBlock],
    identity: &EngineFunctionIdentity,
) -> DecompileProbeDecision {
    let cfg_guard_reason = cfg_guard_reason(blocks);
    let op_count = blocks.iter().map(|block| block.ops.len()).sum::<usize>();
    let display_summary_family =
        has_seeded_summary_family(identity.function_addr, &identity.display_name);
    let canonical_summary_family =
        has_seeded_summary_family(identity.function_addr, &identity.canonical_name);
    let display_program_orchestrator_family =
        r2sym::has_program_orchestrator_summary_family(&identity.display_name);
    let canonical_program_orchestrator_family =
        r2sym::has_program_orchestrator_summary_family(&identity.canonical_name);
    let summary_family =
        display_summary_family || canonical_summary_family || identity.has_summary_family();
    let program_orchestrator_family = display_program_orchestrator_family
        || canonical_program_orchestrator_family
        || identity.has_program_orchestrator_family();
    let program_orchestrator_guarded = program_orchestrator_family
        && should_guard_program_orchestrator_decompile(blocks.len(), op_count);
    let summary_probe_name = identity.summary_probe_name().to_string();
    let prefer_full_named_worker = identity
        .name_candidates()
        .any(should_prefer_full_decompile_for_named_worker);
    let skipped_large_cfg_guarded = !prefer_full_named_worker
        && (cfg_guard_reason.is_some() || blocks.len() > 200 || op_count > 512);
    let direct_named_worker_guarded = identity
        .name_candidates()
        .any(should_use_direct_named_native_worker_decompile);
    let named_worker_guarded = summary_family
        && (direct_named_worker_guarded
            || skipped_large_cfg_guarded
            || program_orchestrator_guarded)
        && (!program_orchestrator_family || program_orchestrator_guarded);
    let block_guarded = named_worker_guarded || skipped_large_cfg_guarded;
    let summary_probe_needed = block_guarded || cfg_guard_reason.is_some();

    DecompileProbeDecision {
        op_count,
        cfg_guard_reason,
        display_summary_family,
        canonical_summary_family,
        display_program_orchestrator_family,
        canonical_program_orchestrator_family,
        program_orchestrator_guarded,
        named_worker_guarded,
        summary_probe_name,
        summary_probe_needed,
        summary_probe_skipped_large_cfg: skipped_large_cfg_guarded,
        block_guarded,
    }
}

fn has_seeded_summary_family(function_addr: u64, name: &str) -> bool {
    r2ssa::FunctionSemanticSummary::seed_for_name(r2ssa::InterprocFunctionId(function_addr), name)
        .is_some()
        || r2sym::has_native_worker_summary_family(name)
}

pub fn should_use_direct_named_native_worker_decompile(function_name: &str) -> bool {
    let name = normalize_engine_route_name(function_name);
    if is_direct_fileinfo_sort_comparator(&name) || is_direct_allocation_wrapper(&name) {
        return true;
    }
    matches!(
        name.as_str(),
        "alloc_ibuf"
            | "alloc_obuf"
            | "check_tuning"
            | "close_stream"
            | "compare"
            | "create_hard_link"
            | "cycle_check"
            | "__do_global_dtors_aux"
            | "deregister_tm_clones"
            | "entry.fini0"
            | "entry0"
            | "exit_cleanup"
            | "file_prefixlen"
            | "filename_unescape"
            | "flush_stdout"
            | "fopen_safer"
            | "format_user_or_group"
            | "getmonth"
            | "has_xattr"
            | "hwcap_allowed"
            | "imaxtostr"
            | "init_node"
            | "_init"
            | "key_to_opts"
            | "localtime_rz"
            | "maybe_close_stdout"
            | "memcoll"
            | "mergefiles"
            | "num_processors_via_affinity_mask"
            | "operand_matches"
            | "process_signals"
            | "print_stats"
            | "quotearg_free"
            | "reap"
            | "record_file"
            | "register_tm_clones"
            | "rpl_fflush"
            | "rpl_fseeko"
            | "rpl_nanosleep"
            | "rpl_obstack_allocated_p"
            | "rpl_obstack_free"
            | "save_token"
            | "set_file_security_ctx"
            | "tzalloc"
            | "umaxtostr"
            | "xinmalloc"
            | "xget_version"
            | "xmemcoll"
            | "xnmalloc"
            | "xstrxfrm"
            | "xstrtol_fatal"
            | "xnrealloc"
    )
}

fn is_direct_fileinfo_sort_comparator(name: &str) -> bool {
    name.starts_with("xstrcoll_df_")
        || name.starts_with("rev_xstrcoll_df_")
        || name.starts_with("strcmp_df_")
        || name.starts_with("rev_strcmp_df_")
}

fn is_direct_allocation_wrapper(name: &str) -> bool {
    matches!(
        name,
        "xmalloc"
            | "ximalloc"
            | "xcharalloc"
            | "xrealloc"
            | "xirealloc"
            | "xreallocarray"
            | "rpl_reallocarray"
            | "xnrealloc"
            | "xnmalloc"
            | "xinmalloc"
            | "x2realloc"
            | "x2nrealloc"
            | "xpalloc"
            | "xzalloc"
            | "xizalloc"
            | "xcalloc"
            | "xicalloc"
            | "xmemdup"
            | "ximemdup"
            | "ximemdup0"
            | "xstrdup"
            | "xalloc_die"
    )
}

fn should_prefer_full_decompile_for_named_worker(function_name: &str) -> bool {
    matches!(
        normalize_engine_route_name(function_name).as_str(),
        "diagnose"
    )
}

pub fn should_use_direct_named_native_worker_type_projection(function_name: &str) -> bool {
    should_use_direct_named_native_worker_decompile(function_name)
        || r2sym::has_program_orchestrator_summary_family(function_name)
        || (r2sym::has_native_worker_summary_family(function_name)
            && r2types::signature_hint_for_name_candidates([function_name], 0).is_some())
}

fn normalize_engine_route_name(name: &str) -> String {
    let mut name = name.trim();
    for prefix in ["dbg.", "sym.", "fcn."] {
        if let Some(stripped) = name.strip_prefix(prefix) {
            name = stripped;
            break;
        }
    }
    for marker in [".isra.", ".constprop.", ".part.", ".llvm."] {
        if let Some((prefix, suffix)) = name.rsplit_once(marker)
            && !prefix.is_empty()
            && !suffix.is_empty()
            && suffix.bytes().all(|byte| byte.is_ascii_digit())
        {
            return prefix.to_string();
        }
    }
    name.to_string()
}

fn is_anonymous_engine_route_name(name: &str) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    let base = normalized
        .strip_prefix("sym.")
        .or_else(|| normalized.strip_prefix("dbg."))
        .unwrap_or(&normalized);
    base.starts_with("fcn.")
        || base.starts_with("fcn_")
        || base.starts_with("sub.")
        || base.starts_with("sub_")
}

pub fn should_guard_program_orchestrator_decompile(block_count: usize, op_count: usize) -> bool {
    block_count > 4 || op_count > 96
}

pub fn semantic_route_from_artifact_plan(
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<r2dec::SemanticRoutePlan> {
    match semantic_artifact.decompile_plan() {
        r2sym::DecompilePlan::NativeLinear { reason }
            if native_linear_artifact_plan_allows_summary_route(semantic_artifact) =>
        {
            Some(r2dec::SemanticRoutePlan::LinearWorker { reason })
        }
        r2sym::DecompilePlan::NativeSummaryIslands { reason } => {
            Some(r2dec::SemanticRoutePlan::SummaryIslands { reason })
        }
        r2sym::DecompilePlan::VmSummaryOnly { reason } => {
            Some(r2dec::SemanticRoutePlan::VmSummary { reason })
        }
        _ => None,
    }
}

fn native_linear_artifact_plan_allows_summary_route(
    semantic_artifact: &r2sym::SemanticArtifact,
) -> bool {
    if semantic_artifact.granularity != r2sym::ArtifactGranularity::SummaryOnly
        && !semantic_artifact.diagnostics.skipped_large_cfg
    {
        return false;
    }
    let Some(native) = semantic_artifact.native_body() else {
        return false;
    };
    let summary_count =
        native.summary.region_summaries.len() + native.summary.worker_summaries.len();
    let has_specific_summary = native.has_memory_read_write_summary_pair()
        || native.summary.worker_summaries.iter().any(|summary| {
            !matches!(
                summary.kind,
                r2sym::NativeWorkerSummaryKind::MemoryRead
                    | r2sym::NativeWorkerSummaryKind::MemoryWrite
                    | r2sym::NativeWorkerSummaryKind::Unknown
            )
        });
    summary_count >= 8
        && has_specific_summary
        && matches!(
            semantic_artifact.slice_class(),
            Some(
                r2sym::SliceClass::Worker
                    | r2sym::SliceClass::GenericLarge
                    | r2sym::SliceClass::Wrapper
            )
        )
}

pub fn has_primary_summary_only_native_worker(semantic_artifact: &r2sym::SemanticArtifact) -> bool {
    semantic_artifact.granularity == r2sym::ArtifactGranularity::SummaryOnly
        && semantic_artifact
            .native_body()
            .is_some_and(|native| native.has_primary_summary_islands())
}

pub fn has_renderable_primary_summary_only_native_worker(function_facts: &FunctionFacts) -> bool {
    function_facts
        .semantic_artifact()
        .is_some_and(has_primary_summary_only_native_worker)
}

pub fn named_worker_summary_route(
    named_worker_guarded: bool,
    function_facts: &FunctionFacts,
) -> Option<r2dec::SemanticRoutePlan> {
    (named_worker_guarded && has_renderable_primary_summary_only_native_worker(function_facts))
        .then(|| r2dec::SemanticRoutePlan::SummaryIslands {
            reason: "named native-worker summary projection".to_string(),
        })
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
    mut type_facts: FunctionTypeFacts,
    function_name: &str,
    name_candidates: impl IntoIterator<Item = &'a str>,
    arch_name: &str,
    ptr_bits: u32,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> FunctionTypeFacts {
    let signature_param_count = type_facts
        .merged_signature
        .as_ref()
        .map(|signature| signature.params.len())
        .unwrap_or_default();
    let current_param_count = signature_param_count.max(type_facts.register_params.len());
    let mut candidates = Vec::new();
    for candidate in name_candidates {
        let candidate = candidate.trim();
        if !candidate.is_empty() && !candidates.iter().any(|existing| existing == &candidate) {
            candidates.push(candidate);
        }
    }
    if candidates.is_empty() {
        candidates.push(function_name);
    }
    let role_identity = semantic_artifact
        .native_body()
        .and_then(|native| native.summary.role_identity.as_ref());
    if let Some(role_identity) = role_identity {
        for candidate in std::iter::once(role_identity.role_name.as_str())
            .chain(role_identity.source_names.iter().map(String::as_str))
        {
            let candidate = candidate.trim();
            if !candidate.is_empty() && !candidates.iter().any(|existing| existing == &candidate) {
                candidates.push(candidate);
            }
        }
    }
    let name_signature = r2types::signature_hint_for_name_candidates(
        candidates.iter().copied(),
        current_param_count,
    );
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
    let projected_signature = if let Some(mut signature) = name_signature.clone() {
        if signature.ret_type.is_none()
            && let Some(fallback_signature) = fallback_signature.as_ref()
        {
            signature.ret_type = fallback_signature.ret_type.clone();
        }
        Some(signature)
    } else {
        fallback_signature
    };
    let Some(projected_signature) = projected_signature else {
        return type_facts;
    };
    let projection = if name_signature.is_some() {
        FunctionSignatureProjection::strong_summary(projected_signature).with_exact_arity(true)
    } else {
        FunctionSignatureProjection::weak_summary_kind(projected_signature)
            .with_return_confidence(fallback_plan.signature.confidence)
            .with_default_param_confidence(fallback_plan.signature.confidence)
    };
    let _ = type_facts.apply_signature_projection(function_name, projection, ptr_bits);
    type_facts
}

#[derive(Debug, Clone)]
pub struct NativeWorkerTypeProjection {
    pub function_facts: FunctionFacts,
    pub semantic_artifact: r2sym::SemanticArtifact,
    pub name_owned_signature: bool,
}

pub fn native_worker_summary_seed(
    function_addr: u64,
    function_name: &str,
) -> Option<r2ssa::FunctionSemanticSummary> {
    r2ssa::FunctionSemanticSummary::seed_for_name(
        r2ssa::InterprocFunctionId(function_addr),
        function_name,
    )
    .or_else(|| {
        r2sym::has_native_worker_summary_family(function_name).then(|| {
            r2ssa::FunctionSemanticSummary::unknown(
                r2ssa::InterprocFunctionId(function_addr),
                Some(function_name.to_string()),
            )
        })
    })
}

pub fn native_worker_summary_artifact(
    blocks: &[R2ILBlock],
    function_name: &str,
    arch: Option<&r2il::ArchSpec>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    skipped_large_cfg: bool,
) -> Option<r2sym::SemanticArtifact> {
    let ssa_func = r2ssa::SsaArtifact::for_decompile(blocks, arch)?.with_name(function_name);
    if r2sym::has_strong_vm_evidence(&ssa_func) {
        return None;
    }
    let summary_id =
        r2ssa::InterprocFunctionId(blocks.first().map(|block| block.addr).unwrap_or_default());
    let root_summary =
        native_worker_summary_seed(summary_id.0, function_name).unwrap_or_else(|| {
            r2ssa::FunctionSemanticSummary::unknown(summary_id, Some(function_name.to_string()))
        });
    if let Some(artifact) =
        r2sym::compile_named_native_worker_summary_artifact(&root_summary, skipped_large_cfg)
    {
        return Some(artifact);
    }
    r2sym::compile_native_worker_summary_artifact(
        &ssa_func,
        symbolic_scope,
        Some(&root_summary),
        skipped_large_cfg,
    )
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
    FunctionTypeFacts::builder(FunctionTypeFactInputs {
        merged_signature: parsed_context
            .merged_signature
            .clone()
            .or_else(|| parsed_context.current_signature.clone()),
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
    let summary = native_worker_summary_seed(identity.function_addr, summary_name)?;
    let semantic_artifact =
        r2sym::compile_named_native_worker_summary_artifact(&summary, skipped_large_cfg)?;
    let type_facts = type_facts_from_parsed_context(parsed_context);
    let current_param_count = type_facts
        .merged_signature
        .as_ref()
        .map(|signature| signature.params.len())
        .unwrap_or_default();
    let name_owned_signature = r2types::signature_hint_for_name_candidates(
        identity.name_candidates(),
        current_param_count,
    )
    .is_some();
    let type_facts = type_facts_with_summary_projection_for_candidates(
        type_facts,
        identity.primary_name(),
        identity.name_candidates(),
        arch_name,
        ptr_bits,
        &semantic_artifact,
    );
    let function_facts = FunctionFacts::new(type_facts, Some(semantic_artifact.clone()))
        .with_assumptions(parsed_context.assumptions.clone());
    Some(NativeWorkerTypeProjection {
        function_facts,
        semantic_artifact,
        name_owned_signature,
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
        let type_facts = type_facts_with_summary_projection_for_candidates(
            type_seed,
            request.display_name,
            identity.name_candidates(),
            &arch_name,
            request.ptr_bits,
            &semantic_artifact,
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
    matches!(
        artifact.granularity,
        r2sym::ArtifactGranularity::SummaryOnly
    ) && artifact
        .native_body()
        .is_some_and(r2sym::NativeArtifactBody::has_summary_islands)
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

pub fn select_engine_plan(
    request: EngineRequestKind,
    route: Option<&r2dec::SemanticRoutePlan>,
    function_facts: Option<&FunctionFacts>,
) -> EnginePlan {
    match request {
        EngineRequestKind::Types => {
            if function_facts
                .and_then(FunctionFacts::semantic_artifact)
                .is_some()
            {
                EnginePlan::SemanticSummary
            } else {
                EnginePlan::PreparedOnly
            }
        }
        EngineRequestKind::SymbolicQuery => EnginePlan::SemanticStructured,
        EngineRequestKind::Profile | EngineRequestKind::DebugFacts => EnginePlan::PreparedOnly,
        EngineRequestKind::Decompile => match route {
            Some(r2dec::SemanticRoutePlan::Standard) | None => EnginePlan::FastLocal,
            Some(r2dec::SemanticRoutePlan::FallbackComment { .. }) => {
                EnginePlan::RefuseWithEvidence
            }
            Some(r2dec::SemanticRoutePlan::VmSummary { .. })
            | Some(r2dec::SemanticRoutePlan::SummaryIslands { .. })
            | Some(r2dec::SemanticRoutePlan::LinearWorker { .. }) => EnginePlan::SemanticSummary,
            Some(r2dec::SemanticRoutePlan::StructuredWorker { .. }) => {
                EnginePlan::SemanticStructured
            }
        },
    }
}

pub fn plan_decompile_request(
    func_name: &str,
    function_facts: &FunctionFacts,
    prepared: Option<&SsaArtifact>,
    type_facts: &FunctionTypeFacts,
    cfg_summary: &CFGRiskSummary,
) -> EngineRequestPlan {
    EngineRequestPlan::decompile(decompile_route_decision(
        func_name,
        function_facts,
        prepared,
        type_facts,
        cfg_summary,
    ))
}

pub fn plan_type_request(
    function_facts: &FunctionFacts,
    cfg_summary: &CFGRiskSummary,
    caller_prefers_bounded_type_plan: bool,
) -> EngineRequestPlan {
    EngineRequestPlan::types(type_route_decision(
        function_facts,
        cfg_summary,
        caller_prefers_bounded_type_plan,
    ))
}

pub fn profile_route_decision() -> EngineProfileRouteDecision {
    EngineProfileRouteDecision {
        request: EngineRequestKind::Profile,
        plan: select_engine_plan(EngineRequestKind::Profile, None, None),
        kind: EngineProfileRouteKind::MetricsSnapshot,
        reason: Some("session cache metrics snapshot".to_string()),
    }
}

pub fn plan_profile_request() -> EngineRequestPlan {
    EngineRequestPlan::profile(profile_route_decision())
}

pub fn semantic_route_plan(
    func_name: &str,
    function_facts: &FunctionFacts,
    cfg_summary: &CFGRiskSummary,
) -> r2dec::SemanticRoutePlan {
    if let Some(reason) = preferred_vm_summary_reason(function_facts) {
        return r2dec::SemanticRoutePlan::VmSummary { reason };
    }
    if let Some(comment) = preferred_semantic_fallback_comment(func_name, function_facts) {
        return r2dec::SemanticRoutePlan::FallbackComment { comment };
    }
    if let Some(reason) = preferred_semantic_summary_islands_reason(function_facts, cfg_summary) {
        return r2dec::SemanticRoutePlan::SummaryIslands { reason };
    }
    if let Some(reason) =
        preferred_semantic_structuring_reason(func_name, function_facts, cfg_summary)
    {
        return r2dec::SemanticRoutePlan::StructuredWorker { reason };
    }
    if let Some(reason) =
        preferred_semantic_linearization_reason(func_name, function_facts, cfg_summary)
    {
        return r2dec::SemanticRoutePlan::LinearWorker { reason };
    }
    if let Some(route) = function_facts
        .semantic_artifact()
        .and_then(semantic_route_from_artifact_plan)
    {
        return route;
    }
    r2dec::SemanticRoutePlan::Standard
}

pub fn decompile_route_decision(
    func_name: &str,
    function_facts: &FunctionFacts,
    prepared: Option<&SsaArtifact>,
    type_facts: &FunctionTypeFacts,
    cfg_summary: &CFGRiskSummary,
) -> EngineRouteDecision {
    let route = semantic_route_plan(func_name, function_facts, cfg_summary);
    let plan = select_engine_plan(
        EngineRequestKind::Decompile,
        Some(&route),
        Some(function_facts),
    );
    let route_reason = semantic_route_reason(&route);
    let refusal = match &route {
        r2dec::SemanticRoutePlan::FallbackComment { comment } => Some(comment.clone()),
        _ => None,
    };
    EngineRouteDecision {
        request: EngineRequestKind::Decompile,
        plan,
        skip_runtime_type_inference: should_skip_runtime_type_inference(
            prepared,
            type_facts,
            function_facts,
        ),
        use_prepared_semantic_view: should_use_prepared_semantic_view(prepared, function_facts),
        route,
        route_reason,
        refusal,
    }
}

pub fn decompiler_context_with_route_decision(
    context: r2dec::DecompilerContext,
    decision: &EngineRouteDecision,
) -> r2dec::DecompilerContext {
    context
        .with_semantic_route(Some(decision.route.clone()))
        .with_runtime_type_inference_policy(Some(decision.skip_runtime_type_inference))
        .with_prepared_semantic_view_policy(Some(decision.use_prepared_semantic_view))
}

pub fn semantic_route_reason(route: &r2dec::SemanticRoutePlan) -> Option<String> {
    match route {
        r2dec::SemanticRoutePlan::StructuredWorker { reason }
        | r2dec::SemanticRoutePlan::SummaryIslands { reason }
        | r2dec::SemanticRoutePlan::LinearWorker { reason }
        | r2dec::SemanticRoutePlan::VmSummary { reason } => Some(reason.clone()),
        r2dec::SemanticRoutePlan::FallbackComment { comment } => Some(comment.clone()),
        r2dec::SemanticRoutePlan::Standard => None,
    }
}

pub fn detached_semantic_route_plan(
    func_name: &str,
    blocks: &[R2ILBlock],
    function_facts: &FunctionFacts,
) -> Option<r2dec::SemanticRoutePlan> {
    let ssa_func = SSAFunction::from_blocks_raw_no_arch(blocks)?;
    Some(semantic_route_plan(
        func_name,
        function_facts,
        &ssa_func.cfg_risk_summary(),
    ))
}

pub fn detached_semantic_linearization_reason(
    func_name: &str,
    blocks: &[R2ILBlock],
    function_facts: &FunctionFacts,
) -> Option<String> {
    match detached_semantic_route_plan(func_name, blocks, function_facts)? {
        r2dec::SemanticRoutePlan::LinearWorker { reason }
        | r2dec::SemanticRoutePlan::SummaryIslands { reason } => Some(reason),
        _ => None,
    }
}

pub fn cfg_guard_reason(blocks: &[R2ILBlock]) -> Option<String> {
    let ssa_func = SSAFunction::from_blocks_raw_no_arch(blocks)?;
    cfg_guard_reason_from_summary(&ssa_func.cfg_risk_summary())
}

pub fn cfg_guard_reason_from_summary(summary: &CFGRiskSummary) -> Option<String> {
    if summary.loop_count > 8 || summary.back_edge_count > 16 {
        return Some(format!(
            "complex loop graph (loops={}, back_edges={})",
            summary.loop_count, summary.back_edge_count
        ));
    }

    if summary.loop_count > 0 && summary.block_count >= 32 && summary.max_switch_cases >= 32 {
        return Some(format!(
            "dense switch in looped CFG (blocks={}, loops={}, max_switch_cases={})",
            summary.block_count, summary.loop_count, summary.max_switch_cases
        ));
    }

    if summary.loop_count > 4 && summary.block_count >= 96 && summary.max_switch_cases >= 32 {
        return Some(format!(
            "large dense switch in looped CFG (blocks={}, loops={}, max_switch_cases={})",
            summary.block_count, summary.loop_count, summary.max_switch_cases
        ));
    }

    None
}

pub fn type_cfg_prefers_bounded_plan(summary: &CFGRiskSummary) -> bool {
    if cfg_guard_reason_from_summary(summary).is_some() {
        return true;
    }
    summary.block_count >= 200
        || (summary.block_count >= 96
            && (summary.loop_count > 0
                || summary.back_edge_count > 0
                || summary.max_switch_cases >= 32))
}

pub fn type_cfg_forces_bounded_plan(summary: &CFGRiskSummary) -> bool {
    cfg_guard_reason_from_summary(summary).is_some()
}

pub fn type_cfg_allows_semantic_plan(summary: &CFGRiskSummary) -> bool {
    summary.block_count <= 96 && summary.loop_count <= 4 && summary.back_edge_count <= 8
}

pub fn type_cfg_bounded_reason(summary: &CFGRiskSummary) -> String {
    cfg_guard_reason_from_summary(summary).unwrap_or_else(|| {
        format!(
            "bounded type plan for large CFG (blocks={}, loops={}, back_edges={}, max_switch_cases={})",
            summary.block_count, summary.loop_count, summary.back_edge_count, summary.max_switch_cases
        )
    })
}

pub fn semantic_or_cfg_prefers_bounded_type_plan(
    artifact: &r2sym::SemanticArtifact,
    cfg_summary: &CFGRiskSummary,
) -> bool {
    if r2types::semantic_artifact_prefers_bounded_type_plan(artifact) {
        return true;
    }
    type_cfg_prefers_bounded_plan(cfg_summary)
        && !type_cfg_allows_semantic_plan(cfg_summary)
        && artifact.type_plan().allows_native_augmentation()
        && matches!(
            artifact.slice_class(),
            Some(r2sym::SliceClass::Worker | r2sym::SliceClass::GenericLarge)
        )
}

pub fn semantic_artifact_needs_fallback_type_payload(
    artifact: &r2sym::SemanticArtifact,
    cfg_summary: &CFGRiskSummary,
) -> bool {
    !matches!(
        artifact.granularity,
        r2sym::ArtifactGranularity::SummaryOnly
    ) && semantic_or_cfg_prefers_bounded_type_plan(artifact, cfg_summary)
}

pub fn type_route_decision(
    function_facts: &FunctionFacts,
    cfg_summary: &CFGRiskSummary,
    caller_prefers_bounded_type_plan: bool,
) -> EngineTypeRouteDecision {
    let prefer_cfg_bounded = (type_cfg_forces_bounded_plan(cfg_summary)
        && !type_cfg_allows_semantic_plan(cfg_summary))
        || (caller_prefers_bounded_type_plan && type_cfg_prefers_bounded_plan(cfg_summary));
    if prefer_cfg_bounded {
        return EngineTypeRouteDecision {
            request: EngineRequestKind::Types,
            plan: EnginePlan::BoundedType,
            kind: EngineTypeRouteKind::BoundedCfg,
            prefer_bounded_type_plan: true,
            reason: Some(type_cfg_bounded_reason(cfg_summary)),
            apply_artifact_signature_hint: false,
        };
    }

    if let Some(artifact) = function_facts.semantic_artifact()
        && semantic_artifact_needs_fallback_type_payload(artifact, cfg_summary)
    {
        return EngineTypeRouteDecision {
            request: EngineRequestKind::Types,
            plan: EnginePlan::SemanticSummary,
            kind: EngineTypeRouteKind::SemanticFallback,
            prefer_bounded_type_plan: true,
            reason: Some("semantic fallback type projection".to_string()),
            apply_artifact_signature_hint: true,
        };
    }

    EngineTypeRouteDecision {
        request: EngineRequestKind::Types,
        plan: select_engine_plan(EngineRequestKind::Types, None, Some(function_facts)),
        kind: EngineTypeRouteKind::FullWriteback,
        prefer_bounded_type_plan: false,
        reason: None,
        apply_artifact_signature_hint: false,
    }
}

pub fn signature_override_from_type_facts(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    callconv: Option<&str>,
    type_facts: &r2types::FunctionTypeFacts,
) -> Option<r2types::InferredSignature> {
    type_facts.merged_signature.as_ref().map(|signature| {
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

pub fn prefer_symbolic_large_worker_decompile(function_facts: &FunctionFacts) -> bool {
    let capability = function_facts.decompile_capability();
    capability
        .plan
        .as_ref()
        .is_some_and(r2sym::DecompilePlan::allows_native_linearization)
        && capability.skipped_large_cfg
        && matches!(
            capability.slice_class,
            Some(r2sym::SliceClass::Worker | r2sym::SliceClass::GenericLarge)
        )
        && (capability.has_native_regions || capability.has_summary_islands)
}

pub fn should_skip_runtime_type_inference(
    prepared: Option<&SsaArtifact>,
    _type_facts: &FunctionTypeFacts,
    function_facts: &FunctionFacts,
) -> bool {
    if prefer_symbolic_large_worker_decompile(function_facts) {
        return true;
    }
    let Some(prepared) = prepared else {
        return false;
    };
    let summary = prepared.function().cfg_risk_summary();
    summary.block_count >= 96
        && summary.switch_block_count > 0
        && summary.max_switch_cases >= 32
        && summary.back_edge_count == 0
}

pub fn should_use_prepared_semantic_view(
    prepared: Option<&SsaArtifact>,
    function_facts: &FunctionFacts,
) -> bool {
    prepared.is_some() && !prefer_symbolic_large_worker_decompile(function_facts)
}

fn preferred_vm_summary_reason(function_facts: &FunctionFacts) -> Option<String> {
    match function_facts.decompile_plan()? {
        r2sym::DecompilePlan::VmSummaryOnly { reason } => Some(reason),
        _ => None,
    }
}

fn preferred_semantic_fallback_comment(
    func_name: &str,
    function_facts: &FunctionFacts,
) -> Option<String> {
    let capability = function_facts.decompile_capability();
    if !is_autogenerated_function_name(func_name) {
        return None;
    }
    if capability
        .plan
        .as_ref()
        .is_some_and(r2sym::DecompilePlan::allows_native_linearization)
    {
        return None;
    }
    if capability.skipped_large_cfg
        || capability
            .residual_reasons
            .contains(&r2sym::ResidualReason::InterpreterRequiresStepSummary)
    {
        return r2dec::semantic_fallback_comment(func_name, function_facts.semantics.as_ref());
    }
    None
}

fn preferred_semantic_linearization_reason(
    func_name: &str,
    function_facts: &FunctionFacts,
    cfg_summary: &CFGRiskSummary,
) -> Option<String> {
    let capability = function_facts.decompile_capability();
    let plan = capability.plan.as_ref()?;
    if let r2sym::DecompilePlan::NativeLinear { reason } = plan
        && capability.has_native_regions
        && (!capability.skipped_large_cfg || !is_autogenerated_function_name(func_name))
        && matches!(capability.slice_class, Some(r2sym::SliceClass::Worker))
        && !capability.assumption_conflicted
        && capability.ambiguous_targets.is_empty()
        && (!has_generic_only_summary_islands(&capability) || capability.skipped_large_cfg)
    {
        return Some(reason.clone());
    }
    if let r2sym::DecompilePlan::NativeLinear { reason } = plan
        && capability.has_summary_islands
        && capability.has_primary_summary_islands
        && !capability.has_native_regions
        && matches!(
            capability.slice_class,
            Some(r2sym::SliceClass::Worker | r2sym::SliceClass::GenericLarge)
        )
        && !has_weak_summary_arg_contract_conflict(function_facts)
        && !capability.assumption_conflicted
        && !capability.summary_conflicted
        && capability.ambiguous_targets.is_empty()
    {
        return Some(reason.clone());
    }
    if !is_autogenerated_function_name(func_name) {
        return None;
    }
    let downgraded_from_structured = matches!(plan, r2sym::DecompilePlan::NativeStructured)
        && (capability.assumption_conflicted
            || capability.summary_conflicted
            || !capability.ambiguous_targets.is_empty());
    let linear_ready =
        matches!(plan, r2sym::DecompilePlan::NativeLinear { .. }) || downgraded_from_structured;
    if !linear_ready || !capability.skipped_large_cfg || !capability.has_native_regions {
        return None;
    }
    Some(preferred_semantic_worker_reason(cfg_summary))
}

fn preferred_semantic_summary_islands_reason(
    function_facts: &FunctionFacts,
    cfg_summary: &CFGRiskSummary,
) -> Option<String> {
    let capability = function_facts.decompile_capability();
    if has_weak_summary_arg_contract_conflict(function_facts) {
        return None;
    }
    let large_bounded_memory_worker = has_large_bounded_memory_summary_worker(&capability);
    let dense_summary_only_memory_worker = has_dense_summary_only_memory_worker(&capability);
    if !capability.has_summary_islands
        || (!capability.has_primary_summary_islands
            && !large_bounded_memory_worker
            && !dense_summary_only_memory_worker)
        || !matches!(
            capability.slice_class,
            Some(r2sym::SliceClass::Worker | r2sym::SliceClass::GenericLarge)
        )
    {
        return None;
    }
    match capability.plan.as_ref()? {
        r2sym::DecompilePlan::NativeStructured => {
            if capability.skipped_large_cfg
                && (cfg_guard_reason_from_summary(cfg_summary).is_some()
                    || capability.primary_summary_island_count >= 8
                    || large_bounded_memory_worker)
            {
                return Some(preferred_semantic_worker_reason(cfg_summary));
            }
            let summary_dense_native_worker = capability.primary_summary_island_count >= 16
                && (cfg_summary.loop_count > 0
                    || cfg_summary.back_edge_count > 0
                    || capability.actionable_region_count >= 4);
            summary_dense_native_worker.then(|| "summary-dense semantic worker islands".to_string())
        }
        r2sym::DecompilePlan::NativeSummaryIslands { reason } => {
            if !capability.skipped_large_cfg && capability.primary_summary_island_count < 16 {
                return None;
            }
            if capability.summary_conflicted || capability.assumption_conflicted {
                Some(preferred_semantic_worker_reason(cfg_summary))
            } else {
                Some(reason.clone())
            }
        }
        r2sym::DecompilePlan::NativeLinear { reason } => {
            if dense_summary_only_memory_worker {
                return Some("dense summary-only memory worker".to_string());
            }
            let summary_dense_native_worker = capability.primary_summary_island_count >= 16
                && (cfg_summary.loop_count > 0
                    || cfg_summary.back_edge_count > 0
                    || capability.actionable_region_count >= 4);
            if summary_dense_native_worker {
                return Some("summary-dense semantic worker islands".to_string());
            }
            let high_risk = cfg_guard_reason_from_summary(cfg_summary).is_some()
                || (capability.skipped_large_cfg && capability.primary_summary_island_count >= 8)
                || large_bounded_memory_worker;
            high_risk.then(|| reason.clone())
        }
        _ => None,
    }
}

fn preferred_semantic_structuring_reason(
    func_name: &str,
    function_facts: &FunctionFacts,
    _cfg_summary: &CFGRiskSummary,
) -> Option<String> {
    let capability = function_facts.decompile_capability();
    if !is_autogenerated_function_name(func_name) {
        return None;
    }
    if !capability
        .plan
        .as_ref()
        .is_some_and(r2sym::DecompilePlan::allows_native_structuring)
    {
        return None;
    }
    if !capability.skipped_large_cfg || !capability.has_native_regions {
        return None;
    }
    if capability.actionable_region_count == 0
        || capability.assumption_conflicted
        || capability.summary_conflicted
        || !capability.ambiguous_targets.is_empty()
    {
        return None;
    }
    Some(preferred_semantic_worker_reason(_cfg_summary))
}

fn preferred_semantic_worker_reason(cfg_summary: &CFGRiskSummary) -> String {
    cfg_guard_reason_from_summary(cfg_summary)
        .unwrap_or_else(|| "semantic worker islands".to_string())
}

fn has_generic_only_summary_islands(capability: &DecompileCapabilityView) -> bool {
    capability.has_summary_islands && !capability.has_primary_summary_islands
}

fn has_large_bounded_memory_summary_worker(capability: &DecompileCapabilityView) -> bool {
    capability.skipped_large_cfg
        && capability.has_memory_read_write_summary_pair
        && matches!(
            capability.slice_class,
            Some(r2sym::SliceClass::Worker | r2sym::SliceClass::GenericLarge)
        )
}

fn has_dense_summary_only_memory_worker(capability: &DecompileCapabilityView) -> bool {
    !capability.has_native_regions
        && capability.has_memory_read_write_summary_pair
        && capability.summary_island_count >= 24
        && matches!(
            capability.slice_class,
            Some(r2sym::SliceClass::Worker | r2sym::SliceClass::GenericLarge)
        )
}

fn has_weak_summary_arg_contract_conflict(function_facts: &FunctionFacts) -> bool {
    let Some(signature) = function_facts.types.merged_signature.as_ref() else {
        return false;
    };
    let Some(native) = function_facts
        .semantic_artifact()
        .and_then(r2sym::SemanticArtifact::native_body)
    else {
        return false;
    };
    let param_count = signature.params.len();
    let weak_worker_conflict = native.summary.worker_summaries.iter().any(|summary| {
        !summary.evidence.allows_guarded_structuring()
            && summary
                .arg_indices()
                .into_iter()
                .any(|index| index >= param_count)
    });
    let weak_region_conflict = native.summary.region_summaries.iter().any(|summary| {
        !summary.evidence.allows_guarded_structuring()
            && summary
                .arg_indices()
                .into_iter()
                .any(|index| index >= param_count)
    });
    weak_worker_conflict || weak_region_conflict
}

fn is_autogenerated_function_name(name: &str) -> bool {
    let underscore_hex_addr = name
        .strip_prefix('_')
        .is_some_and(|rest| !rest.is_empty() && rest.chars().all(|ch| ch.is_ascii_hexdigit()));
    name.is_empty()
        || name.starts_with("fcn.")
        || name.starts_with("fcn_")
        || name.starts_with("sub.")
        || name.starts_with("sub_")
        || name.starts_with("loc.")
        || underscore_hex_addr
}

struct BoundedArcCache<K, V> {
    limit: usize,
    entries: HashMap<K, (Arc<V>, u64)>,
    order: BTreeMap<u64, K>,
    next_ticket: u64,
}

struct CacheInsertResult<V> {
    value: Arc<V>,
    evicted_count: u64,
}

impl<K, V> BoundedArcCache<K, V>
where
    K: Clone + Eq + Hash,
{
    fn new(limit: usize) -> Self {
        Self {
            limit,
            entries: HashMap::new(),
            order: BTreeMap::new(),
            next_ticket: 1,
        }
    }

    fn allocate_ticket(&mut self) -> u64 {
        let ticket = self.next_ticket;
        self.next_ticket = self.next_ticket.wrapping_add(1).max(1);
        ticket
    }

    fn get(&mut self, key: &K) -> Option<Arc<V>> {
        let new_ticket = self.allocate_ticket();
        let (value, old_ticket) = self.entries.get_mut(key)?;
        let value = value.clone();
        let previous_ticket = *old_ticket;
        *old_ticket = new_ticket;
        self.order.remove(&previous_ticket);
        self.order.insert(new_ticket, key.clone());
        Some(value)
    }

    fn insert(&mut self, key: K, value: Arc<V>) -> CacheInsertResult<V> {
        if self.limit == 0 {
            return CacheInsertResult {
                value,
                evicted_count: 0,
            };
        }
        let ticket = self.allocate_ticket();
        if let Some((_, old_ticket)) = self.entries.insert(key.clone(), (value.clone(), ticket)) {
            self.order.remove(&old_ticket);
        }
        self.order.insert(ticket, key);
        let mut evicted_count = 0;
        while self.entries.len() > self.limit {
            let Some((_, evicted_key)) = self.order.pop_first() else {
                break;
            };
            if self.entries.remove(&evicted_key).is_some() {
                evicted_count += 1;
            }
        }
        CacheInsertResult {
            value,
            evicted_count,
        }
    }

    fn retain<F>(&mut self, mut keep: F) -> bool
    where
        F: FnMut(&K, &Arc<V>) -> bool,
    {
        let before = self.entries.len();
        self.entries.retain(|key, (value, _)| keep(key, value));
        self.order.clear();
        for (key, (_, ticket)) in &self.entries {
            self.order.insert(*ticket, key.clone());
        }
        self.entries.len() != before
    }

    fn len(&self) -> usize {
        self.entries.len()
    }
}

#[derive(Clone)]
struct Fnv64Hasher(u64);

impl Default for Fnv64Hasher {
    fn default() -> Self {
        Self(0xcbf29ce484222325)
    }
}

impl Hasher for Fnv64Hasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x100000001b3);
        }
    }
}

struct FnvFmtWriter<'a>(&'a mut Fnv64Hasher);

impl fmt::Write for FnvFmtWriter<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.write(s.as_bytes());
        Ok(())
    }
}

pub fn stable_fnv1a_hash<T: Hash + ?Sized>(value: &T) -> u64 {
    let mut hasher = Fnv64Hasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

pub fn stable_fnv1a_debug_hash<T: std::fmt::Debug + ?Sized>(value: &T) -> u64 {
    let mut hasher = Fnv64Hasher::default();
    let _ = write!(&mut FnvFmtWriter(&mut hasher), "{value:?}");
    hasher.finish()
}

pub fn stable_fnv1a_bytes(bytes: &[u8]) -> u64 {
    let mut hasher = Fnv64Hasher::default();
    hasher.write(bytes);
    hasher.finish()
}

pub fn stable_blocks_hash(blocks: &[R2ILBlock]) -> u64 {
    let mut hasher = Fnv64Hasher::default();
    "r2il-blocks-v1".hash(&mut hasher);
    blocks.len().hash(&mut hasher);
    for block in blocks {
        block.addr.hash(&mut hasher);
        block.size.hash(&mut hasher);
        block.ops.len().hash(&mut hasher);
        for op in &block.ops {
            let _ = write!(&mut FnvFmtWriter(&mut hasher), "{op:?}");
        }
        let _ = write!(
            &mut FnvFmtWriter(&mut hasher),
            "{:?}{:?}",
            block.switch_info,
            block.op_metadata
        );
    }
    hasher.finish()
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

        assert!(decision.display_summary_family);
        assert!(decision.named_worker_guarded);
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
    fn decompile_probe_decision_prefers_full_diagnostic_wrappers() {
        let mut blocks = const_return_blocks(0x4bc0, 0);
        for idx in 0..600 {
            blocks[0].push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x200 + idx, 8),
                src: r2il::Varnode::constant(idx, 8),
            });
        }

        let decision = decompile_probe_decision(&blocks, 0x4bc0, "sym.diagnose", "sym.diagnose");

        assert!(decision.display_summary_family);
        assert!(!decision.block_guarded);
        assert!(!decision.summary_probe_needed);
        assert!(!decision.summary_probe_skipped_large_cfg);
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
        assert!(identity.has_summary_family());
    }

    #[test]
    fn function_identity_uses_address_name_aliases_for_route_policy() {
        let identity = EngineFunctionIdentity::with_aliases(
            0x8b50,
            "fcn.00008b50",
            "fcn.00008b50",
            ["dbg.key_to_opts"],
        );

        assert!(
            identity
                .name_candidates()
                .any(should_use_direct_named_native_worker_decompile)
        );
        assert_eq!(identity.summary_probe_name(), "dbg.key_to_opts");
    }

    #[test]
    fn direct_named_worker_decompile_fastpath_covers_noisy_summary_owned_families() {
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.init_node"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "sym.rpl_nanosleep"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.mergefiles"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.xnrealloc"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.xnmalloc"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.xinmalloc"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.init_node.isra.0"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.cycle_check"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.key_to_opts"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.file_prefixlen"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "sym.operand_matches"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.xstrcoll_df_version"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.rev_strcmp_df_mtime"
        ));
        assert!(should_use_direct_named_native_worker_decompile("entry0"));
        assert!(should_use_direct_named_native_worker_decompile(
            "sym.register_tm_clones"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.save_token"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.filename_unescape"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "sym.compare"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.close_stream"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.rpl_fseeko"
        ));
        assert!(should_use_direct_named_native_worker_decompile("dbg.reap"));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.record_file"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.quotearg_free"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.num_processors_via_affinity_mask"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "sym.format_user_or_group"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "entry.fini0"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "sym.xmalloc"
        ));
        assert!(should_use_direct_named_native_worker_decompile(
            "dbg.rpl_reallocarray"
        ));
        assert!(!should_use_direct_named_native_worker_decompile(
            "dbg.hash_initialize"
        ));
        assert!(!should_use_direct_named_native_worker_decompile(
            "dbg.canonicalize_filename_mode"
        ));
        assert!(should_prefer_full_decompile_for_named_worker(
            "sym.diagnose"
        ));
    }

    #[test]
    fn direct_named_worker_type_projection_includes_program_orchestrators() {
        assert!(should_use_direct_named_native_worker_type_projection(
            "dbg.main"
        ));
        assert!(should_use_direct_named_native_worker_type_projection(
            "dbg.xnmalloc"
        ));
        assert!(should_use_direct_named_native_worker_type_projection(
            "randread"
        ));
        assert!(should_use_direct_named_native_worker_type_projection(
            "sym.sha256_process_block"
        ));
    }

    #[test]
    fn direct_named_worker_decompile_summary_renders_without_blocks() {
        let (_, ptr_bits, config) = r2dec::DecompilerConfig::for_arch(None);
        let parsed_context = r2types::ParsedExternalContext::default();
        let response = EngineSession::new(4)
            .decompile_direct_named_worker_summary(EngineDirectNamedWorkerDecompileRequest {
                function_addr: 0x8b50,
                function_name: "dbg.init_node",
                arch: None,
                ptr_bits,
                parsed_context: &parsed_context,
                config,
            })
            .expect("direct init_node summary");

        assert!(response.output.contains("init_node"));
        assert!(response.output.contains("r2dec summary:"));
        assert!(response.output.contains("worker summary:"));
        assert!(matches!(
            response.decision.plan,
            EnginePlan::SemanticSummary
        ));
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
    fn semantic_compile_prefers_named_native_worker_seed_before_full_semantics() {
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

        assert_eq!(
            artifact.granularity,
            r2sym::ArtifactGranularity::SummaryOnly
        );
        assert!(matches!(
            artifact.decompile_plan(),
            r2sym::DecompilePlan::NativeSummaryIslands { .. }
                | r2sym::DecompilePlan::NativeLinear { .. }
        ));
        let native = artifact.native_body().expect("native summary body");
        assert!(
            native
                .summary
                .worker_summaries
                .iter()
                .any(|summary| { summary.kind == r2sym::NativeWorkerSummaryKind::SortMerge })
        );
    }

    #[test]
    fn native_worker_type_projection_uses_name_params_and_summary_return() {
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

        let projection =
            native_worker_type_projection(0x11a9, "randread", "x86-64", 64, &parsed_context, true)
                .expect("expected randread native-worker projection");
        let signature = projection
            .function_facts
            .types
            .merged_signature
            .expect("expected projected signature");

        assert!(
            projection.name_owned_signature,
            "randread owns params by name while the summary supplies the return"
        );
        assert_eq!(
            signature
                .ret_type
                .as_ref()
                .map(|ty| r2types::render_signature_type(ty, 64))
                .as_deref(),
            Some("void")
        );
        assert_eq!(signature.params.len(), 3);
        assert_eq!(signature.params[0].name, "source");
        assert_eq!(
            signature.params[0]
                .ty
                .as_ref()
                .map(|ty| r2types::render_signature_type(ty, 64))
                .as_deref(),
            Some("randread_source*")
        );
        assert_eq!(signature.params[1].name, "buf");
        assert_eq!(
            signature.params[1]
                .ty
                .as_ref()
                .map(|ty| r2types::render_signature_type(ty, 64))
                .as_deref(),
            Some("int8_t*")
        );
        assert_eq!(signature.params[2].name, "size");
        assert_eq!(
            signature.params[2]
                .ty
                .as_ref()
                .map(|ty| r2types::render_signature_type(ty, 64))
                .as_deref(),
            Some("size_t")
        );
    }

    #[test]
    fn summary_projection_uses_register_params_when_signature_is_absent() {
        let summary = native_worker_summary_seed(0x401000, "sym.diagnose")
            .expect("expected diagnostic summary seed");
        let artifact = r2sym::compile_named_native_worker_summary_artifact(&summary, true)
            .expect("expected diagnostic summary artifact");
        let type_facts = FunctionTypeFacts {
            register_params: [
                "rdi", "rsi", "rdx", "rcx", "r8", "r9", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4",
            ]
            .into_iter()
            .enumerate()
            .map(|(idx, reg)| r2types::ExternalRegisterParamSpec {
                name: format!("arg{}", idx + 1),
                ty: None,
                reg: reg.to_string(),
            })
            .collect(),
            ..FunctionTypeFacts::default()
        };

        let projected = type_facts_with_summary_projection_for_candidates(
            type_facts,
            "sym.diagnose",
            ["sym.diagnose"],
            "x86-64",
            64,
            &artifact,
        );
        let signature = projected
            .merged_signature
            .expect("diagnostic summary should project a signature");

        assert_eq!(signature.params.len(), 11);
        assert_eq!(signature.params[0].name, "errnum");
        assert_eq!(signature.params[1].name, "fmt");
        assert_eq!(signature.params[10].name, "diag_value9");
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
    fn type_route_decision_keeps_summary_only_worker_as_type_input() {
        let summary = native_worker_summary_seed(0x11a9, "randread")
            .expect("expected randread native-worker seed");
        let artifact = r2sym::compile_named_native_worker_summary_artifact(&summary, true)
            .expect("expected randread native-worker artifact");
        let function_facts =
            FunctionFacts::new(FunctionTypeFacts::default(), Some(artifact.clone()));
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 200,
            loop_count: 8,
            back_edge_count: 12,
            switch_block_count: 0,
            max_switch_cases: 0,
        };

        assert!(semantic_or_cfg_prefers_bounded_type_plan(
            &artifact,
            &cfg_summary
        ));
        assert!(!semantic_artifact_needs_fallback_type_payload(
            &artifact,
            &cfg_summary
        ));
        assert_eq!(
            type_route_decision(&function_facts, &cfg_summary, false).kind,
            EngineTypeRouteKind::FullWriteback
        );
    }

    #[test]
    fn bounded_cfg_writeback_plan_preserves_signature_context() {
        let type_facts = FunctionTypeFacts {
            merged_signature: Some(r2types::FunctionSignatureSpec {
                ret_type: Some(r2types::CTypeLike::Void),
                params: vec![r2types::FunctionParamSpec {
                    name: "status".to_string(),
                    ty: Some(r2types::CTypeLike::Int {
                        bits: 32,
                        signedness: r2types::Signedness::Signed,
                    }),
                }],
            }),
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
    fn semantic_fallback_writeback_plan_preserves_name_owned_role_signature() {
        let summary = r2ssa::FunctionSemanticSummary::seed_for_name(
            r2ssa::InterprocFunctionId(0x11a9),
            "verror_at_line",
        )
        .unwrap_or_else(|| {
            r2ssa::FunctionSemanticSummary::unknown(
                r2ssa::InterprocFunctionId(0x11a9),
                Some("verror_at_line".to_string()),
            )
        });
        let artifact = r2sym::compile_named_native_worker_summary_artifact(&summary, true)
            .expect("expected named diagnostic summary artifact");
        let role_signature = r2types::signature_hint_for_name_candidates(["verror_at_line"], 6)
            .expect("expected exact diagnostic role signature");
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(role_signature),
                ..FunctionTypeFacts::default()
            },
            Some(artifact.clone()),
        );

        let plan = semantic_fallback_type_writeback_plan(
            "verror_at_line",
            "x86-64",
            64,
            Some("amd64"),
            &artifact,
            &function_facts,
            false,
        );

        assert_eq!(plan.signature.ret_type, "void");
        assert_eq!(plan.signature.params[3].param_type, "unsigned int");
        assert_eq!(plan.signature.params[5].param_type, "__va_list_tag*");
    }

    #[test]
    fn type_summary_preprobe_bounds_large_program_orchestrator_without_full_analysis() {
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
        })
        .expect("large program orchestrator should use summary type preprobe");

        assert_eq!(
            response.route_decision.kind,
            EngineTypeRouteKind::SemanticFallback
        );
        let signature = response
            .function_facts
            .types
            .merged_signature
            .as_ref()
            .expect("main role signature");
        assert_eq!(signature.params[0].name, "argc");
        assert!(
            response
                .function_facts
                .semantic_artifact()
                .and_then(r2sym::SemanticArtifact::native_body)
                .is_some_and(|native| {
                    native.summary.worker_summaries.iter().any(|summary| {
                        summary.kind == r2sym::NativeWorkerSummaryKind::ProgramOrchestrator
                    })
                })
        );
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
            .expect("large program orchestrator should be typed by engine preprobe");

        assert_eq!(
            response.route_decision.kind,
            EngineTypeRouteKind::SemanticFallback
        );
        assert!(response.artifact_key.is_none());
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

        assert!(response.output.contains("r2dec summary:"));
        assert!(response.output.contains("init_node"));
        assert!(matches!(
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
            refusal: Some(comment.clone()),
        };

        let request_plan = EngineRequestPlan::decompile(decision);
        let diagnostics = request_plan.diagnostics();

        assert_eq!(request_plan.engine_plan(), EnginePlan::RefuseWithEvidence);
        assert_eq!(request_plan.cache.layer, EngineCacheLayer::Render);
        assert_eq!(diagnostics.refusal, Some(comment.clone()));
        assert_eq!(diagnostics.route_reason, Some(comment));
    }

    #[test]
    fn native_linear_artifact_plan_keeps_regioned_generic_workers_standard_by_default() {
        let blocks = const_return_blocks(0x401000, 0);
        let cfg_summary = r2ssa::SSAFunction::from_blocks_raw_no_arch(&blocks)
            .expect("ssa")
            .cfg_risk_summary();

        for slice_class in [r2sym::SliceClass::GenericLarge, r2sym::SliceClass::Wrapper] {
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
    fn named_summary_route_accepts_weak_arg_contract_for_summary_only_worker() {
        let summary = native_worker_summary_seed(0xe0a0, "dbg.print_current_files")
            .expect("expected print_current_files native-worker seed");
        let artifact = r2sym::compile_named_native_worker_summary_artifact(&summary, true)
            .expect("expected print_current_files summary artifact");
        let function_facts = FunctionFacts::new(
            FunctionTypeFacts {
                merged_signature: Some(r2types::FunctionSignatureSpec {
                    ret_type: Some(r2types::CTypeLike::Void),
                    params: Vec::new(),
                }),
                ..FunctionTypeFacts::default()
            },
            Some(artifact),
        );

        assert!(has_renderable_primary_summary_only_native_worker(
            &function_facts
        ));
        assert!(matches!(
            named_worker_summary_route(true, &function_facts),
            Some(r2dec::SemanticRoutePlan::SummaryIslands { .. })
        ));
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
