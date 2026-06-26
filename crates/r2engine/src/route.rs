use std::collections::BTreeSet;

use r2il::R2ILBlock;
use r2ssa::{CFGRiskSummary, SSAFunction, SsaArtifact};
use r2types::{DecompileCapabilityView, FunctionFacts, FunctionTypeFacts};
use serde::{Deserialize, Serialize};

use crate::EngineCachePlan;

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
        let normalized = r2sym::normalize_native_worker_role_name(alias);
        if let Some(normalized) = normalized
            && !self.aliases.iter().any(|existing| existing == &normalized)
        {
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

    pub fn name_route_facts(&self) -> r2sym::NativeWorkerNameRouteFacts {
        r2sym::NativeWorkerNameRouteFacts::for_candidates(
            self.function_addr,
            &self.display_name,
            &self.canonical_name,
            self.name_candidates(),
            self.primary_name(),
        )
    }

    pub fn summary_probe_name(&self) -> String {
        self.name_route_facts().summary_probe_name
    }

    pub fn has_summary_family(&self) -> bool {
        self.name_route_facts().summary_family
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineSemanticRoutePlan {
    Standard,
    StructuredWorker { reason: String },
    SummaryIslands { reason: String },
    LinearWorker { reason: String },
    VmSummary { reason: String },
    FallbackComment { comment: String },
}

impl EngineSemanticRoutePlan {
    pub fn to_decompiler_route(&self) -> r2dec::SemanticRoutePlan {
        match self {
            Self::Standard => r2dec::SemanticRoutePlan::Standard,
            Self::StructuredWorker { reason } => r2dec::SemanticRoutePlan::StructuredWorker {
                reason: reason.clone(),
            },
            Self::SummaryIslands { reason } => r2dec::SemanticRoutePlan::SummaryIslands {
                reason: reason.clone(),
            },
            Self::LinearWorker { reason } => r2dec::SemanticRoutePlan::LinearWorker {
                reason: reason.clone(),
            },
            Self::VmSummary { reason } => r2dec::SemanticRoutePlan::VmSummary {
                reason: reason.clone(),
            },
            Self::FallbackComment { comment } => r2dec::SemanticRoutePlan::FallbackComment {
                comment: comment.clone(),
            },
        }
    }
}

fn decompile_route_kind(route: &EngineSemanticRoutePlan) -> r2types::DecompileRouteKind {
    match route {
        EngineSemanticRoutePlan::Standard => r2types::DecompileRouteKind::Standard,
        EngineSemanticRoutePlan::StructuredWorker { .. } => {
            r2types::DecompileRouteKind::StructuredWorker
        }
        EngineSemanticRoutePlan::SummaryIslands { .. } => {
            r2types::DecompileRouteKind::SummaryIslands
        }
        EngineSemanticRoutePlan::LinearWorker { .. } => r2types::DecompileRouteKind::LinearWorker,
        EngineSemanticRoutePlan::VmSummary { .. } => r2types::DecompileRouteKind::VmSummary,
        EngineSemanticRoutePlan::FallbackComment { .. } => {
            r2types::DecompileRouteKind::FallbackComment
        }
    }
}

pub fn decompile_route_facts_from_decision(
    decision: &EngineRouteDecision,
) -> r2types::DecompileRouteFacts {
    r2types::DecompileRouteFacts {
        kind: decompile_route_kind(&decision.route),
        reason: decision.route_reason.clone(),
        fallback_comment: match &decision.route {
            EngineSemanticRoutePlan::FallbackComment { comment } => Some(comment.clone()),
            _ => None,
        },
        skip_runtime_type_inference: decision.skip_runtime_type_inference,
        use_prepared_semantic_view: decision.use_prepared_semantic_view,
        proof_coverage: decision.proof_coverage.clone(),
        render_permission: decision.render_permission.clone(),
    }
}

pub fn decompile_route_from_facts(route: &r2types::DecompileRouteFacts) -> EngineSemanticRoutePlan {
    match route.kind {
        r2types::DecompileRouteKind::Standard => EngineSemanticRoutePlan::Standard,
        r2types::DecompileRouteKind::StructuredWorker => {
            EngineSemanticRoutePlan::StructuredWorker {
                reason: route.reason.clone().unwrap_or_default(),
            }
        }
        r2types::DecompileRouteKind::SummaryIslands => EngineSemanticRoutePlan::SummaryIslands {
            reason: route.reason.clone().unwrap_or_default(),
        },
        r2types::DecompileRouteKind::LinearWorker => EngineSemanticRoutePlan::LinearWorker {
            reason: route.reason.clone().unwrap_or_default(),
        },
        r2types::DecompileRouteKind::VmSummary => EngineSemanticRoutePlan::VmSummary {
            reason: route.reason.clone().unwrap_or_default(),
        },
        r2types::DecompileRouteKind::FallbackComment => EngineSemanticRoutePlan::FallbackComment {
            comment: route
                .fallback_comment
                .clone()
                .or_else(|| route.reason.clone())
                .unwrap_or_default(),
        },
    }
}

#[derive(Debug, Clone, Default)]
pub struct EngineDiagnostics {
    pub plan: Option<EnginePlan>,
    pub route_reason: Option<String>,
    pub proof_coverage: Option<r2sym::ProofCoverage>,
    pub render_permission: Option<r2sym::RenderPermission>,
    pub warnings: Vec<String>,
    pub refusal: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineRouteContext<'a> {
    pub func_name: &'a str,
    pub function_facts: &'a FunctionFacts,
    pub cfg_summary: &'a CFGRiskSummary,
    pub semantic_claims: r2sym::SemanticClaimSummary,
}

impl<'a> EngineRouteContext<'a> {
    pub fn new(
        func_name: &'a str,
        function_facts: &'a FunctionFacts,
        cfg_summary: &'a CFGRiskSummary,
    ) -> Self {
        let semantic_claims = function_facts
            .semantic_artifact()
            .map(r2sym::SemanticArtifact::semantic_claim_summary)
            .unwrap_or_else(r2sym::SemanticClaimSummary::empty);
        Self {
            func_name,
            function_facts,
            cfg_summary,
            semantic_claims,
        }
    }

    pub fn has_renderable_semantic_claims(&self) -> bool {
        self.semantic_claims.has_renderable_non_name_claim()
    }

    pub fn has_structured_control_claims(&self) -> bool {
        self.semantic_claims.structural_control_claims > 0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineRouteDecision {
    pub request: EngineRequestKind,
    pub plan: EnginePlan,
    pub route: EngineSemanticRoutePlan,
    pub route_reason: Option<String>,
    pub skip_runtime_type_inference: bool,
    pub use_prepared_semantic_view: bool,
    pub proof_coverage: r2sym::ProofCoverage,
    pub render_permission: r2sym::RenderPermission,
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
    Decompile(Box<EngineRouteDecision>),
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

    pub fn proof_coverage(&self) -> Option<r2sym::ProofCoverage> {
        match self {
            Self::Decompile(decision) => Some(decision.proof_coverage.clone()),
            Self::Types(_) | Self::Profile(_) => None,
        }
    }

    pub fn render_permission(&self) -> Option<r2sym::RenderPermission> {
        match self {
            Self::Decompile(decision) => Some(decision.render_permission.clone()),
            Self::Types(_) | Self::Profile(_) => None,
        }
    }

    pub fn diagnostics(&self) -> EngineDiagnostics {
        EngineDiagnostics {
            plan: Some(self.plan()),
            route_reason: self.reason(),
            proof_coverage: self.proof_coverage(),
            render_permission: self.render_permission(),
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
        Self::new(EngineTypedRouteDecision::Decompile(Box::new(decision)))
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecompileProbeDecision {
    pub op_count: usize,
    pub cfg_guard_reason: Option<String>,
    pub display_summary_family: bool,
    pub canonical_summary_family: bool,
    pub named_worker_guarded: bool,
    pub summary_probe_name: String,
    pub summary_probe_needed: bool,
    pub summary_probe_skipped_large_cfg: bool,
    pub block_guarded: bool,
}

pub(super) fn raw_cfg_risk_summary_for_preprobe(blocks: &[R2ILBlock]) -> CFGRiskSummary {
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
    let name_facts = identity.name_route_facts();
    let cfg_guard_reason = cfg_guard_reason(blocks);
    let op_count = blocks.iter().map(|block| block.ops.len()).sum::<usize>();
    let raw_cfg = raw_cfg_risk_summary_for_preprobe(blocks);
    let small_structural_worker_probe = raw_cfg.block_count > 0
        && raw_cfg.block_count <= 64
        && (raw_cfg.loop_count > 0
            || raw_cfg.back_edge_count > 0
            || raw_cfg.switch_block_count > 0);
    let skipped_large_cfg_guarded =
        cfg_guard_reason.is_some() || blocks.len() > 200 || op_count > 512;
    let named_worker_guarded = name_facts.summary_family && skipped_large_cfg_guarded;
    let block_guarded = named_worker_guarded || skipped_large_cfg_guarded;
    let summary_probe_needed =
        block_guarded || cfg_guard_reason.is_some() || small_structural_worker_probe;

    DecompileProbeDecision {
        op_count,
        cfg_guard_reason,
        display_summary_family: name_facts.display_summary_family,
        canonical_summary_family: name_facts.canonical_summary_family,
        named_worker_guarded,
        summary_probe_name: name_facts.summary_probe_name,
        summary_probe_needed,
        summary_probe_skipped_large_cfg: skipped_large_cfg_guarded,
        block_guarded,
    }
}

pub fn should_guard_program_orchestrator_decompile(block_count: usize, op_count: usize) -> bool {
    block_count > 4 || op_count > 96
}

pub fn semantic_route_from_artifact_plan(
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<EngineSemanticRoutePlan> {
    match semantic_artifact.decompile_plan() {
        r2sym::DecompilePlan::NativeLinear { reason }
            if native_linear_artifact_plan_allows_summary_route(semantic_artifact) =>
        {
            Some(EngineSemanticRoutePlan::LinearWorker { reason })
        }
        r2sym::DecompilePlan::NativeSummaryIslands { reason } => {
            Some(EngineSemanticRoutePlan::SummaryIslands { reason })
        }
        r2sym::DecompilePlan::VmSummaryOnly { reason } => {
            Some(EngineSemanticRoutePlan::VmSummary { reason })
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
    if !semantic_artifact.diagnostics.skipped_large_cfg
        && !native_body_has_renderable_worker_summary(native)
    {
        return false;
    }
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
            .is_some_and(|native| native.has_primary_non_name_summary_islands())
}

pub fn has_renderable_primary_summary_only_native_worker(function_facts: &FunctionFacts) -> bool {
    function_facts
        .semantic_artifact()
        .is_some_and(has_primary_summary_only_native_worker)
}

pub fn named_worker_summary_route(
    named_worker_guarded: bool,
    function_facts: &FunctionFacts,
) -> Option<EngineSemanticRoutePlan> {
    (named_worker_guarded && has_renderable_primary_summary_only_native_worker(function_facts))
        .then(|| EngineSemanticRoutePlan::SummaryIslands {
            reason: "named native-worker summary projection".to_string(),
        })
}

pub(super) fn proof_coverage_from_type_facts(
    type_facts: &FunctionTypeFacts,
) -> r2sym::ProofCoverage {
    r2sym::ProofCoverage {
        certified_field_accesses: type_facts.field_access_certificates.len(),
        certified_array_indexes: type_facts.array_index_certificates.len(),
        certified_out_params: type_facts
            .source_authorized_out_param_certificates()
            .count(),
        certified_signatures: usize::from(type_facts.render_authorized_signature().is_some()),
        ..r2sym::ProofCoverage::default()
    }
}

pub fn select_engine_plan(
    request: EngineRequestKind,
    route: Option<&EngineSemanticRoutePlan>,
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
            Some(EngineSemanticRoutePlan::Standard) | None => EnginePlan::FastLocal,
            Some(EngineSemanticRoutePlan::FallbackComment { .. }) => EnginePlan::RefuseWithEvidence,
            Some(EngineSemanticRoutePlan::VmSummary { .. })
            | Some(EngineSemanticRoutePlan::SummaryIslands { .. })
            | Some(EngineSemanticRoutePlan::LinearWorker { .. }) => EnginePlan::SemanticSummary,
            Some(EngineSemanticRoutePlan::StructuredWorker { .. }) => {
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
) -> EngineSemanticRoutePlan {
    let context = EngineRouteContext::new(func_name, function_facts, cfg_summary);
    semantic_route_plan_from_context(&context)
}

pub fn semantic_route_plan_from_context(
    context: &EngineRouteContext<'_>,
) -> EngineSemanticRoutePlan {
    if let Some(reason) = preferred_vm_summary_reason(context.function_facts) {
        return EngineSemanticRoutePlan::VmSummary { reason };
    }
    if let Some(comment) =
        preferred_semantic_fallback_comment(context.func_name, context.function_facts)
    {
        return EngineSemanticRoutePlan::FallbackComment { comment };
    }
    if let Some(reason) = preferred_semantic_summary_islands_reason(context) {
        return EngineSemanticRoutePlan::SummaryIslands { reason };
    }
    if let Some(reason) = preferred_semantic_structuring_reason(context) {
        return EngineSemanticRoutePlan::StructuredWorker { reason };
    }
    if let Some(reason) = preferred_semantic_linearization_reason(context) {
        return EngineSemanticRoutePlan::LinearWorker { reason };
    }
    if let Some(route) = context
        .function_facts
        .semantic_artifact()
        .and_then(semantic_route_from_artifact_plan)
        .filter(|_| context.has_renderable_semantic_claims())
    {
        return route;
    }
    EngineSemanticRoutePlan::Standard
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
        EngineSemanticRoutePlan::FallbackComment { comment } => Some(comment.clone()),
        _ => None,
    };
    let proof_coverage = prepared
        .map(|prepared| r2sym::ProofCoverage::from_prepared_certificates(prepared.certificates()))
        .unwrap_or_default()
        .merge(function_facts.proof.clone())
        .merge(proof_coverage_from_type_facts(type_facts));
    let render_permission = render_permission_for_decompile_route(
        &route,
        cfg_summary,
        &proof_coverage,
        prepared.is_some(),
    );
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
        proof_coverage,
        render_permission,
        refusal,
    }
}

pub fn decompile_route_decision_with_route(
    mut decision: EngineRouteDecision,
    route: EngineSemanticRoutePlan,
    cfg_summary: &CFGRiskSummary,
    prepared_available: bool,
) -> EngineRouteDecision {
    decision.route = route;
    decision.plan = select_engine_plan(EngineRequestKind::Decompile, Some(&decision.route), None);
    decision.route_reason = semantic_route_reason(&decision.route);
    decision.refusal = match &decision.route {
        EngineSemanticRoutePlan::FallbackComment { comment } => Some(comment.clone()),
        _ => None,
    };
    decision.render_permission = render_permission_for_decompile_route(
        &decision.route,
        cfg_summary,
        &decision.proof_coverage,
        prepared_available,
    );
    decision
}

fn render_permission_for_decompile_route(
    route: &EngineSemanticRoutePlan,
    cfg_summary: &CFGRiskSummary,
    proof_coverage: &r2sym::ProofCoverage,
    prepared_available: bool,
) -> r2sym::RenderPermission {
    match route {
        EngineSemanticRoutePlan::Standard => {
            proof_coverage.standard_control_render_permission(cfg_summary, prepared_available)
        }
        EngineSemanticRoutePlan::FallbackComment { comment } => {
            r2sym::RenderPermission::refuse(r2sym::ProofOwner::R2engine, comment.clone())
        }
        EngineSemanticRoutePlan::VmSummary { reason }
        | EngineSemanticRoutePlan::SummaryIslands { reason }
        | EngineSemanticRoutePlan::LinearWorker { reason }
        | EngineSemanticRoutePlan::StructuredWorker { reason } => {
            r2sym::RenderPermission::summary(r2sym::ProofOwner::R2engine, reason.clone())
        }
    }
}

pub(crate) fn decompiler_context_with_route_decision(
    context: r2dec::DecompilerContext,
    decision: &EngineRouteDecision,
) -> r2dec::DecompilerContext {
    let mut function_facts = context.function_facts.clone();
    function_facts.set_decompile_route(Some(decompile_route_facts_from_decision(decision)));
    context.with_function_facts(function_facts)
}

pub fn semantic_route_reason(route: &EngineSemanticRoutePlan) -> Option<String> {
    match route {
        EngineSemanticRoutePlan::StructuredWorker { reason }
        | EngineSemanticRoutePlan::SummaryIslands { reason }
        | EngineSemanticRoutePlan::LinearWorker { reason }
        | EngineSemanticRoutePlan::VmSummary { reason } => Some(reason.clone()),
        EngineSemanticRoutePlan::FallbackComment { comment } => Some(comment.clone()),
        EngineSemanticRoutePlan::Standard => None,
    }
}

pub fn detached_semantic_route_plan(
    func_name: &str,
    blocks: &[R2ILBlock],
    function_facts: &FunctionFacts,
) -> Option<EngineSemanticRoutePlan> {
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
        EngineSemanticRoutePlan::LinearWorker { reason }
        | EngineSemanticRoutePlan::SummaryIslands { reason } => Some(reason),
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
    if !r2sym::is_autogenerated_semantic_function_name(func_name) {
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

fn preferred_semantic_linearization_reason(context: &EngineRouteContext<'_>) -> Option<String> {
    if !context.has_renderable_semantic_claims() {
        return None;
    }
    let function_facts = context.function_facts;
    let capability = function_facts.decompile_capability();
    let plan = capability.plan.as_ref()?;
    let compact_renderable_worker = !capability.skipped_large_cfg
        && has_renderable_native_linear_worker_summary(function_facts);
    if let r2sym::DecompilePlan::NativeLinear { reason } = plan
        && capability.has_native_regions
        && ((capability.skipped_large_cfg
            && !r2sym::is_autogenerated_semantic_function_name(context.func_name))
            || compact_renderable_worker)
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
        && (capability.skipped_large_cfg || compact_renderable_worker)
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
    if !r2sym::is_autogenerated_semantic_function_name(context.func_name) {
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
    Some(preferred_semantic_worker_reason(context.cfg_summary))
}

fn preferred_semantic_summary_islands_reason(context: &EngineRouteContext<'_>) -> Option<String> {
    if !context.has_renderable_semantic_claims() {
        return None;
    }
    let function_facts = context.function_facts;
    let cfg_summary = context.cfg_summary;
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
            if has_summary_only_scan_table_worker(function_facts) {
                return Some(reason.clone());
            }
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

fn preferred_semantic_structuring_reason(context: &EngineRouteContext<'_>) -> Option<String> {
    let capability = context.function_facts.decompile_capability();
    if !r2sym::is_autogenerated_semantic_function_name(context.func_name) {
        return None;
    }
    if !context.has_structured_control_claims() {
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
    Some(preferred_semantic_worker_reason(context.cfg_summary))
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

pub(super) fn has_renderable_native_linear_worker_summary(function_facts: &FunctionFacts) -> bool {
    let Some(native) = function_facts
        .semantic_artifact()
        .and_then(r2sym::SemanticArtifact::native_body)
    else {
        return false;
    };
    native_body_has_renderable_worker_summary(native)
}

pub(super) fn native_body_has_renderable_worker_summary(
    native: &r2sym::NativeArtifactBody,
) -> bool {
    if !r2sym::SemanticClaimSummary::from_native_body(native).has_renderable_non_name_claim() {
        return false;
    }
    native
        .summary
        .worker_summaries
        .iter()
        .any(is_renderable_native_worker_summary)
}

fn is_renderable_native_worker_summary(summary: &r2sym::NativeWorkerSummary) -> bool {
    if summary.has_name_hint_evidence() {
        return false;
    }
    match summary.kind {
        r2sym::NativeWorkerSummaryKind::NumericTransform => {
            summary.dst.is_none()
                && summary.memory.is_some()
                && worker_summary_has_known_length(summary)
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.fold.as_ref().is_some_and(|fold| {
                        fold.operation == r2sym::NativeWorkerFoldOperation::Add
                            && fold.predicate.is_some()
                    })
                })
        }
        r2sym::NativeWorkerSummaryKind::HashFold => {
            summary.memory.is_some()
                && worker_summary_has_known_length(summary)
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.fold.as_ref().is_some_and(|fold| {
                        fold.operation == r2sym::NativeWorkerFoldOperation::Xor
                            && fold.init.is_some()
                            && fold.multiplier.is_some()
                    })
                })
        }
        r2sym::NativeWorkerSummaryKind::Parser => {
            summary.memory.is_some() && summary.parser.is_some()
        }
        r2sym::NativeWorkerSummaryKind::StringScan | r2sym::NativeWorkerSummaryKind::TableWalk => {
            is_renderable_scan_table_worker_summary(summary)
        }
        _ => false,
    }
}

fn has_summary_only_scan_table_worker(function_facts: &FunctionFacts) -> bool {
    let Some(semantic_artifact) = function_facts.semantic_artifact() else {
        return false;
    };
    if semantic_artifact.granularity != r2sym::ArtifactGranularity::SummaryOnly {
        return false;
    }
    semantic_artifact.native_body().is_some_and(|native| {
        native
            .summary
            .worker_summaries
            .iter()
            .any(is_renderable_scan_table_worker_summary)
    })
}

fn is_renderable_scan_table_worker_summary(summary: &r2sym::NativeWorkerSummary) -> bool {
    matches!(
        summary.kind,
        r2sym::NativeWorkerSummaryKind::StringScan | r2sym::NativeWorkerSummaryKind::TableWalk
    ) && summary.memory.is_some()
        && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
            loop_summary.terminator.is_some_and(|terminator| {
                !matches!(terminator, r2sym::NativeWorkerTerminator::Unknown)
            })
        })
}

fn worker_summary_has_known_length(summary: &r2sym::NativeWorkerSummary) -> bool {
    matches!(
        summary.len,
        Some(r2ssa::SummaryTransferLength::Arg(_) | r2ssa::SummaryTransferLength::Const(_))
    ) || summary
        .loop_summary
        .as_ref()
        .and_then(|loop_summary| loop_summary.length_arg)
        .is_some()
}

fn has_weak_summary_arg_contract_conflict(function_facts: &FunctionFacts) -> bool {
    let Some(signature) = function_facts.types.render_authorized_signature() else {
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
