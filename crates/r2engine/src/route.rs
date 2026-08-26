use std::collections::BTreeSet;

use r2il::R2ILBlock;
use r2ssa::{CFGRiskSummary, SSAFunction, SsaArtifact};
use r2types::{DecompileCapabilityView, FunctionFacts};
use serde::{Deserialize, Serialize};

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

fn provisional_decompile_route(
    kind: r2types::DecompileRouteKind,
    reason: Option<String>,
    fallback_comment: Option<String>,
) -> r2types::DecompileRouteFacts {
    r2types::DecompileRouteFacts {
        kind,
        reason,
        fallback_comment,
        use_prepared_semantic_view: matches!(kind, r2types::DecompileRouteKind::Standard),
    }
}

#[derive(Debug, Clone, Default)]
pub struct EngineDiagnostics {
    pub plan: Option<EnginePlan>,
    pub route_reason: Option<String>,
    pub warnings: Vec<String>,
    pub refusal: Option<String>,
}

#[derive(Debug, Clone)]
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
            .semantic_report()
            .map(r2sym::SemanticArtifactReport::semantic_claim_summary)
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
    pub route: r2types::DecompileRouteFacts,
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineTypedRouteDecision {
    Decompile(Box<EngineRouteDecision>),
    Types(EngineTypeRouteDecision),
}

impl EngineTypedRouteDecision {
    pub fn request(&self) -> EngineRequestKind {
        match self {
            Self::Decompile(decision) => decision.request,
            Self::Types(decision) => decision.request,
        }
    }

    pub fn plan(&self) -> EnginePlan {
        match self {
            Self::Decompile(decision) => decision.plan,
            Self::Types(decision) => decision.plan,
        }
    }

    pub fn reason(&self) -> Option<String> {
        match self {
            Self::Decompile(decision) => decision.route.reason.clone(),
            Self::Types(decision) => decision.reason.clone(),
        }
    }

    pub fn refusal(&self) -> Option<String> {
        match self {
            Self::Decompile(decision) => decision.route.fallback_comment.clone(),
            Self::Types(_) => None,
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
}

impl EngineRequestPlan {
    pub fn new(decision: EngineTypedRouteDecision) -> Self {
        Self { decision }
    }

    pub fn decompile(decision: EngineRouteDecision) -> Self {
        Self::new(EngineTypedRouteDecision::Decompile(Box::new(decision)))
    }

    pub fn types(decision: EngineTypeRouteDecision) -> Self {
        Self::new(EngineTypedRouteDecision::Types(decision))
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

#[cfg(test)]
pub(crate) fn decompile_probe_decision(
    blocks: &[R2ILBlock],
    function_addr: u64,
    canonical_name: &str,
    display_name: &str,
) -> DecompileProbeDecision {
    let identity = EngineFunctionIdentity::new(function_addr, canonical_name, display_name);
    decompile_probe_decision_for_identity(blocks, &identity)
}

pub(crate) fn decompile_probe_decision_for_identity(
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
    let skipped_large_cfg_guarded = cfg_guard_reason.is_some()
        || blocks.len() > crate::ENGINE_DECOMPILE_MAX_BLOCKS
        || op_count > crate::ENGINE_DECOMPILE_MAX_OPS;
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

pub(crate) fn semantic_route_from_artifact_plan(
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<r2types::DecompileRouteFacts> {
    match semantic_artifact.decompile_plan() {
        r2sym::DecompilePlan::NativeLinear { reason }
            if native_linear_artifact_plan_allows_summary_route(semantic_artifact) =>
        {
            Some(provisional_decompile_route(
                r2types::DecompileRouteKind::LinearWorker,
                Some(reason),
                None,
            ))
        }
        r2sym::DecompilePlan::NativeSummaryIslands { reason } => Some(provisional_decompile_route(
            r2types::DecompileRouteKind::SummaryIslands,
            Some(reason),
            None,
        )),
        r2sym::DecompilePlan::VmSummaryOnly { reason } => Some(provisional_decompile_route(
            r2types::DecompileRouteKind::VmSummary,
            Some(reason),
            None,
        )),
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

pub fn select_engine_plan(
    request: EngineRequestKind,
    route: Option<&r2types::DecompileRouteFacts>,
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
        EngineRequestKind::Decompile => match route {
            Some(route) if route.kind == r2types::DecompileRouteKind::FallbackComment => {
                EnginePlan::RefuseWithEvidence
            }
            Some(route)
                if matches!(
                    route.kind,
                    r2types::DecompileRouteKind::VmSummary
                        | r2types::DecompileRouteKind::SummaryIslands
                        | r2types::DecompileRouteKind::LinearWorker
                ) =>
            {
                EnginePlan::SemanticSummary
            }
            Some(route) if route.kind == r2types::DecompileRouteKind::StructuredWorker => {
                EnginePlan::SemanticStructured
            }
            Some(_) | None => EnginePlan::FastLocal,
        },
    }
}

#[cfg(test)]
pub(crate) fn plan_decompile_request(
    func_name: &str,
    function_facts: &FunctionFacts,
    prepared: Option<&SsaArtifact>,
    cfg_summary: &CFGRiskSummary,
) -> EngineRequestPlan {
    EngineRequestPlan::decompile(decompile_route_decision(
        func_name,
        function_facts,
        prepared,
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

pub(crate) fn semantic_route_plan(
    func_name: &str,
    function_facts: &FunctionFacts,
    cfg_summary: &CFGRiskSummary,
) -> r2types::DecompileRouteFacts {
    let context = EngineRouteContext::new(func_name, function_facts, cfg_summary);
    semantic_route_plan_from_context(&context)
}

pub(crate) fn semantic_route_plan_from_context(
    context: &EngineRouteContext<'_>,
) -> r2types::DecompileRouteFacts {
    if let Some(reason) = preferred_vm_summary_reason(context.function_facts) {
        return provisional_decompile_route(
            r2types::DecompileRouteKind::VmSummary,
            Some(reason),
            None,
        );
    }
    if let Some(artifact) = context.function_facts.semantic_artifact()
        && artifact.execution == r2sym::ExecutionModel::Native
        && artifact.granularity == r2sym::ArtifactGranularity::SummaryOnly
    {
        let comment = crate::semantic_fallback_comment_for_facts(
            context.func_name,
            context.function_facts,
        )
        .unwrap_or_else(|| {
            crate::artifact_guard_fallback_comment(
                context.func_name,
                "summary-only semantic report is advisory and cannot authorize executable C",
            )
        });
        return provisional_decompile_route(
            r2types::DecompileRouteKind::FallbackComment,
            Some(comment.clone()),
            Some(comment),
        );
    }
    if let Some(comment) =
        preferred_semantic_fallback_comment(context.func_name, context.function_facts)
    {
        return provisional_decompile_route(
            r2types::DecompileRouteKind::FallbackComment,
            Some(comment.clone()),
            Some(comment),
        );
    }
    if let Some(reason) = preferred_semantic_summary_islands_reason(context) {
        return provisional_decompile_route(
            r2types::DecompileRouteKind::SummaryIslands,
            Some(reason),
            None,
        );
    }
    if let Some(reason) = preferred_semantic_structuring_reason(context) {
        return provisional_decompile_route(
            r2types::DecompileRouteKind::StructuredWorker,
            Some(reason),
            None,
        );
    }
    if let Some(reason) = preferred_semantic_linearization_reason(context) {
        return provisional_decompile_route(
            r2types::DecompileRouteKind::LinearWorker,
            Some(reason),
            None,
        );
    }
    if let Some(route) = context
        .function_facts
        .semantic_artifact()
        .and_then(semantic_route_from_artifact_plan)
        .filter(|_| context.has_renderable_semantic_claims())
    {
        return route;
    }
    if let Some(comment) =
        preferred_unrenderable_summary_fallback_comment(context.func_name, context.function_facts)
    {
        return provisional_decompile_route(
            r2types::DecompileRouteKind::FallbackComment,
            Some(comment.clone()),
            Some(comment),
        );
    }
    provisional_decompile_route(r2types::DecompileRouteKind::Standard, None, None)
}

pub(crate) fn decompile_route_decision(
    func_name: &str,
    function_facts: &FunctionFacts,
    prepared: Option<&SsaArtifact>,
    cfg_summary: &CFGRiskSummary,
) -> EngineRouteDecision {
    let route = semantic_route_plan(func_name, function_facts, cfg_summary);
    let plan = select_engine_plan(
        EngineRequestKind::Decompile,
        Some(&route),
        Some(function_facts),
    );
    let mut route = route;
    route.use_prepared_semantic_view = should_use_prepared_semantic_view(prepared, function_facts);
    EngineRouteDecision {
        request: EngineRequestKind::Decompile,
        plan,
        route,
    }
}

#[cfg(test)]
pub(crate) fn semantic_route_reason(route: &r2types::DecompileRouteFacts) -> Option<String> {
    route
        .reason
        .clone()
        .or_else(|| route.fallback_comment.clone())
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
            reason: Some("semantic summary retained as advisory type evidence".to_string()),
        };
    }

    EngineTypeRouteDecision {
        request: EngineRequestKind::Types,
        plan: select_engine_plan(EngineRequestKind::Types, None, Some(function_facts)),
        kind: EngineTypeRouteKind::FullWriteback,
        prefer_bounded_type_plan: false,
        reason: None,
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
        return crate::semantic_fallback_comment_for_facts(func_name, function_facts);
    }
    None
}

fn preferred_unrenderable_summary_fallback_comment(
    func_name: &str,
    function_facts: &FunctionFacts,
) -> Option<String> {
    let artifact = function_facts.semantic_artifact()?;
    if artifact.granularity != r2sym::ArtifactGranularity::SummaryOnly
        || artifact.diagnostics.skipped_large_cfg
        || !matches!(
            artifact.decompile_plan(),
            r2sym::DecompilePlan::NativeLinear { .. }
        )
    {
        return None;
    }
    let native = artifact.native_body()?;
    if native_body_has_renderable_worker_summary(native) {
        return None;
    }
    Some(
        crate::semantic_fallback_comment_for_facts(func_name, function_facts).unwrap_or_else(
            || {
                crate::artifact_guard_fallback_comment(
                    func_name,
                    "summary-only native linear artifact without renderable worker summary",
                )
            },
        ),
    )
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
        .semantic_report()
        .and_then(r2sym::SemanticArtifactReport::native_body)
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
    let Some(signature) = function_facts.type_facts().render_authorized_signature() else {
        return false;
    };
    let Some(native) = function_facts
        .semantic_report()
        .and_then(r2sym::SemanticArtifactReport::native_body)
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
