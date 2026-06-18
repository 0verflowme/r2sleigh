use std::collections::BTreeSet;

use r2il::R2ILBlock;
use r2ssa::CFGRiskSummary;
use r2types::FunctionFacts;
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
                direct_named_worker_summary_applicability_for_name(self.function_addr, alias)
                    .is_some()
                    || (has_summary_applicability(self.function_addr, alias)
                        && !is_anonymous_engine_route_name(alias))
            })
            .or_else(|| {
                self.aliases
                    .iter()
                    .find(|alias| has_summary_applicability(self.function_addr, alias))
            })
            .map(String::as_str)
            .unwrap_or_else(|| self.primary_name())
    }

    pub fn has_summary_family(&self) -> bool {
        self.name_candidates()
            .any(|name| has_summary_applicability(self.function_addr, name))
    }

    pub fn has_program_orchestrator_family(&self) -> bool {
        self.name_candidates().any(|name| {
            r2sym::has_program_orchestrator_summary_family(name)
                && has_summary_applicability(self.function_addr, name)
        })
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
    pub route: r2dec::SemanticRoutePlan,
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
    pub display_program_orchestrator_family: bool,
    pub canonical_program_orchestrator_family: bool,
    pub program_orchestrator_guarded: bool,
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct EngineNameRouteFacts {
    display_summary_family: bool,
    canonical_summary_family: bool,
    display_program_orchestrator_family: bool,
    canonical_program_orchestrator_family: bool,
    summary_family: bool,
    program_orchestrator_family: bool,
    prefer_full_named_worker: bool,
    direct_named_worker_guarded: bool,
    summary_probe_name: String,
}

fn engine_name_route_facts(identity: &EngineFunctionIdentity) -> EngineNameRouteFacts {
    let mut display_summary_family = false;
    let mut canonical_summary_family = false;
    let mut display_program_orchestrator_family = false;
    let mut canonical_program_orchestrator_family = false;
    let mut summary_family = false;
    let mut program_orchestrator_family = false;
    let mut prefer_full_named_worker = false;
    let mut direct_named_worker_guarded = false;
    let mut first_preferred_summary_name: Option<String> = None;
    let mut first_supported_summary_name: Option<String> = None;

    for name in identity.name_candidates() {
        let policy =
            r2sym::native_worker_summary_route_policy_for_name(identity.function_addr, name);
        let summary_route_backed = policy.has_route_certificate();
        let program_orchestrator = r2sym::has_program_orchestrator_summary_family(name);

        if name == identity.display_name {
            display_summary_family |= summary_route_backed;
            display_program_orchestrator_family |= program_orchestrator && summary_route_backed;
        }
        if name == identity.canonical_name {
            canonical_summary_family |= summary_route_backed;
            canonical_program_orchestrator_family |= program_orchestrator && summary_route_backed;
        }

        summary_family |= summary_route_backed;
        program_orchestrator_family |= program_orchestrator && summary_route_backed;
        prefer_full_named_worker |= policy.should_prefer_full();
        direct_named_worker_guarded |= policy.should_use_direct_summary();

        if summary_route_backed {
            first_supported_summary_name.get_or_insert_with(|| name.to_string());
            if first_preferred_summary_name.is_none()
                && (policy.should_use_direct_summary() || !is_anonymous_engine_route_name(name))
            {
                first_preferred_summary_name = Some(name.to_string());
            }
        }
    }

    let summary_probe_name = first_preferred_summary_name
        .or(first_supported_summary_name)
        .unwrap_or_else(|| identity.primary_name().to_string());

    EngineNameRouteFacts {
        display_summary_family,
        canonical_summary_family,
        display_program_orchestrator_family,
        canonical_program_orchestrator_family,
        summary_family,
        program_orchestrator_family,
        prefer_full_named_worker,
        direct_named_worker_guarded,
        summary_probe_name,
    }
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
    let name_facts = engine_name_route_facts(identity);
    let cfg_guard_reason = super::cfg_guard_reason(blocks);
    let op_count = blocks.iter().map(|block| block.ops.len()).sum::<usize>();
    let raw_cfg = raw_cfg_risk_summary_for_preprobe(blocks);
    let small_structural_worker_probe = raw_cfg.block_count > 0
        && raw_cfg.block_count <= 64
        && (raw_cfg.loop_count > 0
            || raw_cfg.back_edge_count > 0
            || raw_cfg.switch_block_count > 0);
    let program_orchestrator_guarded = name_facts.program_orchestrator_family
        && should_guard_program_orchestrator_decompile(blocks.len(), op_count);
    let skipped_large_cfg_guarded = !name_facts.prefer_full_named_worker
        && (cfg_guard_reason.is_some() || blocks.len() > 200 || op_count > 512);
    let named_worker_guarded = name_facts.summary_family
        && (name_facts.direct_named_worker_guarded
            || skipped_large_cfg_guarded
            || program_orchestrator_guarded)
        && (!name_facts.program_orchestrator_family || program_orchestrator_guarded);
    let block_guarded = named_worker_guarded || skipped_large_cfg_guarded;
    let summary_probe_needed = block_guarded
        || cfg_guard_reason.is_some()
        || name_facts.prefer_full_named_worker
        || small_structural_worker_probe;

    DecompileProbeDecision {
        op_count,
        cfg_guard_reason,
        display_summary_family: name_facts.display_summary_family,
        canonical_summary_family: name_facts.canonical_summary_family,
        display_program_orchestrator_family: name_facts.display_program_orchestrator_family,
        canonical_program_orchestrator_family: name_facts.canonical_program_orchestrator_family,
        program_orchestrator_guarded,
        named_worker_guarded,
        summary_probe_name: name_facts.summary_probe_name,
        summary_probe_needed,
        summary_probe_skipped_large_cfg: skipped_large_cfg_guarded,
        block_guarded,
    }
}

fn has_summary_applicability(function_addr: u64, name: &str) -> bool {
    r2sym::native_worker_summary_route_policy_for_name(function_addr, name).has_route_certificate()
}

pub fn should_use_direct_named_native_worker_decompile(function_name: &str) -> bool {
    direct_named_worker_summary_applicability_for_name(0, function_name).is_some()
}

pub(super) fn direct_named_worker_summary_applicability_for_identity(
    identity: &EngineFunctionIdentity,
) -> Option<r2sym::NativeWorkerSummaryApplicability> {
    identity.name_candidates().find_map(|name| {
        direct_named_worker_summary_applicability_for_name(identity.function_addr, name)
    })
}

fn direct_named_worker_summary_applicability_for_name(
    function_addr: u64,
    function_name: &str,
) -> Option<r2sym::NativeWorkerSummaryApplicability> {
    r2sym::direct_native_worker_summary_applicability_for_name(function_addr, function_name)
}

pub(super) fn should_prefer_full_decompile_for_named_worker(function_name: &str) -> bool {
    r2sym::native_worker_summary_route_policy_for_name(0, function_name).should_prefer_full()
}

pub fn should_use_direct_named_native_worker_type_projection(function_name: &str) -> bool {
    should_use_direct_named_native_worker_decompile(function_name)
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
