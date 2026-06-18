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
        let normalized = super::normalize_engine_route_name(alias);
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
                super::direct_named_worker_summary_applicability_for_name(self.function_addr, alias)
                    .is_some()
                    || (super::has_summary_applicability(self.function_addr, alias)
                        && !super::is_anonymous_engine_route_name(alias))
            })
            .or_else(|| {
                self.aliases
                    .iter()
                    .find(|alias| super::has_summary_applicability(self.function_addr, alias))
            })
            .map(String::as_str)
            .unwrap_or_else(|| self.primary_name())
    }

    pub fn has_summary_family(&self) -> bool {
        self.name_candidates()
            .any(|name| super::has_summary_applicability(self.function_addr, name))
    }

    pub fn has_program_orchestrator_family(&self) -> bool {
        self.name_candidates().any(|name| {
            r2sym::has_program_orchestrator_summary_family(name)
                && super::has_summary_applicability(self.function_addr, name)
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
