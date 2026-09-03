//! r2engine owns cross-crate analysis orchestration.
//!
//! Fact ownership stays in the lower crates: SSA in `r2ssa`, semantic artifacts
//! in `r2sym`, type facts in `r2types`, and rendering in `r2dec`. This crate is
//! the request-level scheduler boundary that decides which artifacts are
//! needed for a request. Analysis artifacts are built directly for each
//! source snapshot request.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs::OpenOptions;
use std::io::Write;
use std::sync::Arc;
use std::time::{Duration, Instant};

use r2il::R2ILBlock;
use r2ssa::{CFGRiskSummary, SsaArtifact};
use r2types::{
    FunctionFacts, FunctionTypeFacts, MetadataScalarKind, TypeHint, TypeWritebackPlan,
    merge_type_hint, type_hint_from_value_metadata,
};
use serde::{Deserialize, Serialize};

mod json;
mod policy;
mod program_cache;
pub use json::*;
pub use policy::*;
pub use program_cache::{
    PreparedRole, ProgramCacheStats, cache_function_artifact, cached_function_artifact,
    cached_function_fingerprint, clear_program_cache, program_cache_stats,
};

mod route;

pub use r2dec::{
    BindingMachineProjectionFailure, BindingObservationAudit, BindingObservationDomainAudit,
    BindingObservationJournalFailure, BindingShadowAuditFailure, BindingShadowAuditLedger,
    BindingShadowAuditOutcome, BindingShadowDomainAudit, DecompileRenderRefusal,
    EffectObligationAudit, EffectObligationDisposition, PlacementAudit, PlacementAuditRefusal,
};
pub use route::{
    DecompileProbeDecision, EngineDiagnostics, EngineFunctionIdentity, EnginePlan,
    EngineRequestKind, EngineRequestPlan, EngineRouteContext, EngineRouteDecision,
    EngineTypeRouteDecision, EngineTypeRouteKind, EngineTypedRouteDecision, cfg_guard_reason,
    cfg_guard_reason_from_summary, plan_type_request, prefer_symbolic_large_worker_decompile,
    select_engine_plan, semantic_artifact_needs_fallback_type_payload,
    semantic_or_cfg_prefers_bounded_type_plan, should_guard_program_orchestrator_decompile,
    should_use_prepared_semantic_view, type_cfg_allows_semantic_plan, type_cfg_bounded_reason,
    type_cfg_forces_bounded_plan, type_cfg_prefers_bounded_plan, type_route_decision,
};
use route::{decompile_probe_decision, decompile_route_decision};
#[cfg(test)]
use route::{plan_decompile_request, semantic_route_reason};
const MISSING_SOURCE_SNAPSHOT_REFUSAL: &str =
    "engine analysis requires an immutable source snapshot";

/// Immutable, source-owned interface facts for one exact lifted revision.
///
/// The engine only transports these facts into SSA. It does not infer a
/// revision identity or upgrade absent interface data into authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineSourceSnapshot {
    revision_identity: Box<[u8]>,
    function_interface: Option<r2ssa::SourceFunctionInterface>,
    machine_roles: r2ssa::SourceMachineRoles,
    call_site_interfaces: Box<[r2ssa::SourceCallSiteInterface]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EngineSourceSnapshotError {
    EmptyRevisionIdentity,
    FunctionRevisionMismatch,
    CallSiteRevisionMismatch,
    DuplicateCallSiteIdentity,
    DuplicateCallSiteLocation,
}

impl std::fmt::Display for EngineSourceSnapshotError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid engine source snapshot: {self:?}")
    }
}

impl std::error::Error for EngineSourceSnapshotError {}

impl EngineSourceSnapshot {
    pub fn new(
        revision_identity: impl Into<Vec<u8>>,
        function_interface: Option<r2ssa::SourceFunctionInterface>,
        call_site_interfaces: impl IntoIterator<Item = r2ssa::SourceCallSiteInterface>,
    ) -> Result<Self, EngineSourceSnapshotError> {
        Self::new_with_machine_roles(
            revision_identity,
            function_interface,
            r2ssa::SourceMachineRoles::default(),
            call_site_interfaces,
        )
    }

    pub fn new_with_machine_roles(
        revision_identity: impl Into<Vec<u8>>,
        function_interface: Option<r2ssa::SourceFunctionInterface>,
        machine_roles: r2ssa::SourceMachineRoles,
        call_site_interfaces: impl IntoIterator<Item = r2ssa::SourceCallSiteInterface>,
    ) -> Result<Self, EngineSourceSnapshotError> {
        let revision_identity = revision_identity.into();
        if revision_identity.is_empty() {
            return Err(EngineSourceSnapshotError::EmptyRevisionIdentity);
        }
        if function_interface
            .as_ref()
            .is_some_and(|interface| interface.revision_identity() != revision_identity)
        {
            return Err(EngineSourceSnapshotError::FunctionRevisionMismatch);
        }
        let call_site_interfaces = call_site_interfaces.into_iter().collect::<Vec<_>>();
        if call_site_interfaces
            .iter()
            .any(|interface| interface.revision_identity() != revision_identity)
        {
            return Err(EngineSourceSnapshotError::CallSiteRevisionMismatch);
        }
        let mut identities = BTreeSet::new();
        let mut locations = BTreeSet::new();
        for interface in &call_site_interfaces {
            let identity = interface.identity();
            if !identities.insert(identity) {
                return Err(EngineSourceSnapshotError::DuplicateCallSiteIdentity);
            }
            if !locations.insert((identity.block_addr(), identity.op_index())) {
                return Err(EngineSourceSnapshotError::DuplicateCallSiteLocation);
            }
        }
        Ok(Self {
            revision_identity: revision_identity.into_boxed_slice(),
            function_interface,
            machine_roles,
            call_site_interfaces: call_site_interfaces.into_boxed_slice(),
        })
    }

    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn function_interface(&self) -> Option<&r2ssa::SourceFunctionInterface> {
        self.function_interface.as_ref()
    }

    pub const fn machine_roles(&self) -> &r2ssa::SourceMachineRoles {
        &self.machine_roles
    }

    pub const fn call_site_interfaces(&self) -> &[r2ssa::SourceCallSiteInterface] {
        &self.call_site_interfaces
    }
}

pub fn compiled_semantic_info(artifact: &r2sym::SemanticArtifact) -> r2sym::CompiledSemanticInfo {
    r2sym::compiled_semantic_info(artifact)
}

pub fn direct_block_c_residual_comment(block_addr: u64) -> String {
    format!(
        "/* r2dec residual: block C output for 0x{block_addr:x} requires engine FunctionFacts route; direct C-like block decompile suppressed */"
    )
}

pub fn direct_block_ast_residual_json(block_addr: u64) -> String {
    let comment = format!(
        "r2dec residual: block AST for 0x{block_addr:x} requires engine FunctionFacts route; direct SSA op lowering suppressed"
    );
    let value = serde_json::json!([{ "Comment": comment }]);
    serde_json::to_string_pretty(&value).unwrap_or_else(|_| "[]".to_string())
}

pub fn type_writeback_mutation_kind_id(kind: r2types::TypeWritebackMutationKind) -> u32 {
    match kind {
        r2types::TypeWritebackMutationKind::Signature => TYPE_WRITEBACK_MUTATION_SIGNATURE_ID,
        r2types::TypeWritebackMutationKind::Callconv => TYPE_WRITEBACK_MUTATION_CALLCONV_ID,
        r2types::TypeWritebackMutationKind::Var => TYPE_WRITEBACK_MUTATION_VAR_ID,
        r2types::TypeWritebackMutationKind::VarRename => TYPE_WRITEBACK_MUTATION_VAR_RENAME_ID,
        r2types::TypeWritebackMutationKind::VarType => TYPE_WRITEBACK_MUTATION_VAR_TYPE_ID,
        r2types::TypeWritebackMutationKind::Xref => TYPE_WRITEBACK_MUTATION_XREF_ID,
        r2types::TypeWritebackMutationKind::Comment => TYPE_WRITEBACK_MUTATION_COMMENT_ID,
        r2types::TypeWritebackMutationKind::Flag => TYPE_WRITEBACK_MUTATION_FLAG_ID,
        r2types::TypeWritebackMutationKind::TypeDecl => TYPE_WRITEBACK_MUTATION_TYPE_DECL_ID,
        r2types::TypeWritebackMutationKind::TypeLink => TYPE_WRITEBACK_MUTATION_TYPE_LINK_ID,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineAnalysisDepth {
    Basic,
    Default,
    Aggressive,
}

impl EngineAnalysisDepth {
    pub fn from_radare2_depth(depth: u32) -> Self {
        match depth {
            RADARE2_ANALYSIS_DEPTH_BASIC => Self::Basic,
            RADARE2_ANALYSIS_DEPTH_AGGRESSIVE => Self::Aggressive,
            _ => Self::Default,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineAnalysisMode {
    Fast,
    Balanced,
    Full,
}

impl EngineAnalysisMode {
    pub const fn level(self) -> u8 {
        match self {
            Self::Fast => 0,
            Self::Balanced => 1,
            Self::Full => 2,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineTypeWritebackMode {
    Off,
    Balanced,
    Aggressive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineAutoCallbackKind {
    AnalyzeFunction,
    DataRefs,
    PostAnalysisTaint,
    PostAnalysisXref,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineAutoCallbackRefusalReason {
    Allowed,
    ModeNotFull,
    TooManyBlocks,
    TooLarge,
    TooCostly,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineAutoCallbackMetrics {
    pub basic_block_count: u32,
    pub cost: u32,
    pub linear_size: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineAutoCallbackPlan {
    pub allowed: bool,
    pub kind: EngineAutoCallbackKind,
    pub reason: EngineAutoCallbackRefusalReason,
}

impl EngineTypeWritebackMode {
    pub const fn level(self) -> u8 {
        match self {
            Self::Off => 0,
            Self::Balanced => 1,
            Self::Aggressive => 2,
        }
    }
}

pub fn type_writeback_apply_policy_for_mode(
    mode: EngineTypeWritebackMode,
) -> r2types::TypeWritebackApplyPolicy {
    match mode {
        EngineTypeWritebackMode::Off => r2types::TypeWritebackApplyPolicy::off(),
        EngineTypeWritebackMode::Balanced => r2types::TypeWritebackApplyPolicy::balanced(),
        EngineTypeWritebackMode::Aggressive => r2types::TypeWritebackApplyPolicy::aggressive(),
    }
}

fn type_writeback_authority_report_for_policy(
    analysis: &r2types::TypeWritebackAnalysis,
    budget: r2types::TypeWritebackMutationBudget,
    apply_policy: r2types::TypeWritebackApplyPolicy,
) -> r2types::TypeWritebackAuthorityReport {
    analysis.authority_report(budget, apply_policy)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EngineTypeWritebackPlanReport {
    plan: TypeWritebackPlan,
    authority_report: r2types::TypeWritebackAuthorityReport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineTypeWritebackPayload {
    /// The target's pointer width, carried so the JSON edge can spell the
    /// plan's types without guessing which target they were recovered for.
    pub ptr_bits: u32,
    pub signature: r2types::InferredSignature,
    pub signature_render_authorized: bool,
    pub signature_writeback_authorized: bool,
    pub signature_action_decision: r2types::SignatureWritebackActionDecision,
    pub callconv_action_decision: r2types::SignatureWritebackActionDecision,
    pub signature_certificate_sources: Vec<String>,
    pub signature_writeback_refusal: Option<String>,
    pub var_type_candidates: Vec<r2types::VarTypeCandidate>,
    pub var_rename_candidates: Vec<r2types::VarRenameCandidate>,
    pub external_struct_names: Vec<String>,
    pub field_access_certificate_names: Vec<String>,
    pub fact_counts: EngineTypeWritebackFactCounts,
    pub param_home_stack_slot_offsets: Vec<i64>,
    pub certified_stack_slot_offsets: Vec<i64>,
    pub struct_decls: Vec<r2types::StructDeclCandidate>,
    pub global_type_links: Vec<r2types::GlobalTypeLinkCandidate>,
    pub plans: r2types::AnalysisPlans,
    pub assumptions: r2ssa::AssumptionSet,
    pub assumption_usage: r2types::AssumptionUsageReport,
    pub mutation_plan: r2types::TypeWritebackMutationPlan,
    pub diagnostics: r2types::TypeWritebackDiagnostics,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineTypeWritebackFactCounts {
    pub register_params: usize,
    pub stack_slots: usize,
    pub param_home_stack_slots: usize,
    pub hidden_home_bindings: usize,
    pub field_access_certificates: usize,
    pub array_index_certificates: usize,
    pub scalar_array_render_candidates: usize,
    pub render_member_accesses: usize,
    pub render_array_accesses: usize,
    pub certified_expressions: usize,
    pub certified_parameters: usize,
    pub certified_stack_slots: usize,
    pub certified_memory_accesses: usize,
    pub certified_returns: usize,
    pub certified_control_domains: usize,
    pub incomplete_control_domains: usize,
}

impl EngineTypeWritebackFactCountsJson {
    pub fn is_empty(&self) -> bool {
        self.register_params == 0
            && self.stack_slots == 0
            && self.param_home_stack_slots == 0
            && self.hidden_home_bindings == 0
            && self.field_access_certificates == 0
            && self.array_index_certificates == 0
            && self.scalar_array_render_candidates == 0
            && self.render_member_accesses == 0
            && self.render_array_accesses == 0
            && self.certified_expressions == 0
            && self.certified_parameters == 0
            && self.certified_stack_slots == 0
            && self.certified_memory_accesses == 0
            && self.certified_returns == 0
            && self.certified_control_domains == 0
            && self.incomplete_control_domains == 0
    }
}

#[derive(Debug, Clone)]
pub struct EngineFunctionAnalysisReportPayload {
    pub function_name: String,
    pub function_addr: u64,
    pub cfg_summary: CFGRiskSummary,
    pub plans: r2types::AnalysisPlans,
    pub assumptions: r2ssa::AssumptionSet,
    pub assumption_usage: r2types::AssumptionUsageReport,
    pub semantic_report: Option<r2sym::SemanticArtifactReport>,
    pub compiled_semantics: Option<r2sym::CompiledSemanticInfo>,
    pub semantic_build_plan: Option<r2sym::ArtifactBuildPlan>,
    pub semantic_route: Option<r2types::DecompileRouteFacts>,
    pub summary_diagnostics: Option<r2ssa::InterprocSummaryDiagnostics>,
    pub type_writeback: EngineTypeWritebackPayload,
    pub prefer_bounded_type_plan: bool,
    pub callsite_count: usize,
    pub current_summary: Option<r2ssa::FunctionSemanticSummary>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EnginePhase {
    SnapshotContext,
    LiftNormalize,
    Ssa,
    Obligations,
    Symbolic,
    Types,
    Certification,
    Structuring,
    Normalization,
    Rendering,
    FfiConversion,
}

impl EnginePhase {
    pub const ALL: [Self; 11] = [
        Self::SnapshotContext,
        Self::LiftNormalize,
        Self::Ssa,
        Self::Obligations,
        Self::Symbolic,
        Self::Types,
        Self::Certification,
        Self::Structuring,
        Self::Normalization,
        Self::Rendering,
        Self::FfiConversion,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SnapshotContext => "snapshot_context",
            Self::LiftNormalize => "lift_normalize",
            Self::Ssa => "ssa",
            Self::Obligations => "obligations",
            Self::Symbolic => "symbolic",
            Self::Types => "types",
            Self::Certification => "certification",
            Self::Structuring => "structuring",
            Self::Normalization => "normalization",
            Self::Rendering => "rendering",
            Self::FfiConversion => "ffi_conversion",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EnginePhaseStatus {
    NotExecuted,
    Executed,
    /// The phase executed inside the elapsed span attributed to another
    /// boundary. Its zero duration means "not separately measured", not free.
    Folded,
    Refused,
}

impl EnginePhaseTimingJson {
    fn not_executed(phase: EnginePhase) -> Self {
        Self {
            phase,
            status: EnginePhaseStatus::NotExecuted,
            elapsed_us: 0,
        }
    }
}

fn empty_engine_phase_timings() -> Vec<EnginePhaseTimingJson> {
    EnginePhase::ALL
        .into_iter()
        .map(EnginePhaseTimingJson::not_executed)
        .collect()
}

fn normalize_engine_phase_timings(
    timings: Vec<EnginePhaseTimingJson>,
) -> Vec<EnginePhaseTimingJson> {
    let mut normalized = empty_engine_phase_timings();
    for timing in timings {
        if let Some(slot) = normalized
            .iter_mut()
            .find(|slot| slot.phase == timing.phase)
        {
            *slot = timing;
        }
    }
    normalized
}

impl std::ops::Deref for EngineInferredTypeWritebackJson {
    type Target = EngineTypeWritebackJsonCore;

    fn deref(&self) -> &Self::Target {
        &self.core
    }
}

fn type_writeback_plan_report_for_policy(
    analysis: &r2types::TypeWritebackAnalysis,
    budget: r2types::TypeWritebackMutationBudget,
    apply_policy: r2types::TypeWritebackApplyPolicy,
) -> EngineTypeWritebackPlanReport {
    let authority_report =
        type_writeback_authority_report_for_policy(analysis, budget, apply_policy);
    EngineTypeWritebackPlanReport {
        plan: analysis.plan().clone(),
        authority_report,
    }
}

fn type_writeback_payload_from_plan_report(
    plan_report: EngineTypeWritebackPlanReport,
    function_facts: &FunctionFacts,
    budget: r2types::TypeWritebackMutationBudget,
) -> EngineTypeWritebackPayload {
    let EngineTypeWritebackPlanReport {
        plan,
        authority_report,
    } = plan_report;
    let r2types::TypeWritebackAuthorityReport {
        mutation_plan,
        signature_render_authorized,
        signature_writeback,
        signature_action_decision,
        callconv_action_decision,
        warnings,
    } = authority_report;
    let diagnostics = r2types::TypeWritebackDiagnostics {
        conflicts: plan.diagnostics.conflicts,
        warnings,
        solver_warnings: plan.diagnostics.solver_warnings,
    };
    EngineTypeWritebackPayload {
        ptr_bits: plan.ptr_bits,
        signature: plan.signature,
        signature_render_authorized,
        signature_writeback_authorized: signature_writeback.authorized,
        signature_action_decision,
        callconv_action_decision,
        signature_certificate_sources: signature_writeback.sources,
        signature_writeback_refusal: signature_writeback.refusal,
        var_type_candidates: plan.var_type_candidates,
        var_rename_candidates: plan.var_rename_candidates,
        external_struct_names: type_writeback_external_struct_names(function_facts),
        field_access_certificate_names: type_writeback_field_access_certificate_names(
            function_facts,
        ),
        fact_counts: type_writeback_fact_counts(function_facts),
        param_home_stack_slot_offsets: type_writeback_param_home_stack_slot_offsets(function_facts),
        certified_stack_slot_offsets: type_writeback_certified_stack_slot_offsets(function_facts),
        struct_decls: plan
            .struct_decls
            .into_iter()
            .take(budget.max_type_decls)
            .collect(),
        global_type_links: plan
            .global_type_links
            .into_iter()
            .take(budget.global_max_links)
            .collect(),
        plans: function_facts.plans().clone(),
        assumptions: function_facts.assumptions().clone(),
        assumption_usage: function_facts.assumption_usage().clone(),
        mutation_plan,
        diagnostics,
    }
}

fn type_writeback_payload_for_policy(
    analysis: &r2types::TypeWritebackAnalysis,
    budget: r2types::TypeWritebackMutationBudget,
    apply_policy: r2types::TypeWritebackApplyPolicy,
) -> EngineTypeWritebackPayload {
    let plan_report = type_writeback_plan_report_for_policy(analysis, budget, apply_policy);
    type_writeback_payload_from_plan_report(plan_report, analysis.function_facts(), budget)
}

pub fn type_writeback_payload_from_analysis_response(
    response: &EngineTypeAnalysisResponse,
    budget: r2types::TypeWritebackMutationBudget,
    apply_policy: r2types::TypeWritebackApplyPolicy,
) -> EngineTypeWritebackPayload {
    type_writeback_payload_for_policy(response.type_analysis(), budget, apply_policy)
}

fn semantic_granularity_label(granularity: r2sym::ArtifactGranularity) -> &'static str {
    match granularity {
        r2sym::ArtifactGranularity::WholeFunction => "whole_function",
        r2sym::ArtifactGranularity::Regioned => "regioned",
        r2sym::ArtifactGranularity::SummaryOnly => "summary_only",
    }
}

pub fn function_analysis_report_payload_from_type_response(
    function_name: String,
    function_addr: u64,
    response: EngineTypeAnalysisResponse,
    budget: r2types::TypeWritebackMutationBudget,
    apply_policy: r2types::TypeWritebackApplyPolicy,
) -> EngineFunctionAnalysisReportPayload {
    let type_writeback =
        type_writeback_payload_from_analysis_response(&response, budget, apply_policy);
    let function_facts = response.function_facts();
    let semantic_owner = function_facts.semantic_artifact();
    let semantic_build_plan = semantic_owner.map(|artifact| artifact.report().build_plan());
    let compiled_semantics = semantic_owner.map(compiled_semantic_info);
    let semantic_report = semantic_owner.map(|artifact| artifact.report().clone());
    let semantic_route = Some(response.decompile_route().clone());
    let summary_diagnostics = function_facts.summary_view().diagnostics().cloned();
    EngineFunctionAnalysisReportPayload {
        function_name,
        function_addr,
        cfg_summary: *response.cfg_summary(),
        plans: function_facts.plans().clone(),
        assumptions: function_facts.assumptions().clone(),
        assumption_usage: function_facts.assumption_usage().clone(),
        semantic_report,
        compiled_semantics,
        semantic_build_plan,
        semantic_route,
        summary_diagnostics,
        type_writeback,
        prefer_bounded_type_plan: response.route_decision().prefer_bounded_type_plan,
        callsite_count: response.callsite_count(),
        current_summary: response.current_summary().cloned(),
    }
}

pub fn type_writeback_fact_counts(function_facts: &FunctionFacts) -> EngineTypeWritebackFactCounts {
    let type_facts = function_facts.type_facts();
    let render = function_facts.render();
    EngineTypeWritebackFactCounts {
        register_params: type_facts.register_params.len(),
        stack_slots: type_facts.stack_slots.len(),
        param_home_stack_slots: type_facts
            .stack_slots
            .values()
            .filter(|slot| matches!(slot.role, r2types::ExternalStackSlotRole::ParamHome))
            .count(),
        hidden_home_bindings: type_facts
            .visible_bindings
            .iter()
            .filter(|binding| matches!(binding.kind, r2types::VisibleBindingKind::HiddenHome))
            .count(),
        field_access_certificates: type_facts.field_access_certificates.len(),
        array_index_certificates: type_facts.array_index_certificates.len(),
        scalar_array_render_candidates: type_facts.scalar_array_render_candidates.len(),
        render_member_accesses: render
            .map(|facts| facts.member_accesses_by_op.values().map(Vec::len).sum())
            .unwrap_or(0),
        render_array_accesses: render
            .map(|facts| facts.array_accesses_by_op.values().map(Vec::len).sum())
            .unwrap_or(0),
        certified_expressions: render.map(|facts| facts.certified_exprs.len()).unwrap_or(0),
        certified_parameters: render
            .map(|facts| {
                facts
                    .certified_entities
                    .values()
                    .filter(|entity| matches!(entity, r2types::CertifiedEntity::Parameter { .. }))
                    .count()
            })
            .unwrap_or(0),
        certified_stack_slots: render
            .map(|facts| {
                facts
                    .certified_entities
                    .values()
                    .filter(|entity| matches!(entity, r2types::CertifiedEntity::StackSlot { .. }))
                    .count()
            })
            .unwrap_or(0),
        certified_memory_accesses: render
            .map(|facts| {
                facts
                    .certified_effects
                    .values()
                    .filter(|effect| {
                        matches!(
                            effect.kind(),
                            r2types::CertifiedEffectKind::MemoryRead
                                | r2types::CertifiedEffectKind::MemoryWrite
                        )
                    })
                    .count()
            })
            .unwrap_or(0),
        certified_returns: render
            .map(|facts| {
                facts
                    .certified_effects
                    .values()
                    .filter(|effect| effect.kind() == r2types::CertifiedEffectKind::Return)
                    .count()
            })
            .unwrap_or(0),
        certified_control_domains: function_facts
            .control()
            .map_or(0, |facts| facts.control_domains.domains.len()),
        incomplete_control_domains: function_facts.control().map_or(0, |facts| {
            facts
                .control_domains
                .domains
                .values()
                .filter(|domain| !domain.complete)
                .count()
        }),
    }
}

pub fn type_writeback_param_home_stack_slot_offsets(function_facts: &FunctionFacts) -> Vec<i64> {
    let mut offsets = function_facts
        .type_facts()
        .stack_slots
        .iter()
        .filter_map(|(slot_key, slot)| {
            matches!(slot.role, r2types::ExternalStackSlotRole::ParamHome)
                .then_some(slot_key.offset)
        })
        .collect::<Vec<_>>();
    offsets.sort_unstable();
    offsets.dedup();
    offsets
}

pub fn type_writeback_certified_stack_slot_offsets(function_facts: &FunctionFacts) -> Vec<i64> {
    let mut offsets = function_facts
        .render()
        .map(|render| {
            render
                .stack_slots()
                .map(|(_, _, offset, _)| offset)
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    offsets.sort_unstable();
    offsets.dedup();
    offsets
}

pub fn type_writeback_external_struct_names(function_facts: &FunctionFacts) -> Vec<String> {
    let mut names = function_facts
        .type_facts()
        .external_type_db
        .structs
        .values()
        .map(|st| st.name.clone())
        .collect::<Vec<_>>();
    names.sort();
    names.dedup();
    names
}

pub fn type_writeback_field_access_certificate_names(
    function_facts: &FunctionFacts,
) -> Vec<String> {
    let mut names = function_facts
        .type_facts()
        .field_access_certificates
        .iter()
        .map(|cert| {
            format!(
                "arg{}+0x{:x}:{}",
                cert.slot, cert.field_offset, cert.field_name
            )
        })
        .collect::<Vec<_>>();
    names.sort();
    names.dedup();
    names
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineAnalysisPolicy {
    pub mode: EngineAnalysisMode,
    pub type_writeback_mode: EngineTypeWritebackMode,
    pub type_interproc_max_iters: usize,
    pub type_max_blocks: usize,
    pub type_global_max_links: usize,
    pub type_max_decls: usize,
    pub type_max_mutations: usize,
}

pub fn analysis_policy_for_depth(depth: EngineAnalysisDepth) -> EngineAnalysisPolicy {
    match depth {
        EngineAnalysisDepth::Basic => EngineAnalysisPolicy {
            mode: EngineAnalysisMode::Fast,
            type_writeback_mode: EngineTypeWritebackMode::Off,
            type_interproc_max_iters: 1,
            type_max_blocks: 96,
            type_global_max_links: 8,
            type_max_decls: 8,
            type_max_mutations: 32,
        },
        EngineAnalysisDepth::Default => EngineAnalysisPolicy {
            mode: EngineAnalysisMode::Balanced,
            type_writeback_mode: EngineTypeWritebackMode::Balanced,
            type_interproc_max_iters: 4,
            type_max_blocks: 200,
            type_global_max_links: 32,
            type_max_decls: 32,
            type_max_mutations: 128,
        },
        EngineAnalysisDepth::Aggressive => EngineAnalysisPolicy {
            mode: EngineAnalysisMode::Full,
            type_writeback_mode: EngineTypeWritebackMode::Aggressive,
            type_interproc_max_iters: 12,
            type_max_blocks: 500,
            type_global_max_links: 128,
            type_max_decls: 64,
            type_max_mutations: 512,
        },
    }
}

pub fn analysis_policy_for_radare2_depth(depth: u32) -> EngineAnalysisPolicy {
    analysis_policy_for_depth(EngineAnalysisDepth::from_radare2_depth(depth))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnginePostAnalysisPlan {
    pub policy: EngineAnalysisPolicy,
    pub function_count: usize,
    pub post_budget_us: u64,
    pub xref_enabled: bool,
    pub taint_enabled: bool,
    pub signature_writeback_enabled: bool,
    pub type_writeback_enabled: bool,
    pub semantic_comments_enabled: bool,
    pub signature_verify_enabled: bool,
    pub balanced_focus_only: bool,
    pub taint_focus_only: bool,
    pub signature_writeback_focus_only: bool,
    pub type_writeback_focus_only: bool,
}

pub fn post_analysis_plan_for_policy(
    policy: EngineAnalysisPolicy,
    function_count: usize,
) -> EnginePostAnalysisPlan {
    let post_budget_us = match policy.mode {
        EngineAnalysisMode::Fast => POST_ANALYSIS_FAST_BUDGET_USEC,
        EngineAnalysisMode::Balanced => POST_ANALYSIS_BALANCED_BUDGET_USEC,
        EngineAnalysisMode::Full => POST_ANALYSIS_AGGRESSIVE_BUDGET_USEC,
    };
    let xref_enabled = policy.mode.level() >= EngineAnalysisMode::Balanced.level();
    let taint_enabled = policy.mode == EngineAnalysisMode::Full;
    let signature_writeback_enabled = policy.mode.level() >= EngineAnalysisMode::Balanced.level();
    let type_writeback_enabled =
        signature_writeback_enabled && policy.type_writeback_mode != EngineTypeWritebackMode::Off;
    let balanced_focus_only = policy.mode == EngineAnalysisMode::Balanced;

    EnginePostAnalysisPlan {
        policy,
        function_count,
        post_budget_us,
        xref_enabled,
        taint_enabled,
        signature_writeback_enabled,
        type_writeback_enabled,
        semantic_comments_enabled: false,
        signature_verify_enabled: false,
        balanced_focus_only,
        taint_focus_only: taint_enabled && function_count > TAINT_GLOBAL_MAX_FUNCTIONS,
        signature_writeback_focus_only: signature_writeback_enabled
            && (balanced_focus_only || function_count > SIGNATURE_WRITEBACK_GLOBAL_MAX_FUNCTIONS),
        type_writeback_focus_only: type_writeback_enabled
            && (balanced_focus_only || function_count > TYPE_WRITEBACK_GLOBAL_MAX_FUNCTIONS),
    }
}

pub fn post_analysis_plan_for_radare2_depth(
    depth: u32,
    function_count: usize,
) -> EnginePostAnalysisPlan {
    post_analysis_plan_for_policy(analysis_policy_for_radare2_depth(depth), function_count)
}

pub fn auto_callback_plan_for_policy(
    policy: EngineAnalysisPolicy,
    kind: EngineAutoCallbackKind,
    metrics: EngineAutoCallbackMetrics,
) -> EngineAutoCallbackPlan {
    let min_mode = match kind {
        EngineAutoCallbackKind::PostAnalysisXref => EngineAnalysisMode::Balanced,
        EngineAutoCallbackKind::AnalyzeFunction
        | EngineAutoCallbackKind::DataRefs
        | EngineAutoCallbackKind::PostAnalysisTaint => EngineAnalysisMode::Full,
    };
    let reason = if policy.mode.level() < min_mode.level() {
        EngineAutoCallbackRefusalReason::ModeNotFull
    } else if metrics.basic_block_count > AUTO_CALLBACK_MAX_BLOCKS {
        EngineAutoCallbackRefusalReason::TooManyBlocks
    } else if metrics.linear_size > AUTO_CALLBACK_MAX_LINEAR_SIZE {
        EngineAutoCallbackRefusalReason::TooLarge
    } else if metrics.cost > AUTO_CALLBACK_MAX_COST {
        EngineAutoCallbackRefusalReason::TooCostly
    } else {
        EngineAutoCallbackRefusalReason::Allowed
    };

    EngineAutoCallbackPlan {
        allowed: reason == EngineAutoCallbackRefusalReason::Allowed,
        kind,
        reason,
    }
}

pub fn auto_callback_plan_for_radare2_depth(
    depth: u32,
    kind: EngineAutoCallbackKind,
    metrics: EngineAutoCallbackMetrics,
) -> EngineAutoCallbackPlan {
    auto_callback_plan_for_policy(analysis_policy_for_radare2_depth(depth), kind, metrics)
}

pub fn engine_normalized_arch_name(arch: Option<&r2il::ArchSpec>) -> Option<String> {
    let arch = arch?;
    let family = r2ssa::MachineArchitectureFamily::from_arch_spec(Some(arch));
    Some(
        match family {
            r2ssa::MachineArchitectureFamily::X86 => "x86",
            r2ssa::MachineArchitectureFamily::X86_64 => "x86-64",
            r2ssa::MachineArchitectureFamily::Arm => "arm",
            r2ssa::MachineArchitectureFamily::AArch64 => "aarch64",
            r2ssa::MachineArchitectureFamily::RiscV32 => "riscv32",
            r2ssa::MachineArchitectureFamily::RiscV64 => "riscv64",
            r2ssa::MachineArchitectureFamily::Mips32 => "mips",
            r2ssa::MachineArchitectureFamily::Mips64 => "mips64",
            r2ssa::MachineArchitectureFamily::PowerPc32 => "powerpc",
            r2ssa::MachineArchitectureFamily::PowerPc64 => "powerpc64",
            r2ssa::MachineArchitectureFamily::Unknown => return Some(arch.name.clone()),
        }
        .to_string(),
    )
}

pub fn engine_arch_target(arch: Option<&r2il::ArchSpec>) -> (String, u32) {
    let arch_name = engine_normalized_arch_name(arch).unwrap_or_else(|| "unknown".to_string());
    let ptr_bits = arch.map(engine_effective_ptr_bits).unwrap_or(64);
    (arch_name, ptr_bits)
}

pub fn engine_effective_ptr_bits(arch: &r2il::ArchSpec) -> u32 {
    engine_effective_addr_size_bytes(arch).saturating_mul(8)
}

fn engine_effective_addr_size_bytes(arch: &r2il::ArchSpec) -> u32 {
    if arch.addr_size > 1 {
        return arch.addr_size;
    }

    if let Some(pc_size) = arch
        .registers
        .iter()
        .find(|reg| {
            matches!(
                reg.name.to_ascii_lowercase().as_str(),
                "pc" | "ip" | "eip" | "rip"
            )
        })
        .map(|reg| reg.size)
        .filter(|size| *size > 1)
    {
        return pc_size;
    }

    if let Some(default_size) = arch
        .spaces
        .iter()
        .find(|space| space.is_default && space.addr_size > 1)
        .map(|space| space.addr_size)
    {
        return default_size;
    }

    arch.spaces
        .iter()
        .map(|space| space.addr_size)
        .max()
        .filter(|size| *size > 1)
        .unwrap_or(arch.addr_size.max(1))
}

fn metadata_scalar_kind_from_r2il(kind: r2il::ScalarKind) -> MetadataScalarKind {
    match kind {
        r2il::ScalarKind::Bool => MetadataScalarKind::Bool,
        r2il::ScalarKind::SignedInt => MetadataScalarKind::SignedInt,
        r2il::ScalarKind::UnsignedInt => MetadataScalarKind::UnsignedInt,
        r2il::ScalarKind::Float => MetadataScalarKind::Float,
        r2il::ScalarKind::Bitvector => MetadataScalarKind::Bitvector,
        r2il::ScalarKind::Unknown => MetadataScalarKind::Unknown,
    }
}

fn metadata_type_hint_for_varnode(vn: &r2il::Varnode) -> Option<TypeHint> {
    let meta = vn.meta.as_ref()?;
    let pointer_like = meta
        .pointer_hint
        .is_some_and(|hint| !matches!(hint, r2il::PointerHint::Unknown));
    let scalar_kind = meta.scalar_kind.map(metadata_scalar_kind_from_r2il);

    type_hint_from_value_metadata(pointer_like, scalar_kind, vn.size)
}

pub fn collect_register_type_hints_with_names<F>(
    r2il_blocks: &[R2ILBlock],
    mut register_name: F,
) -> HashMap<String, TypeHint>
where
    F: FnMut(&r2il::Varnode) -> Option<String>,
{
    let mut hints = HashMap::new();

    let mut visit = |vn: &r2il::Varnode| {
        if !vn.is_register() {
            return;
        }
        let Some(hint) = metadata_type_hint_for_varnode(vn) else {
            return;
        };
        let Some(name) = register_name(vn) else {
            return;
        };

        merge_type_hint(&mut hints, name.to_ascii_lowercase(), hint);
    };

    for block in r2il_blocks {
        for op in &block.ops {
            if let Some(vn) = op.output() {
                visit(vn);
            }
            for vn in op.inputs() {
                visit(vn);
            }
        }
    }

    hints
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EngineRenderTarget {
    pub arch_name: String,
    pub ptr_bits: u32,
}

impl Default for EngineRenderTarget {
    fn default() -> Self {
        Self::for_arch_name("x86-64", 64)
    }
}

impl EngineRenderTarget {
    pub fn for_arch_name(arch_name: &str, ptr_bits: u32) -> Self {
        let arch_name = match (arch_name.to_ascii_lowercase().as_str(), ptr_bits) {
            ("x86_64" | "x64" | "amd64", _) => "x86-64".to_string(),
            ("x86-64", _) => "x86-64".to_string(),
            ("x86-32" | "i386" | "i686", _) => "x86".to_string(),
            ("x86", _) => "x86".to_string(),
            _ => arch_name.to_string(),
        };
        Self {
            arch_name,
            ptr_bits,
        }
    }

    pub fn for_arch(arch: Option<&r2il::ArchSpec>) -> (String, u32, Self) {
        let (arch_name, ptr_bits) = engine_arch_target(arch);
        let target = Self::for_arch_name(&arch_name, ptr_bits);
        (arch_name, ptr_bits, target)
    }

    pub fn for_arch_with_ptr_bits(arch: Option<&r2il::ArchSpec>, ptr_bits: u32) -> (String, Self) {
        let arch_name = engine_normalized_arch_name(arch).unwrap_or_else(|| "unknown".to_string());
        let target = Self::for_arch_name(&arch_name, ptr_bits);
        (arch_name, target)
    }

    fn for_prepared(source: &SsaArtifact) -> Option<Self> {
        let memory = source.machine_context().memory_model();
        if !memory.is_available() || !memory.is_coherent() {
            return None;
        }
        let ptr_bits = memory.default_address_bits();
        if ptr_bits == 0 {
            return None;
        }
        let (arch_name, expected_bits) = match source.machine_context().architecture_family() {
            r2ssa::MachineArchitectureFamily::X86 => ("x86", 32),
            r2ssa::MachineArchitectureFamily::X86_64 => ("x86-64", 64),
            r2ssa::MachineArchitectureFamily::Arm => ("arm", 32),
            r2ssa::MachineArchitectureFamily::AArch64 => ("aarch64", 64),
            r2ssa::MachineArchitectureFamily::RiscV32 => ("riscv32", 32),
            r2ssa::MachineArchitectureFamily::RiscV64 => ("riscv64", 64),
            r2ssa::MachineArchitectureFamily::Mips32 => ("mips", 32),
            r2ssa::MachineArchitectureFamily::Mips64 => ("mips64", 64),
            r2ssa::MachineArchitectureFamily::PowerPc32 => ("powerpc", 32),
            r2ssa::MachineArchitectureFamily::PowerPc64 => ("powerpc64", 64),
            r2ssa::MachineArchitectureFamily::Unknown => return None,
        };
        if ptr_bits != expected_bits {
            return None;
        }
        Some(Self::for_arch_name(arch_name, ptr_bits))
    }

    fn to_decompiler_config(&self) -> r2dec::DecompilerConfig {
        r2dec::DecompilerConfig::for_arch_name(&self.arch_name, self.ptr_bits)
    }
}

#[derive(Debug, Clone)]
pub struct EngineMetrics {
    pub planning_time: Duration,
    pub ssa_time: Duration,
    pub semantic_time: Duration,
    pub type_time: Duration,
    pub render_time: Duration,
    /// Stable, complete phase inventory. A phase which this engine boundary
    /// did not execute is retained with `NotExecuted` status and zero time.
    pub phase_timings: Vec<EnginePhaseTimingJson>,
}

impl Default for EngineMetrics {
    fn default() -> Self {
        Self {
            planning_time: Duration::default(),
            ssa_time: Duration::default(),
            semantic_time: Duration::default(),
            type_time: Duration::default(),
            render_time: Duration::default(),
            phase_timings: empty_engine_phase_timings(),
        }
    }
}

impl EngineMetrics {
    fn record_phase(&mut self, phase: EnginePhase, status: EnginePhaseStatus, elapsed: Duration) {
        let elapsed_us = elapsed.as_micros().min(u128::from(u64::MAX)) as u64;
        let timing = self
            .phase_timings
            .iter_mut()
            .find(|timing| timing.phase == phase)
            .expect("engine metrics must contain every stable phase");
        timing.status = status;
        timing.elapsed_us = elapsed_us;
    }

    fn refuse_from(&mut self, phase: EnginePhase) {
        let Some(start) = self
            .phase_timings
            .iter()
            .position(|timing| timing.phase == phase)
        else {
            return;
        };
        for timing in &mut self.phase_timings[start..] {
            if timing.status == EnginePhaseStatus::NotExecuted {
                timing.status = EnginePhaseStatus::Refused;
            }
        }
    }

    fn record_folded_if_not_executed(&mut self, phase: EnginePhase) {
        if self
            .phase_timings
            .iter()
            .any(|timing| timing.phase == phase && timing.status == EnginePhaseStatus::NotExecuted)
        {
            self.record_phase(phase, EnginePhaseStatus::Folded, Duration::default());
        }
    }
}

#[derive(Debug, Clone)]
pub struct EngineAnalysis {
    ssa_func: Arc<SsaArtifact>,
}

impl EngineAnalysis {
    /// Construct an engine-owned analysis from an already prepared SSA owner.
    pub(crate) fn from_prepared_ssa(ssa_func: Arc<SsaArtifact>) -> Self {
        Self { ssa_func }
    }

    /// Borrow the immutable prepared SSA consumed by this analysis.
    pub fn ssa_func(&self) -> &SsaArtifact {
        self.ssa_func.as_ref()
    }

    fn from_trusted_ssa(trusted: &r2ssa::TrustedSsaArtifact) -> Self {
        Self {
            ssa_func: trusted.shared_artifact(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineRuntimeMaterializedSource {
    pub addr: u64,
    pub size: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineInterprocTargetSkipReason {
    Imported,
    SummaryModeled,
    Unmaterialized,
    OverBudget,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineInterprocTargetMetrics {
    pub basic_block_count: u32,
    pub cost: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineInterprocTargetInput {
    pub direct_target: u64,
    /// Advisory presentation/debug metadata; never role or linkage authority.
    pub name: Option<String>,
    pub linkage: r2ssa::FunctionSemanticLinkage,
    pub semantic_summary: Option<r2ssa::FunctionSemanticSummary>,
    pub resolved_target: Option<u64>,
    pub target_materialized: bool,
    pub target_metrics: Option<EngineInterprocTargetMetrics>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineInterprocTargetDecision {
    pub direct_target: u64,
    pub resolved_target: Option<u64>,
    pub queued_targets: Vec<u64>,
    pub registration_target: bool,
    pub runtime_copy_target: bool,
    pub skip_reason: Option<EngineInterprocTargetSkipReason>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineInterprocTargetPlan {
    pub queued_targets: Vec<u64>,
    pub registration_targets: Vec<u64>,
    pub runtime_copy_targets: Vec<u64>,
    pub decisions: Vec<EngineInterprocTargetDecision>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineSymbolicScopeFunctionReason {
    Allowed,
    ScopeFull,
    InterprocDisabled,
    TargetTerminal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineSymbolicScopeFunctionInput {
    pub current_scope_count: usize,
    pub root_function: bool,
    pub target_hint_function: bool,
    pub interproc: EngineInterprocSessionPlan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineSymbolicScopeFunctionPlan {
    pub append_function: bool,
    pub expand_targets: bool,
    pub reason: EngineSymbolicScopeFunctionReason,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineRuntimeMaterializedSourceReason {
    Allowed,
    ScopeFull,
    EmptySource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineRuntimeMaterializedSourcePlan {
    pub append_source: bool,
    pub capped_size: u64,
    pub slot_bytes: u64,
    pub reason: EngineRuntimeMaterializedSourceReason,
}

fn engine_linkage_is_imported(linkage: r2ssa::FunctionSemanticLinkage) -> bool {
    matches!(linkage, r2ssa::FunctionSemanticLinkage::Imported)
}

fn interproc_target_skip_reason_from_evidence(
    import_authorized: bool,
    has_modeled_summary: bool,
    target_materialized: bool,
    metrics_within_budget: bool,
) -> Option<EngineInterprocTargetSkipReason> {
    if import_authorized {
        Some(EngineInterprocTargetSkipReason::Imported)
    } else if has_modeled_summary {
        Some(EngineInterprocTargetSkipReason::SummaryModeled)
    } else if !target_materialized {
        Some(EngineInterprocTargetSkipReason::Unmaterialized)
    } else if !metrics_within_budget {
        Some(EngineInterprocTargetSkipReason::OverBudget)
    } else {
        None
    }
}

fn interproc_target_metrics_within_budget(metrics: Option<&EngineInterprocTargetMetrics>) -> bool {
    let Some(metrics) = metrics else {
        return false;
    };
    metrics.basic_block_count <= ENGINE_INTERPROC_HELPER_MAX_BLOCKS
        && metrics.cost <= ENGINE_INTERPROC_HELPER_MAX_COST
}

pub fn interproc_helper_scope_within_budget(basic_block_count: u32, cost: u32) -> bool {
    interproc_target_metrics_within_budget(Some(&EngineInterprocTargetMetrics {
        basic_block_count,
        cost,
    }))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EngineInterprocSessionPurpose {
    TypeAnalysis,
    Decompile,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineInterprocSessionPlan {
    pub include_type_interproc_scope: bool,
    pub include_root_symbolic_scope: bool,
    pub interproc_iter: usize,
    pub interproc_max_iters: usize,
    pub interproc_converged: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineSessionPolicyPlan {
    pub interproc: EngineInterprocSessionPlan,
    pub type_writeback_mode: EngineTypeWritebackMode,
    pub global_max_links: usize,
    pub max_type_decls: usize,
    pub max_mutations: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineSessionBudgetInput {
    pub interproc_iter: usize,
    pub interproc_max_iters: usize,
    pub interproc_converged: bool,
    pub global_max_links: usize,
    pub max_type_decls: usize,
    pub max_mutations: usize,
    pub type_writeback_mode: EngineTypeWritebackMode,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineSessionBudget {
    pub interproc_iter: usize,
    pub interproc_max_iters: usize,
    pub interproc_converged: bool,
    pub writeback_budget: r2types::TypeWritebackMutationBudget,
    pub writeback_apply_policy: r2types::TypeWritebackApplyPolicy,
}

impl EngineSessionBudget {
    pub fn from_input(input: EngineSessionBudgetInput) -> Self {
        let interproc_iter = input.interproc_iter.max(1);
        let interproc_max_iters = input.interproc_max_iters.max(interproc_iter);
        Self {
            interproc_iter,
            interproc_max_iters,
            interproc_converged: input.interproc_converged,
            writeback_budget: r2types::TypeWritebackMutationBudget::new(
                input.global_max_links.max(1),
                input.max_type_decls.max(1),
                input.max_mutations.max(1),
            ),
            writeback_apply_policy: type_writeback_apply_policy_for_mode(input.type_writeback_mode),
        }
    }
}

pub fn interproc_session_plan(
    policy: EngineAnalysisPolicy,
    purpose: EngineInterprocSessionPurpose,
    metrics: Option<EngineInterprocTargetMetrics>,
) -> EngineInterprocSessionPlan {
    let within_budget = interproc_target_metrics_within_budget(metrics.as_ref());
    match purpose {
        EngineInterprocSessionPurpose::TypeAnalysis if within_budget => {
            EngineInterprocSessionPlan {
                include_type_interproc_scope: true,
                include_root_symbolic_scope: false,
                interproc_iter: 1,
                interproc_max_iters: policy.type_interproc_max_iters.max(1),
                interproc_converged: true,
            }
        }
        EngineInterprocSessionPurpose::TypeAnalysis => EngineInterprocSessionPlan {
            include_type_interproc_scope: false,
            include_root_symbolic_scope: true,
            interproc_iter: 1,
            interproc_max_iters: 1,
            interproc_converged: false,
        },
        EngineInterprocSessionPurpose::Decompile if within_budget => EngineInterprocSessionPlan {
            include_type_interproc_scope: true,
            include_root_symbolic_scope: false,
            interproc_iter: 1,
            interproc_max_iters: 1,
            interproc_converged: true,
        },
        EngineInterprocSessionPurpose::Decompile => EngineInterprocSessionPlan {
            include_type_interproc_scope: false,
            include_root_symbolic_scope: false,
            interproc_iter: 1,
            interproc_max_iters: 1,
            interproc_converged: true,
        },
    }
}

pub fn session_policy_plan(
    policy: EngineAnalysisPolicy,
    purpose: EngineInterprocSessionPurpose,
    metrics: Option<EngineInterprocTargetMetrics>,
) -> EngineSessionPolicyPlan {
    EngineSessionPolicyPlan {
        interproc: interproc_session_plan(policy, purpose, metrics),
        type_writeback_mode: policy.type_writeback_mode,
        global_max_links: policy.type_global_max_links,
        max_type_decls: policy.type_max_decls,
        max_mutations: policy.type_max_mutations,
    }
}

pub fn session_policy_plan_for_radare2_depth(
    depth: u32,
    purpose: EngineInterprocSessionPurpose,
    metrics: Option<EngineInterprocTargetMetrics>,
) -> EngineSessionPolicyPlan {
    session_policy_plan(analysis_policy_for_radare2_depth(depth), purpose, metrics)
}

fn interproc_target_queue_pair(
    direct_target: u64,
    resolved_target: Option<u64>,
    skip_reason: Option<EngineInterprocTargetSkipReason>,
) -> (Option<u64>, Option<u64>) {
    if skip_reason.is_some() {
        return (None, None);
    }
    let effective_target = resolved_target.unwrap_or(direct_target);
    if effective_target != direct_target {
        (Some(direct_target), Some(effective_target))
    } else {
        (Some(effective_target), None)
    }
}

pub fn interproc_scope_target_plan<I>(targets: I) -> EngineInterprocTargetPlan
where
    I: IntoIterator<Item = EngineInterprocTargetInput>,
{
    let mut queued_targets = BTreeSet::new();
    let mut runtime_copy_targets = BTreeSet::new();
    let mut decisions = Vec::new();

    for target in targets {
        let direct_target = target.direct_target;
        let resolved_target = target.resolved_target.filter(|addr| *addr != 0);
        let semantic_summary = target.semantic_summary.as_ref();

        // No source-owned typed registration role exists yet. An import name
        // is presentation metadata, so exact planning refuses this role.
        let registration_target = false;

        let runtime_copy_target =
            semantic_summary.is_some_and(r2sym::semantic_summary_has_runtime_copy_role);
        if runtime_copy_target {
            runtime_copy_targets.insert(direct_target);
        }

        let skip_reason = interproc_target_skip_reason_from_evidence(
            engine_linkage_is_imported(target.linkage),
            semantic_summary.is_some_and(r2sym::semantic_summary_has_modeled_evidence),
            target.target_materialized,
            interproc_target_metrics_within_budget(target.target_metrics.as_ref()),
        );

        let mut decision_queued_targets = Vec::new();
        let (first_queue_target, second_queue_target) =
            interproc_target_queue_pair(direct_target, resolved_target, skip_reason);
        for target in [first_queue_target, second_queue_target]
            .into_iter()
            .flatten()
        {
            queued_targets.insert(target);
            decision_queued_targets.push(target);
        }
        decision_queued_targets.sort_unstable();
        decision_queued_targets.dedup();

        decisions.push(EngineInterprocTargetDecision {
            direct_target,
            resolved_target,
            queued_targets: decision_queued_targets,
            registration_target,
            runtime_copy_target,
            skip_reason,
        });
    }

    decisions.sort_by_key(|decision| decision.direct_target);

    EngineInterprocTargetPlan {
        queued_targets: queued_targets.into_iter().collect(),
        registration_targets: Vec::new(),
        runtime_copy_targets: runtime_copy_targets.into_iter().collect(),
        decisions,
    }
}

pub fn symbolic_scope_function_plan(
    input: EngineSymbolicScopeFunctionInput,
) -> EngineSymbolicScopeFunctionPlan {
    if input.current_scope_count >= SYMBOLIC_SCOPE_MAX_FUNCTIONS {
        return EngineSymbolicScopeFunctionPlan {
            append_function: false,
            expand_targets: false,
            reason: EngineSymbolicScopeFunctionReason::ScopeFull,
        };
    }

    if input.root_function {
        return EngineSymbolicScopeFunctionPlan {
            append_function: true,
            expand_targets: true,
            reason: EngineSymbolicScopeFunctionReason::Allowed,
        };
    }

    if input.target_hint_function {
        return EngineSymbolicScopeFunctionPlan {
            append_function: true,
            expand_targets: false,
            reason: EngineSymbolicScopeFunctionReason::TargetTerminal,
        };
    }

    if !input.interproc.include_type_interproc_scope {
        return EngineSymbolicScopeFunctionPlan {
            append_function: false,
            expand_targets: false,
            reason: EngineSymbolicScopeFunctionReason::InterprocDisabled,
        };
    }

    EngineSymbolicScopeFunctionPlan {
        append_function: true,
        expand_targets: true,
        reason: EngineSymbolicScopeFunctionReason::Allowed,
    }
}

pub fn runtime_materialized_source_plan(
    current_scope_count: usize,
    addr: u64,
    size: u64,
) -> EngineRuntimeMaterializedSourcePlan {
    if current_scope_count >= SYMBOLIC_SCOPE_MAX_FUNCTIONS {
        return EngineRuntimeMaterializedSourcePlan {
            append_source: false,
            capped_size: 0,
            slot_bytes: RUNTIME_MATERIALIZED_SLOT_BYTES,
            reason: EngineRuntimeMaterializedSourceReason::ScopeFull,
        };
    }
    if addr == 0 || size == 0 {
        return EngineRuntimeMaterializedSourcePlan {
            append_source: false,
            capped_size: 0,
            slot_bytes: RUNTIME_MATERIALIZED_SLOT_BYTES,
            reason: EngineRuntimeMaterializedSourceReason::EmptySource,
        };
    }

    EngineRuntimeMaterializedSourcePlan {
        append_source: true,
        capped_size: size.min(RUNTIME_MATERIALIZED_MAX_BYTES),
        slot_bytes: RUNTIME_MATERIALIZED_SLOT_BYTES,
        reason: EngineRuntimeMaterializedSourceReason::Allowed,
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    #[kani::proof]
    fn interproc_target_skip_reason_is_fail_closed_and_priority_ordered() {
        let import_authorized: bool = kani::any();
        let has_modeled_summary: bool = kani::any();
        let target_materialized: bool = kani::any();
        let metrics_within_budget: bool = kani::any();

        let skip_reason = interproc_target_skip_reason_from_evidence(
            import_authorized,
            has_modeled_summary,
            target_materialized,
            metrics_within_budget,
        );

        if import_authorized {
            assert_eq!(skip_reason, Some(EngineInterprocTargetSkipReason::Imported));
        } else if has_modeled_summary {
            assert_eq!(
                skip_reason,
                Some(EngineInterprocTargetSkipReason::SummaryModeled)
            );
        } else if !target_materialized {
            assert_eq!(
                skip_reason,
                Some(EngineInterprocTargetSkipReason::Unmaterialized)
            );
        } else if !metrics_within_budget {
            assert_eq!(
                skip_reason,
                Some(EngineInterprocTargetSkipReason::OverBudget)
            );
        } else {
            assert_eq!(skip_reason, None);
        }

        if skip_reason.is_none() {
            assert!(target_materialized);
            assert!(metrics_within_budget);
            assert!(!has_modeled_summary);
            assert!(!import_authorized);
        }
    }

    #[kani::proof]
    fn imported_skip_authority_is_typed_linkage_only() {
        let linkage = match kani::any::<u8>() % 3 {
            0 => r2ssa::FunctionSemanticLinkage::Unknown,
            1 => r2ssa::FunctionSemanticLinkage::Internal,
            _ => r2ssa::FunctionSemanticLinkage::Imported,
        };

        assert_eq!(
            engine_linkage_is_imported(linkage),
            matches!(linkage, r2ssa::FunctionSemanticLinkage::Imported)
        );
    }

    #[kani::proof]
    fn interproc_target_metric_budget_is_owned_by_engine_thresholds() {
        let basic_block_count: u32 = kani::any();
        let cost: u32 = kani::any();
        let metrics = EngineInterprocTargetMetrics {
            basic_block_count,
            cost,
        };

        let within_budget = interproc_target_metrics_within_budget(Some(&metrics));
        assert_eq!(
            within_budget,
            basic_block_count <= ENGINE_INTERPROC_HELPER_MAX_BLOCKS
                && cost <= ENGINE_INTERPROC_HELPER_MAX_COST
        );
        assert_eq!(
            interproc_helper_scope_within_budget(basic_block_count, cost),
            within_budget
        );
        assert!(!interproc_target_metrics_within_budget(None));
    }

    #[kani::proof]
    fn interproc_target_queue_pair_queues_only_unskipped_targets() {
        let direct_target = 0x1000 + u64::from(kani::any::<u16>());
        let resolved_offset = u64::from(kani::any::<u8>() % 4);
        let has_resolved_target: bool = kani::any();
        let skipped: bool = kani::any();
        let resolved_target = has_resolved_target.then_some(direct_target + resolved_offset);

        let skip_reason = skipped.then_some(EngineInterprocTargetSkipReason::OverBudget);
        let (first, second) =
            interproc_target_queue_pair(direct_target, resolved_target, skip_reason);

        if skipped {
            assert_eq!(first, None);
            assert_eq!(second, None);
        } else {
            let effective_target = resolved_target.unwrap_or(direct_target);
            if effective_target != direct_target {
                assert_eq!(first, Some(direct_target));
                assert_eq!(second, Some(effective_target));
            } else {
                assert_eq!(first, Some(effective_target));
                assert_eq!(second, None);
            }
        }
    }

    #[kani::proof]
    fn analysis_policy_depths_have_nonzero_monotonic_budgets() {
        let depth = kani::any::<u32>();
        let selected = analysis_policy_for_radare2_depth(depth);
        assert!(selected.type_interproc_max_iters > 0);
        assert!(selected.type_max_blocks > 0);
        assert!(selected.type_global_max_links > 0);
        assert!(selected.type_max_decls > 0);
        assert!(selected.type_max_mutations > 0);

        let basic = analysis_policy_for_depth(EngineAnalysisDepth::Basic);
        let balanced = analysis_policy_for_depth(EngineAnalysisDepth::Default);
        let aggressive = analysis_policy_for_depth(EngineAnalysisDepth::Aggressive);

        assert!(basic.mode.level() < balanced.mode.level());
        assert!(balanced.mode.level() < aggressive.mode.level());
        assert!(basic.type_writeback_mode.level() < balanced.type_writeback_mode.level());
        assert!(balanced.type_writeback_mode.level() < aggressive.type_writeback_mode.level());
        assert!(basic.type_interproc_max_iters < balanced.type_interproc_max_iters);
        assert!(balanced.type_interproc_max_iters < aggressive.type_interproc_max_iters);
        assert!(basic.type_max_blocks < balanced.type_max_blocks);
        assert!(balanced.type_max_blocks < aggressive.type_max_blocks);
        assert!(basic.type_global_max_links < balanced.type_global_max_links);
        assert!(balanced.type_global_max_links < aggressive.type_global_max_links);
        assert!(basic.type_max_decls < balanced.type_max_decls);
        assert!(balanced.type_max_decls < aggressive.type_max_decls);
        assert!(basic.type_max_mutations < balanced.type_max_mutations);
        assert!(balanced.type_max_mutations < aggressive.type_max_mutations);
    }

    #[kani::proof]
    fn post_analysis_plan_focus_policy_matches_engine_thresholds() {
        let depth = kani::any::<u32>();
        let function_count = usize::from(kani::any::<u16>());
        let plan = post_analysis_plan_for_radare2_depth(depth, function_count);

        assert_eq!(
            plan.xref_enabled,
            plan.policy.mode.level() >= EngineAnalysisMode::Balanced.level()
        );
        assert_eq!(
            plan.taint_enabled,
            plan.policy.mode == EngineAnalysisMode::Full
        );
        assert_eq!(
            plan.signature_writeback_enabled,
            plan.policy.mode.level() >= EngineAnalysisMode::Balanced.level()
        );
        assert_eq!(
            plan.type_writeback_enabled,
            plan.signature_writeback_enabled
                && plan.policy.type_writeback_mode != EngineTypeWritebackMode::Off
        );
        assert_eq!(
            plan.balanced_focus_only,
            plan.policy.mode == EngineAnalysisMode::Balanced
        );
        assert_eq!(
            plan.taint_focus_only,
            plan.taint_enabled && function_count > TAINT_GLOBAL_MAX_FUNCTIONS
        );
        assert_eq!(
            plan.signature_writeback_focus_only,
            plan.signature_writeback_enabled
                && (plan.balanced_focus_only
                    || function_count > SIGNATURE_WRITEBACK_GLOBAL_MAX_FUNCTIONS)
        );
        assert_eq!(
            plan.type_writeback_focus_only,
            plan.type_writeback_enabled
                && (plan.balanced_focus_only
                    || function_count > TYPE_WRITEBACK_GLOBAL_MAX_FUNCTIONS)
        );
    }

    #[kani::proof]
    fn bounded_type_plan_budget_policy_is_fail_closed() {
        let interproc_max_iters = kani::any::<usize>();
        let interproc_converged: bool = kani::any();
        let prefers_bounded =
            type_analysis_interproc_prefers_bounded_plan(interproc_max_iters, interproc_converged);

        assert_eq!(
            prefers_bounded,
            interproc_max_iters <= 1 && !interproc_converged
        );
        if interproc_converged || interproc_max_iters > 1 {
            assert!(!prefers_bounded);
        }
    }
}

pub fn interproc_direct_call_targets(analysis: &EngineAnalysis) -> Vec<u64> {
    let mut targets = BTreeSet::new();
    for call in analysis.ssa_func.call_sites().by_id.values() {
        if let Some(target) = analysis.ssa_func.resolved_call_target(call) {
            targets.insert(target);
        }
    }
    targets.into_iter().collect()
}

fn debug_runtime_scope_enabled() -> bool {
    std::env::var_os("R2SLEIGH_DEBUG_RUNTIME_TARGETS").is_some()
}

fn debug_runtime_scope_log(message: &str) {
    if !debug_runtime_scope_enabled() {
        return;
    }
    let path = std::env::var("R2SLEIGH_DEBUG_RUNTIME_TARGETS_LOG")
        .unwrap_or_else(|_| "/tmp/r2sleigh_runtime_targets.log".to_string());
    if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(path) {
        let _ = writeln!(file, "{message}");
    }
}

fn windows_x64_runtime_call_observations(
    analysis: &EngineAnalysis,
) -> Option<BTreeMap<r2ssa::CallSiteId, Vec<r2ssa::CallArgObservation>>> {
    let prepared = analysis.ssa_func();
    if prepared.machine_context().effective_abi_class() != r2ssa::SourceAbiClass::MicrosoftX64 {
        return None;
    }
    let abi = prepared.abi()?;
    Some(r2ssa::observe_call_arguments(prepared, &abi))
}

fn complete_windows_x64_call_arguments<'a>(
    analysis: &EngineAnalysis,
    observations: &'a BTreeMap<r2ssa::CallSiteId, Vec<r2ssa::CallArgObservation>>,
    call_id: r2ssa::CallSiteId,
) -> Option<&'a [r2ssa::CallArgObservation]> {
    let prepared = analysis.ssa_func();
    let machine = prepared.machine_context();
    let interface = machine.call_site_interface(call_id)?;
    if !interface.is_complete()
        || machine
            .architecture_family()
            .refine_abi_class(interface.abi_class())
            != r2ssa::SourceAbiClass::MicrosoftX64
    {
        return None;
    }
    let arguments = observations.get(&call_id)?;
    (arguments.len() == interface.arguments().len()
        && !arguments
            .iter()
            .any(|argument| matches!(argument, r2ssa::CallArgObservation::Unknown)))
    .then_some(arguments)
}

/// Discover registered handlers only from an exact Microsoft x64 function ABI
/// and complete, exact Microsoft x64 callsite observations.
pub fn interproc_runtime_registration_targets(
    analysis: &EngineAnalysis,
    registration_call_targets: &[u64],
) -> Vec<u64> {
    if registration_call_targets.is_empty() {
        return Vec::new();
    }
    let Some(observations) = windows_x64_runtime_call_observations(analysis) else {
        debug_runtime_scope_log("skip missing exact Microsoft x64 ABI authority");
        return Vec::new();
    };

    let registrations = registration_call_targets
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut targets = BTreeSet::new();
    for (call_id, call) in &analysis.ssa_func.call_sites().by_id {
        let Some(target) = analysis.ssa_func.resolved_call_target(call) else {
            debug_runtime_scope_log(&format!("call_id={call_id:?} unresolved_target"));
            continue;
        };
        if !registrations.contains(&target) {
            debug_runtime_scope_log(&format!(
                "call_id={call_id:?} target=0x{target:x} not_registration"
            ));
            continue;
        }
        let Some(args) = complete_windows_x64_call_arguments(analysis, &observations, *call_id)
        else {
            debug_runtime_scope_log(&format!(
                "call_id={call_id:?} target=0x{target:x} incomplete_exact_args"
            ));
            continue;
        };
        let Some(r2ssa::CallArgObservation::Const(handler)) = args.get(1) else {
            debug_runtime_scope_log(&format!(
                "call_id={call_id:?} target=0x{target:x} handler_arg={:?}",
                args.get(1)
            ));
            continue;
        };
        if *handler >= 0x1000 {
            debug_runtime_scope_log(&format!(
                "call_id={call_id:?} target=0x{target:x} handler=0x{handler:x}"
            ));
            targets.insert(*handler);
        }
    }
    targets.into_iter().collect()
}

/// Discover materialized code only from the same exact ABI/callsite authority
/// required for runtime registration targets.
pub fn interproc_runtime_materialized_sources(
    analysis: &EngineAnalysis,
    copy_call_targets: &[u64],
) -> Vec<EngineRuntimeMaterializedSource> {
    if copy_call_targets.is_empty() {
        return Vec::new();
    }
    let Some(observations) = windows_x64_runtime_call_observations(analysis) else {
        return Vec::new();
    };

    let copy_targets = copy_call_targets.iter().copied().collect::<BTreeSet<_>>();
    let mut sources = BTreeMap::<u64, u64>::new();
    for (call_id, call) in &analysis.ssa_func.call_sites().by_id {
        let Some(target) = analysis.ssa_func.resolved_call_target(call) else {
            continue;
        };
        if !copy_targets.contains(&target) {
            continue;
        }
        let Some(args) = complete_windows_x64_call_arguments(analysis, &observations, *call_id)
        else {
            continue;
        };
        let (
            Some(r2ssa::CallArgObservation::Const(source)),
            Some(r2ssa::CallArgObservation::Const(size)),
        ) = (args.get(1), args.get(2))
        else {
            continue;
        };
        if *source >= 0x1000 && *size > 0 {
            sources
                .entry(*source)
                .and_modify(|existing| *existing = (*existing).max(*size))
                .or_insert(*size);
        }
    }

    sources
        .into_iter()
        .map(|(addr, size)| EngineRuntimeMaterializedSource { addr, size })
        .collect()
}

#[derive(Debug)]
pub struct EngineAnalysisArtifact {
    type_analysis: r2types::TypeWritebackAnalysis,
    /// Certifying view of the retained source, available only for the unmodified
    /// source-retaining trusted preparation path.
    trusted_ssa: Option<Arc<r2ssa::TrustedSsaArtifact>>,
}

impl EngineAnalysisArtifact {
    fn new(
        type_analysis: r2types::TypeWritebackAnalysis,
        trusted_ssa: Option<Arc<r2ssa::TrustedSsaArtifact>>,
    ) -> Option<Self> {
        let source = type_analysis.shared_source();
        if trusted_ssa
            .as_deref()
            .is_some_and(|trusted| !trusted.shares_artifact(&source))
        {
            return None;
        }
        Some(Self {
            type_analysis,
            trusted_ssa,
        })
    }

    /// Borrow the exact immutable SSA owner used to build these facts.
    pub fn ssa_func(&self) -> &SsaArtifact {
        self.type_analysis.source()
    }

    /// Borrow the report sealed to the exact immutable SSA owner.
    pub fn function_facts(&self) -> &FunctionFacts {
        self.type_analysis.function_facts()
    }

    /// Borrow the inseparable source-owned type analysis.
    pub fn type_analysis(&self) -> &r2types::TypeWritebackAnalysis {
        &self.type_analysis
    }

    /// Borrow the writeback plan derived from the same exact source owner.
    pub fn writeback_plan(&self) -> &TypeWritebackPlan {
        self.type_analysis.plan()
    }

    /// Borrow request-local certification authority when this artifact retains it.
    pub fn trusted_ssa(&self) -> Option<&r2ssa::TrustedSsaArtifact> {
        self.trusted_ssa.as_deref()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EngineSemanticMode {
    Full,
    Optional,
}

#[derive(Debug, Clone, Default)]
pub struct EngineCancellationToken {
    symbolic: r2sym::SymCancellationToken,
    ssa: r2ssa::SsaCancellationToken,
}

impl EngineCancellationToken {
    pub fn cancel(&self) {
        self.symbolic.cancel();
        self.ssa.cancel();
    }

    pub fn is_cancelled(&self) -> bool {
        self.symbolic.is_cancelled() || self.ssa.is_cancelled()
    }
}

#[derive(Debug, Clone, Default)]
pub struct EngineExecutionControl {
    cancellation: EngineCancellationToken,
    deadline: Option<Instant>,
}

impl EngineExecutionControl {
    /// Build a control in which cancellation and a deadline coexist.
    pub fn new(cancellation: EngineCancellationToken, deadline: Option<Instant>) -> Self {
        Self {
            cancellation,
            deadline,
        }
    }

    pub fn with_cancellation_and_deadline(
        cancellation: EngineCancellationToken,
        deadline: Instant,
    ) -> Self {
        Self::new(cancellation, Some(deadline))
    }

    pub fn with_cancellation(cancellation: EngineCancellationToken) -> Self {
        Self::new(cancellation, None)
    }

    pub fn with_deadline(deadline: Instant) -> Self {
        Self::new(EngineCancellationToken::default(), Some(deadline))
    }

    pub fn with_timeout(timeout: Duration) -> Self {
        Self::with_deadline(
            Instant::now()
                .checked_add(timeout)
                .unwrap_or_else(Instant::now),
        )
    }

    pub fn cancellation(&self) -> EngineCancellationToken {
        self.cancellation.clone()
    }

    pub fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    pub fn symbolic_execution_control(&self) -> r2sym::SymExecutionControl {
        r2sym::SymExecutionControl::new(self.cancellation.symbolic.clone(), self.deadline)
    }

    pub fn ssa_execution_control(&self) -> r2ssa::SsaExecutionControl {
        r2ssa::SsaExecutionControl::new(self.cancellation.ssa.clone(), self.deadline)
    }

    fn replace_cancellation(&mut self, cancellation: EngineCancellationToken) {
        self.cancellation = cancellation;
    }

    fn replace_deadline(&mut self, deadline: Instant) {
        self.deadline = Some(deadline);
    }

    fn refusal_reason(&self, phase: EnginePhase) -> Option<String> {
        if self.cancellation.is_cancelled() {
            return Some(format!(
                "engine request cancelled before {} phase",
                phase.as_str()
            ));
        }
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
            .then(|| {
                format!(
                    "engine request deadline exceeded before {} phase",
                    phase.as_str()
                )
            })
    }
}

#[derive(Debug, Clone)]
pub struct EngineExecutionRefusal {
    pub reason: String,
    pub phase: EnginePhase,
    pub metrics: Box<EngineMetrics>,
    pub diagnostics: Box<EngineDiagnostics>,
}

impl std::fmt::Display for EngineExecutionRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.reason)
    }
}

impl std::error::Error for EngineExecutionRefusal {}

fn engine_execution_refusal(
    reason: String,
    phase: EnginePhase,
    mut metrics: EngineMetrics,
) -> EngineExecutionRefusal {
    metrics.refuse_from(phase);
    EngineExecutionRefusal {
        diagnostics: Box::new(EngineDiagnostics {
            plan: Some(EnginePlan::RefuseWithEvidence),
            route_reason: Some(reason.clone()),
            refusal: Some(reason.clone()),
            ..EngineDiagnostics::default()
        }),
        reason,
        phase,
        metrics: Box::new(metrics),
    }
}

fn engine_render_execution_refusal(
    reason: String,
    phase: EnginePhase,
    metrics: EngineMetrics,
) -> EngineExecutionRefusal {
    EngineExecutionRefusal {
        diagnostics: Box::new(EngineDiagnostics {
            plan: Some(EnginePlan::RefuseWithEvidence),
            route_reason: Some(reason.clone()),
            refusal: Some(reason.clone()),
            ..EngineDiagnostics::default()
        }),
        reason,
        phase,
        metrics: Box::new(metrics),
    }
}

fn ssa_prepare_execution_refusal(
    error: r2ssa::SsaPrepareError,
    metrics: EngineMetrics,
) -> EngineExecutionRefusal {
    let reason = match error {
        r2ssa::SsaPrepareError::Cancelled => {
            "engine request cancelled during ssa phase".to_string()
        }
        r2ssa::SsaPrepareError::DeadlineExceeded => {
            "engine request deadline exceeded during ssa phase".to_string()
        }
        r2ssa::SsaPrepareError::MalformedInput => {
            "malformed SSA source input during ssa phase".to_string()
        }
    };
    engine_execution_refusal(reason, EnginePhase::Ssa, metrics)
}

fn poll_engine_execution(
    execution: &EngineExecutionControl,
    phase: EnginePhase,
    metrics: &EngineMetrics,
) -> Result<(), EngineExecutionRefusal> {
    if let Some(reason) = execution.refusal_reason(phase) {
        return Err(engine_execution_refusal(reason, phase, metrics.clone()));
    }
    Ok(())
}

#[derive(Debug, Clone)]
pub struct EngineAnalyzeRequest {
    pub function_name: String,
    pub function_addr: u64,
    pub blocks: Vec<R2ILBlock>,
    pub arch: Option<r2il::ArchSpec>,
    pub source_snapshot: Option<Arc<EngineSourceSnapshot>>,
    trusted_ssa: Option<Arc<r2ssa::TrustedSsaArtifact>>,
    /// Bodies of the functions the root calls, captured in the same transaction.
    trusted_callees: Vec<Arc<r2ssa::SsaArtifact>>,
    pub ptr_bits: u32,
    pub semantic_metadata_enabled: bool,
    pub reg_type_hints: HashMap<String, r2types::TypeHint>,
    pub parsed_context: r2types::ParsedExternalContext,
    pub interproc_max_iterations: usize,
    pub symbolic_scope: Option<r2sym::PreparedFunctionScope>,
    pub semantic_mode: EngineSemanticMode,
    pub include_interproc_summary_set: bool,
    pub execution: EngineExecutionControl,
}

#[derive(Debug, Clone)]
pub struct EngineAnalyzeRequestParts {
    pub function_name: String,
    pub function_addr: u64,
    pub blocks: Vec<R2ILBlock>,
    pub arch: Option<r2il::ArchSpec>,
    pub source_snapshot: Option<Arc<EngineSourceSnapshot>>,
    pub ptr_bits: u32,
    pub semantic_metadata_enabled: bool,
    pub reg_type_hints: HashMap<String, r2types::TypeHint>,
    pub parsed_context: r2types::ParsedExternalContext,
    pub interproc_max_iterations: usize,
    pub symbolic_scope: Option<r2sym::PreparedFunctionScope>,
    pub include_interproc_summary_set: bool,
}

#[derive(Debug, Clone)]
pub struct EngineFunctionInput {
    pub function_name: String,
    pub function_addr: u64,
    pub blocks: Vec<R2ILBlock>,
    pub arch: Option<r2il::ArchSpec>,
    pub source_snapshot: Option<Arc<EngineSourceSnapshot>>,
    pub semantic_metadata_enabled: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineFunctionInputQuality {
    pub expected_blocks: usize,
    pub lifted_blocks: usize,
    pub read_failures: usize,
    pub invalid_blocks: usize,
    pub null_lift_failures: usize,
    pub truncated_blocks: usize,
}

impl EngineFunctionInputQuality {
    pub fn complete(lifted_blocks: usize) -> Self {
        Self {
            expected_blocks: lifted_blocks,
            lifted_blocks,
            read_failures: 0,
            invalid_blocks: 0,
            null_lift_failures: 0,
            truncated_blocks: 0,
        }
    }

    pub fn is_complete(self) -> bool {
        self.expected_blocks > 0
            && self.lifted_blocks > 0
            && self.expected_blocks == self.lifted_blocks
            && self.read_failures == 0
            && self.invalid_blocks == 0
            && self.null_lift_failures == 0
            && self.truncated_blocks == 0
    }

    pub fn refusal_reason(self) -> Option<String> {
        if self.expected_blocks == 0 || self.lifted_blocks == 0 {
            return Some(format!(
                "empty lifted function input: expected_blocks={} lifted_blocks={} read_failures={} invalid_blocks={} null_lift_failures={} truncated_blocks={}",
                self.expected_blocks,
                self.lifted_blocks,
                self.read_failures,
                self.invalid_blocks,
                self.null_lift_failures,
                self.truncated_blocks
            ));
        }
        (!self.is_complete()).then(|| {
            format!(
                "incomplete lifted function input: expected_blocks={} lifted_blocks={} read_failures={} invalid_blocks={} null_lift_failures={} truncated_blocks={}",
                self.expected_blocks,
                self.lifted_blocks,
                self.read_failures,
                self.invalid_blocks,
                self.null_lift_failures,
                self.truncated_blocks
            )
        })
    }

    pub fn refusal_reason_for_actual_lifted_blocks(
        self,
        actual_lifted_blocks: usize,
    ) -> Option<String> {
        if self.lifted_blocks != actual_lifted_blocks {
            return Some(format!(
                "inconsistent lifted function input: expected_blocks={} lifted_blocks={} actual_lifted_blocks={} read_failures={} invalid_blocks={} null_lift_failures={} truncated_blocks={}",
                self.expected_blocks,
                self.lifted_blocks,
                actual_lifted_blocks,
                self.read_failures,
                self.invalid_blocks,
                self.null_lift_failures,
                self.truncated_blocks
            ));
        }
        self.refusal_reason()
    }
}

fn function_input_quality_facts(
    quality: EngineFunctionInputQuality,
    actual_lifted_blocks: usize,
    refusal_reason: Option<String>,
) -> r2types::FunctionInputQualityFacts {
    r2types::FunctionInputQualityFacts {
        expected_blocks: quality.expected_blocks,
        lifted_blocks: quality.lifted_blocks,
        actual_lifted_blocks,
        read_failures: quality.read_failures,
        invalid_blocks: quality.invalid_blocks,
        null_lift_failures: quality.null_lift_failures,
        truncated_blocks: quality.truncated_blocks,
        refusal_reason,
    }
}

#[derive(Debug, Clone)]
pub struct EngineAnalyzeRequestInput {
    pub function_name: String,
    pub function_addr: u64,
    pub blocks: Vec<R2ILBlock>,
    pub arch: Option<r2il::ArchSpec>,
    pub source_snapshot: Option<Arc<EngineSourceSnapshot>>,
    pub ptr_bits: Option<u32>,
    pub semantic_metadata_enabled: bool,
    pub reg_type_hints: HashMap<String, r2types::TypeHint>,
    pub parsed_context: r2types::ParsedExternalContext,
    pub interproc_max_iterations: usize,
    pub symbolic_scope: Option<r2sym::PreparedFunctionScope>,
    pub include_interproc_summary_set: bool,
}

#[derive(Debug, Clone)]
pub struct EngineAnalyzeFunctionRequestInput {
    pub function: EngineFunctionInput,
    pub ptr_bits: Option<u32>,
    pub reg_type_hints: HashMap<String, r2types::TypeHint>,
    pub parsed_context: r2types::ParsedExternalContext,
    pub interproc_max_iterations: usize,
    pub symbolic_scope: Option<r2sym::PreparedFunctionScope>,
    pub include_interproc_summary_set: bool,
}

/// Names the source gave its stack slots, keyed the way the renderer looks them up.
///
/// These are presentation only: the role comes from the interface so a home or a
/// saved carrier is not offered as a local, and a name that matches no slot is
/// not carried at all.
/// A source type rendered as the source spells it.
///
/// The shared parser canonicalises a spelling to structure, which is right for
/// analysis and wrong for a name: it turns `char` into an eight-bit integer and
/// `size_t` into an unsigned word, so the rendered C says `int8_t *` where the
/// source said `char *`. Structure is already carried by the type graph, so the
/// spelling is what this has to preserve.
fn source_spelled_type(spelling: &str, ptr_bits: u32) -> Option<r2types::CTypeLike> {
    let mut rest = spelling.trim();
    if rest.is_empty() {
        return None;
    }
    let mut array_len = None;
    if let Some(start) = rest.rfind('[')
        && rest.ends_with(']')
    {
        let len = &rest[start + 1..rest.len() - 1];
        array_len = Some(len.trim().parse::<usize>().ok());
        rest = rest[..start].trim_end();
    }
    let mut pointers = 0usize;
    while let Some(stripped) = rest.strip_suffix('*') {
        pointers += 1;
        rest = stripped.trim_end();
    }
    let base_words = rest
        .split_whitespace()
        .filter(|word| {
            !matches!(
                word.to_ascii_lowercase().as_str(),
                "const" | "volatile" | "restrict" | "__restrict" | "__restrict__"
            )
        })
        .collect::<Vec<_>>();
    let base_spelling = base_words.join(" ");
    if base_spelling.is_empty() {
        return None;
    }
    // A structural spelling stays structural so width-aware analysis keeps
    // working; a named one is carried by name so it renders as itself.
    let mut ty = match r2types::parse_type_like_spec(&base_spelling, ptr_bits) {
        Some(r2types::CTypeLike::Void) => r2types::CTypeLike::Void,
        Some(
            structural @ (r2types::CTypeLike::Struct(_)
            | r2types::CTypeLike::Union(_)
            | r2types::CTypeLike::Enum(_)),
        ) => structural,
        Some(_) => r2types::CTypeLike::Typedef(base_spelling),
        None => return None,
    };
    for _ in 0..pointers {
        ty = r2types::CTypeLike::Pointer(Box::new(ty));
    }
    if let Some(len) = array_len {
        ty = r2types::CTypeLike::Array(Box::new(ty), len);
    }
    Some(ty)
}

/// The struct layouts radare2 captured alongside the function, as the external
/// type database the field-naming path reads.
///
/// The snapshot already carries an aggregate layout for every struct its
/// signature mentions, but nothing turned those layouts into the database, so
/// it stayed empty in every real decompile. Field certificates are only kept
/// when the database confirms a field, so every struct access fell back to
/// pointer arithmetic however completely radare2 knew the type: `list_sum`
/// rendered `cur[1]` for `cur->next`.
fn trusted_external_type_db(trusted: &r2ssa::TrustedSsaArtifact) -> r2types::ExternalTypeDb {
    let mut db = r2types::ExternalTypeDb::default();
    let Some(graph) = trusted
        .source()
        .function_interface()
        .and_then(r2ssa::SourceFunctionInterface::type_graph)
    else {
        return db;
    };
    for aggregate in graph.aggregates() {
        let name = aggregate.name();
        if name.is_empty() {
            continue;
        }
        let mut fields = std::collections::BTreeMap::new();
        collect_external_struct_fields(graph, aggregate, 0, "", &mut fields, 0);
        if fields.is_empty() {
            continue;
        }
        db.structs.insert(
            r2types::normalize_external_type_name(name).to_ascii_lowercase(),
            r2types::ExternalStruct {
                name: name.to_string(),
                fields,
            },
        );
    }
    db
}

/// The scalar members of an aggregate, keyed by byte offset, with a nested
/// aggregate flattened into the dotted path that reaches its members.
///
/// Code reads the scalars, never the aggregate that contains them, so naming a
/// four-byte read after the eight-byte `Point` sharing its offset would claim a
/// member the access is not. Flattening gives that read the name it deserves:
/// `r->top_left.x` rather than an unnamed subscript.
fn collect_external_struct_fields(
    graph: &r2ssa::SourceTypeGraph,
    aggregate: &r2ssa::SourceAggregateLayout,
    base_offset: u64,
    prefix: &str,
    fields: &mut std::collections::BTreeMap<u64, r2types::ExternalField>,
    depth: u32,
) {
    // A type graph is acyclic, but a bound keeps a malformed capture from
    // walking forever.
    if depth > 4 {
        return;
    }
    for member in aggregate.members() {
        // A member the capture could not name, or one that does not start on a
        // byte, cannot be spelled as a field access.
        if member.name().is_empty() || member.offset_bits() % 8 != 0 {
            continue;
        }
        let Some(offset) = base_offset.checked_add(member.offset_bits() / 8) else {
            continue;
        };
        let path = if prefix.is_empty() {
            member.name().to_string()
        } else {
            format!("{prefix}.{}", member.name())
        };
        let member_type = usize::try_from(member.type_id())
            .ok()
            .and_then(|id| graph.types().get(id));
        if let Some(source_type) = member_type
            && let r2ssa::SourceTypeKind::Struct { aggregate_id } = source_type.kind()
        {
            if let Some(nested) = graph
                .aggregates()
                .iter()
                .find(|candidate| candidate.id() == aggregate_id)
            {
                collect_external_struct_fields(graph, nested, offset, &path, fields, depth + 1);
            }
            continue;
        }
        fields.insert(
            offset,
            r2types::ExternalField {
                name: path,
                offset,
                ty: source_member_type_spelling(graph, member),
            },
        );
    }
}

/// How a captured aggregate member's type spells in C, so the width check that
/// gates a field certificate has something exact to measure against.
fn source_member_type_spelling(
    graph: &r2ssa::SourceTypeGraph,
    member: &r2ssa::SourceAggregateMember,
) -> Option<String> {
    let source_type = usize::try_from(member.type_id())
        .ok()
        .and_then(|id| graph.types().get(id))?;
    let bits = source_type.size_bits();
    let element = match source_type.kind() {
        r2ssa::SourceTypeKind::SignedInteger => format!("int{bits}_t"),
        r2ssa::SourceTypeKind::UnsignedInteger => format!("uint{bits}_t"),
        r2ssa::SourceTypeKind::Pointer { .. } => "void *".to_string(),
        // An inline struct member has no scalar width to check an access against.
        r2ssa::SourceTypeKind::Struct { .. } => return None,
    };
    // A member wider than one element repeats it. The capture states the repeat
    // count, but the Rust contract for a member does not carry it, so the
    // member's own width against the element width recovers the length. Without
    // the length only the first element could be named, and every later one fell
    // back to an offset placeholder: `st->r[2]` rendered as `st->f_8`.
    let count = source_member_element_count(member, bits)?;
    Some(if count > 1 {
        format!("{element}[{count}]")
    } else {
        element
    })
}

/// How many elements a captured member holds, from its own width against the
/// width of one element. `None` when the two do not divide evenly, because a
/// member that is not a whole number of elements is not an array of them.
fn source_member_element_count(
    member: &r2ssa::SourceAggregateMember,
    element_bits: u64,
) -> Option<u64> {
    if element_bits == 0 {
        return None;
    }
    let total_bits = member.size_bits();
    if total_bits == 0 || total_bits == element_bits {
        return Some(1);
    }
    total_bits
        .is_multiple_of(element_bits)
        .then(|| total_bits / element_bits)
}

/// The prototype the source recovered, spelled as the source spells it.
///
/// The type graph carries structure and the interface carries storage; only
/// this says `size_t` rather than `uint64_t`, or `char *` rather than a pointer
/// to an eight-bit integer.
fn trusted_source_signature(
    trusted: &r2ssa::TrustedSsaArtifact,
    ptr_bits: u32,
) -> Option<(r2types::FunctionSignatureSpec, Option<String>, bool)> {
    let signature = trusted.source().presentation().signature()?;
    let params = signature
        .parameters()
        .iter()
        .enumerate()
        .map(|(index, parameter)| r2types::FunctionParamSpec {
            name: parameter
                .name()
                .filter(|name| !name.is_empty())
                .map_or_else(|| format!("arg{index}"), str::to_string),
            ty: parameter
                .type_spelling()
                .and_then(|spelling| source_spelled_type(spelling, ptr_bits)),
        })
        .collect();
    let spec = r2types::FunctionSignatureSpec {
        ret_type: signature
            .return_type()
            .and_then(|spelling| source_spelled_type(spelling, ptr_bits)),
        params,
    };
    let callconv = signature
        .calling_convention()
        .filter(|convention| !convention.is_empty())
        .map(str::to_string);
    Some((spec, callconv, signature.noreturn()))
}

/// The prototype of each callee, keyed by the name the call renders with.
///
/// Without these an argument is typed by how wide its register is, so a call
/// to `malloc` takes whatever fits rather than the `size_t` it declares.
fn trusted_callee_signatures(
    trusted: &r2ssa::TrustedSsaArtifact,
    ptr_bits: u32,
) -> std::collections::HashMap<String, r2types::FunctionType> {
    trusted
        .source()
        .presentation()
        .callee_signatures()
        .iter()
        // A prototype with no parameters and no result is what radare2 writes
        // for a callee it knows nothing about. Carrying it would say the callee
        // takes no arguments, which is a claim, and would truncate the ones the
        // lift recovered.
        .filter(|(_, signature)| {
            !signature.parameters().is_empty()
                || signature
                    .return_type()
                    .is_some_and(|spelling| spelling.trim() != "void" && !spelling.is_empty())
        })
        .map(|(name, signature)| {
            (
                name.to_string(),
                r2types::FunctionType {
                    return_type: signature
                        .return_type()
                        .and_then(|spelling| source_spelled_type(spelling, ptr_bits))
                        .unwrap_or(r2types::CTypeLike::Unknown),
                    // The ellipsis is not a parameter and has no type. Copying
                    // it in as one, and then calling the whole prototype
                    // non-variadic, said `fprintf` takes exactly three
                    // arguments -- so every call to it was cut to three,
                    // whatever the machine passed.
                    params: signature
                        .named_parameters()
                        .iter()
                        .map(|parameter| {
                            parameter
                                .type_spelling()
                                .and_then(|spelling| source_spelled_type(spelling, ptr_bits))
                                .unwrap_or(r2types::CTypeLike::Unknown)
                        })
                        .collect(),
                    variadic: signature.is_variadic(),
                },
            )
        })
        .collect()
}

fn trusted_stack_slot_names(
    trusted: &r2ssa::TrustedSsaArtifact,
    ptr_bits: u32,
) -> std::collections::BTreeMap<r2types::StackSlotKey, r2types::ExternalStackSlotSpec> {
    let snapshot = trusted.source();
    let Some(interface) = snapshot.function_interface() else {
        return Default::default();
    };
    let mut slots = std::collections::BTreeMap::new();
    for slot_name in snapshot.presentation().stack_slot_names() {
        let Some(slot) = interface
            .stack_slots()
            .iter()
            .find(|slot| slot.base() == slot_name.base() && slot.offset() == slot_name.offset())
        else {
            continue;
        };
        let base = match slot_name.base() {
            r2ssa::StackAddressBase::FramePointer => r2types::ExternalStackBase::FramePointer,
            r2ssa::StackAddressBase::StackPointer => r2types::ExternalStackBase::StackPointer,
        };
        // A home is the parameter it spills and is named through the parameter
        // list, so only a slot that stands for itself is named here.
        let role = match slot.role() {
            r2ssa::SourceStackSlotRole::Local => r2types::ExternalStackSlotRole::Local,
            r2ssa::SourceStackSlotRole::UnclassifiedResource => {
                r2types::ExternalStackSlotRole::Unknown
            }
            r2ssa::SourceStackSlotRole::ParameterHome { .. } => continue,
        };
        slots.insert(
            r2types::StackSlotKey {
                base: base.clone(),
                offset: slot_name.offset(),
            },
            r2types::ExternalStackSlotSpec {
                name: slot_name.name().to_string(),
                ty: slot_name
                    .type_spelling()
                    .and_then(|spelling| source_spelled_type(spelling, ptr_bits)),
                base,
                role,
                ..r2types::ExternalStackSlotSpec::default()
            },
        );
    }
    slots
}

impl EngineAnalyzeRequest {
    pub fn full_semantics_from_input(input: EngineAnalyzeRequestInput) -> Self {
        Self::full_semantics(engine_analyze_request_parts_from_input(input))
    }

    pub fn full_semantics_for_function(input: EngineAnalyzeFunctionRequestInput) -> Self {
        Self::full_semantics_from_input(engine_analyze_request_input_from_function(input))
    }

    pub fn full_semantics_for_function_with_register_names<F>(
        mut input: EngineAnalyzeFunctionRequestInput,
        register_name: F,
    ) -> Self
    where
        F: FnMut(&r2il::Varnode) -> Option<String>,
    {
        if input.function.semantic_metadata_enabled {
            for (name, hint) in
                collect_register_type_hints_with_names(&input.function.blocks, register_name)
            {
                merge_type_hint(&mut input.reg_type_hints, name, hint);
            }
        }
        Self::full_semantics_for_function(input)
    }

    pub fn from_input_with_compile_missing_semantics(
        input: EngineAnalyzeRequestInput,
        compile_missing_semantics: bool,
    ) -> Self {
        Self::from_compile_missing_semantics(
            engine_analyze_request_parts_from_input(input),
            compile_missing_semantics,
        )
    }

    pub fn full_semantics(parts: EngineAnalyzeRequestParts) -> Self {
        Self::from_parts(parts, EngineSemanticMode::Full)
    }

    pub fn from_compile_missing_semantics(
        parts: EngineAnalyzeRequestParts,
        compile_missing_semantics: bool,
    ) -> Self {
        let semantic_mode = if compile_missing_semantics {
            EngineSemanticMode::Full
        } else {
            EngineSemanticMode::Optional
        };
        Self::from_parts(parts, semantic_mode)
    }

    fn from_parts(parts: EngineAnalyzeRequestParts, semantic_mode: EngineSemanticMode) -> Self {
        Self {
            function_name: parts.function_name,
            function_addr: parts.function_addr,
            blocks: parts.blocks,
            arch: parts.arch,
            source_snapshot: parts.source_snapshot,
            trusted_ssa: None,
            trusted_callees: Vec::new(),
            ptr_bits: parts.ptr_bits,
            semantic_metadata_enabled: parts.semantic_metadata_enabled,
            reg_type_hints: parts.reg_type_hints,
            parsed_context: parts.parsed_context,
            interproc_max_iterations: parts.interproc_max_iterations,
            symbolic_scope: parts.symbolic_scope,
            semantic_mode,
            include_interproc_summary_set: parts.include_interproc_summary_set,
            execution: EngineExecutionControl::default(),
        }
    }

    pub fn with_execution_control(mut self, execution: EngineExecutionControl) -> Self {
        self.execution = execution;
        self
    }

    /// Attach one request-local trusted SSA owner.
    ///
    /// The exact retained lift replaces every detached identity, block,
    /// architecture, source snapshot, type hint, external context, scope, and
    /// precomputed-semantic input. Root-only interprocedural solving remains
    /// enabled when requested because it derives solely from this exact owner.
    /// Trusted authority remains request-local.
    pub fn with_trusted_ssa(mut self, trusted: Arc<r2ssa::TrustedSsaArtifact>) -> Self {
        let function_addr = trusted.source().function().address();
        self.function_name = format!("fcn_{function_addr:x}");
        self.function_addr = function_addr;
        self.blocks = trusted.source_blocks().to_vec();
        self.arch = Some(trusted.arch_spec().clone());
        self.ptr_bits = engine_arch_target(self.arch.as_ref()).1;
        self.source_snapshot = None;
        self.semantic_metadata_enabled = true;
        self.reg_type_hints.clear();
        let signature = trusted_source_signature(&trusted, self.ptr_bits);
        self.parsed_context = r2types::ParsedExternalContext {
            known_function_signatures: trusted_callee_signatures(&trusted, self.ptr_bits),
            stack_slots: trusted_stack_slot_names(&trusted, self.ptr_bits),
            callconv: signature
                .as_ref()
                .and_then(|(_, callconv, _)| callconv.clone()),
            noreturn: signature.as_ref().is_some_and(|(_, _, noreturn)| *noreturn),
            current_signature: signature.as_ref().map(|(spec, _, _)| spec.clone()),
            merged_signature: signature.map(|(spec, _, _)| spec),
            external_type_db: trusted_external_type_db(&trusted),
            ..r2types::ParsedExternalContext::default()
        };
        self.interproc_max_iterations = self.interproc_max_iterations.max(1);
        self.symbolic_scope = None;
        self.semantic_mode = EngineSemanticMode::Full;
        self.trusted_ssa = Some(trusted);
        self
    }

    /// Attach the bodies of the functions the root calls, captured with it.
    ///
    /// Without them the solver has no callee to look at and must assume every
    /// direct call does anything to anything it was handed.
    pub fn with_trusted_callees(
        mut self,
        callees: impl IntoIterator<Item = Arc<r2ssa::TrustedSsaArtifact>>,
    ) -> Self {
        self.trusted_callees = callees
            .into_iter()
            .map(|callee| callee.shared_artifact())
            .collect();
        self
    }

    fn with_optional_trusted_ssa(self, trusted: Option<Arc<r2ssa::TrustedSsaArtifact>>) -> Self {
        match trusted {
            Some(trusted) => self.with_trusted_ssa(trusted),
            None => self,
        }
    }

    fn canonicalize_trusted(self) -> Self {
        let trusted = self.trusted_ssa.clone();
        self.with_optional_trusted_ssa(trusted)
    }

    pub fn with_cancellation(mut self, cancellation: EngineCancellationToken) -> Self {
        self.execution.replace_cancellation(cancellation);
        self
    }

    pub fn with_deadline(mut self, deadline: Instant) -> Self {
        self.execution.replace_deadline(deadline);
        self
    }

    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.execution.replace_deadline(
            Instant::now()
                .checked_add(timeout)
                .unwrap_or_else(Instant::now),
        );
        self
    }
}

fn engine_analyze_request_input_from_function(
    input: EngineAnalyzeFunctionRequestInput,
) -> EngineAnalyzeRequestInput {
    EngineAnalyzeRequestInput {
        function_name: input.function.function_name,
        function_addr: input.function.function_addr,
        blocks: input.function.blocks,
        arch: input.function.arch,
        source_snapshot: input.function.source_snapshot,
        ptr_bits: input.ptr_bits,
        semantic_metadata_enabled: input.function.semantic_metadata_enabled,
        reg_type_hints: input.reg_type_hints,
        parsed_context: input.parsed_context,
        interproc_max_iterations: input.interproc_max_iterations,
        symbolic_scope: input.symbolic_scope,
        include_interproc_summary_set: input.include_interproc_summary_set,
    }
}

fn engine_analyze_request_parts_from_input(
    input: EngineAnalyzeRequestInput,
) -> EngineAnalyzeRequestParts {
    let ptr_bits = input
        .ptr_bits
        .unwrap_or_else(|| engine_arch_target(input.arch.as_ref()).1);
    EngineAnalyzeRequestParts {
        function_name: input.function_name,
        function_addr: input.function_addr,
        blocks: input.blocks,
        arch: input.arch,
        source_snapshot: input.source_snapshot,
        ptr_bits,
        semantic_metadata_enabled: input.semantic_metadata_enabled,
        reg_type_hints: input.reg_type_hints,
        parsed_context: input.parsed_context,
        interproc_max_iterations: input.interproc_max_iterations,
        symbolic_scope: input.symbolic_scope,
        include_interproc_summary_set: input.include_interproc_summary_set,
    }
}

#[derive(Debug)]
pub struct EngineAnalyzeResponse {
    pub artifact: EngineAnalysisArtifact,
    pub metrics: EngineMetrics,
    pub diagnostics: EngineDiagnostics,
}

#[derive(Debug, Clone)]
struct EngineDecompileRequest {
    pub function_name: String,
    pub source_owned_facts: r2types::SourceOwnedFunctionFacts,
    pub trusted_ssa: Option<Arc<r2ssa::TrustedSsaArtifact>>,
    pub input_quality: Option<r2types::FunctionInputQualityFacts>,
    pub render_target: EngineRenderTarget,
    pub execution: EngineExecutionControl,
    pub metrics: EngineMetrics,
}

impl EngineDecompileRequest {
    fn function_facts(&self) -> &FunctionFacts {
        self.source_owned_facts.report()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct EngineFunctionDecompileRequest {
    analysis: EngineAnalyzeRequest,
    input_quality: Option<EngineFunctionInputQuality>,
}

#[derive(Debug, Clone)]
pub struct EngineFunctionDecompileRequestInput {
    function: EngineFunctionInput,
    ptr_bits: Option<u32>,
    parsed_context: r2types::ParsedExternalContext,
    interproc_max_iterations: usize,
    symbolic_scope: Option<r2sym::PreparedFunctionScope>,
    input_quality: EngineFunctionInputQuality,
    execution: EngineExecutionControl,
    trusted_ssa: Option<Arc<r2ssa::TrustedSsaArtifact>>,
    trusted_callees: Vec<Arc<r2ssa::TrustedSsaArtifact>>,
}

impl EngineFunctionDecompileRequestInput {
    pub fn single_function(
        function: EngineFunctionInput,
        ptr_bits: Option<u32>,
        parsed_context: r2types::ParsedExternalContext,
    ) -> Self {
        let function_block_count = function.blocks.len();
        Self {
            function,
            ptr_bits,
            parsed_context,
            interproc_max_iterations: 1,
            symbolic_scope: None,
            input_quality: EngineFunctionInputQuality::complete(function_block_count),
            execution: EngineExecutionControl::default(),
            trusted_ssa: None,
            trusted_callees: Vec::new(),
        }
    }

    pub fn with_input_quality(mut self, input_quality: EngineFunctionInputQuality) -> Self {
        self.input_quality = input_quality;
        self
    }

    pub fn with_execution_control(mut self, execution: EngineExecutionControl) -> Self {
        self.execution = execution;
        self
    }

    pub fn with_trusted_ssa(mut self, trusted: Arc<r2ssa::TrustedSsaArtifact>) -> Self {
        self.trusted_ssa = Some(trusted);
        self
    }

    /// Attach the bodies of the functions the root calls, captured with it.
    pub fn with_trusted_callees(
        mut self,
        callees: impl IntoIterator<Item = Arc<r2ssa::TrustedSsaArtifact>>,
    ) -> Self {
        self.trusted_callees = callees.into_iter().collect();
        self
    }

    pub fn with_cancellation(mut self, cancellation: EngineCancellationToken) -> Self {
        self.execution.replace_cancellation(cancellation);
        self
    }

    pub fn with_deadline(mut self, deadline: Instant) -> Self {
        self.execution.replace_deadline(deadline);
        self
    }

    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.execution.replace_deadline(
            Instant::now()
                .checked_add(timeout)
                .unwrap_or_else(Instant::now),
        );
        self
    }

    pub fn with_interproc_scope(
        mut self,
        interproc_max_iterations: usize,
        symbolic_scope: Option<r2sym::PreparedFunctionScope>,
    ) -> Self {
        self.interproc_max_iterations = interproc_max_iterations.max(1);
        self.symbolic_scope = symbolic_scope;
        self
    }
}

impl EngineFunctionDecompileRequest {
    pub(crate) fn full_semantics_for_function(input: EngineFunctionDecompileRequestInput) -> Self {
        let trusted_ssa = input.trusted_ssa;
        let trusted_callees = input.trusted_callees;
        Self {
            input_quality: Some(input.input_quality),
            analysis: EngineAnalyzeRequest::full_semantics_for_function(
                EngineAnalyzeFunctionRequestInput {
                    function: input.function,
                    ptr_bits: input.ptr_bits,
                    reg_type_hints: HashMap::new(),
                    parsed_context: input.parsed_context,
                    interproc_max_iterations: input.interproc_max_iterations,
                    symbolic_scope: input.symbolic_scope,
                    include_interproc_summary_set: true,
                },
            )
            .with_execution_control(input.execution)
            .with_optional_trusted_ssa(trusted_ssa)
            .with_trusted_callees(trusted_callees),
        }
    }
}

pub struct EngineSignatureInferenceRequest<'a> {
    pub analysis: &'a EngineAnalysis,
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
    pub prepared: &'a Arc<SsaArtifact>,
    pub scope: Option<&'a r2sym::PreparedFunctionScope>,
    pub arch: Option<&'a r2il::ArchSpec>,
    pub symbols: &'a r2sym::FunctionSymbolSnapshot,
    pub merge_states: bool,
    pub config_profile: EngineSymbolicConfigProfile,
    pub seed: EngineSymbolicStateSeed<'a>,
}

/// Typed refusal/stop boundary shared by symbolic engine requests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineSymbolicRequestError {
    ExecutionStopped(r2sym::SymExecutionStopReason),
    ReplaySeed(r2sym::PreparedReplaySeedError),
}

impl std::fmt::Display for EngineSymbolicRequestError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExecutionStopped(reason) => reason.fmt(formatter),
            Self::ReplaySeed(reason) => reason.fmt(formatter),
        }
    }
}

impl std::error::Error for EngineSymbolicRequestError {}

impl From<r2sym::SymExecutionStopReason> for EngineSymbolicRequestError {
    fn from(reason: r2sym::SymExecutionStopReason) -> Self {
        Self::ExecutionStopped(reason)
    }
}

impl From<r2sym::PreparedReplaySeedError> for EngineSymbolicRequestError {
    fn from(reason: r2sym::PreparedReplaySeedError) -> Self {
        Self::ReplaySeed(reason)
    }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineSymbolicRunError {
    InvalidSpec(String),
    ExecutionStopped(r2sym::SymExecutionStopReason),
    ReplaySeed(r2sym::PreparedReplaySeedError),
}

impl std::fmt::Display for EngineSymbolicRunError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSpec(reason) => formatter.write_str(reason),
            Self::ExecutionStopped(reason) => reason.fmt(formatter),
            Self::ReplaySeed(reason) => reason.fmt(formatter),
        }
    }
}

impl std::error::Error for EngineSymbolicRunError {}

#[derive(Debug, Clone)]
pub struct EngineConditionedSymbolicScope {
    pub scope: r2sym::PreparedFunctionScope,
    pub prepared: Arc<r2ssa::SsaArtifact>,
    pub assumption_usage: r2ssa::AssumptionUsageReport,
    pub assumption_conditioned: bool,
}

#[derive(Debug, Clone)]
pub struct EngineTypeAnalysisRequest {
    pub analysis: EngineAnalyzeRequest,
    pub caller_prefers_bounded_type_plan: bool,
}

#[derive(Debug, Clone)]
pub struct EngineFunctionAnalysisReportRequest {
    pub analysis: EngineAnalyzeRequest,
    pub interproc_max_iters: usize,
    pub interproc_converged: bool,
    pub writeback_budget: r2types::TypeWritebackMutationBudget,
    pub writeback_apply_policy: r2types::TypeWritebackApplyPolicy,
}

#[derive(Debug, Clone)]
pub struct EngineFunctionAnalysisArtifactRequest {
    pub analysis: EngineAnalyzeRequest,
}

#[derive(Debug, Clone)]
pub struct EngineInterprocSummaryReportRequest {
    pub analysis: EngineAnalyzeRequest,
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub scope_report: Option<serde_json::Value>,
}

#[derive(Debug, Clone)]
pub struct EngineInterprocSummaryReportResponse {
    pub report: EngineInterprocSummaryJson,
    pub metrics: EngineMetrics,
    pub diagnostics: EngineDiagnostics,
}

#[derive(Debug, Clone)]
pub struct EngineFunctionAnalysisArtifactRequestInput {
    pub function: EngineFunctionInput,
    pub ptr_bits: Option<u32>,
    pub parsed_context: r2types::ParsedExternalContext,
    pub interproc_max_iterations: usize,
    pub symbolic_scope: Option<r2sym::PreparedFunctionScope>,
}

#[derive(Debug, Clone)]
pub struct EngineFunctionAnalysisReportRequestInput {
    pub function: EngineFunctionInput,
    pub ptr_bits: Option<u32>,
    pub parsed_context: r2types::ParsedExternalContext,
    pub interproc_max_iters: usize,
    pub interproc_converged: bool,
    pub symbolic_scope: Option<r2sym::PreparedFunctionScope>,
    pub writeback_budget: r2types::TypeWritebackMutationBudget,
    pub writeback_apply_policy: r2types::TypeWritebackApplyPolicy,
}

impl EngineFunctionAnalysisArtifactRequest {
    pub fn full_semantics_for_function(input: EngineFunctionAnalysisArtifactRequestInput) -> Self {
        Self {
            analysis: EngineAnalyzeRequest::full_semantics_for_function(
                EngineAnalyzeFunctionRequestInput {
                    function: input.function,
                    ptr_bits: input.ptr_bits,
                    reg_type_hints: HashMap::new(),
                    parsed_context: input.parsed_context,
                    interproc_max_iterations: input.interproc_max_iterations,
                    symbolic_scope: input.symbolic_scope,
                    include_interproc_summary_set: true,
                },
            ),
        }
    }

    pub fn full_semantics_for_function_with_register_names<F>(
        input: EngineFunctionAnalysisArtifactRequestInput,
        register_name: F,
    ) -> Self
    where
        F: FnMut(&r2il::Varnode) -> Option<String>,
    {
        Self {
            analysis: EngineAnalyzeRequest::full_semantics_for_function_with_register_names(
                EngineAnalyzeFunctionRequestInput {
                    function: input.function,
                    ptr_bits: input.ptr_bits,
                    reg_type_hints: HashMap::new(),
                    parsed_context: input.parsed_context,
                    interproc_max_iterations: input.interproc_max_iterations,
                    symbolic_scope: input.symbolic_scope,
                    include_interproc_summary_set: true,
                },
                register_name,
            ),
        }
    }
}

impl EngineInterprocSummaryReportRequest {
    pub fn full_semantics_for_function(
        input: EngineFunctionAnalysisArtifactRequestInput,
        iterations: usize,
        max_iterations: usize,
        converged: bool,
        scope_report: Option<serde_json::Value>,
    ) -> Self {
        Self {
            analysis: EngineFunctionAnalysisArtifactRequest::full_semantics_for_function(input)
                .analysis,
            iterations,
            max_iterations,
            converged,
            scope_report,
        }
    }

    pub fn full_semantics_for_function_with_register_names<F>(
        input: EngineFunctionAnalysisArtifactRequestInput,
        register_name: F,
        iterations: usize,
        max_iterations: usize,
        converged: bool,
        scope_report: Option<serde_json::Value>,
    ) -> Self
    where
        F: FnMut(&r2il::Varnode) -> Option<String>,
    {
        Self {
            analysis:
                EngineFunctionAnalysisArtifactRequest::full_semantics_for_function_with_register_names(
                    input,
                    register_name,
                )
                .analysis,
            iterations,
            max_iterations,
            converged,
            scope_report,
        }
    }
}

impl EngineFunctionAnalysisReportRequest {
    pub fn full_semantics_for_function(input: EngineFunctionAnalysisReportRequestInput) -> Self {
        Self {
            analysis: EngineAnalyzeRequest::full_semantics_for_function(
                EngineAnalyzeFunctionRequestInput {
                    function: input.function,
                    ptr_bits: input.ptr_bits,
                    reg_type_hints: HashMap::new(),
                    parsed_context: input.parsed_context,
                    interproc_max_iterations: input.interproc_max_iters,
                    symbolic_scope: input.symbolic_scope,
                    include_interproc_summary_set: true,
                },
            ),
            interproc_max_iters: input.interproc_max_iters,
            interproc_converged: input.interproc_converged,
            writeback_budget: input.writeback_budget,
            writeback_apply_policy: input.writeback_apply_policy,
        }
    }

    pub fn full_semantics_for_function_with_register_names<F>(
        input: EngineFunctionAnalysisReportRequestInput,
        register_name: F,
    ) -> Self
    where
        F: FnMut(&r2il::Varnode) -> Option<String>,
    {
        Self {
            analysis: EngineAnalyzeRequest::full_semantics_for_function_with_register_names(
                EngineAnalyzeFunctionRequestInput {
                    function: input.function,
                    ptr_bits: input.ptr_bits,
                    reg_type_hints: HashMap::new(),
                    parsed_context: input.parsed_context,
                    interproc_max_iterations: input.interproc_max_iters,
                    symbolic_scope: input.symbolic_scope,
                    include_interproc_summary_set: true,
                },
                register_name,
            ),
            interproc_max_iters: input.interproc_max_iters,
            interproc_converged: input.interproc_converged,
            writeback_budget: input.writeback_budget,
            writeback_apply_policy: input.writeback_apply_policy,
        }
    }
}

impl EngineTypeAnalysisRequest {
    pub fn from_interproc_budget(
        analysis: EngineAnalyzeRequest,
        interproc_max_iters: usize,
        interproc_converged: bool,
    ) -> Self {
        Self {
            analysis,
            caller_prefers_bounded_type_plan: type_analysis_interproc_prefers_bounded_plan(
                interproc_max_iters,
                interproc_converged,
            ),
        }
    }
}

pub fn type_analysis_interproc_prefers_bounded_plan(
    interproc_max_iters: usize,
    interproc_converged: bool,
) -> bool {
    interproc_max_iters <= 1 && !interproc_converged
}

#[derive(Debug)]
pub struct EngineTypeAnalysisResponse {
    type_analysis: r2types::TypeWritebackAnalysis,
    cfg_summary: CFGRiskSummary,
    route_decision: EngineTypeRouteDecision,
    decompile_route: r2types::DecompileRouteFacts,
    callsite_count: usize,
    current_summary: Option<r2ssa::FunctionSemanticSummary>,
    metrics: EngineMetrics,
    diagnostics: EngineDiagnostics,
}

impl EngineTypeAnalysisResponse {
    pub fn type_analysis(&self) -> &r2types::TypeWritebackAnalysis {
        &self.type_analysis
    }

    pub fn function_facts(&self) -> &FunctionFacts {
        self.type_analysis.function_facts()
    }

    pub fn cfg_summary(&self) -> &CFGRiskSummary {
        &self.cfg_summary
    }

    pub fn route_decision(&self) -> &EngineTypeRouteDecision {
        &self.route_decision
    }

    pub fn decompile_route(&self) -> &r2types::DecompileRouteFacts {
        &self.decompile_route
    }

    pub fn callsite_count(&self) -> usize {
        self.callsite_count
    }

    pub fn current_summary(&self) -> Option<&r2ssa::FunctionSemanticSummary> {
        self.current_summary.as_ref()
    }

    pub fn metrics(&self) -> &EngineMetrics {
        &self.metrics
    }

    pub fn diagnostics(&self) -> &EngineDiagnostics {
        &self.diagnostics
    }
}

#[derive(Debug, Clone)]
pub struct EngineDecompileResponse {
    pub output: String,
    pub binding_audit: BindingShadowAuditOutcome,
    pub effect_obligations: EffectObligationAudit,
    pub placement_audit: PlacementAudit,
    pub render_refusal: Option<DecompileRenderRefusal>,
    pub function_facts: FunctionFacts,
    pub input_quality: Option<r2types::FunctionInputQualityFacts>,
    pub metrics: EngineMetrics,
    pub diagnostics: EngineDiagnostics,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct EngineSession;

impl EngineSession {
    pub const fn new() -> Self {
        Self
    }

    pub fn analyze(&self, request: EngineAnalyzeRequest) -> Option<EngineAnalyzeResponse> {
        self.analyze_checked(request).ok()
    }

    pub fn analyze_checked(
        &self,
        mut request: EngineAnalyzeRequest,
    ) -> Result<EngineAnalyzeResponse, EngineExecutionRefusal> {
        // Re-derive the complete request at the consumption boundary so a
        // caller cannot attach authority and then mutate public analysis
        // fields into a detached configuration.
        request = request.canonicalize_trusted();
        let started = Instant::now();
        let mut metrics = EngineMetrics::default();
        poll_engine_execution(&request.execution, EnginePhase::SnapshotContext, &metrics)?;
        let phase_started = Instant::now();
        if request.source_snapshot.is_none() && request.trusted_ssa.is_none() {
            return Err(engine_execution_refusal(
                MISSING_SOURCE_SNAPSHOT_REFUSAL.to_string(),
                EnginePhase::SnapshotContext,
                metrics,
            ));
        }
        metrics.record_phase(
            EnginePhase::SnapshotContext,
            EnginePhaseStatus::Executed,
            phase_started.elapsed(),
        );
        let ssa_control = request.execution.ssa_execution_control();
        self.analyze_with_ssa_control(request, started, metrics, &ssa_control)
    }

    pub fn interproc_summary_report(
        &self,
        request: EngineInterprocSummaryReportRequest,
    ) -> Option<EngineInterprocSummaryReportResponse> {
        let EngineInterprocSummaryReportRequest {
            analysis,
            iterations,
            max_iterations,
            converged,
            scope_report,
        } = request;
        let analysis = analysis.canonicalize_trusted();
        let symbolic_scope = analysis.symbolic_scope.clone();
        let response = self.analyze(analysis)?;
        let summary = response
            .artifact
            .function_facts()
            .summary_view()
            .root_summary();
        let report = interproc_summary_json(EngineInterprocSummaryJsonInput {
            callsite_count: summary.map(|summary| summary.callsite_count).unwrap_or(0),
            iterations,
            max_iterations,
            converged,
            summary,
            scope_report: scope_report.as_ref(),
            symbolic_scope: symbolic_scope.as_ref(),
        });
        Some(EngineInterprocSummaryReportResponse {
            report,
            metrics: response.metrics,
            diagnostics: response.diagnostics,
        })
    }

    fn analyze_with_ssa_control<C: r2ssa::SsaWorkControl + ?Sized>(
        &self,
        request: EngineAnalyzeRequest,
        started: Instant,
        mut metrics: EngineMetrics,
        ssa_control: &C,
    ) -> Result<EngineAnalyzeResponse, EngineExecutionRefusal> {
        poll_engine_execution(&request.execution, EnginePhase::Ssa, &metrics)?;
        let ssa_started = Instant::now();
        let analysis = if let Some(trusted) = request.trusted_ssa.as_ref() {
            ssa_control
                .poll()
                .map_err(|error| ssa_prepare_execution_refusal(error.into(), metrics.clone()))?;
            Arc::new(EngineAnalysis::from_trusted_ssa(trusted))
        } else {
            let Some(source_snapshot) = request.source_snapshot.as_deref() else {
                return Err(engine_execution_refusal(
                    MISSING_SOURCE_SNAPSHOT_REFUSAL.to_string(),
                    EnginePhase::SnapshotContext,
                    metrics,
                ));
            };
            Arc::new(
                match build_engine_analysis_from_parts_with_control(
                    &request.function_name,
                    &request.blocks,
                    request.arch.as_ref(),
                    source_snapshot,
                    ssa_control,
                ) {
                    Ok(analysis) => analysis,
                    Err(error) => {
                        metrics.record_phase(
                            EnginePhase::Ssa,
                            EnginePhaseStatus::Refused,
                            ssa_started.elapsed(),
                        );
                        return Err(ssa_prepare_execution_refusal(error, metrics));
                    }
                },
            )
        };
        metrics.record_phase(
            EnginePhase::Ssa,
            EnginePhaseStatus::Executed,
            ssa_started.elapsed(),
        );
        metrics.record_phase(
            EnginePhase::Obligations,
            EnginePhaseStatus::Folded,
            Duration::default(),
        );
        metrics.ssa_time = ssa_started.elapsed();

        poll_engine_execution(&request.execution, EnginePhase::Symbolic, &metrics)?;
        let artifact_started = Instant::now();
        let artifact = match build_engine_analysis_artifact(&request, analysis.as_ref()) {
            Ok(artifact) => artifact,
            Err(reason) => {
                poll_engine_execution(&request.execution, EnginePhase::Types, &metrics)?;
                return Err(engine_execution_refusal(
                    reason,
                    EnginePhase::Types,
                    metrics,
                ));
            }
        };
        let artifact_elapsed = artifact_started.elapsed();
        if artifact.function_facts().semantic_artifact().is_some() {
            metrics.record_phase(
                EnginePhase::Symbolic,
                EnginePhaseStatus::Folded,
                Duration::default(),
            );
        }
        metrics.record_phase(
            EnginePhase::Types,
            EnginePhaseStatus::Executed,
            artifact_elapsed,
        );
        metrics.type_time = artifact_elapsed;
        poll_engine_execution(&request.execution, EnginePhase::Certification, &metrics)?;
        metrics.planning_time = started.elapsed();
        Ok(EngineAnalyzeResponse {
            artifact,
            metrics,
            diagnostics: EngineDiagnostics::default(),
        })
    }

    pub fn type_function(
        &self,
        request: EngineTypeAnalysisRequest,
    ) -> Option<EngineTypeAnalysisResponse> {
        self.type_function_checked(request).ok()
    }

    pub fn type_function_checked(
        &self,
        request: EngineTypeAnalysisRequest,
    ) -> Result<EngineTypeAnalysisResponse, EngineExecutionRefusal> {
        let started = Instant::now();
        let analysis_request = request.analysis.canonicalize_trusted();
        let analyze_response = self.analyze_checked(analysis_request.clone())?;
        let artifact = analyze_response.artifact;
        let cfg_summary = artifact.ssa_func().function().cfg_risk_summary();
        let route_decision = type_route_decision(
            artifact.function_facts(),
            &cfg_summary,
            request.caller_prefers_bounded_type_plan,
        );
        if !matches!(route_decision.kind, EngineTypeRouteKind::FullWriteback) {
            return Err(engine_execution_refusal(
                route_decision.reason.clone().unwrap_or_else(|| {
                    "bounded or summary-only type evidence cannot authorize writeback".to_string()
                }),
                EnginePhase::Types,
                analyze_response.metrics,
            ));
        }
        let decompile_decision = decompile_route_decision(
            &analysis_request.function_name,
            artifact.function_facts(),
            Some(artifact.ssa_func()),
            &cfg_summary,
        );
        let callsite_count = count_prepared_callsites(&artifact.ssa_func().local_ssa_blocks());
        let current_summary = current_interproc_summary(artifact.function_facts());
        let EngineAnalysisArtifact {
            type_analysis,
            trusted_ssa: _,
        } = artifact;

        Ok(EngineTypeAnalysisResponse {
            type_analysis,
            cfg_summary,
            route_decision,
            decompile_route: decompile_decision.route,
            callsite_count,
            current_summary,
            metrics: EngineMetrics {
                planning_time: started.elapsed(),
                ..analyze_response.metrics
            },
            diagnostics: analyze_response.diagnostics,
        })
    }

    pub fn type_function_report_payload(
        &self,
        mut request: EngineFunctionAnalysisReportRequest,
    ) -> Option<EngineFunctionAnalysisReportPayload> {
        request.analysis = request.analysis.canonicalize_trusted();
        let function_name = request.analysis.function_name.clone();
        let function_addr = request.analysis.function_addr;
        let response = self.type_function(EngineTypeAnalysisRequest::from_interproc_budget(
            request.analysis,
            request.interproc_max_iters,
            request.interproc_converged,
        ))?;
        Some(function_analysis_report_payload_from_type_response(
            function_name,
            function_addr,
            response,
            request.writeback_budget,
            request.writeback_apply_policy,
        ))
    }

    pub(crate) fn decompile_function(
        &self,
        request: EngineFunctionDecompileRequest,
    ) -> EngineDecompileResponse {
        let started = Instant::now();
        let EngineFunctionDecompileRequest {
            analysis: analysis_request,
            input_quality,
        } = request;
        let execution = analysis_request.execution.clone();
        let canonical_name = analysis_request.function_name.clone();
        let display_name = canonical_name.clone();
        if let Err(refusal) = poll_engine_execution(
            &execution,
            EnginePhase::SnapshotContext,
            &EngineMetrics::default(),
        ) {
            return refused_decompile_response_with_metrics(
                &display_name,
                &refusal.reason,
                None,
                *refusal.metrics,
                *refusal.diagnostics,
            );
        }
        let actual_lifted_blocks = analysis_request.blocks.len();
        let input_quality_facts = if let Some(quality) = input_quality {
            let reason = quality.refusal_reason_for_actual_lifted_blocks(actual_lifted_blocks);
            let facts = function_input_quality_facts(quality, actual_lifted_blocks, reason.clone());
            if let Some(reason) = reason {
                return refused_decompile_response(
                    &display_name,
                    &reason,
                    started.elapsed(),
                    Some(facts),
                );
            }
            Some(facts)
        } else {
            None
        };
        let (_, requested_render_target) = EngineRenderTarget::for_arch_with_ptr_bits(
            analysis_request.arch.as_ref(),
            analysis_request.ptr_bits,
        );
        let probe = decompile_probe_decision(&analysis_request.blocks);
        if actual_lifted_blocks > ENGINE_DECOMPILE_MAX_BLOCKS
            || probe.op_count > ENGINE_DECOMPILE_MAX_OPS
        {
            let reason = format!(
                "decompile complexity limit exceeded: blocks={actual_lifted_blocks}/{} ops={}/{}",
                ENGINE_DECOMPILE_MAX_BLOCKS, probe.op_count, ENGINE_DECOMPILE_MAX_OPS
            );
            return refused_decompile_response(
                &display_name,
                &reason,
                started.elapsed(),
                input_quality_facts,
            );
        }
        let analyze_response = match self.analyze_checked(analysis_request) {
            Ok(response) => response,
            Err(refusal) => {
                return refused_decompile_response_with_metrics(
                    &display_name,
                    &refusal.reason,
                    input_quality_facts,
                    *refusal.metrics,
                    *refusal.diagnostics,
                );
            }
        };

        let mut metrics = analyze_response.metrics;
        let analyze_diagnostics = analyze_response.diagnostics;
        let artifact = analyze_response.artifact;
        let analyzed_function_facts = artifact.function_facts().clone();
        let Some(render_target) = EngineRenderTarget::for_prepared(artifact.ssa_func()) else {
            metrics.refuse_from(EnginePhase::Normalization);
            return refused_decompile_response_with_metrics_and_audits(
                &display_name,
                "source-owned machine context cannot define an exact render target",
                input_quality_facts,
                metrics,
                analyze_diagnostics,
                Some(analyzed_function_facts),
                BindingShadowAuditOutcome::NotRun,
                EffectObligationAudit::NOT_RUN,
                PlacementAudit::NotRun,
                None,
            );
        };
        if render_target != requested_render_target {
            metrics.refuse_from(EnginePhase::Normalization);
            return refused_decompile_response_with_metrics_and_audits(
                &display_name,
                "requested render target does not match the source-owned machine context",
                input_quality_facts,
                metrics,
                analyze_diagnostics,
                Some(analyzed_function_facts),
                BindingShadowAuditOutcome::NotRun,
                EffectObligationAudit::NOT_RUN,
                PlacementAudit::NotRun,
                None,
            );
        }

        if let Err(refusal) =
            poll_engine_execution(&execution, EnginePhase::Normalization, &metrics)
        {
            return refused_decompile_response_with_metrics_and_audits(
                &display_name,
                &refusal.reason,
                input_quality_facts,
                *refusal.metrics,
                *refusal.diagnostics,
                Some(analyzed_function_facts),
                BindingShadowAuditOutcome::NotRun,
                EffectObligationAudit::NOT_RUN,
                PlacementAudit::NotRun,
                None,
            );
        }
        let normalization_started = Instant::now();
        let cfg_summary = artifact.ssa_func().function().cfg_risk_summary();
        let route = decompile_route_decision(
            &display_name,
            artifact.function_facts(),
            Some(artifact.ssa_func()),
            &cfg_summary,
        )
        .route;
        let finalization = r2types::DecompileFinalization {
            kind: route.kind,
            reason: route
                .reason
                .clone()
                .or_else(|| route.fallback_comment.clone())
                .unwrap_or_else(|| "engine decompile route decision".to_string()),
            fallback_comment: route.fallback_comment,
        };
        let EngineAnalysisArtifact {
            type_analysis,
            trusted_ssa,
        } = artifact;
        let source_owned_facts = match type_analysis.finalize_for_decompile(finalization) {
            Ok(facts) => facts,
            Err(_) => {
                metrics.refuse_from(EnginePhase::Normalization);
                return refused_decompile_response_with_metrics_and_audits(
                    &display_name,
                    "requested decompile route is incompatible with source-owned facts",
                    input_quality_facts,
                    metrics,
                    analyze_diagnostics,
                    Some(analyzed_function_facts),
                    BindingShadowAuditOutcome::NotRun,
                    EffectObligationAudit::NOT_RUN,
                    PlacementAudit::NotRun,
                    None,
                );
            }
        };
        metrics.record_phase(
            EnginePhase::Normalization,
            EnginePhaseStatus::Executed,
            normalization_started.elapsed(),
        );
        self.decompile(EngineDecompileRequest {
            function_name: display_name,
            source_owned_facts,
            trusted_ssa,
            input_quality: input_quality_facts,
            render_target,
            execution,
            metrics,
        })
    }

    pub fn decompile_function_from_input(
        &self,
        input: EngineFunctionDecompileRequestInput,
    ) -> EngineDecompileResponse {
        let actual_lifted_blocks = input.function.blocks.len();
        if let Some(reason) = input
            .input_quality
            .refusal_reason_for_actual_lifted_blocks(actual_lifted_blocks)
        {
            let input_quality = function_input_quality_facts(
                input.input_quality,
                actual_lifted_blocks,
                Some(reason.clone()),
            );
            return refused_decompile_response(
                &input.function.function_name,
                &reason,
                Duration::default(),
                Some(input_quality),
            );
        }
        self.decompile_function(EngineFunctionDecompileRequest::full_semantics_for_function(
            input,
        ))
    }

    fn decompile(&self, request: EngineDecompileRequest) -> EngineDecompileResponse {
        let render_control = request.execution.ssa_execution_control();
        self.decompile_with_r2dec_control(request, &render_control)
    }

    fn decompile_with_r2dec_control<C: r2ssa::SsaWorkControl>(
        &self,
        request: EngineDecompileRequest,
        render_control: &C,
    ) -> EngineDecompileResponse {
        let started = Instant::now();
        let input_quality = request.input_quality.clone();
        let response_function_facts = request.function_facts().clone();
        if request.trusted_ssa.as_deref().is_some_and(|trusted| {
            !trusted.shares_artifact(&request.source_owned_facts.shared_source())
        }) {
            return refused_decompile_response_with_metrics_and_audits(
                &request.function_name,
                "trusted SSA does not match the source-owned function facts",
                input_quality.clone(),
                request.metrics,
                EngineDiagnostics::default(),
                Some(response_function_facts),
                BindingShadowAuditOutcome::NotRun,
                EffectObligationAudit::NOT_RUN,
                PlacementAudit::NotRun,
                None,
            );
        }
        let mut diagnostics = decompile_diagnostics_from_function_facts(request.function_facts());
        let planning_time = started.elapsed();

        if let Err(refusal) = poll_engine_execution(
            &request.execution,
            EnginePhase::Certification,
            &request.metrics,
        ) {
            return refused_decompile_response_with_metrics_and_audits(
                &request.function_name,
                &refusal.reason,
                input_quality.clone(),
                *refusal.metrics,
                *refusal.diagnostics,
                Some(response_function_facts),
                BindingShadowAuditOutcome::NotRun,
                EffectObligationAudit::NOT_RUN,
                PlacementAudit::NotRun,
                None,
            );
        }

        let render_started = Instant::now();
        let rendered = match render_engine_decompile_request(&request, render_control) {
            Ok(rendered) => rendered,
            Err(stop) => {
                let render_time = render_started.elapsed();
                let metrics = engine_metrics_for_render_stop(
                    request.metrics,
                    &stop,
                    planning_time,
                    render_time,
                );
                let binding_audit = *stop.binding_audit;
                let effect_obligations = *stop.effect_obligations;
                let placement_audit = stop.placement_audit;
                let render_refusal = stop.render_refusal.map(|refusal| *refusal);
                let refusal = engine_render_execution_refusal(stop.reason, stop.phase, metrics);
                return refused_decompile_response_with_metrics_and_audits(
                    &request.function_name,
                    &refusal.reason,
                    input_quality.clone(),
                    *refusal.metrics,
                    *refusal.diagnostics,
                    Some(response_function_facts),
                    binding_audit,
                    effect_obligations,
                    placement_audit,
                    render_refusal,
                );
            }
        };
        let render_time = render_started.elapsed();
        let mut metrics = request.metrics;
        if rendered.structuring_executed {
            metrics.record_phase(
                EnginePhase::Structuring,
                EnginePhaseStatus::Folded,
                Duration::default(),
            );
        }
        match &rendered.stopped {
            // A rendering and a stop. The phases that finished are folded and the
            // one that stopped is refused, exactly as a discarded rendering would
            // have recorded -- the difference is that the body survives.
            Some(stop) => {
                if stop.certification_completed {
                    metrics.record_folded_if_not_executed(EnginePhase::Certification);
                }
                if stop.normalization_completed {
                    metrics.record_folded_if_not_executed(EnginePhase::Normalization);
                }
                if stop.structuring_completed {
                    metrics.record_folded_if_not_executed(EnginePhase::Structuring);
                }
                metrics.record_phase(stop.phase, EnginePhaseStatus::Refused, render_time);
            }
            None => metrics.record_phase(
                EnginePhase::Rendering,
                EnginePhaseStatus::Executed,
                render_time,
            ),
        }
        diagnostics
            .warnings
            .extend(rendered.semantic_kernel_warnings);
        if let Some(stop) = &rendered.stopped {
            // The reason the run gives for itself is the stop, not the route it
            // was taking when the stop arrived. The refusal is recorded too: the
            // body above is what was reached, and a reader is entitled to know
            // it is not the whole function.
            diagnostics.route_reason = Some(stop.reason.clone());
            diagnostics.refusal = Some(stop.reason.clone());
        }
        metrics.planning_time += planning_time;
        metrics.render_time = render_time;
        let rendering_stopped = rendered.stopped.is_some();
        let (output, binding_audit, effect_obligations, placement_audit, render_refusal) =
            rendered.product.finalize();
        if !rendering_stopped && let Some(reason) = placement_refusal_reason(placement_audit) {
            metrics.record_phase(
                EnginePhase::Rendering,
                EnginePhaseStatus::Refused,
                render_time,
            );
            return refused_decompile_response_with_metrics_and_audits(
                &request.function_name,
                &reason,
                input_quality,
                metrics,
                diagnostics,
                Some(response_function_facts),
                binding_audit,
                effect_obligations,
                placement_audit,
                render_refusal,
            );
        }
        if !rendering_stopped && let Some(refusal) = render_refusal {
            let reason = render_refusal_reason(refusal);
            metrics.record_phase(
                EnginePhase::Rendering,
                EnginePhaseStatus::Refused,
                render_time,
            );
            return refused_decompile_response_with_metrics_and_audits(
                &request.function_name,
                &reason,
                input_quality,
                metrics,
                diagnostics,
                Some(response_function_facts),
                binding_audit,
                effect_obligations,
                placement_audit,
                Some(refusal),
            );
        }
        if !rendering_stopped
            && let Some(reason) = effect_obligation_refusal_reason(effect_obligations)
        {
            metrics.record_phase(
                EnginePhase::Rendering,
                EnginePhaseStatus::Refused,
                render_time,
            );
            return refused_decompile_response_with_metrics_and_audits(
                &request.function_name,
                &reason,
                input_quality,
                metrics,
                diagnostics,
                Some(response_function_facts),
                binding_audit,
                effect_obligations,
                placement_audit,
                None,
            );
        }
        if let Err(refusal) =
            poll_engine_execution(&request.execution, EnginePhase::FfiConversion, &metrics)
        {
            return refused_decompile_response_with_metrics_and_audits(
                &request.function_name,
                &refusal.reason,
                input_quality,
                *refusal.metrics,
                *refusal.diagnostics,
                Some(response_function_facts),
                binding_audit,
                effect_obligations,
                placement_audit,
                None,
            );
        }
        let output = with_phase_timing_comment(output, &metrics);
        EngineDecompileResponse {
            output,
            binding_audit,
            effect_obligations,
            placement_audit,
            render_refusal,
            function_facts: response_function_facts,
            input_quality,
            metrics,
            diagnostics,
        }
    }

    pub fn symbolic_summary<'ctx>(
        &self,
        request: EngineSymbolicSummaryRequest<'ctx, '_>,
    ) -> Result<EngineSymbolicSummaryResponse<'ctx>, EngineSymbolicRequestError> {
        self.symbolic_summary_with_execution_control(request, EngineExecutionControl::default())
    }

    pub fn symbolic_summary_with_execution_control<'ctx>(
        &self,
        request: EngineSymbolicSummaryRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineSymbolicSummaryResponse<'ctx>, EngineSymbolicRequestError> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution
            .poll()
            .map_err(EngineSymbolicRequestError::ExecutionStopped)?;
        let context = request.context;
        let (assumption_usage, assumption_conditioned) =
            prepared_assumption_conditioning(context.prepared);
        let mut query_config = symbolic_query_config_for_context(&context);
        let scope = symbolic_scope_for_context(&context);
        let compiled = request.compile_semantics.then(|| {
            r2sym::compile_semantic_artifact_with_scope(
                context.z3_ctx,
                context.prepared,
                scope,
                query_config.summary_profile,
            )
        });
        symbolic_execution
            .poll()
            .map_err(EngineSymbolicRequestError::ExecutionStopped)?;
        if compiled
            .as_ref()
            .is_some_and(should_skip_expensive_symbolic_summary)
        {
            let initial_state = symbolic_initial_state(&context)?;
            let query_policy = symbolic_query_policy_for_state(
                &mut query_config,
                context.prepared,
                &initial_state,
                None,
            );
            return Ok(EngineSymbolicSummaryResponse {
                summary: empty_symbolic_summary(),
                compiled,
                query_policy,
                assumption_usage,
                assumption_conditioned,
            });
        }

        let initial_state = symbolic_initial_state(&context)?;
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            context.prepared,
            &initial_state,
            None,
        );
        let mut explorer =
            query_config.make_explorer_with_execution_control(context.z3_ctx, symbolic_execution);
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let summary = explorer.summarize_function(context.prepared, initial_state);
        explorer.execution_stop_reason().map_or(
            Ok(EngineSymbolicSummaryResponse {
                summary,
                compiled,
                query_policy,
                assumption_usage,
                assumption_conditioned,
            }),
            |reason| Err(EngineSymbolicRequestError::ExecutionStopped(reason)),
        )
    }

    pub fn symbolic_paths<'ctx>(
        &self,
        request: EngineSymbolicPathsRequest<'ctx, '_>,
    ) -> Result<EngineSymbolicPathsResponse<'ctx>, EngineSymbolicRequestError> {
        self.symbolic_paths_with_execution_control(request, EngineExecutionControl::default())
    }

    pub fn symbolic_paths_with_execution_control<'ctx>(
        &self,
        request: EngineSymbolicPathsRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineSymbolicPathsResponse<'ctx>, EngineSymbolicRequestError> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution
            .poll()
            .map_err(EngineSymbolicRequestError::ExecutionStopped)?;
        let context = request.context;
        let (assumption_usage, assumption_conditioned) =
            prepared_assumption_conditioning(context.prepared);
        let mut query_config = symbolic_query_config_for_context(&context);
        let initial_state = symbolic_initial_state(&context)?;
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            context.prepared,
            &initial_state,
            None,
        );
        let mut explorer =
            query_config.make_explorer_with_execution_control(context.z3_ctx, symbolic_execution);
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let summary = explorer.summarize_function(context.prepared, initial_state);
        let solution_limit = path_listing_solution_limit(summary.paths.len(), context.prepared);
        explorer.execution_stop_reason().map_or(
            Ok(EngineSymbolicPathsResponse {
                summary,
                explorer,
                solution_limit,
                query_policy,
                assumption_usage,
                assumption_conditioned,
            }),
            |reason| Err(EngineSymbolicRequestError::ExecutionStopped(reason)),
        )
    }

    pub fn symbolic_target_explore<'ctx>(
        &self,
        request: EngineTargetExploreRequest<'ctx, '_>,
    ) -> Result<EngineTargetExploreResponse<'ctx>, EngineSymbolicRequestError> {
        self.symbolic_target_explore_with_execution_control(
            request,
            EngineExecutionControl::default(),
        )
    }

    pub fn symbolic_target_explore_with_execution_control<'ctx>(
        &self,
        request: EngineTargetExploreRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineTargetExploreResponse<'ctx>, EngineSymbolicRequestError> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution
            .poll()
            .map_err(EngineSymbolicRequestError::ExecutionStopped)?;
        let context = request.context;
        let mut query_config = symbolic_query_config_for_context(&context);
        let scope = symbolic_scope_for_context(&context);
        let compiled = r2sym::compile_query_semantic_artifact_with_scope(
            context.z3_ctx,
            context.prepared,
            scope,
            request.target_addr,
            query_config.summary_profile,
        );
        symbolic_execution
            .poll()
            .map_err(EngineSymbolicRequestError::ExecutionStopped)?;
        let initial_state = symbolic_initial_state(&context)?;
        let selected_route = target_query_route_decision(TargetQueryRouteInput {
            z3_ctx: context.z3_ctx,
            compiled: &compiled,
            scope,
            target_addr: request.target_addr,
            arch: context.arch,
            symbols: context.symbols,
            explore_config: query_config.explore.clone(),
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(compiled.prepared()),
        });
        let prepared = compiled.prepared();
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer =
            query_config.make_explorer_with_execution_control(context.z3_ctx, symbolic_execution);
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let reach = explorer.can_reach_with_artifact_in_scope(
            prepared,
            scope,
            Some(&compiled),
            initial_state,
            request.target_addr,
        );
        let selected_route = reach.selected_route.clone();
        explorer.execution_stop_reason().map_or(
            Ok(EngineTargetExploreResponse {
                reach,
                explorer,
                compiled,
                selected_route,
                query_policy,
            }),
            |reason| Err(EngineSymbolicRequestError::ExecutionStopped(reason)),
        )
    }

    pub fn symbolic_target_solve<'ctx>(
        &self,
        request: EngineTargetSolveRequest<'ctx, '_>,
    ) -> Result<EngineTargetSolveResponse<'ctx>, EngineSymbolicRequestError> {
        self.symbolic_target_solve_with_execution_control(
            request,
            EngineExecutionControl::default(),
        )
    }

    pub fn symbolic_target_solve_with_execution_control<'ctx>(
        &self,
        request: EngineTargetSolveRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineTargetSolveResponse<'ctx>, EngineSymbolicRequestError> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution
            .poll()
            .map_err(EngineSymbolicRequestError::ExecutionStopped)?;
        let context = request.context;
        let mut query_config = symbolic_query_config_for_context(&context);
        let scope = symbolic_scope_for_context(&context);
        let compiled = r2sym::compile_query_semantic_artifact_with_scope(
            context.z3_ctx,
            context.prepared,
            scope,
            request.target_addr,
            query_config.summary_profile,
        );
        symbolic_execution
            .poll()
            .map_err(EngineSymbolicRequestError::ExecutionStopped)?;
        let initial_state = symbolic_initial_state(&context)?;
        let selected_route = target_query_route_decision(TargetQueryRouteInput {
            z3_ctx: context.z3_ctx,
            compiled: &compiled,
            scope,
            target_addr: request.target_addr,
            arch: context.arch,
            symbols: context.symbols,
            explore_config: query_config.explore.clone(),
            summary_profile: query_config.summary_profile,
            assumption_conflicted: prepared_assumption_conflicted(compiled.prepared()),
        });
        let prepared = compiled.prepared();
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            prepared,
            &initial_state,
            Some(&selected_route),
        );
        let mut explorer =
            query_config.make_explorer_with_execution_control(context.z3_ctx, symbolic_execution);
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let solve = explorer.solve_for_target_with_artifact_in_scope(
            prepared,
            scope,
            Some(&compiled),
            initial_state,
            request.target_addr,
        );
        let selected_route = solve.selected_route.clone();
        explorer.execution_stop_reason().map_or(
            Ok(EngineTargetSolveResponse {
                solve,
                explorer,
                compiled,
                selected_route,
                query_policy,
            }),
            |reason| Err(EngineSymbolicRequestError::ExecutionStopped(reason)),
        )
    }

    pub fn symbolic_run_spec<'ctx>(
        &self,
        request: EngineRunSpecRequest<'ctx, '_>,
    ) -> Result<EngineRunSpecResponse<'ctx>, EngineSymbolicRunError> {
        self.symbolic_run_spec_with_execution_control(request, EngineExecutionControl::default())
    }

    pub fn symbolic_run_spec_with_execution_control<'ctx>(
        &self,
        request: EngineRunSpecRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineRunSpecResponse<'ctx>, EngineSymbolicRunError> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution
            .poll()
            .map_err(EngineSymbolicRunError::ExecutionStopped)?;
        let context = request.context;
        let (assumption_usage, assumption_conditioned) =
            prepared_assumption_conditioning(context.prepared);
        let mut query_config = symbolic_query_config_for_context(&context);
        let start_pc = request
            .spec
            .start_pc(context.seed.entry_addr())
            .map_err(EngineSymbolicRunError::InvalidSpec)?;
        let mut initial_state = symbolic_initial_state_at(&context, start_pc)
            .map_err(EngineSymbolicRunError::ReplaySeed)?;
        request.spec.apply_to_state(&mut initial_state);
        let query_policy = symbolic_query_policy_for_state(
            &mut query_config,
            context.prepared,
            &initial_state,
            None,
        );
        let mut explorer = r2sym::PathExplorer::with_config_and_execution_control(
            context.z3_ctx,
            request.spec.to_explore_config(&query_config.explore),
            symbolic_execution,
        );
        install_symbolic_hooks_for_context(&mut explorer, &context, &query_policy);
        let result = explorer
            .run_spec(context.prepared, initial_state, request.spec)
            .map_err(EngineSymbolicRunError::InvalidSpec)?;
        let stats = explorer.stats().clone();
        let solver_stats = explorer.solver().stats();
        if let Some(reason) = explorer.execution_stop_reason() {
            return Err(EngineSymbolicRunError::ExecutionStopped(reason));
        }
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
            max_steps: Some(200_000),
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
    config.explore.max_steps = Some(SYMBOLIC_PATHS_MAX_STEPS);
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
        Arc::clone(&root.prepared)
    } else {
        Arc::new(root.prepared.with_assumptions(assumptions))
    };
    let scope = if assumptions.is_empty() {
        scope.clone()
    } else {
        scope
            .with_prepared_root(Arc::clone(&prepared))
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

fn symbolic_scope_for_context<'a>(
    context: &'a EngineSymbolicContextRequest<'_, '_>,
) -> Option<&'a r2sym::PreparedFunctionScope> {
    context
        .scope
        .and_then(|scope| scope.exact_for_artifact(context.prepared.as_ref()))
}

fn symbolic_initial_state<'ctx>(
    context: &EngineSymbolicContextRequest<'ctx, '_>,
) -> Result<r2sym::SymState<'ctx>, EngineSymbolicRequestError> {
    symbolic_initial_state_at(context, context.seed.display_entry_addr())
        .map_err(EngineSymbolicRequestError::ReplaySeed)
}

fn symbolic_initial_state_at<'ctx>(
    context: &EngineSymbolicContextRequest<'ctx, '_>,
    entry_addr: u64,
) -> Result<r2sym::SymState<'ctx>, r2sym::PreparedReplaySeedError> {
    let mut initial_state = r2sym::SymState::new(context.z3_ctx, entry_addr);
    match context.seed {
        EngineSymbolicStateSeed::Default { .. } => {
            let _ = r2sym::seed_default_state_for_prepared(
                &mut initial_state,
                context.prepared.as_ref(),
            );
        }
        EngineSymbolicStateSeed::Scope { .. } => {
            if let Some(scope) = symbolic_scope_for_context(context) {
                // The exact scope API deliberately withholds process-like
                // `main` arguments until a typed entrypoint role exists.
                let _ = r2sym::seed_scope_state_for_prepared(
                    &mut initial_state,
                    context.prepared.as_ref(),
                    scope,
                );
            }
        }
        EngineSymbolicStateSeed::Replay { seed, .. } => {
            r2sym::seed_replay_state_for_prepared(
                &mut initial_state,
                context.prepared.as_ref(),
                seed,
            )?;
        }
    }
    Ok(initial_state)
}

fn install_symbolic_hooks_for_context<'ctx>(
    explorer: &mut r2sym::PathExplorer<'ctx>,
    context: &EngineSymbolicContextRequest<'ctx, '_>,
    policy: &r2sym::QueryExecutionPolicy,
) {
    if let Some(scope) = symbolic_scope_for_context(context) {
        r2sym::install_symbolic_hooks_for_query_policy(
            explorer,
            r2sym::SymbolicHookInstallContext::new(
                context.z3_ctx,
                context.prepared.as_ref(),
                scope,
                context.arch,
                context.symbols.imported_names(),
                symbolic_query_config_for_context(context).summary_profile,
                policy,
            ),
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

fn effect_obligation_refusal_reason(audit: EffectObligationAudit) -> Option<String> {
    (matches!(audit.disposition, EffectObligationDisposition::Refused)
        || audit.refused != 0
        || audit.unaccounted != 0
        || audit.conflicts != 0)
        .then(|| {
            format!(
                "native effect obligations refused: {} refused, {} unaccounted, {} conflicts",
                audit.refused, audit.unaccounted, audit.conflicts
            )
        })
}

fn placement_refusal_reason(audit: PlacementAudit) -> Option<String> {
    match audit {
        PlacementAudit::Refused(refusal) => Some(format!(
            "native declaration placement refused: {}",
            refusal.kind()
        )),
        PlacementAudit::Applied | PlacementAudit::NotRun => None,
    }
}

/// The name of an enum variant, taken from its `Debug` form.
///
/// The refusal causes are typed and precise; what reached the reader was the
/// name of the *outer* variant alone, so sixty distinct journal failures all
/// printed as "observation journal" and could not be counted apart. The payload
/// already knows which one it is.
fn refusal_variant_name(debug: &str) -> String {
    debug
        .split(['(', '{', ' '])
        .next()
        .unwrap_or(debug)
        .to_string()
}

fn render_refusal_reason(refusal: DecompileRenderRefusal) -> String {
    match refusal {
        DecompileRenderRefusal::MissingMachineProjectionAuthorization(origin) => {
            format!(
                "native rendering refused: missing machine projection authorization: {origin:?}"
            )
        }
        DecompileRenderRefusal::MissingProgramVariableAuthorization => {
            "native rendering refused: missing program-variable authorization".to_string()
        }
        DecompileRenderRefusal::ObservationJournal(failure) => {
            format!(
                "native rendering refused: observation journal: {}",
                refusal_variant_name(&format!("{failure:?}"))
            )
        }
        DecompileRenderRefusal::DeclarationPlacement(refusal) => {
            format!(
                "native rendering refused: declaration placement: {}",
                refusal_variant_name(&format!("{refusal:?}"))
            )
        }
        DecompileRenderRefusal::RefusedBindingDisposition { .. } => {
            "native rendering refused: refused binding disposition".to_string()
        }
        DecompileRenderRefusal::NormalizationOriginUnavailable => {
            "native rendering refused: normalization origin unavailable".to_string()
        }
        DecompileRenderRefusal::UnrepresentableControlFlow => {
            "native rendering refused: unrepresentable control flow".to_string()
        }
        DecompileRenderRefusal::IncompleteEffectInventory => {
            "native rendering refused: incomplete effect inventory".to_string()
        }
        DecompileRenderRefusal::UnrepresentableOperation => {
            "native rendering refused: unrepresentable operation".to_string()
        }
    }
}

fn should_skip_expensive_symbolic_summary(compiled: &r2sym::SemanticArtifact) -> bool {
    compiled.diagnostics.skipped_large_cfg
        || compiled
            .prepared()
            .function()
            .cfg_risk_summary()
            .block_count
            > 96
}

fn decompile_diagnostics_from_function_facts(function_facts: &FunctionFacts) -> EngineDiagnostics {
    let Some(route) = function_facts.decompile_route() else {
        return EngineDiagnostics {
            plan: None,
            route_reason: Some("missing FunctionFacts decompile route".to_string()),
            warnings: vec![
                "decompile request reached render without engine-stamped route facts".to_string(),
            ],
            refusal: None,
        };
    };
    EngineDiagnostics {
        plan: Some(engine_plan_from_decompile_route_kind(route.kind)),
        route_reason: route.reason.clone(),
        warnings: Vec::new(),
        refusal: route.fallback_comment.clone(),
    }
}

fn engine_plan_from_decompile_route_kind(kind: r2types::DecompileRouteKind) -> EnginePlan {
    match kind {
        r2types::DecompileRouteKind::Standard => EnginePlan::FastLocal,
        r2types::DecompileRouteKind::StructuredWorker => EnginePlan::SemanticStructured,
        r2types::DecompileRouteKind::SummaryIslands
        | r2types::DecompileRouteKind::LinearWorker
        | r2types::DecompileRouteKind::VmSummary => EnginePlan::SemanticSummary,
        r2types::DecompileRouteKind::FallbackComment => EnginePlan::RefuseWithEvidence,
    }
}

struct EngineRenderedDecompile {
    product: EngineRenderedProduct,
    semantic_kernel_warnings: Vec<String>,
    structuring_executed: bool,
    /// Set when rendering stopped and the output above is what it had reached.
    ///
    /// A rendering and a stop, not one or the other: the body is kept so the
    /// reader gets what was produced, and the phase is still recorded as refused
    /// so the accounting says the run did not finish.
    stopped: Option<EngineRenderExecutionStop>,
}

struct ReadyEngineRenderedProduct {
    output: String,
    binding_audit: BindingShadowAuditOutcome,
    effect_obligations: EffectObligationAudit,
    placement_audit: PlacementAudit,
    render_refusal: Option<DecompileRenderRefusal>,
}

enum EngineRenderedProduct {
    Ready(Box<ReadyEngineRenderedProduct>),
    Pending(Box<r2dec::PendingDecompileBindingAudit>),
}

impl EngineRenderedProduct {
    fn finalize(
        self,
    ) -> (
        String,
        BindingShadowAuditOutcome,
        EffectObligationAudit,
        PlacementAudit,
        Option<DecompileRenderRefusal>,
    ) {
        match self {
            Self::Ready(ready) => {
                let ReadyEngineRenderedProduct {
                    output,
                    binding_audit,
                    effect_obligations,
                    placement_audit,
                    render_refusal,
                } = *ready;
                (
                    output,
                    binding_audit,
                    effect_obligations,
                    placement_audit,
                    render_refusal,
                )
            }
            Self::Pending(pending) => {
                let audited = (*pending).finalize();
                let binding_audit = audited.binding_shadow();
                let effect_obligations = audited.effect_obligations();
                let placement_audit = audited.placement_audit();
                let render_refusal = audited.render_refusal();
                (
                    audited.into_output(),
                    binding_audit,
                    effect_obligations,
                    placement_audit,
                    render_refusal,
                )
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EngineRenderExecutionStop {
    reason: String,
    phase: EnginePhase,
    binding_audit: Box<BindingShadowAuditOutcome>,
    effect_obligations: Box<EffectObligationAudit>,
    placement_audit: PlacementAudit,
    render_refusal: Option<Box<DecompileRenderRefusal>>,
    certification_completed: bool,
    normalization_completed: bool,
    structuring_completed: bool,
}

fn engine_metrics_for_render_stop(
    mut metrics: EngineMetrics,
    stop: &EngineRenderExecutionStop,
    planning_time: Duration,
    render_time: Duration,
) -> EngineMetrics {
    if stop.certification_completed {
        metrics.record_folded_if_not_executed(EnginePhase::Certification);
    }
    if stop.normalization_completed {
        metrics.record_folded_if_not_executed(EnginePhase::Normalization);
    }
    if stop.structuring_completed {
        metrics.record_folded_if_not_executed(EnginePhase::Structuring);
    }
    metrics.record_phase(stop.phase, EnginePhaseStatus::Refused, render_time);
    metrics.planning_time += planning_time;
    metrics.render_time = render_time;
    metrics
}

fn engine_render_stop_reason(
    reason: r2ssa::SsaExecutionStopReason,
    phase: EnginePhase,
) -> EngineRenderExecutionStop {
    let reason = match reason {
        r2ssa::SsaExecutionStopReason::Cancelled => {
            format!("engine request cancelled during {} phase", phase.as_str())
        }
        r2ssa::SsaExecutionStopReason::DeadlineExceeded => format!(
            "engine request deadline exceeded during {} phase",
            phase.as_str()
        ),
    };
    EngineRenderExecutionStop {
        reason,
        phase,
        binding_audit: Box::new(BindingShadowAuditOutcome::NotRun),
        effect_obligations: Box::new(EffectObligationAudit::NOT_RUN),
        placement_audit: PlacementAudit::NotRun,
        render_refusal: None,
        certification_completed: false,
        normalization_completed: false,
        structuring_completed: false,
    }
}

fn poll_engine_render_control<C: r2ssa::SsaWorkControl + ?Sized>(
    control: &C,
    phase: EnginePhase,
) -> Result<(), EngineRenderExecutionStop> {
    poll_engine_render_control_with_completion(control, phase, false, false)
}

fn poll_engine_render_control_with_completion<C: r2ssa::SsaWorkControl + ?Sized>(
    control: &C,
    phase: EnginePhase,
    certification_completed: bool,
    structuring_completed: bool,
) -> Result<(), EngineRenderExecutionStop> {
    control.poll().map_err(|reason| {
        let mut stop = engine_render_stop_reason(reason, phase);
        stop.certification_completed = certification_completed;
        stop.structuring_completed = structuring_completed;
        stop
    })
}

fn engine_render_stop_from_decompiler(
    stop: r2dec::DecompileExecutionStop,
    binding_audit: BindingShadowAuditOutcome,
    effect_obligations: EffectObligationAudit,
    placement_audit: PlacementAudit,
    render_refusal: Option<DecompileRenderRefusal>,
) -> EngineRenderExecutionStop {
    let phase = match stop.phase() {
        r2dec::DecompileWorkPhase::Normalization => EnginePhase::Normalization,
        r2dec::DecompileWorkPhase::Structuring => EnginePhase::Structuring,
        r2dec::DecompileWorkPhase::Rendering => EnginePhase::Rendering,
    };
    let mut mapped = engine_render_stop_reason(stop.reason(), phase);
    mapped.binding_audit = Box::new(binding_audit);
    mapped.effect_obligations = Box::new(effect_obligations);
    mapped.placement_audit = placement_audit;
    mapped.render_refusal = render_refusal.map(Box::new);
    match stop.phase() {
        r2dec::DecompileWorkPhase::Normalization => {}
        r2dec::DecompileWorkPhase::Structuring => {
            mapped.normalization_completed = true;
        }
        r2dec::DecompileWorkPhase::Rendering => {
            mapped.normalization_completed = true;
            mapped.structuring_completed = true;
        }
    }
    mapped
}

fn render_engine_decompile_request<C: r2ssa::SsaWorkControl>(
    request: &EngineDecompileRequest,
    control: &C,
) -> Result<EngineRenderedDecompile, EngineRenderExecutionStop> {
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    if let Some(output) = render_semantic_route(
        &request.function_name,
        request.function_facts(),
        &request.render_target,
    ) {
        poll_engine_render_control(control, EnginePhase::Rendering)?;
        return Ok(EngineRenderedDecompile {
            product: EngineRenderedProduct::Ready(Box::new(ReadyEngineRenderedProduct {
                output,
                binding_audit: BindingShadowAuditOutcome::NotRun,
                effect_obligations: EffectObligationAudit::NOT_RUN,
                placement_audit: PlacementAudit::NotRun,
                render_refusal: None,
            })),
            semantic_kernel_warnings: Vec::new(),
            structuring_executed: false,
            stopped: None,
        });
    }

    let input = decompiler_input_for_engine_request(request);
    // Keep a rendering the decompiler reached before it stopped. Discarding it
    // reports a function that ran out of budget as one that produced nothing,
    // and takes the ledger that would have said so with it.
    let audited = match r2dec::Decompiler::new(request.render_target.to_decompiler_config())
        .decompile_input_keeping_partial_with_pending_binding_audit(&input, control)
    {
        Ok(pending) => pending,
        Err((stop, Some(partial))) if !partial.output().trim().is_empty() => {
            let audited = partial.finalize();
            let binding_audit = audited.binding_shadow();
            let effect_obligations = audited.effect_obligations();
            let placement_audit = audited.placement_audit();
            let render_refusal = audited.render_refusal();
            let output = audited.into_output();
            return Ok(EngineRenderedDecompile {
                product: EngineRenderedProduct::Ready(Box::new(ReadyEngineRenderedProduct {
                    output,
                    binding_audit,
                    effect_obligations,
                    placement_audit,
                    render_refusal,
                })),
                semantic_kernel_warnings: vec![format!(
                    "rendering stopped in {:?}: {}; the body above is what was reached",
                    stop.phase(),
                    stop.reason()
                )],
                structuring_executed: true,
                stopped: Some(engine_render_stop_from_decompiler(
                    stop,
                    binding_audit,
                    effect_obligations,
                    placement_audit,
                    render_refusal,
                )),
            });
        }
        Err((stop, partial)) => {
            let (binding_audit, effect_obligations, placement_audit, render_refusal) = partial
                .map(r2dec::PendingDecompileBindingAudit::finalize)
                .map_or(
                    (
                        BindingShadowAuditOutcome::NotRun,
                        EffectObligationAudit::NOT_RUN,
                        PlacementAudit::NotRun,
                        None,
                    ),
                    |audit| {
                        (
                            audit.binding_shadow(),
                            audit.effect_obligations(),
                            audit.placement_audit(),
                            audit.render_refusal(),
                        )
                    },
                );
            return Err(engine_render_stop_from_decompiler(
                stop,
                binding_audit,
                effect_obligations,
                placement_audit,
                render_refusal,
            ));
        }
    };
    if !audited.output().trim().is_empty() {
        return Ok(EngineRenderedDecompile {
            product: EngineRenderedProduct::Pending(Box::new(audited)),
            semantic_kernel_warnings: Vec::new(),
            structuring_executed: true,
            stopped: None,
        });
    }

    let audited = audited.finalize();
    let binding_audit = audited.binding_shadow();
    let effect_obligations = audited.effect_obligations();
    let placement_audit = audited.placement_audit();
    let render_refusal = audited.render_refusal();
    Ok(EngineRenderedDecompile {
        product: EngineRenderedProduct::Ready(Box::new(ReadyEngineRenderedProduct {
            output: decompile_route_output_from_function_facts(
                &request.function_name,
                request.function_facts(),
            )
            .unwrap_or_default(),
            binding_audit,
            effect_obligations,
            placement_audit,
            render_refusal,
        })),
        semantic_kernel_warnings: Vec::new(),
        structuring_executed: false,
        stopped: None,
    })
}

fn decompiler_input_for_engine_request(request: &EngineDecompileRequest) -> r2dec::DecompilerInput {
    r2dec::DecompilerInput::new(request.source_owned_facts.clone())
}

/// The measured cost of one decompile, per phase, appended to the rendered
/// output when `R2SLEIGH_TIMING` is set.
///
/// The engine has recorded a complete phase inventory since it was written and
/// no reachable command printed it, so a decompile could be timed only from
/// outside the process, which measures radare2's analysis and the plugin load
/// along with it. A refusal is timed too: refusing has to be cheaper than
/// rendering, and a four-second refusal is exactly the case that measurement
/// from outside could not distinguish from a slow render.
///
/// A phase the boundary did not execute is omitted; `folded` says the phase ran
/// inside another phase's span, which is not the same as free.
fn phase_timing_comment(metrics: &EngineMetrics) -> Option<String> {
    std::env::var_os("R2SLEIGH_TIMING")?;
    Some(format_phase_timing(metrics))
}

/// The comment's text, separate from the decision to emit it, so the format is
/// testable without a process-global environment variable.
fn format_phase_timing(metrics: &EngineMetrics) -> String {
    let mut measured = String::new();
    let mut total_us = 0u64;
    // `EnginePhase::ALL` order, so two runs of one function print one line.
    for timing in &metrics.phase_timings {
        match timing.status {
            EnginePhaseStatus::NotExecuted => continue,
            EnginePhaseStatus::Executed => {
                total_us = total_us.saturating_add(timing.elapsed_us);
                measured.push_str(&format!(
                    " {}={}us",
                    timing.phase.as_str(),
                    timing.elapsed_us
                ));
            }
            EnginePhaseStatus::Folded => {
                measured.push_str(&format!(" {}=folded", timing.phase.as_str()));
            }
            EnginePhaseStatus::Refused => {
                measured.push_str(&format!(" {}=refused", timing.phase.as_str()));
            }
        }
    }
    format!("/* r2dec timing: measured={total_us}us{measured} */")
}

/// Append the timing comment to a rendered body, or leave it exactly as it was.
fn with_phase_timing_comment(output: String, metrics: &EngineMetrics) -> String {
    match phase_timing_comment(metrics) {
        Some(comment) => {
            let mut output = output;
            if !output.ends_with('\n') {
                output.push('\n');
            }
            output.push_str(&comment);
            output.push('\n');
            output
        }
        None => output,
    }
}

fn refused_decompile_response(
    function_name: &str,
    reason: &str,
    planning_time: Duration,
    input_quality: Option<r2types::FunctionInputQualityFacts>,
) -> EngineDecompileResponse {
    let mut metrics = EngineMetrics {
        planning_time,
        ..EngineMetrics::default()
    };
    metrics.refuse_from(EnginePhase::SnapshotContext);
    refused_decompile_response_with_metrics(
        function_name,
        reason,
        input_quality,
        metrics,
        EngineDiagnostics::default(),
    )
}

fn refused_decompile_response_with_metrics(
    function_name: &str,
    reason: &str,
    input_quality: Option<r2types::FunctionInputQualityFacts>,
    metrics: EngineMetrics,
    diagnostics: EngineDiagnostics,
) -> EngineDecompileResponse {
    refused_decompile_response_with_metrics_and_audits(
        function_name,
        reason,
        input_quality,
        metrics,
        diagnostics,
        None,
        BindingShadowAuditOutcome::NotRun,
        EffectObligationAudit::NOT_RUN,
        PlacementAudit::NotRun,
        None,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "the sole refusal constructor receives each independent typed ledger explicitly so none can be silently defaulted or reconstructed"
)]
fn refused_decompile_response_with_metrics_and_audits(
    function_name: &str,
    reason: &str,
    input_quality: Option<r2types::FunctionInputQualityFacts>,
    metrics: EngineMetrics,
    mut diagnostics: EngineDiagnostics,
    existing_function_facts: Option<FunctionFacts>,
    binding_audit: BindingShadowAuditOutcome,
    effect_obligations: EffectObligationAudit,
    placement_audit: PlacementAudit,
    render_refusal: Option<DecompileRenderRefusal>,
) -> EngineDecompileResponse {
    let function_facts = seal_refused_decompile_function_facts(
        existing_function_facts.unwrap_or_default(),
        function_name,
        reason,
    );
    let output = decompile_route_output_from_function_facts(function_name, &function_facts)
        .expect("refused decompile response must stamp a fallback route");
    let route_diagnostics = decompile_diagnostics_from_function_facts(&function_facts);
    diagnostics.plan = route_diagnostics.plan;
    diagnostics.route_reason = route_diagnostics.route_reason;
    diagnostics.refusal = route_diagnostics.refusal;
    let output = with_phase_timing_comment(output, &metrics);
    EngineDecompileResponse {
        output,
        binding_audit,
        effect_obligations,
        placement_audit,
        render_refusal,
        function_facts,
        input_quality,
        metrics,
        diagnostics,
    }
}

fn seal_refused_decompile_function_facts(
    function_facts: FunctionFacts,
    function_name: &str,
    reason: &str,
) -> FunctionFacts {
    let output = artifact_guard_fallback_comment(function_name, reason);
    let route = r2types::DecompileRouteFacts {
        kind: r2types::DecompileRouteKind::FallbackComment,
        reason: Some(reason.to_string()),
        fallback_comment: Some(output),
        use_prepared_semantic_view: false,
    };
    function_facts.with_decompile_route(route)
}

fn decompile_route_output_from_function_facts(
    _function_name: &str,
    function_facts: &FunctionFacts,
) -> Option<String> {
    let route = function_facts.decompile_route()?;
    match route.kind {
        r2types::DecompileRouteKind::FallbackComment => route
            .fallback_comment
            .as_ref()
            .or(route.reason.as_ref())
            .cloned(),
        r2types::DecompileRouteKind::LinearWorker
        | r2types::DecompileRouteKind::SummaryIslands
        | r2types::DecompileRouteKind::StructuredWorker
        | r2types::DecompileRouteKind::VmSummary => function_facts
            .decompile_fallback_comment()
            .map(str::to_string),
        r2types::DecompileRouteKind::Standard => None,
    }
}

#[cfg(test)]
fn build_engine_analysis_from_parts(
    function_name: &str,
    blocks: &[R2ILBlock],
    arch: Option<&r2il::ArchSpec>,
    source_snapshot: &EngineSourceSnapshot,
) -> Option<EngineAnalysis> {
    build_engine_analysis_from_parts_with_control(
        function_name,
        blocks,
        arch,
        source_snapshot,
        &r2ssa::SsaExecutionControl::default(),
    )
    .ok()
}

fn build_engine_analysis_from_parts_with_control<C: r2ssa::SsaWorkControl + ?Sized>(
    function_name: &str,
    blocks: &[R2ILBlock],
    arch: Option<&r2il::ArchSpec>,
    source_snapshot: &EngineSourceSnapshot,
    control: &C,
) -> Result<EngineAnalysis, r2ssa::SsaPrepareError> {
    let ssa_func = Arc::new(
        r2ssa::SsaArtifact::for_decompile_with_interfaces_machine_roles_and_control(
            blocks,
            arch,
            source_snapshot.function_interface().cloned(),
            *source_snapshot.machine_roles(),
            source_snapshot.call_site_interfaces().to_vec(),
            control,
        )?
        .with_name(function_name),
    );
    control.poll()?;
    Ok(EngineAnalysis::from_prepared_ssa(ssa_func))
}

struct InterprocSummaryBuildInput<'a> {
    pub analysis: &'a EngineAnalysis,
    pub max_iterations: usize,
    pub symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
    /// Bodies of the functions the root calls, captured with it. Without these
    /// every direct call is an unresolved callee, and the solver has to mark
    /// every pointer argument read, written and escaped.
    pub trusted_callees: &'a [Arc<r2ssa::SsaArtifact>],
}

fn build_prepared_interproc_summary_set(
    input: InterprocSummaryBuildInput<'_>,
) -> Result<r2ssa::PreparedInterprocSummarySet, r2ssa::PreparedInterprocSummaryError> {
    let root = r2ssa::InterprocFunctionId(input.analysis.ssa_func.function().entry);
    let symbolic_scope = input.symbolic_scope.filter(|scope| {
        scope.root_id() == root
            && scope.root().is_some_and(|scope_root| {
                scope_root.id == root
                    && scope_root.prepared.function().entry == root.0
                    && scope_root.prepared.authority() == input.analysis.ssa_func().authority()
            })
    });
    let mut functions = vec![r2ssa::PreparedInterprocFunctionInput {
        id: root,
        name: input.analysis.ssa_func.function().name.clone(),
        prepared: &input.analysis.ssa_func,
    }];
    if let Some(scope) = symbolic_scope {
        for function in scope.functions().values() {
            if function.id == root {
                continue;
            }
            functions.push(r2ssa::PreparedInterprocFunctionInput {
                id: function.id,
                name: function.name.clone(),
                prepared: &function.prepared,
            });
        }
    }
    for callee in input.trusted_callees {
        let id = r2ssa::InterprocFunctionId(callee.function().entry);
        if id == root || functions.iter().any(|function| function.id == id) {
            continue;
        }
        functions.push(r2ssa::PreparedInterprocFunctionInput {
            id,
            name: callee.function().name.clone(),
            prepared: callee,
        });
    }
    r2ssa::solve_prepared_interproc_summary_set(
        Arc::clone(&input.analysis.ssa_func),
        &functions,
        r2ssa::InterprocSolveConfig {
            max_iterations: input.max_iterations.max(1),
        },
    )
}

/// Build the analysis artifact, naming the cause when one cannot be built.
///
/// The reason is surfaced to the user, so every exit below says which stage
/// declined and why rather than collapsing to a single opaque failure.
fn build_engine_analysis_artifact(
    request: &EngineAnalyzeRequest,
    analysis: &EngineAnalysis,
) -> Result<EngineAnalysisArtifact, String> {
    let trusted_ssa = request
        .parsed_context
        .assumptions
        .is_empty()
        .then(|| request.trusted_ssa.clone())
        .flatten();
    let ssa_func = if request.parsed_context.assumptions.is_empty() {
        Arc::clone(&analysis.ssa_func)
    } else {
        Arc::new(
            analysis
                .ssa_func
                .with_assumptions(&request.parsed_context.assumptions),
        )
    };
    let semantic_analysis = EngineAnalysis::from_prepared_ssa(ssa_func);
    let interproc_summary_set = if request.include_interproc_summary_set {
        match build_prepared_interproc_summary_set(InterprocSummaryBuildInput {
            analysis: &semantic_analysis,
            max_iterations: request.interproc_max_iterations,
            symbolic_scope: request.symbolic_scope.as_ref(),
            trusted_callees: &request.trusted_callees,
        }) {
            Ok(summary) => Some(summary),
            Err(
                r2ssa::PreparedInterprocSummaryError::ArchitectureMismatch
                | r2ssa::PreparedInterprocSummaryError::UnknownOrIncoherentMachineContext,
            ) => None,
            Err(error) => {
                return Err(format!(
                    "interprocedural summary construction failed: {error:?}"
                ));
            }
        }
    } else {
        None
    };
    let pattern_ssa_blocks = semantic_analysis.ssa_func.local_ssa_blocks();
    let optional_semantics_required = optional_semantics_required_for_analysis(
        &request.parsed_context,
        &semantic_analysis.ssa_func,
        &pattern_ssa_blocks,
    );
    let semantic_artifact = (|| {
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
                request.symbolic_scope.as_ref(),
                interproc_summary_set.as_ref(),
            );
        }
        optional_semantics_required.then(|| {
            r2sym::compile_semantic_artifact_default_with_scope(
                &z3::Context::thread_local(),
                &semantic_analysis.ssa_func,
                request.symbolic_scope.as_ref(),
            )
        })
    })();
    if let Some(reason) = request.execution.refusal_reason(EnginePhase::Types) {
        return Err(format!("type analysis stopped: {reason}"));
    }
    let mut writeback_request = r2types::TypeWritebackAnalysisRequest::new(
        Arc::clone(&semantic_analysis.ssa_func),
        request.parsed_context.clone(),
    )
    .map_err(|error| format!("type writeback request rejected the source: {error:?}"))?;
    if let Some(semantic_artifact) = semantic_artifact {
        writeback_request = writeback_request
            .with_semantic_artifact(semantic_artifact)
            .map_err(|error| {
                format!("type writeback request rejected the semantic artifact: {error:?}")
            })?;
    }
    if let Some(interproc_summary_set) = interproc_summary_set {
        writeback_request = writeback_request
            .with_interproc_summary(interproc_summary_set)
            .map_err(|error| {
                format!("type writeback request rejected the interprocedural summary: {error:?}")
            })?;
    }
    let writeback = r2types::build_source_owned_type_writeback_analysis(writeback_request)
        .map_err(|error| format!("type writeback analysis failed: {error:?}"))?;
    if let Some(reason) = request.execution.refusal_reason(EnginePhase::Certification) {
        return Err(format!("certification stopped: {reason}"));
    }
    EngineAnalysisArtifact::new(
        writeback,
        // Trusted capture authority is deliberately request-local and may
        // only accompany its exact retained SSA allocation.
        trusted_ssa,
    )
    .ok_or_else(|| {
        "trusted SSA authority does not accompany its own type analysis source".to_string()
    })
}

fn maybe_compile_semantic_artifact_for_analysis(
    ssa_func: &Arc<SsaArtifact>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    interproc_summaries: Option<&r2ssa::PreparedInterprocSummarySet>,
) -> Option<r2sym::SemanticArtifact> {
    let root_summary = interproc_summaries.and_then(prepared_root_summary);
    if should_probe_native_worker_summary_before_full_semantics(ssa_func, root_summary) {
        let vm_route_evidence = r2sym::has_strong_vm_evidence(ssa_func);
        if !vm_route_evidence
            && should_skip_unbounded_semantic_artifact_after_worker_preprobe(ssa_func, root_summary)
        {
            return None;
        }
        if !vm_route_evidence
            && let Some(artifact) = r2sym::compile_native_worker_summary_artifact(
                ssa_func,
                symbolic_scope,
                interproc_summaries,
                false,
            )
            && artifact
                .native_body()
                .is_some_and(r2sym::NativeArtifactBody::has_primary_summary_islands)
        {
            let cfg = ssa_func.function().cfg_risk_summary();
            if cfg.block_count <= 12 || cfg.loop_count == 0 || cfg.block_count > 64 {
                return Some(artifact);
            }
            // Small looped function: skip preprobe, use full semantics
        }
    }
    Some(compile_semantic_artifact_for_analysis(
        ssa_func,
        symbolic_scope,
        interproc_summaries,
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
    ssa_func: &Arc<SsaArtifact>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
    interproc_summaries: Option<&r2ssa::PreparedInterprocSummarySet>,
) -> r2sym::SemanticArtifact {
    let root_summary = interproc_summaries.and_then(prepared_root_summary);
    let vm_route_evidence = r2sym::has_strong_vm_evidence(ssa_func);
    if !vm_route_evidence
        && let Some(summaries) = interproc_summaries
        && let Some(artifact) = r2sym::compile_summary_dense_worker_artifact_from_interproc_summary(
            ssa_func,
            symbolic_scope,
            summaries,
        )
    {
        return artifact;
    }
    if !vm_route_evidence
        && should_probe_native_worker_summary_before_full_semantics(ssa_func, root_summary)
        && let Some(artifact) = r2sym::compile_native_worker_summary_artifact(
            ssa_func,
            symbolic_scope,
            interproc_summaries,
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
    );
    if let Some(summaries) = interproc_summaries {
        r2sym::augment_semantic_artifact_with_interproc_summary(&mut artifact, summaries);
    }
    artifact
}

fn prepared_root_summary(
    summaries: &r2ssa::PreparedInterprocSummarySet,
) -> Option<&r2ssa::FunctionSemanticSummary> {
    let report = summaries.report();
    report.root.and_then(|root| report.summaries.get(&root))
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

pub fn infer_signature_from_analysis(
    request: EngineSignatureInferenceRequest<'_>,
) -> r2types::InferredSignature {
    r2types::infer_signature_from_prepared_ssa(request.analysis.ssa_func())
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

pub fn block_guard_fallback_comment(
    function_name: &str,
    blocks: usize,
    max_blocks: usize,
) -> String {
    let function_name = sanitize_fallback_comment_text(function_name);
    format!(
        "/* r2dec budget: skipped decompilation for {} ({} blocks > limit {}). */",
        function_name, blocks, max_blocks
    )
}

pub fn cfg_guard_fallback_comment(
    function_name: &str,
    cfg_summary: &CFGRiskSummary,
) -> Option<String> {
    cfg_guard_reason_from_summary(cfg_summary)
        .map(|reason| artifact_guard_fallback_comment(function_name, &reason))
}

pub fn artifact_guard_fallback_comment(function_name: &str, reason: &str) -> String {
    let function_name = sanitize_fallback_comment_text(function_name);
    let reason = sanitize_fallback_comment_text(reason);
    format!(
        "/* r2dec fallback: skipped decompilation for {} ({}) */",
        function_name, reason
    )
}

fn sanitize_fallback_comment_text(text: &str) -> String {
    text.replace("*/", "* /").replace(['\r', '\n'], " ")
}

pub fn semantic_fallback_comment_for_facts(
    function_name: &str,
    function_facts: &FunctionFacts,
) -> Option<String> {
    let semantic_artifact = function_facts.semantic_artifact()?;
    if let Some(comment) = vm_semantic_fallback_comment(function_name, semantic_artifact) {
        return Some(comment);
    }
    let slice_class = semantic_artifact.slice_class()?;
    let mut reason = format!(
        "semantic fallback: {} slice in {} mode",
        semantic_slice_class_label(slice_class),
        semantic_mode_label(semantic_artifact)
    );
    if !semantic_artifact.diagnostics.residual_reasons.is_empty() {
        reason.push_str(" (");
        reason.push_str(
            &semantic_artifact
                .diagnostics
                .residual_reasons
                .iter()
                .map(|reason| semantic_residual_reason_label(*reason))
                .collect::<Vec<_>>()
                .join(", "),
        );
        reason.push(')');
    }
    if !semantic_artifact.ambiguous_targets().is_empty() {
        reason.push_str("; ambiguous_targets=[");
        reason.push_str(
            &semantic_artifact
                .ambiguous_targets()
                .into_iter()
                .map(|target| format!("0x{target:x}"))
                .collect::<Vec<_>>()
                .join(", "),
        );
        reason.push(']');
    }
    if let Some(native) = semantic_artifact.native_body()
        && !native.regions.is_empty()
    {
        reason.push_str(&format!(
            "; regions={}, actionable_conditions={}, exact_conditions={}",
            native.regions.len(),
            native.actionable_control_count(),
            native.exact_control_count(),
        ));
    }
    let actionable_preview = semantic_artifact
        .actionable_regions()
        .into_iter()
        .filter_map(|region| {
            region
                .actionable_compiled_condition()
                .map(|condition| format!("0x{:x}: {}", region.anchor, condition.simplified))
        })
        .take(3)
        .collect::<Vec<_>>();
    if !actionable_preview.is_empty() {
        reason.push_str("; actionable_preview=[");
        reason.push_str(&actionable_preview.join(" | "));
        reason.push(']');
    }
    if function_facts.has_assumption_conflicts() {
        reason.push_str(&format!(
            "; assumption_conflicts={}",
            function_facts.assumption_usage().conflicts.len()
        ));
    }
    if let Some(rollup) = function_facts.summary_rollup() {
        if let Some(return_relation) = rollup.root_return_relation.as_ref() {
            reason.push_str(&format!("; summary_return={return_relation:?}"));
        }
        let certified_out_params = certified_out_param_labels(function_facts.type_facts());
        if !certified_out_params.is_empty() {
            reason.push_str("; out_params=[");
            reason.push_str(&certified_out_params.join(", "));
            reason.push(']');
        }
    }
    Some(artifact_guard_fallback_comment(function_name, &reason))
}

fn vm_semantic_fallback_comment(
    function_name: &str,
    semantic_artifact: &r2sym::SemanticArtifact,
) -> Option<String> {
    let vm_body = semantic_artifact.vm_body()?;
    let vm_step = vm_body
        .step_summary
        .as_ref()
        .or(vm_body.transfer_summary.as_ref())?;
    Some(format!(
        "/* {} */",
        vm_summary_stats_comment(function_name, vm_step)
    ))
}

fn vm_summary_stats_comment(function_name: &str, vm_step: &r2sym::VmStepSummary) -> String {
    let kind = interpreter_kind_label(vm_step.kind);
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
        function_name,
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

fn interpreter_kind_label(kind: r2sym::InterpreterKind) -> &'static str {
    match kind {
        r2sym::InterpreterKind::SwitchDispatch => "switch_dispatch",
        r2sym::InterpreterKind::IndirectDispatch => "indirect_dispatch",
    }
}

fn semantic_mode_label(artifact: &r2sym::SemanticArtifact) -> &'static str {
    match (artifact.execution, artifact.stage, artifact.granularity) {
        (r2sym::ExecutionModel::Vm, _, _) => "vm_summary",
        (_, r2sym::RefinementStage::Raw, _) => "raw",
        (_, r2sym::RefinementStage::Compiled, r2sym::ArtifactGranularity::Regioned) => {
            "island_compiled"
        }
        (_, r2sym::RefinementStage::Compiled, _) => "compiled",
        (_, r2sym::RefinementStage::Residual, _) => "residual",
    }
}

fn semantic_report_mode_label(artifact: &r2sym::SemanticArtifactReport) -> &'static str {
    match (artifact.execution, artifact.stage, artifact.granularity) {
        (r2sym::ExecutionModel::Vm, _, _) => "vm_summary",
        (_, r2sym::RefinementStage::Raw, _) => "raw",
        (_, r2sym::RefinementStage::Compiled, r2sym::ArtifactGranularity::Regioned) => {
            "island_compiled"
        }
        (_, r2sym::RefinementStage::Compiled, _) => "compiled",
        (_, r2sym::RefinementStage::Residual, _) => "residual",
    }
}

fn semantic_slice_class_label(slice_class: r2sym::SliceClass) -> &'static str {
    match slice_class {
        r2sym::SliceClass::Wrapper => "wrapper",
        r2sym::SliceClass::Worker => "worker",
        r2sym::SliceClass::RecursiveGroup => "recursive_group",
        r2sym::SliceClass::InterpreterSwitch => "interpreter_switch",
        r2sym::SliceClass::InterpreterIndirect => "interpreter_indirect",
        r2sym::SliceClass::GenericLarge => "generic_large",
    }
}

fn semantic_residual_reason_label(reason: r2sym::ResidualReason) -> &'static str {
    match reason {
        r2sym::ResidualReason::MissingArch => "missing_arch",
        r2sym::ResidualReason::LargeCfg => "large_cfg",
        r2sym::ResidualReason::SummaryBudgetExhausted => "summary_budget_exhausted",
        r2sym::ResidualReason::SccBudgetExhausted => "scc_budget_exhausted",
        r2sym::ResidualReason::InterpreterRequiresStepSummary => {
            "interpreter_requires_step_summary"
        }
    }
}

fn certified_out_param_labels(type_facts: &FunctionTypeFacts) -> Vec<String> {
    type_facts
        .source_authorized_out_param_certificates()
        .map(|cert| {
            if cert.param_name.trim().is_empty() {
                cert.param_index.to_string()
            } else {
                format!("{}:{}", cert.param_index, cert.param_name)
            }
        })
        .collect()
}

pub fn render_semantic_route(
    function_name: &str,
    function_facts: &FunctionFacts,
    _config: &EngineRenderTarget,
) -> Option<String> {
    decompile_route_output_from_function_facts(function_name, function_facts)
}

pub struct TargetQueryRouteInput<'a> {
    pub z3_ctx: &'a z3::Context,
    pub compiled: &'a r2sym::SemanticArtifact,
    pub scope: Option<&'a r2sym::PreparedFunctionScope>,
    pub target_addr: u64,
    pub arch: Option<&'a r2il::ArchSpec>,
    pub symbols: &'a r2sym::FunctionSymbolSnapshot,
    pub explore_config: r2sym::ExploreConfig,
    pub summary_profile: r2sym::SummaryProfile,
    pub assumption_conflicted: bool,
}

pub fn target_query_route_decision(
    input: TargetQueryRouteInput<'_>,
) -> r2sym::TargetQueryRoutePlan {
    let TargetQueryRouteInput {
        z3_ctx,
        compiled,
        scope,
        target_addr,
        arch,
        symbols,
        explore_config,
        summary_profile,
        assumption_conflicted,
    } = input;
    let scope = scope.and_then(|scope| scope.exact_for_artifact(compiled.prepared()));
    let probe_config = r2sym::SymQueryConfig {
        explore: explore_config,
        mode: r2sym::QueryMode::TargetGuided,
        summary_profile,
        solve_tactics: r2sym::SolveTacticConfig::default(),
    };
    let mut explorer = probe_config.make_explorer(z3_ctx);
    if let Some(scope) = scope {
        r2sym::install_runtime_hooks_for_scope(
            &mut explorer,
            compiled.prepared(),
            scope,
            arch,
            symbols.imported_names(),
        );
    }
    r2sym::selected_target_query_route_in_scope(
        &mut explorer,
        compiled.prepared(),
        scope,
        Some(compiled),
        target_addr,
        assumption_conflicted,
    )
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
    use std::cell::Cell;
    use std::collections::{BTreeMap, HashMap};

    fn test_decompile_route(
        kind: r2types::DecompileRouteKind,
        reason: Option<&str>,
        fallback_comment: Option<&str>,
    ) -> r2types::DecompileRouteFacts {
        r2types::DecompileRouteFacts {
            kind,
            reason: reason.map(str::to_string),
            fallback_comment: fallback_comment.map(str::to_string),
            use_prepared_semantic_view: kind == r2types::DecompileRouteKind::Standard,
        }
    }

    fn const_return_blocks(addr: u64, value: u64) -> Vec<R2ILBlock> {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(value, 8),
        });
        vec![block]
    }

    fn test_source_snapshot(revision: &str) -> Arc<EngineSourceSnapshot> {
        Arc::new(
            EngineSourceSnapshot::new(revision.as_bytes().to_vec(), None, Vec::new())
                .expect("test source snapshot"),
        )
    }

    fn exact_empty_test_source_snapshot(revision: &str) -> Arc<EngineSourceSnapshot> {
        let revision_identity = revision.as_bytes().to_vec();
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            revision_identity.clone(),
            "sysv64",
            std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
            r2ssa::SourceFunctionReturn::Void,
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| {
            interface.with_stack_pointer_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x28,
                size: 8,
            })
        })
        .and_then(|interface| {
            interface.with_return_address_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x30,
                size: 8,
            })
        })
        .expect("exact empty test interface");
        Arc::new(
            EngineSourceSnapshot::new(revision_identity, Some(interface), Vec::new())
                .expect("exact empty test source snapshot"),
        )
    }

    fn exact_rdi_test_source_snapshot(revision: &str) -> Arc<EngineSourceSnapshot> {
        let revision_identity = revision.as_bytes().to_vec();
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            revision_identity.clone(),
            "sysv64",
            [r2ssa::SourceAbiParameterSpec::new(
                0,
                r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 0x10,
                    size: 8,
                },
            )],
            r2ssa::SourceFunctionReturn::Void,
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| {
            interface.with_stack_pointer_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x28,
                size: 8,
            })
        })
        .and_then(|interface| {
            interface.with_return_address_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x30,
                size: 8,
            })
        })
        .expect("exact RDI test interface");
        Arc::new(
            EngineSourceSnapshot::new(revision_identity, Some(interface), Vec::new())
                .expect("exact RDI test source snapshot"),
        )
    }

    fn direct_call_return_blocks(addr: u64, target: u64) -> Vec<R2ILBlock> {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(target, 8),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(0, 8),
        });
        vec![block]
    }

    fn source_snapshot_call_interface(
        revision_identity: &[u8],
        block_addr: u64,
        op_index: usize,
        target: u64,
    ) -> r2ssa::SourceCallSiteInterface {
        r2ssa::SourceCallSiteInterface::new(
            revision_identity.to_vec(),
            r2ssa::SourceCallSiteIdentity::new(
                block_addr,
                op_index,
                r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Constant,
                    offset: target,
                    size: 8,
                },
            ),
            true,
            "sysv",
            Vec::<r2ssa::SourceCallArgumentSpec>::new(),
            false,
            false,
            r2ssa::SourceCallResult::Void,
        )
        .expect("source callsite interface")
    }

    fn source_snapshot_function_interface(
        revision_identity: &[u8],
    ) -> r2ssa::SourceFunctionInterface {
        r2ssa::SourceFunctionInterface::new(
            revision_identity.to_vec(),
            "sysv",
            Vec::<r2ssa::SourceAbiParameterSpec>::new(),
            r2ssa::SourceFunctionReturn::Register {
                storage: r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 8,
                },
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("source function interface")
    }

    #[test]
    fn engine_source_snapshot_preserves_exact_ordered_interfaces() {
        let revision = b"source-revision-1";
        let function_interface = source_snapshot_function_interface(revision);
        let first = source_snapshot_call_interface(revision, 0x401000, 1, 0x5000);
        let second = source_snapshot_call_interface(revision, 0x401000, 3, 0x6000);

        let snapshot = EngineSourceSnapshot::new(
            revision.to_vec(),
            Some(function_interface.clone()),
            vec![second.clone(), first.clone()],
        )
        .expect("coherent source snapshot");

        assert_eq!(snapshot.revision_identity(), revision);
        assert_eq!(snapshot.function_interface(), Some(&function_interface));
        assert_eq!(snapshot.call_site_interfaces(), &[second, first]);
    }

    #[test]
    fn engine_source_snapshot_rejects_empty_mismatched_and_duplicate_authority() {
        assert_eq!(
            EngineSourceSnapshot::new(Vec::new(), None, Vec::new()),
            Err(EngineSourceSnapshotError::EmptyRevisionIdentity)
        );
        assert_eq!(
            EngineSourceSnapshot::new(
                b"source-revision-1".to_vec(),
                Some(source_snapshot_function_interface(b"source-revision-2")),
                Vec::new(),
            ),
            Err(EngineSourceSnapshotError::FunctionRevisionMismatch)
        );

        let first = source_snapshot_call_interface(b"source-revision-1", 0x401000, 1, 0x5000);
        assert_eq!(
            EngineSourceSnapshot::new(b"source-revision-2".to_vec(), None, vec![first.clone()],),
            Err(EngineSourceSnapshotError::CallSiteRevisionMismatch)
        );
        assert_eq!(
            EngineSourceSnapshot::new(
                b"source-revision-1".to_vec(),
                None,
                vec![first.clone(), first],
            ),
            Err(EngineSourceSnapshotError::DuplicateCallSiteIdentity)
        );

        let same_location_other_target =
            source_snapshot_call_interface(b"source-revision-1", 0x401000, 1, 0x6000);
        let first = source_snapshot_call_interface(b"source-revision-1", 0x401000, 1, 0x5000);
        assert_eq!(
            EngineSourceSnapshot::new(
                b"source-revision-1".to_vec(),
                None,
                vec![first, same_location_other_target],
            ),
            Err(EngineSourceSnapshotError::DuplicateCallSiteLocation)
        );
    }

    #[test]
    fn authoritative_source_interface_reaches_prepared_ssa_through_request() {
        let revision = b"source-revision-1";
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let function_interface = r2ssa::SourceFunctionInterface::new_exact(
            revision.to_vec(),
            "sysv",
            Vec::<r2ssa::SourceAbiParameterSpec>::new(),
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0),
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("exact source interface")
        .with_return_address_storage(register(0x30))
        .and_then(|interface| interface.with_stack_pointer_storage(register(0x28)))
        .expect("exact source machine carriers");
        let snapshot = Arc::new(
            EngineSourceSnapshot::new(
                revision.to_vec(),
                Some(function_interface),
                vec![source_snapshot_call_interface(
                    revision, 0x401000, 0, 0x5000,
                )],
            )
            .expect("source snapshot"),
        );
        let mut blocks = direct_call_return_blocks(0x401000, 0x5000);
        blocks[0].ops[1] = r2il::R2ILOp::Return {
            target: r2il::Varnode::register(0x30, 8),
        };
        let arch = x86_64_result_arch();
        let request =
            EngineAnalyzeRequest::full_semantics_for_function(EngineAnalyzeFunctionRequestInput {
                function: EngineFunctionInput {
                    function_name: "sym.snapshot".to_string(),
                    function_addr: 0x401000,
                    blocks,
                    arch: Some(arch),
                    source_snapshot: Some(snapshot.clone()),
                    semantic_metadata_enabled: false,
                },
                ptr_bits: Some(64),
                reg_type_hints: HashMap::new(),
                parsed_context: r2types::ParsedExternalContext::default(),
                interproc_max_iterations: 1,
                symbolic_scope: None,
                include_interproc_summary_set: false,
            });
        assert!(Arc::ptr_eq(
            request.source_snapshot.as_ref().expect("request snapshot"),
            &snapshot
        ));

        let response = EngineSession::new()
            .analyze(request)
            .expect("snapshot-backed analysis");
        let context = response.artifact.ssa_func().machine_context();
        assert_eq!(
            context
                .function_interface()
                .expect("authoritative function interface")
                .revision_identity(),
            revision
        );
        assert!(
            context.abi_model().is_coherent(),
            "authoritative source context must remain coherent: {context:#?}"
        );
        assert_eq!(context.call_site_interfaces().len(), 1);
        assert!(
            response
                .artifact
                .ssa_func()
                .facts()
                .boundaries
                .calls
                .values()
                .next()
                .expect("authoritative call boundary")
                .complete
        );
    }

    #[test]
    fn absent_source_snapshot_refuses_before_ssa_construction() {
        let blocks = const_return_blocks(0x401000, 0);
        let arch = x86_64_result_arch();
        let session = EngineSession::new();
        let request =
            EngineAnalyzeRequest::full_semantics_for_function(EngineAnalyzeFunctionRequestInput {
                function: EngineFunctionInput {
                    function_name: "sym.no_snapshot".to_string(),
                    function_addr: 0x401000,
                    blocks: blocks.clone(),
                    arch: Some(arch.clone()),
                    source_snapshot: None,
                    semantic_metadata_enabled: false,
                },
                ptr_bits: Some(64),
                reg_type_hints: HashMap::new(),
                parsed_context: r2types::ParsedExternalContext::default(),
                interproc_max_iterations: 1,
                symbolic_scope: None,
                include_interproc_summary_set: false,
            });

        let refusal = session
            .analyze_checked(request)
            .expect_err("missing source snapshot must refuse");
        assert_eq!(refusal.reason, MISSING_SOURCE_SNAPSHOT_REFUSAL);
        assert_eq!(refusal.phase, EnginePhase::SnapshotContext);
    }

    #[test]
    fn request_assumptions_produce_one_shared_semantic_artifact() {
        let arch = x86_64_exact_rdi_arch();
        let mut block = R2ILBlock::new(0x401000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::unique(0, 8),
            src: r2il::Varnode::register(0x10, 8),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::unique(0, 8),
        });
        let parsed_context = r2types::ParsedExternalContext {
            assumptions: r2ssa::AssumptionSet::new(vec![register_assumption(
                "rdi-seven",
                "RDI",
                7,
            )]),
            ..r2types::ParsedExternalContext::default()
        };
        let response = EngineSession::new()
            .analyze_checked(EngineAnalyzeRequest {
                function_name: "sym.assumed".to_string(),
                function_addr: 0x401000,
                blocks: vec![block],
                arch: Some(arch),
                source_snapshot: Some(exact_rdi_test_source_snapshot("sym.assumed/rev1")),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                interproc_max_iterations: 1,
                symbolic_scope: None,
                semantic_mode: EngineSemanticMode::Optional,
                include_interproc_summary_set: true,
                execution: EngineExecutionControl::default(),
            })
            .expect("assumption-conditioned analysis");

        assert!(response.artifact.trusted_ssa.is_none());
        let (usage, conditioned) = prepared_assumption_conditioning(response.artifact.ssa_func());
        assert!(conditioned);
        assert_eq!(usage.applied.len(), 1);
    }

    fn x86_64_result_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.set_memory_endianness(r2il::Endianness::Little);
        for (name, offset) in [("rax", 0), ("rsp", 0x28), ("rip", 0x30)] {
            let storage = r2il::RegisterStorage { offset, size: 8 };
            arch.add_register(r2il::RegisterDef::new(name, offset, 8));
            arch.register_projections.push(r2il::RegisterProjection {
                written: storage,
                disposition: r2il::RegisterProjectionDisposition::Bound {
                    carrier: storage,
                    slice: r2il::RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 64,
                    },
                },
            });
        }
        arch
    }

    fn x86_64_exact_rdi_arch() -> r2il::ArchSpec {
        let mut arch = x86_64_result_arch();
        arch.add_register(r2il::RegisterDef::new("rdi", 0x10, 8));
        arch
    }

    #[test]
    fn engine_render_target_canonicalizes_arch_without_renderer_config_type() {
        let mut arch = r2il::ArchSpec::new("amd64");
        arch.addr_size = 8;
        let (arch_name, ptr_bits, target) = EngineRenderTarget::for_arch(Some(&arch));

        assert_eq!(arch_name, "x86-64");
        assert_eq!(ptr_bits, 64);
        assert_eq!(
            target,
            EngineRenderTarget {
                arch_name: "x86-64".to_string(),
                ptr_bits: 64,
            }
        );

        let x86 = EngineRenderTarget::for_arch_name("i386", 32);
        assert_eq!(x86.arch_name, "x86");
        assert_eq!(x86.ptr_bits, 32);

        let (unknown_arch_name, unknown_target) =
            EngineRenderTarget::for_arch_with_ptr_bits(None, 32);
        assert_eq!(unknown_arch_name, "unknown");
        assert_eq!(
            unknown_target,
            EngineRenderTarget {
                arch_name: "unknown".to_string(),
                ptr_bits: 32,
            }
        );

        let riscv = EngineRenderTarget::for_arch_name("riscv32", 32).to_decompiler_config();
        assert_eq!(riscv.ptr_size, 32);
        assert_eq!(riscv.fp_name, "s0");
        assert_eq!(riscv.arg_regs.first().map(String::as_str), Some("a0"));

        let mut arm64 = r2il::ArchSpec::new("arm64");
        arm64.addr_size = 8;
        assert_eq!(
            engine_normalized_arch_name(Some(&arm64)).as_deref(),
            Some("aarch64")
        );
        let mut rv64 = r2il::ArchSpec::new("riscv:LE:64:default");
        rv64.addr_size = 8;
        assert_eq!(
            engine_normalized_arch_name(Some(&rv64)).as_deref(),
            Some("riscv64")
        );

        let mut contradictory = r2il::ArchSpec::new("x86-64");
        contradictory.addr_size = 4;
        let prepared = r2ssa::SsaArtifact::for_decompile(
            &const_return_blocks(0x401000, 0),
            Some(&contradictory),
        )
        .expect("mismatched family/width remains analyzable");
        assert!(EngineRenderTarget::for_prepared(&prepared).is_none());
    }

    #[test]
    fn analysis_policy_tracks_radare2_analysis_depths() {
        let basic = analysis_policy_for_radare2_depth(RADARE2_ANALYSIS_DEPTH_BASIC);
        assert_eq!(basic.mode, EngineAnalysisMode::Fast);
        assert_eq!(basic.type_writeback_mode, EngineTypeWritebackMode::Off);
        assert_eq!(basic.type_interproc_max_iters, 1);
        assert_eq!(basic.type_max_blocks, 96);
        assert_eq!(basic.type_global_max_links, 8);
        assert_eq!(basic.type_max_decls, 8);
        assert_eq!(basic.type_max_mutations, 32);

        let balanced = analysis_policy_for_radare2_depth(0);
        assert_eq!(balanced.mode, EngineAnalysisMode::Balanced);
        assert_eq!(
            balanced.type_writeback_mode,
            EngineTypeWritebackMode::Balanced
        );
        assert_eq!(balanced.type_interproc_max_iters, 4);
        assert_eq!(balanced.type_max_blocks, 200);
        assert_eq!(balanced.type_global_max_links, 32);
        assert_eq!(balanced.type_max_decls, 32);
        assert_eq!(balanced.type_max_mutations, 128);

        let aggressive = analysis_policy_for_radare2_depth(RADARE2_ANALYSIS_DEPTH_AGGRESSIVE);
        assert_eq!(aggressive.mode, EngineAnalysisMode::Full);
        assert_eq!(
            aggressive.type_writeback_mode,
            EngineTypeWritebackMode::Aggressive
        );
        assert_eq!(aggressive.type_interproc_max_iters, 12);
        assert_eq!(aggressive.type_max_blocks, 500);
        assert_eq!(aggressive.type_global_max_links, 128);
        assert_eq!(aggressive.type_max_decls, 64);
        assert_eq!(aggressive.type_max_mutations, 512);
    }

    #[test]
    fn analysis_policy_is_monotonic_from_basic_to_aggressive() {
        let basic = analysis_policy_for_depth(EngineAnalysisDepth::Basic);
        let balanced = analysis_policy_for_depth(EngineAnalysisDepth::Default);
        let aggressive = analysis_policy_for_depth(EngineAnalysisDepth::Aggressive);

        assert!(basic.mode.level() < balanced.mode.level());
        assert!(balanced.mode.level() < aggressive.mode.level());
        assert!(basic.type_writeback_mode.level() < balanced.type_writeback_mode.level());
        assert!(balanced.type_writeback_mode.level() < aggressive.type_writeback_mode.level());
        assert!(basic.type_interproc_max_iters < balanced.type_interproc_max_iters);
        assert!(balanced.type_interproc_max_iters < aggressive.type_interproc_max_iters);
        assert!(basic.type_max_blocks < balanced.type_max_blocks);
        assert!(balanced.type_max_blocks < aggressive.type_max_blocks);
        assert!(basic.type_global_max_links < balanced.type_global_max_links);
        assert!(balanced.type_global_max_links < aggressive.type_global_max_links);
        assert!(basic.type_max_decls < balanced.type_max_decls);
        assert!(balanced.type_max_decls < aggressive.type_max_decls);
        assert!(basic.type_max_mutations < balanced.type_max_mutations);
        assert!(balanced.type_max_mutations < aggressive.type_max_mutations);
    }

    #[test]
    fn engine_owns_type_writeback_apply_policy_mapping() {
        assert_eq!(
            type_writeback_apply_policy_for_mode(EngineTypeWritebackMode::Off).mode,
            r2types::TypeWritebackApplyMode::Off
        );
        assert_eq!(
            type_writeback_apply_policy_for_mode(EngineTypeWritebackMode::Balanced).mode,
            r2types::TypeWritebackApplyMode::Balanced
        );
        assert_eq!(
            type_writeback_apply_policy_for_mode(EngineTypeWritebackMode::Aggressive).mode,
            r2types::TypeWritebackApplyMode::Aggressive
        );
    }

    #[test]
    fn engine_type_writeback_mutation_kind_ids_are_stable() {
        let cases = [
            (
                r2types::TypeWritebackMutationKind::Signature,
                TYPE_WRITEBACK_MUTATION_SIGNATURE_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::Callconv,
                TYPE_WRITEBACK_MUTATION_CALLCONV_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::Var,
                TYPE_WRITEBACK_MUTATION_VAR_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::VarRename,
                TYPE_WRITEBACK_MUTATION_VAR_RENAME_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::VarType,
                TYPE_WRITEBACK_MUTATION_VAR_TYPE_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::Xref,
                TYPE_WRITEBACK_MUTATION_XREF_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::Comment,
                TYPE_WRITEBACK_MUTATION_COMMENT_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::Flag,
                TYPE_WRITEBACK_MUTATION_FLAG_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::TypeDecl,
                TYPE_WRITEBACK_MUTATION_TYPE_DECL_ID,
            ),
            (
                r2types::TypeWritebackMutationKind::TypeLink,
                TYPE_WRITEBACK_MUTATION_TYPE_LINK_ID,
            ),
        ];

        for (kind, expected) in cases {
            assert_eq!(type_writeback_mutation_kind_id(kind), expected);
        }
    }

    #[test]
    fn engine_interproc_summary_json_merges_symbolic_scope_report() {
        let root_blocks = const_return_blocks(0x401000, 0);
        let helper_blocks = const_return_blocks(0x402000, 1);
        let root_prepared =
            Arc::new(r2ssa::SsaArtifact::for_symbolic(&root_blocks, None).expect("root prepared"));
        let helper_prepared = Arc::new(
            r2ssa::SsaArtifact::for_symbolic(&helper_blocks, None).expect("helper prepared"),
        );
        let scope = r2sym::PreparedFunctionScope::new(
            0x401000,
            vec![
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x401000),
                    name: Some("root".to_string()),
                    prepared: root_prepared,
                },
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(0x402000),
                    name: Some("helper".to_string()),
                    prepared: helper_prepared,
                },
            ],
        )
        .expect("scope");
        let existing_scope = serde_json::json!({
            "payloads": [{ "function_addr": 0x403000u64, "function_name": "seeded" }],
            "seeds": [{ "id": 0x403000u64, "name": "seeded" }],
        });

        let interproc = interproc_summary_json(EngineInterprocSummaryJsonInput {
            callsite_count: 2,
            iterations: 0,
            max_iterations: 0,
            converged: true,
            summary: None,
            scope_report: Some(&existing_scope),
            symbolic_scope: Some(&scope),
        });
        let scope = interproc.scope.expect("merged scope");

        assert_eq!(interproc.iterations, 1);
        assert_eq!(interproc.max_iterations, 1);
        assert_eq!(scope["phase"], "symbolic_scope");
        assert_eq!(scope["payloads"].as_array().expect("payloads").len(), 2);
        assert_eq!(scope["seeds"].as_array().expect("seeds").len(), 2);
        assert_eq!(scope["payloads"][1]["function_addr"], 0x402000);
        assert_eq!(scope["payloads"][1]["function_name"], "helper");
        assert_eq!(scope["seeds"][1]["id"], 0x402000);
        assert_eq!(scope["seeds"][1]["name"], "helper");
    }

    #[test]
    fn engine_owns_type_writeback_function_facts_projection() {
        let mut type_facts = FunctionTypeFacts::default();
        type_facts.external_type_db.structs.insert(
            "type.Foo".to_string(),
            r2types::ExternalStruct {
                name: "Foo".to_string(),
                fields: BTreeMap::new(),
            },
        );
        type_facts.external_type_db.structs.insert(
            "type.Foo.alias".to_string(),
            r2types::ExternalStruct {
                name: "Foo".to_string(),
                fields: BTreeMap::new(),
            },
        );
        type_facts
            .field_access_certificates
            .push(r2types::FieldAccessCertificate {
                slot: 1,
                field_offset: 0x10,
                field_name: "len".to_string(),
                field_type: None,
            });
        type_facts
            .field_access_certificates
            .push(r2types::FieldAccessCertificate {
                slot: 1,
                field_offset: 0x10,
                field_name: "len".to_string(),
                field_type: None,
            });
        let function_facts = FunctionFacts::new(type_facts, None);

        assert_eq!(
            type_writeback_external_struct_names(&function_facts),
            vec!["Foo".to_string()]
        );
        assert_eq!(
            type_writeback_field_access_certificate_names(&function_facts),
            vec!["arg1+0x10:len".to_string()]
        );
    }

    #[test]
    fn post_analysis_plan_owns_mode_budgets_and_focus_thresholds() {
        let fast = post_analysis_plan_for_radare2_depth(RADARE2_ANALYSIS_DEPTH_BASIC, 512);
        assert_eq!(fast.policy.mode, EngineAnalysisMode::Fast);
        assert_eq!(fast.post_budget_us, POST_ANALYSIS_FAST_BUDGET_USEC);
        assert!(!fast.xref_enabled);
        assert!(!fast.taint_enabled);
        assert!(!fast.signature_writeback_enabled);
        assert!(!fast.type_writeback_enabled);
        assert!(!fast.balanced_focus_only);
        assert!(!fast.taint_focus_only);
        assert!(!fast.signature_writeback_focus_only);
        assert!(!fast.type_writeback_focus_only);

        let balanced = post_analysis_plan_for_radare2_depth(0, 1);
        assert_eq!(balanced.policy.mode, EngineAnalysisMode::Balanced);
        assert_eq!(balanced.post_budget_us, POST_ANALYSIS_BALANCED_BUDGET_USEC);
        assert!(balanced.xref_enabled);
        assert!(!balanced.taint_enabled);
        assert!(balanced.signature_writeback_enabled);
        assert!(balanced.type_writeback_enabled);
        assert!(balanced.balanced_focus_only);
        assert!(!balanced.taint_focus_only);
        assert!(balanced.signature_writeback_focus_only);
        assert!(balanced.type_writeback_focus_only);

        let full = post_analysis_plan_for_radare2_depth(RADARE2_ANALYSIS_DEPTH_AGGRESSIVE, 129);
        assert_eq!(full.policy.mode, EngineAnalysisMode::Full);
        assert_eq!(full.post_budget_us, POST_ANALYSIS_AGGRESSIVE_BUDGET_USEC);
        assert!(full.xref_enabled);
        assert!(full.taint_enabled);
        assert!(full.signature_writeback_enabled);
        assert!(full.type_writeback_enabled);
        assert!(!full.balanced_focus_only);
        assert!(full.taint_focus_only);
        assert!(full.signature_writeback_focus_only);
        assert!(full.type_writeback_focus_only);
    }

    #[test]
    fn auto_callback_plan_owns_mode_gate_and_scalar_thresholds() {
        let ok_metrics = EngineAutoCallbackMetrics {
            basic_block_count: AUTO_CALLBACK_MAX_BLOCKS,
            cost: AUTO_CALLBACK_MAX_COST,
            linear_size: AUTO_CALLBACK_MAX_LINEAR_SIZE,
        };
        let full = auto_callback_plan_for_radare2_depth(
            RADARE2_ANALYSIS_DEPTH_AGGRESSIVE,
            EngineAutoCallbackKind::AnalyzeFunction,
            ok_metrics,
        );
        assert!(full.allowed);
        assert_eq!(full.kind, EngineAutoCallbackKind::AnalyzeFunction);
        assert_eq!(full.reason, EngineAutoCallbackRefusalReason::Allowed);

        let balanced_deep_callback = auto_callback_plan_for_radare2_depth(
            0,
            EngineAutoCallbackKind::AnalyzeFunction,
            ok_metrics,
        );
        assert!(!balanced_deep_callback.allowed);
        assert_eq!(
            balanced_deep_callback.reason,
            EngineAutoCallbackRefusalReason::ModeNotFull
        );

        let balanced_xref = auto_callback_plan_for_radare2_depth(
            0,
            EngineAutoCallbackKind::PostAnalysisXref,
            ok_metrics,
        );
        assert!(balanced_xref.allowed);
        assert_eq!(
            balanced_xref.reason,
            EngineAutoCallbackRefusalReason::Allowed
        );

        let too_many_blocks = auto_callback_plan_for_radare2_depth(
            RADARE2_ANALYSIS_DEPTH_AGGRESSIVE,
            EngineAutoCallbackKind::DataRefs,
            EngineAutoCallbackMetrics {
                basic_block_count: AUTO_CALLBACK_MAX_BLOCKS + 1,
                ..ok_metrics
            },
        );
        assert!(!too_many_blocks.allowed);
        assert_eq!(
            too_many_blocks.reason,
            EngineAutoCallbackRefusalReason::TooManyBlocks
        );

        let too_large = auto_callback_plan_for_radare2_depth(
            RADARE2_ANALYSIS_DEPTH_AGGRESSIVE,
            EngineAutoCallbackKind::PostAnalysisTaint,
            EngineAutoCallbackMetrics {
                linear_size: AUTO_CALLBACK_MAX_LINEAR_SIZE + 1,
                ..ok_metrics
            },
        );
        assert!(!too_large.allowed);
        assert_eq!(too_large.reason, EngineAutoCallbackRefusalReason::TooLarge);

        let too_costly = auto_callback_plan_for_radare2_depth(
            RADARE2_ANALYSIS_DEPTH_AGGRESSIVE,
            EngineAutoCallbackKind::PostAnalysisXref,
            EngineAutoCallbackMetrics {
                cost: AUTO_CALLBACK_MAX_COST + 1,
                ..ok_metrics
            },
        );
        assert!(!too_costly.allowed);
        assert_eq!(
            too_costly.reason,
            EngineAutoCallbackRefusalReason::TooCostly
        );
    }

    #[test]
    fn type_analysis_interproc_budget_policy_is_engine_owned() {
        assert!(type_analysis_interproc_prefers_bounded_plan(0, false));
        assert!(type_analysis_interproc_prefers_bounded_plan(1, false));
        assert!(!type_analysis_interproc_prefers_bounded_plan(1, true));
        assert!(!type_analysis_interproc_prefers_bounded_plan(2, false));
    }

    #[test]
    fn analyze_request_builders_own_semantic_mode_selection() {
        let parts = EngineAnalyzeRequestParts {
            function_name: "sym.builder".to_string(),
            function_addr: 0x401000,
            blocks: const_return_blocks(0x401000, 0),
            arch: None,
            source_snapshot: Some(test_source_snapshot("sym.builder/rev1")),
            ptr_bits: 64,
            semantic_metadata_enabled: false,
            reg_type_hints: HashMap::new(),
            parsed_context: r2types::parse_external_context_json("{}", 64),
            interproc_max_iterations: 1,
            symbolic_scope: None,
            include_interproc_summary_set: true,
        };

        let full = EngineAnalyzeRequest::full_semantics(parts.clone());
        assert!(matches!(full.semantic_mode, EngineSemanticMode::Full));

        let compile_missing =
            EngineAnalyzeRequest::from_compile_missing_semantics(parts.clone(), true);
        assert!(matches!(
            compile_missing.semantic_mode,
            EngineSemanticMode::Full
        ));

        let optional = EngineAnalyzeRequest::from_compile_missing_semantics(parts, false);
        assert!(matches!(
            optional.semantic_mode,
            EngineSemanticMode::Optional
        ));
    }

    #[test]
    fn analyze_request_input_builder_owns_parts_and_pointer_width() {
        let mut arch = r2il::ArchSpec::new("x86");
        arch.addr_size = 4;
        let input = EngineAnalyzeRequestInput {
            function_name: "sym.input_builder".to_string(),
            function_addr: 0x402000,
            blocks: const_return_blocks(0x402000, 0),
            arch: Some(arch),
            source_snapshot: Some(test_source_snapshot("sym.input_builder/rev1")),
            ptr_bits: None,
            semantic_metadata_enabled: true,
            reg_type_hints: HashMap::new(),
            parsed_context: r2types::parse_external_context_json("{}", 32),
            interproc_max_iterations: 2,
            symbolic_scope: None,
            include_interproc_summary_set: true,
        };

        let full = EngineAnalyzeRequest::full_semantics_from_input(input.clone());
        assert_eq!(full.ptr_bits, 32);
        assert!(matches!(full.semantic_mode, EngineSemanticMode::Full));
        assert_eq!(full.function_name, "sym.input_builder");

        let explicit = EngineAnalyzeRequest::from_input_with_compile_missing_semantics(
            EngineAnalyzeRequestInput {
                ptr_bits: Some(64),
                ..input
            },
            false,
        );
        assert_eq!(explicit.ptr_bits, 64);
        assert!(matches!(
            explicit.semantic_mode,
            EngineSemanticMode::Optional
        ));

        let grouped =
            EngineAnalyzeRequest::full_semantics_for_function(EngineAnalyzeFunctionRequestInput {
                function: EngineFunctionInput {
                    function_name: "sym.grouped".to_string(),
                    function_addr: 0x403000,
                    blocks: const_return_blocks(0x403000, 0),
                    arch: explicit.arch.clone(),
                    source_snapshot: Some(test_source_snapshot("sym.grouped/rev1")),
                    semantic_metadata_enabled: false,
                },
                ptr_bits: Some(32),
                reg_type_hints: HashMap::new(),
                parsed_context: r2types::parse_external_context_json("{}", 32),
                interproc_max_iterations: 1,
                symbolic_scope: None,
                include_interproc_summary_set: false,
            });
        assert_eq!(grouped.function_name, "sym.grouped");
        assert_eq!(grouped.ptr_bits, 32);
        assert!(matches!(grouped.semantic_mode, EngineSemanticMode::Full));
    }

    #[test]
    fn signature_inference_is_engine_owned_and_uses_prepared_arch() {
        let mut arch = r2il::ArchSpec::new("amd64");
        arch.addr_size = 8;
        let blocks = const_return_blocks(0x401000, 0);
        let snapshot = test_source_snapshot("sym.owner/rev1");
        let analysis =
            build_engine_analysis_from_parts("sym.owner", &blocks, Some(&arch), &snapshot)
                .expect("analysis");

        let signature = infer_signature_from_analysis(EngineSignatureInferenceRequest {
            analysis: &analysis,
        });

        assert_eq!(signature.function_name, "sym.owner");
        assert_eq!(signature.arch, "x86-64");
    }

    #[test]
    fn register_type_hint_collection_is_engine_owned() {
        let ptr_reg = r2il::Varnode::register(0, 8).with_meta(r2il::VarnodeMetadata {
            scalar_kind: Some(r2il::ScalarKind::UnsignedInt),
            pointer_hint: Some(r2il::PointerHint::PointerLike),
            ..Default::default()
        });
        let int_reg = r2il::Varnode::register(4, 4).with_meta(r2il::VarnodeMetadata {
            scalar_kind: Some(r2il::ScalarKind::SignedInt),
            ..Default::default()
        });
        let mut block = r2il::R2ILBlock::new(0x401000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: int_reg,
            src: r2il::Varnode::constant(1, 4),
        });
        block.push(r2il::R2ILOp::IntAdd {
            dst: r2il::Varnode::unique(0, 8),
            a: ptr_reg,
            b: r2il::Varnode::constant(8, 8),
        });

        let hints = collect_register_type_hints_with_names(&[block], |vn| match vn.offset {
            0 => Some("RDI".to_string()),
            4 => Some("ESI".to_string()),
            _ => None,
        });

        assert_eq!(
            hints.get("rdi").map(|hint| hint.ty.as_str()),
            Some("void *")
        );
        assert_eq!(
            hints.get("esi").map(|hint| hint.ty.as_str()),
            Some("int32_t")
        );
        assert!(!hints.contains_key("RDI"));
    }

    #[test]
    fn analyze_function_request_collects_register_hints_inside_engine() {
        let ptr_reg = r2il::Varnode::register(0, 8).with_meta(r2il::VarnodeMetadata {
            scalar_kind: Some(r2il::ScalarKind::UnsignedInt),
            pointer_hint: Some(r2il::PointerHint::PointerLike),
            ..Default::default()
        });
        let mut block = r2il::R2ILBlock::new(0x401000, 4);
        block.push(r2il::R2ILOp::IntAdd {
            dst: r2il::Varnode::unique(0, 8),
            a: ptr_reg,
            b: r2il::Varnode::constant(8, 8),
        });
        let input = EngineAnalyzeFunctionRequestInput {
            function: EngineFunctionInput {
                function_name: "sym.hints".to_string(),
                function_addr: 0x401000,
                blocks: vec![block],
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.hints/rev1")),
                semantic_metadata_enabled: true,
            },
            ptr_bits: Some(64),
            reg_type_hints: HashMap::new(),
            parsed_context: r2types::parse_external_context_json("{}", 64),
            interproc_max_iterations: 1,
            symbolic_scope: None,
            include_interproc_summary_set: false,
        };

        let request = EngineAnalyzeRequest::full_semantics_for_function_with_register_names(
            input.clone(),
            |vn| (vn.offset == 0).then(|| "RDI".to_string()),
        );
        assert_eq!(
            request
                .reg_type_hints
                .get("rdi")
                .map(|hint| hint.ty.as_str()),
            Some("void *")
        );

        let disabled = EngineAnalyzeRequest::full_semantics_for_function_with_register_names(
            EngineAnalyzeFunctionRequestInput {
                function: EngineFunctionInput {
                    semantic_metadata_enabled: false,
                    ..input.function
                },
                ..input
            },
            |vn| (vn.offset == 0).then(|| "RDI".to_string()),
        );
        assert!(disabled.reg_type_hints.is_empty());
    }

    #[test]
    fn interproc_summary_scope_requires_exact_root_and_source_helper_provenance() {
        let root_addr = 0x401000;
        let helper_addr = 0x402000;
        let root_blocks = const_return_blocks(root_addr, 0);
        let helper_blocks = const_return_blocks(helper_addr, 1);
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rdi", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        arch.add_register(r2il::RegisterDef::new("rsp", 24, 8));
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"interproc-owner/rev1".to_vec(),
            "sysv64",
            [r2ssa::SourceAbiParameterSpec::new(0, storage(8))],
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(24)))
        .expect("exact interproc interface");
        let root_prepared = Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(
                &root_blocks,
                Some(&arch),
                interface.clone(),
            )
            .expect("root prepared"),
        );
        let helper_prepared = Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(
                &helper_blocks,
                Some(&arch),
                interface.clone(),
            )
            .expect("helper prepared"),
        );
        let analysis = EngineAnalysis::from_prepared_ssa(Arc::clone(&root_prepared));
        let exact_scope = r2sym::PreparedFunctionScope::new(
            root_addr,
            vec![
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(root_addr),
                    name: Some("root".to_string()),
                    prepared: Arc::clone(&root_prepared),
                },
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(helper_addr),
                    name: Some("helper".to_string()),
                    prepared: Arc::clone(&helper_prepared),
                },
            ],
        )
        .expect("exact scope");
        let foreign_root = Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(&root_blocks, Some(&arch), interface)
                .expect("foreign root prepared"),
        );
        let foreign_scope = r2sym::PreparedFunctionScope::new(
            root_addr,
            vec![
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(root_addr),
                    name: Some("root".to_string()),
                    prepared: foreign_root,
                },
                r2sym::ScopedPreparedFunction {
                    id: r2ssa::InterprocFunctionId(helper_addr),
                    name: Some("helper".to_string()),
                    prepared: helper_prepared,
                },
            ],
        )
        .expect("foreign scope");
        let solve = |symbolic_scope| {
            build_prepared_interproc_summary_set(InterprocSummaryBuildInput {
                analysis: &analysis,
                max_iterations: 1,
                symbolic_scope,
                trusted_callees: &[],
            })
        };

        assert_eq!(
            solve(Some(&exact_scope)).expect_err("manual helper must not become source evidence"),
            r2ssa::PreparedInterprocSummaryError::ManualFunction
        );

        let foreign = solve(Some(&foreign_scope)).expect("root-only prepared summary set");
        assert_eq!(foreign.report().diagnostics.scope_size, 1);
        assert!(
            !foreign
                .report()
                .summaries
                .contains_key(&r2ssa::InterprocFunctionId(helper_addr))
        );
    }

    fn windows_x64_runtime_scope_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rcx", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rdx", 16, 8));
        arch.add_register(r2il::RegisterDef::new("r8", 24, 8));
        arch.add_register(r2il::RegisterDef::new("r9", 32, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 40, 8));
        arch.add_register(r2il::RegisterDef::new("rsp", 48, 8));
        arch
    }

    fn runtime_reg(offset: u64, size: u32) -> r2il::Varnode {
        r2il::Varnode {
            space: r2il::SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn windows_runtime_source_snapshot(
        revision: &str,
        function_convention: &str,
        calls: &[(u64, usize, u64, usize, bool, &str)],
    ) -> Arc<EngineSourceSnapshot> {
        let revision_identity = revision.as_bytes().to_vec();
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let function_interface = r2ssa::SourceFunctionInterface::new_exact(
            revision_identity.clone(),
            function_convention,
            [],
            r2ssa::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register(40)))
        .and_then(|interface| interface.with_stack_pointer_storage(register(48)))
        .expect("exact runtime function interface");
        let argument_offsets = [8, 16, 24, 32];
        let call_site_interfaces = calls
            .iter()
            .map(
                |&(block_addr, op_index, target, argument_count, complete, convention)| {
                    r2ssa::SourceCallSiteInterface::new(
                        revision_identity.clone(),
                        r2ssa::SourceCallSiteIdentity::new(
                            block_addr,
                            op_index,
                            r2ssa::CanonicalStorageId {
                                space: r2ssa::CanonicalStorageSpace::Constant,
                                offset: target,
                                size: 8,
                            },
                        ),
                        complete,
                        convention,
                        argument_offsets[..argument_count].iter().enumerate().map(
                            |(index, offset)| {
                                r2ssa::SourceCallArgumentSpec::new(index as u32, register(*offset))
                            },
                        ),
                        false,
                        false,
                        r2ssa::SourceCallResult::Void,
                    )
                    .expect("exact runtime callsite interface")
                },
            )
            .collect::<Vec<_>>();
        Arc::new(
            EngineSourceSnapshot::new(
                revision_identity,
                Some(function_interface),
                call_site_interfaces,
            )
            .expect("exact runtime source snapshot"),
        )
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

    fn symbolic_register_branch_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("symbolic-assumption-test");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("QUERY_ARG", 0x38, 8));
        arch.add_register(r2il::RegisterDef::new("QUERY_PREDICATE", 0x80, 1));
        arch
    }

    fn symbolic_register_assumption(prepared: &r2ssa::SsaArtifact) -> r2ssa::AnalysisAssumption {
        let storage = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.version == 0 && value.var.is_register() && value.var.size == 8)
            .expect("version-zero input register")
            .canonical_storage
            .expect("input register has exact storage");
        let reg_name = prepared
            .machine_context()
            .register_name(storage)
            .expect("source register map names the input storage");
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

    fn register_assumption(id: &str, name: &str, value: u64) -> r2ssa::AnalysisAssumption {
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

        let summary = route::raw_cfg_risk_summary_for_preprobe(&[entry, switch]);

        assert_eq!(summary.block_count, 2);
        assert_eq!(summary.loop_count, 1);
        assert_eq!(summary.back_edge_count, 2);
        assert_eq!(summary.switch_block_count, 1);
        assert_eq!(summary.max_switch_cases, 2);
    }

    #[test]
    fn analyze_reports_planning_time() {
        let session = EngineSession::new();
        let request = EngineAnalyzeRequest {
            function_name: "sym.zero".to_string(),
            function_addr: 0x401000,
            blocks: const_return_blocks(0x401000, 0),
            arch: Some(x86_64_result_arch()),
            source_snapshot: Some(exact_empty_test_source_snapshot("sym.zero/analyze/rev1")),
            trusted_ssa: None,
            trusted_callees: Vec::new(),
            ptr_bits: 64,
            semantic_metadata_enabled: false,
            reg_type_hints: HashMap::new(),
            parsed_context: r2types::ParsedExternalContext::default(),
            interproc_max_iterations: 1,
            symbolic_scope: None,
            semantic_mode: EngineSemanticMode::Full,
            include_interproc_summary_set: true,
            execution: EngineExecutionControl::default(),
        };
        let response = session.analyze(request).expect("analysis should succeed");

        assert!(response.metrics.planning_time > Duration::default());
        assert_eq!(response.metrics.phase_timings.len(), EnginePhase::ALL.len());
        assert_eq!(
            response
                .metrics
                .phase_timings
                .iter()
                .map(|timing| timing.phase)
                .collect::<Vec<_>>(),
            EnginePhase::ALL
        );
        assert_eq!(
            response.metrics.phase_timings[2].status,
            EnginePhaseStatus::Executed
        );

        let decompiled = session.decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: "sym.zero".to_string(),
                    function_addr: 0x401000,
                    blocks: const_return_blocks(0x401000, 0),
                    arch: Some(x86_64_result_arch()),
                    source_snapshot: Some(exact_empty_test_source_snapshot(
                        "sym.zero/decompile/rev1",
                    )),
                    semantic_metadata_enabled: false,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        assert_eq!(
            decompiled.metrics.phase_timings.len(),
            EnginePhase::ALL.len()
        );
        assert_eq!(
            decompiled.metrics.phase_timings[10].status,
            EnginePhaseStatus::NotExecuted,
            "FFI conversion is outside the engine measurement boundary"
        );
    }

    fn controlled_ssa_test_request(
        function_name: &str,
        blocks: Vec<R2ILBlock>,
    ) -> EngineAnalyzeRequest {
        EngineAnalyzeRequest::full_semantics_for_function(EngineAnalyzeFunctionRequestInput {
            function: EngineFunctionInput {
                function_name: function_name.to_string(),
                function_addr: blocks.first().map(|block| block.addr).unwrap_or(0),
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot(&format!(
                    "{function_name}/controlled/rev1"
                ))),
                semantic_metadata_enabled: false,
            },
            ptr_bits: Some(64),
            reg_type_hints: HashMap::new(),
            parsed_context: r2types::ParsedExternalContext::default(),
            interproc_max_iterations: 1,
            symbolic_scope: None,
            include_interproc_summary_set: false,
        })
    }

    fn controlled_r2dec_render_request() -> EngineDecompileRequest {
        let mut block = R2ILBlock::new(0x614000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::constant(7, 8),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(0x30, 8),
        });
        let blocks = vec![block];
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"controlled-r2dec-source".to_vec(),
            "sysv64",
            std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
            r2ssa::SourceFunctionReturn::Register {
                storage: r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 8,
                },
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| {
            interface.with_stack_pointer_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x28,
                size: 8,
            })
        })
        .and_then(|interface| {
            interface.with_return_address_storage(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x30,
                size: 8,
            })
        })
        .expect("exact controlled r2dec interface");
        let prepared = Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(
                &blocks,
                Some(&x86_64_result_arch()),
                interface,
            )
            .expect("prepared render SSA")
            .with_name("sym.r2dec_controlled"),
        );
        let writeback = r2types::build_source_owned_type_writeback_analysis(
            r2types::TypeWritebackAnalysisRequest::new(
                prepared,
                r2types::ParsedExternalContext::default(),
            )
            .expect("coherent test owner request"),
        )
        .expect("source-owned test facts");
        let source_owned_facts = writeback
            .finalize_for_decompile(r2types::DecompileFinalization {
                kind: r2types::DecompileRouteKind::Standard,
                reason: "controlled r2dec residual test".to_string(),
                fallback_comment: None,
            })
            .expect("compatible controlled r2dec route");
        EngineDecompileRequest {
            function_name: "sym.r2dec_controlled".to_string(),
            source_owned_facts,
            trusted_ssa: None,
            input_quality: None,
            render_target: EngineRenderTarget::default(),
            execution: EngineExecutionControl::default(),
            metrics: EngineMetrics::default(),
        }
    }

    #[derive(Default)]
    struct CountingRenderControl {
        polls: Cell<usize>,
    }

    impl r2ssa::SsaWorkControl for CountingRenderControl {
        fn poll(&self) -> Result<(), r2ssa::SsaExecutionStopReason> {
            self.polls.set(self.polls.get().saturating_add(1));
            Ok(())
        }
    }

    struct StopRenderAtPoll {
        polls: Cell<usize>,
        stop_at: usize,
        reason: r2ssa::SsaExecutionStopReason,
    }

    impl StopRenderAtPoll {
        fn new(stop_at: usize, reason: r2ssa::SsaExecutionStopReason) -> Self {
            Self {
                polls: Cell::new(0),
                stop_at,
                reason,
            }
        }
    }

    impl r2ssa::SsaWorkControl for StopRenderAtPoll {
        fn poll(&self) -> Result<(), r2ssa::SsaExecutionStopReason> {
            let polls = self.polls.get().saturating_add(1);
            self.polls.set(polls);
            if polls >= self.stop_at {
                Err(self.reason)
            } else {
                Ok(())
            }
        }
    }

    #[test]
    fn engine_decompiler_input_retains_exact_source_owned_facts() {
        let request = controlled_r2dec_render_request();
        let source = request.source_owned_facts.shared_source();
        let input = decompiler_input_for_engine_request(&request);

        assert!(input.source_owned_facts().shares_source(&source));
        assert_eq!(
            input.function_facts().decompile_route(),
            request.function_facts().decompile_route()
        );
    }

    #[test]
    fn r2dec_inner_stops_map_to_engine_refusals_and_keep_exact_audits() {
        let session = EngineSession::new();
        let request = controlled_r2dec_render_request();
        let decompiler_input = decompiler_input_for_engine_request(&request);
        let legacy_output = r2dec::Decompiler::new(request.render_target.to_decompiler_config())
            .decompile_input(&decompiler_input);
        let counting = CountingRenderControl::default();
        let controlled = session.decompile_with_r2dec_control(request.clone(), &counting);
        assert!(
            legacy_output.contains("return"),
            "the exact control fixture must reach native rendering: {legacy_output}"
        );
        assert!(
            controlled.output.contains("return"),
            "the engine path must render the same exact fixture: {}",
            controlled.output
        );
        assert_ne!(
            controlled.binding_audit,
            BindingShadowAuditOutcome::NotRun,
            "the completed native render must retain its exact r2dec audit: {}",
            controlled.output
        );
        assert_ne!(
            controlled.effect_obligations,
            EffectObligationAudit::NOT_RUN,
            "the completed native render must retain its exact effect audit"
        );
        assert_eq!(
            controlled.render_refusal, None,
            "the exact fixture must not cross a renderer refusal boundary"
        );
        let completed_binding_audit = controlled.binding_audit;
        let completed_effect_obligations = controlled.effect_obligations;
        let total_polls = counting.polls.get();
        assert!(total_polls > 3, "r2dec pipeline must expose inner polls");

        let mut observed = HashMap::new();
        for stop_at in 1..=total_polls {
            let stop = StopRenderAtPoll::new(stop_at, r2ssa::SsaExecutionStopReason::Cancelled);
            let response = session.decompile_with_r2dec_control(request.clone(), &stop);
            let phase = [EnginePhase::Normalization, EnginePhase::Rendering]
                .into_iter()
                .find(|phase| {
                    response.metrics.phase_timings.iter().any(|timing| {
                        timing.phase == *phase && timing.status == EnginePhaseStatus::Refused
                    })
                })
                .expect("stopped render must mark one render phase refused");
            observed.entry(phase).or_insert(stop_at);
            if observed.len() == 2 {
                break;
            }
        }
        observed.insert(EnginePhase::Rendering, total_polls);

        for phase in [EnginePhase::Normalization, EnginePhase::Rendering] {
            let stop_at = *observed
                .get(&phase)
                .unwrap_or_else(|| {
                    panic!(
                        "missing deterministic {phase:?} stop (polls={total_polls}, output={legacy_output})"
                    )
                });
            let reason = if phase == EnginePhase::Rendering {
                r2ssa::SsaExecutionStopReason::DeadlineExceeded
            } else {
                r2ssa::SsaExecutionStopReason::Cancelled
            };
            let stop = StopRenderAtPoll::new(stop_at, reason);
            let response = session.decompile_with_r2dec_control(request.clone(), &stop);
            let expected_reason = match reason {
                r2ssa::SsaExecutionStopReason::Cancelled => {
                    format!("engine request cancelled during {} phase", phase.as_str())
                }
                r2ssa::SsaExecutionStopReason::DeadlineExceeded => format!(
                    "engine request deadline exceeded during {} phase",
                    phase.as_str()
                ),
            };
            assert_eq!(response.metrics.phase_timings.len(), EnginePhase::ALL.len());
            assert!(response.metrics.phase_timings.iter().any(|timing| {
                timing.phase == phase && timing.status == EnginePhaseStatus::Refused
            }));
            assert_eq!(
                response
                    .metrics
                    .phase_timings
                    .iter()
                    .filter(|timing| timing.status == EnginePhaseStatus::Refused)
                    .count(),
                1,
                "only the interrupted phase is refused"
            );
            let normalization_status = if phase == EnginePhase::Rendering {
                EnginePhaseStatus::Folded
            } else {
                EnginePhaseStatus::Refused
            };
            let structuring_status = if phase == EnginePhase::Rendering {
                EnginePhaseStatus::Folded
            } else {
                EnginePhaseStatus::NotExecuted
            };
            assert_eq!(
                response.metrics.phase_timings[EnginePhase::Normalization as usize].status,
                normalization_status
            );
            assert_eq!(
                response.metrics.phase_timings[EnginePhase::Structuring as usize].status,
                structuring_status
            );
            assert_eq!(
                response.metrics.phase_timings[EnginePhase::FfiConversion as usize].status,
                EnginePhaseStatus::NotExecuted
            );
            assert_eq!(
                response.diagnostics.route_reason.as_deref(),
                Some(expected_reason.as_str()),
                "an execution stop remains primary over audits retained from the partial render"
            );
            if phase == EnginePhase::Rendering {
                assert_eq!(response.binding_audit, completed_binding_audit);
                assert_eq!(response.effect_obligations, completed_effect_obligations);
                assert!(
                    !response.output.trim().is_empty(),
                    "the stopped render retains the partial output it reached"
                );
                assert!(
                    response
                        .diagnostics
                        .refusal
                        .as_deref()
                        .is_some_and(|value| value.contains(&expected_reason)),
                    "the execution stop must remain the response refusal: {}",
                    response.output
                );
            } else {
                assert_eq!(response.binding_audit, BindingShadowAuditOutcome::NotRun);
                assert_eq!(response.effect_obligations, EffectObligationAudit::NOT_RUN);
                assert!(
                    response
                        .diagnostics
                        .refusal
                        .as_deref()
                        .is_some_and(|refusal| refusal.contains(&expected_reason))
                );
                assert_eq!(
                    response
                        .function_facts
                        .decompile_route()
                        .map(|route| route.kind),
                    Some(r2types::DecompileRouteKind::FallbackComment)
                );
                assert!(response.output.starts_with("/* r2dec fallback:"));
                assert!(!response.output.contains("() {"));
            }
        }
    }

    #[test]
    fn r2dec_stop_mapping_preserves_all_decompiler_phases_and_reasons() {
        // Production r2dec deliberately refuses executable Standard rendering before its
        // structurer, while every non-Standard route exits at a summary boundary. The r2dec
        // assignment-consensus test therefore exercises the actual inner Structuring stop;
        // this engine test covers its exact cross-crate phase/reason mapping without weakening
        // that fail-closed authorization boundary.
        for (decompile_phase, engine_phase) in [
            (
                r2dec::DecompileWorkPhase::Normalization,
                EnginePhase::Normalization,
            ),
            (
                r2dec::DecompileWorkPhase::Structuring,
                EnginePhase::Structuring,
            ),
            (r2dec::DecompileWorkPhase::Rendering, EnginePhase::Rendering),
        ] {
            for reason in [
                r2ssa::SsaExecutionStopReason::Cancelled,
                r2ssa::SsaExecutionStopReason::DeadlineExceeded,
            ] {
                let mapped = engine_render_stop_from_decompiler(
                    r2dec::DecompileExecutionStop::new(decompile_phase, reason),
                    BindingShadowAuditOutcome::NotRun,
                    EffectObligationAudit {
                        disposition: EffectObligationDisposition::Refused,
                        total: 11,
                        rendered: 5,
                        justified_elision: 2,
                        refused: 1,
                        unaccounted: 2,
                        conflicts: 1,
                    },
                    PlacementAudit::NotRun,
                    Some(DecompileRenderRefusal::UnrepresentableOperation),
                );
                assert_eq!(mapped.phase, engine_phase);
                assert_eq!(*mapped.binding_audit, BindingShadowAuditOutcome::NotRun);
                assert_eq!(mapped.effect_obligations.total, 11);
                assert_eq!(mapped.effect_obligations.rendered, 5);
                assert_eq!(mapped.effect_obligations.justified_elision, 2);
                assert_eq!(mapped.effect_obligations.refused, 1);
                assert_eq!(mapped.effect_obligations.unaccounted, 2);
                assert_eq!(mapped.effect_obligations.conflicts, 1);
                assert_eq!(mapped.placement_audit, PlacementAudit::NotRun);
                assert_eq!(
                    mapped.render_refusal.as_deref(),
                    Some(&DecompileRenderRefusal::UnrepresentableOperation)
                );
                assert_eq!(
                    mapped.normalization_completed,
                    !matches!(decompile_phase, r2dec::DecompileWorkPhase::Normalization)
                );
                assert_eq!(
                    mapped.structuring_completed,
                    matches!(decompile_phase, r2dec::DecompileWorkPhase::Rendering)
                );
                match reason {
                    r2ssa::SsaExecutionStopReason::Cancelled => {
                        assert_eq!(
                            mapped.reason,
                            format!(
                                "engine request cancelled during {} phase",
                                engine_phase.as_str()
                            )
                        );
                    }
                    r2ssa::SsaExecutionStopReason::DeadlineExceeded => {
                        assert_eq!(
                            mapped.reason,
                            format!(
                                "engine request deadline exceeded during {} phase",
                                engine_phase.as_str()
                            )
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn refused_effect_obligations_produce_a_typed_engine_refusal() {
        let effect_obligations = EffectObligationAudit {
            disposition: EffectObligationDisposition::Refused,
            total: 9,
            rendered: 4,
            justified_elision: 1,
            refused: 2,
            unaccounted: 1,
            conflicts: 1,
        };
        let reason = effect_obligation_refusal_reason(effect_obligations)
            .expect("refused effects must refuse the native engine outcome");
        let render_time = Duration::from_micros(17);
        let mut metrics = EngineMetrics::default();
        metrics.record_phase(
            EnginePhase::Rendering,
            EnginePhaseStatus::Refused,
            render_time,
        );
        let sentinel_quality = r2types::FunctionInputQualityFacts {
            expected_blocks: 7,
            lifted_blocks: 7,
            actual_lifted_blocks: 7,
            read_failures: 0,
            invalid_blocks: 0,
            null_lift_failures: 0,
            truncated_blocks: 0,
            refusal_reason: None,
        };
        let response = refused_decompile_response_with_metrics_and_audits(
            "sym.effect_refusal",
            &reason,
            None,
            metrics,
            EngineDiagnostics::default(),
            Some(FunctionFacts::default().with_input_quality(sentinel_quality.clone())),
            BindingShadowAuditOutcome::NotRun,
            effect_obligations,
            PlacementAudit::NotRun,
            None,
        );

        assert_eq!(response.effect_obligations, effect_obligations);
        assert_eq!(
            response.metrics.phase_timings[EnginePhase::Rendering as usize].status,
            EnginePhaseStatus::Refused
        );
        assert_eq!(
            response.diagnostics.route_reason.as_deref(),
            Some(reason.as_str())
        );
        assert!(
            response
                .diagnostics
                .refusal
                .as_deref()
                .is_some_and(|value| value.contains(reason.as_str()))
        );
        assert!(response.output.starts_with("/* r2dec fallback:"));
        assert!(effect_obligation_refusal_reason(EffectObligationAudit::NOT_RUN).is_none());
        assert_eq!(
            response.function_facts.input_quality(),
            Some(&sentinel_quality),
            "late effect refusal replaces only the route and retains existing function facts"
        );
        assert!(
            effect_obligation_refusal_reason(EffectObligationAudit {
                disposition: EffectObligationDisposition::Admitted,
                total: 1,
                rendered: 0,
                justified_elision: 0,
                refused: 1,
                unaccounted: 0,
                conflicts: 0,
            })
            .is_some(),
            "nonzero refusal counts fail closed independently of disposition"
        );
    }

    #[test]
    fn refused_placement_produces_a_typed_engine_refusal() {
        let placement_audit =
            PlacementAudit::Refused(PlacementAuditRefusal::ReadBeforeAssignment {
                binding_index: 3,
                instruction_id: 11,
                input_index: 2,
            });
        let reason = placement_refusal_reason(placement_audit)
            .expect("refused placement must refuse the native engine outcome");
        let mut metrics = EngineMetrics::default();
        metrics.record_phase(
            EnginePhase::Rendering,
            EnginePhaseStatus::Refused,
            Duration::from_micros(18),
        );
        let response = refused_decompile_response_with_metrics_and_audits(
            "sym.placement_refusal",
            &reason,
            None,
            metrics,
            EngineDiagnostics::default(),
            None,
            BindingShadowAuditOutcome::NotRun,
            EffectObligationAudit::NOT_RUN,
            placement_audit,
            None,
        );

        assert_eq!(response.placement_audit, placement_audit);
        assert_eq!(
            response.metrics.phase_timings[EnginePhase::Rendering as usize].status,
            EnginePhaseStatus::Refused,
        );
        assert_eq!(
            response.diagnostics.route_reason.as_deref(),
            Some(reason.as_str())
        );
        assert!(
            response
                .diagnostics
                .refusal
                .as_deref()
                .is_some_and(|value| value.contains(&reason))
        );
        assert!(response.output.starts_with("/* r2dec fallback:"));
        assert!(placement_refusal_reason(PlacementAudit::Applied).is_none());
        assert!(placement_refusal_reason(PlacementAudit::NotRun).is_none());
    }

    #[test]
    fn renderer_boundary_refusal_produces_a_typed_engine_refusal() {
        let render_refusal = DecompileRenderRefusal::MissingMachineProjectionAuthorization(
            r2dec::MachineProjectionRefusalOrigin::op_lowering(),
        );
        let reason = render_refusal_reason(render_refusal);
        let render_time = Duration::from_micros(19);
        let mut metrics = EngineMetrics::default();
        metrics.record_phase(
            EnginePhase::Rendering,
            EnginePhaseStatus::Refused,
            render_time,
        );
        let response = refused_decompile_response_with_metrics_and_audits(
            "sym.render_refusal",
            &reason,
            None,
            metrics,
            EngineDiagnostics::default(),
            None,
            BindingShadowAuditOutcome::NotRun,
            EffectObligationAudit::NOT_RUN,
            PlacementAudit::NotRun,
            Some(render_refusal),
        );

        assert_eq!(response.render_refusal, Some(render_refusal));
        assert_eq!(response.effect_obligations, EffectObligationAudit::NOT_RUN);
        assert_eq!(
            response.metrics.phase_timings[EnginePhase::Rendering as usize].status,
            EnginePhaseStatus::Refused
        );
        assert_eq!(
            response.diagnostics.route_reason.as_deref(),
            Some(reason.as_str())
        );
        assert!(
            response
                .diagnostics
                .refusal
                .as_deref()
                .is_some_and(|value| value.contains(reason.as_str()))
        );
        assert!(response.output.starts_with("/* r2dec fallback:"));
        assert!(!response.output.contains("() {"));
    }

    fn analyze_with_injected_ssa_control<C: r2ssa::SsaWorkControl + ?Sized>(
        session: &EngineSession,
        request: EngineAnalyzeRequest,
        control: &C,
    ) -> Result<EngineAnalyzeResponse, EngineExecutionRefusal> {
        let started = Instant::now();
        let mut metrics = EngineMetrics::default();
        poll_engine_execution(&request.execution, EnginePhase::SnapshotContext, &metrics)?;
        let phase_started = Instant::now();
        metrics.record_phase(
            EnginePhase::SnapshotContext,
            EnginePhaseStatus::Executed,
            phase_started.elapsed(),
        );
        session.analyze_with_ssa_control(request, started, metrics, control)
    }

    enum SsaPollTrigger {
        Cancel(EngineCancellationToken),
        Stop(r2ssa::SsaExecutionStopReason),
    }

    struct DeterministicSsaControl {
        polls: Cell<usize>,
        stop_at: usize,
        trigger: SsaPollTrigger,
        downstream: Option<r2ssa::SsaExecutionControl>,
    }

    impl r2ssa::SsaWorkControl for DeterministicSsaControl {
        fn poll(&self) -> Result<(), r2ssa::SsaExecutionStopReason> {
            let polls = self.polls.get() + 1;
            self.polls.set(polls);
            if polls == self.stop_at {
                match &self.trigger {
                    SsaPollTrigger::Cancel(cancellation) => cancellation.cancel(),
                    SsaPollTrigger::Stop(reason) => return Err(*reason),
                }
            }
            self.downstream
                .as_ref()
                .map_or(Ok(()), r2ssa::SsaWorkControl::poll)
        }
    }

    #[test]
    fn analyze_checked_maps_mid_ssa_cancellation() {
        let session = EngineSession::new();
        let cancellation = EngineCancellationToken::default();
        let request =
            controlled_ssa_test_request("sym.ssa_cancelled", const_return_blocks(0x611000, 7))
                .with_cancellation(cancellation.clone());
        let control = DeterministicSsaControl {
            polls: Cell::new(0),
            stop_at: 10,
            trigger: SsaPollTrigger::Cancel(cancellation),
            downstream: Some(request.execution.ssa_execution_control()),
        };

        let refusal = analyze_with_injected_ssa_control(&session, request, &control)
            .expect_err("mid-SSA cancellation must fail closed");

        assert_eq!(control.polls.get(), 10);
        assert_eq!(refusal.phase, EnginePhase::Ssa);
        assert_eq!(refusal.reason, "engine request cancelled during ssa phase");
        assert_eq!(
            refusal.metrics.phase_timings[EnginePhase::Ssa as usize].status,
            EnginePhaseStatus::Refused
        );
    }

    #[test]
    fn analyze_checked_maps_mid_ssa_deadline() {
        let session = EngineSession::new();
        let request =
            controlled_ssa_test_request("sym.ssa_deadline", const_return_blocks(0x612000, 9));
        let control = DeterministicSsaControl {
            polls: Cell::new(0),
            stop_at: 10,
            trigger: SsaPollTrigger::Stop(r2ssa::SsaExecutionStopReason::DeadlineExceeded),
            downstream: None,
        };

        let refusal = analyze_with_injected_ssa_control(&session, request, &control)
            .expect_err("mid-SSA deadline must fail closed");

        assert_eq!(control.polls.get(), 10);
        assert_eq!(refusal.phase, EnginePhase::Ssa);
        assert_eq!(
            refusal.reason,
            "engine request deadline exceeded during ssa phase"
        );
        assert_eq!(
            refusal.metrics.phase_timings[EnginePhase::Ssa as usize].status,
            EnginePhaseStatus::Refused
        );
    }

    #[test]
    fn analyze_checked_keeps_malformed_ssa_distinct_from_execution_stops() {
        let session = EngineSession::new();
        let request = controlled_ssa_test_request("sym.ssa_malformed", Vec::new());
        let refusal = session
            .analyze_checked(request)
            .expect_err("malformed SSA input must fail closed");

        assert_eq!(refusal.phase, EnginePhase::Ssa);
        assert_eq!(
            refusal.reason,
            "malformed SSA source input during ssa phase"
        );
        assert!(!refusal.reason.contains("cancelled"));
        assert!(!refusal.reason.contains("deadline"));
        assert_eq!(
            refusal.metrics.phase_timings[EnginePhase::Ssa as usize].status,
            EnginePhaseStatus::Refused
        );
    }

    #[test]
    fn controlled_ssa_build_is_unchanged() {
        let blocks = const_return_blocks(0x613000, 11);
        let snapshot = test_source_snapshot("sym.ssa_same/rev1");
        let prepared = build_engine_analysis_from_parts("sym.ssa_same", &blocks, None, &snapshot)
            .expect("snapshot-backed analysis");
        let controlled = build_engine_analysis_from_parts_with_control(
            "sym.ssa_same",
            &blocks,
            None,
            &snapshot,
            &r2ssa::SsaExecutionControl::default(),
        )
        .expect("controlled analysis");
        assert_eq!(prepared.ssa_func.graph(), controlled.ssa_func.graph());
        assert_eq!(prepared.ssa_func.facts(), controlled.ssa_func.facts());
    }

    #[test]
    fn engine_execution_control_translates_combined_ssa_control() {
        let cancellation = EngineCancellationToken::default();
        let deadline = Instant::now()
            .checked_add(Duration::from_secs(30))
            .expect("future deadline");
        let execution =
            EngineExecutionControl::with_cancellation_and_deadline(cancellation.clone(), deadline);
        let ssa = execution.ssa_execution_control();
        assert_eq!(ssa.deadline(), Some(deadline));

        cancellation.cancel();
        assert_eq!(
            r2ssa::SsaWorkControl::poll(&ssa),
            Err(r2ssa::SsaExecutionStopReason::Cancelled)
        );
    }

    #[test]
    fn analyze_checked_refuses_pre_cancelled_request_with_full_phase_report() {
        let cancellation = EngineCancellationToken::default();
        cancellation.cancel();
        let request =
            EngineAnalyzeRequest::full_semantics_for_function(EngineAnalyzeFunctionRequestInput {
                function: EngineFunctionInput {
                    function_name: "sym.cancelled".to_string(),
                    function_addr: 0x401000,
                    blocks: const_return_blocks(0x401000, 0),
                    arch: None,
                    source_snapshot: Some(test_source_snapshot("sym.cancelled/rev1")),
                    semantic_metadata_enabled: false,
                },
                ptr_bits: Some(64),
                reg_type_hints: HashMap::new(),
                parsed_context: r2types::ParsedExternalContext::default(),
                interproc_max_iterations: 1,
                symbolic_scope: None,
                include_interproc_summary_set: false,
            })
            .with_cancellation(cancellation);

        let refusal = EngineSession::new()
            .analyze_checked(request)
            .expect_err("pre-cancelled analysis must fail closed");
        assert_eq!(refusal.phase, EnginePhase::SnapshotContext);
        assert!(refusal.reason.contains("cancelled before snapshot_context"));
        assert_eq!(refusal.metrics.phase_timings.len(), EnginePhase::ALL.len());
        assert!(
            refusal
                .metrics
                .phase_timings
                .iter()
                .all(|timing| timing.status == EnginePhaseStatus::Refused)
        );
        assert_eq!(
            refusal.diagnostics.refusal.as_deref(),
            Some(refusal.reason.as_str())
        );
    }

    #[test]
    fn decompile_expired_deadline_returns_actionable_refusal_without_c() {
        let deadline = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("deadline before now");
        let input = EngineFunctionDecompileRequestInput::single_function(
            EngineFunctionInput {
                function_name: "sym.expired".to_string(),
                function_addr: 0x401000,
                blocks: const_return_blocks(0x401000, 0),
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.expired/rev1")),
                semantic_metadata_enabled: false,
            },
            Some(64),
            r2types::ParsedExternalContext::default(),
        )
        .with_deadline(deadline);

        let response = EngineSession::new().decompile_function_from_input(input);
        assert!(
            response
                .output
                .contains("deadline exceeded before snapshot_context")
        );
        assert!(!response.output.contains("uint64_t sym_expired"));
        assert!(
            response
                .diagnostics
                .refusal
                .as_deref()
                .is_some_and(|reason| reason.contains("deadline exceeded"))
        );
        assert_eq!(response.metrics.phase_timings.len(), EnginePhase::ALL.len());
        assert!(
            response
                .metrics
                .phase_timings
                .iter()
                .all(|timing| timing.status == EnginePhaseStatus::Refused)
        );
    }

    #[test]
    fn cancellation_and_deadline_coexist_and_refuse_without_partial_c() {
        let cancellation = EngineCancellationToken::default();
        let deadline = Instant::now()
            .checked_add(Duration::from_secs(30))
            .expect("future deadline");
        let input = EngineFunctionDecompileRequestInput::single_function(
            EngineFunctionInput {
                function_name: "sym.combined".to_string(),
                function_addr: 0x401000,
                blocks: const_return_blocks(0x401000, 7),
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.combined/rev1")),
                semantic_metadata_enabled: false,
            },
            Some(64),
            r2types::ParsedExternalContext::default(),
        )
        .with_deadline(deadline)
        .with_cancellation(cancellation.clone());
        assert_eq!(input.execution.deadline(), Some(deadline));
        cancellation.cancel();

        let response = EngineSession::new().decompile_function_from_input(input);

        assert!(
            response
                .output
                .contains("cancelled before snapshot_context")
        );
        assert!(!response.output.contains("uint64_t sym_combined"));
    }

    #[test]
    fn engine_owns_public_guard_fallback_comments() {
        let block_comment = block_guard_fallback_comment("sym.big", 201, 200);
        assert!(block_comment.contains("r2dec budget"));
        assert!(block_comment.contains("sym.big"));
        assert!(block_comment.contains("201"));
        assert!(block_comment.contains("200"));

        let cfg_comment = cfg_guard_fallback_comment(
            "sym.loopy",
            &CFGRiskSummary {
                block_count: 107,
                loop_count: 9,
                back_edge_count: 17,
                switch_block_count: 0,
                max_switch_cases: 0,
            },
        )
        .expect("complex CFG should produce a guard fallback");
        assert!(cfg_comment.contains("r2dec fallback"));
        assert!(cfg_comment.contains("sym.loopy"));
        assert!(cfg_comment.contains("complex loop graph"));

        let hostile_name = "sym.*/\r\nint forged(void)";
        let hostile_reason = "budget */\nreturn 7";
        let hostile_comments = [
            block_guard_fallback_comment(hostile_name, 201, 200),
            artifact_guard_fallback_comment(hostile_name, hostile_reason),
        ];
        for comment in &hostile_comments {
            let body = comment
                .strip_suffix("*/")
                .expect("engine fallback must remain one closed comment");
            assert!(!body.contains("*/"), "comment closed early: {comment}");
            assert!(!comment.contains(['\r', '\n']));
            assert!(comment.contains("sym.* /  int forged(void)"));
        }
        assert!(hostile_comments[1].contains("budget * / return 7"));
    }

    #[test]
    fn decompile_probe_decision_guards_named_large_worker() {
        let mut blocks = const_return_blocks(0x4b30, 0);
        for idx in 0..210 {
            blocks.push(R2ILBlock::new(0x5000 + idx, 1));
        }
        let decision = decompile_probe_decision(&blocks);

        assert!(decision.summary_probe_needed);
        assert!(decision.summary_probe_skipped_large_cfg);
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

        let decision = decompile_probe_decision(&blocks);

        assert!(!decision.summary_probe_needed);
        assert!(!decision.summary_probe_skipped_large_cfg);
    }

    #[test]
    fn decompile_probe_decision_does_not_prefer_full_diagnostic_name_without_evidence() {
        let mut blocks = const_return_blocks(0x4bc0, 0);
        for idx in 0..ENGINE_DECOMPILE_MAX_OPS as u64 + 1 {
            blocks[0].push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x200 + idx, 8),
                src: r2il::Varnode::constant(idx, 8),
            });
        }

        let decision = decompile_probe_decision(&blocks);

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

        let at_limit = decompile_probe_decision(&exactly_limit);
        let over_limit = decompile_probe_decision(&over_limit);

        assert!(!at_limit.summary_probe_skipped_large_cfg);
        assert!(over_limit.summary_probe_skipped_large_cfg);
    }

    #[test]
    fn decompile_probe_decision_uses_strict_op_count_guard_boundary() {
        let mut exactly_limit = R2ILBlock::new(0x9000, 1);
        let mut over_limit = R2ILBlock::new(0xa000, 1);
        for idx in 0..ENGINE_DECOMPILE_MAX_OPS as u64 {
            exactly_limit.push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x10000 + idx, 8),
                src: r2il::Varnode::constant(idx, 8),
            });
            over_limit.push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x30000 + idx, 8),
                src: r2il::Varnode::constant(idx, 8),
            });
        }
        over_limit.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::unique(0x900, 8),
            src: r2il::Varnode::constant(0x900, 8),
        });

        let at_limit = decompile_probe_decision(&[exactly_limit]);
        let over_limit = decompile_probe_decision(&[over_limit]);

        assert!(!at_limit.summary_probe_skipped_large_cfg);
        assert!(over_limit.summary_probe_skipped_large_cfg);
    }

    #[test]
    fn decompile_complexity_caps_refuse_before_analysis_construction() {
        let over_blocks = (0..=ENGINE_DECOMPILE_MAX_BLOCKS)
            .map(|index| {
                R2ILBlock::new(0xb000 + u64::try_from(index).expect("small block index"), 1)
            })
            .collect::<Vec<_>>();
        let mut over_ops = R2ILBlock::new(0xc000, 1);
        for index in 0..=ENGINE_DECOMPILE_MAX_OPS {
            over_ops.push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(
                    0x100 + u64::try_from(index).expect("small operation index"),
                    8,
                ),
                src: r2il::Varnode::constant(
                    u64::try_from(index).expect("small operation index"),
                    8,
                ),
            });
        }

        for (name, addr, blocks) in [
            ("sym.over_blocks", 0xb000, over_blocks),
            ("sym.over_ops", 0xc000, vec![over_ops]),
        ] {
            let session = EngineSession::new();
            let response = session.decompile_function_from_input(
                EngineFunctionDecompileRequestInput::single_function(
                    EngineFunctionInput {
                        function_name: name.to_string(),
                        function_addr: addr,
                        blocks,
                        arch: None,
                        source_snapshot: Some(test_source_snapshot(&format!(
                            "{name}/decompile/rev1"
                        ))),
                        semantic_metadata_enabled: false,
                    },
                    Some(64),
                    r2types::ParsedExternalContext::default(),
                ),
            );
            assert!(
                response
                    .output
                    .contains("decompile complexity limit exceeded"),
                "{}",
                response.output
            );
            assert_eq!(
                response
                    .function_facts
                    .decompile_route()
                    .map(|route| route.kind),
                Some(r2types::DecompileRouteKind::FallbackComment)
            );
        }
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

        let decision = decompile_probe_decision(&blocks);

        assert!(!decision.summary_probe_skipped_large_cfg);
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
    }

    #[test]
    fn semantic_compile_does_not_prefer_name_only_worker_seed_before_full_semantics() {
        let blocks = const_return_blocks(0x8b50, 0);
        let ssa_func = Arc::new(
            r2ssa::SsaArtifact::for_decompile(&blocks, None)
                .expect("prepared ssa")
                .with_name("dbg.init_node"),
        );

        let artifact = compile_semantic_artifact_for_analysis(&ssa_func, None, None);

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
        let decision = decompile_probe_decision(&[entry]);

        assert!(should_probe_native_worker_summary_before_full_semantics(
            &loop_ssa, None
        ));
        assert!(decision.summary_probe_needed);
    }

    #[test]
    fn prefer_full_named_workers_need_evidence_before_decompile_preprobe() {
        let blocks = const_return_blocks(0x401000, 0);
        let decision = decompile_probe_decision(&blocks);

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
        let loop_ssa = Arc::new(
            r2ssa::SsaArtifact::for_decompile(&[entry], None)
                .expect("loop ssa")
                .with_name("dbg.loop_worker_without_summary"),
        );

        assert!(should_skip_unbounded_semantic_artifact_after_worker_preprobe(&loop_ssa, None));
        assert!(maybe_compile_semantic_artifact_for_analysis(&loop_ssa, None, None).is_none());
    }

    #[test]
    fn semantic_compile_keeps_vm_evidence_after_loop_preprobe() {
        let blocks = switch_loop_vm_blocks();
        let arch = vm_test_arch();
        let vm_ssa = Arc::new(
            r2ssa::SsaArtifact::for_decompile(&blocks, Some(&arch))
                .expect("vm ssa")
                .with_name("dbg.vm_loop_worker"),
        );

        assert!(should_probe_native_worker_summary_before_full_semantics(
            &vm_ssa, None
        ));
        assert!(
            r2sym::has_strong_vm_evidence(&vm_ssa),
            "test fixture must carry enough structural VM evidence to justify bypassing the refusal gate"
        );
        assert!(!should_skip_unbounded_semantic_artifact_after_worker_preprobe(&vm_ssa, None));

        let artifact = maybe_compile_semantic_artifact_for_analysis(&vm_ssa, None, None)
            .expect("vm artifact should not be refused before classification");

        assert_eq!(artifact.execution, r2sym::ExecutionModel::Vm);
        assert!(artifact.vm_body().is_some());
    }

    #[test]
    fn engine_owns_interproc_direct_call_target_collection() {
        let arch = windows_x64_runtime_scope_arch();
        let snapshot = test_source_snapshot("sym.wrapper/rev1");
        let analysis = build_engine_analysis_from_parts(
            "sym.wrapper",
            &direct_call_return_blocks(0x401000, 0x2000),
            Some(&arch),
            &snapshot,
        )
        .expect("analysis");

        assert_eq!(interproc_direct_call_targets(&analysis), vec![0x2000]);
    }

    fn small_interproc_target_metrics() -> EngineInterprocTargetMetrics {
        EngineInterprocTargetMetrics {
            basic_block_count: 1,
            cost: 1,
        }
    }

    fn oversized_interproc_target_metrics() -> EngineInterprocTargetMetrics {
        EngineInterprocTargetMetrics {
            basic_block_count: ENGINE_INTERPROC_HELPER_MAX_BLOCKS + 1,
            cost: 1,
        }
    }

    #[test]
    fn interproc_helper_scope_budget_is_engine_owned() {
        assert!(interproc_helper_scope_within_budget(
            ENGINE_INTERPROC_HELPER_MAX_BLOCKS,
            ENGINE_INTERPROC_HELPER_MAX_COST,
        ));
        assert!(!interproc_helper_scope_within_budget(
            ENGINE_INTERPROC_HELPER_MAX_BLOCKS + 1,
            ENGINE_INTERPROC_HELPER_MAX_COST,
        ));
        assert!(!interproc_helper_scope_within_budget(
            ENGINE_INTERPROC_HELPER_MAX_BLOCKS,
            ENGINE_INTERPROC_HELPER_MAX_COST + 1,
        ));
    }

    #[test]
    fn interproc_session_plan_owns_scope_and_budget_policy() {
        let policy = analysis_policy_for_depth(EngineAnalysisDepth::Default);
        let small = Some(small_interproc_target_metrics());
        let oversized = Some(oversized_interproc_target_metrics());

        let full_type =
            interproc_session_plan(policy, EngineInterprocSessionPurpose::TypeAnalysis, small);
        assert!(full_type.include_type_interproc_scope);
        assert!(!full_type.include_root_symbolic_scope);
        assert_eq!(full_type.interproc_iter, 1);
        assert_eq!(
            full_type.interproc_max_iters,
            policy.type_interproc_max_iters
        );
        assert!(full_type.interproc_converged);

        let bounded_type = interproc_session_plan(
            policy,
            EngineInterprocSessionPurpose::TypeAnalysis,
            oversized,
        );
        assert!(!bounded_type.include_type_interproc_scope);
        assert!(bounded_type.include_root_symbolic_scope);
        assert_eq!(bounded_type.interproc_iter, 1);
        assert_eq!(bounded_type.interproc_max_iters, 1);
        assert!(!bounded_type.interproc_converged);

        let full_decompile = interproc_session_plan(
            policy,
            EngineInterprocSessionPurpose::Decompile,
            Some(small_interproc_target_metrics()),
        );
        assert!(full_decompile.include_type_interproc_scope);
        assert!(!full_decompile.include_root_symbolic_scope);
        assert_eq!(full_decompile.interproc_max_iters, 1);
        assert!(full_decompile.interproc_converged);

        let bounded_decompile = interproc_session_plan(
            policy,
            EngineInterprocSessionPurpose::Decompile,
            Some(oversized_interproc_target_metrics()),
        );
        assert!(!bounded_decompile.include_type_interproc_scope);
        assert!(!bounded_decompile.include_root_symbolic_scope);
        assert_eq!(bounded_decompile.interproc_max_iters, 1);
        assert!(bounded_decompile.interproc_converged);
    }

    #[test]
    fn session_policy_plan_owns_budget_projection() {
        let policy = analysis_policy_for_depth(EngineAnalysisDepth::Aggressive);
        let plan = session_policy_plan(
            policy,
            EngineInterprocSessionPurpose::Decompile,
            Some(small_interproc_target_metrics()),
        );

        assert!(plan.interproc.include_type_interproc_scope);
        assert_eq!(plan.interproc.interproc_iter, 1);
        assert_eq!(plan.interproc.interproc_max_iters, 1);
        assert_eq!(plan.type_writeback_mode, policy.type_writeback_mode);
        assert_eq!(plan.global_max_links, policy.type_global_max_links);
        assert_eq!(plan.max_type_decls, policy.type_max_decls);
        assert_eq!(plan.max_mutations, policy.type_max_mutations);

        let bounded = session_policy_plan_for_radare2_depth(
            RADARE2_ANALYSIS_DEPTH_BASIC,
            EngineInterprocSessionPurpose::TypeAnalysis,
            Some(oversized_interproc_target_metrics()),
        );
        let basic_policy = analysis_policy_for_radare2_depth(RADARE2_ANALYSIS_DEPTH_BASIC);
        assert!(!bounded.interproc.include_type_interproc_scope);
        assert!(bounded.interproc.include_root_symbolic_scope);
        assert_eq!(
            bounded.type_writeback_mode,
            basic_policy.type_writeback_mode
        );
        assert_eq!(bounded.global_max_links, basic_policy.type_global_max_links);
        assert_eq!(bounded.max_type_decls, basic_policy.type_max_decls);
        assert_eq!(bounded.max_mutations, basic_policy.type_max_mutations);
    }

    #[test]
    fn session_budget_input_normalizes_limits_in_engine() {
        let budget = EngineSessionBudget::from_input(EngineSessionBudgetInput {
            interproc_iter: 0,
            interproc_max_iters: 0,
            interproc_converged: true,
            global_max_links: 0,
            max_type_decls: 0,
            max_mutations: 0,
            type_writeback_mode: EngineTypeWritebackMode::Balanced,
        });

        assert_eq!(budget.interproc_iter, 1);
        assert_eq!(budget.interproc_max_iters, 1);
        assert!(budget.interproc_converged);
        assert_eq!(budget.writeback_budget.global_max_links, 1);
        assert_eq!(budget.writeback_budget.max_type_decls, 1);
        assert_eq!(budget.writeback_budget.max_mutations, 1);
        assert_eq!(
            budget.writeback_apply_policy.mode,
            r2types::TypeWritebackApplyMode::Balanced
        );
    }

    #[test]
    fn interproc_scope_target_plan_keeps_plugin_out_of_import_policy() {
        let plan = interproc_scope_target_plan([
            EngineInterprocTargetInput {
                direct_target: 0x2000,
                name: Some("sym.imp.printf".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                semantic_summary: None,
                resolved_target: Some(0x2000),
                target_materialized: true,
                target_metrics: Some(small_interproc_target_metrics()),
            },
            EngineInterprocTargetInput {
                direct_target: 0x3000,
                name: Some("sym.imp.memcpy".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Imported,
                semantic_summary: None,
                resolved_target: Some(0x3000),
                target_materialized: true,
                target_metrics: Some(small_interproc_target_metrics()),
            },
        ]);

        assert_eq!(
            plan.queued_targets,
            vec![0x2000],
            "import-shaped names must not skip helper scope without typed import linkage"
        );
        let imported = plan
            .decisions
            .iter()
            .find(|decision| decision.direct_target == 0x3000)
            .expect("imported decision");
        assert_eq!(
            imported.skip_reason,
            Some(EngineInterprocTargetSkipReason::Imported)
        );
        assert!(
            plan.runtime_copy_targets.is_empty(),
            "an imported memcpy spelling is advisory without typed semantic summary evidence"
        );
    }

    #[test]
    fn interproc_scope_target_plan_reports_runtime_roles_and_thunks() {
        let runtime_copy_summary = r2sym::function_semantic_summary_seed_for_name_with_linkage(
            r2ssa::InterprocFunctionId(0x4200),
            "memcpy",
            r2ssa::FunctionSemanticLinkage::Imported,
        )
        .expect("typed memcpy summary");
        let plan = interproc_scope_target_plan([
            EngineInterprocTargetInput {
                direct_target: 0x4100,
                name: Some("sym.imp.AddVectoredExceptionHandler".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Imported,
                semantic_summary: None,
                resolved_target: Some(0x4100),
                target_materialized: true,
                target_metrics: Some(small_interproc_target_metrics()),
            },
            EngineInterprocTargetInput {
                direct_target: 0x4200,
                name: Some("sym.local_memcpy_thunk".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Internal,
                semantic_summary: Some(runtime_copy_summary),
                resolved_target: Some(0x4200),
                target_materialized: true,
                target_metrics: Some(small_interproc_target_metrics()),
            },
            EngineInterprocTargetInput {
                direct_target: 0x4300,
                name: Some("sym.local_thunk".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Internal,
                semantic_summary: None,
                resolved_target: Some(0x4310),
                target_materialized: true,
                target_metrics: Some(small_interproc_target_metrics()),
            },
        ]);

        assert!(
            plan.registration_targets.is_empty(),
            "registration names must refuse until a typed source role exists"
        );
        assert_eq!(plan.runtime_copy_targets, vec![0x4200]);
        assert_eq!(
            plan.queued_targets,
            vec![0x4300, 0x4310],
            "thunked direct targets queue both the direct wrapper and resolved target"
        );
        let summary = plan
            .decisions
            .iter()
            .find(|decision| decision.direct_target == 0x4200)
            .expect("summary decision");
        assert_eq!(
            summary.skip_reason,
            Some(EngineInterprocTargetSkipReason::SummaryModeled)
        );
    }

    #[test]
    fn interproc_scope_target_plan_rejects_name_only_runtime_roles() {
        let plan = interproc_scope_target_plan([
            EngineInterprocTargetInput {
                direct_target: 0x4400,
                name: Some("memcpy".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Internal,
                semantic_summary: None,
                resolved_target: Some(0x4400),
                target_materialized: true,
                target_metrics: Some(small_interproc_target_metrics()),
            },
            EngineInterprocTargetInput {
                direct_target: 0x4500,
                name: Some("sym.imp.AddVectoredExceptionHandler".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Imported,
                semantic_summary: None,
                resolved_target: Some(0x4500),
                target_materialized: true,
                target_metrics: Some(small_interproc_target_metrics()),
            },
        ]);

        assert!(
            plan.registration_targets.is_empty(),
            "even imported linkage plus a matching name is not a typed registration role"
        );
        assert!(
            plan.runtime_copy_targets.is_empty(),
            "runtime copy requires explicit modeled summary evidence"
        );
        assert_eq!(
            plan.queued_targets,
            vec![0x4400],
            "the internal helper queues normally; typed imported linkage skips the imported target without granting a runtime role"
        );
    }

    #[test]
    fn interproc_scope_target_plan_refuses_unmaterialized_and_over_budget_targets() {
        let plan = interproc_scope_target_plan([
            EngineInterprocTargetInput {
                direct_target: 0x5000,
                name: Some("sym.unmaterialized".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Internal,
                semantic_summary: None,
                resolved_target: None,
                target_materialized: false,
                target_metrics: None,
            },
            EngineInterprocTargetInput {
                direct_target: 0x6000,
                name: Some("sym.too_large".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Internal,
                semantic_summary: None,
                resolved_target: Some(0x6000),
                target_materialized: true,
                target_metrics: Some(oversized_interproc_target_metrics()),
            },
            EngineInterprocTargetInput {
                direct_target: 0x7000,
                name: Some("sym.unmeasured".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Internal,
                semantic_summary: None,
                resolved_target: Some(0x7000),
                target_materialized: true,
                target_metrics: None,
            },
        ]);

        assert!(plan.queued_targets.is_empty());
        assert_eq!(
            plan.decisions
                .iter()
                .map(|decision| decision.skip_reason)
                .collect::<Vec<_>>(),
            vec![
                Some(EngineInterprocTargetSkipReason::Unmaterialized),
                Some(EngineInterprocTargetSkipReason::OverBudget),
                Some(EngineInterprocTargetSkipReason::OverBudget),
            ]
        );
    }

    #[test]
    fn symbolic_scope_function_plan_owns_queue_admission_policy() {
        let allowed_interproc = EngineInterprocSessionPlan {
            include_type_interproc_scope: true,
            include_root_symbolic_scope: false,
            interproc_iter: 1,
            interproc_max_iters: 1,
            interproc_converged: true,
        };
        let disabled_interproc = EngineInterprocSessionPlan {
            include_type_interproc_scope: false,
            include_root_symbolic_scope: true,
            interproc_iter: 1,
            interproc_max_iters: 1,
            interproc_converged: false,
        };

        let root = symbolic_scope_function_plan(EngineSymbolicScopeFunctionInput {
            current_scope_count: 0,
            root_function: true,
            target_hint_function: false,
            interproc: disabled_interproc,
        });
        assert!(root.append_function);
        assert!(root.expand_targets);
        assert_eq!(root.reason, EngineSymbolicScopeFunctionReason::Allowed);

        let helper = symbolic_scope_function_plan(EngineSymbolicScopeFunctionInput {
            current_scope_count: 1,
            root_function: false,
            target_hint_function: false,
            interproc: allowed_interproc,
        });
        assert!(helper.append_function);
        assert!(helper.expand_targets);

        let target_terminal = symbolic_scope_function_plan(EngineSymbolicScopeFunctionInput {
            current_scope_count: 1,
            root_function: false,
            target_hint_function: true,
            interproc: disabled_interproc,
        });
        assert!(target_terminal.append_function);
        assert!(!target_terminal.expand_targets);
        assert_eq!(
            target_terminal.reason,
            EngineSymbolicScopeFunctionReason::TargetTerminal
        );

        let disabled = symbolic_scope_function_plan(EngineSymbolicScopeFunctionInput {
            current_scope_count: 1,
            root_function: false,
            target_hint_function: false,
            interproc: disabled_interproc,
        });
        assert!(!disabled.append_function);
        assert!(!disabled.expand_targets);
        assert_eq!(
            disabled.reason,
            EngineSymbolicScopeFunctionReason::InterprocDisabled
        );

        let full = symbolic_scope_function_plan(EngineSymbolicScopeFunctionInput {
            current_scope_count: SYMBOLIC_SCOPE_MAX_FUNCTIONS,
            root_function: true,
            target_hint_function: false,
            interproc: allowed_interproc,
        });
        assert!(!full.append_function);
        assert!(!full.expand_targets);
        assert_eq!(full.reason, EngineSymbolicScopeFunctionReason::ScopeFull);
    }

    #[test]
    fn runtime_materialized_source_plan_owns_caps() {
        let allowed = runtime_materialized_source_plan(0, 0x9000, 0x20);
        assert!(allowed.append_source);
        assert_eq!(allowed.capped_size, 0x20);
        assert_eq!(allowed.slot_bytes, RUNTIME_MATERIALIZED_SLOT_BYTES);
        assert_eq!(
            allowed.reason,
            EngineRuntimeMaterializedSourceReason::Allowed
        );

        let capped =
            runtime_materialized_source_plan(0, 0x9000, RUNTIME_MATERIALIZED_MAX_BYTES + 1);
        assert!(capped.append_source);
        assert_eq!(capped.capped_size, RUNTIME_MATERIALIZED_MAX_BYTES);

        let empty = runtime_materialized_source_plan(0, 0, 0x20);
        assert!(!empty.append_source);
        assert_eq!(
            empty.reason,
            EngineRuntimeMaterializedSourceReason::EmptySource
        );

        let full = runtime_materialized_source_plan(SYMBOLIC_SCOPE_MAX_FUNCTIONS, 0x9000, 0x20);
        assert!(!full.append_source);
        assert_eq!(
            full.reason,
            EngineRuntimeMaterializedSourceReason::ScopeFull
        );
    }

    #[test]
    fn engine_owns_windows_runtime_registration_scope_targets() {
        let arch = windows_x64_runtime_scope_arch();
        let mut block = R2ILBlock::new(0x5000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(8, 8),
            src: r2il::Varnode::constant(1, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(16, 8),
            src: r2il::Varnode::constant(0x1400_3d0f, 8),
        });
        block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(0x1800_1000, 8),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(0, 8),
        });
        let snapshot = windows_runtime_source_snapshot(
            "sym.runtime_seed/rev1",
            "ms",
            &[(0x5000, 2, 0x1800_1000, 2, true, "ms")],
        );
        let analysis =
            build_engine_analysis_from_parts("sym.runtime_seed", &[block], Some(&arch), &snapshot)
                .expect("analysis");

        assert_eq!(
            interproc_runtime_registration_targets(&analysis, &[0x1800_1000]),
            vec![0x1400_3d0f],
            "handler comes from the complete exact Microsoft x64 callsite observation"
        );
        assert!(
            interproc_runtime_registration_targets(&analysis, &[0x1800_2000]).is_empty(),
            "non-registration callees must not expand symbolic scope"
        );
    }

    #[test]
    fn runtime_registration_scope_refuses_absent_non_microsoft_or_incomplete_evidence() {
        let arch = windows_x64_runtime_scope_arch();
        let mut block = R2ILBlock::new(0x5000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(8, 8),
            src: r2il::Varnode::constant(1, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(16, 8),
            src: r2il::Varnode::constant(0x1400_3d0f, 8),
        });
        block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(0x1800_1000, 8),
        });
        let absent = test_source_snapshot("sym.runtime_seed/gated/absent/rev1");
        let absent_analysis = build_engine_analysis_from_parts(
            "sym.runtime_seed",
            &[block.clone()],
            Some(&arch),
            &absent,
        )
        .expect("analysis without ABI authority");
        assert!(
            interproc_runtime_registration_targets(&absent_analysis, &[0x1800_1000]).is_empty(),
            "absent source ABI authority must refuse runtime scope expansion"
        );

        let system_v = windows_runtime_source_snapshot(
            "sym.runtime_seed/gated/system-v/rev1",
            "amd64",
            &[(0x5000, 2, 0x1800_1000, 2, true, "ms")],
        );
        let system_v_analysis = build_engine_analysis_from_parts(
            "sym.runtime_seed",
            &[block.clone()],
            Some(&arch),
            &system_v,
        )
        .expect("System V analysis");
        assert!(
            interproc_runtime_registration_targets(&system_v_analysis, &[0x1800_1000]).is_empty(),
            "an exact System V ABI must not enable Microsoft runtime policy"
        );

        let incomplete = windows_runtime_source_snapshot(
            "sym.runtime_seed/gated/incomplete/rev1",
            "ms",
            &[(0x5000, 2, 0x1800_1000, 2, false, "ms")],
        );
        let incomplete_analysis = build_engine_analysis_from_parts(
            "sym.runtime_seed",
            &[block.clone()],
            Some(&arch),
            &incomplete,
        )
        .expect("incomplete-callsite analysis");
        assert!(
            interproc_runtime_registration_targets(&incomplete_analysis, &[0x1800_1000]).is_empty(),
            "an incomplete callsite must refuse otherwise exact arguments"
        );

        let unknown_callsite_abi = windows_runtime_source_snapshot(
            "sym.runtime_seed/gated/unknown-callsite-abi/rev1",
            "ms",
            &[(0x5000, 2, 0x1800_1000, 2, true, "default")],
        );
        let unknown_callsite_abi_analysis = build_engine_analysis_from_parts(
            "sym.runtime_seed",
            &[block],
            Some(&arch),
            &unknown_callsite_abi,
        )
        .expect("unknown-callsite-ABI analysis");
        assert!(
            interproc_runtime_registration_targets(&unknown_callsite_abi_analysis, &[0x1800_1000])
                .is_empty(),
            "an unknown callsite ABI must not inherit the function ABI"
        );

        let mut unknown_argument_block = R2ILBlock::new(0x5100, 4);
        unknown_argument_block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(16, 8),
            src: r2il::Varnode::constant(0x1400_3d0f, 8),
        });
        unknown_argument_block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(0x1800_1000, 8),
        });
        let unknown_argument = windows_runtime_source_snapshot(
            "sym.runtime_seed/gated/unknown-argument/rev1",
            "ms",
            &[(0x5100, 1, 0x1800_1000, 2, true, "ms")],
        );
        let unknown_argument_analysis = build_engine_analysis_from_parts(
            "sym.runtime_seed",
            &[unknown_argument_block],
            Some(&arch),
            &unknown_argument,
        )
        .expect("unknown-argument analysis");
        assert!(
            interproc_runtime_registration_targets(&unknown_argument_analysis, &[0x1800_1000])
                .is_empty(),
            "one unknown observed argument invalidates the complete call observation"
        );
    }

    #[test]
    fn engine_owns_runtime_materialized_source_collection() {
        let arch = windows_x64_runtime_scope_arch();
        let mut block = R2ILBlock::new(0x6000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(8, 8),
            src: r2il::Varnode::constant(0x7000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(16, 8),
            src: r2il::Varnode::constant(0x9000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(24, 8),
            src: r2il::Varnode::constant(0x20, 8),
        });
        block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(0x1800_2000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(8, 8),
            src: r2il::Varnode::constant(0x7000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(16, 8),
            src: r2il::Varnode::constant(0x9000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(24, 8),
            src: r2il::Varnode::constant(0x40, 8),
        });
        block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(0x1800_2000, 8),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(0, 8),
        });
        let snapshot = windows_runtime_source_snapshot(
            "sym.runtime_copy/rev1",
            "ms",
            &[
                (0x6000, 3, 0x1800_2000, 3, true, "ms"),
                (0x6000, 7, 0x1800_2000, 3, true, "ms"),
            ],
        );
        let analysis =
            build_engine_analysis_from_parts("sym.runtime_copy", &[block], Some(&arch), &snapshot)
                .expect("analysis");

        assert_eq!(
            interproc_runtime_materialized_sources(&analysis, &[0x1800_2000]),
            vec![EngineRuntimeMaterializedSource {
                addr: 0x9000,
                size: 0x40
            }],
            "duplicate copy observations must collapse to the maximum materialized size"
        );
    }

    #[test]
    fn runtime_materialized_sources_reject_non_code_and_zero_size_inputs() {
        let arch = windows_x64_runtime_scope_arch();
        let mut block = R2ILBlock::new(0x6000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(8, 8),
            src: r2il::Varnode::constant(0x7000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(16, 8),
            src: r2il::Varnode::constant(0x900, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(24, 8),
            src: r2il::Varnode::constant(0x20, 8),
        });
        block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(0x1800_2000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(8, 8),
            src: r2il::Varnode::constant(0x7000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(16, 8),
            src: r2il::Varnode::constant(0x9000, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(24, 8),
            src: r2il::Varnode::constant(0, 8),
        });
        block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(0x1800_2000, 8),
        });
        let snapshot = windows_runtime_source_snapshot(
            "sym.runtime_copy/rejected/rev1",
            "ms",
            &[
                (0x6000, 3, 0x1800_2000, 3, true, "ms"),
                (0x6000, 7, 0x1800_2000, 3, true, "ms"),
            ],
        );
        let analysis =
            build_engine_analysis_from_parts("sym.runtime_copy", &[block], Some(&arch), &snapshot)
                .expect("analysis");

        assert!(
            interproc_runtime_materialized_sources(&analysis, &[0x1800_2000]).is_empty(),
            "runtime materialization needs both a code-like source address and a nonzero size"
        );
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
        let cfg_summary = r2ssa::CFGRiskSummary {
            block_count: 200,
            loop_count: 8,
            back_edge_count: 12,
            switch_block_count: 0,
            max_switch_cases: 0,
        };
        let function_facts = FunctionFacts::default();

        assert_eq!(
            type_route_decision(&function_facts, &cfg_summary, false).kind,
            EngineTypeRouteKind::FullWriteback
        );
    }

    #[test]
    fn external_layout_names_rewrite_placeholder_field_certificates() {
        let signature = r2types::FunctionSignatureSpec {
            ret_type: None,
            params: vec![r2types::FunctionParamSpec {
                name: "arg0".to_string(),
                ty: Some(r2types::CTypeLike::Pointer(Box::new(
                    r2types::CTypeLike::Struct("DemoStruct".to_string()),
                ))),
            }],
        };
        let type_facts = FunctionTypeFacts {
            merged_signature: Some(signature),
            external_type_db: r2types::ExternalTypeDb {
                structs: HashMap::from([(
                    "demostruct".to_string(),
                    r2types::ExternalStruct {
                        name: "DemoStruct".to_string(),
                        fields: BTreeMap::from([(
                            48,
                            r2types::ExternalField {
                                name: "thirteenth".to_string(),
                                offset: 48,
                                ty: Some("int32_t".to_string()),
                            },
                        )]),
                    },
                )]),
                ..r2types::ExternalTypeDb::default()
            },
            field_access_certificates: vec![r2types::FieldAccessCertificate {
                slot: 0,
                field_offset: 48,
                field_name: "f_30".to_string(),
                field_type: None,
            }],
            ..FunctionTypeFacts::default()
        };
        let mut facts = FunctionFacts::new(type_facts, None);

        facts.normalize_field_certificates_from_external_layout();

        assert_eq!(
            facts.type_facts().field_access_certificates[0].field_name,
            "thirteenth"
        );
        assert_eq!(
            facts.type_facts().field_access_certificates[0]
                .field_type
                .as_deref(),
            Some("int32_t")
        );
    }

    #[test]
    fn type_function_refuses_large_name_only_summary_preprobe() {
        let mut blocks = const_return_blocks(0x55a0, 0);
        for idx in 0..210 {
            blocks.push(R2ILBlock::new(0x5600 + idx, 1));
        }
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.type_function(EngineTypeAnalysisRequest {
            analysis: EngineAnalyzeRequest {
                function_name: "dbg.main".to_string(),
                function_addr: 0x55a0,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("dbg.main/type/rev1")),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                interproc_max_iterations: 1,
                symbolic_scope: None,
                semantic_mode: EngineSemanticMode::Full,
                include_interproc_summary_set: true,
                execution: EngineExecutionControl::default(),
            },
            caller_prefers_bounded_type_plan: false,
        });

        assert!(
            response.is_none(),
            "a large name-only fixture has no prepared semantic owner to authorize a summary route"
        );
    }

    #[test]
    fn type_function_report_payload_refuses_name_only_summary_projection() {
        let mut blocks = const_return_blocks(0x55a0, 0);
        for idx in 0..210 {
            blocks.push(R2ILBlock::new(0x5600 + idx, 1));
        }
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let payload = session.type_function_report_payload(EngineFunctionAnalysisReportRequest {
            analysis: EngineAnalyzeRequest {
                function_name: "dbg.main".to_string(),
                function_addr: 0x55a0,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("dbg.main/report/rev1")),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                interproc_max_iterations: 1,
                symbolic_scope: None,
                semantic_mode: EngineSemanticMode::Full,
                include_interproc_summary_set: true,
                execution: EngineExecutionControl::default(),
            },
            interproc_max_iters: 1,
            interproc_converged: false,
            writeback_budget: r2types::TypeWritebackMutationBudget::new(1, 1, 1),
            writeback_apply_policy: type_writeback_apply_policy_for_mode(
                EngineTypeWritebackMode::Off,
            ),
        });

        assert!(
            payload.is_none(),
            "report projection cannot promote a name-only preprobe into semantic authority"
        );
    }

    #[test]
    fn function_analysis_report_request_builder_owns_analysis_policy() {
        let request = EngineFunctionAnalysisReportRequest::full_semantics_for_function(
            EngineFunctionAnalysisReportRequestInput {
                function: EngineFunctionInput {
                    function_name: "dbg.session".to_string(),
                    function_addr: 0x55a0,
                    blocks: Vec::new(),
                    arch: None,
                    source_snapshot: Some(test_source_snapshot("dbg.session/rev1")),
                    semantic_metadata_enabled: false,
                },
                ptr_bits: Some(64),
                parsed_context: r2types::ParsedExternalContext::default(),
                interproc_max_iters: 5,
                interproc_converged: true,
                symbolic_scope: None,
                writeback_budget: r2types::TypeWritebackMutationBudget::new(7, 11, 13),
                writeback_apply_policy: type_writeback_apply_policy_for_mode(
                    EngineTypeWritebackMode::Balanced,
                ),
            },
        );

        assert_eq!(request.analysis.function_name, "dbg.session");
        assert_eq!(request.analysis.function_addr, 0x55a0);
        assert_eq!(request.analysis.ptr_bits, 64);
        assert_eq!(request.analysis.semantic_mode, EngineSemanticMode::Full);
        assert!(request.analysis.include_interproc_summary_set);
        assert_eq!(request.analysis.interproc_max_iterations, 5);
        assert_eq!(request.interproc_max_iters, 5);
        assert!(request.interproc_converged);
        assert_eq!(request.writeback_budget.global_max_links, 7);
        assert_eq!(request.writeback_budget.max_type_decls, 11);
        assert_eq!(request.writeback_budget.max_mutations, 13);
    }

    #[test]
    fn function_analysis_artifact_request_builder_owns_analysis_policy() {
        let request = EngineFunctionAnalysisArtifactRequest::full_semantics_for_function(
            EngineFunctionAnalysisArtifactRequestInput {
                function: EngineFunctionInput {
                    function_name: "dbg.artifact".to_string(),
                    function_addr: 0x6600,
                    blocks: Vec::new(),
                    arch: None,
                    source_snapshot: Some(test_source_snapshot("dbg.artifact/rev1")),
                    semantic_metadata_enabled: false,
                },
                ptr_bits: Some(64),
                parsed_context: r2types::ParsedExternalContext::default(),
                interproc_max_iterations: 9,
                symbolic_scope: None,
            },
        );

        assert_eq!(request.analysis.function_name, "dbg.artifact");
        assert_eq!(request.analysis.function_addr, 0x6600);
        assert_eq!(request.analysis.ptr_bits, 64);
        assert_eq!(request.analysis.semantic_mode, EngineSemanticMode::Full);
        assert!(request.analysis.include_interproc_summary_set);
        assert_eq!(request.analysis.interproc_max_iterations, 9);
        assert!(
            request.analysis.reg_type_hints.is_empty(),
            "request builder owns default register-hint policy"
        );
    }

    #[test]
    fn decompile_function_uses_engine_summary_preprobe_without_plugin_policy() {
        let blocks = const_return_blocks(0x401000, 0);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function(EngineFunctionDecompileRequest {
            input_quality: None,
            analysis: EngineAnalyzeRequest {
                function_name: "dbg.init_node".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("dbg.init_node/rev1")),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                interproc_max_iterations: 1,
                symbolic_scope: None,
                semantic_mode: EngineSemanticMode::Full,
                include_interproc_summary_set: true,
                execution: EngineExecutionControl::default(),
            },
        });

        assert!(response.output.contains("init_node"));
        let route = response
            .function_facts
            .decompile_route()
            .expect("decompile response should carry FunctionFacts route");
        assert_ne!(route.kind, r2types::DecompileRouteKind::SummaryIslands);
    }

    #[test]
    fn decompile_function_from_input_refuses_incomplete_lifted_function() {
        let blocks = const_return_blocks(0x401000, 0);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function_from_input(EngineFunctionDecompileRequestInput {
            function: EngineFunctionInput {
                function_name: "sym.partial".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.partial/rev1")),
                semantic_metadata_enabled: false,
            },
            ptr_bits: Some(64),
            parsed_context,
            interproc_max_iterations: 1,
            symbolic_scope: None,
            input_quality: EngineFunctionInputQuality {
                expected_blocks: 2,
                lifted_blocks: 1,
                read_failures: 1,
                invalid_blocks: 0,
                null_lift_failures: 0,
                truncated_blocks: 0,
            },
            execution: EngineExecutionControl::default(),
            trusted_ssa: None,
            trusted_callees: Vec::new(),
        });

        assert!(
            response.output.contains("incomplete lifted function input"),
            "{}",
            response.output
        );
        let route = response
            .function_facts
            .decompile_route()
            .expect("refusal route must travel through FunctionFacts");
        assert_eq!(route.kind, r2types::DecompileRouteKind::FallbackComment);
        assert!(
            route
                .fallback_comment
                .as_deref()
                .is_some_and(|comment| comment.contains("read_failures=1")),
            "{route:?}"
        );
        assert_eq!(
            response.diagnostics.refusal,
            route.fallback_comment.clone(),
            "engine diagnostics must derive refusal from FunctionFacts route"
        );
        let quality = response
            .input_quality
            .as_ref()
            .expect("input quality must remain response-local");
        assert_eq!(quality.expected_blocks, 2);
        assert_eq!(quality.lifted_blocks, 1);
        assert_eq!(quality.actual_lifted_blocks, 1);
        assert_eq!(quality.read_failures, 1);
        assert_eq!(
            quality.refusal_reason.as_deref(),
            Some(
                "incomplete lifted function input: expected_blocks=2 lifted_blocks=1 read_failures=1 invalid_blocks=0 null_lift_failures=0 truncated_blocks=0"
            )
        );
    }

    #[test]
    fn decompile_function_from_input_refuses_inconsistent_lift_quality() {
        let blocks = const_return_blocks(0x401000, 0);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function_from_input(EngineFunctionDecompileRequestInput {
            function: EngineFunctionInput {
                function_name: "sym.inconsistent".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.inconsistent/rev1")),
                semantic_metadata_enabled: false,
            },
            ptr_bits: Some(64),
            parsed_context,
            interproc_max_iterations: 1,
            symbolic_scope: None,
            input_quality: EngineFunctionInputQuality::complete(2),
            execution: EngineExecutionControl::default(),
            trusted_ssa: None,
            trusted_callees: Vec::new(),
        });

        assert!(
            response
                .output
                .contains("inconsistent lifted function input"),
            "{}",
            response.output
        );
        assert!(response.output.contains("actual_lifted_blocks=1"));
        let route = response
            .function_facts
            .decompile_route()
            .expect("refusal route must travel through FunctionFacts");
        assert_eq!(route.kind, r2types::DecompileRouteKind::FallbackComment);
        assert_eq!(response.diagnostics.refusal, route.fallback_comment.clone());
        let quality = response
            .input_quality
            .as_ref()
            .expect("input quality must remain response-local");
        assert_eq!(quality.expected_blocks, 2);
        assert_eq!(quality.lifted_blocks, 2);
        assert_eq!(quality.actual_lifted_blocks, 1);
        assert!(
            quality
                .refusal_reason
                .as_deref()
                .is_some_and(|reason| reason.contains("actual_lifted_blocks=1")),
            "{quality:?}"
        );
    }

    #[test]
    fn decompile_function_from_input_refuses_zero_lifted_function() {
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function_from_input(EngineFunctionDecompileRequestInput {
            function: EngineFunctionInput {
                function_name: "sym.all_failed".to_string(),
                function_addr: 0x401000,
                blocks: Vec::new(),
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.all_failed/rev1")),
                semantic_metadata_enabled: false,
            },
            ptr_bits: Some(64),
            parsed_context,
            interproc_max_iterations: 1,
            symbolic_scope: None,
            input_quality: EngineFunctionInputQuality {
                expected_blocks: 1,
                lifted_blocks: 0,
                read_failures: 0,
                invalid_blocks: 0,
                null_lift_failures: 1,
                truncated_blocks: 0,
            },
            execution: EngineExecutionControl::default(),
            trusted_ssa: None,
            trusted_callees: Vec::new(),
        });

        assert!(
            response.output.contains("empty lifted function input"),
            "{}",
            response.output
        );
        assert!(response.output.contains("null_lift_failures=1"));
        let route = response
            .function_facts
            .decompile_route()
            .expect("refusal route must travel through FunctionFacts");
        assert_eq!(route.kind, r2types::DecompileRouteKind::FallbackComment);
        assert_eq!(response.diagnostics.refusal, route.fallback_comment.clone());
        let quality = response
            .input_quality
            .as_ref()
            .expect("input quality must remain response-local");
        assert_eq!(quality.expected_blocks, 1);
        assert_eq!(quality.lifted_blocks, 0);
        assert_eq!(quality.actual_lifted_blocks, 0);
        assert_eq!(quality.null_lift_failures, 1);
        assert!(
            quality
                .refusal_reason
                .as_deref()
                .is_some_and(|reason| reason.contains("empty lifted function input")),
            "{quality:?}"
        );
    }

    #[test]
    fn decompile_function_from_input_refuses_zero_expected_blocks() {
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function_from_input(EngineFunctionDecompileRequestInput {
            function: EngineFunctionInput {
                function_name: "sym.empty".to_string(),
                function_addr: 0x401000,
                blocks: Vec::new(),
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.empty/rev1")),
                semantic_metadata_enabled: false,
            },
            ptr_bits: Some(64),
            parsed_context,
            interproc_max_iterations: 1,
            symbolic_scope: None,
            input_quality: EngineFunctionInputQuality::complete(0),
            execution: EngineExecutionControl::default(),
            trusted_ssa: None,
            trusted_callees: Vec::new(),
        });

        assert!(
            response.output.contains("empty lifted function input"),
            "{}",
            response.output
        );
        assert!(response.output.contains("expected_blocks=0"));
        let route = response
            .function_facts
            .decompile_route()
            .expect("refusal route must travel through FunctionFacts");
        assert_eq!(route.kind, r2types::DecompileRouteKind::FallbackComment);
        assert_eq!(response.diagnostics.refusal, route.fallback_comment.clone());
        let quality = response
            .input_quality
            .as_ref()
            .expect("input quality must remain response-local");
        assert_eq!(quality.expected_blocks, 0);
        assert_eq!(quality.lifted_blocks, 0);
        assert_eq!(quality.actual_lifted_blocks, 0);
        assert!(
            quality
                .refusal_reason
                .as_deref()
                .is_some_and(|reason| reason.contains("expected_blocks=0")),
            "{quality:?}"
        );
    }

    #[test]
    fn decompile_function_from_input_attaches_complete_input_quality() {
        let blocks = const_return_blocks(0x401000, 0);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function_from_input(EngineFunctionDecompileRequestInput {
            function: EngineFunctionInput {
                function_name: "sym.complete".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.complete/rev1")),
                semantic_metadata_enabled: false,
            },
            ptr_bits: Some(64),
            parsed_context,
            interproc_max_iterations: 1,
            symbolic_scope: None,
            input_quality: EngineFunctionInputQuality::complete(1),
            execution: EngineExecutionControl::default(),
            trusted_ssa: None,
            trusted_callees: Vec::new(),
        });

        let quality = response
            .input_quality
            .as_ref()
            .expect("complete input quality must remain response-local");
        assert!(quality.is_complete(), "{quality:?}");
        assert_eq!(quality.expected_blocks, 1);
        assert_eq!(quality.lifted_blocks, 1);
        assert_eq!(quality.actual_lifted_blocks, 1);
        assert_eq!(quality.refusal_reason, None);
    }

    #[test]
    fn decompile_function_refuses_incomplete_optional_input_quality() {
        let blocks = const_return_blocks(0x401000, 0);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function(EngineFunctionDecompileRequest {
            input_quality: Some(EngineFunctionInputQuality {
                expected_blocks: 2,
                lifted_blocks: 1,
                read_failures: 1,
                invalid_blocks: 0,
                null_lift_failures: 0,
                truncated_blocks: 0,
            }),
            analysis: EngineAnalyzeRequest {
                function_name: "sym.direct_partial".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.direct_partial/rev1")),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                interproc_max_iterations: 1,
                symbolic_scope: None,
                semantic_mode: EngineSemanticMode::Full,
                include_interproc_summary_set: true,
                execution: EngineExecutionControl::default(),
            },
        });

        assert!(
            response.output.contains("incomplete lifted function input"),
            "{}",
            response.output
        );
        let route = response
            .function_facts
            .decompile_route()
            .expect("refusal route must travel through FunctionFacts");
        assert_eq!(route.kind, r2types::DecompileRouteKind::FallbackComment);
        let quality = response
            .input_quality
            .as_ref()
            .expect("direct decompile refusal must retain input quality");
        assert_eq!(quality.expected_blocks, 2);
        assert_eq!(quality.lifted_blocks, 1);
        assert_eq!(quality.actual_lifted_blocks, 1);
        assert_eq!(quality.read_failures, 1);
        assert!(quality.refusal_reason.is_some());
    }

    #[test]
    fn decompile_function_uses_canonical_display_identity_without_raw_payloads() {
        let blocks = const_return_blocks(0x401000, 0);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function(EngineFunctionDecompileRequest {
            input_quality: None,
            analysis: EngineAnalyzeRequest {
                function_name: "dbg.raw_name".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("dbg.raw_name/rev1")),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                interproc_max_iterations: 1,
                symbolic_scope: None,
                semantic_mode: EngineSemanticMode::Full,
                include_interproc_summary_set: true,
                execution: EngineExecutionControl::default(),
            },
        });

        assert!(
            !response.output.contains("rendered_name"),
            "decompile display identity must come from canonical analysis input: {}",
            response.output
        );
        assert!(
            response.output.contains("raw_name"),
            "canonical analysis name must remain the r2engine display identity: {}",
            response.output
        );
        let route = response
            .function_facts
            .decompile_route()
            .expect("decompile response should carry FunctionFacts route");
        assert_ne!(route.kind, r2types::DecompileRouteKind::SummaryIslands);
    }

    #[test]
    fn decompile_function_does_not_invent_raw_payload_callee_names() {
        let blocks = direct_call_return_blocks(0x401000, 0x5000);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function(EngineFunctionDecompileRequest {
            input_quality: None,
            analysis: EngineAnalyzeRequest {
                function_name: "sym.caller".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.caller/rev1")),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                interproc_max_iterations: 1,
                symbolic_scope: None,
                semantic_mode: EngineSemanticMode::Full,
                include_interproc_summary_set: true,
                execution: EngineExecutionControl::default(),
            },
        });

        assert!(
            !response.output.contains("printf"),
            "uncertified raw callee names must not appear in rendered calls: {}",
            response.output
        );
        assert!(
            !response
                .function_facts
                .type_facts()
                .known_function_signatures
                .contains_key("printf"),
            "uncertified raw callee names must not seed FunctionFacts signatures"
        );
    }

    #[test]
    fn decompile_function_does_not_invent_raw_payload_strings() {
        let blocks = const_return_blocks(0x401000, 0x6000);
        let parsed_context = r2types::parse_external_context_json("{}", 64);
        let session = EngineSession::new();

        let response = session.decompile_function(EngineFunctionDecompileRequest {
            input_quality: None,
            analysis: EngineAnalyzeRequest {
                function_name: "sym.string_const".to_string(),
                function_addr: 0x401000,
                blocks,
                arch: None,
                source_snapshot: Some(test_source_snapshot("sym.string_const/rev1")),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
                ptr_bits: 64,
                semantic_metadata_enabled: false,
                reg_type_hints: HashMap::new(),
                parsed_context,
                interproc_max_iterations: 1,
                symbolic_scope: None,
                semantic_mode: EngineSemanticMode::Full,
                include_interproc_summary_set: true,
                execution: EngineExecutionControl::default(),
            },
        });

        assert!(
            !response.output.contains("raw string payload"),
            "uncertified raw strings must not render as string literals: {}",
            response.output
        );
    }

    #[test]
    fn decompile_request_builder_owns_analysis_policy() {
        let request = EngineFunctionDecompileRequest::full_semantics_for_function(
            EngineFunctionDecompileRequestInput {
                function: EngineFunctionInput {
                    function_name: "sym.demo".to_string(),
                    function_addr: 0x401000,
                    blocks: Vec::new(),
                    arch: None,
                    source_snapshot: Some(test_source_snapshot("sym.demo/rev1")),
                    semantic_metadata_enabled: false,
                },
                ptr_bits: Some(64),
                parsed_context: r2types::ParsedExternalContext::default(),
                interproc_max_iterations: 3,
                symbolic_scope: None,
                input_quality: EngineFunctionInputQuality::complete(0),
                execution: EngineExecutionControl::default(),
                trusted_ssa: None,
                trusted_callees: Vec::new(),
            },
        );

        assert_eq!(request.analysis.function_name, "sym.demo");
        assert_eq!(request.analysis.function_addr, 0x401000);
        assert_eq!(request.analysis.ptr_bits, 64);
        assert_eq!(request.analysis.semantic_mode, EngineSemanticMode::Full);
        assert!(request.analysis.include_interproc_summary_set);
        assert_eq!(request.analysis.interproc_max_iterations, 3);
    }

    #[test]
    fn engine_plan_maps_routes_to_work_levels() {
        let route = test_decompile_route(
            r2types::DecompileRouteKind::SummaryIslands,
            Some("summary"),
            None,
        );
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
    fn semantic_route_reason_preserves_exact_engine_route_reason() {
        for (route, expected) in [
            (
                test_decompile_route(
                    r2types::DecompileRouteKind::StructuredWorker,
                    Some("structured proof"),
                    None,
                ),
                Some("structured proof".to_string()),
            ),
            (
                test_decompile_route(
                    r2types::DecompileRouteKind::SummaryIslands,
                    Some("summary islands"),
                    None,
                ),
                Some("summary islands".to_string()),
            ),
            (
                test_decompile_route(
                    r2types::DecompileRouteKind::LinearWorker,
                    Some("linear worker"),
                    None,
                ),
                Some("linear worker".to_string()),
            ),
            (
                test_decompile_route(
                    r2types::DecompileRouteKind::VmSummary,
                    Some("vm summary"),
                    None,
                ),
                Some("vm summary".to_string()),
            ),
            (
                test_decompile_route(
                    r2types::DecompileRouteKind::FallbackComment,
                    Some("fallback comment"),
                    Some("fallback comment"),
                ),
                Some("fallback comment".to_string()),
            ),
            (
                test_decompile_route(r2types::DecompileRouteKind::Standard, None, None),
                None,
            ),
        ] {
            assert_eq!(semantic_route_reason(&route), expected);
        }
    }

    #[test]
    fn request_plans_cover_decompile_and_types() {
        let blocks = const_return_blocks(0x3010, 0);
        let prepared = r2ssa::SsaArtifact::for_decompile(&blocks, None).expect("prepared");
        let cfg_summary = prepared.function().cfg_risk_summary();
        let function_facts = FunctionFacts::default();

        let decompile =
            plan_decompile_request("sym.simple", &function_facts, Some(&prepared), &cfg_summary);
        assert_eq!(decompile.request(), EngineRequestKind::Decompile);
        assert_eq!(decompile.engine_plan(), EnginePlan::FastLocal);
        assert_eq!(decompile.diagnostics().plan, Some(EnginePlan::FastLocal));

        let types = plan_type_request(&function_facts, &cfg_summary, false);
        assert_eq!(types.request(), EngineRequestKind::Types);
        assert_eq!(types.engine_plan(), EnginePlan::PreparedOnly);
    }

    #[test]
    fn symbolic_scope_seed_uses_exact_prepared_abi_without_main_name_authority() {
        let arch = windows_x64_runtime_scope_arch();
        let mut block = R2ILBlock::new(0x401000, 4);
        for (unique, register) in [(0x10, 8), (0x20, 16), (0x30, 24), (0x40, 48)] {
            block.push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(unique, 8),
                src: runtime_reg(register, 8),
            });
        }
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::constant(0, 8),
        });
        let revision = b"main-exact-symbolic-seed".to_vec();
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let function_interface = r2ssa::SourceFunctionInterface::new_exact(
            revision.clone(),
            "ms",
            [8, 16, 24].into_iter().enumerate().map(|(index, offset)| {
                r2ssa::SourceAbiParameterSpec::new(index as u32, storage(offset))
            }),
            r2ssa::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(40)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(48)))
        .expect("exact symbolic seed interface");
        let snapshot = EngineSourceSnapshot::new(revision, Some(function_interface), [])
            .expect("exact symbolic seed snapshot");
        let analysis = build_engine_analysis_from_parts("main", &[block], Some(&arch), &snapshot)
            .expect("exact symbolic seed analysis");
        let prepared = Arc::clone(&analysis.ssa_func);
        let scope = r2sym::PreparedFunctionScope::new(
            prepared.entry,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(prepared.entry),
                name: Some("main".to_string()),
                prepared: Arc::clone(&prepared),
            }],
        )
        .expect("exact symbolic scope");
        let z3_ctx = z3::Context::thread_local();
        let symbols = r2sym::FunctionSymbolSnapshot::default();
        let context = EngineSymbolicContextRequest {
            z3_ctx: &z3_ctx,
            prepared: &prepared,
            scope: Some(&scope),
            arch: Some(&arch),
            symbols: &symbols,
            merge_states: false,
            config_profile: EngineSymbolicConfigProfile::DefaultQuery,
            seed: EngineSymbolicStateSeed::Scope {
                entry_addr: prepared.entry,
            },
        };

        let state = symbolic_initial_state(&context).expect("exact scope seed");
        let register = |prefix: &str| {
            state
                .registers()
                .iter()
                .find(|(name, _)| name.to_ascii_lowercase().starts_with(prefix))
                .map(|(_, value)| value)
                .unwrap_or_else(|| {
                    panic!(
                        "exact ABI register {prefix:?} must be seeded; got {:?}",
                        state.registers().keys().collect::<Vec<_>>()
                    )
                })
        };
        assert!(register("rcx_").is_symbolic());
        assert!(register("rdx_").is_symbolic());
        assert!(register("r8_").is_symbolic());
        assert!(register("rsp_").as_concrete().is_some());
        assert!(
            register("rdx_").as_concrete().is_none(),
            "the spelling main must not authorize synthetic argv construction"
        );

        let rejected_replay = r2sym::ReplaySeed {
            registers: vec![r2sym::ReplayRegisterValue {
                name: "UNDECLARED_REGISTER".to_string(),
                value: 0xdead_beef,
            }],
            ..r2sym::ReplaySeed::default()
        };
        let replay_context = EngineSymbolicContextRequest {
            z3_ctx: &z3_ctx,
            prepared: &prepared,
            scope: Some(&scope),
            arch: Some(&arch),
            symbols: &symbols,
            merge_states: false,
            config_profile: EngineSymbolicConfigProfile::DefaultQuery,
            seed: EngineSymbolicStateSeed::Replay {
                entry_addr: prepared.entry,
                seed: &rejected_replay,
            },
        };
        assert!(matches!(
            symbolic_initial_state(&replay_context),
            Err(EngineSymbolicRequestError::ReplaySeed(
                r2sym::PreparedReplaySeedError::UnknownRegister(name)
            )) if name == "UNDECLARED_REGISTER"
        ));

        let replay_request = EngineSymbolicPathsRequest {
            context: replay_context,
        };
        assert!(matches!(
            EngineSession::new().symbolic_paths(replay_request),
            Err(EngineSymbolicRequestError::ReplaySeed(
                r2sym::PreparedReplaySeedError::UnknownRegister(name)
            )) if name == "UNDECLARED_REGISTER"
        ));

        let missing_scope_context = EngineSymbolicContextRequest {
            scope: None,
            ..context
        };
        assert!(
            symbolic_initial_state(&missing_scope_context)
                .expect("missing exact scope leaves an empty state")
                .registers()
                .is_empty(),
            "a scope seed without exact scope authority must refuse rather than fall back to architecture seeding"
        );
    }

    #[test]
    fn symbolic_path_listing_runs_through_engine_policy() {
        let blocks = const_return_blocks(0x401000, 0);
        let prepared = Arc::new(r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared"));
        let scope = r2sym::PreparedFunctionScope::new(
            0x401000,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x401000),
                name: Some("sym.simple".to_string()),
                prepared: Arc::clone(&prepared),
            }],
        )
        .expect("scope");
        let z3_ctx = z3::Context::thread_local();
        let symbols = r2sym::FunctionSymbolSnapshot::default();
        let session = EngineSession::new();

        let response = session
            .symbolic_paths(EngineSymbolicPathsRequest {
                context: EngineSymbolicContextRequest {
                    z3_ctx: &z3_ctx,
                    prepared: &prepared,
                    scope: Some(&scope),
                    arch: None,
                    symbols: &symbols,
                    merge_states: false,
                    config_profile: EngineSymbolicConfigProfile::PathListing,
                    seed: EngineSymbolicStateSeed::Default {
                        entry_addr: 0x401000,
                    },
                },
            })
            .expect("symbolic paths");

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
    fn engine_translates_pre_cancelled_control_into_symbolic_request() {
        let blocks = const_return_blocks(0x401000, 0);
        let prepared = Arc::new(r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared"));
        let z3_ctx = z3::Context::thread_local();
        let symbols = r2sym::FunctionSymbolSnapshot::default();
        let cancellation = EngineCancellationToken::default();
        cancellation.cancel();

        let result = EngineSession::new().symbolic_paths_with_execution_control(
            EngineSymbolicPathsRequest {
                context: EngineSymbolicContextRequest {
                    z3_ctx: &z3_ctx,
                    prepared: &prepared,
                    scope: None,
                    arch: None,
                    symbols: &symbols,
                    merge_states: false,
                    config_profile: EngineSymbolicConfigProfile::PathListing,
                    seed: EngineSymbolicStateSeed::Default {
                        entry_addr: 0x401000,
                    },
                },
            },
            EngineExecutionControl::with_cancellation(cancellation),
        );

        assert!(matches!(
            result,
            Err(EngineSymbolicRequestError::ExecutionStopped(
                r2sym::SymExecutionStopReason::Cancelled
            ))
        ));
    }

    #[test]
    fn engine_conditions_symbolic_scope_with_root_assumptions() {
        let blocks = symbolic_register_branch_blocks(0x501000);
        let arch = symbolic_register_branch_arch();
        let prepared =
            Arc::new(r2ssa::SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("prepared"));
        let scope = r2sym::PreparedFunctionScope::new(
            0x501000,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x501000),
                name: Some("sym.branch".to_string()),
                prepared: Arc::clone(&prepared),
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
        let prepared = Arc::new(r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared"));
        let scope = r2sym::PreparedFunctionScope::new(
            0x501800,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x501800),
                name: Some("sym.branch".to_string()),
                prepared: Arc::clone(&prepared),
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
        let arch = symbolic_register_branch_arch();
        let prepared =
            Arc::new(r2ssa::SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("prepared"));
        let scope = r2sym::PreparedFunctionScope::new(
            0x502000,
            vec![r2sym::ScopedPreparedFunction {
                id: r2ssa::InterprocFunctionId(0x502000),
                name: Some("sym.branch".to_string()),
                prepared: Arc::clone(&prepared),
            }],
        )
        .expect("scope");
        let assumption = symbolic_register_assumption(&prepared);
        let assumptions = r2ssa::AssumptionSet::new(vec![assumption.clone()]);
        let conditioned = condition_symbolic_scope_with_assumptions(&scope, &assumptions)
            .expect("conditioned scope");
        let z3_ctx = z3::Context::thread_local();
        let symbols = r2sym::FunctionSymbolSnapshot::default();
        let session = EngineSession::new();

        let response = session
            .symbolic_summary(EngineSymbolicSummaryRequest {
                context: EngineSymbolicContextRequest {
                    z3_ctx: &z3_ctx,
                    prepared: &conditioned.prepared,
                    scope: Some(&conditioned.scope),
                    arch: None,
                    symbols: &symbols,
                    merge_states: false,
                    config_profile: EngineSymbolicConfigProfile::PathListing,
                    seed: EngineSymbolicStateSeed::Scope {
                        entry_addr: 0x502000,
                    },
                },
                compile_semantics: false,
            })
            .expect("symbolic summary");

        assert!(response.assumption_conditioned);
        assert_eq!(response.assumption_usage.applied, vec![assumption]);
        assert!(response.assumption_usage.ignored.is_empty());
        assert!(response.assumption_usage.conflicts.is_empty());
    }

    #[test]
    fn request_plan_preserves_refusal_diagnostics() {
        let comment = "/* r2dec fallback: semantic evidence unavailable */".to_string();
        let route = test_decompile_route(
            r2types::DecompileRouteKind::FallbackComment,
            Some(&comment),
            Some(&comment),
        );
        let decision = EngineRouteDecision {
            request: EngineRequestKind::Decompile,
            plan: select_engine_plan(EngineRequestKind::Decompile, Some(&route), None),
            route,
        };

        let request_plan = EngineRequestPlan::decompile(decision);
        let diagnostics = request_plan.diagnostics();

        assert_eq!(request_plan.engine_plan(), EnginePlan::RefuseWithEvidence);
        assert_eq!(diagnostics.refusal, Some(comment.clone()));
        assert_eq!(diagnostics.route_reason, Some(comment.clone()));
    }

    #[test]
    fn phase_timing_reports_executed_phases_and_omits_the_rest() {
        let mut metrics = EngineMetrics::default();
        metrics.record_phase(
            EnginePhase::Ssa,
            EnginePhaseStatus::Executed,
            Duration::from_micros(4_000),
        );
        metrics.record_phase(
            EnginePhase::Rendering,
            EnginePhaseStatus::Executed,
            Duration::from_micros(11_500),
        );
        metrics.record_phase(
            EnginePhase::Types,
            EnginePhaseStatus::Folded,
            Duration::default(),
        );
        let comment = format_phase_timing(&metrics);
        assert_eq!(
            comment,
            "/* r2dec timing: measured=15500us ssa=4000us types=folded rendering=11500us */"
        );
        // A phase this boundary never ran says nothing, rather than claiming
        // it cost nothing.
        assert!(!comment.contains("symbolic"));
    }

    #[test]
    fn phase_timing_survives_a_refusal_so_refusing_can_be_compared_with_rendering() {
        let mut metrics = EngineMetrics::default();
        metrics.record_phase(
            EnginePhase::SnapshotContext,
            EnginePhaseStatus::Executed,
            Duration::from_micros(120),
        );
        metrics.refuse_from(EnginePhase::LiftNormalize);
        let comment = format_phase_timing(&metrics);
        assert!(
            comment.starts_with("/* r2dec timing: measured=120us"),
            "{comment}"
        );
        assert!(comment.contains("lift_normalize=refused"), "{comment}");
    }

    #[test]
    fn a_body_without_the_switch_is_returned_byte_for_byte() {
        // The comment is opt-in, and every corpus gate compares bytes.
        let body = "uint64_t sym__f(void)\n{\n    return 0;\n}\n".to_string();
        let metrics = EngineMetrics::default();
        unsafe { std::env::remove_var("R2SLEIGH_TIMING") };
        assert_eq!(with_phase_timing_comment(body.clone(), &metrics), body);
    }
}
