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

mod route;

pub use route::{
    DecompileProbeDecision, EngineDiagnostics, EngineFunctionIdentity, EnginePlan,
    EngineRequestKind, EngineRequestPlan, EngineRouteContext, EngineRouteDecision,
    EngineSemanticKernelRegion, EngineSemanticKernelRender, EngineTypeRouteDecision,
    EngineTypeRouteKind, EngineTypedRouteDecision, cfg_guard_reason, cfg_guard_reason_from_summary,
    plan_type_request, prefer_symbolic_large_worker_decompile, select_engine_plan,
    semantic_artifact_needs_fallback_type_payload, semantic_or_cfg_prefers_bounded_type_plan,
    should_guard_program_orchestrator_decompile, should_use_prepared_semantic_view,
    type_cfg_allows_semantic_plan, type_cfg_bounded_reason, type_cfg_forces_bounded_plan,
    type_cfg_prefers_bounded_plan, type_route_decision,
};
#[cfg(test)]
use route::{decompile_probe_decision, plan_decompile_request, semantic_route_reason};
use route::{decompile_probe_decision_for_identity, decompile_route_decision};
pub const SYMBOLIC_PATHS_LIMIT: usize = 32;
pub const SYMBOLIC_PATHS_CALL_FREE_MAX_STATES: usize = 16;
pub const SYMBOLIC_PATHS_CALL_FREE_MAX_DEPTH: usize = 64;
pub const SYMBOLIC_PATHS_CALL_HEAVY_MAX_STATES: usize = 8;
pub const SYMBOLIC_PATHS_CALL_HEAVY_MAX_DEPTH: usize = 32;
pub const SYMBOLIC_PATHS_TIMEOUT_MS: u64 = 500;
pub const SYMBOLIC_PATHS_SOLUTION_LIMIT: usize = 4;
pub const RADARE2_ANALYSIS_DEPTH_BASIC: u32 = 1;
pub const RADARE2_ANALYSIS_DEPTH_AGGRESSIVE: u32 = 3;
pub const POST_ANALYSIS_FAST_BUDGET_USEC: u64 = 2 * 1_000_000;
pub const POST_ANALYSIS_BALANCED_BUDGET_USEC: u64 = 10 * 1_000_000;
pub const POST_ANALYSIS_AGGRESSIVE_BUDGET_USEC: u64 = 30 * 1_000_000;
pub const TAINT_GLOBAL_MAX_FUNCTIONS: usize = 128;
pub const SIGNATURE_WRITEBACK_GLOBAL_MAX_FUNCTIONS: usize = 128;
pub const TYPE_WRITEBACK_GLOBAL_MAX_FUNCTIONS: usize = 128;
pub const ENGINE_DECOMPILE_MAX_BLOCKS: usize = 200;
pub const ENGINE_DECOMPILE_MAX_OPS: usize = 512;
pub const AUTO_CALLBACK_MAX_BLOCKS: u32 = 96;
pub const AUTO_CALLBACK_MAX_COST: u32 = 512;
pub const AUTO_CALLBACK_MAX_LINEAR_SIZE: u64 = 256 * 1024;
pub const SYMBOLIC_SCOPE_MAX_FUNCTIONS: usize = 32;
pub const RUNTIME_MATERIALIZED_MAX_BYTES: u64 = 0x4000;
pub const RUNTIME_MATERIALIZED_SLOT_BYTES: u64 = 16;
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
            call_site_interfaces: call_site_interfaces.into_boxed_slice(),
        })
    }

    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub const fn function_interface(&self) -> Option<&r2ssa::SourceFunctionInterface> {
        self.function_interface.as_ref()
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

pub const TYPE_WRITEBACK_MUTATION_SIGNATURE_ID: u32 = 0;
pub const TYPE_WRITEBACK_MUTATION_CALLCONV_ID: u32 = 1;
pub const TYPE_WRITEBACK_MUTATION_VAR_ID: u32 = 2;
pub const TYPE_WRITEBACK_MUTATION_VAR_RENAME_ID: u32 = 3;
pub const TYPE_WRITEBACK_MUTATION_VAR_TYPE_ID: u32 = 4;
pub const TYPE_WRITEBACK_MUTATION_XREF_ID: u32 = 5;
pub const TYPE_WRITEBACK_MUTATION_COMMENT_ID: u32 = 6;
pub const TYPE_WRITEBACK_MUTATION_FLAG_ID: u32 = 7;
pub const TYPE_WRITEBACK_MUTATION_TYPE_DECL_ID: u32 = 8;
pub const TYPE_WRITEBACK_MUTATION_TYPE_LINK_ID: u32 = 9;

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

pub const ENGINE_EXTERNAL_VAR_REGISTER: u32 = 0;
pub const ENGINE_EXTERNAL_VAR_STACK: u32 = 1;
pub const ENGINE_EXTERNAL_STACK_LOCAL: u32 = 0;
pub const ENGINE_EXTERNAL_STACK_ARG: u32 = 1;
pub const ENGINE_EXTERNAL_STACK_HOME: u32 = 2;
pub const ENGINE_EXTERNAL_STACK_SAVED_REG: u32 = 3;
pub const ENGINE_EXTERNAL_STACK_SAVED_FP: u32 = 4;
pub const ENGINE_EXTERNAL_STACK_UNKNOWN: u32 = 5;
pub const ENGINE_EXTERNAL_BASE_STRUCT: u32 = 0;
pub const ENGINE_EXTERNAL_BASE_UNION: u32 = 1;
pub const ENGINE_EXTERNAL_BASE_ENUM: u32 = 2;
pub const ENGINE_EXTERNAL_BASE_TYPEDEF: u32 = 3;
pub const ENGINE_EXTERNAL_BASE_ATOMIC: u32 = 4;
pub const ENGINE_EXTERNAL_LINKAGE_UNKNOWN: u32 = 0;
pub const ENGINE_EXTERNAL_LINKAGE_INTERNAL: u32 = 1;
pub const ENGINE_EXTERNAL_LINKAGE_IMPORTED: u32 = 2;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineExternalContextInput {
    pub schema_version: u32,
    pub dirty_epoch: u64,
    pub context_hash: u64,
    pub type_dirty_epoch: u64,
    pub signature: EngineExternalSignatureInput,
    pub vars: Vec<EngineExternalVarInput>,
    pub base_types: Vec<EngineExternalBaseTypeInput>,
    pub callees: Vec<EngineExternalCalleeInput>,
    pub assumptions_json: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineExternalSignatureInput {
    pub name: Option<String>,
    pub ret_type: Option<String>,
    pub callconv: Option<String>,
    pub noreturn: bool,
    pub params: Vec<EngineExternalSignatureParamInput>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineExternalSignatureParamInput {
    pub name: Option<String>,
    pub ty: Option<String>,
    pub cc_reg: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineExternalVarInput {
    pub kind: u32,
    pub name: Option<String>,
    pub ty: Option<String>,
    pub reg: Option<String>,
    pub base: Option<String>,
    pub offset: Option<i64>,
    pub role: u32,
    pub param_index: Option<usize>,
    pub param_name: Option<String>,
    pub source_reg: Option<String>,
    pub is_arg: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineExternalBaseTypeInput {
    pub kind: u32,
    pub name: Option<String>,
    pub ty: Option<String>,
    pub size_bits: Option<u64>,
    pub members: Vec<EngineExternalBaseMemberInput>,
    pub variants: Vec<EngineExternalEnumVariantInput>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineExternalBaseMemberInput {
    pub name: Option<String>,
    pub ty: Option<String>,
    pub offset: u64,
    pub size_bits: Option<u64>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineExternalEnumVariantInput {
    pub name: Option<String>,
    pub value: i64,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineExternalCalleeInput {
    pub call_addr: u64,
    pub addr: u64,
    pub name: Option<String>,
    pub linkage: u32,
    pub signature: EngineExternalSignatureInput,
}

pub fn parse_typed_external_context(
    input: EngineExternalContextInput,
    ptr_bits: u32,
) -> r2types::ParsedExternalContext {
    let signature = engine_external_signature_json(input.signature);
    let vars = input
        .vars
        .into_iter()
        .enumerate()
        .map(engine_external_var_json)
        .collect::<Vec<_>>();
    let mut raw = r2types::ExternalContextJson {
        context: Some(r2types::ExternalContextMetadataJson {
            schema_version: (input.schema_version != 0).then_some(input.schema_version as u64),
            dirty_epoch: (input.dirty_epoch != 0).then_some(input.dirty_epoch),
            type_dirty_epoch: (input.type_dirty_epoch != 0).then_some(input.type_dirty_epoch),
            context_hash: (input.context_hash != 0).then_some(input.context_hash),
        }),
        signature,
        vars,
        base_types: input
            .base_types
            .into_iter()
            .map(engine_external_base_type_json)
            .collect(),
        callees: input
            .callees
            .into_iter()
            .map(engine_external_callee_json)
            .collect(),
        known_signatures: Vec::new(),
        assumptions: Vec::new(),
    };

    if let Some(assumptions) = input.assumptions_json
        && let Ok(parsed) = r2types::parse_external_assumption_payload_json(&assumptions, ptr_bits)
    {
        raw.assumptions = parsed.items;
    }

    r2types::parse_external_context(raw, ptr_bits)
}

fn engine_external_signature_input_is_empty(signature: &EngineExternalSignatureInput) -> bool {
    signature.name.is_none()
        && signature.ret_type.is_none()
        && signature.callconv.is_none()
        && !signature.noreturn
        && signature.params.is_empty()
}

fn engine_external_signature_json(
    signature: EngineExternalSignatureInput,
) -> Option<r2types::ExternalSignatureJson> {
    (!engine_external_signature_input_is_empty(&signature)).then(|| {
        r2types::ExternalSignatureJson {
            name: signature.name,
            ret_type: signature.ret_type,
            callconv: signature.callconv,
            noreturn: signature.noreturn,
            params: signature
                .params
                .into_iter()
                .map(|param| r2types::ExternalSignatureParamJson {
                    name: param.name,
                    ty: param.ty,
                    cc_reg: param.cc_reg,
                })
                .collect(),
        }
    })
}

fn engine_external_var_json(
    (idx, var): (usize, EngineExternalVarInput),
) -> r2types::ExternalVarJson {
    let (kind, is_register) = match var.kind {
        ENGINE_EXTERNAL_VAR_REGISTER => (r2types::ExternalVarKind::Register, true),
        _ => (r2types::ExternalVarKind::Stack, false),
    };
    let fallback_name = if is_register {
        format!("arg{}", idx + 1)
    } else {
        format!("stack_{:x}", var.offset.unwrap_or_default())
    };
    r2types::ExternalVarJson {
        kind,
        name: var.name.unwrap_or(fallback_name),
        ty: var.ty,
        is_arg: var.is_arg,
        reg: var.reg,
        base: var.base,
        offset: var.offset,
        role: Some(engine_external_stack_role(var.role)),
        param_index: var.param_index,
        param_name: var.param_name,
        source_reg: var.source_reg,
    }
}

fn engine_external_stack_role(role: u32) -> r2types::ExternalStackSlotRole {
    match role {
        ENGINE_EXTERNAL_STACK_LOCAL => r2types::ExternalStackSlotRole::Local,
        ENGINE_EXTERNAL_STACK_ARG => r2types::ExternalStackSlotRole::StackArg,
        ENGINE_EXTERNAL_STACK_HOME => r2types::ExternalStackSlotRole::ParamHome,
        ENGINE_EXTERNAL_STACK_SAVED_REG => r2types::ExternalStackSlotRole::SavedReg,
        ENGINE_EXTERNAL_STACK_SAVED_FP => r2types::ExternalStackSlotRole::SavedFp,
        ENGINE_EXTERNAL_STACK_UNKNOWN => r2types::ExternalStackSlotRole::Unknown,
        _ => r2types::ExternalStackSlotRole::Unknown,
    }
}

fn engine_external_base_type_kind(kind: u32) -> r2types::ExternalBaseTypeKind {
    match kind {
        ENGINE_EXTERNAL_BASE_STRUCT => r2types::ExternalBaseTypeKind::Struct,
        ENGINE_EXTERNAL_BASE_UNION => r2types::ExternalBaseTypeKind::Union,
        ENGINE_EXTERNAL_BASE_ENUM => r2types::ExternalBaseTypeKind::Enum,
        ENGINE_EXTERNAL_BASE_TYPEDEF => r2types::ExternalBaseTypeKind::Typedef,
        ENGINE_EXTERNAL_BASE_ATOMIC => r2types::ExternalBaseTypeKind::Atomic,
        _ => r2types::ExternalBaseTypeKind::Atomic,
    }
}

fn engine_external_base_type_json(
    base_type: EngineExternalBaseTypeInput,
) -> r2types::ExternalBaseTypeJson {
    r2types::ExternalBaseTypeJson {
        kind: engine_external_base_type_kind(base_type.kind),
        name: base_type.name.unwrap_or_default(),
        members: base_type
            .members
            .into_iter()
            .map(|member| r2types::ExternalBaseTypeMemberJson {
                name: member.name.unwrap_or_default(),
                ty: member.ty.unwrap_or_else(|| "void *".to_string()),
                offset: member.offset,
                size_bits: member.size_bits,
            })
            .collect(),
        variants: base_type
            .variants
            .into_iter()
            .map(|variant| r2types::ExternalEnumVariantJson {
                name: variant.name.unwrap_or_default(),
                value: variant.value,
            })
            .collect(),
        ty: base_type.ty,
        size_bits: base_type.size_bits,
    }
}

fn engine_external_callee_json(callee: EngineExternalCalleeInput) -> r2types::ExternalCalleeJson {
    r2types::ExternalCalleeJson {
        signature: engine_external_signature_json(callee.signature),
        call_addr: Some(callee.call_addr),
        addr: callee.addr,
        name: callee.name,
        linkage: match callee.linkage {
            ENGINE_EXTERNAL_LINKAGE_INTERNAL => r2types::ExternalCalleeLinkageJson::Internal,
            ENGINE_EXTERNAL_LINKAGE_IMPORTED => r2types::ExternalCalleeLinkageJson::Imported,
            _ => r2types::ExternalCalleeLinkageJson::Unknown,
        },
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineInferredParamJson {
    pub name: String,
    #[serde(rename = "type")]
    pub param_type: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineVarTypeCandidateJson {
    pub name: String,
    pub kind: String,
    pub delta: i64,
    #[serde(rename = "type")]
    pub var_type: String,
    pub isarg: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reg: Option<String>,
    pub size: u32,
    pub confidence: u8,
    pub source: String,
    pub evidence: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineVarRenameCandidateJson {
    pub name: String,
    pub target_name: String,
    pub confidence: u8,
    pub source: String,
    pub evidence: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineStructFieldCandidateJson {
    pub name: String,
    pub offset: u64,
    #[serde(rename = "type")]
    pub field_type: String,
    pub confidence: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineStructDeclCandidateJson {
    pub name: String,
    pub decl: String,
    pub confidence: u8,
    pub source: String,
    pub fields: Vec<EngineStructFieldCandidateJson>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineGlobalTypeLinkCandidateJson {
    pub addr: u64,
    #[serde(rename = "type")]
    pub target_type: String,
    pub confidence: u8,
    pub source: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct EngineTypeWritebackDiagnosticsJson {
    pub conflicts: Vec<String>,
    pub warnings: Vec<String>,
    pub solver_warnings: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct EngineTypeWritebackFactCountsJson {
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineTypeWritebackJsonCore {
    pub function_name: String,
    pub signature: String,
    pub ret_type: String,
    pub params: Vec<EngineInferredParamJson>,
    pub callconv: String,
    pub arch: String,
    pub confidence: u8,
    pub callconv_confidence: u8,
    pub signature_render_authorized: bool,
    pub signature_writeback_authorized: bool,
    pub signature_action_decision: u32,
    pub callconv_action_decision: u32,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub signature_certificate_sources: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature_writeback_refusal: Option<String>,
    pub var_type_candidates: Vec<EngineVarTypeCandidateJson>,
    pub var_rename_candidates: Vec<EngineVarRenameCandidateJson>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub external_struct_names: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub field_access_certificate_names: Vec<String>,
    #[serde(
        default,
        skip_serializing_if = "EngineTypeWritebackFactCountsJson::is_empty"
    )]
    pub fact_counts: EngineTypeWritebackFactCountsJson,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub param_home_stack_slot_offsets: Vec<i64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub certified_stack_slot_offsets: Vec<i64>,
    pub struct_decls: Vec<EngineStructDeclCandidateJson>,
    pub global_type_links: Vec<EngineGlobalTypeLinkCandidateJson>,
    pub plans: r2types::AnalysisPlans,
    #[serde(skip_serializing_if = "r2ssa::AssumptionSet::is_empty")]
    pub assumptions: r2ssa::AssumptionSet,
    #[serde(skip_serializing_if = "r2types::AssumptionUsageReport::is_empty")]
    pub assumption_usage: r2types::AssumptionUsageReport,
    pub mutation_plan: r2types::TypeWritebackMutationPlan,
    pub diagnostics: EngineTypeWritebackDiagnosticsJson,
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineCfgRiskSummaryJson {
    pub block_count: usize,
    pub loop_count: usize,
    pub back_edge_count: usize,
    pub switch_block_count: usize,
    pub max_switch_cases: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineDecompileRouteJson {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineFunctionAnalysisReportJsonCore {
    pub function_name: String,
    pub function_addr: u64,
    pub cfg_risk: EngineCfgRiskSummaryJson,
    pub plans: r2types::AnalysisPlans,
    #[serde(skip_serializing_if = "r2ssa::AssumptionSet::is_empty")]
    pub assumptions: r2ssa::AssumptionSet,
    #[serde(skip_serializing_if = "r2types::AssumptionUsageReport::is_empty")]
    pub assumption_usage: r2types::AssumptionUsageReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_build_plan: Option<r2sym::ArtifactBuildPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_route: Option<EngineDecompileRouteJson>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary_diagnostics: Option<r2ssa::InterprocSummaryDiagnostics>,
    pub prefer_bounded_type_plan: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EngineInterprocSummaryJson {
    pub callsite_count: usize,
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary: Option<r2ssa::FunctionSemanticSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary_json: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub scope: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Copy)]
pub struct EngineInterprocSummaryJsonInput<'a> {
    pub callsite_count: usize,
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub summary: Option<&'a r2ssa::FunctionSemanticSummary>,
    pub scope_report: Option<&'a serde_json::Value>,
    pub symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnginePhaseTimingJson {
    pub phase: EnginePhase,
    pub status: EnginePhaseStatus,
    pub elapsed_us: u64,
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

#[derive(Debug, Clone, Serialize)]
pub struct EngineSemanticStatusJson {
    pub available: bool,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct EngineInferredTypeWritebackJson {
    #[serde(flatten)]
    pub core: EngineTypeWritebackJsonCore,
    pub interproc: EngineInterprocSummaryJson,
    pub semantic_status: EngineSemanticStatusJson,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantics: Option<r2sym::SemanticArtifactReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiled_semantics: Option<r2sym::CompiledSemanticInfo>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub phase_timings: Vec<EnginePhaseTimingJson>,
}

impl std::ops::Deref for EngineInferredTypeWritebackJson {
    type Target = EngineTypeWritebackJsonCore;

    fn deref(&self) -> &Self::Target {
        &self.core
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct EngineFunctionAnalysisSessionReportJson {
    #[serde(flatten)]
    pub core: EngineFunctionAnalysisReportJsonCore,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic: Option<r2sym::CompiledSemanticInfo>,
    pub type_writeback: EngineInferredTypeWritebackJson,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub phase_timings: Vec<EnginePhaseTimingJson>,
}

#[derive(Debug, Clone, Copy)]
pub struct EngineFunctionAnalysisTypeWritebackJsonRequest<'a> {
    pub report: &'a EngineFunctionAnalysisReportPayload,
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub scope_report: Option<&'a serde_json::Value>,
    pub symbolic_scope: Option<&'a r2sym::PreparedFunctionScope>,
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

fn writeback_evidence_json(evidence: &[r2types::WritebackEvidence]) -> Vec<String> {
    evidence
        .iter()
        .map(|tag| tag.as_str().to_string())
        .collect()
}

fn struct_fields_json(
    fields: &[r2types::StructFieldCandidate],
) -> Vec<EngineStructFieldCandidateJson> {
    fields
        .iter()
        .map(|field| EngineStructFieldCandidateJson {
            name: field.name.clone(),
            offset: field.offset,
            field_type: field.field_type.clone(),
            confidence: field.confidence,
        })
        .collect()
}

pub fn type_writeback_json_core(
    payload: EngineTypeWritebackPayload,
) -> EngineTypeWritebackJsonCore {
    EngineTypeWritebackJsonCore {
        function_name: payload.signature.function_name,
        signature: payload.signature.signature,
        ret_type: payload.signature.ret_type,
        params: payload
            .signature
            .params
            .into_iter()
            .map(|param| EngineInferredParamJson {
                name: param.name,
                param_type: param.param_type,
            })
            .collect(),
        callconv: payload.signature.callconv,
        arch: payload.signature.arch,
        confidence: payload.signature.confidence,
        callconv_confidence: payload.signature.callconv_confidence,
        signature_render_authorized: payload.signature_render_authorized,
        signature_writeback_authorized: payload.signature_writeback_authorized,
        signature_action_decision: payload.signature_action_decision as u32,
        callconv_action_decision: payload.callconv_action_decision as u32,
        signature_certificate_sources: payload.signature_certificate_sources,
        signature_writeback_refusal: payload.signature_writeback_refusal,
        var_type_candidates: payload
            .var_type_candidates
            .into_iter()
            .map(|candidate| EngineVarTypeCandidateJson {
                name: candidate.name,
                kind: candidate.kind,
                delta: candidate.delta,
                var_type: candidate.var_type,
                isarg: candidate.isarg,
                reg: candidate.reg,
                size: candidate.size,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: writeback_evidence_json(&candidate.evidence),
            })
            .collect(),
        var_rename_candidates: payload
            .var_rename_candidates
            .into_iter()
            .map(|candidate| EngineVarRenameCandidateJson {
                name: candidate.name,
                target_name: candidate.target_name,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
                evidence: writeback_evidence_json(&candidate.evidence),
            })
            .collect(),
        external_struct_names: payload.external_struct_names,
        field_access_certificate_names: payload.field_access_certificate_names,
        fact_counts: EngineTypeWritebackFactCountsJson {
            register_params: payload.fact_counts.register_params,
            stack_slots: payload.fact_counts.stack_slots,
            param_home_stack_slots: payload.fact_counts.param_home_stack_slots,
            hidden_home_bindings: payload.fact_counts.hidden_home_bindings,
            field_access_certificates: payload.fact_counts.field_access_certificates,
            array_index_certificates: payload.fact_counts.array_index_certificates,
            scalar_array_render_candidates: payload.fact_counts.scalar_array_render_candidates,
            render_member_accesses: payload.fact_counts.render_member_accesses,
            render_array_accesses: payload.fact_counts.render_array_accesses,
            certified_expressions: payload.fact_counts.certified_expressions,
            certified_parameters: payload.fact_counts.certified_parameters,
            certified_stack_slots: payload.fact_counts.certified_stack_slots,
            certified_memory_accesses: payload.fact_counts.certified_memory_accesses,
            certified_returns: payload.fact_counts.certified_returns,
            certified_control_domains: payload.fact_counts.certified_control_domains,
            incomplete_control_domains: payload.fact_counts.incomplete_control_domains,
        },
        param_home_stack_slot_offsets: payload.param_home_stack_slot_offsets,
        certified_stack_slot_offsets: payload.certified_stack_slot_offsets,
        struct_decls: payload
            .struct_decls
            .into_iter()
            .map(|decl| EngineStructDeclCandidateJson {
                name: decl.name,
                decl: decl.decl,
                confidence: decl.confidence,
                source: decl.source.as_str().to_string(),
                fields: struct_fields_json(&decl.fields),
            })
            .collect(),
        global_type_links: payload
            .global_type_links
            .into_iter()
            .map(|candidate| EngineGlobalTypeLinkCandidateJson {
                addr: candidate.addr,
                target_type: candidate.target_type,
                confidence: candidate.confidence,
                source: candidate.source.as_str().to_string(),
            })
            .collect(),
        plans: payload.plans,
        assumptions: payload.assumptions,
        assumption_usage: payload.assumption_usage,
        mutation_plan: payload.mutation_plan,
        diagnostics: EngineTypeWritebackDiagnosticsJson {
            conflicts: payload.diagnostics.conflicts,
            warnings: payload.diagnostics.warnings,
            solver_warnings: payload.diagnostics.solver_warnings,
        },
    }
}

pub fn type_writeback_report_json(
    payload: EngineTypeWritebackPayload,
    interproc: EngineInterprocSummaryJson,
    semantics: Option<r2sym::SemanticArtifactReport>,
    compiled_semantics: Option<r2sym::CompiledSemanticInfo>,
) -> EngineInferredTypeWritebackJson {
    let semantic_status = semantic_status_json(semantics.as_ref(), None);
    EngineInferredTypeWritebackJson {
        core: type_writeback_json_core(payload),
        interproc,
        semantic_status,
        semantics,
        compiled_semantics,
        phase_timings: empty_engine_phase_timings(),
    }
}

fn semantic_status_json(
    semantics: Option<&r2sym::SemanticArtifactReport>,
    fallback_reason: Option<String>,
) -> EngineSemanticStatusJson {
    match semantics {
        Some(artifact) => EngineSemanticStatusJson {
            available: true,
            reason: format!(
                "{} {}",
                semantic_granularity_label(artifact.granularity),
                semantic_report_mode_label(artifact)
            ),
        },
        None => EngineSemanticStatusJson {
            available: false,
            reason: fallback_reason.unwrap_or_else(|| "semantic artifact unavailable".to_string()),
        },
    }
}

fn semantic_granularity_label(granularity: r2sym::ArtifactGranularity) -> &'static str {
    match granularity {
        r2sym::ArtifactGranularity::WholeFunction => "whole_function",
        r2sym::ArtifactGranularity::Regioned => "regioned",
        r2sym::ArtifactGranularity::SummaryOnly => "summary_only",
    }
}

pub fn type_writeback_report_json_from_function_analysis(
    request: EngineFunctionAnalysisTypeWritebackJsonRequest<'_>,
) -> EngineInferredTypeWritebackJson {
    let semantics = request.report.semantic_report.clone();
    let compiled_semantics = request.report.compiled_semantics.clone();
    let mut report = type_writeback_report_json(
        request.report.type_writeback.clone(),
        interproc_summary_json(EngineInterprocSummaryJsonInput {
            callsite_count: request.report.callsite_count,
            iterations: request.iterations,
            max_iterations: request.max_iterations,
            converged: request.converged,
            summary: request.report.current_summary.as_ref(),
            scope_report: request.scope_report,
            symbolic_scope: request.symbolic_scope,
        }),
        semantics,
        compiled_semantics,
    );
    report.semantic_status = semantic_status_json(
        report.semantics.as_ref(),
        request
            .report
            .semantic_route
            .as_ref()
            .and_then(|route| route.reason.clone())
            .or_else(|| {
                request
                    .report
                    .summary_diagnostics
                    .as_ref()
                    .map(|diagnostics| format!("summary diagnostics: {diagnostics:?}"))
            }),
    );
    report
}

pub fn symbolic_scope_report_json(
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<serde_json::Value> {
    let scope = symbolic_scope?;
    let payloads = scope
        .helper_functions()
        .filter_map(|function| {
            function.name.as_ref().map(|name| {
                serde_json::json!({
                    "function_addr": function.id.0,
                    "function_name": name,
                })
            })
        })
        .collect::<Vec<_>>();
    let seeds = scope
        .helper_functions()
        .filter_map(|function| {
            function.name.as_ref().map(|name| {
                serde_json::json!({
                    "id": function.id.0,
                    "name": name,
                })
            })
        })
        .collect::<Vec<_>>();
    if seeds.is_empty() && payloads.is_empty() {
        return None;
    }
    Some(serde_json::json!({
        "phase": "symbolic_scope",
        "payloads": payloads,
        "seeds": seeds,
    }))
}

pub fn merged_interproc_scope_report_json(
    scope_report: Option<&serde_json::Value>,
    symbolic_scope: Option<&r2sym::PreparedFunctionScope>,
) -> Option<serde_json::Value> {
    let Some(symbolic_scope_json) = symbolic_scope_report_json(symbolic_scope) else {
        return scope_report.cloned();
    };
    let Some(mut merged) = scope_report.cloned() else {
        return Some(symbolic_scope_json);
    };
    let (Some(merged_obj), Some(symbolic_obj)) =
        (merged.as_object_mut(), symbolic_scope_json.as_object())
    else {
        return Some(merged);
    };

    if !merged_obj.contains_key("phase")
        && let Some(phase) = symbolic_obj.get("phase")
    {
        merged_obj.insert("phase".to_string(), phase.clone());
    }
    for key in ["payloads", "seeds"] {
        let Some(serde_json::Value::Array(symbolic_items)) = symbolic_obj.get(key) else {
            continue;
        };
        let entry = merged_obj
            .entry(key.to_string())
            .or_insert_with(|| serde_json::Value::Array(Vec::new()));
        if let serde_json::Value::Array(items) = entry {
            items.extend(symbolic_items.iter().cloned());
        }
    }

    Some(merged)
}

pub fn interproc_summary_json(
    input: EngineInterprocSummaryJsonInput<'_>,
) -> EngineInterprocSummaryJson {
    let iterations = input.iterations.max(1);
    EngineInterprocSummaryJson {
        callsite_count: input.callsite_count,
        iterations,
        max_iterations: input.max_iterations.max(iterations),
        converged: input.converged,
        summary: input.summary.cloned(),
        summary_json: input
            .summary
            .and_then(|summary| serde_json::to_string(summary).ok()),
        scope: merged_interproc_scope_report_json(input.scope_report, input.symbolic_scope),
    }
}

fn cfg_risk_summary_json(summary: CFGRiskSummary) -> EngineCfgRiskSummaryJson {
    EngineCfgRiskSummaryJson {
        block_count: summary.block_count,
        loop_count: summary.loop_count,
        back_edge_count: summary.back_edge_count,
        switch_block_count: summary.switch_block_count,
        max_switch_cases: summary.max_switch_cases,
    }
}

pub fn decompile_route_json(route: &r2types::DecompileRouteFacts) -> EngineDecompileRouteJson {
    match route.kind {
        r2types::DecompileRouteKind::Standard => EngineDecompileRouteJson {
            kind: "standard".to_string(),
            reason: None,
            comment: None,
        },
        r2types::DecompileRouteKind::StructuredWorker => EngineDecompileRouteJson {
            kind: "structured_worker".to_string(),
            reason: route.reason.clone(),
            comment: None,
        },
        r2types::DecompileRouteKind::LinearWorker => EngineDecompileRouteJson {
            kind: "linear_worker".to_string(),
            reason: route.reason.clone(),
            comment: None,
        },
        r2types::DecompileRouteKind::SummaryIslands => EngineDecompileRouteJson {
            kind: "summary_islands".to_string(),
            reason: route.reason.clone(),
            comment: None,
        },
        r2types::DecompileRouteKind::VmSummary => EngineDecompileRouteJson {
            kind: "vm_summary".to_string(),
            reason: route.reason.clone(),
            comment: None,
        },
        r2types::DecompileRouteKind::FallbackComment => EngineDecompileRouteJson {
            kind: "fallback_comment".to_string(),
            reason: route.reason.clone(),
            comment: route.fallback_comment.clone(),
        },
    }
}

pub fn function_analysis_report_json_core(
    payload: &EngineFunctionAnalysisReportPayload,
) -> EngineFunctionAnalysisReportJsonCore {
    EngineFunctionAnalysisReportJsonCore {
        function_name: payload.function_name.clone(),
        function_addr: payload.function_addr,
        cfg_risk: cfg_risk_summary_json(payload.cfg_summary),
        plans: payload.plans.clone(),
        assumptions: payload.assumptions.clone(),
        assumption_usage: payload.assumption_usage.clone(),
        semantic_build_plan: payload.semantic_build_plan.clone(),
        semantic_route: payload.semantic_route.as_ref().map(decompile_route_json),
        summary_diagnostics: payload.summary_diagnostics.clone(),
        prefer_bounded_type_plan: payload.prefer_bounded_type_plan,
    }
}

pub fn function_analysis_session_report_json(
    payload: &EngineFunctionAnalysisReportPayload,
    mut type_writeback: EngineInferredTypeWritebackJson,
    phase_timings: Vec<EnginePhaseTimingJson>,
) -> EngineFunctionAnalysisSessionReportJson {
    type_writeback.phase_timings = normalize_engine_phase_timings(type_writeback.phase_timings);
    EngineFunctionAnalysisSessionReportJson {
        core: function_analysis_report_json_core(payload),
        semantic: payload.compiled_semantics.clone(),
        type_writeback,
        phase_timings: normalize_engine_phase_timings(phase_timings),
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

pub const ENGINE_INTERPROC_HELPER_MAX_BLOCKS: u32 = 64;
pub const ENGINE_INTERPROC_HELPER_MAX_COST: u32 = 256;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineInterprocTargetMetrics {
    pub basic_block_count: u32,
    pub cost: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineInterprocTargetInput {
    pub direct_target: u64,
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

fn target_name_is_import_authorized(
    name: Option<&str>,
    linkage: r2ssa::FunctionSemanticLinkage,
) -> bool {
    name.is_some_and(r2types::callee_name_is_import_like) && engine_linkage_is_imported(linkage)
}

fn imported_name_authorizes_runtime_role(
    name: Option<&str>,
    linkage: r2ssa::FunctionSemanticLinkage,
    predicate: impl FnOnce(&str) -> bool,
) -> bool {
    engine_linkage_is_imported(linkage) && name.is_some_and(predicate)
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
    let mut registration_targets = BTreeSet::new();
    let mut runtime_copy_targets = BTreeSet::new();
    let mut decisions = Vec::new();

    for target in targets {
        let direct_target = target.direct_target;
        let resolved_target = target.resolved_target.filter(|addr| *addr != 0);
        let name = target.name.as_deref();
        let semantic_summary = target.semantic_summary.as_ref();

        let registration_target = imported_name_authorizes_runtime_role(
            name,
            target.linkage,
            r2types::callee_name_is_windows_runtime_registration,
        );
        if registration_target {
            registration_targets.insert(direct_target);
        }

        let runtime_copy_target = imported_name_authorizes_runtime_role(
            name,
            target.linkage,
            r2types::callee_name_is_runtime_copy,
        ) || semantic_summary
            .is_some_and(r2sym::semantic_summary_has_runtime_copy_role);
        if runtime_copy_target {
            runtime_copy_targets.insert(direct_target);
        }

        let skip_reason = interproc_target_skip_reason_from_evidence(
            target_name_is_import_authorized(name, target.linkage),
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
        registration_targets: registration_targets.into_iter().collect(),
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
    fn imported_name_runtime_role_requires_imported_linkage() {
        let name_matches_runtime_role: bool = kani::any();
        let linkage = match kani::any::<u8>() % 3 {
            0 => r2ssa::FunctionSemanticLinkage::Unknown,
            1 => r2ssa::FunctionSemanticLinkage::Internal,
            _ => r2ssa::FunctionSemanticLinkage::Imported,
        };

        let authorized =
            imported_name_authorizes_runtime_role(Some("runtime_role"), linkage, |_| {
                name_matches_runtime_role
            });

        assert_eq!(
            authorized,
            name_matches_runtime_role
                && matches!(linkage, r2ssa::FunctionSemanticLinkage::Imported)
        );
        if linkage != r2ssa::FunctionSemanticLinkage::Imported {
            assert!(!authorized);
        }
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

fn arch_supports_windows_x64_runtime_scope(arch: Option<&r2il::ArchSpec>) -> bool {
    let Some(arch) = arch else {
        return false;
    };
    let lower_name = arch.name.to_ascii_lowercase();
    (lower_name.contains("x86") || matches!(lower_name.as_str(), "x64" | "amd64"))
        && (arch.addr_size == 8 || lower_name.contains("64"))
}

pub fn interproc_runtime_registration_targets(
    analysis: &EngineAnalysis,
    arch: Option<&r2il::ArchSpec>,
    registration_call_targets: &[u64],
) -> Vec<u64> {
    if !arch_supports_windows_x64_runtime_scope(arch) || registration_call_targets.is_empty() {
        debug_runtime_scope_log(&format!(
            "skip supports_windows_x64={} arch={:?} registrations={}",
            arch_supports_windows_x64_runtime_scope(arch),
            arch.map(|arch| arch.name.as_str()),
            registration_call_targets.len()
        ));
        return Vec::new();
    }

    let registrations = registration_call_targets
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let observations =
        r2ssa::observe_call_arguments(&analysis.ssa_func, &r2ssa::AbiProfile::windows_x64());
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
        let Some(args) = observations.get(call_id) else {
            debug_runtime_scope_log(&format!(
                "call_id={call_id:?} target=0x{target:x} missing_args"
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

pub fn interproc_runtime_materialized_sources(
    analysis: &EngineAnalysis,
    arch: Option<&r2il::ArchSpec>,
    copy_call_targets: &[u64],
) -> Vec<EngineRuntimeMaterializedSource> {
    if !arch_supports_windows_x64_runtime_scope(arch) || copy_call_targets.is_empty() {
        return Vec::new();
    }

    let copy_targets = copy_call_targets.iter().copied().collect::<BTreeSet<_>>();
    let observations =
        r2ssa::observe_call_arguments(&analysis.ssa_func, &r2ssa::AbiProfile::windows_x64());
    let mut sources = BTreeMap::<u64, u64>::new();
    for (call_id, call) in &analysis.ssa_func.call_sites().by_id {
        let Some(target) = analysis.ssa_func.resolved_call_target(call) else {
            continue;
        };
        if !copy_targets.contains(&target) {
            continue;
        }
        let Some(args) = observations.get(call_id) else {
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
        self.parsed_context = r2types::ParsedExternalContext::default();
        self.interproc_max_iterations = self.interproc_max_iterations.max(1);
        self.symbolic_scope = None;
        self.semantic_mode = EngineSemanticMode::Full;
        self.trusted_ssa = Some(trusted);
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
            .with_optional_trusted_ssa(trusted_ssa),
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
}

impl std::fmt::Display for EngineSymbolicRunError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSpec(reason) => formatter.write_str(reason),
            Self::ExecutionStopped(reason) => reason.fmt(formatter),
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
        let identity = EngineFunctionIdentity::new(
            analysis_request.function_addr,
            &canonical_name,
            &display_name,
        );
        let probe = decompile_probe_decision_for_identity(&analysis_request.blocks, &identity);
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
        let Some(render_target) = EngineRenderTarget::for_prepared(artifact.ssa_func()) else {
            metrics.refuse_from(EnginePhase::Normalization);
            return refused_decompile_response_with_metrics(
                &display_name,
                "source-owned machine context cannot define an exact render target",
                input_quality_facts,
                metrics,
                analyze_diagnostics,
            );
        };
        if render_target != requested_render_target {
            metrics.refuse_from(EnginePhase::Normalization);
            return refused_decompile_response_with_metrics(
                &display_name,
                "requested render target does not match the source-owned machine context",
                input_quality_facts,
                metrics,
                analyze_diagnostics,
            );
        }

        if let Err(refusal) =
            poll_engine_execution(&execution, EnginePhase::Normalization, &metrics)
        {
            return refused_decompile_response_with_metrics(
                &display_name,
                &refusal.reason,
                input_quality_facts,
                *refusal.metrics,
                *refusal.diagnostics,
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
                return refused_decompile_response_with_metrics(
                    &display_name,
                    "requested decompile route is incompatible with source-owned facts",
                    input_quality_facts,
                    metrics,
                    analyze_diagnostics,
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
        self.decompile_with_r2dec_control_and_kernel_policy(request, render_control, true)
    }

    fn decompile_with_r2dec_control_and_kernel_policy<C: r2ssa::SsaWorkControl>(
        &self,
        request: EngineDecompileRequest,
        render_control: &C,
        try_semantic_kernel: bool,
    ) -> EngineDecompileResponse {
        let started = Instant::now();
        let input_quality = request.input_quality.clone();
        let response_function_facts = request.function_facts().clone();
        if request.trusted_ssa.as_deref().is_some_and(|trusted| {
            !trusted.shares_artifact(&request.source_owned_facts.shared_source())
        }) {
            return refused_decompile_response_with_metrics(
                &request.function_name,
                "trusted SSA does not match the source-owned function facts",
                input_quality.clone(),
                request.metrics,
                EngineDiagnostics::default(),
            );
        }
        let mut diagnostics = decompile_diagnostics_from_function_facts(request.function_facts());
        let planning_time = started.elapsed();

        if let Err(refusal) = poll_engine_execution(
            &request.execution,
            EnginePhase::Certification,
            &request.metrics,
        ) {
            return refused_decompile_response_with_metrics(
                &request.function_name,
                &refusal.reason,
                input_quality.clone(),
                *refusal.metrics,
                *refusal.diagnostics,
            );
        }

        let render_started = Instant::now();
        let rendered =
            match render_engine_decompile_request(&request, render_control, try_semantic_kernel) {
                Ok(rendered) => rendered,
                Err(stop) => {
                    let render_time = render_started.elapsed();
                    let metrics = engine_metrics_for_render_stop(
                        request.metrics,
                        &stop,
                        planning_time,
                        render_time,
                    );
                    let refusal = engine_render_execution_refusal(stop.reason, stop.phase, metrics);
                    return refused_decompile_response_with_metrics(
                        &request.function_name,
                        &refusal.reason,
                        input_quality.clone(),
                        *refusal.metrics,
                        *refusal.diagnostics,
                    );
                }
            };
        let render_time = render_started.elapsed();
        let mut metrics = request.metrics;
        if rendered.semantic_kernel_render.is_some() {
            metrics.record_phase(
                EnginePhase::Certification,
                EnginePhaseStatus::Folded,
                Duration::default(),
            );
        }
        if rendered.structuring_executed {
            metrics.record_phase(
                EnginePhase::Structuring,
                EnginePhaseStatus::Folded,
                Duration::default(),
            );
        }
        metrics.record_phase(
            EnginePhase::Rendering,
            EnginePhaseStatus::Executed,
            render_time,
        );
        diagnostics
            .warnings
            .extend(rendered.semantic_kernel_warnings);
        metrics.planning_time += planning_time;
        metrics.render_time = render_time;
        if let Err(refusal) =
            poll_engine_execution(&request.execution, EnginePhase::FfiConversion, &metrics)
        {
            return refused_decompile_response_with_metrics(
                &request.function_name,
                &refusal.reason,
                input_quality,
                *refusal.metrics,
                *refusal.diagnostics,
            );
        }
        if let Some(status) = rendered.semantic_kernel_render {
            let (plan, reason) = match status.region {
                EngineSemanticKernelRegion::TerminalReturnBlock => (
                    EnginePlan::FastLocal,
                    "r2dec sealed exact terminal-return typed-output ownership",
                ),
                EngineSemanticKernelRegion::AggregateMemberTerminalReturnFunction => (
                    EnginePlan::FastLocal,
                    "r2dec sealed exact aggregate-member terminal-return typed-output ownership",
                ),
                EngineSemanticKernelRegion::PlainRamMemoryTerminalReturnFunction => (
                    EnginePlan::FastLocal,
                    "r2dec sealed exact plain-RAM-memory terminal-return typed-output ownership",
                ),
                EngineSemanticKernelRegion::DirectCallTerminalReturnFunction => (
                    EnginePlan::SemanticStructured,
                    "r2dec sealed exact direct-call terminal-return typed-output ownership",
                ),
                EngineSemanticKernelRegion::PrivateFrameConditionalJoinFunction => (
                    EnginePlan::SemanticStructured,
                    "r2dec sealed exact private-frame conditional-join typed-output ownership",
                ),
                EngineSemanticKernelRegion::ConditionalTerminalReturnFunction => (
                    EnginePlan::SemanticStructured,
                    "r2dec sealed exact conditional-return typed-output ownership",
                ),
                EngineSemanticKernelRegion::GuardedTerminalReturnFunction => (
                    EnginePlan::SemanticStructured,
                    "r2dec sealed exact guarded terminal-return typed-output ownership",
                ),
                EngineSemanticKernelRegion::SwitchTerminalReturnFunction => (
                    EnginePlan::SemanticStructured,
                    "r2dec sealed exact switch terminal-return typed-output ownership",
                ),
                EngineSemanticKernelRegion::CarrierFreeLoopTerminalReturnFunction => (
                    EnginePlan::SemanticStructured,
                    "r2dec sealed exact carrier-free loop terminal-return typed-output ownership",
                ),
            };
            diagnostics.plan = Some(plan);
            diagnostics.route_reason = Some(reason.to_string());
            diagnostics.semantic_kernel_render = Some(status);
            diagnostics.refusal = None;
        }

        EngineDecompileResponse {
            output: rendered.output,
            function_facts: response_function_facts,
            input_quality,
            metrics,
            diagnostics,
        }
    }

    pub fn symbolic_summary<'ctx>(
        &self,
        request: EngineSymbolicSummaryRequest<'ctx, '_>,
    ) -> EngineSymbolicSummaryResponse<'ctx> {
        self.symbolic_summary_with_execution_control(request, EngineExecutionControl::default())
            .expect("default symbolic execution control cannot stop")
    }

    pub fn symbolic_summary_with_execution_control<'ctx>(
        &self,
        request: EngineSymbolicSummaryRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineSymbolicSummaryResponse<'ctx>, r2sym::SymExecutionStopReason> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution.poll()?;
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
        symbolic_execution.poll()?;
        if compiled
            .as_ref()
            .is_some_and(should_skip_expensive_symbolic_summary)
        {
            let initial_state = symbolic_initial_state(&context);
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

        let initial_state = symbolic_initial_state(&context);
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
            Err,
        )
    }

    pub fn symbolic_paths<'ctx>(
        &self,
        request: EngineSymbolicPathsRequest<'ctx, '_>,
    ) -> EngineSymbolicPathsResponse<'ctx> {
        self.symbolic_paths_with_execution_control(request, EngineExecutionControl::default())
            .expect("default symbolic execution control cannot stop")
    }

    pub fn symbolic_paths_with_execution_control<'ctx>(
        &self,
        request: EngineSymbolicPathsRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineSymbolicPathsResponse<'ctx>, r2sym::SymExecutionStopReason> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution.poll()?;
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
            Err,
        )
    }

    pub fn symbolic_target_explore<'ctx>(
        &self,
        request: EngineTargetExploreRequest<'ctx, '_>,
    ) -> EngineTargetExploreResponse<'ctx> {
        self.symbolic_target_explore_with_execution_control(
            request,
            EngineExecutionControl::default(),
        )
        .expect("default symbolic execution control cannot stop")
    }

    pub fn symbolic_target_explore_with_execution_control<'ctx>(
        &self,
        request: EngineTargetExploreRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineTargetExploreResponse<'ctx>, r2sym::SymExecutionStopReason> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution.poll()?;
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
        symbolic_execution.poll()?;
        let initial_state = symbolic_initial_state(&context);
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
            Err,
        )
    }

    pub fn symbolic_target_solve<'ctx>(
        &self,
        request: EngineTargetSolveRequest<'ctx, '_>,
    ) -> EngineTargetSolveResponse<'ctx> {
        self.symbolic_target_solve_with_execution_control(
            request,
            EngineExecutionControl::default(),
        )
        .expect("default symbolic execution control cannot stop")
    }

    pub fn symbolic_target_solve_with_execution_control<'ctx>(
        &self,
        request: EngineTargetSolveRequest<'ctx, '_>,
        execution: EngineExecutionControl,
    ) -> Result<EngineTargetSolveResponse<'ctx>, r2sym::SymExecutionStopReason> {
        let symbolic_execution = execution.symbolic_execution_control();
        symbolic_execution.poll()?;
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
        symbolic_execution.poll()?;
        let initial_state = symbolic_initial_state(&context);
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
            Err,
        )
    }

    pub fn symbolic_run_spec<'ctx>(
        &self,
        request: EngineRunSpecRequest<'ctx, '_>,
    ) -> Result<EngineRunSpecResponse<'ctx>, String> {
        self.symbolic_run_spec_with_execution_control(request, EngineExecutionControl::default())
            .map_err(|error| error.to_string())
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
        let mut initial_state = symbolic_initial_state_at(&context, start_pc);
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
            if let Some(scope) = symbolic_scope_for_context(context) {
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
            semantic_kernel_render: None,
            warnings: vec![
                "decompile request reached render without engine-stamped route facts".to_string(),
            ],
            refusal: None,
        };
    };
    EngineDiagnostics {
        plan: Some(engine_plan_from_decompile_route_kind(route.kind)),
        route_reason: route.reason.clone(),
        semantic_kernel_render: None,
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

#[derive(Debug)]
struct EngineRenderedDecompile {
    output: String,
    semantic_kernel_render: Option<EngineSemanticKernelRender>,
    semantic_kernel_warnings: Vec<String>,
    structuring_executed: bool,
}

const ENGINE_SEMANTIC_KERNEL_TRACE_LIMIT: usize = 8;
const ENGINE_SEMANTIC_KERNEL_REASON_CHAR_LIMIT: usize = 512;
const ENGINE_SEMANTIC_KERNEL_WARNING_TAG: &str = "semantic-kernel:";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EngineSemanticKernelProbe {
    PrivateFrame,
    Aggregate,
    Memory,
    DirectCall,
    Conditional,
    Guard,
    Switch,
    Loop,
    Terminal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EnginePrivateFrameProbeDisposition {
    NotApplicable,
    Refused,
}

fn classify_private_frame_probe_error(
    error: &r2dec::PrivateFrameConditionalJoinFunctionError,
) -> EnginePrivateFrameProbeDisposition {
    match error {
        r2dec::PrivateFrameConditionalJoinFunctionError::MissingExactJoin => {
            EnginePrivateFrameProbeDisposition::NotApplicable
        }
        _ => EnginePrivateFrameProbeDisposition::Refused,
    }
}

impl EngineSemanticKernelProbe {
    fn as_str(self) -> &'static str {
        match self {
            Self::PrivateFrame => "private-frame",
            Self::Aggregate => "aggregate",
            Self::Memory => "memory",
            Self::DirectCall => "direct-call",
            Self::Conditional => "conditional",
            Self::Guard => "guard",
            Self::Switch => "switch",
            Self::Loop => "loop",
            Self::Terminal => "terminal",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EngineSemanticKernelProbeOutcome {
    NotApplicable,
    Refused,
}

impl EngineSemanticKernelProbeOutcome {
    fn as_str(self) -> &'static str {
        match self {
            Self::NotApplicable => "not_applicable",
            Self::Refused => "refused",
        }
    }
}

#[derive(Debug, Default)]
struct EngineSemanticKernelTrace {
    warnings: Vec<String>,
}

impl EngineSemanticKernelTrace {
    fn record(
        &mut self,
        probe: EngineSemanticKernelProbe,
        outcome: EngineSemanticKernelProbeOutcome,
        reason: &str,
    ) {
        if self.warnings.len() >= ENGINE_SEMANTIC_KERNEL_TRACE_LIMIT {
            return;
        }
        let reason: String = reason
            .chars()
            .take(ENGINE_SEMANTIC_KERNEL_REASON_CHAR_LIMIT)
            .map(|ch| if ch.is_control() { ' ' } else { ch })
            .collect();
        let reason = if reason.is_empty() {
            "unspecified"
        } else {
            reason.as_str()
        };
        self.warnings.push(format!(
            "{ENGINE_SEMANTIC_KERNEL_WARNING_TAG}{}:{}:{reason}",
            probe.as_str(),
            outcome.as_str(),
        ));
    }

    fn not_applicable(&mut self, probe: EngineSemanticKernelProbe, reason: &str) {
        self.record(
            probe,
            EngineSemanticKernelProbeOutcome::NotApplicable,
            reason,
        );
    }

    fn refused(&mut self, probe: EngineSemanticKernelProbe, reason: &str) {
        self.record(probe, EngineSemanticKernelProbeOutcome::Refused, reason);
    }

    fn into_warnings(self) -> Vec<String> {
        self.warnings
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EngineRenderExecutionStop {
    reason: String,
    phase: EnginePhase,
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
) -> EngineRenderExecutionStop {
    let phase = match stop.phase() {
        r2dec::DecompileWorkPhase::Normalization => EnginePhase::Normalization,
        r2dec::DecompileWorkPhase::Structuring => EnginePhase::Structuring,
        r2dec::DecompileWorkPhase::Rendering => EnginePhase::Rendering,
    };
    let mut mapped = engine_render_stop_reason(stop.reason(), phase);
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

fn engine_semantic_kernel_refusal(
    reason: String,
    phase: EnginePhase,
    certification_completed: bool,
    structuring_completed: bool,
) -> EngineRenderExecutionStop {
    EngineRenderExecutionStop {
        reason,
        phase,
        certification_completed,
        normalization_completed: false,
        structuring_completed,
    }
}

fn prepared_artifact_has_source_aggregate_pointer(artifact: &SsaArtifact) -> bool {
    let Some(interface) = artifact.machine_context().function_interface() else {
        return false;
    };
    let Some(graph) = interface.type_graph() else {
        return false;
    };
    interface.parameter_logical_values().iter().any(|logical| {
        let Some(source_type) = usize::try_from(logical.type_id())
            .ok()
            .and_then(|type_id| graph.types().get(type_id))
        else {
            return false;
        };
        let r2ssa::SourceTypeKind::Pointer { target_type_id } = source_type.kind() else {
            return false;
        };
        usize::try_from(target_type_id)
            .ok()
            .and_then(|type_id| graph.types().get(type_id))
            .is_some_and(|target| matches!(target.kind(), r2ssa::SourceTypeKind::Struct { .. }))
    })
}

#[derive(Debug)]
enum EngineSemanticKernelAttempt {
    NotApplicable(Vec<String>),
    Rendered(EngineRenderedDecompile),
}

fn complete_engine_semantic_kernel_attempt<C: r2ssa::SsaWorkControl + ?Sized>(
    control: &C,
    attempt: EngineSemanticKernelAttempt,
) -> Result<EngineSemanticKernelAttempt, EngineRenderExecutionStop> {
    match &attempt {
        EngineSemanticKernelAttempt::Rendered(rendered) => {
            poll_engine_render_control_with_completion(
                control,
                EnginePhase::Rendering,
                true,
                rendered.structuring_executed,
            )?;
        }
        EngineSemanticKernelAttempt::NotApplicable(_) => {
            poll_engine_render_control(control, EnginePhase::Rendering)?;
        }
    }
    Ok(attempt)
}

fn resolve_engine_semantic_kernel_attempt(
    attempt: EngineSemanticKernelAttempt,
) -> Result<(Option<EngineRenderedDecompile>, Vec<String>), EngineRenderExecutionStop> {
    match attempt {
        EngineSemanticKernelAttempt::NotApplicable(warnings) => Ok((None, warnings)),
        EngineSemanticKernelAttempt::Rendered(rendered) => Ok((Some(rendered), Vec::new())),
    }
}

fn render_semantic_kernel_function<C: r2ssa::SsaWorkControl + ?Sized>(
    request: &EngineDecompileRequest,
    control: &C,
) -> Result<EngineSemanticKernelAttempt, EngineRenderExecutionStop> {
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    let Some(trusted) = request.trusted_ssa.as_deref() else {
        return complete_engine_semantic_kernel_attempt(
            control,
            EngineSemanticKernelAttempt::NotApplicable(Vec::new()),
        );
    };
    let mut trace = EngineSemanticKernelTrace::default();
    match r2dec::CertifiedPrivateFrameConditionalJoinFunction::from_artifact(trusted) {
        Ok(function) => {
            let output = function.render_certified_c().map_err(|error| {
                engine_semantic_kernel_refusal(
                    format!(
                        "private-frame conditional-join rendering refused after exact certification: {error}"
                    ),
                    EnginePhase::Rendering,
                    true,
                    true,
                )
            })?;
            return complete_engine_semantic_kernel_attempt(
                control,
                EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                    output,
                    structuring_executed: true,
                    semantic_kernel_render: Some(EngineSemanticKernelRender {
                        region: EngineSemanticKernelRegion::PrivateFrameConditionalJoinFunction,
                        region_schema_version: function.schema_version(),
                        exact_obligation_closure: true,
                    }),
                    semantic_kernel_warnings: trace.into_warnings(),
                }),
            );
        }
        Err(error) => match classify_private_frame_probe_error(&error) {
            EnginePrivateFrameProbeDisposition::NotApplicable => {
                trace.not_applicable(EngineSemanticKernelProbe::PrivateFrame, &error.to_string())
            }
            EnginePrivateFrameProbeDisposition::Refused => {
                return Err(engine_semantic_kernel_refusal(
                    format!(
                        "private-frame conditional-join certification refused without fallback: {error}"
                    ),
                    EnginePhase::Certification,
                    false,
                    false,
                ));
            }
        },
    }
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    match r2dec::CertifiedAggregateMemberSemanticCFunction::from_artifact(trusted) {
        Ok(function) => match function.render_certified_c() {
            Ok(output) => {
                return complete_engine_semantic_kernel_attempt(
                    control,
                    EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                        output,
                        structuring_executed: true,
                        semantic_kernel_render: Some(EngineSemanticKernelRender {
                            region:
                                EngineSemanticKernelRegion::AggregateMemberTerminalReturnFunction,
                            region_schema_version: function.schema_version(),
                            exact_obligation_closure: true,
                        }),
                        semantic_kernel_warnings: trace.into_warnings(),
                    }),
                );
            }
            Err(error) => trace.refused(EngineSemanticKernelProbe::Aggregate, &error.to_string()),
        },
        Err(error) => {
            trace.not_applicable(EngineSemanticKernelProbe::Aggregate, &error.to_string())
        }
    }
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    if prepared_artifact_has_source_aggregate_pointer(trusted.artifact()) {
        trace.not_applicable(
            EngineSemanticKernelProbe::Memory,
            "source aggregate pointer requires aggregate-member renderer",
        );
    } else {
        match r2dec::CertifiedMemorySemanticCFunction::from_artifact(trusted) {
            Ok(function) => match function.render_certified_c() {
                Ok(output) => {
                    return complete_engine_semantic_kernel_attempt(
                        control,
                        EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                            output,
                            structuring_executed: true,
                            semantic_kernel_render: Some(EngineSemanticKernelRender {
                                region:
                                    EngineSemanticKernelRegion::PlainRamMemoryTerminalReturnFunction,
                                region_schema_version: function.schema_version(),
                                exact_obligation_closure: true,
                            }),
                            semantic_kernel_warnings: trace.into_warnings(),
                        }),
                    );
                }
                Err(error) => trace.refused(EngineSemanticKernelProbe::Memory, &error.to_string()),
            },
            Err(error) => {
                trace.not_applicable(EngineSemanticKernelProbe::Memory, &error.to_string())
            }
        }
    }
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    match r2dec::CertifiedDirectCallReturnFunction::from_artifact(trusted) {
        Ok(function) => match function.render_certified_c() {
            Ok(output) => {
                return complete_engine_semantic_kernel_attempt(
                    control,
                    EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                        output,
                        structuring_executed: true,
                        semantic_kernel_render: Some(EngineSemanticKernelRender {
                            region: EngineSemanticKernelRegion::DirectCallTerminalReturnFunction,
                            region_schema_version: function.schema_version(),
                            exact_obligation_closure: true,
                        }),
                        semantic_kernel_warnings: trace.into_warnings(),
                    }),
                );
            }
            Err(error) => trace.refused(EngineSemanticKernelProbe::DirectCall, &error.to_string()),
        },
        Err(error) => {
            trace.not_applicable(EngineSemanticKernelProbe::DirectCall, &error.to_string())
        }
    }
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    match r2dec::CertifiedConditionalReturnFunction::from_artifact(trusted) {
        Ok(function) => match function.render_certified_c() {
            Ok(output) => {
                return complete_engine_semantic_kernel_attempt(
                    control,
                    EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                        output,
                        structuring_executed: true,
                        semantic_kernel_render: Some(EngineSemanticKernelRender {
                            region: EngineSemanticKernelRegion::ConditionalTerminalReturnFunction,
                            region_schema_version: function.schema_version(),
                            exact_obligation_closure: true,
                        }),
                        semantic_kernel_warnings: trace.into_warnings(),
                    }),
                );
            }
            Err(error) => trace.refused(EngineSemanticKernelProbe::Conditional, &error.to_string()),
        },
        Err(error) => {
            trace.not_applicable(EngineSemanticKernelProbe::Conditional, &error.to_string())
        }
    }
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    match r2dec::CertifiedGuardedReturnFunction::from_artifact(trusted) {
        Ok(function) => match function.render_certified_c() {
            Ok(output) => {
                return complete_engine_semantic_kernel_attempt(
                    control,
                    EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                        output,
                        structuring_executed: true,
                        semantic_kernel_render: Some(EngineSemanticKernelRender {
                            region: EngineSemanticKernelRegion::GuardedTerminalReturnFunction,
                            region_schema_version: function.schema_version(),
                            exact_obligation_closure: true,
                        }),
                        semantic_kernel_warnings: trace.into_warnings(),
                    }),
                );
            }
            Err(error) => trace.refused(EngineSemanticKernelProbe::Guard, &error.to_string()),
        },
        Err(error) => trace.not_applicable(EngineSemanticKernelProbe::Guard, &error.to_string()),
    }
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    match r2dec::CertifiedSwitchReturnFunction::from_artifact(trusted) {
        Ok(function) => match function.render_certified_c() {
            Ok(output) => {
                return complete_engine_semantic_kernel_attempt(
                    control,
                    EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                        output,
                        structuring_executed: true,
                        semantic_kernel_render: Some(EngineSemanticKernelRender {
                            region: EngineSemanticKernelRegion::SwitchTerminalReturnFunction,
                            region_schema_version: function.schema_version(),
                            exact_obligation_closure: true,
                        }),
                        semantic_kernel_warnings: trace.into_warnings(),
                    }),
                );
            }
            Err(error) => trace.refused(EngineSemanticKernelProbe::Switch, &error.to_string()),
        },
        Err(error) => trace.not_applicable(EngineSemanticKernelProbe::Switch, &error.to_string()),
    }
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    match r2dec::CertifiedLoopReturnFunction::from_artifact(trusted) {
        Ok(function) => match function.render_certified_c() {
            Ok(output) => {
                return complete_engine_semantic_kernel_attempt(
                    control,
                    EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                        output,
                        structuring_executed: true,
                        semantic_kernel_render: Some(EngineSemanticKernelRender {
                            region:
                                EngineSemanticKernelRegion::CarrierFreeLoopTerminalReturnFunction,
                            region_schema_version: function.schema_version(),
                            exact_obligation_closure: true,
                        }),
                        semantic_kernel_warnings: trace.into_warnings(),
                    }),
                );
            }
            Err(error) => trace.refused(EngineSemanticKernelProbe::Loop, &error.to_string()),
        },
        Err(error) => trace.not_applicable(EngineSemanticKernelProbe::Loop, &error.to_string()),
    }
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    match r2dec::CertifiedSemanticCFunction::from_artifact(trusted) {
        Ok(function) => match function.render_certified_c() {
            Ok(output) => {
                return complete_engine_semantic_kernel_attempt(
                    control,
                    EngineSemanticKernelAttempt::Rendered(EngineRenderedDecompile {
                        output,
                        structuring_executed: true,
                        semantic_kernel_render: Some(EngineSemanticKernelRender {
                            region: EngineSemanticKernelRegion::TerminalReturnBlock,
                            region_schema_version: function.schema_version(),
                            exact_obligation_closure: true,
                        }),
                        semantic_kernel_warnings: trace.into_warnings(),
                    }),
                );
            }
            Err(error) => trace.refused(EngineSemanticKernelProbe::Terminal, &error.to_string()),
        },
        Err(error) => trace.not_applicable(EngineSemanticKernelProbe::Terminal, &error.to_string()),
    }
    complete_engine_semantic_kernel_attempt(
        control,
        EngineSemanticKernelAttempt::NotApplicable(trace.into_warnings()),
    )
}

fn render_engine_decompile_request<C: r2ssa::SsaWorkControl>(
    request: &EngineDecompileRequest,
    control: &C,
    try_semantic_kernel: bool,
) -> Result<EngineRenderedDecompile, EngineRenderExecutionStop> {
    let semantic_kernel_warnings = if try_semantic_kernel {
        let (rendered, warnings) = resolve_engine_semantic_kernel_attempt(
            render_semantic_kernel_function(request, control)?,
        )?;
        if let Some(rendered) = rendered {
            return Ok(rendered);
        }
        warnings
    } else {
        poll_engine_render_control(control, EnginePhase::Rendering)?;
        Vec::new()
    };
    poll_engine_render_control(control, EnginePhase::Rendering)?;
    if let Some(output) = render_semantic_route(
        &request.function_name,
        request.function_facts(),
        &request.render_target,
    ) {
        poll_engine_render_control(control, EnginePhase::Rendering)?;
        return Ok(EngineRenderedDecompile {
            output,
            semantic_kernel_render: None,
            semantic_kernel_warnings,
            structuring_executed: false,
        });
    }

    let input = decompiler_input_for_engine_request(request);
    let output = r2dec::Decompiler::new(request.render_target.to_decompiler_config())
        .decompile_input_with_control(&input, control)
        .map_err(engine_render_stop_from_decompiler)?;
    if !output.trim().is_empty() {
        return Ok(EngineRenderedDecompile {
            output,
            semantic_kernel_render: None,
            semantic_kernel_warnings,
            structuring_executed: true,
        });
    }

    Ok(EngineRenderedDecompile {
        output: decompile_route_output_from_function_facts(
            &request.function_name,
            request.function_facts(),
        )
        .unwrap_or_default(),
        semantic_kernel_render: None,
        semantic_kernel_warnings,
        structuring_executed: false,
    })
}

fn decompiler_input_for_engine_request(request: &EngineDecompileRequest) -> r2dec::DecompilerInput {
    r2dec::DecompilerInput::new(request.source_owned_facts.clone())
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
    mut diagnostics: EngineDiagnostics,
) -> EngineDecompileResponse {
    let function_facts = refused_decompile_function_facts(function_name, reason);
    let output = decompile_route_output_from_function_facts(function_name, &function_facts)
        .expect("refused decompile response must stamp a fallback route");
    let route_diagnostics = decompile_diagnostics_from_function_facts(&function_facts);
    diagnostics.plan = route_diagnostics.plan;
    diagnostics.route_reason = route_diagnostics.route_reason;
    diagnostics.refusal = route_diagnostics.refusal;
    EngineDecompileResponse {
        output,
        function_facts,
        input_quality,
        metrics,
        diagnostics,
    }
}

fn refused_decompile_function_facts(function_name: &str, reason: &str) -> FunctionFacts {
    let output = artifact_guard_fallback_comment(function_name, reason);
    let route = r2types::DecompileRouteFacts {
        kind: r2types::DecompileRouteKind::FallbackComment,
        reason: Some(reason.to_string()),
        fallback_comment: Some(output),
        skip_runtime_type_inference: true,
        use_prepared_semantic_view: false,
    };
    FunctionFacts::default().with_decompile_route(route)
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
        r2ssa::SsaArtifact::for_decompile_with_interfaces_and_control(
            blocks,
            arch,
            source_snapshot.function_interface().cloned(),
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
    let (arch_name, _, _) = EngineRenderTarget::for_arch(request.arch.as_ref());
    let mut diagnostics = r2types::TypeWritebackDiagnostics::default();
    let local_structs = r2types::infer_local_struct_artifacts_from_prepared_ssa(
        &semantic_analysis.ssa_func,
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
            skip_runtime_type_inference: kind != r2types::DecompileRouteKind::Standard,
            use_prepared_semantic_view: kind == r2types::DecompileRouteKind::Standard,
        }
    }

    #[test]
    fn typed_external_context_owner_ignores_raw_fallback_and_preserves_typed_inputs() {
        let parsed = parse_typed_external_context(
            EngineExternalContextInput {
                schema_version: 2,
                dirty_epoch: 11,
                context_hash: 0xfeed,
                type_dirty_epoch: 13,
                signature: EngineExternalSignatureInput {
                    name: Some("target".to_string()),
                    ret_type: Some("int".to_string()),
                    callconv: Some("amd64".to_string()),
                    noreturn: false,
                    params: vec![EngineExternalSignatureParamInput {
                        name: Some("argc".to_string()),
                        ty: Some("int".to_string()),
                        cc_reg: Some("rdi".to_string()),
                    }],
                },
                vars: vec![EngineExternalVarInput {
                    kind: ENGINE_EXTERNAL_VAR_REGISTER,
                    name: Some("argc".to_string()),
                    ty: Some("int".to_string()),
                    reg: Some("rdi".to_string()),
                    is_arg: true,
                    ..EngineExternalVarInput::default()
                }],
                base_types: Vec::new(),
                callees: vec![EngineExternalCalleeInput {
                    call_addr: 0x401000,
                    addr: 0x402000,
                    name: Some("setlocale".to_string()),
                    linkage: ENGINE_EXTERNAL_LINKAGE_IMPORTED,
                    signature: EngineExternalSignatureInput {
                        name: Some("setlocale".to_string()),
                        ret_type: Some("char *".to_string()),
                        params: vec![EngineExternalSignatureParamInput {
                            name: Some("category".to_string()),
                            ty: Some("int".to_string()),
                            cc_reg: None,
                        }],
                        ..EngineExternalSignatureInput::default()
                    },
                }],
                assumptions_json: Some(
                    r#"{"assumptions":[{"subject":{"register":{"name":"rdi"}},"value":{"constant":{"value":4660}}}]}"#
                        .to_string(),
                ),
            },
            64,
        );

        assert_eq!(parsed.context_schema_version, Some(2));
        assert_eq!(parsed.type_dirty_epoch, Some(13));
        assert_eq!(parsed.callconv.as_deref(), Some("amd64"));
        assert_eq!(parsed.register_params[0].reg, "rdi");
        assert!(
            parsed.external_type_db.structs.is_empty(),
            "typed context parsing must not import raw fallback base types"
        );

        assert!(!parsed.callee_facts.contains_key(&4198400));
        let callee = parsed.callee_facts.get(&0x402000).expect("typed callee");
        assert_eq!(callee.name.as_deref(), Some("setlocale"));
        assert!(callee.linkage.authorizes_import_policy());
        assert_eq!(
            callee
                .signature
                .as_ref()
                .map(|signature| signature.params.len()),
            Some(1)
        );

        assert!(
            parsed
                .assumptions
                .items
                .iter()
                .any(|assumption| assumption.subject
                    == r2ssa::AssumptionSubject::Register {
                        name: "rdi".to_string()
                    })
        );
    }

    #[test]
    fn typed_external_context_empty_input_stays_empty_without_legacy_raw_context() {
        let parsed = parse_typed_external_context(EngineExternalContextInput::default(), 64);

        assert_eq!(parsed.context_schema_version, None);
        assert_eq!(parsed.context_hash, None);
        assert_eq!(parsed.current_signature, None);
        assert!(parsed.stack_slots.is_empty());
        assert!(parsed.external_type_db.structs.is_empty());
        assert!(parsed.external_type_db.unions.is_empty());
        assert!(parsed.external_type_db.enums.is_empty());
        assert!(parsed.callee_facts.is_empty());
    }

    #[test]
    fn typed_external_context_partial_input_does_not_fill_missing_groups_from_raw_json() {
        let parsed = parse_typed_external_context(
            EngineExternalContextInput {
                schema_version: 3,
                dirty_epoch: 0,
                context_hash: 0,
                type_dirty_epoch: 0,
                signature: EngineExternalSignatureInput::default(),
                vars: Vec::new(),
                base_types: Vec::new(),
                callees: Vec::new(),
                assumptions_json: None,
            },
            64,
        );

        assert_eq!(parsed.context_schema_version, Some(3));
        assert_eq!(parsed.callconv, None);
        assert_eq!(parsed.current_signature, None);
        assert!(
            parsed.stack_slots.is_empty(),
            "empty typed vars must stay empty instead of importing raw fallback vars"
        );
    }

    #[test]
    fn engine_arch_target_uses_effective_pointer_width_fallbacks() {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.addr_size = 0;
        arch.add_register(r2il::RegisterDef::new("rip", 0, 8));

        let (arch_name, ptr_bits) = engine_arch_target(Some(&arch));

        assert_eq!(arch_name, "x86-64");
        assert_eq!(ptr_bits, 64);
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

    fn source_snapshot_terminal_function()
    -> (Vec<R2ILBlock>, r2il::ArchSpec, Arc<EngineSourceSnapshot>) {
        let revision = b"production-terminal-revision";
        let mut arch = r2il::ArchSpec::new("production-terminal-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(r2il::Endianness::Little);
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rdi", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        arch.add_register(r2il::RegisterDef::new("rsi", 24, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new(
            revision.to_vec(),
            "test-register-abi",
            [r2ssa::SourceAbiParameterSpec::new(0, register(8))],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0),
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("source function interface");
        let snapshot = EngineSourceSnapshot::new(revision.to_vec(), Some(interface), Vec::new())
            .expect("source snapshot");
        let mut block = R2ILBlock::new(0x7200, 4);
        block.push(r2il::R2ILOp::IntAdd {
            dst: r2il::Varnode::unique(0x10, 8),
            a: r2il::Varnode::register(8, 8),
            b: r2il::Varnode::constant(1, 8),
        });
        block.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::unique(0x10, 8),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(16, 8),
        });
        (vec![block], arch, Arc::new(snapshot))
    }

    fn source_snapshot_memory_terminal_function()
    -> (Vec<R2ILBlock>, r2il::ArchSpec, Arc<EngineSourceSnapshot>) {
        let revision = b"production-memory-terminal-revision";
        let mut arch = r2il::ArchSpec::new("production-memory-terminal-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(r2il::Endianness::Little);
        arch.add_space(r2il::AddressSpace::ram(8));
        arch.add_register(r2il::RegisterDef::new("eax", 0, 4));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        let interface = r2ssa::SourceFunctionInterface::new(
            revision.to_vec(),
            "test-register-abi",
            Vec::<r2ssa::SourceAbiParameterSpec>::new(),
            r2ssa::SourceFunctionReturn::Register {
                storage: r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 4,
                },
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("source function interface");
        let snapshot = EngineSourceSnapshot::new(revision.to_vec(), Some(interface), Vec::new())
            .expect("source snapshot");
        let mut block = R2ILBlock::new(0x7280, 4);
        block.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::register(0, 4),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::constant(0x40, 8),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(16, 8),
        });
        (vec![block], arch, Arc::new(snapshot))
    }

    fn aggregate_member_test_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.alignment = 4;
        arch.add_register(r2il::RegisterDef::new("x0", 0, 8));
        arch.add_register(r2il::RegisterDef::new("w0", 0, 4));
        arch.add_register(r2il::RegisterDef::new("x1", 8, 8));
        arch.add_register(r2il::RegisterDef::new("w1", 8, 4));
        arch.add_register(r2il::RegisterDef::new("x4", 32, 8));
        arch.add_register(r2il::RegisterDef::new("w4", 32, 4));
        arch.add_register(r2il::RegisterDef::new("x30", 48, 8));
        arch.add_space(r2il::AddressSpace::ram(8));
        arch.set_memory_endianness(r2il::Endianness::Little);
        arch
    }

    fn aggregate_member_test_graph() -> r2ssa::SourceTypeGraph {
        r2ssa::SourceTypeGraph::new(
            [
                r2ssa::SourceType::new(
                    0,
                    r2ssa::SourceTypeKind::Struct { aggregate_id: 0 },
                    56 * 8,
                    32,
                ),
                r2ssa::SourceType::new(1, r2ssa::SourceTypeKind::SignedInteger, 32, 32),
                r2ssa::SourceType::new(
                    2,
                    r2ssa::SourceTypeKind::Pointer { target_type_id: 0 },
                    64,
                    64,
                ),
            ],
            [r2ssa::SourceAggregateLayout::new(
                0,
                0,
                56 * 8,
                32,
                "CosmeticAggregateName",
                (0..14).map(|index| {
                    r2ssa::SourceAggregateMember::new(
                        index,
                        1,
                        u64::from(index) * 32,
                        32,
                        format!("cosmetic_member_{index}"),
                    )
                }),
            )],
        )
        .expect("valid aggregate-member source graph")
    }

    fn source_snapshot_aggregate_member_load_return_function()
    -> (Vec<R2ILBlock>, r2il::ArchSpec, Arc<EngineSourceSnapshot>) {
        let revision = b"production-aggregate-member-load-revision";
        let register = |offset, size| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            "aapcs64",
            [r2ssa::SourceAbiParameterSpec::new(0, register(0, 8))],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(32, 4),
            },
            [],
            [r2ssa::SourceLogicalValue::new(
                2,
                r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64),
            )],
            Some(r2ssa::SourceLogicalValue::new(
                1,
                r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 32),
            )),
            Some(aggregate_member_test_graph()),
        )
        .expect("exact aggregate-member load interface");
        let snapshot = EngineSourceSnapshot::new(revision.to_vec(), Some(interface), Vec::new())
            .expect("aggregate-member load source snapshot");
        let mut block = R2ILBlock::new(0x7700, 4);
        block.push(r2il::R2ILOp::IntAdd {
            dst: r2il::Varnode::unique(0x10, 8),
            a: r2il::Varnode::register(0, 8),
            b: r2il::Varnode::constant(8, 8),
        });
        block.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::register(32, 4),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x10, 8),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(48, 8),
        });
        (
            vec![block],
            aggregate_member_test_arch(),
            Arc::new(snapshot),
        )
    }

    fn source_snapshot_aggregate_member_store_function()
    -> (Vec<R2ILBlock>, r2il::ArchSpec, Arc<EngineSourceSnapshot>) {
        let revision = b"production-aggregate-member-store-revision";
        let register = |offset, size| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
            revision.to_vec(),
            "aapcs64",
            [
                r2ssa::SourceAbiParameterSpec::new(0, register(0, 8)),
                r2ssa::SourceAbiParameterSpec::new(1, register(8, 8)),
            ],
            r2ssa::SourceFunctionReturn::Void,
            [],
            [
                r2ssa::SourceLogicalValue::new(
                    2,
                    r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64),
                ),
                r2ssa::SourceLogicalValue::new(
                    1,
                    r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::LowBits, 0, 32),
                ),
            ],
            None,
            Some(aggregate_member_test_graph()),
        )
        .expect("exact aggregate-member store interface");
        let snapshot = EngineSourceSnapshot::new(revision.to_vec(), Some(interface), Vec::new())
            .expect("aggregate-member store source snapshot");
        let mut block = R2ILBlock::new(0x7710, 4);
        block.push(r2il::R2ILOp::Subpiece {
            dst: r2il::Varnode::unique(0x18, 4),
            src: r2il::Varnode::register(8, 8),
            offset: 0,
        });
        block.push(r2il::R2ILOp::IntAdd {
            dst: r2il::Varnode::unique(0x20, 8),
            a: r2il::Varnode::register(0, 8),
            b: r2il::Varnode::constant(52, 8),
        });
        block.push(r2il::R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x20, 8),
            val: r2il::Varnode::unique(0x18, 4),
        });
        block.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(48, 8),
        });
        (
            vec![block],
            aggregate_member_test_arch(),
            Arc::new(snapshot),
        )
    }

    fn source_snapshot_direct_call_return_function()
    -> (Vec<R2ILBlock>, r2il::ArchSpec, Arc<EngineSourceSnapshot>) {
        let revision = b"production-direct-call-return-revision";
        let mut arch = r2il::ArchSpec::new("production-direct-call-return-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(r2il::Endianness::Little);
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rdi", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let function_interface = r2ssa::SourceFunctionInterface::new(
            revision.to_vec(),
            "caller-test-abi",
            [r2ssa::SourceAbiParameterSpec::new(0, register(8))],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0),
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("source function interface");
        let target = r2il::Varnode::constant(0x8600, 8);
        let call_interface = r2ssa::SourceCallSiteInterface::new(
            revision.to_vec(),
            r2ssa::SourceCallSiteIdentity::new(
                0x7500,
                1,
                r2ssa::CanonicalStorageId::from_varnode(&target),
            ),
            true,
            "callee-test-abi",
            [r2ssa::SourceCallArgumentSpec::new(0, register(8))],
            false,
            false,
            r2ssa::SourceCallResult::Void,
        )
        .expect("source callsite interface");
        let snapshot = EngineSourceSnapshot::new(
            revision.to_vec(),
            Some(function_interface),
            [call_interface],
        )
        .expect("source snapshot");
        let mut call = R2ILBlock::new(0x7500, 4);
        call.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(8, 8),
            src: r2il::Varnode::constant(0x11, 8),
        });
        call.push(r2il::R2ILOp::Call { target });
        let mut returned = R2ILBlock::new(0x7504, 4);
        returned.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::constant(7, 8),
        });
        returned.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(16, 8),
        });
        (vec![call, returned], arch, Arc::new(snapshot))
    }

    fn source_snapshot_conditional_return_function()
    -> (Vec<R2ILBlock>, r2il::ArchSpec, Arc<EngineSourceSnapshot>) {
        let revision = b"production-conditional-return-revision";
        let mut arch = r2il::ArchSpec::new("production-conditional-return-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(r2il::Endianness::Little);
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rdi", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new(
            revision.to_vec(),
            "test-register-abi",
            [r2ssa::SourceAbiParameterSpec::new(0, register(8))],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0),
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("source function interface");
        let snapshot = EngineSourceSnapshot::new(revision.to_vec(), Some(interface), Vec::new())
            .expect("source snapshot");

        let mut header = R2ILBlock::new(0x7300, 4);
        header.push(r2il::R2ILOp::IntNotEqual {
            dst: r2il::Varnode::unique(0x10, 1),
            a: r2il::Varnode::register(8, 8),
            b: r2il::Varnode::constant(0, 8),
        });
        header.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::ram(0x7320, 8),
            cond: r2il::Varnode::unique(0x10, 1),
        });
        let mut false_arm = R2ILBlock::new(0x7304, 4);
        false_arm.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::constant(0, 8),
        });
        false_arm.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(16, 8),
        });
        let mut true_arm = R2ILBlock::new(0x7320, 4);
        true_arm.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::constant(u64::MAX, 8),
        });
        true_arm.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(16, 8),
        });
        (vec![header, false_arm, true_arm], arch, Arc::new(snapshot))
    }

    fn source_snapshot_switch_return_function()
    -> (Vec<R2ILBlock>, r2il::ArchSpec, Arc<EngineSourceSnapshot>) {
        let revision = b"production-switch-return-revision";
        let mut arch = r2il::ArchSpec::new("production-switch-return-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(r2il::Endianness::Little);
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rdi", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        arch.add_register(r2il::RegisterDef::new("rsi", 24, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new(
            revision.to_vec(),
            "test-register-abi",
            [r2ssa::SourceAbiParameterSpec::new(0, register(8))],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0),
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("source function interface");
        let snapshot = EngineSourceSnapshot::new(revision.to_vec(), Some(interface), Vec::new())
            .expect("source snapshot");

        let mut header = R2ILBlock::new(0x7380, 4);
        header.push(r2il::R2ILOp::BranchInd {
            target: r2il::Varnode::register(8, 8),
        });
        header.set_switch_info(r2il::SwitchInfo {
            switch_addr: 0x7380,
            min_val: 1,
            max_val: 7,
            default_target: Some(0x73e0),
            cases: vec![
                r2il::SwitchCase {
                    value: 1,
                    target: 0x73a0,
                },
                r2il::SwitchCase {
                    value: 7,
                    target: 0x73c0,
                },
            ],
        });
        let arm = |addr, value| {
            let mut block = R2ILBlock::new(addr, 4);
            block.push(r2il::R2ILOp::Copy {
                dst: r2il::Varnode::register(0, 8),
                src: r2il::Varnode::constant(value, 8),
            });
            block.push(r2il::R2ILOp::Return {
                target: r2il::Varnode::register(16, 8),
            });
            block
        };
        (
            vec![header, arm(0x73a0, 11), arm(0x73c0, 22), arm(0x73e0, 33)],
            arch,
            Arc::new(snapshot),
        )
    }

    fn source_snapshot_carrier_free_loop_return_function()
    -> (Vec<R2ILBlock>, r2il::ArchSpec, Arc<EngineSourceSnapshot>) {
        let revision = b"production-carrier-free-loop-return-revision";
        let mut arch = r2il::ArchSpec::new("production-carrier-free-loop-return-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(r2il::Endianness::Little);
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("dil", 8, 1));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        arch.add_register(r2il::RegisterDef::new("sil", 24, 1));
        let register = |offset, size| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size,
        };
        let interface = r2ssa::SourceFunctionInterface::new(
            revision.to_vec(),
            "test-register-abi",
            [r2ssa::SourceAbiParameterSpec::new(0, register(8, 1))],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0, 8),
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("source function interface");
        let snapshot = EngineSourceSnapshot::new(revision.to_vec(), Some(interface), Vec::new())
            .expect("source snapshot");

        let mut preheader = R2ILBlock::new(0x7400, 4);
        preheader.push(r2il::R2ILOp::Branch {
            target: r2il::Varnode::ram(0x7410, 8),
        });
        let mut header = R2ILBlock::new(0x7410, 4);
        header.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::ram(0x7430, 8),
            cond: r2il::Varnode::register(8, 1),
        });
        let mut exit = R2ILBlock::new(0x7414, 4);
        exit.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::constant(0x2a, 8),
        });
        exit.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(16, 8),
        });
        let mut body = R2ILBlock::new(0x7430, 4);
        body.push(r2il::R2ILOp::Branch {
            target: r2il::Varnode::ram(0x7410, 8),
        });
        (
            vec![preheader, header, exit, body],
            arch,
            Arc::new(snapshot),
        )
    }

    fn assert_handmade_analysis_only(artifact: &r2ssa::SsaArtifact) {
        assert_ne!(
            artifact.provenance_kind(),
            r2ssa::SsaArtifactProvenanceKind::TrustedSource,
            "caller-authored blocks and interfaces must remain analysis-only"
        );
    }

    fn assert_handmade_engine_refusal(
        function_name: &str,
        function_addr: u64,
        blocks: Vec<R2ILBlock>,
        arch: r2il::ArchSpec,
        source_snapshot: Arc<EngineSourceSnapshot>,
        forbidden_output: &str,
    ) {
        let artifact = r2ssa::SsaArtifact::for_decompile_with_interfaces(
            &blocks,
            Some(&arch),
            source_snapshot.function_interface().cloned(),
            source_snapshot.call_site_interfaces().to_vec(),
        )
        .expect("handmade fixture remains analyzable");
        assert_handmade_analysis_only(&artifact);

        let response = EngineSession::new().decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: function_name.to_string(),
                    function_addr,
                    blocks,
                    arch: Some(arch),
                    source_snapshot: Some(source_snapshot),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        assert!(response.diagnostics.semantic_kernel_render.is_none());
        assert!(
            response.output.contains("r2dec residual:")
                || response.output.contains("r2dec fallback:")
        );
        assert!(!response.output.contains(forbidden_output));
    }

    #[test]
    fn handmade_terminal_fixture_refuses_certified_c() {
        let (blocks, arch, source_snapshot) = source_snapshot_terminal_function();
        assert_handmade_engine_refusal(
            "sym.production_terminal",
            0x7200,
            blocks,
            arch,
            source_snapshot,
            "certified_sub_7200",
        );
    }

    #[test]
    fn handmade_memory_terminal_fixture_refuses_certified_c() {
        let (blocks, arch, source_snapshot) = source_snapshot_memory_terminal_function();
        assert_handmade_engine_refusal(
            "sym.production_memory_terminal",
            0x7280,
            blocks,
            arch,
            source_snapshot,
            "certified_mem_sub_7280",
        );
    }

    #[test]
    fn handmade_aggregate_member_fixtures_refuse_certified_c() {
        let (load_blocks, load_arch, load_snapshot) =
            source_snapshot_aggregate_member_load_return_function();
        let prepared_load = r2ssa::SsaArtifact::for_decompile_with_interface(
            &load_blocks,
            Some(&load_arch),
            load_snapshot
                .function_interface()
                .cloned()
                .expect("aggregate load interface"),
        )
        .expect("prepared aggregate load");
        assert_handmade_analysis_only(&prepared_load);

        let load = EngineSession::new().decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: "sym.production_aggregate_member_load".to_string(),
                    function_addr: 0x7700,
                    blocks: load_blocks.clone(),
                    arch: Some(load_arch.clone()),
                    source_snapshot: Some(Arc::clone(&load_snapshot)),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        assert!(load.diagnostics.semantic_kernel_render.is_none());
        assert!(!load.output.contains("certified_aggregate_sub_7700"));

        let (store_blocks, store_arch, store_snapshot) =
            source_snapshot_aggregate_member_store_function();
        let store = EngineSession::new().decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: "sym.production_aggregate_member_store".to_string(),
                    function_addr: 0x7710,
                    blocks: store_blocks,
                    arch: Some(store_arch),
                    source_snapshot: Some(store_snapshot),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        assert!(store.diagnostics.semantic_kernel_render.is_none());
        assert!(!store.output.contains("certified_aggregate_sub_7710"));

        let mut indirect_address = load_blocks;
        indirect_address[0].ops.insert(
            1,
            r2il::R2ILOp::Copy {
                dst: r2il::Varnode::unique(0x11, 8),
                src: r2il::Varnode::unique(0x10, 8),
            },
        );
        let r2il::R2ILOp::Load { addr, .. } = &mut indirect_address[0].ops[2] else {
            panic!("aggregate near-miss load");
        };
        *addr = r2il::Varnode::unique(0x11, 8);
        let prepared_near_miss = r2ssa::SsaArtifact::for_decompile_with_interface(
            &indirect_address,
            Some(&load_arch),
            load_snapshot
                .function_interface()
                .cloned()
                .expect("aggregate near-miss interface"),
        )
        .expect("prepared aggregate near miss");
        assert_handmade_analysis_only(&prepared_near_miss);
        let refused = EngineSession::new().decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: "sym.production_aggregate_member_near_miss".to_string(),
                    function_addr: 0x7700,
                    blocks: indirect_address,
                    arch: Some(load_arch),
                    source_snapshot: Some(load_snapshot),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        // The function is rendered now rather than refused wholesale, so the
        // claim under test is that the output never presents itself as
        // certified: it carries a proof marker and none of the certified
        // aggregate or memory names.
        assert!(
            (refused.output.contains("r2dec residual:")
                || refused.output.contains("r2dec fallback:")
                || refused
                    .output
                    .contains("r2dec proof: rendered without kernel certification"))
                && !refused.output.contains("certified_aggregate_sub_7700")
                && !refused.output.contains("certified_mem_sub_7700"),
            "non-direct aggregate address must not downgrade to generic memory C:\n{}",
            refused.output
        );
        assert!(refused.diagnostics.semantic_kernel_render.is_none());
    }

    #[test]
    fn handmade_direct_call_return_fixture_refuses_certified_c() {
        let (blocks, arch, source_snapshot) = source_snapshot_direct_call_return_function();
        let response = EngineSession::new().decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: "sym.production_direct_call_return".to_string(),
                    function_addr: 0x7500,
                    blocks: blocks.clone(),
                    arch: Some(arch.clone()),
                    source_snapshot: Some(Arc::clone(&source_snapshot)),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        assert!(response.diagnostics.semantic_kernel_render.is_none());
        assert!(!response.output.contains("certified_call_sub_7500"));

        let missing_callsite = Arc::new(
            EngineSourceSnapshot::new(
                source_snapshot.revision_identity().to_vec(),
                source_snapshot.function_interface().cloned(),
                Vec::new(),
            )
            .expect("snapshot without exact callsite interface"),
        );
        let refused = EngineSession::new().decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: "sym.production_direct_call_return".to_string(),
                    function_addr: 0x7500,
                    blocks,
                    arch: Some(arch),
                    source_snapshot: Some(missing_callsite),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        assert!(
            (refused.output.contains("r2dec residual:")
                || refused.output.contains("r2dec fallback:"))
                && !refused.output.contains("certified_call_sub_7500"),
            "missing callsite authority must fail closed:\n{}",
            refused.output
        );
        assert!(refused.diagnostics.semantic_kernel_render.is_none());
    }

    #[test]
    fn handmade_conditional_return_fixture_refuses_certified_c() {
        let (blocks, arch, source_snapshot) = source_snapshot_conditional_return_function();
        assert_handmade_engine_refusal(
            "sym.production_conditional_return",
            0x7300,
            blocks,
            arch,
            source_snapshot,
            "certified_sub_7300",
        );
    }

    #[test]
    fn handmade_switch_return_fixture_refuses_certified_c() {
        let (blocks, arch, source_snapshot) = source_snapshot_switch_return_function();
        let response = EngineSession::new().decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: "sym.production_switch_return".to_string(),
                    function_addr: 0x7380,
                    blocks: blocks.clone(),
                    arch: Some(arch.clone()),
                    source_snapshot: Some(Arc::clone(&source_snapshot)),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        assert!(response.diagnostics.semantic_kernel_render.is_none());
        assert!(!response.output.contains("certified_sub_7380"));

        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let wrong_interface = r2ssa::SourceFunctionInterface::new(
            source_snapshot.revision_identity().to_vec(),
            "test-register-abi",
            [r2ssa::SourceAbiParameterSpec::new(0, register(24))],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0),
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("wrong selector interface");
        let wrong_storage = Arc::new(
            EngineSourceSnapshot::new(
                source_snapshot.revision_identity().to_vec(),
                Some(wrong_interface),
                Vec::new(),
            )
            .expect("wrong selector snapshot"),
        );
        let missing_interface = Arc::new(
            EngineSourceSnapshot::new(
                source_snapshot.revision_identity().to_vec(),
                None,
                Vec::new(),
            )
            .expect("snapshot without function interface"),
        );
        for source_snapshot in [missing_interface, wrong_storage] {
            let refused = EngineSession::new().decompile_function_from_input(
                EngineFunctionDecompileRequestInput::single_function(
                    EngineFunctionInput {
                        function_name: "sym.production_switch_return".to_string(),
                        function_addr: 0x7380,
                        blocks: blocks.clone(),
                        arch: Some(arch.clone()),
                        source_snapshot: Some(source_snapshot),
                        semantic_metadata_enabled: true,
                    },
                    Some(64),
                    r2types::ParsedExternalContext::default(),
                ),
            );
            assert!(
                (refused.output.contains("r2dec residual:")
                    || refused.output.contains("r2dec fallback:"))
                    && !refused.output.contains("certified_sub_7380"),
                "missing or wrong selector authority must fail closed:\n{}",
                refused.output
            );
            assert!(refused.diagnostics.semantic_kernel_render.is_none());
        }
    }

    #[test]
    fn handmade_carrier_free_loop_return_fixture_refuses_certified_c() {
        let (blocks, arch, source_snapshot) = source_snapshot_carrier_free_loop_return_function();
        let response = EngineSession::new().decompile_function_from_input(
            EngineFunctionDecompileRequestInput::single_function(
                EngineFunctionInput {
                    function_name: "sym.production_carrier_free_loop_return".to_string(),
                    function_addr: 0x7400,
                    blocks: blocks.clone(),
                    arch: Some(arch.clone()),
                    source_snapshot: Some(Arc::clone(&source_snapshot)),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
            ),
        );
        assert!(response.diagnostics.semantic_kernel_render.is_none());
        assert!(!response.output.contains("certified_sub_7400"));

        let register = |offset, size| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size,
        };
        let wrong_interface = r2ssa::SourceFunctionInterface::new(
            source_snapshot.revision_identity().to_vec(),
            "test-register-abi",
            [r2ssa::SourceAbiParameterSpec::new(0, register(24, 1))],
            r2ssa::SourceFunctionReturn::Register {
                storage: register(0, 8),
            },
            Vec::<r2ssa::SourceStackSlotSpec>::new(),
        )
        .expect("wrong loop condition interface");
        let wrong_storage = Arc::new(
            EngineSourceSnapshot::new(
                source_snapshot.revision_identity().to_vec(),
                Some(wrong_interface),
                Vec::new(),
            )
            .expect("wrong loop condition snapshot"),
        );
        let missing_interface = Arc::new(
            EngineSourceSnapshot::new(
                source_snapshot.revision_identity().to_vec(),
                None,
                Vec::new(),
            )
            .expect("snapshot without loop function interface"),
        );
        for source_snapshot in [missing_interface, wrong_storage] {
            let refused = EngineSession::new().decompile_function_from_input(
                EngineFunctionDecompileRequestInput::single_function(
                    EngineFunctionInput {
                        function_name: "sym.production_carrier_free_loop_return".to_string(),
                        function_addr: 0x7400,
                        blocks: blocks.clone(),
                        arch: Some(arch.clone()),
                        source_snapshot: Some(source_snapshot),
                        semantic_metadata_enabled: true,
                    },
                    Some(64),
                    r2types::ParsedExternalContext::default(),
                ),
            );
            assert!(
                (refused.output.contains("r2dec residual:")
                    || refused.output.contains("r2dec fallback:"))
                    && !refused.output.contains("certified_sub_7400"),
                "missing or wrong loop condition authority must fail closed:\n{}",
                refused.output
            );
            assert!(refused.diagnostics.semantic_kernel_render.is_none());
        }
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
        .with_return_address_storage(register(0x10))
        .and_then(|interface| interface.with_stack_pointer_storage(register(0x18)))
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
            target: r2il::Varnode::register(0x10, 8),
        };
        let mut arch = x86_64_result_arch();
        arch.add_register(r2il::RegisterDef::new("rip", 0x10, 8));
        arch.add_register(r2il::RegisterDef::new("rsp", 0x18, 8));
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
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rsp", 0x28, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 0x30, 8));
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
        arch
    }

    fn x86_32_runtime_scope_arch() -> r2il::ArchSpec {
        let mut arch = windows_x64_runtime_scope_arch();
        arch.name = "x86".to_string();
        arch.addr_size = 4;
        arch
    }

    fn x86_64_generic_name_runtime_scope_arch() -> r2il::ArchSpec {
        let mut arch = windows_x64_runtime_scope_arch();
        arch.name = "x86".to_string();
        arch.addr_size = 8;
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
        let blocks = const_return_blocks(0x614000, 7);
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"controlled-r2dec-source".to_vec(),
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
    fn r2dec_inner_stops_map_to_engine_refusals_without_native_output() {
        let session = EngineSession::new();
        let request = controlled_r2dec_render_request();
        let decompiler_input = decompiler_input_for_engine_request(&request);
        let legacy_output = r2dec::Decompiler::new(request.render_target.to_decompiler_config())
            .decompile_input(&decompiler_input);
        let counting = CountingRenderControl::default();
        let controlled = session.decompile_with_r2dec_control_and_kernel_policy(
            request.clone(),
            &counting,
            false,
        );
        assert_eq!(controlled.output, legacy_output);
        let total_polls = counting.polls.get();
        assert!(total_polls > 3, "r2dec pipeline must expose inner polls");

        let mut observed = HashMap::new();
        for stop_at in 1..=total_polls {
            let stop = StopRenderAtPoll::new(stop_at, r2ssa::SsaExecutionStopReason::Cancelled);
            let response = session.decompile_with_r2dec_control_and_kernel_policy(
                request.clone(),
                &stop,
                false,
            );
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
            let response = session.decompile_with_r2dec_control_and_kernel_policy(
                request.clone(),
                &stop,
                false,
            );
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
                Some(expected_reason.as_str())
            );
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
                );
                assert_eq!(mapped.phase, engine_phase);
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
    fn semantic_kernel_trace_preserves_order_and_classification_before_later_success() {
        let mut trace = EngineSemanticKernelTrace::default();
        trace.not_applicable(
            EngineSemanticKernelProbe::PrivateFrame,
            "private-frame constructor mismatch",
        );
        trace.not_applicable(
            EngineSemanticKernelProbe::Aggregate,
            "aggregate constructor mismatch",
        );
        trace.refused(EngineSemanticKernelProbe::Memory, "memory renderer refusal");

        let warnings = trace.into_warnings();
        assert_eq!(
            warnings,
            vec![
                "semantic-kernel:private-frame:not_applicable:private-frame constructor mismatch",
                "semantic-kernel:aggregate:not_applicable:aggregate constructor mismatch",
                "semantic-kernel:memory:refused:memory renderer refusal",
            ],
            "an earlier probe trace must survive a later successful probe"
        );
    }

    #[test]
    fn private_frame_probe_continues_only_when_no_exact_join_exists() {
        use r2dec::PrivateFrameConditionalJoinFunctionError as Error;

        assert_eq!(
            classify_private_frame_probe_error(&Error::MissingExactJoin),
            EnginePrivateFrameProbeDisposition::NotApplicable
        );
        for error in [
            Error::MachineProjection(r2ssa::MachineBuildError::UntrustedArtifactProvenance),
            Error::MultipleExactJoins,
            Error::NonEntryExactJoin,
        ] {
            assert_eq!(
                classify_private_frame_probe_error(&error),
                EnginePrivateFrameProbeDisposition::Refused,
                "{error} must stop before any lower semantic or legacy route"
            );
        }
    }

    #[test]
    fn semantic_kernel_trace_bounds_entries_and_reason_characters() {
        let probes = [
            EngineSemanticKernelProbe::PrivateFrame,
            EngineSemanticKernelProbe::Aggregate,
            EngineSemanticKernelProbe::Memory,
            EngineSemanticKernelProbe::DirectCall,
            EngineSemanticKernelProbe::Conditional,
            EngineSemanticKernelProbe::Switch,
            EngineSemanticKernelProbe::Loop,
            EngineSemanticKernelProbe::Terminal,
        ];
        let mut trace = EngineSemanticKernelTrace::default();
        let long_reason = format!("{}\nignored", "x".repeat(600));
        for probe in probes {
            trace.not_applicable(probe, &long_reason);
        }
        trace.refused(EngineSemanticKernelProbe::Terminal, "ninth entry");

        let warnings = trace.into_warnings();
        assert_eq!(warnings.len(), ENGINE_SEMANTIC_KERNEL_TRACE_LIMIT);
        assert!(
            warnings
                .iter()
                .all(|warning| warning.starts_with(ENGINE_SEMANTIC_KERNEL_WARNING_TAG))
        );
        assert!(warnings.iter().all(|warning| !warning.contains('\n')));
        let reason = warnings[0]
            .rsplit_once(':')
            .map(|(_, reason)| reason)
            .expect("tagged reason");
        assert_eq!(
            reason.chars().count(),
            ENGINE_SEMANTIC_KERNEL_REASON_CHAR_LIMIT
        );
    }

    #[test]
    fn semantic_kernel_region_schema_table_tracks_exact_r2dec_contracts() {
        for (region, contract, expected_wire) in [
            (
                EngineSemanticKernelRegion::TerminalReturnBlock,
                r2dec::CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
                4,
            ),
            (
                EngineSemanticKernelRegion::AggregateMemberTerminalReturnFunction,
                r2dec::CERTIFIED_AGGREGATE_MEMBER_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
                6,
            ),
            (
                EngineSemanticKernelRegion::PlainRamMemoryTerminalReturnFunction,
                r2dec::CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
                4,
            ),
            (
                EngineSemanticKernelRegion::DirectCallTerminalReturnFunction,
                r2dec::CERTIFIED_DIRECT_CALL_RETURN_FUNCTION_SCHEMA_VERSION,
                3,
            ),
            (
                EngineSemanticKernelRegion::PrivateFrameConditionalJoinFunction,
                r2dec::CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_FUNCTION_SCHEMA_VERSION,
                1,
            ),
            (
                EngineSemanticKernelRegion::ConditionalTerminalReturnFunction,
                r2dec::CERTIFIED_CONDITIONAL_RETURN_FUNCTION_SCHEMA_VERSION,
                3,
            ),
            (
                EngineSemanticKernelRegion::SwitchTerminalReturnFunction,
                r2dec::CERTIFIED_SWITCH_RETURN_FUNCTION_SCHEMA_VERSION,
                3,
            ),
            (
                EngineSemanticKernelRegion::CarrierFreeLoopTerminalReturnFunction,
                r2dec::CERTIFIED_LOOP_RETURN_FUNCTION_SCHEMA_VERSION,
                3,
            ),
        ] {
            assert_eq!(contract, expected_wire);
            assert_eq!(region.current_schema_version(), expected_wire);
        }
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
    fn function_identity_rejects_raw_import_name_summary_family() {
        let identity = EngineFunctionIdentity::with_aliases(
            0x401000,
            "sym.imp.memcpy",
            "sym.imp.memcpy",
            ["fcn.00401000", "memcpy"],
        );

        assert!(
            !identity.has_summary_family(),
            "raw import aliases must not create evidence-backed summary-family applicability"
        );
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

        assert!(!identity.has_summary_family());
        assert_eq!(identity.summary_probe_name(), "fcn.00008b50");
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
        assert_eq!(
            plan.runtime_copy_targets,
            vec![0x3000],
            "runtime-copy role is still reported for imported memcpy calls"
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

        assert_eq!(plan.registration_targets, vec![0x4100]);
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
                linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                semantic_summary: None,
                resolved_target: Some(0x4500),
                target_materialized: true,
                target_metrics: Some(small_interproc_target_metrics()),
            },
        ]);

        assert!(
            plan.registration_targets.is_empty(),
            "runtime registration must require typed imported linkage"
        );
        assert!(
            plan.runtime_copy_targets.is_empty(),
            "runtime copy must require typed imported linkage or explicit modeled summary evidence"
        );
        assert_eq!(
            plan.queued_targets,
            vec![0x4400, 0x4500],
            "name-only runtime-looking helpers should stay on the native helper queue"
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
        let snapshot = test_source_snapshot("sym.runtime_seed/rev1");
        let analysis =
            build_engine_analysis_from_parts("sym.runtime_seed", &[block], Some(&arch), &snapshot)
                .expect("analysis");

        assert_eq!(
            interproc_runtime_registration_targets(&analysis, Some(&arch), &[0x1800_1000]),
            vec![0x1400_3d0f],
            "handler comes from the canonical Windows x64 arg1 observation"
        );
        let generic_x86_64 = x86_64_generic_name_runtime_scope_arch();
        assert_eq!(
            interproc_runtime_registration_targets(
                &analysis,
                Some(&generic_x86_64),
                &[0x1800_1000]
            ),
            vec![0x1400_3d0f],
            "64-bit x86 should be accepted even when the arch name omits a 64 suffix"
        );
        assert!(
            interproc_runtime_registration_targets(&analysis, Some(&arch), &[0x1800_2000])
                .is_empty(),
            "non-registration callees must not expand symbolic scope"
        );
    }

    #[test]
    fn runtime_registration_scope_is_gated_to_windows_x64() {
        let arch = windows_x64_runtime_scope_arch();
        let mut block = R2ILBlock::new(0x5000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: runtime_reg(16, 8),
            src: r2il::Varnode::constant(0x1400_3d0f, 8),
        });
        block.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(0x1800_1000, 8),
        });
        let snapshot = test_source_snapshot("sym.runtime_seed/gated/rev1");
        let analysis =
            build_engine_analysis_from_parts("sym.runtime_seed", &[block], Some(&arch), &snapshot)
                .expect("analysis");

        assert!(
            interproc_runtime_registration_targets(&analysis, None, &[0x1800_1000]).is_empty(),
            "missing architecture must not enable Windows runtime scope expansion"
        );
        let x86_32 = x86_32_runtime_scope_arch();
        assert!(
            interproc_runtime_registration_targets(&analysis, Some(&x86_32), &[0x1800_1000])
                .is_empty(),
            "32-bit x86 must not enable Windows x64 runtime scope expansion"
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
        let snapshot = test_source_snapshot("sym.runtime_copy/rev1");
        let analysis =
            build_engine_analysis_from_parts("sym.runtime_copy", &[block], Some(&arch), &snapshot)
                .expect("analysis");

        assert_eq!(
            interproc_runtime_materialized_sources(&analysis, Some(&arch), &[0x1800_2000]),
            vec![EngineRuntimeMaterializedSource {
                addr: 0x9000,
                size: 0x40
            }],
            "duplicate copy observations must collapse to the maximum materialized size"
        );
        let x86_32 = x86_32_runtime_scope_arch();
        assert!(
            interproc_runtime_materialized_sources(&analysis, Some(&x86_32), &[0x1800_2000])
                .is_empty(),
            "unsupported architectures must not report materialized runtime sources even when call args are otherwise valid"
        );
    }

    #[test]
    fn runtime_materialized_sources_reject_non_code_and_zero_size_inputs() {
        let arch = windows_x64_runtime_scope_arch();
        let mut block = R2ILBlock::new(0x6000, 4);
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
        let snapshot = test_source_snapshot("sym.runtime_copy/rejected/rev1");
        let analysis =
            build_engine_analysis_from_parts("sym.runtime_copy", &[block], Some(&arch), &snapshot)
                .expect("analysis");

        assert!(
            interproc_runtime_materialized_sources(&analysis, Some(&arch), &[0x1800_2000])
                .is_empty(),
            "runtime materialization needs both a code-like source address and a nonzero size"
        );
        let x86_32 = x86_32_runtime_scope_arch();
        assert!(
            interproc_runtime_materialized_sources(&analysis, Some(&x86_32), &[0x1800_2000])
                .is_empty(),
            "32-bit x86 must not enable Windows x64 materialized-source collection"
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

        let response = session.symbolic_paths(EngineSymbolicPathsRequest {
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
            Err(r2sym::SymExecutionStopReason::Cancelled)
        ));
    }

    #[test]
    fn engine_conditions_symbolic_scope_with_root_assumptions() {
        let blocks = symbolic_register_branch_blocks(0x501000);
        let prepared = Arc::new(r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared"));
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
        let prepared = Arc::new(r2ssa::SsaArtifact::for_symbolic(&blocks, None).expect("prepared"));
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

        let response = session.symbolic_summary(EngineSymbolicSummaryRequest {
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
        });

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
}
