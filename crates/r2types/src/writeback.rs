use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::{Hash, Hasher};

use r2ssa::{
    FunctionSemanticSummary, InterprocSummarySet, SSABlock, SSAOp, SSAVar, SummaryArgEffect,
    SummaryMemoryEffect, SummaryMemoryEffectKind, SummaryMemoryRegion, SummaryReturnRelation,
};

use crate::context::{
    ExternalStackBase, ExternalStackSlotRole, ExternalStackVarSpec, ParsedExternalContext,
    StackSlotKey, apply_main_signature_override, canonical_main_signature_spec,
    is_generic_arg_name, stack_slots_from_legacy_external_stack_vars,
};
use crate::convert::CTypeLike;
use crate::external::{
    ExternalField, ExternalStruct, ExternalTypeDb, ExternalUnion, normalize_external_type_name,
};
use crate::facts::{
    ArrayIndexBase, ArrayIndexCertificate, CalleeAllocationEffect, CalleeArgEffect,
    CalleeAtomicEffect, CalleeAtomicOp, CalleeAtomicOrdering, CalleeFact, CalleeLifetimeEffect,
    CalleeLifetimeOp, CalleeMemoryEffect, CalleeMemoryEffectKind, CalleeMemoryLocation,
    CalleeMemoryRange, CalleeMemoryRegion, CalleeModelPolicyEvidence, CalleeReturnRelation,
    CalleeSyncEffect, CalleeSyncOp, CalleeTransferEffect, CalleeTransferLength, FunctionParamSpec,
    FunctionSignatureProjection, FunctionSignatureSpec, FunctionTypeFactInputs, FunctionTypeFacts,
    InterprocFactDiagnostics, LocalFieldAccessFact, OutParamCertificate,
    OutParamCertificateEvidence, OutParamCertificateSource, SignatureCertificate,
    SignatureCertificateSource, SignatureProjectionResult, SignatureProjectionSource,
    VisibleBinding, VisibleBindingKind, parse_type_like_spec,
};
use crate::function_facts::{FunctionFacts, InterprocSummaryView};
use crate::model::Signedness;
use crate::prepare::recover_vars_arch_profile;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WritebackSource {
    LocalInferred,
    SignatureRegistry,
    ExistingState,
    ExternalTypeDb,
    DataflowRanked,
}

impl WritebackSource {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::LocalInferred => "local_inferred",
            Self::SignatureRegistry => "signature_registry",
            Self::ExistingState => "existing_state",
            Self::ExternalTypeDb => "external_type_db",
            Self::DataflowRanked => "dataflow_ranked",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WritebackEvidence {
    SsaVarRecovery,
    ExternalSignatureCurrent,
    CanonicalMainSignature,
    SsaFieldOffsetPattern,
    ExistingStackType,
    ExternalStackAnnotation,
    ExternalStackName,
    ExternalParamName,
}

impl WritebackEvidence {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::SsaVarRecovery => "ssa-var-recovery",
            Self::ExternalSignatureCurrent => "afcfj-current",
            Self::CanonicalMainSignature => "canonical-main-signature",
            Self::SsaFieldOffsetPattern => "ssa-field-offset-pattern",
            Self::ExistingStackType => "afvj-existing-type",
            Self::ExternalStackAnnotation => "afvj-stack-annotation",
            Self::ExternalStackName => "stack-var-name-from-afvj",
            Self::ExternalParamName => "afcfj-param-name",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructDeclSource {
    LocalInferred,
    ExternalTypeDb,
}

impl StructDeclSource {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::LocalInferred => "local_inferred",
            Self::ExternalTypeDb => "external_type_db",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct InferredSignatureParam {
    pub name: String,
    pub param_type: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferredSignature {
    pub function_name: String,
    pub signature: String,
    pub ret_type: String,
    pub params: Vec<InferredSignatureParam>,
    pub callconv: String,
    pub arch: String,
    pub confidence: u8,
    pub callconv_confidence: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RecoveredVariable {
    pub name: String,
    pub kind: String,
    pub delta: i64,
    #[serde(rename = "type")]
    pub var_type: String,
    pub isarg: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reg: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructFieldCandidate {
    pub name: String,
    pub offset: u64,
    pub field_type: String,
    pub confidence: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDeclCandidate {
    pub name: String,
    pub decl: String,
    pub confidence: u8,
    pub source: StructDeclSource,
    pub fields: Vec<StructFieldCandidate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobalTypeLinkCandidate {
    pub addr: u64,
    pub target_type: String,
    pub confidence: u8,
    pub source: WritebackSource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarTypeCandidate {
    pub name: String,
    pub kind: String,
    pub delta: i64,
    pub var_type: String,
    pub isarg: bool,
    pub reg: Option<String>,
    pub size: u32,
    pub confidence: u8,
    pub source: WritebackSource,
    pub evidence: Vec<WritebackEvidence>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarRenameCandidate {
    pub name: String,
    pub target_name: String,
    pub confidence: u8,
    pub source: WritebackSource,
    pub evidence: Vec<WritebackEvidence>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypeWritebackDiagnostics {
    pub conflicts: Vec<String>,
    pub warnings: Vec<String>,
    pub solver_warnings: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LocalStructArtifacts {
    pub struct_decls: Vec<StructDeclCandidate>,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeWritebackPlan {
    pub signature: InferredSignature,
    pub var_type_candidates: Vec<VarTypeCandidate>,
    pub var_rename_candidates: Vec<VarRenameCandidate>,
    pub struct_decls: Vec<StructDeclCandidate>,
    pub global_type_links: Vec<GlobalTypeLinkCandidate>,
    pub diagnostics: TypeWritebackDiagnostics,
}

pub const MATERIALIZED_VAR_MUTATION_MIN_CONFIDENCE: u8 = 95;
pub const TYPE_WRITEBACK_TYPE_MIN_CONFIDENCE_DEFAULT: u8 = 85;
pub const TYPE_WRITEBACK_RENAME_MIN_CONFIDENCE_DEFAULT: u8 = 93;
pub const TYPE_WRITEBACK_STRUCT_MIN_CONFIDENCE_DEFAULT: u8 = 85;
pub const SIGNATURE_WRITEBACK_MAX_BLOCKS: usize = 200;
pub const SIGNATURE_WRITEBACK_MIN_CONFIDENCE: u8 = 70;
pub const CALLCONV_WRITEBACK_MIN_CONFIDENCE: u8 = 80;
const TYPE_WRITEBACK_AGGRESSIVE_TYPE_DELTA: u8 = 10;
const TYPE_WRITEBACK_AGGRESSIVE_RENAME_DELTA: u8 = 8;
const TYPE_WRITEBACK_OFF_THRESHOLD: u8 = 101;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeWritebackMutationBudget {
    pub global_max_links: usize,
    pub max_type_decls: usize,
    pub max_mutations: usize,
}

impl TypeWritebackMutationBudget {
    pub fn new(global_max_links: usize, max_type_decls: usize, max_mutations: usize) -> Self {
        Self {
            global_max_links: global_max_links.max(1),
            max_type_decls: max_type_decls.max(1),
            max_mutations: max_mutations.max(1),
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TypeWritebackApplyMode {
    Off,
    #[default]
    Balanced,
    Aggressive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub struct TypeWritebackApplyPolicy {
    pub mode: TypeWritebackApplyMode,
    pub type_min_confidence: u8,
    pub rename_min_confidence: u8,
    pub struct_min_confidence: u8,
}

impl Default for TypeWritebackApplyPolicy {
    fn default() -> Self {
        Self::balanced()
    }
}

impl TypeWritebackApplyPolicy {
    pub fn balanced() -> Self {
        Self {
            mode: TypeWritebackApplyMode::Balanced,
            type_min_confidence: TYPE_WRITEBACK_TYPE_MIN_CONFIDENCE_DEFAULT,
            rename_min_confidence: TYPE_WRITEBACK_RENAME_MIN_CONFIDENCE_DEFAULT,
            struct_min_confidence: TYPE_WRITEBACK_STRUCT_MIN_CONFIDENCE_DEFAULT,
        }
    }

    pub fn aggressive() -> Self {
        Self {
            mode: TypeWritebackApplyMode::Aggressive,
            ..Self::balanced()
        }
    }

    pub fn off() -> Self {
        Self {
            mode: TypeWritebackApplyMode::Off,
            ..Self::balanced()
        }
    }

    pub fn effective_threshold(self, base: u8, aggressive_delta: u8) -> u8 {
        match self.mode {
            TypeWritebackApplyMode::Off => TYPE_WRITEBACK_OFF_THRESHOLD,
            TypeWritebackApplyMode::Balanced => base.clamp(1, 100),
            TypeWritebackApplyMode::Aggressive => {
                base.saturating_sub(aggressive_delta).clamp(1, 100)
            }
        }
    }

    pub fn mutation_min_confidence(self, kind: TypeWritebackMutationKind) -> u8 {
        match kind {
            TypeWritebackMutationKind::TypeDecl => self.effective_threshold(
                self.struct_min_confidence,
                TYPE_WRITEBACK_AGGRESSIVE_TYPE_DELTA,
            ),
            TypeWritebackMutationKind::VarRename => self.effective_threshold(
                self.rename_min_confidence,
                TYPE_WRITEBACK_AGGRESSIVE_RENAME_DELTA,
            ),
            TypeWritebackMutationKind::Var
            | TypeWritebackMutationKind::VarType
            | TypeWritebackMutationKind::TypeLink => self.effective_threshold(
                self.type_min_confidence,
                TYPE_WRITEBACK_AGGRESSIVE_TYPE_DELTA,
            ),
            TypeWritebackMutationKind::Signature
            | TypeWritebackMutationKind::Callconv
            | TypeWritebackMutationKind::Xref
            | TypeWritebackMutationKind::Comment
            | TypeWritebackMutationKind::Flag => 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TypeWritebackMutationKind {
    Signature,
    Callconv,
    Var,
    VarRename,
    VarType,
    Xref,
    Comment,
    Flag,
    TypeDecl,
    TypeLink,
}

impl TypeWritebackMutationKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Signature => "signature",
            Self::Callconv => "callconv",
            Self::Var => "var",
            Self::VarRename => "var_rename",
            Self::VarType => "var_type",
            Self::Xref => "xref",
            Self::Comment => "comment",
            Self::Flag => "flag",
            Self::TypeDecl => "type_decl",
            Self::TypeLink => "type_link",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct TypeWritebackMutation {
    pub kind: TypeWritebackMutationKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ret_type: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub params: Vec<InferredSignatureParam>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub callconv: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub old_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reg: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none", rename = "type")]
    pub type_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_materialization_key: Option<String>,
    #[serde(skip_serializing_if = "bool_is_false")]
    pub type_materialization_required: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub addr: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub size: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub delta: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub var_kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_arg: Option<bool>,
    pub confidence: u8,
    pub source: String,
    pub evidence: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize)]
pub struct TypeWritebackMutationPlan {
    pub apply_policy: TypeWritebackApplyPolicy,
    pub mutations: Vec<TypeWritebackMutation>,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeWritebackAuthorityReport {
    pub mutation_plan: TypeWritebackMutationPlan,
    pub signature_render_authorized: bool,
    pub signature_writeback: SignatureWritebackDecision,
    pub signature_action_decision: SignatureWritebackActionDecision,
    pub callconv_action_decision: SignatureWritebackActionDecision,
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum TypeWritebackApplyDecision {
    Apply = 0,
    SkipConcreteExisting = 1,
    SkipMissingMaterialization = 2,
    SkipInvalid = 3,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum TypeWritebackRenameApplyDecision {
    Apply = 0,
    SkipInvalid = 1,
    SkipCurrentNameNotGenerated = 2,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureWritebackActionKind {
    Signature,
    Callconv,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum SignatureWritebackActionDecision {
    Apply = 0,
    SkipMissingPayload = 1,
    SkipUnsupportedArch = 2,
    SkipTooLarge = 3,
    SkipLowConfidence = 4,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum SignatureRegisterArgRenameDecision {
    Apply = 0,
    SkipInvalid = 1,
    SkipCurrentNameNotGenerated = 2,
    SkipAlreadyMatches = 3,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SignatureWritebackDecision {
    pub authorized: bool,
    pub refusal: Option<String>,
    pub sources: Vec<String>,
}

pub fn signature_certificate_source_names(
    certificate: Option<&SignatureCertificate>,
) -> Vec<String> {
    certificate
        .map(|certificate| {
            certificate
                .sources
                .iter()
                .map(|source| source.as_str().to_string())
                .collect()
        })
        .unwrap_or_default()
}

pub fn signature_writeback_decision(type_facts: &FunctionTypeFacts) -> SignatureWritebackDecision {
    let Some(certificate) = type_facts.signature_certificate.as_ref() else {
        return SignatureWritebackDecision {
            authorized: false,
            refusal: Some(
                "signature mutation refused: missing exact SignatureCertificate".to_string(),
            ),
            sources: Vec::new(),
        };
    };
    let sources = signature_certificate_source_names(Some(certificate));
    let Some(signature) = type_facts.merged_signature.as_ref() else {
        return SignatureWritebackDecision {
            authorized: false,
            refusal: Some(
                "signature mutation refused: missing current merged signature".to_string(),
            ),
            sources,
        };
    };
    if certificate.signature != *signature {
        return SignatureWritebackDecision {
            authorized: false,
            refusal: Some(
                "signature mutation refused: SignatureCertificate does not match current merged signature"
                    .to_string(),
            ),
            sources,
        };
    }
    if !certificate.authorizes_signature_writeback() {
        return SignatureWritebackDecision {
            authorized: false,
            refusal: Some(format!(
                "signature mutation refused: certificate sources are not authoritative for writeback ({})",
                sources.join(",")
            )),
            sources,
        };
    }
    SignatureWritebackDecision {
        authorized: true,
        refusal: None,
        sources,
    }
}

fn push_budgeted_type_mutation(
    mutations: &mut Vec<TypeWritebackMutation>,
    diagnostics: &mut Vec<String>,
    emitted: &mut usize,
    skipped: &mut usize,
    budget: TypeWritebackMutationBudget,
    mutation: TypeWritebackMutation,
) {
    if *emitted < budget.max_mutations {
        mutations.push(mutation);
        *emitted += 1;
    } else {
        *skipped += 1;
        if *skipped == 1 {
            diagnostics.push(format!(
                "non-signature mutation plan truncated to {} item(s)",
                budget.max_mutations
            ));
        }
    }
}

struct TypeMutationPushContext<'a> {
    mutations: &'a mut Vec<TypeWritebackMutation>,
    diagnostics: &'a mut Vec<String>,
    emitted: &'a mut usize,
    skipped_budgeted: &'a mut usize,
    skipped_low_conf: &'a mut BTreeMap<&'static str, usize>,
    budget: TypeWritebackMutationBudget,
    apply_policy: TypeWritebackApplyPolicy,
}

fn bool_is_false(value: &bool) -> bool {
    !*value
}

fn push_apply_authorized_type_mutation(
    ctx: &mut TypeMutationPushContext<'_>,
    mutation: TypeWritebackMutation,
) {
    let min_confidence = ctx.apply_policy.mutation_min_confidence(mutation.kind);
    if mutation.confidence < min_confidence {
        *ctx.skipped_low_conf
            .entry(mutation.kind.as_str())
            .or_default() += 1;
        return;
    }
    push_budgeted_type_mutation(
        ctx.mutations,
        ctx.diagnostics,
        ctx.emitted,
        ctx.skipped_budgeted,
        ctx.budget,
        mutation,
    );
}

fn evidence_names(evidence: &[WritebackEvidence]) -> Vec<String> {
    evidence
        .iter()
        .map(|tag| tag.as_str().to_string())
        .collect()
}

pub fn type_writeback_mutation_plan(
    plan: &TypeWritebackPlan,
    budget: TypeWritebackMutationBudget,
    type_facts: &FunctionTypeFacts,
) -> TypeWritebackMutationPlan {
    type_writeback_mutation_plan_with_policy(
        plan,
        budget,
        type_facts,
        TypeWritebackApplyPolicy::balanced(),
    )
}

pub fn type_writeback_mutation_plan_with_policy(
    plan: &TypeWritebackPlan,
    budget: TypeWritebackMutationBudget,
    type_facts: &FunctionTypeFacts,
    apply_policy: TypeWritebackApplyPolicy,
) -> TypeWritebackMutationPlan {
    let mut mutations = Vec::new();
    let mut diagnostics = Vec::new();
    let mut emitted_budgeted = 0usize;
    let mut skipped_budgeted = 0usize;
    let mut skipped_low_conf = BTreeMap::new();

    let signature_decision = signature_writeback_decision(type_facts);
    if let Some(refusal) = signature_decision.refusal.clone() {
        diagnostics.push(refusal);
    } else {
        let signature_evidence = signature_decision
            .sources
            .iter()
            .map(|source| format!("signature-certificate:{source}"))
            .collect::<Vec<_>>();
        mutations.push(TypeWritebackMutation {
            kind: TypeWritebackMutationKind::Signature,
            signature: Some(plan.signature.signature.clone()),
            ret_type: Some(plan.signature.ret_type.clone()),
            params: plan.signature.params.clone(),
            callconv: Some(plan.signature.callconv.clone()),
            old_name: None,
            name: Some(plan.signature.function_name.clone()),
            reg: None,
            type_name: None,
            type_materialization_key: None,
            type_materialization_required: false,
            text: None,
            addr: None,
            size: None,
            delta: None,
            var_kind: None,
            is_arg: None,
            confidence: plan.signature.confidence,
            source: "function_facts".to_string(),
            evidence: signature_evidence.clone(),
        });

        mutations.push(TypeWritebackMutation {
            kind: TypeWritebackMutationKind::Callconv,
            signature: None,
            ret_type: None,
            params: Vec::new(),
            callconv: Some(plan.signature.callconv.clone()),
            old_name: None,
            name: Some(plan.signature.function_name.clone()),
            reg: None,
            type_name: None,
            type_materialization_key: None,
            type_materialization_required: false,
            text: None,
            addr: None,
            size: None,
            delta: None,
            var_kind: None,
            is_arg: None,
            confidence: plan.signature.callconv_confidence,
            source: "function_facts".to_string(),
            evidence: signature_evidence,
        });
    }

    {
        let mut mutation_ctx = TypeMutationPushContext {
            mutations: &mut mutations,
            diagnostics: &mut diagnostics,
            emitted: &mut emitted_budgeted,
            skipped_budgeted: &mut skipped_budgeted,
            skipped_low_conf: &mut skipped_low_conf,
            budget,
            apply_policy,
        };

        for decl in plan.struct_decls.iter().take(budget.max_type_decls) {
            push_apply_authorized_type_mutation(
                &mut mutation_ctx,
                TypeWritebackMutation {
                    kind: TypeWritebackMutationKind::TypeDecl,
                    signature: None,
                    ret_type: None,
                    params: Vec::new(),
                    callconv: None,
                    old_name: None,
                    name: Some(decl.name.clone()),
                    reg: None,
                    type_name: None,
                    type_materialization_key: None,
                    type_materialization_required: false,
                    text: Some(decl.decl.clone()),
                    addr: None,
                    size: None,
                    delta: None,
                    var_kind: None,
                    is_arg: None,
                    confidence: decl.confidence,
                    source: decl.source.as_str().to_string(),
                    evidence: vec!["struct-declaration".to_string()],
                },
            );
        }
    }
    if plan.struct_decls.len() > budget.max_type_decls {
        diagnostics.push(format!(
            "type declaration mutation plan truncated from {} to {} item(s)",
            plan.struct_decls.len(),
            budget.max_type_decls
        ));
    }

    {
        let mut mutation_ctx = TypeMutationPushContext {
            mutations: &mut mutations,
            diagnostics: &mut diagnostics,
            emitted: &mut emitted_budgeted,
            skipped_budgeted: &mut skipped_budgeted,
            skipped_low_conf: &mut skipped_low_conf,
            budget,
            apply_policy,
        };

        for candidate in &plan.var_type_candidates {
            let apply_type = canonicalize_writeback_apply_type_name(&candidate.var_type)
                .unwrap_or_else(|| candidate.var_type.clone());
            let type_materialization_key = writeback_type_materialization_key(&apply_type);
            let type_materialization_required = type_materialization_required_for_type(
                &apply_type,
                type_materialization_key.as_deref(),
            );
            if candidate.confidence >= MATERIALIZED_VAR_MUTATION_MIN_CONFIDENCE {
                push_apply_authorized_type_mutation(
                    &mut mutation_ctx,
                    TypeWritebackMutation {
                        kind: TypeWritebackMutationKind::Var,
                        signature: None,
                        ret_type: None,
                        params: Vec::new(),
                        callconv: None,
                        old_name: None,
                        name: Some(candidate.name.clone()),
                        reg: candidate.reg.clone(),
                        type_name: Some(apply_type.clone()),
                        type_materialization_key: type_materialization_key.clone(),
                        type_materialization_required,
                        text: None,
                        addr: None,
                        size: Some(candidate.size as u64),
                        delta: Some(candidate.delta),
                        var_kind: Some(candidate.kind.clone()),
                        is_arg: Some(candidate.isarg),
                        confidence: candidate.confidence,
                        source: candidate.source.as_str().to_string(),
                        evidence: evidence_names(&candidate.evidence),
                    },
                );
            }
            push_apply_authorized_type_mutation(
                &mut mutation_ctx,
                TypeWritebackMutation {
                    kind: TypeWritebackMutationKind::VarType,
                    signature: None,
                    ret_type: None,
                    params: Vec::new(),
                    callconv: None,
                    old_name: Some(candidate.name.clone()),
                    name: Some(candidate.name.clone()),
                    reg: candidate.reg.clone(),
                    type_name: Some(apply_type.clone()),
                    type_materialization_key: type_materialization_key.clone(),
                    type_materialization_required,
                    text: None,
                    addr: None,
                    size: Some(candidate.size as u64),
                    delta: Some(candidate.delta),
                    var_kind: Some(candidate.kind.clone()),
                    is_arg: Some(candidate.isarg),
                    confidence: candidate.confidence,
                    source: candidate.source.as_str().to_string(),
                    evidence: evidence_names(&candidate.evidence),
                },
            );
        }

        for candidate in &plan.var_rename_candidates {
            push_apply_authorized_type_mutation(
                &mut mutation_ctx,
                TypeWritebackMutation {
                    kind: TypeWritebackMutationKind::VarRename,
                    signature: None,
                    ret_type: None,
                    params: Vec::new(),
                    callconv: None,
                    old_name: Some(candidate.name.clone()),
                    name: Some(candidate.target_name.clone()),
                    reg: None,
                    type_name: None,
                    type_materialization_key: None,
                    type_materialization_required: false,
                    text: None,
                    addr: None,
                    size: None,
                    delta: None,
                    var_kind: None,
                    is_arg: None,
                    confidence: candidate.confidence,
                    source: candidate.source.as_str().to_string(),
                    evidence: evidence_names(&candidate.evidence),
                },
            );
        }

        for candidate in plan.global_type_links.iter().take(budget.global_max_links) {
            let apply_type = canonicalize_writeback_apply_type_name(&candidate.target_type)
                .unwrap_or_else(|| candidate.target_type.clone());
            let type_materialization_key = writeback_type_materialization_key(&apply_type);
            let type_materialization_required = type_materialization_required_for_type(
                &apply_type,
                type_materialization_key.as_deref(),
            );
            push_apply_authorized_type_mutation(
                &mut mutation_ctx,
                TypeWritebackMutation {
                    kind: TypeWritebackMutationKind::TypeLink,
                    signature: None,
                    ret_type: None,
                    params: Vec::new(),
                    callconv: None,
                    old_name: None,
                    name: None,
                    reg: None,
                    type_name: Some(apply_type.clone()),
                    type_materialization_key,
                    type_materialization_required,
                    text: None,
                    addr: Some(candidate.addr),
                    size: None,
                    delta: None,
                    var_kind: None,
                    is_arg: None,
                    confidence: candidate.confidence,
                    source: candidate.source.as_str().to_string(),
                    evidence: vec!["global-type-link".to_string()],
                },
            );
        }
    }
    if plan.global_type_links.len() > budget.global_max_links {
        diagnostics.push(format!(
            "global type-link mutation plan truncated from {} to {} item(s)",
            plan.global_type_links.len(),
            budget.global_max_links
        ));
    }
    for (kind, count) in skipped_low_conf {
        diagnostics.push(format!(
            "{kind} mutation plan withheld {count} low-confidence candidate(s)"
        ));
    }

    TypeWritebackMutationPlan {
        apply_policy,
        mutations,
        diagnostics,
    }
}

pub fn type_writeback_authority_report_with_policy(
    plan: &TypeWritebackPlan,
    budget: TypeWritebackMutationBudget,
    type_facts: &FunctionTypeFacts,
    apply_policy: TypeWritebackApplyPolicy,
    basic_block_count: usize,
) -> TypeWritebackAuthorityReport {
    let mutation_plan =
        type_writeback_mutation_plan_with_policy(plan, budget, type_facts, apply_policy);
    let signature_writeback = signature_writeback_decision(type_facts);
    let signature_action_decision = signature_writeback_action_decision(
        SignatureWritebackActionKind::Signature,
        &plan.signature.arch,
        basic_block_count,
        !plan.signature.signature.is_empty(),
        plan.signature.confidence,
    );
    let callconv_action_decision = signature_writeback_action_decision(
        SignatureWritebackActionKind::Callconv,
        &plan.signature.arch,
        basic_block_count,
        !plan.signature.callconv.is_empty(),
        plan.signature.callconv_confidence,
    );
    let mut warnings = plan.diagnostics.warnings.clone();
    if plan.struct_decls.len() > budget.max_type_decls {
        warnings.push(format!(
            "type declaration report truncated from {} to {} item(s)",
            plan.struct_decls.len(),
            budget.max_type_decls
        ));
    }
    if plan.global_type_links.len() > budget.global_max_links {
        warnings.push(format!(
            "global type-link report truncated from {} to {} item(s)",
            plan.global_type_links.len(),
            budget.global_max_links
        ));
    }

    TypeWritebackAuthorityReport {
        mutation_plan,
        signature_render_authorized: type_facts.render_authorized_signature().is_some(),
        signature_writeback,
        signature_action_decision,
        callconv_action_decision,
        warnings,
    }
}

pub fn type_writeback_authority_report(
    plan: &TypeWritebackPlan,
    budget: TypeWritebackMutationBudget,
    type_facts: &FunctionTypeFacts,
    basic_block_count: usize,
) -> TypeWritebackAuthorityReport {
    type_writeback_authority_report_with_policy(
        plan,
        budget,
        type_facts,
        TypeWritebackApplyPolicy::balanced(),
        basic_block_count,
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeWritebackAnalysis {
    pub signature: InferredSignature,
    pub function_facts: FunctionFacts,
    pub type_facts: FunctionTypeFacts,
    pub plan: TypeWritebackPlan,
}

pub struct TypeWritebackAnalysisInput<'a> {
    pub function_name: &'a str,
    pub ptr_bits: u32,
    pub inferred_signature: InferredSignature,
    pub recovered_vars: &'a [RecoveredVariable],
    pub ssa_blocks: &'a [SSABlock],
    pub parsed_context: ParsedExternalContext,
    pub local_structs: LocalStructArtifacts,
    pub interproc_summary_set: Option<InterprocSummarySet>,
    pub diagnostics: TypeWritebackDiagnostics,
}

pub struct TypeWritebackSemanticInputs<'a> {
    pub artifact: &'a r2sym::SemanticArtifact,
    pub local_field_accesses: &'a [LocalFieldAccessFact],
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    fn pick_apply_mode(raw: u8) -> TypeWritebackApplyMode {
        match raw % 3 {
            0 => TypeWritebackApplyMode::Off,
            1 => TypeWritebackApplyMode::Balanced,
            _ => TypeWritebackApplyMode::Aggressive,
        }
    }

    fn pick_summary_linkage(raw: u8) -> r2ssa::FunctionSemanticLinkage {
        match raw % 3 {
            0 => r2ssa::FunctionSemanticLinkage::Unknown,
            1 => r2ssa::FunctionSemanticLinkage::Internal,
            _ => r2ssa::FunctionSemanticLinkage::Imported,
        }
    }

    #[kani::proof]
    fn summary_linkage_to_callee_linkage_is_exact() {
        let summary_linkage = pick_summary_linkage(kani::any());
        let callee_linkage = summary_linkage_to_callee_linkage(summary_linkage);

        assert_eq!(
            callee_linkage.authorizes_import_policy(),
            summary_linkage == r2ssa::FunctionSemanticLinkage::Imported,
        );
        match summary_linkage {
            r2ssa::FunctionSemanticLinkage::Unknown => {
                assert_eq!(callee_linkage, crate::CalleeLinkage::Unknown);
            }
            r2ssa::FunctionSemanticLinkage::Internal => {
                assert_eq!(callee_linkage, crate::CalleeLinkage::Internal);
            }
            r2ssa::FunctionSemanticLinkage::Imported => {
                assert_eq!(callee_linkage, crate::CalleeLinkage::Imported);
            }
        }
    }

    #[kani::proof]
    fn type_writeback_mutation_budget_is_never_zero() {
        let budget = TypeWritebackMutationBudget::new(
            kani::any::<usize>(),
            kani::any::<usize>(),
            kani::any::<usize>(),
        );

        assert!(budget.global_max_links >= 1);
        assert!(budget.max_type_decls >= 1);
        assert!(budget.max_mutations >= 1);
    }

    #[kani::proof]
    fn type_writeback_apply_threshold_is_total_and_nonzero() {
        let mode = pick_apply_mode(kani::any::<u8>());
        let base = kani::any::<u8>();
        let delta = kani::any::<u8>();
        let policy = TypeWritebackApplyPolicy {
            mode,
            ..TypeWritebackApplyPolicy::balanced()
        };
        let threshold = policy.effective_threshold(base, delta);

        assert!(threshold >= 1);
        if mode == TypeWritebackApplyMode::Off {
            assert_eq!(threshold, TYPE_WRITEBACK_OFF_THRESHOLD);
        } else {
            assert!(threshold <= 100);
        }
    }

    #[kani::proof]
    fn aggressive_apply_threshold_is_never_stricter_than_balanced() {
        let base = kani::any::<u8>();
        let delta = kani::any::<u8>();
        let balanced = TypeWritebackApplyPolicy::balanced().effective_threshold(base, delta);
        let aggressive = TypeWritebackApplyPolicy::aggressive().effective_threshold(base, delta);

        assert!(aggressive <= balanced);
    }

    #[kani::proof]
    fn apply_policy_kind_thresholds_use_their_canonical_field() {
        let type_min_confidence = kani::any::<u8>();
        let rename_min_confidence = kani::any::<u8>();
        let struct_min_confidence = kani::any::<u8>();
        let policy = TypeWritebackApplyPolicy {
            mode: TypeWritebackApplyMode::Balanced,
            type_min_confidence,
            rename_min_confidence,
            struct_min_confidence,
        };

        assert_eq!(
            policy.mutation_min_confidence(TypeWritebackMutationKind::TypeDecl),
            struct_min_confidence.clamp(1, 100)
        );
        assert_eq!(
            policy.mutation_min_confidence(TypeWritebackMutationKind::VarRename),
            rename_min_confidence.clamp(1, 100)
        );
        assert_eq!(
            policy.mutation_min_confidence(TypeWritebackMutationKind::VarType),
            type_min_confidence.clamp(1, 100)
        );
        assert_eq!(
            policy.mutation_min_confidence(TypeWritebackMutationKind::TypeLink),
            type_min_confidence.clamp(1, 100)
        );
    }

    #[kani::proof]
    fn var_type_apply_decision_rejects_invalid_candidate() {
        assert_eq!(
            type_writeback_var_type_apply_decision(Some("struct real_type *"), "", false, true),
            TypeWritebackApplyDecision::SkipInvalid
        );
    }

    #[kani::proof]
    fn var_type_apply_decision_rejects_missing_materialization() {
        assert_eq!(
            type_writeback_var_type_apply_decision(None, "struct Foo *", true, false),
            TypeWritebackApplyDecision::SkipMissingMaterialization
        );
    }

    #[kani::proof]
    fn var_type_apply_decision_preserves_concrete_from_generic() {
        assert_eq!(
            type_writeback_var_type_apply_decision(
                Some("struct real_type *"),
                "uint32_t",
                false,
                true,
            ),
            TypeWritebackApplyDecision::SkipConcreteExisting
        );
    }

    #[kani::proof]
    fn signature_action_decision_missing_payload_wins() {
        let blocks = kani::any::<usize>();
        let confidence = kani::any::<u8>();

        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Signature,
                "x86-64",
                blocks,
                false,
                confidence,
            ),
            SignatureWritebackActionDecision::SkipMissingPayload
        );
    }

    #[kani::proof]
    fn signature_action_decision_size_wins_before_arch_and_confidence() {
        let confidence = kani::any::<u8>();

        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Signature,
                "",
                SIGNATURE_WRITEBACK_MAX_BLOCKS + 1,
                true,
                confidence,
            ),
            SignatureWritebackActionDecision::SkipTooLarge
        );
    }

    #[kani::proof]
    fn signature_action_decision_confidence_threshold_is_enforced() {
        let confidence = kani::any::<u8>();
        kani::assume(confidence < SIGNATURE_WRITEBACK_MIN_CONFIDENCE);

        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Signature,
                "x86-64",
                SIGNATURE_WRITEBACK_MAX_BLOCKS,
                true,
                confidence,
            ),
            SignatureWritebackActionDecision::SkipLowConfidence
        );
    }

    #[kani::proof]
    fn generated_var_decimal_suffix_accepts_only_ascii_digits() {
        let suffix = kani::any::<[u8; 4]>();
        if ascii_suffix_is_nonempty_decimal(&suffix) {
            for byte in suffix {
                assert!(byte.is_ascii_digit());
            }
        }

        assert!(!ascii_suffix_is_nonempty_decimal(&[]));
    }

    #[kani::proof]
    fn type_materialization_required_from_key_is_fail_closed() {
        let key = match kani::any::<u8>() % 3 {
            0 => None,
            1 => Some("Foo"),
            _ => Some(""),
        };
        let required = type_materialization_required_from_key(key);
        match key {
            Some(value) if !value.is_empty() => assert!(required),
            _ => assert!(!required),
        }
    }
}

#[derive(Debug, Clone, Default)]
struct SignatureContextMaps {
    param_types: HashMap<usize, String>,
    param_names: HashMap<usize, String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct SemanticTypeProjection {
    return_type_hint: Option<CTypeLike>,
    pointer_param_indices: BTreeSet<usize>,
    out_param_indices: BTreeSet<usize>,
    out_param_evidence: BTreeMap<usize, BTreeSet<OutParamCertificateEvidence>>,
    out_param_sources: BTreeMap<usize, BTreeSet<OutParamCertificateSource>>,
    param_type_hints: BTreeMap<usize, CTypeLike>,
    param_name_hints: BTreeMap<usize, String>,
    slot_field_profiles: BTreeMap<usize, BTreeMap<u64, String>>,
    refused_param_projections: BTreeMap<usize, String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct SummaryRoleKey {
    stable_id: u64,
    anchor: u64,
    kind: r2sym::NativeWorkerSummaryKind,
}

impl SummaryRoleKey {
    fn from_certificate(cert: &r2sym::SummaryRoleCertificate) -> Self {
        Self {
            stable_id: cert.stable_id,
            anchor: cert.anchor,
            kind: cert.summary_kind,
        }
    }

    fn from_worker_summary(summary: &r2sym::NativeWorkerSummary) -> Self {
        Self {
            stable_id: summary.summary_role_certificate_id(),
            anchor: summary.anchor,
            kind: summary.kind,
        }
    }

    fn from_region_summary(summary: &r2sym::NativeRegionSummary) -> Self {
        Self {
            stable_id: summary.summary_role_certificate_id(),
            anchor: summary.anchor,
            kind: summary.kind,
        }
    }
}

fn summary_role_keys(claims: &r2sym::SemanticClaimSummary) -> BTreeSet<SummaryRoleKey> {
    claims
        .summary_role_certificates
        .iter()
        .map(SummaryRoleKey::from_certificate)
        .collect()
}

fn worker_summary_has_role_certificate(
    summary: &r2sym::NativeWorkerSummary,
    role_keys: &BTreeSet<SummaryRoleKey>,
) -> bool {
    role_keys.contains(&SummaryRoleKey::from_worker_summary(summary))
}

fn region_summary_has_role_certificate(
    summary: &r2sym::NativeRegionSummary,
    role_keys: &BTreeSet<SummaryRoleKey>,
) -> bool {
    role_keys.contains(&SummaryRoleKey::from_region_summary(summary))
}

fn signed_byte_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(CTypeLike::Int {
        bits: 8,
        signedness: Signedness::Signed,
    }))
}

fn byte_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(CTypeLike::Int {
        bits: 8,
        signedness: Signedness::Unsigned,
    }))
}

fn signed_int_type(bits: u32) -> CTypeLike {
    CTypeLike::Int {
        bits,
        signedness: Signedness::Signed,
    }
}

fn unsigned_int_type(bits: u32) -> CTypeLike {
    CTypeLike::Int {
        bits,
        signedness: Signedness::Unsigned,
    }
}

fn c_int_type() -> CTypeLike {
    typedef_type("int")
}

fn c_uint_type() -> CTypeLike {
    typedef_type("unsigned int")
}

#[cfg(test)]
fn signed_byte_pointer_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(signed_byte_pointer_type()))
}

fn typedef_type(name: &str) -> CTypeLike {
    CTypeLike::Typedef(name.to_string())
}

fn typedef_pointer_type(name: &str) -> CTypeLike {
    CTypeLike::Pointer(Box::new(typedef_type(name)))
}

fn void_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(CTypeLike::Void))
}

fn size_type(ptr_bits: u32) -> CTypeLike {
    CTypeLike::Int {
        bits: ptr_bits,
        signedness: Signedness::Unsigned,
    }
}

fn summary_location_arg_index(location: Option<&r2ssa::SummaryMemoryLocation>) -> Option<usize> {
    match location?.region {
        r2ssa::SummaryMemoryRegion::Arg { index } => Some(index),
        r2ssa::SummaryMemoryRegion::Global { .. }
        | r2ssa::SummaryMemoryRegion::HeapReturn
        | r2ssa::SummaryMemoryRegion::Unknown => None,
    }
}

fn merge_param_type_hint(
    hints: &mut BTreeMap<usize, CTypeLike>,
    index: usize,
    hint: CTypeLike,
    ptr_bits: u32,
) {
    let Some(existing) = hints.get(&index) else {
        hints.insert(index, hint);
        return;
    };
    if render_signature_type(existing, ptr_bits) == render_signature_type(&hint, ptr_bits) {
        return;
    }
    let should_replace = matches!(
        (existing, &hint),
        (
            CTypeLike::Pointer(inner),
            CTypeLike::Pointer(new_inner)
        ) if matches!(**inner, CTypeLike::Void | CTypeLike::Unknown)
            && !matches!(**new_inner, CTypeLike::Void | CTypeLike::Unknown)
    );
    if should_replace {
        hints.insert(index, hint);
    }
}

fn collect_worker_location_pointer_hint(
    hints: &mut BTreeMap<usize, CTypeLike>,
    pointer_indices: &mut BTreeSet<usize>,
    location: Option<&r2ssa::SummaryMemoryLocation>,
    hint: CTypeLike,
    ptr_bits: u32,
) {
    if let Some(index) = summary_location_arg_index(location) {
        pointer_indices.insert(index);
        merge_param_type_hint(hints, index, hint, ptr_bits);
    }
}

fn collect_projection_size_arg_hint(
    projection: &mut SemanticTypeProjection,
    index: usize,
    name: &str,
    ptr_bits: u32,
) {
    projection
        .param_name_hints
        .entry(index)
        .or_insert_with(|| name.to_string());
    merge_param_type_hint(
        &mut projection.param_type_hints,
        index,
        size_type(ptr_bits),
        ptr_bits,
    );
}

fn mark_projection_out_param(
    projection: &mut SemanticTypeProjection,
    index: usize,
    evidence: OutParamCertificateEvidence,
    source: OutParamCertificateSource,
) {
    projection.out_param_indices.insert(index);
    projection
        .out_param_evidence
        .entry(index)
        .or_default()
        .insert(evidence);
    projection
        .out_param_sources
        .entry(index)
        .or_default()
        .insert(source);
    projection.refused_param_projections.remove(&index);
}

fn native_worker_out_param_source(
    summary: &r2sym::NativeWorkerSummary,
    param_index: usize,
) -> OutParamCertificateSource {
    OutParamCertificateSource::NativeWorkerSummary {
        stable_id: summary.summary_role_certificate_id(),
        anchor: summary.anchor,
        summary_kind: summary.kind,
        param_index,
    }
}

fn native_region_out_param_source(
    summary: &r2sym::NativeRegionSummary,
    param_index: usize,
) -> OutParamCertificateSource {
    OutParamCertificateSource::NativeRegionSummary {
        stable_id: summary.summary_role_certificate_id(),
        anchor: summary.anchor,
        summary_kind: summary.kind,
        param_index,
    }
}

fn semantic_claim_out_param_source(claim: &r2sym::SemanticClaim) -> OutParamCertificateSource {
    OutParamCertificateSource::SemanticClaim {
        stable_id: claim.stable_id,
        anchor: claim.anchor,
    }
}

fn interproc_out_param_source(
    summary: &FunctionSemanticSummary,
    evidence: OutParamCertificateEvidence,
    param_index: usize,
    effect_index: usize,
) -> OutParamCertificateSource {
    OutParamCertificateSource::InterprocSummaryEffect {
        function_id: summary.id.0,
        evidence,
        param_index,
        effect_index,
    }
}

fn refuse_projection_out_param(
    projection: &mut SemanticTypeProjection,
    index: usize,
    reason: impl Into<String>,
) {
    if !projection.out_param_indices.contains(&index) {
        projection
            .refused_param_projections
            .entry(index)
            .or_insert_with(|| reason.into());
    }
}

fn collect_worker_scalar_arg_type_hints(
    summary: &r2sym::NativeWorkerSummary,
    projection: &mut SemanticTypeProjection,
    ptr_bits: u32,
) {
    if let Some(r2ssa::SummaryTransferLength::Arg(index)) = summary.len {
        collect_projection_size_arg_hint(projection, index, "len", ptr_bits);
    }
    if let Some(length_arg) = summary
        .loop_summary
        .as_ref()
        .and_then(|loop_summary| loop_summary.length_arg)
    {
        collect_projection_size_arg_hint(projection, length_arg, "len", ptr_bits);
    }
    if let Some(allocation) = summary.allocation
        && let Some(index) = allocation.size_arg
    {
        collect_projection_size_arg_hint(projection, index, "size", ptr_bits);
    }
}

fn collect_worker_summary_type_hints(
    summary: &r2sym::NativeWorkerSummary,
    projection: &mut SemanticTypeProjection,
    ptr_bits: u32,
    certified_summary_roles: &BTreeSet<SummaryRoleKey>,
) {
    if !semantic_evidence_allows_type_projection(&summary.evidence) {
        return;
    }
    if !worker_summary_has_role_certificate(summary, certified_summary_roles) {
        if summary.is_generic_memory_summary() {
            for index in summary.out_param_indices() {
                refuse_projection_out_param(
                    projection,
                    index,
                    format!(
                        "generic memory summary at 0x{:x} is not specific enough for out-pointer projection",
                        summary.anchor
                    ),
                );
            }
        }
        return;
    }
    match summary.kind {
        r2sym::NativeWorkerSummaryKind::DiagnosticWrapper => {
            projection
                .param_name_hints
                .entry(1)
                .or_insert_with(|| "fmt".to_string());
            merge_param_type_hint(
                &mut projection.param_type_hints,
                0,
                typedef_type("errno_t"),
                ptr_bits,
            );
            collect_worker_location_pointer_hint(
                &mut projection.param_type_hints,
                &mut projection.pointer_param_indices,
                summary.memory.as_ref(),
                signed_byte_pointer_type(),
                ptr_bits,
            );
            return;
        }
        r2sym::NativeWorkerSummaryKind::FormatArgumentFetch => {
            collect_worker_location_pointer_hint(
                &mut projection.param_type_hints,
                &mut projection.pointer_param_indices,
                summary.src.as_ref(),
                typedef_pointer_type("__va_list_tag"),
                ptr_bits,
            );
            collect_worker_location_pointer_hint(
                &mut projection.param_type_hints,
                &mut projection.pointer_param_indices,
                summary.dst.as_ref(),
                typedef_pointer_type("arguments"),
                ptr_bits,
            );
            for index in summary.out_param_indices() {
                mark_projection_out_param(
                    projection,
                    index,
                    OutParamCertificateEvidence::NativeWorkerWrite,
                    native_worker_out_param_source(summary, index),
                );
            }
            return;
        }
        _ => {}
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::Parser) {
        if let Some(index) = summary_location_arg_index(summary.dst.as_ref()) {
            projection
                .param_name_hints
                .entry(index)
                .or_insert_with(|| "output".to_string());
        }
        if let Some(index) = summary
            .parser
            .as_ref()
            .and_then(|parser| parser.cursor_arg)
            .or_else(|| summary_location_arg_index(summary.memory.as_ref()))
        {
            projection
                .param_name_hints
                .entry(index)
                .or_insert_with(|| "stream".to_string());
        }
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::FileTransfer) {
        if let Some(index) = summary_location_arg_index(summary.src.as_ref()) {
            projection
                .param_name_hints
                .entry(index)
                .or_insert_with(|| "src".to_string());
        }
        if let Some(index) = summary_location_arg_index(summary.dst.as_ref()) {
            projection
                .param_name_hints
                .entry(index)
                .or_insert_with(|| "dst".to_string());
        }
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::PathWalk)
        && let Some(index) = summary_location_arg_index(summary.memory.as_ref())
    {
        projection
            .param_name_hints
            .entry(index)
            .or_insert_with(|| "path".to_string());
    }
    if matches!(
        summary.kind,
        r2sym::NativeWorkerSummaryKind::DirectoryTraversal
    ) {
        if let Some(index) = summary_location_arg_index(summary.memory.as_ref()) {
            projection
                .param_name_hints
                .entry(index)
                .or_insert_with(|| "stream".to_string());
        }
        if let Some(index) = summary_location_arg_index(summary.dst.as_ref()) {
            projection
                .param_name_hints
                .entry(index)
                .or_insert_with(|| "entry".to_string());
        }
    }
    match summary.kind {
        r2sym::NativeWorkerSummaryKind::RecordStream => {
            if let Some(index) = summary_location_arg_index(summary.memory.as_ref()) {
                projection
                    .param_name_hints
                    .entry(index)
                    .or_insert_with(|| "stream".to_string());
            }
        }
        r2sym::NativeWorkerSummaryKind::FieldSelection => {
            if let Some(index) = summary_location_arg_index(summary.memory.as_ref()) {
                projection
                    .param_name_hints
                    .entry(index)
                    .or_insert_with(|| "field_spec".to_string());
            }
        }
        r2sym::NativeWorkerSummaryKind::OutputStream => {
            if let Some(index) = summary_location_arg_index(summary.memory.as_ref()) {
                projection
                    .param_name_hints
                    .entry(index)
                    .or_insert_with(|| "text".to_string());
            }
        }
        r2sym::NativeWorkerSummaryKind::FormatRender => {
            if let Some(index) = summary_location_arg_index(summary.memory.as_ref()) {
                projection
                    .param_name_hints
                    .entry(index)
                    .or_insert_with(|| "format_input".to_string());
            }
        }
        r2sym::NativeWorkerSummaryKind::MetadataProbe => {
            if let Some(index) = summary_location_arg_index(summary.memory.as_ref()) {
                projection
                    .param_name_hints
                    .entry(index)
                    .or_insert_with(|| "metadata_subject".to_string());
            }
        }
        r2sym::NativeWorkerSummaryKind::SortMerge => {
            if let Some(index) = summary_location_arg_index(summary.memory.as_ref()) {
                projection
                    .param_name_hints
                    .entry(index)
                    .or_insert_with(|| "files".to_string());
            }
        }
        r2sym::NativeWorkerSummaryKind::NumericTransform => {
            if let Some(index) = summary_location_arg_index(summary.dst.as_ref()) {
                projection
                    .param_name_hints
                    .entry(index)
                    .or_insert_with(|| "result".to_string());
                mark_projection_out_param(
                    projection,
                    index,
                    OutParamCertificateEvidence::NativeWorkerWrite,
                    native_worker_out_param_source(summary, index),
                );
            }
        }
        _ => {}
    }
    collect_worker_scalar_arg_type_hints(summary, projection, ptr_bits);
    if summary.dst.is_none()
        && let Some(fold) = summary
            .loop_summary
            .as_ref()
            .and_then(|loop_summary| loop_summary.fold.as_ref())
    {
        match summary.kind {
            r2sym::NativeWorkerSummaryKind::HashFold => {
                projection
                    .return_type_hint
                    .get_or_insert_with(|| unsigned_int_type(fold.bits));
            }
            r2sym::NativeWorkerSummaryKind::NumericTransform if summary.memory.is_some() => {
                projection
                    .return_type_hint
                    .get_or_insert_with(|| size_type(ptr_bits));
            }
            _ => {}
        }
    }
    if summary.allocation.is_some()
        || matches!(summary.kind, r2sym::NativeWorkerSummaryKind::Allocation)
    {
        projection
            .return_type_hint
            .get_or_insert_with(void_pointer_type);
    }
    if summary.is_generic_memory_summary() {
        for index in summary.out_param_indices() {
            refuse_projection_out_param(
                projection,
                index,
                format!(
                    "generic memory summary at 0x{:x} is not specific enough for out-pointer projection",
                    summary.anchor
                ),
            );
        }
        return;
    }
    for index in summary.out_param_indices() {
        mark_projection_out_param(
            projection,
            index,
            OutParamCertificateEvidence::NativeWorkerWrite,
            native_worker_out_param_source(summary, index),
        );
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::FileTransfer) {
        if let Some(index) = summary_location_arg_index(summary.src.as_ref()) {
            merge_param_type_hint(
                &mut projection.param_type_hints,
                index,
                signed_int_type(32),
                ptr_bits,
            );
        }
        if let Some(index) = summary_location_arg_index(summary.dst.as_ref()) {
            merge_param_type_hint(
                &mut projection.param_type_hints,
                index,
                signed_int_type(32),
                ptr_bits,
            );
        }
        if let Some(r2ssa::SummaryTransferLength::Arg(index)) = summary.len {
            merge_param_type_hint(
                &mut projection.param_type_hints,
                index,
                size_type(ptr_bits),
                ptr_bits,
            );
        }
        return;
    }
    let pointer_hint = match summary.kind {
        r2sym::NativeWorkerSummaryKind::StringScan => signed_byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::Parser
            if summary
                .parser
                .as_ref()
                .is_some_and(|parser| matches!(parser.kind, r2sym::NativeParserKind::Numeric)) =>
        {
            signed_byte_pointer_type()
        }
        r2sym::NativeWorkerSummaryKind::PathWalk => signed_byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::RecordStream => typedef_pointer_type("FILE"),
        r2sym::NativeWorkerSummaryKind::FieldSelection => signed_byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::OutputStream => signed_byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::FormatRender
        | r2sym::NativeWorkerSummaryKind::MetadataProbe => void_pointer_type(),
        r2sym::NativeWorkerSummaryKind::SortMerge => typedef_pointer_type("sortfile"),
        r2sym::NativeWorkerSummaryKind::NumericTransform if summary.memory.is_some() => {
            byte_pointer_type()
        }
        r2sym::NativeWorkerSummaryKind::NumericTransform => void_pointer_type(),
        r2sym::NativeWorkerSummaryKind::HashFold
        | r2sym::NativeWorkerSummaryKind::TableWalk
        | r2sym::NativeWorkerSummaryKind::Parser => byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::DirectoryTraversal => void_pointer_type(),
        r2sym::NativeWorkerSummaryKind::MemoryTransfer
        | r2sym::NativeWorkerSummaryKind::MemoryRead
        | r2sym::NativeWorkerSummaryKind::MemoryWrite => byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::FileTransfer => signed_int_type(32),
        r2sym::NativeWorkerSummaryKind::MemoryEscape
        | r2sym::NativeWorkerSummaryKind::MemoryFree
        | r2sym::NativeWorkerSummaryKind::ProgramOrchestrator
        | r2sym::NativeWorkerSummaryKind::DiagnosticWrapper
        | r2sym::NativeWorkerSummaryKind::FormatArgumentFetch
        | r2sym::NativeWorkerSummaryKind::Allocation
        | r2sym::NativeWorkerSummaryKind::Lifetime
        | r2sym::NativeWorkerSummaryKind::Synchronization
        | r2sym::NativeWorkerSummaryKind::Atomic
        | r2sym::NativeWorkerSummaryKind::Unknown => void_pointer_type(),
    };
    let dst_pointer_hint = if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::Parser)
        && summary
            .parser
            .as_ref()
            .is_some_and(|parser| matches!(parser.kind, r2sym::NativeParserKind::Numeric))
    {
        void_pointer_type()
    } else {
        pointer_hint.clone()
    };
    collect_worker_location_pointer_hint(
        &mut projection.param_type_hints,
        &mut projection.pointer_param_indices,
        summary.dst.as_ref(),
        dst_pointer_hint,
        ptr_bits,
    );
    collect_worker_location_pointer_hint(
        &mut projection.param_type_hints,
        &mut projection.pointer_param_indices,
        summary.src.as_ref(),
        pointer_hint.clone(),
        ptr_bits,
    );
    collect_worker_location_pointer_hint(
        &mut projection.param_type_hints,
        &mut projection.pointer_param_indices,
        summary.memory.as_ref(),
        pointer_hint,
        ptr_bits,
    );
    collect_worker_location_pointer_hint(
        &mut projection.param_type_hints,
        &mut projection.pointer_param_indices,
        summary.atomic.as_ref().map(|effect| &effect.location),
        void_pointer_type(),
        ptr_bits,
    );

    if let Some(lifetime) = summary.lifetime {
        projection.pointer_param_indices.insert(lifetime.arg);
        merge_param_type_hint(
            &mut projection.param_type_hints,
            lifetime.arg,
            void_pointer_type(),
            ptr_bits,
        );
    }
    if let Some(sync) = summary.sync {
        projection.pointer_param_indices.insert(sync.arg);
        merge_param_type_hint(
            &mut projection.param_type_hints,
            sync.arg,
            void_pointer_type(),
            ptr_bits,
        );
    }
}

fn region_summary_pointer_hint(summary: &r2sym::NativeRegionSummary) -> CTypeLike {
    match summary.kind {
        r2sym::NativeWorkerSummaryKind::StringScan => signed_byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::Parser
            if summary
                .parser
                .as_ref()
                .is_some_and(|parser| matches!(parser.kind, r2sym::NativeParserKind::Numeric)) =>
        {
            signed_byte_pointer_type()
        }
        r2sym::NativeWorkerSummaryKind::PathWalk => signed_byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::RecordStream => typedef_pointer_type("FILE"),
        r2sym::NativeWorkerSummaryKind::FieldSelection
        | r2sym::NativeWorkerSummaryKind::OutputStream => signed_byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::SortMerge => typedef_pointer_type("sortfile"),
        r2sym::NativeWorkerSummaryKind::NumericTransform => void_pointer_type(),
        r2sym::NativeWorkerSummaryKind::HashFold
        | r2sym::NativeWorkerSummaryKind::TableWalk
        | r2sym::NativeWorkerSummaryKind::Parser
        | r2sym::NativeWorkerSummaryKind::DiagnosticWrapper
        | r2sym::NativeWorkerSummaryKind::FormatArgumentFetch
        | r2sym::NativeWorkerSummaryKind::MemoryTransfer
        | r2sym::NativeWorkerSummaryKind::MemoryRead
        | r2sym::NativeWorkerSummaryKind::MemoryWrite => byte_pointer_type(),
        r2sym::NativeWorkerSummaryKind::FileTransfer
        | r2sym::NativeWorkerSummaryKind::ProgramOrchestrator
        | r2sym::NativeWorkerSummaryKind::DirectoryTraversal
        | r2sym::NativeWorkerSummaryKind::FormatRender
        | r2sym::NativeWorkerSummaryKind::MetadataProbe => void_pointer_type(),
        r2sym::NativeWorkerSummaryKind::MemoryEscape
        | r2sym::NativeWorkerSummaryKind::MemoryFree
        | r2sym::NativeWorkerSummaryKind::Allocation
        | r2sym::NativeWorkerSummaryKind::Lifetime
        | r2sym::NativeWorkerSummaryKind::Synchronization
        | r2sym::NativeWorkerSummaryKind::Atomic
        | r2sym::NativeWorkerSummaryKind::Unknown => void_pointer_type(),
    }
}

fn collect_region_summary_type_hints(
    summary: &r2sym::NativeRegionSummary,
    projection: &mut SemanticTypeProjection,
    ptr_bits: u32,
    certified_summary_roles: &BTreeSet<SummaryRoleKey>,
) {
    if !semantic_evidence_allows_type_projection(&summary.evidence) {
        return;
    }
    if !region_summary_has_role_certificate(summary, certified_summary_roles) {
        return;
    }
    for access in &summary.memory_accesses {
        if let Some(r2ssa::SummaryTransferLength::Arg(index)) = access.len {
            collect_projection_size_arg_hint(projection, index, "len", ptr_bits);
        }
    }
    if let Some(length_arg) = summary
        .loop_summary
        .as_ref()
        .and_then(|loop_summary| loop_summary.length_arg)
    {
        collect_projection_size_arg_hint(projection, length_arg, "len", ptr_bits);
    }
    if summary.is_generic_memory_summary() {
        return;
    }
    let pointer_hint = region_summary_pointer_hint(summary);
    for index in summary.out_param_indices() {
        mark_projection_out_param(
            projection,
            index,
            OutParamCertificateEvidence::NativeRegionWrite,
            native_region_out_param_source(summary, index),
        );
    }
    if matches!(summary.kind, r2sym::NativeWorkerSummaryKind::Parser)
        && let Some(index) = summary
            .parser
            .as_ref()
            .and_then(|parser| parser.cursor_arg)
            .or_else(|| {
                summary
                    .memory_accesses
                    .iter()
                    .find_map(|access| summary_location_arg_index(access.location.as_ref()))
            })
    {
        projection
            .param_name_hints
            .entry(index)
            .or_insert_with(|| "stream".to_string());
    }
    for access in &summary.memory_accesses {
        let access_hint = match access.kind {
            r2sym::NativeMemoryAccessKind::Read
            | r2sym::NativeMemoryAccessKind::Write
            | r2sym::NativeMemoryAccessKind::Transfer => pointer_hint.clone(),
            r2sym::NativeMemoryAccessKind::Atomic
            | r2sym::NativeMemoryAccessKind::Escape
            | r2sym::NativeMemoryAccessKind::Free
            | r2sym::NativeMemoryAccessKind::Lifetime
            | r2sym::NativeMemoryAccessKind::Synchronization
            | r2sym::NativeMemoryAccessKind::Allocation
            | r2sym::NativeMemoryAccessKind::Unknown => void_pointer_type(),
        };
        collect_worker_location_pointer_hint(
            &mut projection.param_type_hints,
            &mut projection.pointer_param_indices,
            access.location.as_ref(),
            access_hint.clone(),
            ptr_bits,
        );
        collect_worker_location_pointer_hint(
            &mut projection.param_type_hints,
            &mut projection.pointer_param_indices,
            access.dst.as_ref(),
            access_hint.clone(),
            ptr_bits,
        );
        collect_worker_location_pointer_hint(
            &mut projection.param_type_hints,
            &mut projection.pointer_param_indices,
            access.src.as_ref(),
            access_hint,
            ptr_bits,
        );
    }
}

fn semantic_hints_compatible(semantic_hint: &CTypeLike, requested_hint: &CTypeLike) -> bool {
    if semantic_hint == requested_hint {
        return true;
    }
    matches!(
        (semantic_hint, requested_hint),
        (CTypeLike::Pointer(_), CTypeLike::Pointer(_))
            | (
                CTypeLike::Int {
                    signedness: Signedness::Unsigned,
                    ..
                },
                CTypeLike::Int { .. }
            )
    )
}

fn certified_summary_role_kinds(
    claim_summary: &r2sym::SemanticClaimSummary,
) -> BTreeSet<r2sym::NativeWorkerSummaryKind> {
    claim_summary
        .summary_role_certificates
        .iter()
        .filter(|cert| !matches!(cert.source, r2sym::SemanticClaimSource::NameHint))
        .map(|cert| cert.summary_kind)
        .collect()
}

fn role_identity_has_certified_summary_role(
    role: &r2sym::NativeWorkerRoleIdentity,
    certified_role_kinds: &BTreeSet<r2sym::NativeWorkerSummaryKind>,
) -> bool {
    role.summary_kinds
        .iter()
        .any(|kind| certified_role_kinds.contains(kind))
}

pub fn signature_hint_for_semantic_artifact(
    semantic_artifact: &r2sym::SemanticArtifact,
    current_param_count: usize,
) -> Option<FunctionSignatureSpec> {
    signature_projection_for_semantic_artifact(semantic_artifact, current_param_count)
        .map(|projection| projection.signature)
}

pub fn signature_projection_for_semantic_artifact(
    semantic_artifact: &r2sym::SemanticArtifact,
    current_param_count: usize,
) -> Option<FunctionSignatureProjection> {
    let native = semantic_artifact.native_body()?;
    let claim_summary = semantic_artifact.semantic_claim_summary();
    if !claim_summary.has_renderable_non_name_claim() && !claim_summary.has_type_projection_claims()
    {
        return None;
    }
    let certified_role_kinds = certified_summary_role_kinds(&claim_summary);
    if let Some(role) = native.summary.role_identity.as_ref()
        && role_identity_has_certified_summary_role(role, &certified_role_kinds)
        && let Some(signature) =
            crate::role_registry::signature_hint_for_role_identity(role, current_param_count)
    {
        return Some(FunctionSignatureProjection::strong_summary(signature));
    }
    if certified_role_kinds.is_empty() {
        return None;
    }
    crate::role_registry::signature_hint_for_summary_kinds(
        &certified_role_kinds,
        current_param_count,
    )
    .map(FunctionSignatureProjection::weak_summary_kind)
}

fn signature_projection_can_certify(projection: &FunctionSignatureProjection) -> bool {
    projection.has_strong_signature_confidence()
        && !matches!(projection.source, SignatureProjectionSource::SummaryKind)
}

fn semantic_evidence_allows_type_projection(evidence: &r2sym::SemanticEvidence) -> bool {
    evidence.allows_narrowing()
        && !evidence
            .reasons
            .contains(&r2sym::SemanticEvidenceReason::NameHint)
}

fn apply_signature_projection_to_merged(
    merged_signature: &mut Option<FunctionSignatureSpec>,
    function_name: &str,
    projection: FunctionSignatureProjection,
    ptr_bits: u32,
) -> SignatureProjectionResult {
    let mut facts = FunctionTypeFacts {
        merged_signature: merged_signature.take(),
        ..FunctionTypeFacts::default()
    };
    let result = facts.apply_signature_projection(function_name, projection, ptr_bits);
    *merged_signature = facts.merged_signature;
    result
}

fn apply_signature_projection_to_inferred(
    inferred_signature: &mut InferredSignature,
    projection: FunctionSignatureProjection,
    ptr_bits: u32,
) -> SignatureProjectionResult {
    let mut merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    let confidence = projection.signature_confidence();
    let return_confidence = projection.return_confidence;
    let exact_strong_projection =
        projection.exact_arity && projection.has_strong_signature_confidence();
    let param_confidences = (0..projection.signature.params.len())
        .map(|idx| projection.param_confidence(idx))
        .collect::<Vec<_>>();
    let prior_confidence = inferred_signature.confidence;
    let result = apply_signature_projection_to_merged(
        &mut merged_signature,
        &inferred_signature.function_name,
        projection,
        ptr_bits,
    );
    if !result.was_applied() {
        return result;
    }
    if let Some(signature) = merged_signature.as_ref() {
        apply_signature_context_overrides(inferred_signature, Some(signature), ptr_bits);
        if exact_strong_projection && inferred_signature.params.len() > signature.params.len() {
            inferred_signature.params.truncate(signature.params.len());
        }
        if return_confidence >= crate::SIGNATURE_PROJECTION_WEAK_CONFIDENCE
            && let Some(ret_ty) = signature.ret_type.as_ref()
        {
            inferred_signature.ret_type = render_signature_type(ret_ty, ptr_bits);
        }
        for (idx, param) in signature.params.iter().enumerate() {
            if param_confidences.get(idx).is_some_and(|confidence| {
                *confidence >= crate::SIGNATURE_PROJECTION_WEAK_CONFIDENCE
            }) {
                if !param.name.is_empty()
                    && let Some(inferred_param) = inferred_signature.params.get_mut(idx)
                {
                    inferred_param.name = param.name.clone();
                }
                if let Some(ty) = param.ty.as_ref()
                    && let Some(inferred_param) = inferred_signature.params.get_mut(idx)
                {
                    inferred_param.param_type = render_signature_type(ty, ptr_bits);
                }
            }
        }
        inferred_signature.signature = format_signature(
            &inferred_signature.function_name,
            &inferred_signature.ret_type,
            &inferred_signature.params,
        );
        inferred_signature.confidence = prior_confidence.max(confidence);
    }
    result
}

fn semantic_role_param_name_is_weak(name: &str) -> bool {
    crate::signature_param_name_is_weak(name)
}

fn semantic_role_typedef_is_authoritative(name: &str) -> bool {
    crate::role_registry::semantic_typedef_is_authoritative(name)
}

fn heap_allocation_return_type() -> CTypeLike {
    CTypeLike::Typedef("allocation_ptr".to_string())
}

fn merge_role_type_projection(
    projection: &mut SemanticTypeProjection,
    role_projection: crate::role_registry::RoleTypeProjection,
    ptr_bits: u32,
) {
    let crate::role_registry::RoleTypeProjection {
        ret_type,
        pointer_param_indices,
        out_param_indices: _,
        param_type_hints,
        param_name_hints,
    } = role_projection;
    if projection.return_type_hint.is_none() {
        projection.return_type_hint = ret_type;
    }
    projection
        .pointer_param_indices
        .extend(pointer_param_indices);
    for (idx, name) in param_name_hints {
        if !is_generic_arg_name(&name) {
            projection.param_name_hints.entry(idx).or_insert(name);
        }
    }
    for (idx, ty) in param_type_hints {
        merge_param_type_hint(&mut projection.param_type_hints, idx, ty, ptr_bits);
    }
}

fn apply_semantic_claim_type_seeds(
    projection: &mut SemanticTypeProjection,
    claims: &r2sym::SemanticClaimSummary,
    ptr_bits: u32,
) {
    for index in &claims.pointer_param_indices {
        projection.pointer_param_indices.insert(*index);
    }
    for index in &claims.size_param_indices {
        collect_projection_size_arg_hint(projection, *index, "len", ptr_bits);
    }
    for claim in &claims.claims {
        if !claim.allows_type_projection() {
            continue;
        }
        let Some(index) = claim.arg_index else {
            continue;
        };
        match claim.type_seed {
            Some(r2sym::SemanticTypeSeedKind::Pointer) => {
                projection.pointer_param_indices.insert(index);
            }
            Some(r2sym::SemanticTypeSeedKind::ReadOnlyPointer) => {
                projection.pointer_param_indices.insert(index);
            }
            Some(r2sym::SemanticTypeSeedKind::OutParam) => {
                mark_projection_out_param(
                    projection,
                    index,
                    OutParamCertificateEvidence::SemanticTypeSeed,
                    semantic_claim_out_param_source(claim),
                );
            }
            Some(r2sym::SemanticTypeSeedKind::Size) => {
                collect_projection_size_arg_hint(projection, index, "len", ptr_bits);
            }
            Some(
                r2sym::SemanticTypeSeedKind::Return | r2sym::SemanticTypeSeedKind::StructField,
            )
            | None => {}
        }
    }
}

impl SemanticTypeProjection {
    fn from_inputs(
        summary_view: &InterprocSummaryView,
        semantic_artifact: Option<&r2sym::SemanticArtifact>,
        ptr_bits: u32,
    ) -> Self {
        let mut projection = Self::default();
        let claim_summary = semantic_artifact.map(r2sym::SemanticArtifact::semantic_claim_summary);
        if let Some(claims) = claim_summary.as_ref() {
            apply_semantic_claim_type_seeds(&mut projection, claims, ptr_bits);
        }
        let certified_summary_roles = claim_summary
            .as_ref()
            .map(summary_role_keys)
            .unwrap_or_default();
        if let Some(summary) = summary_view.root_summary() {
            for idx in 0..=summary.arg_effects.keys().copied().max().unwrap_or(0) {
                if summary_suggests_pointer_param(summary, idx) {
                    projection.pointer_param_indices.insert(idx);
                }
            }
            for (effect_index, (idx, effect)) in summary.arg_effects.iter().enumerate() {
                if effect.write {
                    mark_projection_out_param(
                        &mut projection,
                        *idx,
                        OutParamCertificateEvidence::InterprocArgWrite,
                        interproc_out_param_source(
                            summary,
                            OutParamCertificateEvidence::InterprocArgWrite,
                            *idx,
                            effect_index,
                        ),
                    );
                }
            }
            for (effect_index, effect) in summary.memory_effects.iter().enumerate() {
                if effect.kind == r2ssa::SummaryMemoryEffectKind::Write
                    && let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region
                {
                    projection.pointer_param_indices.insert(index);
                    mark_projection_out_param(
                        &mut projection,
                        index,
                        OutParamCertificateEvidence::InterprocMemoryWrite,
                        interproc_out_param_source(
                            summary,
                            OutParamCertificateEvidence::InterprocMemoryWrite,
                            index,
                            effect_index,
                        ),
                    );
                }
            }
            for (effect_index, effect) in summary.transfer_effects.iter().enumerate() {
                if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.dst.region {
                    projection.pointer_param_indices.insert(index);
                    mark_projection_out_param(
                        &mut projection,
                        index,
                        OutParamCertificateEvidence::InterprocTransferDst,
                        interproc_out_param_source(
                            summary,
                            OutParamCertificateEvidence::InterprocTransferDst,
                            index,
                            effect_index,
                        ),
                    );
                }
                if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.src.region {
                    projection.pointer_param_indices.insert(index);
                }
            }
            for effect in &summary.lifetime_effects {
                projection.pointer_param_indices.insert(effect.arg);
            }
            for effect in &summary.sync_effects {
                projection.pointer_param_indices.insert(effect.arg);
            }
        }
        if let Some(native) = semantic_artifact.and_then(r2sym::SemanticArtifact::native_body) {
            if let Some(role) = native.summary.role_identity.as_ref()
                && let Some(role_projection) =
                    crate::role_registry::type_projection_for_role_identity(role, 0)
            {
                merge_role_type_projection(&mut projection, role_projection, ptr_bits);
            }
            for summary in &native.summary.worker_summaries {
                collect_worker_summary_type_hints(
                    summary,
                    &mut projection,
                    ptr_bits,
                    &certified_summary_roles,
                );
            }
            for summary in &native.summary.region_summaries {
                collect_region_summary_type_hints(
                    summary,
                    &mut projection,
                    ptr_bits,
                    &certified_summary_roles,
                );
            }
        }
        projection.slot_field_profiles =
            collect_semantic_slot_profiles(semantic_artifact, ptr_bits);
        projection
    }

    fn corroborates_param_type_hint(&self, index: usize, hint: &CTypeLike) -> bool {
        if self
            .param_type_hints
            .get(&index)
            .is_some_and(|semantic_hint| semantic_hints_compatible(semantic_hint, hint))
        {
            return true;
        }
        if !matches!(hint, CTypeLike::Pointer(_)) {
            return false;
        }
        self.pointer_param_indices.contains(&index)
            || self.out_param_indices.contains(&index)
            || self.slot_field_profiles.contains_key(&index)
    }

    fn corroborates_stack_slot_type_hint(&self, slot: usize, hint: &CTypeLike) -> bool {
        matches!(hint, CTypeLike::Pointer(_)) && self.slot_field_profiles.contains_key(&slot)
    }

    fn refusal_warnings(&self) -> Vec<String> {
        self.refused_param_projections
            .iter()
            .map(|(idx, reason)| format!("semantic type projection refused arg{idx}: {reason}"))
            .collect()
    }
}

struct VarTypeCandidateContext<'a> {
    current_context_maps: &'a SignatureContextMaps,
    merged_signature: Option<&'a FunctionSignatureSpec>,
    slot_type_overrides: &'a HashMap<usize, String>,
    stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    existing_types: &'a HashMap<String, String>,
    ptr_bits: u32,
    is_main_signature: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum VisibleBindingKey {
    Param(usize),
    Stack(StackSlotKey),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct RecoveredVarKey {
    name: String,
    kind: String,
    delta: i64,
    isarg: bool,
    reg: Option<String>,
}

impl RecoveredVarKey {
    fn new(name: &str, kind: &str, delta: i64, isarg: bool, reg: Option<&str>) -> Self {
        Self {
            name: name.to_ascii_lowercase(),
            kind: kind.to_ascii_lowercase(),
            delta,
            isarg,
            reg: reg.map(str::to_ascii_lowercase),
        }
    }

    fn for_recovered_var(var: &RecoveredVariable) -> Self {
        Self::new(
            &var.name,
            &var.kind,
            var.delta,
            var.isarg,
            var.reg.as_deref(),
        )
    }

    fn for_type_candidate(candidate: &VarTypeCandidate) -> Self {
        Self::new(
            &candidate.name,
            &candidate.kind,
            candidate.delta,
            candidate.isarg,
            candidate.reg.as_deref(),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GlobalAddrExpr {
    base: u64,
    offset: i64,
    confidence: u8,
}

fn summary_arg_effect_to_callee(effect: &SummaryArgEffect) -> CalleeArgEffect {
    CalleeArgEffect {
        read: effect.read,
        write: effect.write,
        escape: effect.escape,
        free: effect.free,
    }
}

fn summary_return_relation_to_callee(relation: &SummaryReturnRelation) -> CalleeReturnRelation {
    match relation {
        SummaryReturnRelation::Unknown => CalleeReturnRelation::Unknown,
        SummaryReturnRelation::Void => CalleeReturnRelation::Void,
        SummaryReturnRelation::Arg(idx) => CalleeReturnRelation::Arg(*idx),
        SummaryReturnRelation::Const(value) => CalleeReturnRelation::Const(*value),
        SummaryReturnRelation::HeapAlloc => CalleeReturnRelation::HeapAlloc,
        SummaryReturnRelation::Global(address) => CalleeReturnRelation::Global(*address),
    }
}

fn summary_memory_effect_to_callee(effect: &SummaryMemoryEffect) -> CalleeMemoryEffect {
    let kind = match effect.kind {
        SummaryMemoryEffectKind::Read => CalleeMemoryEffectKind::Read,
        SummaryMemoryEffectKind::Write => CalleeMemoryEffectKind::Write,
        SummaryMemoryEffectKind::Escape => CalleeMemoryEffectKind::Escape,
        SummaryMemoryEffectKind::Free => CalleeMemoryEffectKind::Free,
    };
    let location = CalleeMemoryLocation {
        region: match effect.location.region {
            SummaryMemoryRegion::Arg { index } => CalleeMemoryRegion::Arg { index },
            SummaryMemoryRegion::Global { address } => CalleeMemoryRegion::Global { address },
            SummaryMemoryRegion::HeapReturn => CalleeMemoryRegion::HeapReturn,
            SummaryMemoryRegion::Unknown => CalleeMemoryRegion::Unknown,
        },
        range: effect.location.range.map(|range| CalleeMemoryRange {
            offset_lo: range.offset_lo,
            offset_hi: range.offset_hi,
            width: range.width,
        }),
    };
    CalleeMemoryEffect { kind, location }
}

fn summary_location_to_callee(location: r2ssa::SummaryMemoryLocation) -> CalleeMemoryLocation {
    CalleeMemoryLocation {
        region: match location.region {
            r2ssa::SummaryMemoryRegion::Arg { index } => CalleeMemoryRegion::Arg { index },
            r2ssa::SummaryMemoryRegion::Global { address } => {
                CalleeMemoryRegion::Global { address }
            }
            r2ssa::SummaryMemoryRegion::HeapReturn => CalleeMemoryRegion::HeapReturn,
            r2ssa::SummaryMemoryRegion::Unknown => CalleeMemoryRegion::Unknown,
        },
        range: location.range.map(|range| CalleeMemoryRange {
            offset_lo: range.offset_lo,
            offset_hi: range.offset_hi,
            width: range.width,
        }),
    }
}

fn summary_transfer_effect_to_callee(
    effect: &r2ssa::SummaryTransferEffect,
) -> CalleeTransferEffect {
    CalleeTransferEffect {
        dst: summary_location_to_callee(effect.dst),
        src: summary_location_to_callee(effect.src),
        len: match effect.len {
            r2ssa::SummaryTransferLength::Arg(index) => CalleeTransferLength::Arg(index),
            r2ssa::SummaryTransferLength::Const(value) => CalleeTransferLength::Const(value),
            r2ssa::SummaryTransferLength::Unknown => CalleeTransferLength::Unknown,
        },
    }
}

fn summary_allocation_effect_to_callee(
    effect: &r2ssa::SummaryAllocationEffect,
) -> CalleeAllocationEffect {
    CalleeAllocationEffect {
        size_arg: effect.size_arg,
        zeroed: effect.zeroed,
    }
}

fn summary_lifetime_effect_to_callee(
    effect: &r2ssa::SummaryLifetimeEffect,
) -> CalleeLifetimeEffect {
    CalleeLifetimeEffect {
        arg: effect.arg,
        op: match effect.op {
            r2ssa::SummaryLifetimeOp::Free => CalleeLifetimeOp::Free,
            r2ssa::SummaryLifetimeOp::Retain => CalleeLifetimeOp::Retain,
            r2ssa::SummaryLifetimeOp::Release => CalleeLifetimeOp::Release,
        },
    }
}

fn summary_sync_effect_to_callee(effect: &r2ssa::SummarySyncEffect) -> CalleeSyncEffect {
    CalleeSyncEffect {
        arg: effect.arg,
        op: match effect.op {
            r2ssa::SummarySyncOp::Lock => CalleeSyncOp::Lock,
            r2ssa::SummarySyncOp::Unlock => CalleeSyncOp::Unlock,
        },
    }
}

fn summary_atomic_effect_to_callee(effect: &r2ssa::SummaryAtomicEffect) -> CalleeAtomicEffect {
    CalleeAtomicEffect {
        op: match effect.op {
            r2ssa::SummaryAtomicOp::LoadLinked => CalleeAtomicOp::LoadLinked,
            r2ssa::SummaryAtomicOp::StoreConditional => CalleeAtomicOp::StoreConditional,
            r2ssa::SummaryAtomicOp::CompareExchange => CalleeAtomicOp::CompareExchange,
            r2ssa::SummaryAtomicOp::Fence => CalleeAtomicOp::Fence,
        },
        location: summary_location_to_callee(effect.location),
        ordering: match effect.ordering {
            r2ssa::SummaryAtomicOrdering::Relaxed => CalleeAtomicOrdering::Relaxed,
            r2ssa::SummaryAtomicOrdering::Acquire => CalleeAtomicOrdering::Acquire,
            r2ssa::SummaryAtomicOrdering::Release => CalleeAtomicOrdering::Release,
            r2ssa::SummaryAtomicOrdering::AcqRel => CalleeAtomicOrdering::AcqRel,
            r2ssa::SummaryAtomicOrdering::SeqCst => CalleeAtomicOrdering::SeqCst,
            r2ssa::SummaryAtomicOrdering::Unknown => CalleeAtomicOrdering::Unknown,
        },
    }
}

fn summary_observed_param_count(summary: &FunctionSemanticSummary) -> usize {
    let mut max_idx = summary.arg_effects.keys().copied().max();
    for effect in &summary.memory_effects {
        if let SummaryMemoryRegion::Arg { index } = effect.location.region {
            max_idx = Some(max_idx.unwrap_or(0).max(index));
        }
    }
    for effect in &summary.transfer_effects {
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.dst.region {
            max_idx = Some(max_idx.unwrap_or(0).max(index));
        }
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.src.region {
            max_idx = Some(max_idx.unwrap_or(0).max(index));
        }
        if let r2ssa::SummaryTransferLength::Arg(index) = effect.len {
            max_idx = Some(max_idx.unwrap_or(0).max(index));
        }
    }
    for effect in &summary.lifetime_effects {
        max_idx = Some(max_idx.unwrap_or(0).max(effect.arg));
    }
    for effect in &summary.sync_effects {
        max_idx = Some(max_idx.unwrap_or(0).max(effect.arg));
    }
    max_idx.map_or(0, |idx| idx + 1)
}

fn summary_param_type_hints(
    summary: &FunctionSemanticSummary,
    role_projection: Option<&crate::role_registry::RoleTypeProjection>,
) -> BTreeMap<usize, CTypeLike> {
    let pointer_ty = CTypeLike::Pointer(Box::new(CTypeLike::Void));
    let mut hints = role_projection
        .map(|projection| projection.param_type_hints.clone())
        .unwrap_or_default();
    let max_idx = summary_observed_param_count(summary);
    for idx in 0..max_idx {
        if summary_suggests_pointer_param(summary, idx) {
            hints.entry(idx).or_insert_with(|| pointer_ty.clone());
        }
    }
    hints
}

fn summary_return_type_hint(
    summary: &FunctionSemanticSummary,
    param_type_hints: &BTreeMap<usize, CTypeLike>,
    role_projection: Option<&crate::role_registry::RoleTypeProjection>,
) -> Option<CTypeLike> {
    match summary.return_relation {
        SummaryReturnRelation::Void => Some(CTypeLike::Void),
        SummaryReturnRelation::HeapAlloc => Some(heap_allocation_return_type()),
        SummaryReturnRelation::Arg(idx) => param_type_hints.get(&idx).cloned(),
        _ => role_projection.and_then(|projection| projection.ret_type.clone()),
    }
}

fn summary_linkage_to_callee_linkage(
    linkage: r2ssa::FunctionSemanticLinkage,
) -> crate::CalleeLinkage {
    match linkage {
        r2ssa::FunctionSemanticLinkage::Unknown => crate::CalleeLinkage::Unknown,
        r2ssa::FunctionSemanticLinkage::Internal => crate::CalleeLinkage::Internal,
        r2ssa::FunctionSemanticLinkage::Imported => crate::CalleeLinkage::Imported,
    }
}

fn summary_to_callee_fact(summary: &FunctionSemanticSummary) -> CalleeFact {
    let param_type_hints = summary_param_type_hints(summary, None);
    let return_type_hint = summary_return_type_hint(summary, &param_type_hints, None);
    let arg_effects = summary
        .arg_effects
        .iter()
        .map(|(idx, effect)| (*idx, summary_arg_effect_to_callee(effect)))
        .collect::<BTreeMap<_, _>>();
    CalleeFact {
        function_id: summary.id.0,
        name: summary.name.clone(),
        linkage: summary_linkage_to_callee_linkage(summary.linkage),
        signature: None,
        signature_callconv: None,
        signature_noreturn: false,
        model_policy_evidence: BTreeSet::from([CalleeModelPolicyEvidence::InterprocSummary]),
        direct_callees: summary.direct_callees.iter().copied().collect(),
        callsite_count: summary.callsite_count,
        has_unknown_calls: summary.has_unknown_calls,
        arg_effects,
        memory_effects: summary
            .memory_effects
            .iter()
            .map(summary_memory_effect_to_callee)
            .collect(),
        transfer_effects: summary
            .transfer_effects
            .iter()
            .map(summary_transfer_effect_to_callee)
            .collect(),
        allocation_effects: summary
            .allocation_effects
            .iter()
            .map(summary_allocation_effect_to_callee)
            .collect(),
        lifetime_effects: summary
            .lifetime_effects
            .iter()
            .map(summary_lifetime_effect_to_callee)
            .collect(),
        sync_effects: summary
            .sync_effects
            .iter()
            .map(summary_sync_effect_to_callee)
            .collect(),
        atomic_effects: summary
            .atomic_effects
            .iter()
            .map(summary_atomic_effect_to_callee)
            .collect(),
        param_type_hints,
        return_type_hint,
        return_relation: summary_return_relation_to_callee(&summary.return_relation),
        reads_global_memory: summary.reads_global_memory,
        writes_global_memory: summary.writes_global_memory,
        touches_unknown_memory: summary.touches_unknown_memory,
    }
}

fn callee_linkage_rank(linkage: crate::CalleeLinkage) -> u8 {
    match linkage {
        crate::CalleeLinkage::Unknown => 0,
        crate::CalleeLinkage::Internal => 1,
        crate::CalleeLinkage::Imported => 2,
    }
}

fn merge_callee_fact(existing: &mut CalleeFact, incoming: CalleeFact) {
    if existing.name.is_none() {
        existing.name = incoming.name;
    }
    if callee_linkage_rank(incoming.linkage) > callee_linkage_rank(existing.linkage) {
        existing.linkage = incoming.linkage;
    }
    existing
        .model_policy_evidence
        .extend(incoming.model_policy_evidence);
    if existing.direct_callees.is_empty() {
        existing.direct_callees = incoming.direct_callees;
    }
    existing.callsite_count = existing.callsite_count.max(incoming.callsite_count);
    existing.has_unknown_calls |= incoming.has_unknown_calls;
    if existing.arg_effects.is_empty() {
        existing.arg_effects = incoming.arg_effects;
    }
    if existing.memory_effects.is_empty() {
        existing.memory_effects = incoming.memory_effects;
    }
    if existing.transfer_effects.is_empty() {
        existing.transfer_effects = incoming.transfer_effects;
    }
    if existing.allocation_effects.is_empty() {
        existing.allocation_effects = incoming.allocation_effects;
    }
    if existing.lifetime_effects.is_empty() {
        existing.lifetime_effects = incoming.lifetime_effects;
    }
    if existing.sync_effects.is_empty() {
        existing.sync_effects = incoming.sync_effects;
    }
    if existing.atomic_effects.is_empty() {
        existing.atomic_effects = incoming.atomic_effects;
    }
    if existing.param_type_hints.is_empty() {
        existing.param_type_hints = incoming.param_type_hints;
    }
    if existing.return_type_hint.is_none() {
        existing.return_type_hint = incoming.return_type_hint;
    }
    if matches!(
        existing.return_relation,
        crate::CalleeReturnRelation::Unknown
    ) {
        existing.return_relation = incoming.return_relation;
    }
    existing.reads_global_memory |= incoming.reads_global_memory;
    existing.writes_global_memory |= incoming.writes_global_memory;
    existing.touches_unknown_memory |= incoming.touches_unknown_memory;
}

fn merged_context_and_summary_callee_facts(
    context_facts: &BTreeMap<u64, CalleeFact>,
    summary_set: Option<&r2ssa::InterprocSummarySet>,
) -> BTreeMap<u64, CalleeFact> {
    let mut facts = context_facts.clone();
    if let Some(summary_set) = summary_set {
        for (id, summary) in &summary_set.summaries {
            if Some(*id) == summary_set.root {
                continue;
            }
            let incoming = summary_to_callee_fact(summary);
            match facts.entry(id.0) {
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    merge_callee_fact(entry.get_mut(), incoming);
                }
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(incoming);
                }
            }
        }
    }
    facts
}

fn infer_interproc_return_type(
    summary: &FunctionSemanticSummary,
    merged_signature: Option<&FunctionSignatureSpec>,
    inferred_signature: &InferredSignature,
    ptr_bits: u32,
) -> Option<CTypeLike> {
    match summary.return_relation {
        SummaryReturnRelation::Void => Some(CTypeLike::Void),
        SummaryReturnRelation::HeapAlloc => Some(heap_allocation_return_type()),
        SummaryReturnRelation::Arg(idx) => merged_signature
            .and_then(|signature| signature.params.get(idx))
            .and_then(|param| param.ty.clone())
            .filter(|ty| !is_generic_signature_type(Some(ty)))
            .or_else(|| {
                inferred_signature
                    .params
                    .get(idx)
                    .and_then(|param| parse_type_like_spec(&param.param_type, ptr_bits))
                    .filter(|ty| !is_generic_signature_type(Some(ty)))
            }),
        _ => None,
    }
}

fn summary_suggests_pointer_param(summary: &FunctionSemanticSummary, idx: usize) -> bool {
    summary
        .arg_effects
        .get(&idx)
        .is_some_and(|effect| effect.read || effect.write || effect.escape || effect.free)
        || summary.memory_effects.iter().any(|effect| {
            matches!(effect.location.region, SummaryMemoryRegion::Arg { index } if index == idx)
        })
        || summary.transfer_effects.iter().any(|effect| {
            matches!(effect.dst.region, r2ssa::SummaryMemoryRegion::Arg { index } if index == idx)
                || matches!(effect.src.region, r2ssa::SummaryMemoryRegion::Arg { index } if index == idx)
        })
        || summary
            .lifetime_effects
            .iter()
            .any(|effect| effect.arg == idx)
        || summary.sync_effects.iter().any(|effect| effect.arg == idx)
}

fn maybe_upgrade_param_to_pointer(
    summary: &FunctionSemanticSummary,
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    ptr_bits: u32,
) {
    let pointer_ty = CTypeLike::Pointer(Box::new(CTypeLike::Void));

    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }

    let Some(signature) = merged_signature.as_mut() else {
        return;
    };

    for idx in 0..signature.params.len().max(inferred_signature.params.len()) {
        if !summary_suggests_pointer_param(summary, idx) {
            continue;
        }

        let merged_param = signature.params.get_mut(idx);
        let inferred_param = inferred_signature.params.get_mut(idx);

        if merged_param
            .as_ref()
            .is_some_and(|param| param_has_authoritative_named_scalar_role(param, ptr_bits))
            || inferred_param.as_ref().is_some_and(|param| {
                inferred_param_has_authoritative_named_scalar_role(param, ptr_bits)
            })
        {
            continue;
        }

        let merged_is_generic = merged_param.as_ref().is_some_and(|param| {
            param.ty.as_ref().is_none_or(|ty| {
                is_generic_signature_type(Some(ty))
                    || matches!(
                        ty,
                        CTypeLike::Int {
                            bits,
                            signedness: Signedness::Signed
                                | Signedness::Unsigned
                                | Signedness::Unknown,
                        } if *bits == ptr_bits
                    )
            })
        });

        let inferred_is_generic = inferred_param.as_ref().is_some_and(|param| {
            is_generic_type_string(&param.param_type)
                || matches!(
                    parse_type_like_spec(&param.param_type, ptr_bits),
                    Some(CTypeLike::Int {
                        bits,
                        signedness: Signedness::Signed
                            | Signedness::Unsigned
                            | Signedness::Unknown,
                    }) if bits == ptr_bits
                )
        });

        if merged_is_generic && let Some(param) = merged_param {
            param.ty = Some(pointer_ty.clone());
        }
        if inferred_is_generic && let Some(param) = inferred_param {
            param.param_type = render_signature_type(&pointer_ty, ptr_bits);
        }
    }
}

fn upgrade_param_indices_to_pointer(
    indices: impl IntoIterator<Item = usize>,
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    ptr_bits: u32,
) {
    let pointer_ty = CTypeLike::Pointer(Box::new(CTypeLike::Void));

    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }

    let Some(signature) = merged_signature.as_mut() else {
        return;
    };

    for idx in indices {
        let merged_param = signature.params.get_mut(idx);
        let inferred_param = inferred_signature.params.get_mut(idx);

        if merged_param
            .as_ref()
            .is_some_and(|param| param_has_authoritative_named_scalar_role(param, ptr_bits))
            || inferred_param.as_ref().is_some_and(|param| {
                inferred_param_has_authoritative_named_scalar_role(param, ptr_bits)
            })
        {
            continue;
        }

        let merged_is_generic = merged_param.as_ref().is_some_and(|param| {
            param.ty.as_ref().is_none_or(|ty| {
                is_generic_signature_type(Some(ty))
                    || matches!(
                        ty,
                        CTypeLike::Int {
                            bits,
                            signedness: Signedness::Signed
                                | Signedness::Unsigned
                                | Signedness::Unknown,
                        } if *bits == ptr_bits
                    )
            })
        });

        let inferred_is_generic = inferred_param.as_ref().is_some_and(|param| {
            is_generic_type_string(&param.param_type)
                || matches!(
                    parse_type_like_spec(&param.param_type, ptr_bits),
                    Some(CTypeLike::Int {
                        bits,
                        signedness: Signedness::Signed
                            | Signedness::Unsigned
                            | Signedness::Unknown,
                    }) if bits == ptr_bits
                )
        });

        if merged_is_generic && let Some(param) = merged_param {
            param.ty = Some(pointer_ty.clone());
        }
        if inferred_is_generic && let Some(param) = inferred_param {
            param.param_type = render_signature_type(&pointer_ty, ptr_bits);
        }
    }
}

fn type_is_authoritative_named_scalar_role(ty: &CTypeLike) -> bool {
    match ty {
        CTypeLike::Bool | CTypeLike::Enum(_) => true,
        CTypeLike::Typedef(name) => {
            matches!(
                name.trim().to_ascii_lowercase().as_str(),
                "int" | "unsigned int"
            ) || semantic_role_typedef_is_authoritative(name)
        }
        _ => false,
    }
}

fn param_has_authoritative_named_scalar_role(param: &FunctionParamSpec, _ptr_bits: u32) -> bool {
    !semantic_role_param_name_is_weak(&param.name)
        && param
            .ty
            .as_ref()
            .is_some_and(type_is_authoritative_named_scalar_role)
}

fn inferred_param_has_authoritative_named_scalar_role(
    param: &InferredSignatureParam,
    ptr_bits: u32,
) -> bool {
    if semantic_role_param_name_is_weak(&param.name) {
        return false;
    }
    parse_signature_type_preserving_c_typedefs(&param.param_type, ptr_bits)
        .as_ref()
        .is_some_and(type_is_authoritative_named_scalar_role)
}

fn summary_hint_can_replace_weak_existing(
    existing: &CTypeLike,
    hint: &CTypeLike,
    ptr_bits: u32,
) -> bool {
    crate::summary_hint_can_replace_weak_existing(existing, hint, ptr_bits)
}

fn upgrade_param_type_hints(
    hints: &BTreeMap<usize, CTypeLike>,
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    ptr_bits: u32,
) {
    if hints.is_empty() {
        return;
    }
    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }

    if let Some(signature) = merged_signature.as_mut() {
        for (idx, hint) in hints {
            if let Some(param) = signature.params.get_mut(*idx) {
                let should_replace = param.ty.as_ref().is_none_or(|existing| {
                    summary_hint_can_replace_weak_existing(existing, hint, ptr_bits)
                });
                if should_replace {
                    param.ty = Some(hint.clone());
                }
            }
        }
    }

    for (idx, hint) in hints {
        if let Some(param) = inferred_signature.params.get_mut(*idx) {
            let existing_ty = parse_type_like_spec(&param.param_type, ptr_bits);
            let should_replace = is_generic_type_string(&param.param_type)
                || existing_ty.as_ref().is_some_and(|existing| {
                    summary_hint_can_replace_weak_existing(existing, hint, ptr_bits)
                });
            if should_replace {
                param.param_type = render_signature_type(hint, ptr_bits);
            }
        }
    }
}

fn upgrade_return_type_hint(
    hint: Option<&CTypeLike>,
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    ptr_bits: u32,
) -> bool {
    let Some(hint) = hint else {
        return false;
    };
    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }

    let mut changed = false;
    if let Some(signature) = merged_signature.as_mut() {
        let should_replace = signature.ret_type.as_ref().is_none_or(|existing| {
            summary_hint_can_replace_weak_existing(existing, hint, ptr_bits)
                || matches!(hint, CTypeLike::Void)
                    && crate::signature_return_hint_can_replace_existing(
                        existing,
                        Some(hint),
                        ptr_bits,
                    )
        });
        if should_replace && signature.ret_type.as_ref() != Some(hint) {
            signature.ret_type = Some(hint.clone());
            changed = true;
        }
    }

    let existing_ty = parse_type_like_spec(&inferred_signature.ret_type, ptr_bits);
    let should_replace = is_generic_type_string(&inferred_signature.ret_type)
        || existing_ty.as_ref().is_some_and(|existing| {
            summary_hint_can_replace_weak_existing(existing, hint, ptr_bits)
                || matches!(hint, CTypeLike::Void)
                    && crate::signature_return_hint_can_replace_existing(
                        existing,
                        Some(hint),
                        ptr_bits,
                    )
        });
    if should_replace {
        let rendered = render_signature_type(hint, ptr_bits);
        if inferred_signature.ret_type != rendered {
            inferred_signature.ret_type = rendered;
            changed = true;
        }
    }
    if changed {
        inferred_signature.signature = format_signature(
            &inferred_signature.function_name,
            &inferred_signature.ret_type,
            &inferred_signature.params,
        );
    }
    changed
}

fn upgrade_param_name_hints(
    hints: &BTreeMap<usize, String>,
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    ptr_bits: u32,
) {
    if hints.is_empty() {
        return;
    }
    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }
    if let Some(signature) = merged_signature.as_mut() {
        for (idx, hint) in hints {
            if let Some(param) = signature.params.get_mut(*idx)
                && (param.name.is_empty() || is_generic_arg_name(&param.name))
            {
                param.name = hint.clone();
            }
        }
    }
    for (idx, hint) in hints {
        if let Some(param) = inferred_signature.params.get_mut(*idx)
            && (param.name.is_empty() || is_generic_arg_name(&param.name))
        {
            param.name = hint.clone();
        }
    }
    inferred_signature.signature = format_signature(
        &inferred_signature.function_name,
        &inferred_signature.ret_type,
        &inferred_signature.params,
    );
}

fn projection_pointer_upgrade_indices(projection: &SemanticTypeProjection) -> Vec<usize> {
    projection
        .pointer_param_indices
        .iter()
        .copied()
        .filter(|idx| {
            projection
                .param_type_hints
                .get(idx)
                .is_none_or(|ty| matches!(ty, CTypeLike::Pointer(_)))
        })
        .collect()
}

fn apply_interproc_summary_to_signature(
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    summary_view: &InterprocSummaryView,
    semantic_projection: Option<&SemanticTypeProjection>,
    ptr_bits: u32,
) {
    let Some(summary) = summary_view.root_summary() else {
        if let Some(projection) = semantic_projection {
            upgrade_return_type_hint(
                projection.return_type_hint.as_ref(),
                merged_signature,
                inferred_signature,
                ptr_bits,
            );
            upgrade_param_name_hints(
                &projection.param_name_hints,
                merged_signature,
                inferred_signature,
                ptr_bits,
            );
            upgrade_param_indices_to_pointer(
                projection_pointer_upgrade_indices(projection),
                merged_signature,
                inferred_signature,
                ptr_bits,
            );
            upgrade_param_type_hints(
                &projection.param_type_hints,
                merged_signature,
                inferred_signature,
                ptr_bits,
            );
        }
        return;
    };
    maybe_upgrade_param_to_pointer(summary, merged_signature, inferred_signature, ptr_bits);
    if let Some(projection) = semantic_projection {
        upgrade_return_type_hint(
            projection.return_type_hint.as_ref(),
            merged_signature,
            inferred_signature,
            ptr_bits,
        );
        upgrade_param_name_hints(
            &projection.param_name_hints,
            merged_signature,
            inferred_signature,
            ptr_bits,
        );
        upgrade_param_indices_to_pointer(
            projection_pointer_upgrade_indices(projection),
            merged_signature,
            inferred_signature,
            ptr_bits,
        );
        upgrade_param_type_hints(
            &projection.param_type_hints,
            merged_signature,
            inferred_signature,
            ptr_bits,
        );
    }
    let Some(ret_ty) = infer_interproc_return_type(
        summary,
        merged_signature.as_ref(),
        inferred_signature,
        ptr_bits,
    ) else {
        return;
    };

    let should_override = merged_signature
        .as_ref()
        .and_then(|signature| signature.ret_type.as_ref())
        .is_none_or(|ty| {
            is_generic_signature_type(Some(ty))
                || summary_hint_can_replace_weak_existing(ty, &ret_ty, ptr_bits)
                || matches!(summary.return_relation, SummaryReturnRelation::HeapAlloc)
                    && crate::signature_hint_can_replace_existing(ty, Some(&ret_ty), ptr_bits)
                || matches!(ret_ty, CTypeLike::Void)
                    && crate::signature_return_hint_can_replace_existing(
                        ty,
                        Some(&ret_ty),
                        ptr_bits,
                    )
                || matches!(
                    (&ret_ty, ty),
                    (
                        CTypeLike::Pointer(_),
                        CTypeLike::Int {
                            bits,
                            signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
                        }
                    ) if *bits == ptr_bits
                )
        });
    if !should_override {
        return;
    }

    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }
    if let Some(signature) = merged_signature.as_mut() {
        signature.ret_type = Some(ret_ty.clone());
    }

    if is_generic_type_string(&inferred_signature.ret_type)
        || parse_type_like_spec(&inferred_signature.ret_type, ptr_bits)
            .is_some_and(|ty| summary_hint_can_replace_weak_existing(&ty, &ret_ty, ptr_bits))
        || matches!(summary.return_relation, SummaryReturnRelation::HeapAlloc)
            && parse_type_like_spec(&inferred_signature.ret_type, ptr_bits).is_some_and(|ty| {
                crate::signature_hint_can_replace_existing(&ty, Some(&ret_ty), ptr_bits)
            })
        || matches!(ret_ty, CTypeLike::Void)
            && parse_type_like_spec(&inferred_signature.ret_type, ptr_bits).is_some_and(|ty| {
                crate::signature_return_hint_can_replace_existing(&ty, Some(&ret_ty), ptr_bits)
            })
        || matches!(
            parse_type_like_spec(&inferred_signature.ret_type, ptr_bits),
            Some(CTypeLike::Int {
                bits,
                signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
            }) if bits == ptr_bits
        )
    {
        inferred_signature.ret_type = render_signature_type(&ret_ty, ptr_bits);
    }
}

fn assumption_type_hint(
    assumption: &r2ssa::AnalysisAssumption,
    ptr_bits: u32,
) -> Option<CTypeLike> {
    let r2ssa::AssumptionValue::TypeHint { ty } = &assumption.value else {
        return None;
    };
    parse_signature_type_preserving_c_typedefs(ty, ptr_bits)
}

fn type_hint_conflicts(existing: &CTypeLike, hint: &CTypeLike, ptr_bits: u32) -> bool {
    render_signature_type(existing, ptr_bits) != render_signature_type(hint, ptr_bits)
}

fn type_hint_requires_semantic_corroboration(assumption: &r2ssa::AnalysisAssumption) -> bool {
    matches!(assumption.provenance, r2ssa::AssumptionProvenance::Derived)
}

fn type_hint_can_replace_weak_existing(
    assumption: &r2ssa::AnalysisAssumption,
    existing: &CTypeLike,
    binding_name: Option<&str>,
    ptr_bits: u32,
) -> bool {
    if is_generic_signature_type(Some(existing)) {
        return true;
    }

    match assumption.provenance {
        r2ssa::AssumptionProvenance::User | r2ssa::AssumptionProvenance::ImportedContext => {
            let generic_binding = binding_name.is_none_or(is_generic_arg_name);
            generic_binding
                && matches!(
                    existing,
                    CTypeLike::Int {
                        bits,
                        signedness: Signedness::Signed
                            | Signedness::Unsigned
                            | Signedness::Unknown,
                    } if *bits == ptr_bits
                )
        }
        r2ssa::AssumptionProvenance::Replay | r2ssa::AssumptionProvenance::Derived => false,
    }
}

fn apply_type_hint_to_signature_param(
    merged_signature: &mut Option<FunctionSignatureSpec>,
    inferred_signature: &mut InferredSignature,
    index: usize,
    assumption: &r2ssa::AnalysisAssumption,
    hint: &CTypeLike,
    ptr_bits: u32,
) -> Result<bool, String> {
    if merged_signature.is_none() {
        *merged_signature = inferred_signature_to_spec(inferred_signature, ptr_bits);
    }

    let mut applied = false;
    if let Some(signature) = merged_signature.as_mut() {
        let Some(param) = signature.params.get_mut(index) else {
            return Ok(false);
        };
        match param.ty.as_ref() {
            None => {
                param.ty = Some(hint.clone());
                applied = true;
            }
            Some(existing)
                if type_hint_can_replace_weak_existing(
                    assumption,
                    existing,
                    Some(&param.name),
                    ptr_bits,
                ) =>
            {
                param.ty = Some(hint.clone());
                applied = true;
            }
            Some(existing) if !type_hint_conflicts(existing, hint, ptr_bits) => {
                applied = true;
            }
            Some(existing) => {
                return Err(format!(
                    "parameter {} already has incompatible type {}",
                    index,
                    render_signature_type(existing, ptr_bits)
                ));
            }
        }
    }

    if let Some(param) = inferred_signature.params.get_mut(index) {
        let existing_ty = parse_type_like_spec(&param.param_type, ptr_bits);
        let can_replace = is_generic_type_string(&param.param_type)
            || existing_ty.as_ref().is_some_and(|existing| {
                type_hint_can_replace_weak_existing(
                    assumption,
                    existing,
                    Some(&param.name),
                    ptr_bits,
                )
            });
        if can_replace {
            param.param_type = render_signature_type(hint, ptr_bits);
            applied = true;
        }
    }

    Ok(applied)
}

fn assumption_stack_base(base: &str) -> Option<ExternalStackBase> {
    match base.trim().to_ascii_lowercase().as_str() {
        "bp" | "rbp" | "ebp" | "frame" | "fp" => Some(ExternalStackBase::FramePointer),
        "sp" | "rsp" | "esp" | "stack" => Some(ExternalStackBase::StackPointer),
        "" => None,
        other => Some(ExternalStackBase::Named(other.to_string())),
    }
}

fn apply_type_hint_assumptions_to_context(
    parsed_context: &mut ParsedExternalContext,
    inferred_signature: &mut InferredSignature,
    ptr_bits: u32,
    semantic_projection: Option<&SemanticTypeProjection>,
) -> r2ssa::AssumptionUsageReport {
    let mut usage = r2ssa::AssumptionUsageReport::default();
    let assumptions = parsed_context.assumptions.items.clone();
    for assumption in &assumptions {
        let Some(hint) = assumption_type_hint(assumption, ptr_bits) else {
            continue;
        };
        match &assumption.subject {
            r2ssa::AssumptionSubject::Parameter { index } => {
                let corroborated = semantic_projection.is_some_and(|projection| {
                    projection.corroborates_param_type_hint(*index, &hint)
                });
                if type_hint_requires_semantic_corroboration(assumption) && !corroborated {
                    usage.mark_ignored(assumption);
                    continue;
                }
                match apply_type_hint_to_signature_param(
                    &mut parsed_context.merged_signature,
                    inferred_signature,
                    *index,
                    assumption,
                    &hint,
                    ptr_bits,
                ) {
                    Ok(true) => usage.mark_applied(assumption),
                    Ok(false) => usage.mark_ignored(assumption),
                    Err(reason) => usage.mark_conflict(assumption, reason),
                }
            }
            r2ssa::AssumptionSubject::Register { name } => {
                let Some((idx, reg_param)) = parsed_context
                    .register_params
                    .iter_mut()
                    .enumerate()
                    .find(|(_, param)| {
                        param.reg.eq_ignore_ascii_case(name)
                            || param.name.eq_ignore_ascii_case(name)
                    })
                else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                let corroborated = semantic_projection
                    .is_some_and(|projection| projection.corroborates_param_type_hint(idx, &hint));
                if type_hint_requires_semantic_corroboration(assumption) && !corroborated {
                    usage.mark_ignored(assumption);
                    continue;
                }

                let reg_applied = match reg_param.ty.as_ref() {
                    None => {
                        reg_param.ty = Some(hint.clone());
                        true
                    }
                    Some(existing)
                        if type_hint_can_replace_weak_existing(
                            assumption,
                            existing,
                            Some(&reg_param.name),
                            ptr_bits,
                        ) =>
                    {
                        reg_param.ty = Some(hint.clone());
                        true
                    }
                    Some(existing) if !type_hint_conflicts(existing, &hint, ptr_bits) => true,
                    Some(existing) => {
                        usage.mark_conflict(
                            assumption,
                            format!(
                                "register {} already has incompatible type {}",
                                name,
                                render_signature_type(existing, ptr_bits)
                            ),
                        );
                        continue;
                    }
                };
                match apply_type_hint_to_signature_param(
                    &mut parsed_context.merged_signature,
                    inferred_signature,
                    idx,
                    assumption,
                    &hint,
                    ptr_bits,
                ) {
                    Ok(true) => usage.mark_applied(assumption),
                    Ok(false) if reg_applied => usage.mark_applied(assumption),
                    Ok(false) => usage.mark_ignored(assumption),
                    Err(reason) => usage.mark_conflict(assumption, reason),
                }
            }
            r2ssa::AssumptionSubject::StackSlot { base, offset } => {
                let Some(base) = assumption_stack_base(base) else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                let key = StackSlotKey {
                    base,
                    offset: *offset,
                };
                let corroborated = semantic_projection.is_some_and(|projection| {
                    parsed_context
                        .stack_slots
                        .get(&key)
                        .and_then(|slot| slot.param_index)
                        .is_some_and(|slot| {
                            projection.corroborates_stack_slot_type_hint(slot, &hint)
                        })
                });
                if type_hint_requires_semantic_corroboration(assumption) && !corroborated {
                    usage.mark_ignored(assumption);
                    continue;
                }
                let Some(slot) = parsed_context.stack_slots.get_mut(&key) else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                let mut applied = match slot.ty.as_ref() {
                    None => {
                        slot.ty = Some(hint.clone());
                        true
                    }
                    Some(existing)
                        if type_hint_can_replace_weak_existing(
                            assumption,
                            existing,
                            Some(&slot.name),
                            ptr_bits,
                        ) =>
                    {
                        slot.ty = Some(hint.clone());
                        true
                    }
                    Some(existing) if !type_hint_conflicts(existing, &hint, ptr_bits) => true,
                    Some(existing) => {
                        usage.mark_conflict(
                            assumption,
                            format!(
                                "stack slot {}@{} already has incompatible type {}",
                                match &key.base {
                                    ExternalStackBase::FramePointer => "bp",
                                    ExternalStackBase::StackPointer => "sp",
                                    ExternalStackBase::Named(name) => name.as_str(),
                                },
                                key.offset,
                                render_signature_type(existing, ptr_bits)
                            ),
                        );
                        continue;
                    }
                };

                if let Some(index) = slot.param_index {
                    match apply_type_hint_to_signature_param(
                        &mut parsed_context.merged_signature,
                        inferred_signature,
                        index,
                        assumption,
                        &hint,
                        ptr_bits,
                    ) {
                        Ok(result) => applied |= result,
                        Err(reason) => {
                            usage.mark_conflict(assumption, reason);
                            continue;
                        }
                    }
                }
                if applied {
                    usage.mark_applied(assumption);
                } else {
                    usage.mark_ignored(assumption);
                }
            }
            _ => {}
        }
    }
    usage
}

fn build_type_writeback_analysis_inner(
    mut input: TypeWritebackAnalysisInput<'_>,
    semantic_inputs: Option<TypeWritebackSemanticInputs<'_>>,
) -> TypeWritebackAnalysis {
    if input.parsed_context.stack_slots.is_empty()
        && !input.parsed_context.external_stack_vars.is_empty()
    {
        input.parsed_context.stack_slots =
            stack_slots_from_legacy_external_stack_vars(&input.parsed_context.external_stack_vars);
    }
    let summary_view = InterprocSummaryView::new(input.interproc_summary_set.clone());

    let semantic_projection = SemanticTypeProjection::from_inputs(
        &summary_view,
        semantic_inputs.as_ref().map(|semantic| semantic.artifact),
        input.ptr_bits,
    );
    let had_external_signature = input.parsed_context.current_signature.is_some()
        || input.parsed_context.merged_signature.is_some();

    let type_assumption_usage = apply_type_hint_assumptions_to_context(
        &mut input.parsed_context,
        &mut input.inferred_signature,
        input.ptr_bits,
        Some(&semantic_projection),
    );
    let mut signature_certificate_sources = Vec::new();
    if had_external_signature {
        push_signature_certificate_source(
            &mut signature_certificate_sources,
            SignatureCertificateSource::ExternalContext,
        );
    }
    if !type_assumption_usage.applied.is_empty() {
        push_signature_certificate_source(
            &mut signature_certificate_sources,
            SignatureCertificateSource::TypeAssumption,
        );
    }
    let inferred_signature_spec =
        inferred_signature_to_spec(&input.inferred_signature, input.ptr_bits);
    if inferred_signature_spec.is_some() && !had_external_signature {
        push_signature_certificate_source(
            &mut signature_certificate_sources,
            SignatureCertificateSource::LocalInference,
        );
    }

    let mut merged_signature = merge_local_signature_into_merged_signature(
        input.parsed_context.merged_signature.clone(),
        inferred_signature_spec,
    );
    canonicalize_param_home_stack_slots(
        merged_signature.as_ref(),
        &input.parsed_context.register_params,
        &mut input.parsed_context.stack_slots,
        input.ssa_blocks,
        input.ptr_bits,
    );
    hide_unproven_stack_pointer_frame_slots(&mut input.parsed_context.stack_slots);
    apply_main_signature_override(input.function_name, &mut merged_signature);
    let before_recovered_signature = merged_signature.clone();
    merged_signature = merge_recovered_arg_types_into_signature(
        merged_signature,
        input.recovered_vars,
        input.ptr_bits,
        input.function_name,
    );
    if merged_signature != before_recovered_signature {
        push_signature_certificate_source(
            &mut signature_certificate_sources,
            SignatureCertificateSource::RecoveredVariable,
        );
    }
    let current_param_count = merged_signature
        .as_ref()
        .map(|signature| signature.params.len())
        .unwrap_or(input.inferred_signature.params.len());
    let role_projection = semantic_inputs.as_ref().and_then(|semantic| {
        signature_projection_for_semantic_artifact(semantic.artifact, current_param_count)
    });
    let role_hint_has_authoritative_empty_params =
        role_projection.as_ref().is_some_and(|projection| {
            projection.exact_arity
                && projection.has_strong_signature_confidence()
                && projection.signature.params.is_empty()
        });
    if let Some(projection) = role_projection {
        let projection_source = SignatureCertificateSource::from(projection.source);
        let projection_result = apply_signature_projection_to_merged(
            &mut merged_signature,
            input.function_name,
            projection.clone(),
            input.ptr_bits,
        );
        if projection_result.was_applied() && signature_projection_can_certify(&projection) {
            push_signature_certificate_source(
                &mut signature_certificate_sources,
                projection_source,
            );
        }
        apply_signature_projection_to_inferred(
            &mut input.inferred_signature,
            projection,
            input.ptr_bits,
        );
    }
    let before_interproc_signature = merged_signature.clone();
    apply_interproc_summary_to_signature(
        &mut merged_signature,
        &mut input.inferred_signature,
        &summary_view,
        Some(&semantic_projection),
        input.ptr_bits,
    );
    if merged_signature != before_interproc_signature {
        push_signature_certificate_source(
            &mut signature_certificate_sources,
            SignatureCertificateSource::InterprocSummary,
        );
    }

    let mut diagnostics = input.diagnostics;
    diagnostics.solver_warnings = input.parsed_context.diagnostics.clone();
    diagnostics
        .warnings
        .extend(semantic_projection.refusal_warnings());
    if summary_view
        .diagnostics()
        .is_some_and(|diagnostics| !diagnostics.converged)
    {
        diagnostics.warnings.push(
            "interprocedural summary did not converge; downgraded summary-driven type hints"
                .to_string(),
        );
    }

    let external_structs = collect_external_struct_candidates_from_db(
        &input.parsed_context.external_type_db,
        input.ptr_bits,
    );
    let mut local_structs = input.local_structs;
    augment_local_struct_artifacts_with_projection(
        &mut local_structs,
        &semantic_projection,
        input.ptr_bits,
    );
    if let Some(semantic) = semantic_inputs.as_ref() {
        augment_local_struct_artifacts_with_local_field_accesses(
            &mut local_structs,
            semantic.local_field_accesses,
            input.ptr_bits,
        );
    }
    align_local_structs_with_external(
        &mut local_structs.struct_decls,
        &mut local_structs.slot_type_overrides,
        &local_structs.slot_field_profiles,
        &external_structs,
        input.ptr_bits,
    );
    prefer_stronger_local_struct_overrides(
        &local_structs.struct_decls,
        &mut local_structs.slot_type_overrides,
        &local_structs.slot_field_profiles,
        input.ptr_bits,
    );
    materialize_unresolved_signature_struct_layouts(
        merged_signature.as_ref(),
        &mut local_structs.struct_decls,
        &mut local_structs.slot_type_overrides,
        &input.parsed_context.external_type_db,
        input.ptr_bits,
    );
    let array_index_field_profiles = local_structs.slot_field_profiles.clone();
    prune_conflicting_local_struct_overrides(
        &merged_signature,
        &mut local_structs.struct_decls,
        &mut local_structs.slot_type_overrides,
        &mut local_structs.slot_field_profiles,
        &input.parsed_context.external_type_db,
        input.ptr_bits,
    );

    let struct_decls = dedup_struct_decls(
        external_structs
            .into_iter()
            .chain(local_structs.struct_decls.clone())
            .collect(),
    );

    let mut type_db = input.parsed_context.external_type_db.clone();
    merge_local_structs_into_type_db(&mut type_db, &struct_decls);
    let before_slot_signature = merged_signature.clone();
    let merged_signature = merge_slot_type_overrides_into_signature(
        merged_signature,
        &local_structs.slot_type_overrides,
        &type_db,
        input.ptr_bits,
        role_hint_has_authoritative_empty_params,
    );
    if merged_signature != before_slot_signature {
        push_signature_certificate_source(
            &mut signature_certificate_sources,
            SignatureCertificateSource::SlotTypeOverride,
        );
    }
    let mut array_index_certificates = array_index_certificates_from_struct_artifacts(
        &local_structs,
        &array_index_field_profiles,
        merged_signature.as_ref(),
        &type_db,
        input.ptr_bits,
    );
    let scalar_array_access_certificates = scalar_array_access_certificates_from_ssa(
        input.ssa_blocks,
        &input.parsed_context,
        merged_signature.as_ref(),
        if input.inferred_signature.arch.is_empty() {
            input.parsed_context.callconv.as_deref()
        } else {
            Some(input.inferred_signature.arch.as_str())
        },
        input.ptr_bits,
    );
    array_index_certificates.extend(scalar_array_access_certificates.array_index);
    let mut field_access_certificates =
        field_access_certificates_from_struct_artifacts(&local_structs);
    field_access_certificates.extend(scalar_array_access_certificates.field_access);
    if let Some(semantic) = semantic_inputs.as_ref() {
        field_access_certificates.extend(summary_field_access_certificates_from_semantics(
            semantic.artifact,
            merged_signature.as_ref(),
            &type_db,
            input.ptr_bits,
        ));
    }
    field_access_certificates.sort();
    field_access_certificates.dedup();
    let signature_certificate = signature_certificate_from_merged(
        merged_signature.as_ref(),
        &signature_certificate_sources,
    );
    let out_param_certificates = out_param_certificates_from_projection(
        &semantic_projection,
        merged_signature.as_ref(),
        input.ptr_bits,
    );
    let current_context_maps = signature_context_maps(merged_signature.as_ref(), input.ptr_bits);
    apply_signature_context_overrides(
        &mut input.inferred_signature,
        merged_signature.as_ref(),
        input.ptr_bits,
    );
    let existing_types =
        parse_existing_var_types_from_specs(&input.parsed_context.stack_slots, input.ptr_bits);
    let is_main_signature = merged_signature
        .as_ref()
        .is_some_and(is_canonical_main_signature_spec);
    let var_type_ctx = VarTypeCandidateContext {
        current_context_maps: &current_context_maps,
        merged_signature: merged_signature.as_ref(),
        slot_type_overrides: &local_structs.slot_type_overrides,
        stack_slots: &input.parsed_context.stack_slots,
        existing_types: &existing_types,
        ptr_bits: input.ptr_bits,
        is_main_signature,
    };
    let var_type_candidates =
        build_var_type_candidates(input.recovered_vars, &var_type_ctx, &mut diagnostics);
    let var_rename_candidates = build_var_rename_candidates(
        input.recovered_vars,
        &current_context_maps.param_names,
        &input.parsed_context.stack_slots,
    );
    let visible_bindings = build_visible_bindings(
        merged_signature.as_ref(),
        &input.parsed_context.register_params,
        &input.parsed_context.stack_slots,
        input.recovered_vars,
        &var_type_candidates,
        &var_rename_candidates,
        input.ptr_bits,
    );
    let mut type_facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
        merged_signature: merged_signature.clone(),
        callconv: input.parsed_context.callconv.clone(),
        noreturn: input.parsed_context.noreturn,
        known_function_signatures: input.parsed_context.known_function_signatures.clone(),
        register_params: input.parsed_context.register_params.clone(),
        stack_slots: input.parsed_context.stack_slots.clone(),
        visible_bindings,
        callee_facts: merged_context_and_summary_callee_facts(
            &input.parsed_context.callee_facts,
            input.interproc_summary_set.as_ref(),
        ),
        external_stack_vars: if input.parsed_context.stack_slots.is_empty() {
            input.parsed_context.external_stack_vars.clone()
        } else {
            HashMap::new()
        },
        external_type_db: type_db,
        slot_type_overrides: local_structs.slot_type_overrides.clone(),
        slot_field_profiles: local_structs.slot_field_profiles.clone(),
        local_field_accesses: semantic_inputs
            .as_ref()
            .map(|semantic| semantic.local_field_accesses.to_vec())
            .unwrap_or_default(),
        field_access_certificates,
        array_index_certificates,
        out_param_certificates,
        signature_certificate,
        interproc_diagnostics: input
            .interproc_summary_set
            .as_ref()
            .map(|summary_set| InterprocFactDiagnostics {
                iterations: summary_set.diagnostics.iterations,
                max_iterations: summary_set.diagnostics.max_iterations,
                converged: summary_set.diagnostics.converged,
                scope_size: summary_set.diagnostics.scope_size,
                scc_count: summary_set.diagnostics.scc_count,
                max_scc_size: summary_set.diagnostics.max_scc_size,
            })
            .unwrap_or_default(),
        diagnostics: diagnostics.solver_warnings.clone(),
    })
    .build();
    if let Some(semantic) = semantic_inputs.as_ref()
        && semantic.artifact.diagnostics.branches_pruned > 0
    {
        type_facts.diagnostics.push(format!(
            "symbolic pruned {} branch arm(s)",
            semantic.artifact.diagnostics.branches_pruned
        ));
    }
    let global_type_links = score_global_type_links(
        input.ssa_blocks,
        &struct_decls,
        &var_type_candidates,
        input.ptr_bits,
    );

    let plan = TypeWritebackPlan {
        signature: input.inferred_signature.clone(),
        var_type_candidates,
        var_rename_candidates,
        struct_decls: struct_decls.clone(),
        global_type_links,
        diagnostics: diagnostics.clone(),
    };

    TypeWritebackAnalysis {
        signature: input.inferred_signature,
        function_facts: FunctionFacts::new(
            type_facts.clone(),
            semantic_inputs
                .as_ref()
                .map(|semantic| semantic.artifact.clone()),
        )
        .with_assumptions(input.parsed_context.assumptions.clone())
        .with_summary_view(summary_view)
        .with_diagnostics(type_facts.diagnostics.clone())
        .with_assumption_usage(type_assumption_usage),
        type_facts,
        plan,
    }
}

pub fn build_type_writeback_analysis(
    input: TypeWritebackAnalysisInput<'_>,
) -> TypeWritebackAnalysis {
    build_type_writeback_analysis_inner(input, None)
}

pub fn build_type_writeback_analysis_with_semantics(
    input: TypeWritebackAnalysisInput<'_>,
    semantic_inputs: TypeWritebackSemanticInputs<'_>,
) -> TypeWritebackAnalysis {
    build_type_writeback_analysis_inner(input, Some(semantic_inputs))
}

pub fn augment_function_type_facts_with_summary_evidence(
    type_facts: &mut FunctionTypeFacts,
    semantic_artifact: &r2sym::SemanticArtifact,
    ptr_bits: u32,
) {
    let projection = SemanticTypeProjection::from_inputs(
        &InterprocSummaryView::default(),
        Some(semantic_artifact),
        ptr_bits,
    );
    type_facts
        .out_param_certificates
        .extend(out_param_certificates_from_projection(
            &projection,
            type_facts.merged_signature.as_ref(),
            ptr_bits,
        ));
    type_facts.out_param_certificates.sort();
    type_facts.out_param_certificates.dedup();
    type_facts
        .field_access_certificates
        .extend(summary_field_access_certificates_from_semantics(
            semantic_artifact,
            type_facts.merged_signature.as_ref(),
            &type_facts.external_type_db,
            ptr_bits,
        ));
    type_facts.field_access_certificates.sort();
    type_facts.field_access_certificates.dedup();
}

fn collect_semantic_slot_profiles(
    artifact: Option<&r2sym::SemanticArtifact>,
    ptr_bits: u32,
) -> BTreeMap<usize, BTreeMap<u64, String>> {
    fn reliable_post_memory_terms(
        region: &r2sym::SemanticRegion,
    ) -> impl Iterator<Item = &r2sym::BackwardMemoryCondition> {
        region
            .post
            .iter()
            .filter(|predicate| predicate.evidence.is_reliable())
            .filter_map(|predicate| predicate.value.compiled.as_ref())
            .filter(|compiled| compiled.evidence().is_reliable())
            .flat_map(|compiled| compiled.memory_terms.iter())
    }

    fn has_reliable_preconditions(region: &r2sym::SemanticRegion) -> bool {
        region
            .pre
            .iter()
            .any(|predicate| predicate.evidence.is_reliable())
    }

    fn has_decisive_target_support(region: &r2sym::SemanticRegion) -> bool {
        region.actionable_reachable_target().is_some() || {
            let actionable_targets = region
                .targets
                .iter()
                .filter(|fact| fact.evidence.allows_narrowing())
                .filter(|fact| {
                    matches!(
                        fact.value.status,
                        r2sym::SymbolicReachabilityStatus::Reachable
                    )
                })
                .map(|fact| fact.value.target)
                .collect::<BTreeSet<_>>();
            actionable_targets.len() == 1
        }
    }

    fn supports_conservative_type_projection(region: &r2sym::SemanticRegion) -> bool {
        let decisive_target = has_decisive_target_support(region);
        let has_post_support = region.post.iter().any(|predicate| {
            predicate.evidence.allows_narrowing()
                && predicate
                    .value
                    .compiled
                    .as_ref()
                    .is_some_and(|compiled| compiled.evidence().is_reliable())
        });
        if !decisive_target && !has_post_support {
            return false;
        }
        if has_reliable_preconditions(region) && !decisive_target {
            return false;
        }
        true
    }

    let Some(artifact) = artifact else {
        return BTreeMap::new();
    };
    if artifact.vm_summary_only_type_plan() {
        return BTreeMap::new();
    }
    let Some(native) = artifact.native_body() else {
        return BTreeMap::new();
    };

    let mut projected_profiles = BTreeMap::<usize, BTreeMap<u64, String>>::new();
    for region in native.regions.values() {
        if !supports_conservative_type_projection(region) {
            continue;
        }
        for term in region
            .memory
            .iter()
            .filter(|memory| memory.evidence.is_reliable())
            .map(|memory| &memory.value.term)
        {
            let Some((slot, offset, field_type)) = backward_memory_term_slot_field(term, ptr_bits)
            else {
                continue;
            };
            projected_profiles
                .entry(slot)
                .or_default()
                .entry(offset)
                .or_insert(field_type);
        }
        for term in reliable_post_memory_terms(region) {
            let Some((slot, offset, field_type)) = backward_memory_term_slot_field(term, ptr_bits)
            else {
                continue;
            };
            projected_profiles
                .entry(slot)
                .or_default()
                .entry(offset)
                .or_insert(field_type);
        }
    }

    if projected_profiles.is_empty() {
        for region in native.regions.values() {
            if !supports_conservative_type_projection(region) {
                continue;
            }
            let Some(target) = region.actionable_reachable_target() else {
                continue;
            };
            for compiled in region
                .control
                .iter()
                .filter(|fact| fact.evidence.allows_narrowing())
                .filter(|fact| fact.value.target == target)
                .filter_map(|fact| fact.value.compiled.as_ref())
            {
                if !compiled.evidence().is_reliable() {
                    continue;
                }
                for term in &compiled.memory_terms {
                    let Some((slot, offset, field_type)) =
                        backward_memory_term_slot_field(term, ptr_bits)
                    else {
                        continue;
                    };
                    projected_profiles
                        .entry(slot)
                        .or_default()
                        .entry(offset)
                        .or_insert(field_type);
                }
            }
        }
    }

    projected_profiles
}

fn summary_field_access_certificates_from_semantics(
    artifact: &r2sym::SemanticArtifact,
    merged_signature: Option<&FunctionSignatureSpec>,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
) -> Vec<crate::FieldAccessCertificate> {
    let Some(native) = artifact.native_body() else {
        return Vec::new();
    };
    let certified_summary_roles = summary_role_keys(&artifact.semantic_claim_summary());
    let mut certificates = Vec::new();

    for summary in &native.summary.worker_summaries {
        if !semantic_evidence_allows_type_projection(&summary.evidence) {
            continue;
        }
        let has_role_certificate =
            worker_summary_has_role_certificate(summary, &certified_summary_roles);
        if summary.kind == r2sym::NativeWorkerSummaryKind::MemoryWrite {
            push_summary_location_field_access_certificates(
                &mut certificates,
                summary.memory.as_ref(),
                merged_signature,
                type_db,
                ptr_bits,
                None,
            );
        } else if !has_role_certificate {
            continue;
        }
    }

    for summary in &native.summary.region_summaries {
        if !semantic_evidence_allows_type_projection(&summary.evidence) {
            continue;
        }
        let has_role_certificate =
            region_summary_has_role_certificate(summary, &certified_summary_roles);
        for access in &summary.memory_accesses {
            if access.kind != r2sym::NativeMemoryAccessKind::Write {
                continue;
            }
            if !has_role_certificate && access.location.as_ref().and_then(|loc| loc.range).is_none()
            {
                continue;
            }
            push_summary_location_field_access_certificates(
                &mut certificates,
                access.location.as_ref(),
                merged_signature,
                type_db,
                ptr_bits,
                access.width,
            );
        }
    }

    certificates.sort();
    certificates.dedup();
    certificates
}

fn push_summary_location_field_access_certificates(
    certificates: &mut Vec<crate::FieldAccessCertificate>,
    location: Option<&r2ssa::SummaryMemoryLocation>,
    merged_signature: Option<&FunctionSignatureSpec>,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
    access_width: Option<u32>,
) {
    let Some(location) = location else {
        return;
    };
    let r2ssa::SummaryMemoryRegion::Arg { index: slot } = location.region else {
        return;
    };
    let Some(range) = location.range else {
        return;
    };
    if range.offset_lo < 0 || range.offset_lo != range.offset_hi {
        return;
    }
    let offset = range.offset_lo as u64;
    let width = access_width.or(range.width).unwrap_or(1).max(1) as u64;
    let Some(param_ty) = merged_signature
        .and_then(|signature| signature.params.get(slot))
        .and_then(|param| param.ty.as_ref())
    else {
        return;
    };

    for type_name in aggregate_pointee_type_names_from_type(param_ty) {
        if let Some(field) =
            external_layout_field_access_for_offset(type_db, &type_name, offset, width, ptr_bits)
        {
            certificates.push(crate::FieldAccessCertificate {
                slot,
                field_offset: offset,
                field_name: field.name,
                field_type: field.ty,
            });
            return;
        }
    }
}

fn semantic_stage_label(artifact: &r2sym::SemanticArtifact) -> &'static str {
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

fn semantic_fallback_warning(artifact: &r2sym::SemanticArtifact) -> String {
    let slice_class = artifact
        .slice_class()
        .map(semantic_slice_class_label)
        .unwrap_or("unknown");
    let mode = semantic_stage_label(artifact);
    let mut warning = format!("semantic fallback: {slice_class} slice in {mode} mode");
    if !artifact.diagnostics.residual_reasons.is_empty() {
        warning.push_str(" (");
        warning.push_str(
            &artifact
                .diagnostics
                .residual_reasons
                .iter()
                .map(|reason| semantic_residual_reason_label(*reason))
                .collect::<Vec<_>>()
                .join(", "),
        );
        warning.push(')');
    }
    if let Some(native) = artifact.native_body()
        && !native.regions.is_empty()
    {
        warning.push_str(&format!(
            "; regions={}, actionable_conditions={}, exact_conditions={}",
            native.regions.len(),
            native.actionable_control_count(),
            native.exact_control_count(),
        ));
    }
    warning
}

pub fn semantic_artifact_prefers_bounded_type_plan(artifact: &r2sym::SemanticArtifact) -> bool {
    if !artifact.type_plan().allows_native_augmentation() {
        return true;
    }
    let native = artifact.native_body();
    let has_native_regions = native.is_some_and(|body| !body.regions.is_empty());
    let has_summary_islands =
        native.is_some_and(r2sym::NativeArtifactBody::has_primary_non_name_summary_islands);

    matches!(
        artifact.stage,
        r2sym::RefinementStage::Residual | r2sym::RefinementStage::Compiled
    ) && artifact.diagnostics.skipped_large_cfg
        && matches!(
            artifact.slice_class(),
            Some(r2sym::SliceClass::Worker | r2sym::SliceClass::GenericLarge)
        )
        && (has_native_regions || has_summary_islands)
        && (artifact.actionable_control_count() > 0
            || has_summary_islands
            || artifact
                .actionable_regions()
                .into_iter()
                .any(|region| !region.actionable_memory_terms().is_empty()))
}

pub fn build_semantic_type_fallback_plan(
    function_name: &str,
    arch_name: &str,
    ptr_bits: u32,
    artifact: &r2sym::SemanticArtifact,
) -> TypeWritebackPlan {
    let mut warnings = vec![semantic_fallback_warning(artifact)];
    if !artifact.type_plan().allows_native_augmentation() {
        warnings.push("type analysis not ready from semantic capability".to_string());
    }
    let mut local_structs = LocalStructArtifacts::default();
    augment_local_struct_artifacts_with_semantics(&mut local_structs, artifact, ptr_bits);
    let mut signature = InferredSignature {
        function_name: function_name.to_string(),
        signature: format!("void {}(void)", function_name),
        ret_type: "void".to_string(),
        params: Vec::new(),
        callconv: "unknown".to_string(),
        arch: arch_name.to_string(),
        confidence: 0,
        callconv_confidence: 0,
    };
    let empty_summary_view = InterprocSummaryView::new(None);
    apply_semantic_artifact_signature_hint_to_inferred(&mut signature, artifact, ptr_bits);
    let semantic_projection =
        SemanticTypeProjection::from_inputs(&empty_summary_view, Some(artifact), ptr_bits);
    warnings.extend(semantic_projection.refusal_warnings());
    apply_semantic_projection_to_fallback_signature(&mut signature, &semantic_projection, ptr_bits);
    if let Some(merged_signature) = merge_slot_type_overrides_into_signature(
        inferred_signature_to_spec(&signature, ptr_bits),
        &local_structs.slot_type_overrides,
        &ExternalTypeDb::default(),
        ptr_bits,
        false,
    ) {
        apply_signature_context_overrides(&mut signature, Some(&merged_signature), ptr_bits);
    }
    if !local_structs.struct_decls.is_empty() {
        warnings.push(format!(
            "semantic regions projected {} struct candidate(s)",
            local_structs.struct_decls.len()
        ));
    }

    TypeWritebackPlan {
        signature,
        var_type_candidates: Vec::new(),
        var_rename_candidates: Vec::new(),
        struct_decls: local_structs.struct_decls,
        global_type_links: Vec::new(),
        diagnostics: TypeWritebackDiagnostics {
            conflicts: Vec::new(),
            warnings,
            solver_warnings: Vec::new(),
        },
    }
}

fn apply_semantic_projection_to_fallback_signature(
    signature: &mut InferredSignature,
    projection: &SemanticTypeProjection,
    ptr_bits: u32,
) -> bool {
    let mut changed = false;
    if let Some(ret_ty) = projection.return_type_hint.as_ref() {
        let existing_ty = parse_type_like_spec(&signature.ret_type, ptr_bits);
        let should_replace = is_generic_type_string(&signature.ret_type)
            || existing_ty.as_ref().is_some_and(|existing| {
                summary_hint_can_replace_weak_existing(existing, ret_ty, ptr_bits)
                    || matches!(ret_ty, CTypeLike::Void)
                        && crate::signature_return_hint_can_replace_existing(
                            existing,
                            Some(ret_ty),
                            ptr_bits,
                        )
            });
        if should_replace {
            let rendered = render_signature_type(ret_ty, ptr_bits);
            if signature.ret_type != rendered {
                signature.ret_type = rendered;
                changed = true;
            }
        }
    }

    let max_index = projection
        .param_type_hints
        .keys()
        .chain(projection.param_name_hints.keys())
        .chain(projection.pointer_param_indices.iter())
        .chain(projection.out_param_indices.iter())
        .copied()
        .max();
    let Some(max_index) = max_index else {
        if changed {
            signature.signature = format_signature(
                &signature.function_name,
                &signature.ret_type,
                &signature.params,
            );
            signature.confidence = signature.confidence.max(55);
        }
        return changed;
    };

    while signature.params.len() <= max_index {
        let idx = signature.params.len();
        let ty = projection
            .param_type_hints
            .get(&idx)
            .cloned()
            .or_else(|| {
                (projection.pointer_param_indices.contains(&idx)
                    || projection.out_param_indices.contains(&idx))
                .then(void_pointer_type)
            })
            .unwrap_or_else(|| typedef_type("uintptr_t"));
        signature.params.push(InferredSignatureParam {
            name: projection
                .param_name_hints
                .get(&idx)
                .cloned()
                .unwrap_or_else(|| format!("arg{idx}")),
            param_type: render_signature_type(&ty, ptr_bits),
        });
        changed = true;
    }

    for idx in 0..=max_index {
        if let Some(param) = signature.params.get_mut(idx) {
            if let Some(name) = projection.param_name_hints.get(&idx)
                && (param.name.is_empty() || is_generic_arg_name(&param.name))
            {
                param.name = name.clone();
                changed = true;
            }
            if inferred_param_has_authoritative_named_scalar_role(param, ptr_bits) {
                continue;
            }
            if let Some(ty) = projection.param_type_hints.get(&idx) {
                let existing_ty = parse_type_like_spec(&param.param_type, ptr_bits);
                if is_generic_type_string(&param.param_type)
                    || existing_ty.as_ref().is_some_and(|existing| {
                        summary_hint_can_replace_weak_existing(existing, ty, ptr_bits)
                    })
                {
                    let rendered = render_signature_type(ty, ptr_bits);
                    if param.param_type != rendered {
                        param.param_type = rendered;
                        changed = true;
                    }
                }
            }
        }
    }

    signature.signature = format_signature(
        &signature.function_name,
        &signature.ret_type,
        &signature.params,
    );
    if changed {
        signature.confidence = signature.confidence.max(55);
    }
    changed
}

pub fn apply_semantic_artifact_signature_hint_to_inferred(
    signature: &mut InferredSignature,
    artifact: &r2sym::SemanticArtifact,
    ptr_bits: u32,
) -> bool {
    let Some(projection) =
        signature_projection_for_semantic_artifact(artifact, signature.params.len())
    else {
        return false;
    };
    let result = apply_signature_projection_to_inferred(signature, projection, ptr_bits);
    if !result.was_applied() {
        return false;
    }
    signature.signature = format_signature(
        &signature.function_name,
        &signature.ret_type,
        &signature.params,
    );
    true
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LocalAddrExpr {
    slot: usize,
    offset: i64,
    confidence: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScalarPointerValue {
    slot: usize,
    base: ArrayIndexBase,
    element_stride: u64,
    confidence: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScalarArrayAddrExpr {
    pointer: ScalarPointerValue,
    field_offset: u64,
    confidence: u8,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ScalarArrayAccessCertificates {
    array_index: Vec<ArrayIndexCertificate>,
    field_access: Vec<crate::FieldAccessCertificate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExternalLayoutFieldAccess {
    name: String,
    ty: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AffineIndexFactor {
    root: Option<String>,
    scale: i128,
}

struct ScalarArrayInferenceCtx<'a> {
    parsed_context: &'a ParsedExternalContext,
    merged_signature: Option<&'a FunctionSignatureSpec>,
    ptr_bits: u32,
    pointer_arg_slot_map: &'a HashMap<String, usize>,
    pointer_values: &'a HashMap<String, ScalarPointerValue>,
    pointer_value_names: &'a HashMap<String, Option<ScalarPointerValue>>,
    array_addr_exprs: &'a HashMap<String, ScalarArrayAddrExpr>,
    array_addr_expr_names: &'a HashMap<String, Option<ScalarArrayAddrExpr>>,
    stack_addr_offsets: &'a HashMap<String, i64>,
    stack_addr_offset_names: &'a HashMap<String, Option<i64>>,
    block_ops: &'a HashMap<u64, HashMap<String, SSAOp>>,
    value_ops: &'a HashMap<String, SSAOp>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct InferredLocalFieldEvidence {
    reads: u32,
    writes: u32,
    widths: BTreeMap<u32, u32>,
    type_votes: BTreeMap<String, u32>,
}

type LocalFieldEvidenceMap = HashMap<usize, BTreeMap<u64, InferredLocalFieldEvidence>>;

fn collect_pointer_arg_slot_map(arch_name: Option<&str>, ptr_bits: u32) -> HashMap<String, usize> {
    let (arg_regs, _, _) = recover_vars_arch_profile(arch_name);
    let arch_name = arch_name.unwrap_or_default().to_ascii_lowercase();
    let is_arm64 = arch_name.contains("aarch64") || arch_name.contains("arm64");
    let is_x86_64 = arch_name.contains("x86-64")
        || arch_name.contains("x86_64")
        || arch_name.contains("amd64")
        || arch_name.contains("x64");
    let is_riscv64 = arch_name.contains("riscv64") || arch_name.contains("rv64");

    let mut out = HashMap::new();
    for (idx, (canonical, aliases)) in arg_regs.iter().enumerate() {
        let include_alias = |alias: &str| -> bool {
            if ptr_bits <= 32 {
                return true;
            }
            let alias = alias.to_ascii_lowercase();
            if is_arm64 {
                return alias.starts_with('x');
            }
            if is_x86_64 {
                return alias.starts_with('r');
            }
            if is_riscv64 {
                return alias.starts_with('x') || alias.starts_with('a');
            }
            alias == (*canonical).to_ascii_lowercase()
        };

        if include_alias(canonical) {
            out.insert((*canonical).to_string(), idx);
        }
        for alias in *aliases {
            if include_alias(alias) {
                out.insert((*alias).to_string(), idx);
            }
        }
    }
    out
}

fn parse_ssa_const_offset(name: &str, ptr_bits: u32) -> Option<i64> {
    let val_str = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("CONST:"))?;
    let val_str = val_str.split('_').next().unwrap_or(val_str);

    let raw = if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        u64::from_str_radix(hex, 16).ok()?
    } else if let Some(dec) = val_str
        .strip_prefix("0d")
        .or_else(|| val_str.strip_prefix("0D"))
    {
        dec.parse::<u64>().ok()?
    } else {
        u64::from_str_radix(val_str, 16).ok()?
    };
    Some(signed_offset_from_const(raw, ptr_bits))
}

pub fn infer_local_struct_artifacts_from_ssa(
    ssa_blocks: &[SSABlock],
    arch_name: Option<&str>,
    ptr_bits: u32,
    diagnostics: &mut TypeWritebackDiagnostics,
) -> LocalStructArtifacts {
    let pointer_arg_slot_map = collect_pointer_arg_slot_map(arch_name, ptr_bits);
    let (_, stack_bases, frame_bases) = recover_vars_arch_profile(arch_name);
    let mut addr_exprs: HashMap<String, LocalAddrExpr> = HashMap::new();
    let mut stack_addr_offsets: HashMap<String, i64> = HashMap::new();
    let mut stack_slot_values: HashMap<(u64, i64), LocalAddrExpr> = HashMap::new();
    let mut slot_field_evidence: LocalFieldEvidenceMap = HashMap::new();
    let offset_bound = 0x4000i64;
    let block_ops: HashMap<u64, HashMap<String, SSAOp>> = ssa_blocks
        .iter()
        .map(|block| {
            let ops = block
                .ops
                .iter()
                .filter_map(|op| {
                    op.dst()
                        .map(|dst| (ssa_var_block_key(block.addr, dst), op.clone()))
                })
                .collect::<HashMap<_, _>>();
            (block.addr, ops)
        })
        .collect();
    fn is_scaled_index_like(
        block_addr: u64,
        var: &SSAVar,
        ops_by_block: &HashMap<u64, HashMap<String, SSAOp>>,
        addr_exprs: &HashMap<String, LocalAddrExpr>,
        depth: u32,
    ) -> bool {
        if depth > 8 || var.is_const() {
            return false;
        }
        let key = ssa_var_block_key(block_addr, var);
        if addr_exprs.contains_key(&key) {
            return false;
        }
        let Some(op) = ops_by_block.get(&block_addr).and_then(|ops| ops.get(&key)) else {
            return true;
        };
        match op {
            SSAOp::Copy { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::New { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Subpiece { src, .. } => {
                is_scaled_index_like(block_addr, src, ops_by_block, addr_exprs, depth + 1)
            }
            SSAOp::IntMult { a, b, .. } => {
                (parse_ssa_const_offset(&a.name, 64).is_some()
                    && is_scaled_index_like(block_addr, b, ops_by_block, addr_exprs, depth + 1))
                    || (parse_ssa_const_offset(&b.name, 64).is_some()
                        && is_scaled_index_like(block_addr, a, ops_by_block, addr_exprs, depth + 1))
            }
            SSAOp::IntLeft { a, b, .. } => {
                parse_ssa_const_offset(&b.name, 64).is_some()
                    && is_scaled_index_like(block_addr, a, ops_by_block, addr_exprs, depth + 1)
            }
            SSAOp::IntSub { a, b, .. } => {
                (parse_ssa_const_offset(&a.name, 64) == Some(0)
                    && is_scaled_index_like(block_addr, b, ops_by_block, addr_exprs, depth + 1))
                    || (is_scaled_index_like(block_addr, a, ops_by_block, addr_exprs, depth + 1)
                        && is_scaled_index_like(block_addr, b, ops_by_block, addr_exprs, depth + 1))
            }
            SSAOp::Load { .. } | SSAOp::Phi { .. } => true,
            _ => false,
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            op.for_each_source(&mut |src: &SSAVar| {
                if src.version != 0 {
                    return;
                }
                let key = src.name.to_ascii_lowercase();
                if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                    addr_exprs
                        .entry(ssa_var_block_key(block.addr, src))
                        .or_insert(LocalAddrExpr {
                            slot,
                            offset: 0,
                            confidence: 92,
                        });
                }
            });
        }
    }

    let is_stack_base = |name: &str| stack_bases.contains(&name) || frame_bases.contains(&name);

    for _ in 0..6 {
        let mut changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                let addr_of = |var: &SSAVar, map: &HashMap<String, LocalAddrExpr>| {
                    if var.version == 0 {
                        let key = var.name.to_ascii_lowercase();
                        if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                            return Some(LocalAddrExpr {
                                slot,
                                offset: 0,
                                confidence: 92,
                            });
                        }
                    }
                    map.get(&ssa_var_block_key(block.addr, var)).copied()
                };
                let stack_slot_of = |var: &SSAVar, stack_map: &HashMap<String, i64>| {
                    stack_map.get(&ssa_var_block_key(block.addr, var)).copied()
                };
                let set_expr =
                    |dst: &SSAVar,
                     expr: LocalAddrExpr,
                     map: &mut HashMap<String, LocalAddrExpr>| {
                        let key = ssa_var_block_key(block.addr, dst);
                        match map.get(&key).copied() {
                            Some(prev) if prev.confidence >= expr.confidence => false,
                            _ => {
                                map.insert(key, expr);
                                true
                            }
                        }
                    };
                let set_stack_slot = |dst: &SSAVar, offset: i64, map: &mut HashMap<String, i64>| {
                    let key = ssa_var_block_key(block.addr, dst);
                    match map.get(&key).copied() {
                        Some(prev) if prev == offset => false,
                        _ => {
                            map.insert(key, offset);
                            true
                        }
                    }
                };

                match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::New { dst, src }
                    | SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src } => {
                        if let Some(mut expr) = addr_of(src, &addr_exprs) {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                        if let Some(offset) = stack_slot_of(src, &stack_addr_offsets) {
                            changed |= set_stack_slot(dst, offset, &mut stack_addr_offsets);
                        }
                    }
                    SSAOp::Phi { dst, sources } => {
                        let mut selected = None;
                        let mut selected_slot = None;
                        for src in sources {
                            let Some(expr) = addr_of(src, &addr_exprs) else {
                                selected = None;
                                break;
                            };
                            selected = match selected {
                                None => Some(expr),
                                Some(prev)
                                    if prev.slot == expr.slot && prev.offset == expr.offset =>
                                {
                                    Some(LocalAddrExpr {
                                        slot: prev.slot,
                                        offset: prev.offset,
                                        confidence: prev.confidence.max(expr.confidence),
                                    })
                                }
                                _ => None,
                            };
                            let Some(slot) = stack_slot_of(src, &stack_addr_offsets) else {
                                selected_slot = None;
                                break;
                            };
                            selected_slot = match selected_slot {
                                None => Some(slot),
                                Some(prev) if prev == slot => Some(prev),
                                _ => None,
                            };
                            if selected.is_none() {
                                break;
                            }
                        }
                        if let Some(mut expr) = selected {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                        if let Some(slot) = selected_slot {
                            changed |= set_stack_slot(dst, slot, &mut stack_addr_offsets);
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } => {
                        if let Some(off) = parse_ssa_const_offset(&b.name, ptr_bits) {
                            let a_lower = a.name.to_ascii_lowercase();
                            if is_stack_base(a_lower.as_str()) {
                                changed |= set_stack_slot(dst, off, &mut stack_addr_offsets);
                            }
                        }
                        if let Some(off) = parse_ssa_const_offset(&a.name, ptr_bits) {
                            let b_lower = b.name.to_ascii_lowercase();
                            if is_stack_base(b_lower.as_str()) {
                                changed |= set_stack_slot(dst, off, &mut stack_addr_offsets);
                            }
                        }
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits)
                        {
                            let off = base.offset.saturating_add(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    LocalAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(a, &addr_exprs)
                            && is_scaled_index_like(block.addr, b, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                LocalAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&a.name, ptr_bits)
                        {
                            let off = base.offset.saturating_add(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    LocalAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && is_scaled_index_like(block.addr, a, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                LocalAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        }
                    }
                    SSAOp::IntSub { dst, a, b } => {
                        if let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits) {
                            let a_lower = a.name.to_ascii_lowercase();
                            if is_stack_base(a_lower.as_str()) {
                                changed |= set_stack_slot(
                                    dst,
                                    delta.saturating_neg(),
                                    &mut stack_addr_offsets,
                                );
                            }
                        }
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits)
                        {
                            let off = base.offset.saturating_sub(delta);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    LocalAddrExpr {
                                        slot: base.slot,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(a, &addr_exprs)
                            && is_scaled_index_like(block.addr, b, &block_ops, &addr_exprs, 0)
                        {
                            changed |= set_expr(
                                dst,
                                LocalAddrExpr {
                                    slot: base.slot,
                                    offset: base.offset,
                                    confidence: base.confidence.saturating_sub(4),
                                },
                                &mut addr_exprs,
                            );
                        }
                    }
                    SSAOp::Store { addr, val, .. } => {
                        if let Some(offset) = stack_slot_of(addr, &stack_addr_offsets)
                            && let Some(mut expr) = addr_of(val, &addr_exprs)
                        {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            let key = (block.addr, offset);
                            match stack_slot_values.get(&key).copied() {
                                Some(prev) if prev.confidence >= expr.confidence => {}
                                _ => {
                                    stack_slot_values.insert(key, expr);
                                    changed = true;
                                }
                            }
                        }
                    }
                    SSAOp::Load { dst, addr, .. } => {
                        if let Some(offset) = stack_slot_of(addr, &stack_addr_offsets)
                            && let Some(mut expr) =
                                stack_slot_values.get(&(block.addr, offset)).copied()
                        {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            let resolve_addr = |addr: &SSAVar| -> Option<LocalAddrExpr> {
                if addr.version == 0 {
                    let key = addr.name.to_ascii_lowercase();
                    if let Some(slot) = pointer_arg_slot_map.get(key.as_str()).copied() {
                        return Some(LocalAddrExpr {
                            slot,
                            offset: 0,
                            confidence: 92,
                        });
                    }
                }
                addr_exprs
                    .get(&ssa_var_block_key(block.addr, addr))
                    .copied()
            };
            match op {
                SSAOp::Load { dst, addr, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = slot_field_evidence
                            .entry(expr.slot)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.reads = entry.reads.saturating_add(1);
                        *entry.widths.entry(dst.size).or_insert(0) += 1;
                        *entry.type_votes.entry(size_to_type(dst.size)).or_insert(0) += 1;
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = slot_field_evidence
                            .entry(expr.slot)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.writes = entry.writes.saturating_add(1);
                        *entry.widths.entry(val.size).or_insert(0) += 1;
                        *entry.type_votes.entry(size_to_type(val.size)).or_insert(0) += 1;
                    }
                }
                _ => {}
            }
        }
    }

    let mut struct_decls = Vec::new();
    let mut slot_type_overrides = HashMap::new();
    let mut slot_field_profiles = HashMap::new();
    let mut slots: Vec<usize> = slot_field_evidence.keys().copied().collect();
    slots.sort_unstable();

    for slot in slots {
        let Some(fields_map) = slot_field_evidence.get(&slot) else {
            continue;
        };
        if fields_map.is_empty() {
            continue;
        }
        let mut shape = String::new();
        let mut fields = Vec::new();
        let mut normalized_fields = BTreeMap::new();
        let mut confidence_acc = 0u32;
        for (offset, evidence) in fields_map {
            let total_votes: u32 = evidence.type_votes.values().copied().sum();
            let Some((field_type, field_votes)) = evidence
                .type_votes
                .iter()
                .max_by_key(|(_, count)| **count)
                .map(|(ty, count)| (ty.clone(), *count))
            else {
                continue;
            };
            if evidence.type_votes.len() > 1 {
                diagnostics.conflicts.push(format!(
                    "slot {slot} field +0x{offset:x} conflicting type votes {:?}",
                    evidence.type_votes
                ));
            }
            let strength = ((field_votes.saturating_mul(100)) / total_votes.max(1)) as u8;
            let rw_bonus = if evidence.reads > 0 && evidence.writes > 0 {
                10
            } else {
                0
            };
            let field_conf = 70u8.saturating_add(strength / 3).saturating_add(rw_bonus);
            confidence_acc = confidence_acc.saturating_add(field_conf as u32);
            shape.push_str(&format!("{offset:x}:{field_type};"));
            normalized_fields.insert(*offset, field_type.clone());
            fields.push(StructFieldCandidate {
                name: format!("f_{offset:x}"),
                offset: *offset,
                field_type,
                confidence: field_conf,
            });
        }
        if fields.is_empty() {
            continue;
        }
        let avg_conf = (confidence_acc / fields.len() as u32).clamp(1, 100) as u8;
        let allow_single_field = fields.len() == 1 && avg_conf >= 94;
        if fields.len() < 2 && !allow_single_field {
            continue;
        }
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hasher);
        let struct_name = format!("sla_struct_{:016x}", hasher.finish());
        let Some(decl) = build_struct_decl(&struct_name, &fields, ptr_bits) else {
            continue;
        };
        struct_decls.push(StructDeclCandidate {
            name: struct_name.clone(),
            decl,
            confidence: avg_conf.max(84),
            source: StructDeclSource::LocalInferred,
            fields,
        });
        slot_field_profiles.insert(slot, normalized_fields);
        slot_type_overrides.insert(slot, format!("struct {struct_name} *"));
    }

    LocalStructArtifacts {
        struct_decls,
        slot_type_overrides,
        slot_field_profiles,
    }
}

pub fn local_field_accesses_from_struct_artifacts(
    local_structs: &LocalStructArtifacts,
) -> Vec<LocalFieldAccessFact> {
    let mut accesses = Vec::new();
    for (slot, fields) in &local_structs.slot_field_profiles {
        for (field_offset, field_type) in fields {
            accesses.push(LocalFieldAccessFact {
                slot: *slot,
                field_offset: *field_offset,
                field_name: format!("f_{field_offset:x}"),
                field_type: Some(field_type.clone()),
            });
        }
    }
    accesses.sort();
    accesses
}

pub fn field_access_certificates_from_struct_artifacts(
    local_structs: &LocalStructArtifacts,
) -> Vec<crate::FieldAccessCertificate> {
    local_field_accesses_from_struct_artifacts(local_structs)
        .into_iter()
        .map(|access| crate::FieldAccessCertificate {
            slot: access.slot,
            field_offset: access.field_offset,
            field_name: access.field_name,
            field_type: access.field_type,
        })
        .collect()
}

fn array_index_certificates_from_struct_artifacts(
    local_structs: &LocalStructArtifacts,
    slot_field_profiles: &HashMap<usize, BTreeMap<u64, String>>,
    merged_signature: Option<&FunctionSignatureSpec>,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
) -> Vec<ArrayIndexCertificate> {
    let mut certificates = Vec::new();

    let mut slots: Vec<_> = slot_field_profiles.keys().copied().collect();
    slots.sort_unstable();
    for slot in slots {
        let Some(fields) = slot_field_profiles.get(&slot) else {
            continue;
        };
        if fields.is_empty() {
            continue;
        }

        let stride =
            aggregate_stride_for_slot(slot, local_structs, merged_signature, type_db, ptr_bits)
                .or_else(|| profile_minimum_stride(fields, ptr_bits));
        let Some(element_stride) = stride.filter(|stride| *stride > 0) else {
            continue;
        };

        for field_offset in fields.keys() {
            certificates.push(ArrayIndexCertificate {
                slot,
                base: Some(ArrayIndexBase::Param { index: slot }),
                field_offset: *field_offset,
                element_stride,
            });
        }
    }

    certificates.sort();
    certificates.dedup();
    certificates
}

fn scalar_array_access_certificates_from_ssa(
    ssa_blocks: &[SSABlock],
    parsed_context: &ParsedExternalContext,
    merged_signature: Option<&FunctionSignatureSpec>,
    arch_name: Option<&str>,
    ptr_bits: u32,
) -> ScalarArrayAccessCertificates {
    let arch_name = arch_name.filter(|name| !name.is_empty());
    let pointer_arg_slot_map = collect_pointer_arg_slot_map(arch_name, ptr_bits);
    let (_, stack_bases, frame_bases) = recover_vars_arch_profile(arch_name);
    let mut stack_addr_offsets: HashMap<String, i64> = HashMap::new();
    let mut stack_addr_offset_names: HashMap<String, Option<i64>> = HashMap::new();
    let mut pointer_values: HashMap<String, ScalarPointerValue> = HashMap::new();
    let mut pointer_value_names: HashMap<String, Option<ScalarPointerValue>> = HashMap::new();
    let mut array_addr_exprs: HashMap<String, ScalarArrayAddrExpr> = HashMap::new();
    let mut array_addr_expr_names: HashMap<String, Option<ScalarArrayAddrExpr>> = HashMap::new();
    let mut certificates = ScalarArrayAccessCertificates::default();

    let block_ops: HashMap<u64, HashMap<String, SSAOp>> = ssa_blocks
        .iter()
        .map(|block| {
            let ops = block
                .ops
                .iter()
                .filter_map(|op| {
                    op.dst()
                        .map(|dst| (ssa_var_block_key(block.addr, dst), op.clone()))
                })
                .collect::<HashMap<_, _>>();
            (block.addr, ops)
        })
        .collect();
    let value_ops: HashMap<String, SSAOp> = ssa_blocks
        .iter()
        .flat_map(|block| {
            block
                .ops
                .iter()
                .filter_map(|op| op.dst().map(|dst| (dst.display_name(), op.clone())))
        })
        .collect();

    let is_stack_base = |name: &str| stack_bases.contains(&name) || frame_bases.contains(&name);

    for _ in 0..6 {
        let mut changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::New { dst, src }
                    | SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src }
                    | SSAOp::Trunc { dst, src }
                    | SSAOp::Subpiece { dst, src, .. } => {
                        let ctx = ScalarArrayInferenceCtx {
                            parsed_context,
                            merged_signature,
                            ptr_bits,
                            pointer_arg_slot_map: &pointer_arg_slot_map,
                            pointer_values: &pointer_values,
                            pointer_value_names: &pointer_value_names,
                            array_addr_exprs: &array_addr_exprs,
                            array_addr_expr_names: &array_addr_expr_names,
                            stack_addr_offsets: &stack_addr_offsets,
                            stack_addr_offset_names: &stack_addr_offset_names,
                            block_ops: &block_ops,
                            value_ops: &value_ops,
                        };
                        if let Some(mut pointer) =
                            scalar_pointer_value_for_var(block.addr, src, &ctx)
                        {
                            pointer.confidence = pointer.confidence.saturating_sub(2);
                            changed |= set_scalar_pointer_value(
                                block.addr,
                                dst,
                                pointer,
                                &mut pointer_values,
                                &mut pointer_value_names,
                            );
                        }
                        if let Some(mut expr) = scalar_array_addr_expr_for_var(
                            block.addr,
                            src,
                            &array_addr_exprs,
                            &array_addr_expr_names,
                        ) {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            changed |= set_scalar_array_addr_expr(
                                block.addr,
                                dst,
                                expr,
                                &mut array_addr_exprs,
                                &mut array_addr_expr_names,
                            );
                        }
                        if let Some(offset) = stack_addr_offset_for_var(
                            block.addr,
                            src,
                            &stack_addr_offsets,
                            &stack_addr_offset_names,
                        ) {
                            changed |= set_stack_addr_offset(
                                block.addr,
                                dst,
                                offset,
                                &mut stack_addr_offsets,
                                &mut stack_addr_offset_names,
                            );
                        }
                    }
                    SSAOp::Phi { dst, sources } => {
                        let ctx = ScalarArrayInferenceCtx {
                            parsed_context,
                            merged_signature,
                            ptr_bits,
                            pointer_arg_slot_map: &pointer_arg_slot_map,
                            pointer_values: &pointer_values,
                            pointer_value_names: &pointer_value_names,
                            array_addr_exprs: &array_addr_exprs,
                            array_addr_expr_names: &array_addr_expr_names,
                            stack_addr_offsets: &stack_addr_offsets,
                            stack_addr_offset_names: &stack_addr_offset_names,
                            block_ops: &block_ops,
                            value_ops: &value_ops,
                        };
                        if let Some(mut pointer) =
                            phi_scalar_pointer_value(block.addr, dst, sources, &ctx)
                        {
                            pointer.confidence = pointer.confidence.saturating_sub(3);
                            changed |= set_scalar_pointer_value(
                                block.addr,
                                dst,
                                pointer,
                                &mut pointer_values,
                                &mut pointer_value_names,
                            );
                        }
                        if let Some(mut expr) = phi_scalar_array_addr_expr(
                            block.addr,
                            sources,
                            &array_addr_exprs,
                            &array_addr_expr_names,
                        ) {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_scalar_array_addr_expr(
                                block.addr,
                                dst,
                                expr,
                                &mut array_addr_exprs,
                                &mut array_addr_expr_names,
                            );
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } => {
                        if let Some(off) = parse_ssa_const_offset(&b.name, ptr_bits)
                            && is_stack_base(a.name.to_ascii_lowercase().as_str())
                        {
                            changed |= set_stack_addr_offset(
                                block.addr,
                                dst,
                                off,
                                &mut stack_addr_offsets,
                                &mut stack_addr_offset_names,
                            );
                        }
                        if let Some(off) = parse_ssa_const_offset(&a.name, ptr_bits)
                            && is_stack_base(b.name.to_ascii_lowercase().as_str())
                        {
                            changed |= set_stack_addr_offset(
                                block.addr,
                                dst,
                                off,
                                &mut stack_addr_offsets,
                                &mut stack_addr_offset_names,
                            );
                        }
                        let expr = {
                            let ctx = ScalarArrayInferenceCtx {
                                parsed_context,
                                merged_signature,
                                ptr_bits,
                                pointer_arg_slot_map: &pointer_arg_slot_map,
                                pointer_values: &pointer_values,
                                pointer_value_names: &pointer_value_names,
                                array_addr_exprs: &array_addr_exprs,
                                array_addr_expr_names: &array_addr_expr_names,
                                stack_addr_offsets: &stack_addr_offsets,
                                stack_addr_offset_names: &stack_addr_offset_names,
                                block_ops: &block_ops,
                                value_ops: &value_ops,
                            };
                            scalar_array_expr_for_addend_pair(block.addr, a, b, &ctx)
                        };
                        if let Some(expr) = expr {
                            changed |= set_scalar_array_addr_expr(
                                block.addr,
                                dst,
                                expr,
                                &mut array_addr_exprs,
                                &mut array_addr_expr_names,
                            );
                        }
                        let pointer = {
                            let ctx = ScalarArrayInferenceCtx {
                                parsed_context,
                                merged_signature,
                                ptr_bits,
                                pointer_arg_slot_map: &pointer_arg_slot_map,
                                pointer_values: &pointer_values,
                                pointer_value_names: &pointer_value_names,
                                array_addr_exprs: &array_addr_exprs,
                                array_addr_expr_names: &array_addr_expr_names,
                                stack_addr_offsets: &stack_addr_offsets,
                                stack_addr_offset_names: &stack_addr_offset_names,
                                block_ops: &block_ops,
                                value_ops: &value_ops,
                            };
                            scalar_pointer_plus_const(block.addr, a, b, &ctx)
                                .or_else(|| scalar_pointer_plus_const(block.addr, b, a, &ctx))
                        };
                        if let Some(pointer) = pointer {
                            changed |= set_scalar_pointer_value(
                                block.addr,
                                dst,
                                pointer,
                                &mut pointer_values,
                                &mut pointer_value_names,
                            );
                        }
                    }
                    SSAOp::IntSub { dst, a, b } => {
                        if let Some(delta) = parse_ssa_const_offset(&b.name, ptr_bits)
                            && is_stack_base(a.name.to_ascii_lowercase().as_str())
                        {
                            changed |= set_stack_addr_offset(
                                block.addr,
                                dst,
                                delta.saturating_neg(),
                                &mut stack_addr_offsets,
                                &mut stack_addr_offset_names,
                            );
                        }
                        let pointer_expr = {
                            let ctx = ScalarArrayInferenceCtx {
                                parsed_context,
                                merged_signature,
                                ptr_bits,
                                pointer_arg_slot_map: &pointer_arg_slot_map,
                                pointer_values: &pointer_values,
                                pointer_value_names: &pointer_value_names,
                                array_addr_exprs: &array_addr_exprs,
                                array_addr_expr_names: &array_addr_expr_names,
                                stack_addr_offsets: &stack_addr_offsets,
                                stack_addr_offset_names: &stack_addr_offset_names,
                                block_ops: &block_ops,
                                value_ops: &value_ops,
                            };
                            scalar_pointer_value_for_var(block.addr, a, &ctx).filter(|pointer| {
                                scalar_index_matches_stride(
                                    block.addr,
                                    b,
                                    pointer.element_stride,
                                    &ctx,
                                    0,
                                )
                            })
                        };
                        if let Some(pointer) = pointer_expr {
                            let expr = ScalarArrayAddrExpr {
                                confidence: pointer.confidence.saturating_sub(4),
                                pointer,
                                field_offset: 0,
                            };
                            changed |= set_scalar_array_addr_expr(
                                block.addr,
                                dst,
                                expr,
                                &mut array_addr_exprs,
                                &mut array_addr_expr_names,
                            );
                        }
                        let pointer = {
                            let ctx = ScalarArrayInferenceCtx {
                                parsed_context,
                                merged_signature,
                                ptr_bits,
                                pointer_arg_slot_map: &pointer_arg_slot_map,
                                pointer_values: &pointer_values,
                                pointer_value_names: &pointer_value_names,
                                array_addr_exprs: &array_addr_exprs,
                                array_addr_expr_names: &array_addr_expr_names,
                                stack_addr_offsets: &stack_addr_offsets,
                                stack_addr_offset_names: &stack_addr_offset_names,
                                block_ops: &block_ops,
                                value_ops: &value_ops,
                            };
                            scalar_pointer_minus_const(block.addr, a, b, &ctx)
                        };
                        if let Some(pointer) = pointer {
                            changed |= set_scalar_pointer_value(
                                block.addr,
                                dst,
                                pointer,
                                &mut pointer_values,
                                &mut pointer_value_names,
                            );
                        }
                    }
                    SSAOp::Load { dst, addr, .. } => {
                        if let Some(offset) = stack_addr_offset_for_var(
                            block.addr,
                            addr,
                            &stack_addr_offsets,
                            &stack_addr_offset_names,
                        ) && let Some(mut pointer) =
                            scalar_pointer_value_for_stack_slot(parsed_context, offset, ptr_bits)
                        {
                            pointer.confidence = pointer.confidence.saturating_sub(1);
                            changed |= set_scalar_pointer_value(
                                block.addr,
                                dst,
                                pointer,
                                &mut pointer_values,
                                &mut pointer_value_names,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::Load { dst, addr, .. } => {
                    let ctx = ScalarArrayInferenceCtx {
                        parsed_context,
                        merged_signature,
                        ptr_bits,
                        pointer_arg_slot_map: &pointer_arg_slot_map,
                        pointer_values: &pointer_values,
                        pointer_value_names: &pointer_value_names,
                        array_addr_exprs: &array_addr_exprs,
                        array_addr_expr_names: &array_addr_expr_names,
                        stack_addr_offsets: &stack_addr_offsets,
                        stack_addr_offset_names: &stack_addr_offset_names,
                        block_ops: &block_ops,
                        value_ops: &value_ops,
                    };
                    if let Some(expr) = scalar_array_addr_expr_for_var(
                        block.addr,
                        addr,
                        &array_addr_exprs,
                        &array_addr_expr_names,
                    )
                    .or_else(|| direct_scalar_pointer_array_expr(block.addr, addr, &ctx))
                    {
                        push_scalar_array_access_certificates(
                            &mut certificates,
                            &expr,
                            u64::from(dst.size),
                            parsed_context,
                            merged_signature,
                            ptr_bits,
                        );
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    let ctx = ScalarArrayInferenceCtx {
                        parsed_context,
                        merged_signature,
                        ptr_bits,
                        pointer_arg_slot_map: &pointer_arg_slot_map,
                        pointer_values: &pointer_values,
                        pointer_value_names: &pointer_value_names,
                        array_addr_exprs: &array_addr_exprs,
                        array_addr_expr_names: &array_addr_expr_names,
                        stack_addr_offsets: &stack_addr_offsets,
                        stack_addr_offset_names: &stack_addr_offset_names,
                        block_ops: &block_ops,
                        value_ops: &value_ops,
                    };
                    if let Some(expr) = scalar_array_addr_expr_for_var(
                        block.addr,
                        addr,
                        &array_addr_exprs,
                        &array_addr_expr_names,
                    )
                    .or_else(|| direct_scalar_pointer_array_expr(block.addr, addr, &ctx))
                    {
                        push_scalar_array_access_certificates(
                            &mut certificates,
                            &expr,
                            u64::from(val.size),
                            parsed_context,
                            merged_signature,
                            ptr_bits,
                        );
                    }
                }
                _ => {}
            }
        }
    }

    certificates.array_index.sort();
    certificates.array_index.dedup();
    certificates.field_access.sort();
    certificates.field_access.dedup();
    certificates
}

fn push_scalar_array_access_certificates(
    certificates: &mut ScalarArrayAccessCertificates,
    expr: &ScalarArrayAddrExpr,
    access_width: u64,
    parsed_context: &ParsedExternalContext,
    merged_signature: Option<&FunctionSignatureSpec>,
    ptr_bits: u32,
) {
    let full_element_access = expr.field_offset == 0 && access_width == expr.pointer.element_stride;
    let field_layout = external_layout_field_access_for_scalar_expr(
        expr,
        access_width,
        parsed_context,
        merged_signature,
        ptr_bits,
    );

    if !full_element_access && field_layout.is_none() {
        return;
    }

    certificates.array_index.push(ArrayIndexCertificate {
        slot: expr.pointer.slot,
        base: Some(expr.pointer.base.clone()),
        field_offset: expr.field_offset,
        element_stride: expr.pointer.element_stride,
    });

    if let Some(field) = field_layout {
        certificates
            .field_access
            .push(crate::FieldAccessCertificate {
                slot: expr.pointer.slot,
                field_offset: expr.field_offset,
                field_name: field.name,
                field_type: field.ty,
            });
    }
}

fn external_layout_field_access_for_scalar_expr(
    expr: &ScalarArrayAddrExpr,
    access_width: u64,
    parsed_context: &ParsedExternalContext,
    merged_signature: Option<&FunctionSignatureSpec>,
    ptr_bits: u32,
) -> Option<ExternalLayoutFieldAccess> {
    aggregate_pointee_type_names_for_scalar_pointer(&expr.pointer, parsed_context, merged_signature)
        .into_iter()
        .find_map(|type_name| {
            external_layout_field_access_for_offset(
                &parsed_context.external_type_db,
                &type_name,
                expr.field_offset,
                access_width,
                ptr_bits,
            )
        })
}

fn aggregate_pointee_type_names_for_scalar_pointer(
    pointer: &ScalarPointerValue,
    parsed_context: &ParsedExternalContext,
    merged_signature: Option<&FunctionSignatureSpec>,
) -> Vec<String> {
    let names: Vec<String> = match &pointer.base {
        ArrayIndexBase::Param { index } => parsed_context
            .register_params
            .get(*index)
            .and_then(|param| param.ty.as_ref())
            .into_iter()
            .chain(
                merged_signature
                    .and_then(|signature| signature.params.get(*index))
                    .and_then(|param| param.ty.as_ref()),
            )
            .flat_map(aggregate_pointee_type_names_from_type)
            .collect(),
        ArrayIndexBase::StackSlot { slot } => parsed_context
            .stack_slots
            .get(slot)
            .and_then(|spec| spec.ty.as_ref())
            .into_iter()
            .flat_map(aggregate_pointee_type_names_from_type)
            .collect(),
    };
    names.into_iter().fold(Vec::new(), |mut out, name| {
        push_unique_type_name(&mut out, &name);
        out
    })
}

fn external_layout_field_access_for_offset(
    type_db: &ExternalTypeDb,
    type_name: &str,
    offset: u64,
    access_width: u64,
    ptr_bits: u32,
) -> Option<ExternalLayoutFieldAccess> {
    for key in aggregate_lookup_keys_for_writeback(type_name) {
        if let Some(st) = type_db.structs.get(&key)
            && let Some(field) =
                external_struct_field_access_for_offset(st, offset, access_width, ptr_bits)
        {
            return Some(field);
        }
        if let Some(un) = type_db.unions.get(&key)
            && let Some(field) =
                external_union_field_access_for_offset(un, offset, access_width, ptr_bits)
        {
            return Some(field);
        }
    }
    None
}

fn external_struct_field_access_for_offset(
    st: &ExternalStruct,
    offset: u64,
    access_width: u64,
    ptr_bits: u32,
) -> Option<ExternalLayoutFieldAccess> {
    st.fields
        .range(..=offset)
        .next_back()
        .and_then(|(_, field)| {
            external_field_access_for_offset(field, offset, access_width, ptr_bits)
        })
}

fn external_union_field_access_for_offset(
    un: &ExternalUnion,
    offset: u64,
    access_width: u64,
    ptr_bits: u32,
) -> Option<ExternalLayoutFieldAccess> {
    if offset != 0 {
        return None;
    }
    un.fields
        .values()
        .find_map(|field| external_field_access_for_offset(field, offset, access_width, ptr_bits))
}

fn external_field_access_for_offset(
    field: &ExternalField,
    offset: u64,
    access_width: u64,
    ptr_bits: u32,
) -> Option<ExternalLayoutFieldAccess> {
    if offset < field.offset {
        return None;
    }
    let rel = offset - field.offset;
    let field_ty = field.ty.as_deref();
    if let Some(CTypeLike::Array(inner, len)) =
        field_ty.and_then(|ty| parse_type_like_spec(ty, ptr_bits))
    {
        let elem_size = estimate_type_like_size_bytes(&inner, ptr_bits)?;
        if elem_size == 0 || !rel.is_multiple_of(elem_size) || access_width > elem_size {
            return None;
        }
        let index = rel / elem_size;
        if len.is_some_and(|count| index >= count as u64) {
            return None;
        }
        return Some(ExternalLayoutFieldAccess {
            name: format!("{}[{index}]", field.name),
            ty: Some(render_signature_type(&inner, ptr_bits)),
        });
    }

    if rel == 0 {
        return Some(ExternalLayoutFieldAccess {
            name: field.name.clone(),
            ty: field.ty.clone(),
        });
    }

    None
}

fn scalar_pointer_value_for_var(
    block_addr: u64,
    var: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarPointerValue> {
    let lower = var.name.to_ascii_lowercase();
    if let Some(param_index) = ctx.pointer_arg_slot_map.get(lower.as_str()).copied() {
        let has_local_def = ctx.value_ops.contains_key(&var.display_name())
            || ctx
                .block_ops
                .get(&block_addr)
                .is_some_and(|ops| ops.contains_key(&ssa_var_block_key(block_addr, var)));
        if var.version == 0 || !has_local_def {
            let ty = ctx
                .parsed_context
                .register_params
                .iter()
                .find(|param| param.reg.eq_ignore_ascii_case(&var.name))
                .and_then(|param| param.ty.as_ref())
                .or_else(|| {
                    ctx.merged_signature
                        .and_then(|signature| signature.params.get(param_index))
                        .and_then(|param| param.ty.as_ref())
                });
            if let Some(element_stride) = ty.and_then(|ty| {
                pointer_element_stride(ty, &ctx.parsed_context.external_type_db, ctx.ptr_bits)
            }) {
                return Some(ScalarPointerValue {
                    slot: param_index,
                    base: ArrayIndexBase::Param { index: param_index },
                    element_stride,
                    confidence: if var.version == 0 { 94 } else { 82 },
                });
            }
        }
    }
    ctx.pointer_values
        .get(&ssa_var_block_key(block_addr, var))
        .cloned()
        .or_else(|| {
            ctx.pointer_value_names
                .get(&var.display_name())
                .and_then(Clone::clone)
        })
}

fn scalar_pointer_value_for_stack_slot(
    parsed_context: &ParsedExternalContext,
    offset: i64,
    ptr_bits: u32,
) -> Option<ScalarPointerValue> {
    parsed_context
        .stack_slots
        .iter()
        .filter(|(key, _)| key.offset == offset)
        .filter_map(|(key, spec)| {
            let element_stride = spec.ty.as_ref().and_then(|ty| {
                pointer_element_stride(ty, &parsed_context.external_type_db, ptr_bits)
            })?;
            Some(ScalarPointerValue {
                slot: legacy_array_slot_for_stack_slot(key),
                base: ArrayIndexBase::StackSlot { slot: key.clone() },
                element_stride,
                confidence: 94,
            })
        })
        .next()
}

fn legacy_array_slot_for_stack_slot(key: &StackSlotKey) -> usize {
    // Retain the legacy numeric slot while the exact owner is carried by
    // ArrayIndexBase::StackSlot.
    1_000_000usize.saturating_add(key.offset.unsigned_abs() as usize)
}

fn pointer_element_stride(ty: &CTypeLike, type_db: &ExternalTypeDb, ptr_bits: u32) -> Option<u64> {
    match ty {
        CTypeLike::Pointer(inner) | CTypeLike::Array(inner, _) => {
            scalar_element_stride(inner, ptr_bits).or_else(|| {
                aggregate_pointee_type_names_from_type(ty)
                    .into_iter()
                    .find_map(|name| external_aggregate_size(type_db, &name, ptr_bits))
            })
        }
        _ => None,
    }
}

fn scalar_element_stride(ty: &CTypeLike, ptr_bits: u32) -> Option<u64> {
    match ty {
        CTypeLike::Bool | CTypeLike::Int { .. } | CTypeLike::Float(_) => {
            estimate_type_like_size_bytes(ty, ptr_bits).filter(|size| *size > 0)
        }
        CTypeLike::Typedef(name) => {
            let normalized = normalize_external_type_name(name);
            parse_type_like_spec(&normalized, ptr_bits).and_then(|parsed| match parsed {
                CTypeLike::Bool | CTypeLike::Int { .. } | CTypeLike::Float(_) => {
                    estimate_type_like_size_bytes(&parsed, ptr_bits).filter(|size| *size > 0)
                }
                _ => None,
            })
        }
        CTypeLike::Void
        | CTypeLike::Unknown
        | CTypeLike::Pointer(_)
        | CTypeLike::Array(_, _)
        | CTypeLike::Struct(_)
        | CTypeLike::Union(_)
        | CTypeLike::Enum(_)
        | CTypeLike::Function => None,
    }
}

fn set_scalar_pointer_value(
    block_addr: u64,
    dst: &SSAVar,
    pointer: ScalarPointerValue,
    pointer_values: &mut HashMap<String, ScalarPointerValue>,
    pointer_value_names: &mut HashMap<String, Option<ScalarPointerValue>>,
) -> bool {
    let key = ssa_var_block_key(block_addr, dst);
    match pointer_values.get(&key) {
        Some(prev) if prev.confidence >= pointer.confidence => false,
        _ => {
            pointer_values.insert(key, pointer.clone());
            merge_named_scalar_pointer_value(dst, pointer, pointer_value_names);
            true
        }
    }
}

fn set_scalar_array_addr_expr(
    block_addr: u64,
    dst: &SSAVar,
    expr: ScalarArrayAddrExpr,
    array_addr_exprs: &mut HashMap<String, ScalarArrayAddrExpr>,
    array_addr_expr_names: &mut HashMap<String, Option<ScalarArrayAddrExpr>>,
) -> bool {
    let key = ssa_var_block_key(block_addr, dst);
    match array_addr_exprs.get(&key) {
        Some(prev) if prev.confidence >= expr.confidence => false,
        _ => {
            array_addr_exprs.insert(key, expr.clone());
            merge_named_scalar_array_addr_expr(dst, expr, array_addr_expr_names);
            true
        }
    }
}

fn set_stack_addr_offset(
    block_addr: u64,
    dst: &SSAVar,
    offset: i64,
    stack_addr_offsets: &mut HashMap<String, i64>,
    stack_addr_offset_names: &mut HashMap<String, Option<i64>>,
) -> bool {
    let key = ssa_var_block_key(block_addr, dst);
    match stack_addr_offsets.get(&key).copied() {
        Some(prev) if prev == offset => false,
        _ => {
            stack_addr_offsets.insert(key, offset);
            merge_named_stack_addr_offset(dst, offset, stack_addr_offset_names);
            true
        }
    }
}

fn merge_named_scalar_pointer_value(
    dst: &SSAVar,
    pointer: ScalarPointerValue,
    pointer_value_names: &mut HashMap<String, Option<ScalarPointerValue>>,
) {
    merge_named_fact(dst, pointer, pointer_value_names);
}

fn merge_named_scalar_array_addr_expr(
    dst: &SSAVar,
    expr: ScalarArrayAddrExpr,
    array_addr_expr_names: &mut HashMap<String, Option<ScalarArrayAddrExpr>>,
) {
    merge_named_fact(dst, expr, array_addr_expr_names);
}

fn merge_named_stack_addr_offset(
    dst: &SSAVar,
    offset: i64,
    stack_addr_offset_names: &mut HashMap<String, Option<i64>>,
) {
    merge_named_fact(dst, offset, stack_addr_offset_names);
}

fn merge_named_fact<T: Clone + PartialEq>(
    dst: &SSAVar,
    fact: T,
    named_facts: &mut HashMap<String, Option<T>>,
) {
    let key = dst.display_name();
    match named_facts.get(&key) {
        None => {
            named_facts.insert(key, Some(fact));
        }
        Some(Some(prev)) if prev == &fact => {}
        Some(_) => {
            named_facts.insert(key, None);
        }
    }
}

fn stack_addr_offset_for_var(
    block_addr: u64,
    var: &SSAVar,
    stack_addr_offsets: &HashMap<String, i64>,
    stack_addr_offset_names: &HashMap<String, Option<i64>>,
) -> Option<i64> {
    stack_addr_offsets
        .get(&ssa_var_block_key(block_addr, var))
        .copied()
        .or_else(|| {
            stack_addr_offset_names
                .get(&var.display_name())
                .and_then(|value| *value)
        })
}

fn scalar_array_addr_expr_for_var(
    block_addr: u64,
    var: &SSAVar,
    array_addr_exprs: &HashMap<String, ScalarArrayAddrExpr>,
    array_addr_expr_names: &HashMap<String, Option<ScalarArrayAddrExpr>>,
) -> Option<ScalarArrayAddrExpr> {
    array_addr_exprs
        .get(&ssa_var_block_key(block_addr, var))
        .cloned()
        .or_else(|| {
            array_addr_expr_names
                .get(&var.display_name())
                .and_then(Clone::clone)
        })
}

fn phi_scalar_pointer_value(
    block_addr: u64,
    dst: &SSAVar,
    sources: &[SSAVar],
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarPointerValue> {
    let mut selected: Option<ScalarPointerValue> = None;
    let mut unknown_sources = Vec::new();
    for src in sources {
        let Some(pointer) = scalar_pointer_value_for_var(block_addr, src, ctx) else {
            unknown_sources.push(src);
            continue;
        };
        selected = match selected {
            None => Some(pointer),
            Some(prev)
                if prev.base == pointer.base && prev.element_stride == pointer.element_stride =>
            {
                Some(ScalarPointerValue {
                    confidence: prev.confidence.max(pointer.confidence),
                    ..prev
                })
            }
            _ => return None,
        };
    }
    let mut selected = selected?;
    for src in unknown_sources {
        if !phi_source_is_const_stride_pointer_recurrence(dst, src, &selected, ctx, 0) {
            return None;
        }
        selected.confidence = selected.confidence.saturating_sub(4);
    }
    Some(selected)
}

fn phi_source_is_const_stride_pointer_recurrence(
    phi_dst: &SSAVar,
    src: &SSAVar,
    pointer: &ScalarPointerValue,
    ctx: &ScalarArrayInferenceCtx<'_>,
    depth: u32,
) -> bool {
    if depth > 4 {
        return false;
    }
    let Some(op) = ctx.value_ops.get(&src.display_name()) else {
        return false;
    };
    match op {
        SSAOp::Copy { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::New { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            src == phi_dst
                || phi_source_is_const_stride_pointer_recurrence(
                    phi_dst,
                    src,
                    pointer,
                    ctx,
                    depth + 1,
                )
        }
        SSAOp::IntAdd { a, b, .. } => {
            phi_pointer_step_matches(phi_dst, a, b, pointer, ctx)
                || phi_pointer_step_matches(phi_dst, b, a, pointer, ctx)
        }
        SSAOp::IntSub { a, b, .. } => phi_pointer_step_matches(phi_dst, a, b, pointer, ctx),
        _ => false,
    }
}

fn phi_pointer_step_matches(
    phi_dst: &SSAVar,
    pointer_term: &SSAVar,
    offset_term: &SSAVar,
    pointer: &ScalarPointerValue,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> bool {
    if pointer_term != phi_dst {
        return false;
    }
    let Some(offset) = parse_ssa_const_offset(&offset_term.name, ctx.ptr_bits) else {
        return false;
    };
    offset
        .unsigned_abs()
        .is_multiple_of(pointer.element_stride.max(1))
}

fn phi_scalar_array_addr_expr(
    block_addr: u64,
    sources: &[SSAVar],
    array_addr_exprs: &HashMap<String, ScalarArrayAddrExpr>,
    array_addr_expr_names: &HashMap<String, Option<ScalarArrayAddrExpr>>,
) -> Option<ScalarArrayAddrExpr> {
    let mut selected: Option<ScalarArrayAddrExpr> = None;
    for src in sources {
        let expr = scalar_array_addr_expr_for_var(
            block_addr,
            src,
            array_addr_exprs,
            array_addr_expr_names,
        )?;
        selected = match selected {
            None => Some(expr),
            Some(prev)
                if prev.pointer.base == expr.pointer.base
                    && prev.pointer.element_stride == expr.pointer.element_stride
                    && prev.field_offset == expr.field_offset =>
            {
                Some(ScalarArrayAddrExpr {
                    confidence: prev.confidence.max(expr.confidence),
                    ..prev
                })
            }
            _ => return None,
        };
    }
    selected
}

fn scalar_array_expr_for_addend_pair(
    block_addr: u64,
    a: &SSAVar,
    b: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarArrayAddrExpr> {
    if let Some(expr) = scalar_array_plus_const(block_addr, a, b, ctx) {
        return Some(expr);
    }
    if let Some(expr) = scalar_array_plus_const(block_addr, b, a, ctx) {
        return Some(expr);
    }
    if let Some(expr) = scalar_pointer_plus_index(block_addr, a, b, ctx) {
        return Some(expr);
    }
    scalar_pointer_plus_index(block_addr, b, a, ctx)
}

fn direct_scalar_pointer_array_expr(
    block_addr: u64,
    var: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarArrayAddrExpr> {
    let pointer = scalar_pointer_value_for_var(block_addr, var, ctx)?;
    Some(ScalarArrayAddrExpr {
        confidence: pointer.confidence.saturating_sub(2),
        pointer,
        field_offset: 0,
    })
}

fn scalar_pointer_plus_const(
    block_addr: u64,
    pointer_var: &SSAVar,
    const_var: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarPointerValue> {
    let offset = parse_ssa_const_offset(&const_var.name, ctx.ptr_bits)?;
    scalar_pointer_offset_by_const(block_addr, pointer_var, offset, ctx)
}

fn scalar_pointer_minus_const(
    block_addr: u64,
    pointer_var: &SSAVar,
    const_var: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarPointerValue> {
    let offset = parse_ssa_const_offset(&const_var.name, ctx.ptr_bits)?;
    scalar_pointer_offset_by_const(block_addr, pointer_var, offset.saturating_neg(), ctx)
}

fn scalar_pointer_offset_by_const(
    block_addr: u64,
    pointer_var: &SSAVar,
    offset: i64,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarPointerValue> {
    let mut pointer = scalar_pointer_value_for_var(block_addr, pointer_var, ctx)?;
    let stride = pointer.element_stride.max(1);
    if !offset.unsigned_abs().is_multiple_of(stride) {
        return None;
    }
    pointer.confidence = pointer.confidence.saturating_sub(3);
    Some(pointer)
}

fn scalar_array_plus_const(
    block_addr: u64,
    array_var: &SSAVar,
    const_var: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarArrayAddrExpr> {
    let offset = parse_ssa_const_offset(&const_var.name, ctx.ptr_bits)?;
    let mut expr = scalar_array_addr_expr_for_var(
        block_addr,
        array_var,
        ctx.array_addr_exprs,
        ctx.array_addr_expr_names,
    )?;
    if offset < 0 {
        return None;
    }
    expr.field_offset = expr.field_offset.checked_add(offset as u64)?;
    expr.confidence = expr.confidence.saturating_sub(1);
    Some(expr)
}

fn scalar_pointer_plus_index(
    block_addr: u64,
    pointer_var: &SSAVar,
    index_var: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
) -> Option<ScalarArrayAddrExpr> {
    let pointer = scalar_pointer_value_for_var(block_addr, pointer_var, ctx)?;
    if !scalar_index_matches_stride(block_addr, index_var, pointer.element_stride, ctx, 0) {
        return None;
    }
    Some(ScalarArrayAddrExpr {
        confidence: pointer.confidence.saturating_sub(4),
        pointer,
        field_offset: 0,
    })
}

fn scalar_index_matches_stride(
    block_addr: u64,
    var: &SSAVar,
    stride: u64,
    ctx: &ScalarArrayInferenceCtx<'_>,
    depth: u32,
) -> bool {
    if depth > 8 {
        return false;
    }
    let key = ssa_var_block_key(block_addr, var);
    if ctx.pointer_values.contains_key(&key)
        || ctx.array_addr_exprs.contains_key(&key)
        || ctx.stack_addr_offsets.contains_key(&key)
        || ctx
            .pointer_value_names
            .get(&var.display_name())
            .and_then(Clone::clone)
            .is_some()
        || ctx
            .array_addr_expr_names
            .get(&var.display_name())
            .and_then(Clone::clone)
            .is_some()
        || ctx
            .stack_addr_offset_names
            .get(&var.display_name())
            .and_then(|value| *value)
            .is_some()
    {
        return false;
    }
    if let Some(offset) = parse_ssa_const_offset(&var.name, 64) {
        return offset >= 0 && (offset as u64).is_multiple_of(stride.max(1));
    }
    if let Some(factor) = scalar_index_affine_factor(block_addr, var, ctx, depth)
        && factor.root.is_some()
        && factor.scale.unsigned_abs() == u128::from(stride)
    {
        return true;
    }
    if stride == 1 && var.version == 0 {
        return true;
    }
    let Some(op) = ctx.block_ops.get(&block_addr).and_then(|ops| ops.get(&key)) else {
        return stride == 1;
    };
    match op {
        SSAOp::Copy { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::New { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            scalar_index_matches_stride(block_addr, src, stride, ctx, depth + 1)
        }
        SSAOp::Load { .. } | SSAOp::Phi { .. } => stride == 1,
        SSAOp::IntMult { a, b, .. } => {
            scaled_index_term_matches_stride(block_addr, a, b, stride, ctx, depth + 1)
        }
        SSAOp::IntLeft { a, b, .. } => {
            parse_ssa_const_offset(&b.name, 64)
                .and_then(|shift| (shift >= 0).then_some(1u64.checked_shl(shift as u32)?))
                == Some(stride)
                && scalar_index_matches_stride(block_addr, a, 1, ctx, depth + 1)
        }
        SSAOp::IntAdd { a, b, .. } | SSAOp::IntSub { a, b, .. } => {
            stride == 1
                && scalar_index_matches_stride(block_addr, a, stride, ctx, depth + 1)
                && scalar_index_matches_stride(block_addr, b, stride, ctx, depth + 1)
        }
        _ => false,
    }
}

fn scalar_index_affine_factor(
    block_addr: u64,
    var: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
    depth: u32,
) -> Option<AffineIndexFactor> {
    if depth > 8 {
        return None;
    }
    let key = ssa_var_block_key(block_addr, var);
    if ctx.pointer_values.contains_key(&key)
        || ctx.array_addr_exprs.contains_key(&key)
        || ctx.stack_addr_offsets.contains_key(&key)
        || ctx
            .pointer_value_names
            .get(&var.display_name())
            .and_then(Clone::clone)
            .is_some()
        || ctx
            .array_addr_expr_names
            .get(&var.display_name())
            .and_then(Clone::clone)
            .is_some()
        || ctx
            .stack_addr_offset_names
            .get(&var.display_name())
            .and_then(|value| *value)
            .is_some()
    {
        return None;
    }
    if parse_ssa_const_offset(&var.name, 64).is_some() {
        return Some(AffineIndexFactor {
            root: None,
            scale: 0,
        });
    }
    if var.version == 0 {
        return Some(AffineIndexFactor {
            root: Some(var.name.to_ascii_lowercase()),
            scale: 1,
        });
    }

    let op = ctx
        .block_ops
        .get(&block_addr)
        .and_then(|ops| ops.get(&key))?;
    match op {
        SSAOp::Copy { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::New { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            scalar_index_affine_factor(block_addr, src, ctx, depth + 1)
        }
        SSAOp::IntMult { a, b, .. } => affine_scaled_term(block_addr, a, b, ctx, depth + 1)
            .or_else(|| affine_scaled_term(block_addr, b, a, ctx, depth + 1)),
        SSAOp::IntLeft { a, b, .. } => {
            let shift = parse_ssa_const_offset(&b.name, 64)?;
            if shift < 0 {
                return None;
            }
            let factor = scalar_index_affine_factor(block_addr, a, ctx, depth + 1)?;
            let multiplier = 1i128.checked_shl(shift as u32)?;
            Some(AffineIndexFactor {
                root: factor.root,
                scale: factor.scale.checked_mul(multiplier)?,
            })
        }
        SSAOp::IntAdd { a, b, .. } => {
            let left = scalar_index_affine_factor(block_addr, a, ctx, depth + 1)?;
            let right = scalar_index_affine_factor(block_addr, b, ctx, depth + 1)?;
            combine_affine_terms(left, right, 1)
        }
        SSAOp::IntSub { a, b, .. } => {
            let left = scalar_index_affine_factor(block_addr, a, ctx, depth + 1)?;
            let right = scalar_index_affine_factor(block_addr, b, ctx, depth + 1)?;
            combine_affine_terms(left, right, -1)
        }
        _ => None,
    }
}

fn affine_scaled_term(
    block_addr: u64,
    term: &SSAVar,
    multiplier: &SSAVar,
    ctx: &ScalarArrayInferenceCtx<'_>,
    depth: u32,
) -> Option<AffineIndexFactor> {
    let multiplier = parse_ssa_const_offset(&multiplier.name, 64)?;
    let factor = scalar_index_affine_factor(block_addr, term, ctx, depth)?;
    Some(AffineIndexFactor {
        root: factor.root,
        scale: factor.scale.checked_mul(i128::from(multiplier))?,
    })
}

fn combine_affine_terms(
    left: AffineIndexFactor,
    right: AffineIndexFactor,
    right_sign: i128,
) -> Option<AffineIndexFactor> {
    let root = match (left.root, right.root) {
        (Some(left_root), Some(right_root)) if left_root == right_root => Some(left_root),
        (Some(left_root), None) => Some(left_root),
        (None, Some(right_root)) => Some(right_root),
        (None, None) => None,
        _ => return None,
    };
    Some(AffineIndexFactor {
        root,
        scale: left
            .scale
            .checked_add(right.scale.checked_mul(right_sign)?)?,
    })
}

fn scaled_index_term_matches_stride(
    block_addr: u64,
    a: &SSAVar,
    b: &SSAVar,
    stride: u64,
    ctx: &ScalarArrayInferenceCtx<'_>,
    depth: u32,
) -> bool {
    if parse_ssa_const_offset(&a.name, 64).is_some_and(|value| value >= 0 && value as u64 == stride)
    {
        return scalar_index_matches_stride(block_addr, b, 1, ctx, depth + 1);
    }
    if parse_ssa_const_offset(&b.name, 64).is_some_and(|value| value >= 0 && value as u64 == stride)
    {
        return scalar_index_matches_stride(block_addr, a, 1, ctx, depth + 1);
    }
    false
}

fn push_signature_certificate_source(
    sources: &mut Vec<SignatureCertificateSource>,
    source: SignatureCertificateSource,
) {
    if !sources.contains(&source) {
        sources.push(source);
    }
}

fn signature_certificate_from_merged(
    merged_signature: Option<&FunctionSignatureSpec>,
    sources: &[SignatureCertificateSource],
) -> Option<SignatureCertificate> {
    let signature = merged_signature?;
    SignatureCertificate::from_signature(signature, sources.iter().copied())
}

fn out_param_certificates_from_projection(
    projection: &SemanticTypeProjection,
    merged_signature: Option<&FunctionSignatureSpec>,
    ptr_bits: u32,
) -> Vec<OutParamCertificate> {
    let mut certificates = projection
        .out_param_evidence
        .iter()
        .filter(|(_, evidence)| !evidence.is_empty())
        .map(|(param_index, evidence)| {
            let param = merged_signature.and_then(|signature| signature.params.get(*param_index));
            let param_name = param
                .map(|param| param.name.clone())
                .filter(|name| !name.trim().is_empty())
                .unwrap_or_else(|| format!("arg{}", param_index + 1));
            let pointee_type = param
                .and_then(|param| param.ty.as_ref())
                .and_then(|ty| match ty {
                    CTypeLike::Pointer(inner) => Some(render_signature_type(inner, ptr_bits)),
                    _ => None,
                });
            OutParamCertificate {
                param_index: *param_index,
                param_name,
                pointee_type,
                evidence: evidence.iter().copied().collect(),
                sources: projection
                    .out_param_sources
                    .get(param_index)
                    .map(|sources| sources.iter().cloned().collect())
                    .unwrap_or_default(),
            }
        })
        .collect::<Vec<_>>();
    certificates.sort();
    certificates.dedup();
    certificates
}

fn aggregate_stride_for_slot(
    slot: usize,
    local_structs: &LocalStructArtifacts,
    merged_signature: Option<&FunctionSignatureSpec>,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
) -> Option<u64> {
    local_structs
        .slot_type_overrides
        .get(&slot)
        .into_iter()
        .flat_map(|raw_ty| aggregate_pointee_type_names_from_str(raw_ty, ptr_bits))
        .chain(
            merged_signature
                .and_then(|signature| signature.params.get(slot))
                .and_then(|param| param.ty.as_ref())
                .into_iter()
                .flat_map(aggregate_pointee_type_names_from_type),
        )
        .find_map(|name| external_aggregate_size(type_db, &name, ptr_bits))
}

fn aggregate_pointee_type_names_from_str(raw_ty: &str, ptr_bits: u32) -> Vec<String> {
    parse_type_like_spec(raw_ty, ptr_bits)
        .map(|ty| aggregate_pointee_type_names_from_type(&ty))
        .unwrap_or_default()
}

fn aggregate_pointee_type_names_from_type(ty: &CTypeLike) -> Vec<String> {
    let mut out = Vec::new();
    if let CTypeLike::Pointer(inner) | CTypeLike::Array(inner, _) = ty {
        collect_aggregate_type_names(inner, &mut out);
    }
    out
}

fn collect_aggregate_type_names(ty: &CTypeLike, out: &mut Vec<String>) {
    match ty {
        CTypeLike::Struct(name) | CTypeLike::Union(name) | CTypeLike::Enum(name) => {
            push_unique_type_name(out, name);
        }
        CTypeLike::Typedef(name) => {
            push_unique_type_name(out, name);
            push_unique_type_name(out, &format!("struct {name}"));
            push_unique_type_name(out, &format!("union {name}"));
        }
        CTypeLike::Pointer(inner) | CTypeLike::Array(inner, _) => {
            collect_aggregate_type_names(inner, out);
        }
        CTypeLike::Void
        | CTypeLike::Unknown
        | CTypeLike::Bool
        | CTypeLike::Int { .. }
        | CTypeLike::Float(_)
        | CTypeLike::Function => {}
    }
}

fn push_unique_type_name(out: &mut Vec<String>, name: &str) {
    let trimmed = name.trim();
    if !trimmed.is_empty() && !out.iter().any(|existing| existing == trimmed) {
        out.push(trimmed.to_string());
    }
}

fn external_aggregate_size(type_db: &ExternalTypeDb, name: &str, ptr_bits: u32) -> Option<u64> {
    for key in aggregate_lookup_keys_for_writeback(name) {
        if let Some(st) = type_db.structs.get(&key)
            && let Some(size) = external_struct_size(st, ptr_bits)
        {
            return Some(size);
        }
        if let Some(un) = type_db.unions.get(&key) {
            let size = un
                .fields
                .values()
                .filter_map(|field| {
                    field
                        .ty
                        .as_deref()
                        .map(|ty| estimate_c_type_size_bytes(ty, ptr_bits))
                })
                .max()
                .unwrap_or(1);
            return Some(size);
        }
    }
    None
}

fn aggregate_lookup_keys_for_writeback(name: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut push = |candidate: &str| {
        let key = candidate.trim().to_ascii_lowercase();
        if !key.is_empty() && !out.contains(&key) {
            out.push(key);
        }
    };

    let trimmed = name.trim();
    push(trimmed);
    for prefix in ["struct ", "union ", "enum "] {
        if let Some(rest) = trimmed.strip_prefix(prefix) {
            push(rest);
        }
    }

    let normalized = normalize_external_type_name(trimmed);
    if normalized != "void *" {
        push(&normalized);
        for prefix in ["struct ", "union ", "enum "] {
            if let Some(rest) = normalized.strip_prefix(prefix) {
                push(rest);
            }
        }
    }

    out
}

fn external_struct_size(st: &ExternalStruct, ptr_bits: u32) -> Option<u64> {
    st.fields
        .values()
        .filter_map(|field| {
            let ty = field.ty.as_deref().unwrap_or("uint8_t");
            let width = estimate_c_type_size_bytes(ty, ptr_bits).max(1);
            field.offset.checked_add(width)
        })
        .max()
}

fn profile_minimum_stride(fields: &BTreeMap<u64, String>, ptr_bits: u32) -> Option<u64> {
    fields
        .iter()
        .filter_map(|(offset, ty)| offset.checked_add(estimate_c_type_size_bytes(ty, ptr_bits)))
        .max()
}

pub fn augment_local_struct_artifacts_with_semantics(
    local_structs: &mut LocalStructArtifacts,
    artifact: &r2sym::SemanticArtifact,
    ptr_bits: u32,
) {
    let projection = SemanticTypeProjection::from_inputs(
        &InterprocSummaryView::default(),
        Some(artifact),
        ptr_bits,
    );
    augment_local_struct_artifacts_with_projection(local_structs, &projection, ptr_bits);
}

fn augment_local_struct_artifacts_with_projection(
    local_structs: &mut LocalStructArtifacts,
    projection: &SemanticTypeProjection,
    ptr_bits: u32,
) {
    for (slot, projected) in &projection.slot_field_profiles {
        let profile = local_structs.slot_field_profiles.entry(*slot).or_default();
        for (offset, field_type) in projected {
            profile.entry(*offset).or_insert(field_type.clone());
        }
        if profile.is_empty() || local_structs.slot_type_overrides.contains_key(slot) {
            continue;
        }
        let struct_name = format!("sla_struct_symbolic_arg{}", slot + 1);
        let fields = profile
            .iter()
            .map(|(offset, field_type)| StructFieldCandidate {
                name: format!("f_{offset:x}"),
                offset: *offset,
                field_type: field_type.clone(),
                confidence: 84,
            })
            .collect::<Vec<_>>();
        let Some(decl) = build_struct_decl(&struct_name, &fields, ptr_bits) else {
            continue;
        };
        if !local_structs
            .struct_decls
            .iter()
            .any(|candidate| candidate.name.eq_ignore_ascii_case(&struct_name))
        {
            local_structs.struct_decls.push(StructDeclCandidate {
                name: struct_name.clone(),
                decl,
                confidence: 84,
                source: StructDeclSource::LocalInferred,
                fields,
            });
        }
        local_structs
            .slot_type_overrides
            .insert(*slot, format!("struct {struct_name} *"));
    }
}

fn augment_local_struct_artifacts_with_local_field_accesses(
    local_structs: &mut LocalStructArtifacts,
    local_field_accesses: &[LocalFieldAccessFact],
    ptr_bits: u32,
) {
    let mut projected_profiles = BTreeMap::<usize, BTreeMap<u64, String>>::new();
    for access in local_field_accesses {
        let field_type = access
            .field_type
            .clone()
            .unwrap_or_else(|| access.field_name.clone());
        projected_profiles
            .entry(access.slot)
            .or_default()
            .entry(access.field_offset)
            .or_insert(field_type);
    }

    for (slot, projected) in projected_profiles {
        let profile = local_structs.slot_field_profiles.entry(slot).or_default();
        for (offset, field_type) in projected {
            profile.entry(offset).or_insert(field_type);
        }
        if profile.is_empty() || local_structs.slot_type_overrides.contains_key(&slot) {
            continue;
        }

        let allow_single_field = profile.len() == 1;
        if profile.len() < 2 && !allow_single_field {
            continue;
        }
        let mut shape = String::new();
        let fields = profile
            .iter()
            .map(|(offset, field_type)| {
                shape.push_str(&format!("{offset:x}:{field_type};"));
                StructFieldCandidate {
                    name: format!("f_{offset:x}"),
                    offset: *offset,
                    field_type: field_type.clone(),
                    confidence: 90,
                }
            })
            .collect::<Vec<_>>();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hasher);
        let struct_name = format!("sla_struct_{:016x}", hasher.finish());
        let Some(decl) = build_struct_decl(&struct_name, &fields, ptr_bits) else {
            continue;
        };
        if !local_structs
            .struct_decls
            .iter()
            .any(|candidate| candidate.name.eq_ignore_ascii_case(&struct_name))
        {
            local_structs.struct_decls.push(StructDeclCandidate {
                name: struct_name.clone(),
                decl,
                confidence: 90,
                source: StructDeclSource::LocalInferred,
                fields,
            });
        }
        local_structs
            .slot_type_overrides
            .insert(slot, format!("struct {struct_name} *"));
    }
}

fn backward_memory_term_slot_field(
    term: &r2sym::BackwardMemoryCondition,
    _ptr_bits: u32,
) -> Option<(usize, u64, String)> {
    if !term.evidence().is_reliable() {
        return None;
    }
    let slot = match &term.region {
        r2sym::BackwardMemoryRegion::Argument { index } => *index,
        r2sym::BackwardMemoryRegion::Region(_) => return None,
    };
    if !term.exact_offset && term.offset_lo != term.offset_hi {
        return None;
    }
    if term.offset_lo < 0 || term.offset_hi < 0 || term.offset_lo != term.offset_hi {
        return None;
    }
    Some((slot, term.offset_lo as u64, size_to_type(term.size)))
}

fn canonicalize_param_home_stack_slots(
    merged_signature: Option<&FunctionSignatureSpec>,
    register_params: &[crate::context::ExternalRegisterParamSpec],
    stack_slots: &mut BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    ssa_blocks: &[SSABlock],
    ptr_bits: u32,
) {
    if register_params.is_empty() || ssa_blocks.is_empty() {
        return;
    }

    let trivial_value_sources = collect_trivial_value_sources(ssa_blocks);
    let mut slot_addr_by_var = HashMap::<String, StackSlotKey>::new();
    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::IntAdd { dst, a, b } => {
                    if let Some(slot_key) = stack_slot_key_from_add_sub(a, b, false, ptr_bits) {
                        slot_addr_by_var.insert(dst.display_name(), slot_key);
                    }
                }
                SSAOp::IntSub { dst, a, b } => {
                    if let Some(slot_key) = stack_slot_key_from_add_sub(a, b, true, ptr_bits) {
                        slot_addr_by_var.insert(dst.display_name(), slot_key);
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    let Some(slot_key) = slot_addr_by_var.get(&addr.display_name()).cloned() else {
                        continue;
                    };
                    let rooted_val = resolve_trivial_value_root(&trivial_value_sources, val);
                    let Some((param_index, param_reg)) =
                        register_params.iter().enumerate().find_map(|(idx, param)| {
                            register_family_matches(&param.reg, &rooted_val.name)
                                .then_some((idx, param.reg.clone()))
                        })
                    else {
                        continue;
                    };
                    if rooted_val.version != 0 {
                        continue;
                    }
                    let param_name = merged_signature
                        .and_then(|sig| sig.params.get(param_index))
                        .map(|param| param.name.clone())
                        .filter(|name| !name.is_empty())
                        .unwrap_or_else(|| format!("arg{}", param_index + 1));
                    let slot_base = slot_key.base.clone();
                    let slot =
                        stack_slots
                            .entry(slot_key)
                            .or_insert_with(|| ExternalStackVarSpec {
                                name: format!("{param_name}_home"),
                                ty: merged_signature
                                    .and_then(|sig| sig.params.get(param_index))
                                    .and_then(|param| param.ty.clone()),
                                base: slot_base,
                                role: ExternalStackSlotRole::Unknown,
                                param_index: None,
                                param_name: None,
                                source_reg: None,
                            });
                    if !matches!(
                        slot.role,
                        ExternalStackSlotRole::Unknown
                            | ExternalStackSlotRole::Local
                            | ExternalStackSlotRole::StackArg
                    ) {
                        continue;
                    }
                    slot.role = ExternalStackSlotRole::ParamHome;
                    slot.param_index = Some(param_index);
                    slot.param_name = Some(param_name.clone());
                    slot.source_reg = Some(param_reg);
                    if is_low_quality_stack_name(&slot.name) || slot.name.is_empty() {
                        slot.name = format!("{param_name}_home");
                    }
                }
                _ => {}
            }
        }
    }
}

fn hide_unproven_stack_pointer_frame_slots(
    stack_slots: &mut BTreeMap<StackSlotKey, ExternalStackVarSpec>,
) {
    let has_frame_pointer_slots = stack_slots
        .keys()
        .any(|slot_key| matches!(slot_key.base, ExternalStackBase::FramePointer));
    if !has_frame_pointer_slots {
        return;
    }

    for (slot_key, slot) in stack_slots {
        if !matches!(slot_key.base, ExternalStackBase::StackPointer)
            || slot_key.offset != 0
            || !matches!(slot.role, ExternalStackSlotRole::Unknown)
            || slot.param_index.is_some()
            || slot.param_name.is_some()
            || slot.source_reg.is_some()
            || !is_low_quality_stack_name(&slot.name)
        {
            continue;
        }
        slot.role = ExternalStackSlotRole::SavedFp;
        slot.name = "saved_fp".to_string();
    }
}

fn collect_trivial_value_sources(ssa_blocks: &[SSABlock]) -> HashMap<SSAVar, SSAVar> {
    let mut trivial_value_sources = HashMap::new();
    for block in ssa_blocks {
        for op in &block.ops {
            match op {
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src } => {
                    trivial_value_sources.insert(dst.clone(), src.clone());
                }
                SSAOp::Subpiece { dst, src, offset } if *offset == 0 => {
                    trivial_value_sources.insert(dst.clone(), src.clone());
                }
                _ => {}
            }
        }
    }
    trivial_value_sources
}

fn resolve_trivial_value_root(
    trivial_value_sources: &HashMap<SSAVar, SSAVar>,
    value: &SSAVar,
) -> SSAVar {
    let mut current = value.clone();
    let mut seen = HashSet::new();
    while seen.insert(current.clone()) {
        let Some(next) = trivial_value_sources.get(&current) else {
            break;
        };
        current = next.clone();
    }
    current
}

fn stack_slot_key_from_add_sub(
    a: &SSAVar,
    b: &SSAVar,
    is_sub: bool,
    ptr_bits: u32,
) -> Option<StackSlotKey> {
    let base = stack_base_from_var(a)?;
    let raw = parse_const_value(&b.name)?;
    let offset = signed_offset_from_const(raw, ptr_bits);
    Some(StackSlotKey {
        base,
        offset: if is_sub { -offset } else { offset },
    })
}

fn stack_base_from_var(var: &SSAVar) -> Option<ExternalStackBase> {
    let lower = var.name.to_ascii_lowercase();
    match lower.as_str() {
        "rbp" | "ebp" | "bp" | "fp" => Some(ExternalStackBase::FramePointer),
        "rsp" | "esp" | "sp" => Some(ExternalStackBase::StackPointer),
        _ => None,
    }
}

fn register_family_matches(expected: &str, actual: &str) -> bool {
    let expected = expected.to_ascii_lowercase();
    let actual = actual.to_ascii_lowercase();
    if expected == actual {
        return true;
    }

    fn family(name: &str) -> Option<&str> {
        match name {
            "rax" | "eax" | "ax" | "al" | "ah" => Some("ax"),
            "rbx" | "ebx" | "bx" | "bl" | "bh" => Some("bx"),
            "rcx" | "ecx" | "cx" | "cl" | "ch" => Some("cx"),
            "rdx" | "edx" | "dx" | "dl" | "dh" => Some("dx"),
            "rsi" | "esi" | "si" | "sil" => Some("si"),
            "rdi" | "edi" | "di" | "dil" => Some("di"),
            "rbp" | "ebp" | "bp" | "bpl" => Some("bp"),
            "rsp" | "esp" | "sp" | "spl" => Some("sp"),
            "r8" | "r8d" | "r8w" | "r8b" => Some("8"),
            "r9" | "r9d" | "r9w" | "r9b" => Some("9"),
            "r10" | "r10d" | "r10w" | "r10b" => Some("10"),
            "r11" | "r11d" | "r11w" | "r11b" => Some("11"),
            "r12" | "r12d" | "r12w" | "r12b" => Some("12"),
            "r13" | "r13d" | "r13w" | "r13b" => Some("13"),
            "r14" | "r14d" | "r14w" | "r14b" => Some("14"),
            "r15" | "r15d" | "r15w" | "r15b" => Some("15"),
            _ => None,
        }
    }

    family(&expected) == family(&actual)
}

fn parse_signature_type_preserving_c_typedefs(ty: &str, ptr_bits: u32) -> Option<CTypeLike> {
    match normalize_external_type_name(ty)
        .trim()
        .to_ascii_lowercase()
        .as_str()
    {
        "int" => Some(c_int_type()),
        "unsigned int" => Some(c_uint_type()),
        "short" | "short int" => Some(typedef_type("short")),
        "unsigned short" | "unsigned short int" => Some(typedef_type("unsigned short")),
        "long" | "long int" => Some(typedef_type("long")),
        "unsigned long" | "unsigned long int" => Some(typedef_type("unsigned long")),
        "size_t" => Some(typedef_type("size_t")),
        "ssize_t" => Some(typedef_type("ssize_t")),
        "ptrdiff_t" => Some(typedef_type("ptrdiff_t")),
        "uintptr_t" => Some(typedef_type("uintptr_t")),
        "intptr_t" => Some(typedef_type("intptr_t")),
        _ => parse_type_like_spec(ty, ptr_bits),
    }
}

fn inferred_signature_to_spec(
    signature: &InferredSignature,
    ptr_bits: u32,
) -> Option<FunctionSignatureSpec> {
    let ret_type = parse_signature_type_preserving_c_typedefs(&signature.ret_type, ptr_bits);
    let params = signature
        .params
        .iter()
        .map(|param| FunctionParamSpec {
            name: param.name.clone(),
            ty: parse_signature_type_preserving_c_typedefs(&param.param_type, ptr_bits),
        })
        .collect::<Vec<_>>();
    if ret_type.is_none() && params.iter().all(|param| param.ty.is_none()) {
        return None;
    }
    Some(FunctionSignatureSpec { ret_type, params })
}

pub fn inferred_signature_to_function_type_facts(
    signature: &InferredSignature,
    ptr_bits: u32,
) -> FunctionTypeFacts {
    FunctionTypeFacts {
        merged_signature: inferred_signature_to_spec(signature, ptr_bits),
        ..FunctionTypeFacts::default()
    }
}

fn merge_local_signature_into_merged_signature(
    external: Option<FunctionSignatureSpec>,
    local: Option<FunctionSignatureSpec>,
) -> Option<FunctionSignatureSpec> {
    match (external, local) {
        (None, None) => None,
        (Some(signature), None) => Some(signature),
        (None, Some(signature)) => Some(signature),
        (Some(mut external), Some(local)) => {
            let external_param_count_is_authoritative =
                signature_param_count_is_authoritative(&external);
            if local_signature_should_override_external(
                local.ret_type.as_ref(),
                external.ret_type.as_ref(),
            ) {
                external.ret_type = local.ret_type;
            } else if is_generic_signature_type(external.ret_type.as_ref()) {
                external.ret_type = local.ret_type.or(external.ret_type);
            }

            if !external_param_count_is_authoritative && external.params.len() < local.params.len()
            {
                external
                    .params
                    .resize_with(local.params.len(), || FunctionParamSpec {
                        name: String::new(),
                        ty: None,
                    });
            }

            for (idx, local_param) in local.params.into_iter().enumerate() {
                if idx >= external.params.len() {
                    continue;
                }
                let target = &mut external.params[idx];
                if target.name.is_empty() {
                    target.name = format!("arg{}", idx + 1);
                }
                if !is_generic_arg_name(&local_param.name) && is_generic_arg_name(&target.name) {
                    target.name = local_param.name.clone();
                }
                if local_param_should_override_external(
                    local_param.ty.as_ref(),
                    target.ty.as_ref(),
                    &target.name,
                ) {
                    target.ty = local_param.ty;
                } else if is_generic_signature_type(target.ty.as_ref()) {
                    target.ty = local_param.ty.or(target.ty.take());
                }
            }

            Some(external)
        }
    }
}

fn local_signature_should_override_external(
    local: Option<&CTypeLike>,
    external: Option<&CTypeLike>,
) -> bool {
    let Some(local) = local else {
        return false;
    };
    match external {
        None => true,
        Some(external) if is_generic_signature_type(Some(external)) => true,
        Some(external) => local_scalar_override_should_apply(local, external),
    }
}

fn local_param_should_override_external(
    local: Option<&CTypeLike>,
    external: Option<&CTypeLike>,
    external_name: &str,
) -> bool {
    if external.is_some() && !is_generic_arg_name(external_name) {
        return false;
    }
    local_signature_should_override_external(local, external)
}

fn local_scalar_override_should_apply(local: &CTypeLike, external: &CTypeLike) -> bool {
    match (local, external) {
        (CTypeLike::Bool, CTypeLike::Bool) => false,
        (
            CTypeLike::Bool,
            CTypeLike::Int {
                bits: external_bits,
                ..
            },
        ) => *external_bits >= 8,
        (
            CTypeLike::Int {
                bits: local_bits,
                signedness: local_signedness,
            },
            CTypeLike::Int {
                bits: external_bits,
                signedness: external_signedness,
            },
        ) => {
            *local_bits < *external_bits
                || (*local_bits == *external_bits
                    && matches!(local_signedness, Signedness::Signed)
                    && !matches!(external_signedness, Signedness::Signed))
        }
        _ => false,
    }
}

fn is_canonical_main_signature_spec(signature: &FunctionSignatureSpec) -> bool {
    signature == &canonical_main_signature_spec()
}

fn merge_recovered_arg_types_into_signature(
    mut signature: Option<FunctionSignatureSpec>,
    vars: &[RecoveredVariable],
    ptr_bits: u32,
    _function_name: &str,
) -> Option<FunctionSignatureSpec> {
    if signature
        .as_ref()
        .is_some_and(is_canonical_main_signature_spec)
    {
        return signature;
    }

    let local_arg_types = collect_recovered_arg_types(vars, ptr_bits);
    if local_arg_types.is_empty() {
        return signature;
    }

    let max_slot = local_arg_types.keys().copied().max()?;
    let sig = signature.get_or_insert_with(Default::default);
    let allow_param_count_extension = !signature_param_count_is_authoritative(sig);
    while allow_param_count_extension && sig.params.len() <= max_slot {
        let idx = sig.params.len();
        sig.params.push(FunctionParamSpec {
            name: format!("arg{}", idx + 1),
            ty: None,
        });
    }

    for (slot, local_ty) in local_arg_types {
        if slot >= sig.params.len() {
            continue;
        }
        let param = &mut sig.params[slot];
        if param.name.is_empty() {
            param.name = format!("arg{}", slot + 1);
        }
        if local_param_should_override_external(Some(&local_ty), param.ty.as_ref(), &param.name)
            || is_generic_signature_type(param.ty.as_ref())
        {
            param.ty = Some(local_ty);
        }
    }

    signature
}

fn collect_recovered_arg_types(
    vars: &[RecoveredVariable],
    ptr_bits: u32,
) -> BTreeMap<usize, CTypeLike> {
    let mut out = BTreeMap::new();
    for var in vars {
        if !var.isarg {
            continue;
        }
        let Some(slot) = var
            .name
            .strip_prefix("arg")
            .and_then(|idx| idx.parse::<usize>().ok())
        else {
            continue;
        };
        let Some(candidate) = parse_type_like_spec(&var.var_type, ptr_bits) else {
            continue;
        };
        if is_generic_signature_type(Some(&candidate)) {
            continue;
        }
        match out.get(&slot) {
            Some(current)
                if !local_signature_should_override_external(Some(&candidate), Some(current)) => {}
            _ => {
                out.insert(slot, candidate);
            }
        }
    }
    out
}

fn stack_base_for_recovered_var_kind(kind: &str) -> Option<ExternalStackBase> {
    match kind {
        "b" => Some(ExternalStackBase::FramePointer),
        "s" => Some(ExternalStackBase::StackPointer),
        _ => None,
    }
}

fn stack_slot_key_for_recovered_var(var: &RecoveredVariable) -> Option<StackSlotKey> {
    Some(StackSlotKey {
        base: stack_base_for_recovered_var_kind(&var.kind)?,
        offset: var.delta,
    })
}

fn slot_spec_for_recovered_var<'a>(
    var: &RecoveredVariable,
    stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackVarSpec>,
) -> Option<&'a ExternalStackVarSpec> {
    if let Some(slot_key) = stack_slot_key_for_recovered_var(var) {
        return stack_slots.get(&slot_key);
    }
    None
}

fn slot_role_is_hidden(role: ExternalStackSlotRole) -> bool {
    matches!(
        role,
        ExternalStackSlotRole::ParamHome
            | ExternalStackSlotRole::SavedReg
            | ExternalStackSlotRole::SavedFp
    )
}

fn slot_role_allows_external_local_identity(role: ExternalStackSlotRole) -> bool {
    matches!(
        role,
        ExternalStackSlotRole::Local
            | ExternalStackSlotRole::StackArg
            | ExternalStackSlotRole::Unknown
    )
}

fn visible_binding_kind_for_slot_role(role: ExternalStackSlotRole) -> VisibleBindingKind {
    match role {
        ExternalStackSlotRole::Local => VisibleBindingKind::Local,
        ExternalStackSlotRole::StackArg => VisibleBindingKind::Param,
        ExternalStackSlotRole::ParamHome => VisibleBindingKind::HiddenHome,
        ExternalStackSlotRole::SavedReg | ExternalStackSlotRole::SavedFp => {
            VisibleBindingKind::HiddenSaved
        }
        ExternalStackSlotRole::Unknown => VisibleBindingKind::Unknown,
    }
}

fn visible_binding_key_for_recovered_var(var: &RecoveredVariable) -> Option<VisibleBindingKey> {
    if let Some(slot_key) = stack_slot_key_for_recovered_var(var) {
        return Some(VisibleBindingKey::Stack(slot_key));
    }
    if var.isarg {
        return var
            .name
            .strip_prefix("arg")
            .and_then(|idx| idx.parse::<usize>().ok())
            .map(VisibleBindingKey::Param);
    }
    None
}

fn name_is_low_signal_binding(name: &str) -> bool {
    is_low_quality_stack_name(name) || is_generic_arg_name(name)
}

fn visible_binding_type_specificity(ty: &CTypeLike) -> u8 {
    match ty {
        CTypeLike::Unknown => 0,
        CTypeLike::Void => 1,
        CTypeLike::Function => 2,
        CTypeLike::Bool | CTypeLike::Int { .. } | CTypeLike::Float(_) => 4,
        CTypeLike::Typedef(_) | CTypeLike::Enum(_) => 5,
        CTypeLike::Struct(_) | CTypeLike::Union(_) => 6,
        CTypeLike::Array(inner, _) => 12 + visible_binding_type_specificity(inner).min(12),
        CTypeLike::Pointer(inner) => 10 + visible_binding_type_specificity(inner).min(12),
    }
}

fn candidate_visible_binding_type_is_better(
    existing: Option<&CTypeLike>,
    candidate: Option<&CTypeLike>,
) -> bool {
    match (existing, candidate) {
        (_, None) => false,
        (None | Some(CTypeLike::Unknown), Some(_)) => true,
        (Some(existing), Some(candidate)) => {
            visible_binding_type_specificity(candidate) > visible_binding_type_specificity(existing)
        }
    }
}

fn merge_visible_binding(existing: &mut VisibleBinding, candidate: VisibleBinding) {
    let VisibleBinding {
        name,
        ty,
        kind,
        stack_slot,
        param_index,
        source_reg,
    } = candidate;
    let existing_low_signal = name_is_low_signal_binding(&existing.name);
    let candidate_low_signal = name_is_low_signal_binding(&name);
    if existing.name.is_empty() || (existing_low_signal && !candidate_low_signal) {
        existing.name = name;
    }

    if candidate_visible_binding_type_is_better(existing.ty.as_ref(), ty.as_ref()) {
        existing.ty = ty;
    }

    if matches!(existing.kind, VisibleBindingKind::Unknown)
        || (matches!(existing.kind, VisibleBindingKind::Local)
            && matches!(kind, VisibleBindingKind::StackObject))
    {
        existing.kind = kind;
    }

    if existing.stack_slot.is_none() && stack_slot.is_some() {
        existing.stack_slot = stack_slot;
    }
    if existing.param_index.is_none() && param_index.is_some() {
        existing.param_index = param_index;
    }
    if existing.source_reg.is_none() && source_reg.is_some() {
        existing.source_reg = source_reg;
    }
}

fn build_visible_bindings(
    merged_signature: Option<&FunctionSignatureSpec>,
    register_params: &[crate::context::ExternalRegisterParamSpec],
    stack_slots: &BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    recovered_vars: &[RecoveredVariable],
    var_type_candidates: &[VarTypeCandidate],
    var_rename_candidates: &[VarRenameCandidate],
    ptr_bits: u32,
) -> Vec<VisibleBinding> {
    let mut bindings = BTreeMap::<VisibleBindingKey, VisibleBinding>::new();

    for (idx, param) in merged_signature
        .map(|sig| sig.params.iter().enumerate().collect::<Vec<_>>())
        .unwrap_or_default()
    {
        bindings.insert(
            VisibleBindingKey::Param(idx),
            VisibleBinding {
                name: if is_generic_arg_name(&param.name) {
                    format!("arg{}", idx + 1)
                } else {
                    param.name.clone()
                },
                ty: param.ty.clone(),
                kind: VisibleBindingKind::Param,
                stack_slot: None,
                param_index: Some(idx),
                source_reg: register_params.get(idx).map(|param| param.reg.clone()),
            },
        );
    }

    for (idx, reg_param) in register_params.iter().enumerate() {
        let candidate = VisibleBinding {
            name: if reg_param.name.is_empty() {
                format!("arg{}", idx + 1)
            } else {
                reg_param.name.clone()
            },
            ty: reg_param.ty.clone(),
            kind: VisibleBindingKind::Param,
            stack_slot: None,
            param_index: Some(idx),
            source_reg: Some(reg_param.reg.clone()),
        };
        bindings
            .entry(VisibleBindingKey::Param(idx))
            .and_modify(|existing| merge_visible_binding(existing, candidate.clone()))
            .or_insert(candidate);
    }

    let rename_map = var_rename_candidates
        .iter()
        .map(|candidate| (candidate.name.as_str(), candidate.target_name.clone()))
        .collect::<HashMap<_, _>>();
    let mut type_map = BTreeMap::<RecoveredVarKey, CTypeLike>::new();
    for candidate in var_type_candidates {
        let Some(ty) = parse_type_like_spec(&candidate.var_type, ptr_bits) else {
            continue;
        };
        let key = RecoveredVarKey::for_type_candidate(candidate);
        type_map
            .entry(key)
            .and_modify(|existing| {
                if candidate_visible_binding_type_is_better(Some(existing), Some(&ty)) {
                    *existing = ty.clone();
                }
            })
            .or_insert(ty);
    }

    for (slot_key, slot_spec) in stack_slots {
        let key = slot_spec
            .param_index
            .filter(|_| matches!(slot_spec.role, ExternalStackSlotRole::StackArg))
            .map(VisibleBindingKey::Param)
            .unwrap_or_else(|| VisibleBindingKey::Stack(slot_key.clone()));
        let candidate = VisibleBinding {
            name: slot_spec
                .param_name
                .as_ref()
                .filter(|_| matches!(slot_spec.role, ExternalStackSlotRole::StackArg))
                .cloned()
                .or_else(|| (!slot_spec.name.is_empty()).then(|| slot_spec.name.clone()))
                .unwrap_or_else(|| match key {
                    VisibleBindingKey::Param(idx) => format!("arg{}", idx + 1),
                    VisibleBindingKey::Stack(_) => "local".to_string(),
                }),
            ty: slot_spec.ty.clone(),
            kind: visible_binding_kind_for_slot_role(slot_spec.role),
            stack_slot: Some(slot_key.clone()),
            param_index: slot_spec.param_index,
            source_reg: slot_spec.source_reg.clone(),
        };
        bindings
            .entry(key)
            .and_modify(|existing| merge_visible_binding(existing, candidate.clone()))
            .or_insert(candidate);
    }

    for var in recovered_vars {
        let Some(key) = visible_binding_key_for_recovered_var(var) else {
            continue;
        };
        let candidate_name = rename_map
            .get(var.name.as_str())
            .cloned()
            .unwrap_or_else(|| var.name.clone());
        let candidate = VisibleBinding {
            name: sanitize_c_identifier(&candidate_name).unwrap_or(candidate_name),
            ty: type_map
                .get(&RecoveredVarKey::for_recovered_var(var))
                .cloned()
                .or_else(|| parse_type_like_spec(&var.var_type, ptr_bits)),
            kind: if var.isarg {
                VisibleBindingKind::Param
            } else if matches!(key, VisibleBindingKey::Stack(_)) {
                VisibleBindingKind::Local
            } else {
                VisibleBindingKind::Unknown
            },
            stack_slot: match &key {
                VisibleBindingKey::Stack(slot_key) => Some(slot_key.clone()),
                VisibleBindingKey::Param(_) => None,
            },
            param_index: match key {
                VisibleBindingKey::Param(idx) => Some(idx),
                VisibleBindingKey::Stack(_) => None,
            },
            source_reg: var.reg.clone(),
        };
        bindings
            .entry(key)
            .and_modify(|existing| merge_visible_binding(existing, candidate.clone()))
            .or_insert(candidate);
    }

    bindings.into_values().collect()
}

fn build_var_type_candidates(
    vars: &[RecoveredVariable],
    ctx: &VarTypeCandidateContext<'_>,
    diagnostics: &mut TypeWritebackDiagnostics,
) -> Vec<VarTypeCandidate> {
    let mut out = Vec::with_capacity(vars.len());
    for var in vars {
        let slot_spec = slot_spec_for_recovered_var(var, ctx.stack_slots);
        if slot_spec.is_some_and(|spec| slot_role_is_hidden(spec.role)) {
            continue;
        }

        let mut source = WritebackSource::LocalInferred;
        let mut confidence = if var.var_type.contains('*') {
            92
        } else if var.isarg {
            88
        } else {
            84
        };
        let mut evidence = vec![WritebackEvidence::SsaVarRecovery];
        let mut chosen_type = var.var_type.clone();
        let arg_slot = var
            .name
            .strip_prefix("arg")
            .and_then(|idx| idx.parse::<usize>().ok());

        if let Some(slot) = arg_slot
            && let Some(sig_ty) = ctx.current_context_maps.param_types.get(&slot)
            && !is_generic_type_string(sig_ty)
        {
            chosen_type = sig_ty.clone();
            confidence = 96;
            source = WritebackSource::SignatureRegistry;
            evidence.push(WritebackEvidence::ExternalSignatureCurrent);
        } else if let Some(slot) = arg_slot
            && let Some(sig_ty) = ctx
                .merged_signature
                .and_then(|sig| sig.params.get(slot))
                .and_then(|param| param.ty.as_ref())
                .map(|ty| render_signature_type(ty, ctx.ptr_bits))
            && !is_generic_type_string(&sig_ty)
        {
            chosen_type = sig_ty;
            confidence = 96;
            source = WritebackSource::SignatureRegistry;
            if ctx.is_main_signature {
                evidence.push(WritebackEvidence::CanonicalMainSignature);
            } else {
                evidence.push(WritebackEvidence::ExternalSignatureCurrent);
            }
        } else if let Some(slot) = arg_slot
            && let Some(struct_ty) = ctx.slot_type_overrides.get(&slot)
            && is_generic_type_string(&chosen_type)
        {
            chosen_type = struct_ty.clone();
            confidence = 90;
            source = WritebackSource::LocalInferred;
            evidence.push(WritebackEvidence::SsaFieldOffsetPattern);
        }

        if let Some(existing_ty) = ctx.existing_types.get(&var.name)
            && !is_generic_type_string(existing_ty)
        {
            if is_generic_type_string(&chosen_type) {
                chosen_type = existing_ty.clone();
                confidence = 98;
                source = WritebackSource::ExistingState;
                evidence.push(WritebackEvidence::ExistingStackType);
            } else if !existing_ty.eq_ignore_ascii_case(&chosen_type) {
                diagnostics.conflicts.push(format!(
                    "var `{}` existing type `{}` conflicts with inferred `{}`",
                    var.name, existing_ty, chosen_type
                ));
            }
        }

        if let Some(ext) = slot_spec
            && let Some(ext_ty) = ext.ty.as_ref()
            && slot_role_allows_external_local_identity(ext.role)
        {
            let ext_ty_str = render_signature_type(ext_ty, ctx.ptr_bits);
            let external_should_override = !is_generic_type_string(&ext_ty_str)
                && (is_generic_type_string(&chosen_type)
                    || (matches!(source, WritebackSource::LocalInferred)
                        && is_low_signal_storage_scalar_type(&chosen_type, ctx.ptr_bits)));
            if external_should_override {
                chosen_type = ext_ty_str;
                confidence = 97;
                source = WritebackSource::ExternalTypeDb;
                evidence.push(WritebackEvidence::ExternalStackAnnotation);
            }
        }

        let chosen_type = normalize_external_type_name(&chosen_type);
        out.push(VarTypeCandidate {
            name: var.name.clone(),
            kind: var.kind.clone(),
            delta: var.delta,
            var_type: chosen_type.clone(),
            isarg: var.isarg,
            reg: var.reg.clone(),
            size: estimate_c_type_size_bytes(&chosen_type, ctx.ptr_bits) as u32,
            confidence,
            source,
            evidence,
        });
    }
    out
}

fn build_var_rename_candidates(
    vars: &[RecoveredVariable],
    param_names: &HashMap<usize, String>,
    stack_slots: &BTreeMap<StackSlotKey, ExternalStackVarSpec>,
) -> Vec<VarRenameCandidate> {
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();

    for var in vars {
        let slot_spec = slot_spec_for_recovered_var(var, stack_slots);

        if let Some(ext) = slot_spec
            && ext.name != var.name
            && is_low_quality_stack_name(&var.name)
            && !is_low_quality_stack_name(&ext.name)
            && slot_role_allows_external_local_identity(ext.role)
        {
            let target_name = sanitize_c_identifier(&ext.name).unwrap_or_else(|| ext.name.clone());
            let edge = format!("{}->{target_name}", var.name);
            if !target_name.is_empty() && target_name != var.name && seen.insert(edge) {
                out.push(VarRenameCandidate {
                    name: var.name.clone(),
                    target_name,
                    confidence: 94,
                    source: WritebackSource::ExternalTypeDb,
                    evidence: vec![WritebackEvidence::ExternalStackName],
                });
            }
        }

        if let Some(ext) = slot_spec
            && matches!(ext.role, ExternalStackSlotRole::StackArg)
            && let Some(param_name) = ext.param_name.as_ref()
            && is_low_quality_stack_name(&var.name)
        {
            let target_name =
                sanitize_c_identifier(param_name).unwrap_or_else(|| param_name.clone());
            let edge = format!("{}->{target_name}", var.name);
            if !target_name.is_empty() && target_name != var.name && seen.insert(edge) {
                out.push(VarRenameCandidate {
                    name: var.name.clone(),
                    target_name,
                    confidence: 95,
                    source: WritebackSource::SignatureRegistry,
                    evidence: vec![WritebackEvidence::ExternalParamName],
                });
            }
        }

        let arg_slot = var
            .name
            .strip_prefix("arg")
            .and_then(|idx| idx.parse::<usize>().ok());
        if let Some(slot) = arg_slot
            && let Some(param_name) = param_names.get(&slot)
            && is_generic_arg_name(&var.name)
        {
            let target_name =
                sanitize_c_identifier(param_name).unwrap_or_else(|| param_name.clone());
            let edge = format!("{}->{target_name}", var.name);
            if !target_name.is_empty() && target_name != var.name && seen.insert(edge) {
                out.push(VarRenameCandidate {
                    name: var.name.clone(),
                    target_name,
                    confidence: 95,
                    source: WritebackSource::SignatureRegistry,
                    evidence: vec![WritebackEvidence::ExternalParamName],
                });
            }
        }
    }

    out
}

fn signature_context_maps(
    signature: Option<&FunctionSignatureSpec>,
    ptr_bits: u32,
) -> SignatureContextMaps {
    let mut maps = SignatureContextMaps::default();
    let Some(signature) = signature else {
        return maps;
    };
    for (idx, param) in signature.params.iter().enumerate() {
        if let Some(ty) = param.ty.as_ref() {
            let ty_str = render_signature_type(ty, ptr_bits);
            if !is_generic_type_string(&ty_str)
                || param_has_authoritative_named_scalar_role(param, ptr_bits)
            {
                maps.param_types.insert(idx, ty_str);
            }
        }
        if !is_generic_arg_name(&param.name) {
            maps.param_names.insert(idx, param.name.clone());
        }
    }
    maps
}

fn apply_signature_context_overrides(
    signature_out: &mut InferredSignature,
    signature: Option<&FunctionSignatureSpec>,
    ptr_bits: u32,
) {
    let Some(signature) = signature else {
        return;
    };

    let authoritative_param_count = signature_param_count_is_authoritative(signature)
        || crate::signature_projection_is_exact(signature);
    if authoritative_param_count && signature_out.params.len() > signature.params.len() {
        signature_out.params.truncate(signature.params.len());
    }

    while signature_out.params.len() < signature.params.len() {
        let idx = signature_out.params.len();
        let param_type = signature
            .params
            .get(idx)
            .and_then(|param| param.ty.as_ref())
            .map(|ty| render_signature_type(ty, ptr_bits))
            .unwrap_or_else(|| "void *".to_string());
        signature_out.params.push(InferredSignatureParam {
            name: format!("arg{}", idx + 1),
            param_type,
        });
    }

    if let Some(ret_ty) = signature.ret_type.as_ref() {
        let ret_ty = render_signature_type(ret_ty, ptr_bits);
        if !is_generic_signature_type(signature.ret_type.as_ref()) {
            signature_out.ret_type = ret_ty;
        }
    }

    for (idx, param) in signature.params.iter().enumerate() {
        if let Some(ty) = param.ty.as_ref() {
            let ty_str = render_signature_type(ty, ptr_bits);
            if (!is_generic_type_string(&ty_str)
                || param_has_authoritative_named_scalar_role(param, ptr_bits))
                && let Some(inferred_param) = signature_out.params.get_mut(idx)
            {
                inferred_param.param_type = ty_str;
            }
        }
        if !is_generic_arg_name(&param.name)
            && let Some(inferred_param) = signature_out.params.get_mut(idx)
        {
            inferred_param.name = param.name.clone();
        }
    }

    signature_out.signature = format_signature(
        &signature_out.function_name,
        &signature_out.ret_type,
        &signature_out.params,
    );
    signature_out.confidence = signature_out.confidence.max(signature_strength(signature));
}

fn signature_strength(signature: &FunctionSignatureSpec) -> u8 {
    crate::signature_strength(signature)
}

fn signature_param_count_is_authoritative(signature: &FunctionSignatureSpec) -> bool {
    crate::signature_param_count_is_authoritative(signature)
}

fn is_generic_signature_type(ty: Option<&CTypeLike>) -> bool {
    crate::is_generic_signature_type(ty)
}

fn signature_param_allows_local_struct_override(
    param: Option<&FunctionParamSpec>,
    ptr_bits: u32,
) -> bool {
    let Some(param) = param else {
        return true;
    };

    if is_generic_signature_type(param.ty.as_ref()) {
        return true;
    }

    if matches!(
        param.ty.as_ref(),
        Some(CTypeLike::Pointer(inner)) if matches!(inner.as_ref(), CTypeLike::Typedef(_))
    ) {
        return false;
    }

    is_generic_arg_name(&param.name)
        && matches!(
            param.ty.as_ref(),
            Some(CTypeLike::Int { bits, .. }) if *bits == ptr_bits
        )
}

fn merge_slot_type_overrides_into_signature(
    mut signature: Option<FunctionSignatureSpec>,
    slot_type_overrides: &HashMap<usize, String>,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
    preserve_param_count: bool,
) -> Option<FunctionSignatureSpec> {
    if slot_type_overrides.is_empty() {
        return signature;
    }

    let max_slot = slot_type_overrides.keys().copied().max()?;
    let sig = signature.get_or_insert_with(Default::default);
    let allow_param_count_extension =
        !preserve_param_count && !signature_param_count_is_authoritative(sig);
    while allow_param_count_extension && sig.params.len() <= max_slot {
        let idx = sig.params.len();
        sig.params.push(FunctionParamSpec {
            name: format!("arg{}", idx + 1),
            ty: None,
        });
    }

    for (slot, raw_ty) in slot_type_overrides {
        if *slot >= sig.params.len() {
            continue;
        }
        let Some(parsed) = parse_type_like_spec(raw_ty, ptr_bits) else {
            continue;
        };
        let param = &mut sig.params[*slot];
        if !signature_param_blocks_generated_local_struct_override(
            Some(param),
            raw_ty,
            type_db,
            ptr_bits,
        ) && signature_param_allows_local_struct_override(Some(param), ptr_bits)
        {
            param.ty = Some(parsed);
        }
    }

    signature
}

fn override_type_is_generated_local_struct(raw_ty: &str, ptr_bits: u32) -> bool {
    generated_local_struct_name_from_override(raw_ty, ptr_bits).is_some()
}

fn generated_local_struct_name_from_override(raw_ty: &str, ptr_bits: u32) -> Option<String> {
    if let Some(name) = parse_struct_ptr_type_name(raw_ty)
        && is_generated_local_struct_name(&name)
    {
        return Some(name);
    }
    let Some(CTypeLike::Pointer(inner)) = parse_type_like_spec(raw_ty, ptr_bits) else {
        return None;
    };
    match inner.as_ref() {
        CTypeLike::Struct(name) | CTypeLike::Typedef(name)
            if is_generated_local_struct_name(name) =>
        {
            Some(name.clone())
        }
        _ => None,
    }
}

fn external_named_aggregate_has_real_layout(type_db: &ExternalTypeDb, name: &str) -> bool {
    let mut keys = aggregate_lookup_keys_for_writeback(name);
    let mut seen = BTreeSet::new();
    for _ in 0..16 {
        for key in &keys {
            if type_db
                .structs
                .get(key)
                .is_some_and(|st| !st.fields.is_empty())
            {
                return true;
            }
            if type_db
                .unions
                .get(key)
                .is_some_and(|un| !un.fields.is_empty())
            {
                return true;
            }
            if type_db
                .enums
                .get(key)
                .is_some_and(|en| !en.variants.is_empty())
            {
                return true;
            }
        }

        let Some(typedef) = keys.iter().find_map(|key| type_db.typedefs.get(key)) else {
            return false;
        };
        let typedef_key = typedef.name.to_ascii_lowercase();
        if !seen.insert(typedef_key) {
            return false;
        }
        keys = aggregate_lookup_keys_for_writeback(&typedef.target);
    }
    false
}

fn unresolved_named_struct_target_for_param(
    param: &FunctionParamSpec,
    type_db: &ExternalTypeDb,
) -> Option<String> {
    let Some(CTypeLike::Pointer(inner)) = param.ty.as_ref() else {
        return None;
    };
    match inner.as_ref() {
        CTypeLike::Struct(name) => unresolved_named_struct_target(name, type_db),
        CTypeLike::Typedef(name) if !semantic_role_typedef_is_authoritative(name) => {
            unresolved_named_struct_target(name, type_db)
        }
        _ => None,
    }
}

fn unresolved_named_struct_target(name: &str, type_db: &ExternalTypeDb) -> Option<String> {
    let name = canonical_struct_decl_name(name);
    if name.is_empty()
        || is_generated_local_struct_name(&name)
        || external_named_aggregate_has_real_layout(type_db, &name)
    {
        return None;
    }
    Some(name)
}

fn canonical_struct_decl_name(name: &str) -> String {
    let trimmed = name.trim();
    for prefix in ["struct ", "union ", "enum "] {
        if let Some(rest) = trimmed.strip_prefix(prefix) {
            return rest.trim().to_string();
        }
    }
    trimmed.to_string()
}

fn merge_or_insert_local_struct_decl(
    struct_decls: &mut Vec<StructDeclCandidate>,
    incoming: StructDeclCandidate,
    ptr_bits: u32,
) {
    let Some(existing) = struct_decls
        .iter_mut()
        .find(|decl| decl.name.eq_ignore_ascii_case(&incoming.name))
    else {
        struct_decls.push(incoming);
        return;
    };

    let mut fields = existing
        .fields
        .iter()
        .cloned()
        .map(|field| (field.offset, field))
        .collect::<BTreeMap<_, _>>();
    for field in incoming.fields {
        fields.entry(field.offset).or_insert(field);
    }
    existing.fields = fields.into_values().collect();
    existing.confidence = existing.confidence.max(incoming.confidence);
    existing.source = StructDeclSource::LocalInferred;
    if let Some(decl) = build_struct_decl(&existing.name, &existing.fields, ptr_bits) {
        existing.decl = decl;
    }
}

fn materialize_unresolved_signature_struct_layouts(
    merged_signature: Option<&FunctionSignatureSpec>,
    struct_decls: &mut Vec<StructDeclCandidate>,
    slot_type_overrides: &mut HashMap<usize, String>,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
) {
    let Some(signature) = merged_signature else {
        return;
    };

    let mut slots = slot_type_overrides.keys().copied().collect::<Vec<_>>();
    slots.sort_unstable();
    for slot in slots {
        let Some(raw_ty) = slot_type_overrides.get(&slot) else {
            continue;
        };
        let Some(local_name) = generated_local_struct_name_from_override(raw_ty, ptr_bits) else {
            continue;
        };
        let Some(param) = signature.params.get(slot) else {
            continue;
        };
        let Some(target_name) = unresolved_named_struct_target_for_param(param, type_db) else {
            continue;
        };
        let Some(local_decl) = struct_decls
            .iter()
            .find(|decl| {
                decl.source == StructDeclSource::LocalInferred
                    && decl.name.eq_ignore_ascii_case(&local_name)
            })
            .cloned()
        else {
            continue;
        };
        let Some(decl) = build_struct_decl(&target_name, &local_decl.fields, ptr_bits) else {
            continue;
        };
        merge_or_insert_local_struct_decl(
            struct_decls,
            StructDeclCandidate {
                name: target_name.clone(),
                decl,
                confidence: local_decl.confidence,
                source: StructDeclSource::LocalInferred,
                fields: local_decl.fields,
            },
            ptr_bits,
        );
        slot_type_overrides.insert(slot, format!("struct {target_name} *"));
    }
}

fn signature_param_blocks_generated_local_struct_override(
    param: Option<&FunctionParamSpec>,
    raw_ty: &str,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
) -> bool {
    if !override_type_is_generated_local_struct(raw_ty, ptr_bits) {
        return false;
    }
    let Some(param) = param else {
        return false;
    };
    if is_generic_signature_type(param.ty.as_ref()) {
        return false;
    }
    let Some(ty) = param.ty.as_ref() else {
        return false;
    };
    match ty {
        CTypeLike::Pointer(inner) => match inner.as_ref() {
            CTypeLike::Unknown | CTypeLike::Void => false,
            CTypeLike::Struct(name) => external_named_aggregate_has_real_layout(type_db, name),
            CTypeLike::Typedef(name) => {
                semantic_role_typedef_is_authoritative(name)
                    || external_named_aggregate_has_real_layout(type_db, name)
            }
            CTypeLike::Union(_) | CTypeLike::Enum(_) => true,
            _ => true,
        },
        CTypeLike::Int { bits, .. } if *bits == ptr_bits && is_generic_arg_name(&param.name) => {
            false
        }
        _ => true,
    }
}

fn signature_param_blocks_local_struct_override(
    signature: &Option<FunctionSignatureSpec>,
    slot: usize,
    raw_ty: &str,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
) -> bool {
    signature_param_blocks_generated_local_struct_override(
        signature.as_ref().and_then(|sig| sig.params.get(slot)),
        raw_ty,
        type_db,
        ptr_bits,
    )
}

fn prune_conflicting_local_struct_overrides(
    merged_signature: &Option<FunctionSignatureSpec>,
    struct_decls: &mut Vec<StructDeclCandidate>,
    slot_type_overrides: &mut HashMap<usize, String>,
    slot_field_profiles: &mut HashMap<usize, BTreeMap<u64, String>>,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
) {
    let blocked_slots = slot_type_overrides
        .iter()
        .filter_map(|(slot, raw_ty)| {
            signature_param_blocks_local_struct_override(
                merged_signature,
                *slot,
                raw_ty,
                type_db,
                ptr_bits,
            )
            .then_some(*slot)
        })
        .collect::<Vec<_>>();
    if blocked_slots.is_empty() {
        return;
    }

    for slot in &blocked_slots {
        slot_type_overrides.remove(slot);
        slot_field_profiles.remove(slot);
    }

    let referenced_local_names = slot_type_overrides
        .values()
        .filter_map(|ty| ty.trim().strip_prefix("struct "))
        .filter_map(|rest| rest.trim_end().strip_suffix(" *"))
        .map(|name| name.to_ascii_lowercase())
        .collect::<HashSet<_>>();

    struct_decls.retain(|decl| {
        decl.source != StructDeclSource::LocalInferred
            || referenced_local_names.contains(&decl.name.to_ascii_lowercase())
    });
}

fn collect_external_struct_candidates_from_db(
    db: &ExternalTypeDb,
    ptr_bits: u32,
) -> Vec<StructDeclCandidate> {
    let mut keys: Vec<String> = db.structs.keys().cloned().collect();
    keys.sort();

    let mut out = Vec::new();
    for key in keys {
        let Some(st) = db.structs.get(&key) else {
            continue;
        };
        if is_opaque_placeholder_type_name(&st.name)
            || st.fields.is_empty()
            || db.is_aggregate_typedef(&st.name)
        {
            continue;
        }
        let mut fields = Vec::new();
        for (offset, field) in &st.fields {
            let raw_ty = field.ty.clone().unwrap_or_else(|| "uint8_t".to_string());
            fields.push(StructFieldCandidate {
                name: field.name.clone(),
                offset: *offset,
                field_type: normalize_external_type_name(&raw_ty),
                confidence: 95,
            });
        }
        let Some(decl) = build_struct_decl(&st.name, &fields, ptr_bits) else {
            continue;
        };
        out.push(StructDeclCandidate {
            name: st.name.clone(),
            decl,
            confidence: 95,
            source: StructDeclSource::ExternalTypeDb,
            fields,
        });
    }
    out
}

fn merge_local_structs_into_type_db(db: &mut ExternalTypeDb, struct_decls: &[StructDeclCandidate]) {
    for decl in struct_decls {
        let key = decl.name.to_ascii_lowercase();
        let mut fields = BTreeMap::new();
        for field in &decl.fields {
            fields.insert(
                field.offset,
                ExternalField {
                    name: field.name.clone(),
                    offset: field.offset,
                    ty: Some(field.field_type.clone()),
                },
            );
        }
        let candidate = ExternalStruct {
            name: decl.name.clone(),
            fields,
        };
        match db.structs.entry(key) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(candidate);
            }
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                if decl.source == StructDeclSource::LocalInferred
                    && (is_generated_local_struct_name(&decl.name) || entry.get().fields.is_empty())
                {
                    entry.insert(candidate);
                }
            }
        }
    }
}

fn dedup_struct_decls(mut decls: Vec<StructDeclCandidate>) -> Vec<StructDeclCandidate> {
    decls.sort_by(|a, b| {
        a.name
            .to_ascii_lowercase()
            .cmp(&b.name.to_ascii_lowercase())
    });
    let mut merged: Vec<StructDeclCandidate> = Vec::new();
    for decl in decls {
        if let Some(existing) = merged
            .iter_mut()
            .find(|existing| existing.name.eq_ignore_ascii_case(&decl.name))
        {
            if should_replace_struct_decl(existing, &decl) {
                *existing = decl;
            }
        } else {
            merged.push(decl);
        }
    }
    merged
}

fn should_replace_struct_decl(
    existing: &StructDeclCandidate,
    candidate: &StructDeclCandidate,
) -> bool {
    candidate.source == StructDeclSource::LocalInferred
        && is_generated_local_struct_name(&candidate.name)
        && existing.name.eq_ignore_ascii_case(&candidate.name)
}

fn canonical_field_type_key(ty: &str, ptr_bits: u32) -> String {
    let normalized = normalize_external_type_name(ty);
    parse_type_like_spec(&normalized, ptr_bits)
        .map(|parsed| render_signature_type(&parsed, ptr_bits).to_ascii_lowercase())
        .unwrap_or_else(|| normalized.to_ascii_lowercase())
}

fn struct_fields_signature(fields: &[StructFieldCandidate], ptr_bits: u32) -> Vec<(u64, String)> {
    let mut out: Vec<(u64, String)> = fields
        .iter()
        .map(|f| (f.offset, canonical_field_type_key(&f.field_type, ptr_bits)))
        .collect();
    out.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    out
}

fn parse_struct_ptr_type_name(ty: &str) -> Option<String> {
    ty.trim()
        .strip_prefix("struct ")
        .and_then(|rest| rest.strip_suffix(" *"))
        .map(str::to_string)
}

fn local_struct_profile_score(
    decl: &StructDeclCandidate,
    profile: &BTreeMap<u64, String>,
    ptr_bits: u32,
) -> Option<(usize, usize, usize, i32)> {
    if decl.source != StructDeclSource::LocalInferred || profile.is_empty() {
        return None;
    }

    let field_map = decl
        .fields
        .iter()
        .map(|field| {
            (
                field.offset,
                canonical_field_type_key(&field.field_type, ptr_bits),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let mut offset_matches = 0usize;
    let mut typed_matches = 0usize;
    for (offset, ty) in profile {
        let Some(field_ty) = field_map.get(offset) else {
            continue;
        };
        offset_matches += 1;
        if field_ty == &canonical_field_type_key(ty, ptr_bits) {
            typed_matches += 1;
        }
    }

    (offset_matches > 0).then_some((
        offset_matches,
        typed_matches,
        decl.fields.len(),
        i32::from(decl.confidence),
    ))
}

fn prefer_stronger_local_struct_overrides(
    struct_decls: &[StructDeclCandidate],
    slot_type_overrides: &mut HashMap<usize, String>,
    slot_field_profiles: &HashMap<usize, BTreeMap<u64, String>>,
    ptr_bits: u32,
) {
    for (slot, ty) in slot_type_overrides.iter_mut() {
        let Some(profile) = slot_field_profiles.get(slot) else {
            continue;
        };
        if profile.is_empty() {
            continue;
        }

        let current_name = parse_struct_ptr_type_name(ty);
        let current_decl = current_name.as_ref().and_then(|name| {
            struct_decls
                .iter()
                .find(|decl| decl.name.eq_ignore_ascii_case(name))
        });
        if current_decl.is_some_and(|decl| decl.source == StructDeclSource::ExternalTypeDb)
            || current_name.is_some() && current_decl.is_none()
        {
            continue;
        }

        let current_score =
            current_decl.and_then(|decl| local_struct_profile_score(decl, profile, ptr_bits));
        let best_local = struct_decls
            .iter()
            .filter_map(|decl| {
                local_struct_profile_score(decl, profile, ptr_bits)
                    .map(|score| (score, decl.name.clone()))
            })
            .max_by(|(left_score, left_name), (right_score, right_name)| {
                left_score
                    .cmp(right_score)
                    .then_with(|| left_name.cmp(right_name))
            });

        let Some((best_score, best_name)) = best_local else {
            continue;
        };
        if current_score.is_none_or(|score| best_score > score) {
            *ty = format!("struct {} *", best_name);
        }
    }
}

fn structurally_compatible(local_fields: &[(u64, String)], ext_fields: &[(u64, String)]) -> bool {
    if local_fields.is_empty() || ext_fields.is_empty() {
        return false;
    }
    let mut matches = 0usize;
    for (off, ty) in local_fields {
        if ext_fields
            .iter()
            .any(|(eoff, ety)| eoff == off && ety == ty)
        {
            matches += 1;
        }
    }
    matches >= local_fields.len().min(2)
}

fn align_local_structs_with_external(
    struct_decls: &mut [StructDeclCandidate],
    slot_type_overrides: &mut HashMap<usize, String>,
    slot_field_profiles: &HashMap<usize, BTreeMap<u64, String>>,
    external_structs: &[StructDeclCandidate],
    ptr_bits: u32,
) {
    let mut local_to_external: HashMap<String, String> = HashMap::new();
    for local in struct_decls.iter_mut() {
        if local.source != StructDeclSource::LocalInferred {
            continue;
        }
        let local_sig = struct_fields_signature(&local.fields, ptr_bits);
        for ext in external_structs {
            let ext_sig = struct_fields_signature(&ext.fields, ptr_bits);
            if structurally_compatible(&local_sig, &ext_sig) {
                local_to_external.insert(local.name.clone(), ext.name.clone());
                local.confidence = local.confidence.max(92);
                break;
            }
        }
    }

    for (slot, ty) in slot_type_overrides.iter_mut() {
        let Some(profile) = slot_field_profiles.get(slot) else {
            continue;
        };
        if profile.is_empty() {
            continue;
        }
        let replacement = external_structs.iter().find_map(|ext| {
            let ext_sig = struct_fields_signature(&ext.fields, ptr_bits);
            let local_sig: Vec<(u64, String)> = profile
                .iter()
                .map(|(off, ty)| (*off, canonical_field_type_key(ty, ptr_bits)))
                .collect();
            if structurally_compatible(&local_sig, &ext_sig) {
                Some(ext.name.clone())
            } else {
                None
            }
        });
        if let Some(ext_name) = replacement {
            *ty = format!("struct {} *", ext_name);
            continue;
        }
        if let Some(local_name) = ty
            .strip_prefix("struct ")
            .and_then(|s| s.strip_suffix(" *"))
            .map(str::to_string)
            && let Some(ext_name) = local_to_external.get(&local_name)
        {
            *ty = format!("struct {} *", ext_name);
        }
    }
}

fn score_global_type_links(
    ssa_blocks: &[SSABlock],
    struct_decls: &[StructDeclCandidate],
    var_type_candidates: &[VarTypeCandidate],
    ptr_bits: u32,
) -> Vec<GlobalTypeLinkCandidate> {
    let per_addr_profiles = infer_global_field_profiles(ssa_blocks, ptr_bits);
    if per_addr_profiles.is_empty() {
        return Vec::new();
    }

    let mut per_type_weight: BTreeMap<String, i32> = BTreeMap::new();
    let mut decl_profiles: BTreeMap<String, BTreeMap<u64, String>> = BTreeMap::new();
    for decl in struct_decls {
        let key = format!("struct {} *", decl.name);
        if is_generic_type_string(&key) {
            continue;
        }
        let source_boost = if decl.source == StructDeclSource::ExternalTypeDb {
            12
        } else {
            0
        };
        per_type_weight.insert(
            key.clone(),
            32 + source_boost + (decl.confidence as i32 / 6) + (decl.fields.len() as i32).min(16),
        );
        decl_profiles.insert(
            key,
            decl.fields
                .iter()
                .map(|field| {
                    (
                        field.offset,
                        normalize_external_type_name(&field.field_type).to_ascii_lowercase(),
                    )
                })
                .collect(),
        );
    }
    for var in var_type_candidates {
        if var.var_type.starts_with("struct ")
            && var.var_type.ends_with(" *")
            && !is_generic_type_string(&var.var_type)
        {
            *per_type_weight.entry(var.var_type.clone()).or_insert(30) +=
                4 + (var.confidence as i32 / 12);
        }
    }
    if per_type_weight.is_empty() {
        return Vec::new();
    }

    let mut per_addr_best: BTreeMap<u64, (String, i32)> = BTreeMap::new();
    for (addr, profile) in per_addr_profiles {
        if profile.is_empty() {
            continue;
        }
        let observed_fields = profile.len();
        let mut best: Option<(String, i32)> = None;
        for (ty, base_score) in &per_type_weight {
            let Some(decl_profile) = decl_profiles.get(ty) else {
                continue;
            };
            if observed_fields == 1 && decl_profile.len() > 1 {
                continue;
            }

            let mut exact_matches = 0i32;
            let mut declared_offsets = 0i32;
            let mut evidence_weight = 0i32;
            for (offset, evidence) in &profile {
                let Some(decl_ty) = decl_profile.get(offset) else {
                    continue;
                };
                declared_offsets += 1;
                if decl_ty
                    == &normalize_external_type_name(&evidence.field_type).to_ascii_lowercase()
                {
                    exact_matches += 1;
                    evidence_weight +=
                        1 + evidence.reads.min(4) as i32 + evidence.writes.min(4) as i32;
                }
            }
            if exact_matches == 0 {
                continue;
            }
            if observed_fields > 1 && exact_matches < observed_fields.min(2) as i32 {
                continue;
            }

            let score =
                *base_score + exact_matches * 18 + declared_offsets * 6 + evidence_weight.min(18);
            match best {
                Some((ref prev_ty, prev_score))
                    if prev_score > score || (prev_score == score && prev_ty <= ty) => {}
                _ => best = Some((ty.clone(), score)),
            }
        }
        if let Some(candidate) = best {
            per_addr_best.insert(addr, candidate);
        }
    }

    per_addr_best
        .into_iter()
        .map(|(addr, (target_type, score))| GlobalTypeLinkCandidate {
            addr,
            target_type,
            confidence: score.clamp(1, 99) as u8,
            source: WritebackSource::DataflowRanked,
        })
        .collect()
}

fn infer_global_field_profiles(
    ssa_blocks: &[SSABlock],
    ptr_bits: u32,
) -> BTreeMap<u64, BTreeMap<u64, InferredGlobalFieldEvidence>> {
    let mut addr_exprs: HashMap<String, GlobalAddrExpr> = HashMap::new();
    let mut field_evidence: BTreeMap<u64, BTreeMap<u64, InferredGlobalFieldEvidence>> =
        BTreeMap::new();
    let offset_bound = 0x4000i64;

    for _ in 0..6 {
        let mut changed = false;
        for block in ssa_blocks {
            for op in &block.ops {
                let addr_of = |var: &SSAVar, map: &HashMap<String, GlobalAddrExpr>| {
                    parse_const_value(&var.name)
                        .filter(|base| *base >= 0x10000)
                        .map(|base| GlobalAddrExpr {
                            base,
                            offset: 0,
                            confidence: 92,
                        })
                        .or_else(|| map.get(&ssa_var_block_key(block.addr, var)).copied())
                };
                let set_expr =
                    |dst: &SSAVar,
                     expr: GlobalAddrExpr,
                     map: &mut HashMap<String, GlobalAddrExpr>| {
                        let key = ssa_var_block_key(block.addr, dst);
                        match map.get(&key).copied() {
                            Some(prev) if prev.confidence >= expr.confidence => false,
                            _ => {
                                map.insert(key, expr);
                                true
                            }
                        }
                    };
                match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::Cast { dst, src }
                    | SSAOp::New { dst, src }
                    | SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src } => {
                        if let Some(mut expr) = addr_of(src, &addr_exprs) {
                            expr.confidence = expr.confidence.saturating_sub(2);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    SSAOp::Phi { dst, sources } => {
                        let mut selected = None;
                        for src in sources {
                            let Some(expr) = addr_of(src, &addr_exprs) else {
                                selected = None;
                                break;
                            };
                            selected = match selected {
                                None => Some(expr),
                                Some(prev)
                                    if prev.base == expr.base && prev.offset == expr.offset =>
                                {
                                    Some(GlobalAddrExpr {
                                        base: prev.base,
                                        offset: prev.offset,
                                        confidence: prev.confidence.max(expr.confidence),
                                    })
                                }
                                _ => None,
                            };
                            if selected.is_none() {
                                break;
                            }
                        }
                        if let Some(mut expr) = selected {
                            expr.confidence = expr.confidence.saturating_sub(3);
                            changed |= set_expr(dst, expr, &mut addr_exprs);
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } => {
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(raw) = parse_const_value(&b.name)
                        {
                            let off = base
                                .offset
                                .saturating_add(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        } else if let Some(base) = addr_of(b, &addr_exprs)
                            && let Some(raw) = parse_const_value(&a.name)
                        {
                            let off = base
                                .offset
                                .saturating_add(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    SSAOp::IntSub { dst, a, b } => {
                        if let Some(base) = addr_of(a, &addr_exprs)
                            && let Some(raw) = parse_const_value(&b.name)
                        {
                            let off = base
                                .offset
                                .saturating_sub(signed_offset_from_const(raw, ptr_bits));
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base.base,
                                        offset: off,
                                        confidence: base.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    SSAOp::PtrAdd {
                        dst,
                        base,
                        index,
                        element_size,
                    } => {
                        if let Some(base_expr) = addr_of(base, &addr_exprs)
                            && let Some(raw) = parse_const_value(&index.name)
                        {
                            let scaled = signed_offset_from_const(raw, ptr_bits)
                                .saturating_mul((*element_size).into());
                            let off = base_expr.offset.saturating_add(scaled);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base_expr.base,
                                        offset: off,
                                        confidence: base_expr.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    SSAOp::PtrSub {
                        dst,
                        base,
                        index,
                        element_size,
                    } => {
                        if let Some(base_expr) = addr_of(base, &addr_exprs)
                            && let Some(raw) = parse_const_value(&index.name)
                        {
                            let scaled = signed_offset_from_const(raw, ptr_bits)
                                .saturating_mul((*element_size).into());
                            let off = base_expr.offset.saturating_sub(scaled);
                            if (-offset_bound..=offset_bound).contains(&off) {
                                changed |= set_expr(
                                    dst,
                                    GlobalAddrExpr {
                                        base: base_expr.base,
                                        offset: off,
                                        confidence: base_expr.confidence.saturating_sub(1),
                                    },
                                    &mut addr_exprs,
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }

    for block in ssa_blocks {
        for op in &block.ops {
            let resolve_addr = |addr: &SSAVar| -> Option<GlobalAddrExpr> {
                parse_const_value(&addr.name)
                    .filter(|base| *base >= 0x10000)
                    .map(|base| GlobalAddrExpr {
                        base,
                        offset: 0,
                        confidence: 92,
                    })
                    .or_else(|| {
                        addr_exprs
                            .get(&ssa_var_block_key(block.addr, addr))
                            .copied()
                    })
            };
            match op {
                SSAOp::Load { dst, addr, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = field_evidence
                            .entry(expr.base)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.reads = entry.reads.saturating_add(1);
                        entry.field_type = size_to_type(dst.size);
                    }
                }
                SSAOp::Store { addr, val, .. } => {
                    if let Some(expr) = resolve_addr(addr)
                        && (0..=offset_bound).contains(&expr.offset)
                    {
                        let entry = field_evidence
                            .entry(expr.base)
                            .or_default()
                            .entry(expr.offset as u64)
                            .or_default();
                        entry.writes = entry.writes.saturating_add(1);
                        entry.field_type = size_to_type(val.size);
                    }
                }
                _ => {}
            }
        }
    }

    field_evidence
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct InferredGlobalFieldEvidence {
    reads: u32,
    writes: u32,
    field_type: String,
}

fn parse_existing_var_types_from_specs(
    stack_vars: &BTreeMap<StackSlotKey, ExternalStackVarSpec>,
    ptr_bits: u32,
) -> HashMap<String, String> {
    stack_vars
        .values()
        .filter(|var| slot_role_allows_external_local_identity(var.role))
        .filter_map(|var| {
            let ty = var
                .ty
                .as_ref()
                .map(|ty| render_signature_type(ty, ptr_bits))?;
            Some((var.name.clone(), normalize_external_type_name(&ty)))
        })
        .collect()
}

fn estimate_c_type_size_bytes(ty: &str, ptr_bits: u32) -> u64 {
    if let Some(parsed) = parse_type_like_spec(ty, ptr_bits)
        && let Some(size) = estimate_type_like_size_bytes(&parsed, ptr_bits)
        && size > 0
    {
        return size;
    }

    let lower = normalize_external_type_name(ty).trim().to_ascii_lowercase();
    if lower.contains('*') {
        return (ptr_bits / 8).max(1) as u64;
    }
    if lower == "double" || lower == "long double" {
        return 8;
    }
    1
}

fn estimate_type_like_size_bytes(ty: &CTypeLike, ptr_bits: u32) -> Option<u64> {
    match ty {
        CTypeLike::Void | CTypeLike::Unknown | CTypeLike::Function => None,
        CTypeLike::Bool => Some(1),
        CTypeLike::Int { bits, .. } | CTypeLike::Float(bits) => {
            Some((u64::from(*bits).saturating_add(7) / 8).max(1))
        }
        CTypeLike::Pointer(_) => Some((ptr_bits / 8).max(1) as u64),
        CTypeLike::Array(inner, Some(count)) => estimate_type_like_size_bytes(inner, ptr_bits)
            .map(|inner_size| inner_size.saturating_mul(*count as u64)),
        CTypeLike::Array(inner, None) => estimate_type_like_size_bytes(inner, ptr_bits),
        CTypeLike::Struct(_) | CTypeLike::Union(_) | CTypeLike::Enum(_) | CTypeLike::Typedef(_) => {
            None
        }
    }
}

fn render_signature_type(ty: &CTypeLike, ptr_bits: u32) -> String {
    crate::render_signature_type(ty, ptr_bits)
}

fn format_signature(
    function_name: &str,
    ret_type: &str,
    params: &[InferredSignatureParam],
) -> String {
    crate::format_afs_signature(function_name, ret_type, params)
}

fn build_struct_decl(
    struct_name: &str,
    fields: &[StructFieldCandidate],
    ptr_bits: u32,
) -> Option<String> {
    if fields.is_empty() {
        return None;
    }
    let mut sorted_fields = fields.iter().collect::<Vec<_>>();
    sorted_fields.sort_by_key(|field| (field.offset, field.name.as_str()));

    let mut cursor = 0u64;
    let mut lines = Vec::new();
    for field in sorted_fields {
        if field.offset > cursor {
            let gap = field.offset - cursor;
            lines.push(format!("    uint8_t _pad_{cursor:x}[{gap}];"));
            cursor = field.offset;
        }

        let field_type = normalize_external_type_name(&field.field_type);
        lines.push(format!("    {} {};", field_type, field.name));
        cursor = cursor.saturating_add(estimate_c_type_size_bytes(&field_type, ptr_bits));
    }

    let body = lines.join("\n");
    Some(format!("struct {struct_name} {{\n{body}\n}};"))
}

pub fn writeback_type_name_is_opaque_placeholder(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    let stripped = lower
        .trim_start_matches("struct ")
        .trim_start_matches("union ")
        .trim_start_matches("enum ")
        .trim_end_matches('*')
        .trim_end();
    stripped.starts_with("anon_") || stripped.starts_with("type_0x") || lower.contains(" type_0x")
}

fn is_generated_local_struct_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .trim_start_matches("struct ")
        .starts_with("sla_struct_")
}

pub fn writeback_type_name_is_generic(ty: &str) -> bool {
    let normalized = normalize_external_type_name(ty);
    let lower = normalized.trim().to_ascii_lowercase();
    if lower.is_empty() {
        return true;
    }
    if lower.starts_with("byte[") {
        return true;
    }
    if writeback_type_name_is_opaque_placeholder(&lower) {
        return true;
    }
    matches!(
        lower.as_str(),
        "void *"
            | "void*"
            | "char *"
            | "char*"
            | "const char *"
            | "const char*"
            | "signed char *"
            | "signed char*"
            | "unsigned char *"
            | "unsigned char*"
            | "int"
            | "unsigned"
            | "unsigned int"
            | "long"
            | "unsigned long"
    )
}

pub fn writeback_apply_type_name_is_opaque_placeholder(type_name: &str) -> bool {
    if type_name.is_empty() {
        return false;
    }
    normalize_writeback_apply_compare_string(type_name).contains("type_0x")
}

pub fn writeback_apply_type_name_is_generic(type_name: &str) -> bool {
    if type_name.is_empty() {
        return true;
    }
    if writeback_apply_type_name_is_opaque_placeholder(type_name) {
        return true;
    }
    let normalized = normalize_writeback_apply_compare_string(type_name);
    normalized == "void*"
        || normalized == "char*"
        || normalized == "int"
        || normalized == "unsigned"
        || normalized == "long"
        || normalized == "unsignedlong"
        || normalized == "unknown"
        || normalized.starts_with("int")
        || normalized.starts_with("uint")
        || normalized.starts_with("byte[")
}

pub fn signature_writeback_arch_supported(arch_name: &str) -> bool {
    !arch_name.trim().is_empty()
}

pub fn callconv_writeback_arch_supported(arch_name: &str) -> bool {
    matches!(
        arch_name.trim().to_ascii_lowercase().as_str(),
        "x86" | "x86-64" | "x86_64" | "x64" | "amd64"
    )
}

pub fn signature_writeback_size_eligible(basic_block_count: usize) -> bool {
    basic_block_count <= SIGNATURE_WRITEBACK_MAX_BLOCKS
}

pub fn signature_writeback_action_decision(
    kind: SignatureWritebackActionKind,
    arch_name: &str,
    basic_block_count: usize,
    payload_present: bool,
    confidence: u8,
) -> SignatureWritebackActionDecision {
    if !payload_present {
        return SignatureWritebackActionDecision::SkipMissingPayload;
    }
    if !signature_writeback_size_eligible(basic_block_count) {
        return SignatureWritebackActionDecision::SkipTooLarge;
    }
    let (arch_supported, min_confidence) = match kind {
        SignatureWritebackActionKind::Signature => (
            signature_writeback_arch_supported(arch_name),
            SIGNATURE_WRITEBACK_MIN_CONFIDENCE,
        ),
        SignatureWritebackActionKind::Callconv => (
            callconv_writeback_arch_supported(arch_name),
            CALLCONV_WRITEBACK_MIN_CONFIDENCE,
        ),
    };
    if !arch_supported {
        return SignatureWritebackActionDecision::SkipUnsupportedArch;
    }
    if confidence < min_confidence {
        return SignatureWritebackActionDecision::SkipLowConfidence;
    }
    SignatureWritebackActionDecision::Apply
}

pub fn signature_register_arg_var_score(
    current_name: Option<&str>,
    expected_name: Option<&str>,
) -> i32 {
    let Some(current_name) = current_name else {
        return 10;
    };
    if let Some(expected_name) = expected_name.filter(|name| !name.trim().is_empty())
        && writeback_compare_strings_equivalent(current_name, expected_name)
    {
        return 100;
    }
    if !current_name.trim().is_empty() && !writeback_var_name_is_generated(current_name) {
        return 50;
    }
    10
}

pub fn signature_register_arg_rename_decision(
    current_name: Option<&str>,
    expected_name: Option<&str>,
) -> SignatureRegisterArgRenameDecision {
    let Some(expected_name) = expected_name.filter(|name| !name.trim().is_empty()) else {
        return SignatureRegisterArgRenameDecision::SkipInvalid;
    };
    if let Some(current_name) = current_name.filter(|name| !name.trim().is_empty()) {
        if writeback_compare_strings_equivalent(current_name, expected_name) {
            return SignatureRegisterArgRenameDecision::SkipAlreadyMatches;
        }
        if !writeback_var_name_is_generated(current_name) {
            return SignatureRegisterArgRenameDecision::SkipCurrentNameNotGenerated;
        }
    }
    SignatureRegisterArgRenameDecision::Apply
}

pub fn signature_register_arg_type_apply_required(
    current_type: Option<&str>,
    expected_type: Option<&str>,
) -> bool {
    let Some(expected_type) = expected_type.filter(|ty| !ty.trim().is_empty()) else {
        return false;
    };
    let Some(current_type) = current_type.filter(|ty| !ty.trim().is_empty()) else {
        return true;
    };
    !writeback_compare_strings_equivalent(current_type, expected_type)
}

pub fn type_writeback_stack_arg_name_conflict_delete_required(
    conflict_name: Option<&str>,
    target_name: Option<&str>,
    conflict_is_selected_var: bool,
    conflict_is_arg: bool,
    conflict_is_stack_arg: bool,
) -> bool {
    if conflict_is_selected_var || !conflict_is_arg || !conflict_is_stack_arg {
        return false;
    }
    let Some(conflict_name) = conflict_name.filter(|name| !name.trim().is_empty()) else {
        return false;
    };
    let Some(target_name) = target_name.filter(|name| !name.trim().is_empty()) else {
        return false;
    };
    writeback_compare_strings_equivalent(conflict_name, target_name)
}

pub fn signature_register_arg_stack_conflict_delete_required(
    conflict_name: Option<&str>,
    expected_name: Option<&str>,
    conflict_is_selected_var: bool,
    conflict_is_arg: bool,
    conflict_is_stack_arg: bool,
) -> bool {
    type_writeback_stack_arg_name_conflict_delete_required(
        conflict_name,
        expected_name,
        conflict_is_selected_var,
        conflict_is_arg,
        conflict_is_stack_arg,
    )
}

pub fn signature_register_arg_duplicate_delete_required(
    candidate_is_selected_var: bool,
    candidate_is_arg: bool,
    candidate_is_register_arg: bool,
    candidate_arg_index: usize,
    expected_arg_index: usize,
) -> bool {
    !candidate_is_selected_var
        && candidate_is_arg
        && candidate_is_register_arg
        && candidate_arg_index == expected_arg_index
}

pub fn type_writeback_var_type_apply_decision(
    existing_type: Option<&str>,
    candidate_type: &str,
    type_materialization_required: bool,
    type_materialization_available: bool,
) -> TypeWritebackApplyDecision {
    if candidate_type.trim().is_empty() {
        return TypeWritebackApplyDecision::SkipInvalid;
    }
    if type_materialization_required && !type_materialization_available {
        return TypeWritebackApplyDecision::SkipMissingMaterialization;
    }
    if let Some(existing_type) = existing_type.filter(|ty| !ty.trim().is_empty())
        && !writeback_apply_type_name_is_generic(existing_type)
        && writeback_apply_type_name_is_generic(candidate_type)
    {
        return TypeWritebackApplyDecision::SkipConcreteExisting;
    }
    TypeWritebackApplyDecision::Apply
}

pub fn type_writeback_global_type_link_apply_decision(
    existing_type: Option<&str>,
    candidate_type: &str,
    type_materialization_required: bool,
    type_materialization_available: bool,
) -> TypeWritebackApplyDecision {
    if candidate_type.trim().is_empty() {
        return TypeWritebackApplyDecision::SkipInvalid;
    }
    if type_materialization_required && !type_materialization_available {
        return TypeWritebackApplyDecision::SkipMissingMaterialization;
    }
    if let Some(existing_type) = existing_type.filter(|ty| !ty.trim().is_empty())
        && !writeback_apply_types_equivalent(existing_type, candidate_type)
        && !writeback_apply_type_name_is_generic(existing_type)
    {
        return TypeWritebackApplyDecision::SkipConcreteExisting;
    }
    TypeWritebackApplyDecision::Apply
}

pub fn type_writeback_var_rename_apply_decision(
    current_name: Option<&str>,
    old_name: &str,
    new_name: &str,
) -> TypeWritebackRenameApplyDecision {
    if old_name.trim().is_empty() || new_name.trim().is_empty() {
        return TypeWritebackRenameApplyDecision::SkipInvalid;
    }
    if let Some(current_name) = current_name.filter(|name| !name.trim().is_empty())
        && !writeback_var_name_is_generated(current_name)
    {
        return TypeWritebackRenameApplyDecision::SkipCurrentNameNotGenerated;
    }
    TypeWritebackRenameApplyDecision::Apply
}

pub fn canonicalize_writeback_apply_type_name(type_name: &str) -> Option<String> {
    let mut canonical = type_name.trim().to_string();
    if canonical.is_empty() {
        None
    } else {
        while canonical.starts_with("type.") {
            canonical.drain(..5);
        }
        for (dotted, spaced) in [
            ("struct.", "struct "),
            ("union.", "union "),
            ("enum.", "enum "),
            ("struct type.", "struct "),
            ("union type.", "union "),
            ("enum type.", "enum "),
        ] {
            if let Some(rest) = canonical.strip_prefix(dotted) {
                canonical = format!("{spaced}{rest}");
                break;
            }
        }
        if let Some(star_idx) = canonical.find('*')
            && star_idx > 0
            && canonical.as_bytes()[star_idx - 1] != b' '
        {
            canonical.insert(star_idx, ' ');
        }
        Some(canonical)
    }
}

pub fn writeback_type_materialization_key(type_name: &str) -> Option<String> {
    if writeback_apply_type_name_is_generic(type_name) {
        return None;
    }
    let canonical = canonicalize_writeback_apply_type_name(type_name)?;
    aggregate_type_materialization_key(&canonical)
        .or_else(|| named_type_materialization_key(&canonical))
}

pub fn writeback_type_materialization_required(type_name: &str) -> bool {
    type_materialization_required_for_type(
        type_name,
        writeback_type_materialization_key(type_name).as_deref(),
    )
}

fn type_materialization_required_for_type(
    type_name: &str,
    type_materialization_key: Option<&str>,
) -> bool {
    type_materialization_required_from_key(type_materialization_key)
        || writeback_apply_type_name_is_opaque_placeholder(type_name)
}

fn type_materialization_required_from_key(type_materialization_key: Option<&str>) -> bool {
    type_materialization_key.is_some_and(|key| !key.is_empty())
}

pub fn writeback_var_name_is_generated(name: &str) -> bool {
    if name.is_empty() {
        return true;
    }
    if let Some(suffix) = name.strip_prefix("arg")
        && ascii_suffix_is_nonempty_decimal(suffix.as_bytes())
    {
        return true;
    }
    name.starts_with("var_")
        || name.starts_with("local_")
        || name.starts_with("stack_")
        || name.starts_with("arg_")
}

fn normalize_writeback_apply_compare_string(type_name: &str) -> String {
    type_name
        .chars()
        .filter(|ch| !ch.is_whitespace() && *ch != ';')
        .map(|ch| ch.to_ascii_lowercase())
        .collect()
}

fn writeback_compare_strings_equivalent(a: &str, b: &str) -> bool {
    normalize_writeback_apply_compare_string(a) == normalize_writeback_apply_compare_string(b)
}

fn writeback_apply_types_equivalent(a: &str, b: &str) -> bool {
    let a = normalize_external_type_name(a);
    let b = normalize_external_type_name(b);
    writeback_compare_strings_equivalent(&a, &b)
}

fn aggregate_type_materialization_key(type_name: &str) -> Option<String> {
    for prefix in ["struct ", "struct.", "union ", "union.", "enum ", "enum."] {
        let Some(mut rest) = type_name.trim().strip_prefix(prefix) else {
            continue;
        };
        rest = rest.trim_start();
        if let Some(stripped) = rest.strip_prefix("type.") {
            rest = stripped;
        }
        let name = rest
            .chars()
            .take_while(|ch| ch.is_ascii_alphanumeric() || *ch == '_')
            .collect::<String>();
        if !name.is_empty() {
            return Some(name);
        }
    }
    None
}

fn named_type_materialization_key(type_name: &str) -> Option<String> {
    let normalized = normalized_materialization_compare_key(type_name);
    if normalized.is_empty() || writeback_apply_normalized_type_is_builtin(&normalized) {
        None
    } else {
        exact_materialization_type_key(type_name)
    }
}

fn normalized_materialization_compare_key(type_name: &str) -> String {
    let mut normalized =
        normalize_writeback_apply_compare_string(strip_leading_c_qualifiers(type_name));
    while normalized.ends_with('*') {
        normalized.pop();
    }
    normalized
}

fn exact_materialization_type_key(type_name: &str) -> Option<String> {
    let mut exact = strip_leading_c_qualifiers(type_name).trim().to_string();
    while exact.ends_with('*') {
        exact.pop();
        exact = exact.trim_end().to_string();
    }
    if exact.is_empty() { None } else { Some(exact) }
}

fn strip_leading_c_qualifiers(mut type_name: &str) -> &str {
    loop {
        let trimmed = type_name.trim_start();
        let Some((token, rest)) = trimmed
            .split_once(char::is_whitespace)
            .map(|(token, rest)| (token, rest.trim_start()))
        else {
            return trimmed;
        };
        if matches!(token, "const" | "volatile" | "restrict" | "register") {
            type_name = rest;
        } else {
            return trimmed;
        }
    }
}

fn writeback_apply_normalized_type_is_builtin(normalized: &str) -> bool {
    matches!(
        normalized,
        "void"
            | "bool"
            | "char"
            | "signedchar"
            | "unsignedchar"
            | "short"
            | "unsignedshort"
            | "int"
            | "unsigned"
            | "unsignedint"
            | "long"
            | "unsignedlong"
            | "longlong"
            | "unsignedlonglong"
            | "float"
            | "double"
            | "size_t"
    ) || normalized.starts_with("int")
        || normalized.starts_with("uint")
}

fn ascii_suffix_is_nonempty_decimal(bytes: &[u8]) -> bool {
    !bytes.is_empty() && bytes.iter().all(u8::is_ascii_digit)
}

fn is_opaque_placeholder_type_name(name: &str) -> bool {
    writeback_type_name_is_opaque_placeholder(name)
}

fn is_generic_type_string(ty: &str) -> bool {
    writeback_type_name_is_generic(ty)
}

fn is_low_signal_storage_scalar_type(ty: &str, ptr_bits: u32) -> bool {
    parse_type_like_spec(ty, ptr_bits).is_some_and(|parsed| matches!(parsed, CTypeLike::Int { .. }))
}

fn sanitize_c_identifier(raw: &str) -> Option<String> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return None;
    }
    let mut out = String::with_capacity(trimmed.len());
    for ch in trimmed.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.chars().next().is_some_and(|ch| ch.is_ascii_digit()) {
        out.insert(0, '_');
    }
    if out.chars().all(|c| c == '_') {
        None
    } else {
        Some(out)
    }
}

fn is_low_quality_stack_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.starts_with("var_")
        || lower.starts_with("local_")
        || lower.starts_with("stack_")
        || lower == "saved_fp"
        || is_generic_arg_name(&lower)
}

fn parse_const_value(name: &str) -> Option<u64> {
    let val_str = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("CONST:"))?;
    let val_str = val_str.split('_').next().unwrap_or(val_str);

    if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }
    if let Some(dec) = val_str
        .strip_prefix("0d")
        .or_else(|| val_str.strip_prefix("0D"))
    {
        return dec.parse::<u64>().ok();
    }
    if val_str.chars().all(|c| c.is_ascii_hexdigit()) {
        return u64::from_str_radix(val_str, 16).ok();
    }
    val_str.parse::<u64>().ok()
}

fn size_to_type(size: u32) -> String {
    match size {
        1 => "int8_t".to_string(),
        2 => "int16_t".to_string(),
        4 => "int32_t".to_string(),
        8 => "int64_t".to_string(),
        _ => format!("byte[{size}]"),
    }
}

fn signed_offset_from_const(raw: u64, ptr_bits: u32) -> i64 {
    let bits = ptr_bits.clamp(8, 64);
    if bits == 64 {
        return raw as i64;
    }
    let mask = (1u64 << bits) - 1;
    let sign = 1u64 << (bits - 1);
    let v = raw & mask;
    if (v & sign) != 0 {
        (v | (!mask)) as i64
    } else {
        v as i64
    }
}

fn ssa_var_block_key(block_addr: u64, var: &SSAVar) -> String {
    format!(
        "{}_{}@{block_addr:x}",
        var.name.to_ascii_lowercase(),
        var.version
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    fn test_signature_spec(param_name: &str, param_bits: u32) -> FunctionSignatureSpec {
        FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: param_name.to_string(),
                ty: Some(CTypeLike::Int {
                    bits: param_bits,
                    signedness: Signedness::Signed,
                }),
            }],
        }
    }

    fn inferred_test_signature(function_name: &str, param_name: &str) -> InferredSignature {
        InferredSignature {
            function_name: function_name.to_string(),
            signature: format!("int32_t {function_name}(int32_t {param_name});"),
            ret_type: "int32_t".to_string(),
            params: vec![InferredSignatureParam {
                name: param_name.to_string(),
                param_type: "int32_t".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 96,
            callconv_confidence: 90,
        }
    }

    fn empty_writeback_plan(function_name: &str) -> TypeWritebackPlan {
        TypeWritebackPlan {
            signature: inferred_test_signature(function_name, "value"),
            var_type_candidates: Vec::new(),
            var_rename_candidates: Vec::new(),
            struct_decls: Vec::new(),
            global_type_links: Vec::new(),
            diagnostics: TypeWritebackDiagnostics::default(),
        }
    }

    #[test]
    fn writeback_generated_var_name_policy_matches_apply_guard() {
        for generated in [
            "", "arg0", "arg12", "arg_8", "var_10h", "local_20", "stack_18",
        ] {
            assert!(
                writeback_var_name_is_generated(generated),
                "{generated:?} should be replaceable generated storage"
            );
        }

        for user_name in ["arg", "argc", "value", "count", "user_var_10"] {
            assert!(
                !writeback_var_name_is_generated(user_name),
                "{user_name:?} should be preserved as user/current identity"
            );
        }
    }

    #[test]
    fn var_rename_apply_decision_allows_generated_current_names() {
        for current_name in [
            None,
            Some(""),
            Some("arg0"),
            Some("var_10h"),
            Some("local_20"),
        ] {
            assert_eq!(
                type_writeback_var_rename_apply_decision(current_name, "arg0", "count"),
                TypeWritebackRenameApplyDecision::Apply,
                "{current_name:?} should be replaceable"
            );
        }
    }

    #[test]
    fn var_rename_apply_decision_preserves_user_current_names() {
        for current_name in ["arg", "argc", "value", "count", "user_var_10"] {
            assert_eq!(
                type_writeback_var_rename_apply_decision(Some(current_name), "arg0", "count"),
                TypeWritebackRenameApplyDecision::SkipCurrentNameNotGenerated,
                "{current_name:?} should be preserved"
            );
        }
    }

    #[test]
    fn var_rename_apply_decision_rejects_invalid_payload() {
        assert_eq!(
            type_writeback_var_rename_apply_decision(Some("arg0"), "", "count"),
            TypeWritebackRenameApplyDecision::SkipInvalid
        );
        assert_eq!(
            type_writeback_var_rename_apply_decision(Some("arg0"), "arg0", ""),
            TypeWritebackRenameApplyDecision::SkipInvalid
        );
    }

    #[test]
    fn signature_register_arg_var_score_prefers_exact_then_user_named_args() {
        assert_eq!(
            signature_register_arg_var_score(Some(" argc "), Some("argc")),
            100
        );
        assert_eq!(
            signature_register_arg_var_score(Some("ARGC;"), Some("argc")),
            100
        );
        assert_eq!(
            signature_register_arg_var_score(Some("user_count"), Some("argc")),
            50
        );
        assert_eq!(
            signature_register_arg_var_score(Some("arg0"), Some("argc")),
            10
        );
        assert_eq!(signature_register_arg_var_score(None, Some("argc")), 10);
    }

    #[test]
    fn signature_register_arg_rename_decision_preserves_user_names() {
        assert_eq!(
            signature_register_arg_rename_decision(Some("arg0"), Some("argc")),
            SignatureRegisterArgRenameDecision::Apply
        );
        assert_eq!(
            signature_register_arg_rename_decision(Some("argc"), Some("argc")),
            SignatureRegisterArgRenameDecision::SkipAlreadyMatches
        );
        assert_eq!(
            signature_register_arg_rename_decision(Some("user_count"), Some("argc")),
            SignatureRegisterArgRenameDecision::SkipCurrentNameNotGenerated
        );
        assert_eq!(
            signature_register_arg_rename_decision(Some("arg0"), Some("")),
            SignatureRegisterArgRenameDecision::SkipInvalid
        );
    }

    #[test]
    fn signature_register_arg_type_apply_required_matches_legacy_compare() {
        assert!(!signature_register_arg_type_apply_required(
            Some(" int32_t ;"),
            Some("int32_t")
        ));
        assert!(signature_register_arg_type_apply_required(
            None,
            Some("int32_t")
        ));
        assert!(signature_register_arg_type_apply_required(
            Some("int32_t"),
            Some("uint32_t")
        ));
        assert!(!signature_register_arg_type_apply_required(
            Some("int32_t"),
            None
        ));
    }

    #[test]
    fn signature_register_arg_stack_conflict_delete_requires_stack_arg_name_match() {
        assert!(type_writeback_stack_arg_name_conflict_delete_required(
            Some(" argc ;"),
            Some("argc"),
            false,
            true,
            true,
        ));
        assert!(signature_register_arg_stack_conflict_delete_required(
            Some(" argc ;"),
            Some("argc"),
            false,
            true,
            true,
        ));
        assert!(!signature_register_arg_stack_conflict_delete_required(
            Some("argc"),
            Some("argc"),
            true,
            true,
            true,
        ));
        assert!(!signature_register_arg_stack_conflict_delete_required(
            Some("argc"),
            Some("argc"),
            false,
            false,
            true,
        ));
        assert!(!signature_register_arg_stack_conflict_delete_required(
            Some("argc"),
            Some("argc"),
            false,
            true,
            false,
        ));
        assert!(!signature_register_arg_stack_conflict_delete_required(
            Some("other"),
            Some("argc"),
            false,
            true,
            true,
        ));
    }

    #[test]
    fn signature_register_arg_duplicate_delete_requires_same_register_arg_index() {
        assert!(signature_register_arg_duplicate_delete_required(
            false, true, true, 2, 2,
        ));
        assert!(!signature_register_arg_duplicate_delete_required(
            true, true, true, 2, 2,
        ));
        assert!(!signature_register_arg_duplicate_delete_required(
            false, false, true, 2, 2,
        ));
        assert!(!signature_register_arg_duplicate_delete_required(
            false, true, false, 2, 2,
        ));
        assert!(!signature_register_arg_duplicate_delete_required(
            false, true, true, 1, 2,
        ));
    }

    #[test]
    fn writeback_apply_type_name_policy_matches_executor_guard() {
        for generic in [
            "",
            "void *",
            "char*",
            "int",
            "unsigned",
            "long",
            "unsigned long",
            "uint32_t",
            "unknown",
            "byte[16]",
            "struct type_0x1234 *",
        ] {
            assert!(
                writeback_apply_type_name_is_generic(generic),
                "{generic:?} should remain a weak apply-time type"
            );
        }

        assert!(writeback_apply_type_name_is_opaque_placeholder(
            "struct type_0x1234 *"
        ));
        assert!(!writeback_apply_type_name_is_opaque_placeholder(
            "struct real_type *"
        ));
        assert!(!writeback_apply_type_name_is_generic("struct real_type *"));
    }

    #[test]
    fn var_type_apply_decision_preserves_concrete_existing_type() {
        assert_eq!(
            type_writeback_var_type_apply_decision(
                Some("struct real_type *"),
                "uint32_t",
                false,
                true,
            ),
            TypeWritebackApplyDecision::SkipConcreteExisting
        );
        assert_eq!(
            type_writeback_var_type_apply_decision(
                Some("uint32_t"),
                "struct real_type *",
                false,
                true
            ),
            TypeWritebackApplyDecision::Apply
        );
        assert_eq!(
            type_writeback_var_type_apply_decision(
                Some("struct real_type *"),
                "struct better_type *",
                false,
                true,
            ),
            TypeWritebackApplyDecision::Apply
        );
    }

    #[test]
    fn var_type_apply_decision_fails_closed_on_invalid_or_missing_materialization() {
        assert_eq!(
            type_writeback_var_type_apply_decision(None, "", false, true),
            TypeWritebackApplyDecision::SkipInvalid
        );
        assert_eq!(
            type_writeback_var_type_apply_decision(None, "struct Foo *", true, false),
            TypeWritebackApplyDecision::SkipMissingMaterialization
        );
        assert_eq!(
            type_writeback_var_type_apply_decision(None, "struct Foo *", true, true),
            TypeWritebackApplyDecision::Apply
        );
    }

    #[test]
    fn global_type_link_apply_decision_preserves_concrete_existing_type() {
        assert_eq!(
            type_writeback_global_type_link_apply_decision(
                Some("struct real_type *"),
                "uint32_t",
                false,
                true,
            ),
            TypeWritebackApplyDecision::SkipConcreteExisting
        );
        assert_eq!(
            type_writeback_global_type_link_apply_decision(
                Some("struct real_type *"),
                "struct better_type *",
                false,
                true,
            ),
            TypeWritebackApplyDecision::SkipConcreteExisting
        );
    }

    #[test]
    fn global_type_link_apply_decision_allows_same_or_generic_existing_type() {
        assert_eq!(
            type_writeback_global_type_link_apply_decision(
                Some("struct real_type *"),
                "struct.real_type*",
                false,
                true,
            ),
            TypeWritebackApplyDecision::Apply
        );
        assert_eq!(
            type_writeback_global_type_link_apply_decision(
                Some("uint32_t"),
                "struct real_type *",
                false,
                true,
            ),
            TypeWritebackApplyDecision::Apply
        );
    }

    #[test]
    fn global_type_link_apply_decision_fails_closed_on_invalid_or_missing_materialization() {
        assert_eq!(
            type_writeback_global_type_link_apply_decision(None, "", false, true),
            TypeWritebackApplyDecision::SkipInvalid
        );
        assert_eq!(
            type_writeback_global_type_link_apply_decision(None, "struct Foo *", true, false),
            TypeWritebackApplyDecision::SkipMissingMaterialization
        );
    }

    #[test]
    fn global_type_link_apply_decision_requires_materialization_only_when_required() {
        assert_eq!(
            type_writeback_global_type_link_apply_decision(None, "uint32_t", false, false),
            TypeWritebackApplyDecision::Apply
        );
        assert_eq!(
            type_writeback_global_type_link_apply_decision(None, "struct Foo *", true, true),
            TypeWritebackApplyDecision::Apply
        );
    }

    #[test]
    fn signature_action_decision_filters_payload_arch_size_and_confidence() {
        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Signature,
                "x86-64",
                1,
                false,
                SIGNATURE_WRITEBACK_MIN_CONFIDENCE,
            ),
            SignatureWritebackActionDecision::SkipMissingPayload
        );
        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Signature,
                "x86-64",
                SIGNATURE_WRITEBACK_MAX_BLOCKS + 1,
                true,
                100,
            ),
            SignatureWritebackActionDecision::SkipTooLarge
        );
        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Signature,
                "",
                SIGNATURE_WRITEBACK_MAX_BLOCKS,
                true,
                100,
            ),
            SignatureWritebackActionDecision::SkipUnsupportedArch
        );
        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Signature,
                "x86-64",
                SIGNATURE_WRITEBACK_MAX_BLOCKS,
                true,
                SIGNATURE_WRITEBACK_MIN_CONFIDENCE - 1,
            ),
            SignatureWritebackActionDecision::SkipLowConfidence
        );
        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Signature,
                "x86-64",
                SIGNATURE_WRITEBACK_MAX_BLOCKS,
                true,
                SIGNATURE_WRITEBACK_MIN_CONFIDENCE,
            ),
            SignatureWritebackActionDecision::Apply
        );
        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Callconv,
                "arm64",
                1,
                true,
                100,
            ),
            SignatureWritebackActionDecision::SkipUnsupportedArch
        );
        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Callconv,
                "amd64",
                1,
                true,
                CALLCONV_WRITEBACK_MIN_CONFIDENCE - 1,
            ),
            SignatureWritebackActionDecision::SkipLowConfidence
        );
        assert_eq!(
            signature_writeback_action_decision(
                SignatureWritebackActionKind::Callconv,
                "amd64",
                1,
                true,
                CALLCONV_WRITEBACK_MIN_CONFIDENCE,
            ),
            SignatureWritebackActionDecision::Apply
        );
    }

    #[test]
    fn writeback_type_name_policy_matches_planner_guard() {
        assert!(writeback_type_name_is_opaque_placeholder(
            "struct type_0x1234 *"
        ));
        assert!(writeback_type_name_is_opaque_placeholder(
            "struct anon_field"
        ));
        assert!(!writeback_type_name_is_opaque_placeholder(
            "struct real_type *"
        ));

        for generic in ["void *", "const char *", "unsigned char*", "unsigned long"] {
            assert!(
                writeback_type_name_is_generic(generic),
                "{generic:?} should stay a weak planner type"
            );
        }
        assert!(!writeback_type_name_is_generic("struct real_type *"));
    }

    #[test]
    fn writeback_private_compat_wrappers_route_to_public_policy() {
        assert!(is_opaque_placeholder_type_name("union type_0xabcd"));
        assert!(!is_opaque_placeholder_type_name("union concrete"));
        assert!(is_generic_type_string("char *"));
        assert!(!is_generic_type_string("struct concrete *"));
    }

    #[test]
    fn writeback_apply_type_name_canonicalization_matches_legacy_executor_spelling() {
        assert_eq!(
            canonicalize_writeback_apply_type_name(" type.int* "),
            Some("int *".to_string())
        );
        assert_eq!(
            canonicalize_writeback_apply_type_name("struct.sla_example *"),
            Some("struct sla_example *".to_string())
        );
        assert_eq!(
            canonicalize_writeback_apply_type_name("struct type.foo_bar*"),
            Some("struct foo_bar *".to_string())
        );
        assert_eq!(
            canonicalize_writeback_apply_type_name("type.IOCPU_VTable.setCPUNumber"),
            Some("IOCPU_VTable.setCPUNumber".to_string())
        );
        assert_eq!(
            canonicalize_writeback_apply_type_name("*already_pointer"),
            Some("*already_pointer".to_string())
        );
        assert_eq!(canonicalize_writeback_apply_type_name("   "), None);
    }

    #[test]
    fn writeback_type_materialization_key_extracts_live_type_db_keys() {
        for (raw, expected) in [
            ("struct.Foo*", "Foo"),
            ("struct type.Foo *", "Foo"),
            ("union.Bar *", "Bar"),
            ("enum Baz", "Baz"),
            ("IOCPU_VTable *", "IOCPU_VTable"),
            ("const MyAlias *", "MyAlias"),
            ("constant_t *", "constant_t"),
        ] {
            assert_eq!(
                writeback_type_materialization_key(raw).as_deref(),
                Some(expected),
                "{raw:?} should derive the exact radare2 materialization key"
            );
            assert!(
                writeback_type_materialization_required(raw),
                "{raw:?} should require live type-db verification"
            );
        }
    }

    #[test]
    fn writeback_type_materialization_key_omits_builtin_generic_and_opaque_types() {
        for raw in [
            "int *",
            "int32_t *",
            "uint64_t *",
            "const uint64_t *",
            "size_t *",
            "unsigned long *",
            "int32_t",
            "uint64_t",
            "void *",
            "char *",
            "byte[8]",
        ] {
            assert_eq!(writeback_type_materialization_key(raw), None);
            assert!(
                !writeback_type_materialization_required(raw),
                "{raw:?} should not require a radare2 type-db key"
            );
        }

        let opaque = "struct type_0x123 *";
        assert_eq!(writeback_type_materialization_key(opaque), None);
        assert!(
            writeback_type_materialization_required(opaque),
            "opaque placeholders should fail closed when no materialization key exists"
        );
    }

    #[test]
    fn type_writeback_mutation_serializes_materialization_required_only_when_true() {
        let mut mutation = TypeWritebackMutation {
            kind: TypeWritebackMutationKind::VarType,
            signature: None,
            ret_type: None,
            params: Vec::new(),
            callconv: None,
            old_name: None,
            name: Some("var_8h".to_string()),
            reg: None,
            type_name: Some("int32_t".to_string()),
            type_materialization_key: None,
            type_materialization_required: false,
            text: None,
            addr: None,
            size: Some(4),
            delta: Some(-8),
            var_kind: Some("b".to_string()),
            is_arg: Some(false),
            confidence: 90,
            source: WritebackSource::ExternalTypeDb.as_str().to_string(),
            evidence: vec!["unit-test".to_string()],
        };
        let value = serde_json::to_value(&mutation).expect("mutation should serialize");
        assert!(
            value.get("type_materialization_required").is_none(),
            "false materialization requirement should be omitted from JSON"
        );
        assert!(
            value.get("type_materialization_key").is_none(),
            "absent materialization key should be omitted from JSON"
        );

        mutation.type_name = Some("struct Foo *".to_string());
        mutation.type_materialization_key = Some("Foo".to_string());
        mutation.type_materialization_required = true;
        let value = serde_json::to_value(&mutation).expect("mutation should serialize");
        assert_eq!(
            value
                .get("type_materialization_required")
                .and_then(serde_json::Value::as_bool),
            Some(true)
        );
        assert_eq!(
            value
                .get("type_materialization_key")
                .and_then(serde_json::Value::as_str),
            Some("Foo")
        );
    }

    fn certified_signature_facts(param_name: &str, param_bits: u32) -> FunctionTypeFacts {
        let signature_spec = test_signature_spec(param_name, param_bits);
        let signature_certificate = SignatureCertificate::from_signature(
            &signature_spec,
            [SignatureCertificateSource::ExternalContext],
        )
        .expect("external signature should be certifiable");
        FunctionTypeFacts {
            merged_signature: Some(signature_spec),
            signature_certificate: Some(signature_certificate),
            ..FunctionTypeFacts::default()
        }
    }

    fn policy_test_plan(
        function_name: &str,
        confidence: u8,
        rename_confidence: u8,
    ) -> TypeWritebackPlan {
        TypeWritebackPlan {
            signature: inferred_test_signature(function_name, "value"),
            var_type_candidates: vec![VarTypeCandidate {
                name: "var_8h".to_string(),
                kind: "b".to_string(),
                delta: -8,
                var_type: "int32_t".to_string(),
                isarg: false,
                reg: None,
                size: 4,
                confidence,
                source: WritebackSource::ExternalTypeDb,
                evidence: vec![WritebackEvidence::ExternalStackAnnotation],
            }],
            var_rename_candidates: vec![VarRenameCandidate {
                name: "arg1".to_string(),
                target_name: "value".to_string(),
                confidence: rename_confidence,
                source: WritebackSource::ExistingState,
                evidence: vec![WritebackEvidence::ExternalParamName],
            }],
            struct_decls: vec![StructDeclCandidate {
                name: "struct policy_item".to_string(),
                decl: "typedef struct policy_item { int x; } policy_item;".to_string(),
                confidence,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            }],
            global_type_links: vec![GlobalTypeLinkCandidate {
                addr: 0x404000,
                target_type: "struct policy_item *".to_string(),
                confidence,
                source: WritebackSource::ExternalTypeDb,
            }],
            diagnostics: TypeWritebackDiagnostics::default(),
        }
    }

    fn mutation_kind_count(
        mutation_plan: &TypeWritebackMutationPlan,
        kind: TypeWritebackMutationKind,
    ) -> usize {
        mutation_plan
            .mutations
            .iter()
            .filter(|mutation| mutation.kind == kind)
            .count()
    }

    #[test]
    fn inferred_signature_to_type_facts_preserves_merged_signature() {
        let inferred = inferred_test_signature("dbg.typed", "value");

        let type_facts = inferred_signature_to_function_type_facts(&inferred, 64);
        let merged = type_facts
            .merged_signature
            .as_ref()
            .expect("inferred signature should materialize merged signature");

        assert_eq!(merged.params.len(), 1);
        assert_eq!(merged.params[0].name, "value");
        assert!(matches!(
            merged.ret_type,
            Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed
            })
        ));
    }

    #[test]
    fn phi_scalar_pointer_value_preserves_max_confidence() {
        let block_addr = 0x401000;
        let dst = SSAVar::new("phi_ptr", 1, 8);
        let left = SSAVar::new("left_ptr", 1, 8);
        let right = SSAVar::new("right_ptr", 1, 8);
        let parsed_context = ParsedExternalContext::default();
        let pointer_arg_slot_map = HashMap::new();
        let mut pointer_values = HashMap::new();
        let pointer_value_names = HashMap::new();
        let array_addr_exprs = HashMap::new();
        let array_addr_expr_names = HashMap::new();
        let stack_addr_offsets = HashMap::new();
        let stack_addr_offset_names = HashMap::new();
        let block_ops = HashMap::new();
        let value_ops = HashMap::new();

        let low = ScalarPointerValue {
            slot: 0,
            base: ArrayIndexBase::Param { index: 0 },
            element_stride: 8,
            confidence: 20,
        };
        let high = ScalarPointerValue {
            confidence: 88,
            ..low.clone()
        };
        pointer_values.insert(ssa_var_block_key(block_addr, &left), low);
        pointer_values.insert(ssa_var_block_key(block_addr, &right), high);
        let ctx = ScalarArrayInferenceCtx {
            parsed_context: &parsed_context,
            merged_signature: None,
            ptr_bits: 64,
            pointer_arg_slot_map: &pointer_arg_slot_map,
            pointer_values: &pointer_values,
            pointer_value_names: &pointer_value_names,
            array_addr_exprs: &array_addr_exprs,
            array_addr_expr_names: &array_addr_expr_names,
            stack_addr_offsets: &stack_addr_offsets,
            stack_addr_offset_names: &stack_addr_offset_names,
            block_ops: &block_ops,
            value_ops: &value_ops,
        };

        let selected = phi_scalar_pointer_value(block_addr, &dst, &[left, right], &ctx)
            .expect("same-base phi should preserve pointer value");

        assert_eq!(selected.confidence, 88);
    }

    #[test]
    fn phi_scalar_array_addr_expr_preserves_max_confidence() {
        let block_addr = 0x401000;
        let left = SSAVar::new("left_expr", 1, 8);
        let right = SSAVar::new("right_expr", 1, 8);
        let mut array_addr_exprs = HashMap::new();
        let array_addr_expr_names = HashMap::new();
        let pointer = ScalarPointerValue {
            slot: 0,
            base: ArrayIndexBase::Param { index: 0 },
            element_stride: 8,
            confidence: 80,
        };
        let low = ScalarArrayAddrExpr {
            pointer: pointer.clone(),
            field_offset: 0x10,
            confidence: 30,
        };
        let high = ScalarArrayAddrExpr {
            confidence: 91,
            ..low.clone()
        };
        array_addr_exprs.insert(ssa_var_block_key(block_addr, &left), low);
        array_addr_exprs.insert(ssa_var_block_key(block_addr, &right), high);

        let selected = phi_scalar_array_addr_expr(
            block_addr,
            &[left, right],
            &array_addr_exprs,
            &array_addr_expr_names,
        )
        .expect("same-base phi should preserve array address expression");

        assert_eq!(selected.confidence, 91);
    }

    #[test]
    fn mutation_plan_materializes_typed_writeback_kinds_in_order() {
        let type_facts = certified_signature_facts("a", 32);
        let mut plan = empty_writeback_plan("dbg.sum");
        plan.signature = inferred_test_signature("dbg.sum", "a");
        plan.var_type_candidates.push(VarTypeCandidate {
            name: "var_8h".to_string(),
            kind: "b".to_string(),
            delta: -8,
            var_type: "int32_t".to_string(),
            isarg: false,
            reg: None,
            size: 4,
            confidence: MATERIALIZED_VAR_MUTATION_MIN_CONFIDENCE,
            source: WritebackSource::ExternalTypeDb,
            evidence: vec![WritebackEvidence::ExternalStackAnnotation],
        });
        plan.var_rename_candidates.push(VarRenameCandidate {
            name: "arg1".to_string(),
            target_name: "a".to_string(),
            confidence: 96,
            source: WritebackSource::ExistingState,
            evidence: vec![WritebackEvidence::ExternalParamName],
        });

        let mutation_plan = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(usize::MAX, usize::MAX, usize::MAX),
            &type_facts,
        );
        let kinds = mutation_plan
            .mutations
            .iter()
            .map(|mutation| mutation.kind)
            .collect::<Vec<_>>();

        assert_eq!(
            kinds,
            vec![
                TypeWritebackMutationKind::Signature,
                TypeWritebackMutationKind::Callconv,
                TypeWritebackMutationKind::Var,
                TypeWritebackMutationKind::VarType,
                TypeWritebackMutationKind::VarRename,
            ]
        );
        assert_eq!(
            mutation_plan.mutations[0].signature.as_deref(),
            Some("int32_t dbg.sum(int32_t a);")
        );
        assert_eq!(
            mutation_plan.mutations[3].type_name.as_deref(),
            Some("int32_t")
        );
        assert_eq!(mutation_plan.mutations[4].old_name.as_deref(), Some("arg1"));
        assert_eq!(
            mutation_plan.mutations[0].evidence,
            vec!["signature-certificate:external_context".to_string()]
        );
    }

    #[test]
    fn mutation_plan_propagates_type_materialization_keys() {
        let mut plan = empty_writeback_plan("dbg.types");
        plan.var_type_candidates.push(VarTypeCandidate {
            name: "var_8h".to_string(),
            kind: "b".to_string(),
            delta: -8,
            var_type: "struct type.Foo*".to_string(),
            isarg: false,
            reg: None,
            size: 8,
            confidence: MATERIALIZED_VAR_MUTATION_MIN_CONFIDENCE,
            source: WritebackSource::ExternalTypeDb,
            evidence: vec![WritebackEvidence::ExternalStackAnnotation],
        });
        plan.global_type_links.push(GlobalTypeLinkCandidate {
            addr: 0x404000,
            target_type: "struct.Foo*".to_string(),
            confidence: 95,
            source: WritebackSource::ExternalTypeDb,
        });
        plan.var_type_candidates.push(VarTypeCandidate {
            name: "var_ch".to_string(),
            kind: "b".to_string(),
            delta: -12,
            var_type: "int32_t".to_string(),
            isarg: false,
            reg: None,
            size: 4,
            confidence: 90,
            source: WritebackSource::ExternalTypeDb,
            evidence: vec![WritebackEvidence::ExternalStackAnnotation],
        });
        plan.var_type_candidates.push(VarTypeCandidate {
            name: "var_10h".to_string(),
            kind: "b".to_string(),
            delta: -16,
            var_type: "struct type_0x123 *".to_string(),
            isarg: false,
            reg: None,
            size: 8,
            confidence: 90,
            source: WritebackSource::ExternalTypeDb,
            evidence: vec![WritebackEvidence::ExternalStackAnnotation],
        });

        let mutation_plan = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(usize::MAX, usize::MAX, usize::MAX),
            &FunctionTypeFacts::default(),
        );
        let type_mutations = mutation_plan
            .mutations
            .iter()
            .filter(|mutation| {
                matches!(
                    mutation.kind,
                    TypeWritebackMutationKind::Var
                        | TypeWritebackMutationKind::VarType
                        | TypeWritebackMutationKind::TypeLink
                )
            })
            .collect::<Vec<_>>();

        assert_eq!(type_mutations.len(), 5);
        let foo_mutations = type_mutations
            .iter()
            .filter(|mutation| mutation.type_name.as_deref() == Some("struct Foo *"))
            .collect::<Vec<_>>();
        assert_eq!(foo_mutations.len(), 3);
        for mutation in foo_mutations {
            assert_eq!(mutation.type_materialization_key.as_deref(), Some("Foo"));
            assert!(mutation.type_materialization_required);
        }
        let builtin_var_type = type_mutations
            .iter()
            .find(|mutation| mutation.type_name.as_deref() == Some("int32_t"))
            .expect("builtin var type mutation should be emitted");
        assert_eq!(builtin_var_type.type_materialization_key, None);
        assert!(!builtin_var_type.type_materialization_required);
        let opaque_var_type = type_mutations
            .iter()
            .find(|mutation| mutation.type_name.as_deref() == Some("struct type_0x123 *"))
            .expect("opaque var type mutation should be emitted fail-closed");
        assert_eq!(opaque_var_type.type_materialization_key, None);
        assert!(opaque_var_type.type_materialization_required);
    }

    #[test]
    fn mutation_apply_policy_balanced_filters_by_kind_thresholds() {
        let type_facts = FunctionTypeFacts::default();
        let budget = TypeWritebackMutationBudget::new(64, 64, 64);
        let below = policy_test_plan("dbg.policy_low", 84, 92);
        let at_threshold = policy_test_plan("dbg.policy_ok", 85, 93);

        let below_plan = type_writeback_mutation_plan_with_policy(
            &below,
            budget,
            &type_facts,
            TypeWritebackApplyPolicy::balanced(),
        );
        let threshold_plan = type_writeback_mutation_plan_with_policy(
            &at_threshold,
            budget,
            &type_facts,
            TypeWritebackApplyPolicy::balanced(),
        );

        assert_eq!(
            mutation_kind_count(&below_plan, TypeWritebackMutationKind::TypeDecl),
            0
        );
        assert_eq!(
            mutation_kind_count(&below_plan, TypeWritebackMutationKind::VarType),
            0
        );
        assert_eq!(
            mutation_kind_count(&below_plan, TypeWritebackMutationKind::VarRename),
            0
        );
        assert_eq!(
            mutation_kind_count(&below_plan, TypeWritebackMutationKind::TypeLink),
            0
        );
        assert_eq!(
            mutation_kind_count(&threshold_plan, TypeWritebackMutationKind::TypeDecl),
            1
        );
        assert_eq!(
            mutation_kind_count(&threshold_plan, TypeWritebackMutationKind::VarType),
            1
        );
        assert_eq!(
            mutation_kind_count(&threshold_plan, TypeWritebackMutationKind::VarRename),
            1
        );
        assert_eq!(
            mutation_kind_count(&threshold_plan, TypeWritebackMutationKind::TypeLink),
            1
        );
        assert_eq!(
            mutation_kind_count(&threshold_plan, TypeWritebackMutationKind::Var),
            0,
            "materialized vars require their stronger confidence threshold"
        );
        assert!(below_plan.diagnostics.iter().any(|diagnostic| {
            diagnostic == "var_type mutation plan withheld 1 low-confidence candidate(s)"
        }));
    }

    #[test]
    fn mutation_apply_policy_aggressive_lowers_expected_thresholds() {
        let type_facts = FunctionTypeFacts::default();
        let budget = TypeWritebackMutationBudget::new(64, 64, 64);
        let plan = policy_test_plan("dbg.policy_aggressive", 75, 85);

        let balanced = type_writeback_mutation_plan_with_policy(
            &plan,
            budget,
            &type_facts,
            TypeWritebackApplyPolicy::balanced(),
        );
        let aggressive = type_writeback_mutation_plan_with_policy(
            &plan,
            budget,
            &type_facts,
            TypeWritebackApplyPolicy::aggressive(),
        );

        assert_eq!(
            mutation_kind_count(&balanced, TypeWritebackMutationKind::TypeDecl),
            0
        );
        assert_eq!(
            mutation_kind_count(&balanced, TypeWritebackMutationKind::VarRename),
            0
        );
        assert_eq!(
            mutation_kind_count(&aggressive, TypeWritebackMutationKind::TypeDecl),
            1
        );
        assert_eq!(
            mutation_kind_count(&aggressive, TypeWritebackMutationKind::VarType),
            1
        );
        assert_eq!(
            mutation_kind_count(&aggressive, TypeWritebackMutationKind::VarRename),
            1
        );
        assert_eq!(
            mutation_kind_count(&aggressive, TypeWritebackMutationKind::TypeLink),
            1
        );
    }

    #[test]
    fn mutation_apply_policy_off_keeps_certified_signature_only() {
        let type_facts = certified_signature_facts("value", 32);
        let budget = TypeWritebackMutationBudget::new(64, 64, 64);
        let plan = policy_test_plan("dbg.policy_off", 100, 100);

        let mutation_plan = type_writeback_mutation_plan_with_policy(
            &plan,
            budget,
            &type_facts,
            TypeWritebackApplyPolicy::off(),
        );
        let kinds = mutation_plan
            .mutations
            .iter()
            .map(|mutation| mutation.kind)
            .collect::<Vec<_>>();

        assert_eq!(
            kinds,
            vec![
                TypeWritebackMutationKind::Signature,
                TypeWritebackMutationKind::Callconv,
            ]
        );
    }

    #[test]
    fn mutation_apply_policy_preserves_materialized_var_threshold() {
        let type_facts = FunctionTypeFacts::default();
        let budget = TypeWritebackMutationBudget::new(64, 64, 64);
        let below_materialized = policy_test_plan(
            "dbg.policy_materialized_var",
            MATERIALIZED_VAR_MUTATION_MIN_CONFIDENCE - 1,
            100,
        );

        let mutation_plan = type_writeback_mutation_plan_with_policy(
            &below_materialized,
            budget,
            &type_facts,
            TypeWritebackApplyPolicy::aggressive(),
        );

        assert_eq!(
            mutation_kind_count(&mutation_plan, TypeWritebackMutationKind::VarType),
            1
        );
        assert_eq!(
            mutation_kind_count(&mutation_plan, TypeWritebackMutationKind::Var),
            0
        );
    }

    #[test]
    fn render_only_signature_certificate_is_not_writeback_authority() {
        let signature_spec = test_signature_spec("value", 32);
        let signature_certificate = SignatureCertificate::from_signature(
            &signature_spec,
            [SignatureCertificateSource::LocalInference],
        )
        .expect("exact local signature should be recorded");
        let type_facts = FunctionTypeFacts {
            merged_signature: Some(signature_spec),
            signature_certificate: Some(signature_certificate),
            ..FunctionTypeFacts::default()
        };
        let plan = empty_writeback_plan("dbg.local");

        let decision = signature_writeback_decision(&type_facts);
        let mutation_plan = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(64, usize::MAX, usize::MAX),
            &type_facts,
        );

        assert!(!decision.authorized);
        assert_eq!(decision.sources, vec!["local_inference".to_string()]);
        assert!(
            decision
                .refusal
                .as_deref()
                .is_some_and(|reason| reason.contains("certificate sources are not authoritative"))
        );
        assert!(
            mutation_plan.mutations.iter().all(|mutation| {
                !matches!(
                    mutation.kind,
                    TypeWritebackMutationKind::Signature | TypeWritebackMutationKind::Callconv
                )
            }),
            "{:?}",
            mutation_plan.mutations
        );
        assert!(
            mutation_plan
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains("certificate sources are not authoritative"))
        );
    }

    #[test]
    fn stale_signature_certificate_is_not_writeback_authority() {
        let current_signature = test_signature_spec("value", 32);
        let stale_signature = test_signature_spec("old_value", 64);
        let signature_certificate = SignatureCertificate::from_signature(
            &stale_signature,
            [SignatureCertificateSource::ExternalContext],
        )
        .expect("external signature should be certifiable");
        let type_facts = FunctionTypeFacts {
            merged_signature: Some(current_signature),
            signature_certificate: Some(signature_certificate),
            ..FunctionTypeFacts::default()
        };
        let plan = empty_writeback_plan("dbg.stale");

        let decision = signature_writeback_decision(&type_facts);
        let mutation_plan = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(64, usize::MAX, usize::MAX),
            &type_facts,
        );

        assert!(!decision.authorized);
        assert!(decision.refusal.as_deref().is_some_and(|reason| {
            reason.contains("SignatureCertificate does not match current merged signature")
        }));
        assert!(
            mutation_plan.mutations.iter().all(|mutation| {
                !matches!(
                    mutation.kind,
                    TypeWritebackMutationKind::Signature | TypeWritebackMutationKind::Callconv
                )
            }),
            "{:?}",
            mutation_plan.mutations
        );
        assert!(
            mutation_plan.diagnostics.iter().any(|diagnostic| {
                diagnostic.contains("does not match current merged signature")
            })
        );
    }

    #[test]
    fn authority_report_owns_signature_and_mutation_policy() {
        let type_facts = certified_signature_facts("value", 32);
        let plan = empty_writeback_plan("dbg.authorized");

        let report = type_writeback_authority_report(
            &plan,
            TypeWritebackMutationBudget::new(64, usize::MAX, usize::MAX),
            &type_facts,
            1,
        );

        assert!(report.signature_render_authorized);
        assert!(report.signature_writeback.authorized);
        assert_eq!(
            report.signature_writeback.sources,
            vec![
                SignatureCertificateSource::ExternalContext
                    .as_str()
                    .to_string()
            ]
        );
        assert!(
            report
                .mutation_plan
                .mutations
                .iter()
                .any(|mutation| { mutation.kind == TypeWritebackMutationKind::Signature }),
            "{:?}",
            report.mutation_plan.mutations
        );
        assert!(
            report
                .mutation_plan
                .mutations
                .iter()
                .any(|mutation| { mutation.kind == TypeWritebackMutationKind::Callconv }),
            "{:?}",
            report.mutation_plan.mutations
        );
    }

    #[test]
    fn authority_report_owns_display_truncation_warnings() {
        let type_facts = certified_signature_facts("value", 32);
        let mut plan = empty_writeback_plan("dbg.report_budget");
        plan.diagnostics.warnings.push("seed warning".to_string());
        plan.struct_decls = vec![
            StructDeclCandidate {
                name: "struct a".to_string(),
                decl: "typedef struct a { int x; } a;".to_string(),
                confidence: 90,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            },
            StructDeclCandidate {
                name: "struct b".to_string(),
                decl: "typedef struct b { int x; } b;".to_string(),
                confidence: 90,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            },
        ];
        plan.global_type_links = vec![
            GlobalTypeLinkCandidate {
                addr: 0x404000,
                target_type: "struct a *".to_string(),
                confidence: 90,
                source: WritebackSource::ExternalTypeDb,
            },
            GlobalTypeLinkCandidate {
                addr: 0x404008,
                target_type: "struct b *".to_string(),
                confidence: 90,
                source: WritebackSource::ExternalTypeDb,
            },
        ];

        let report = type_writeback_authority_report(
            &plan,
            TypeWritebackMutationBudget::new(1, 1, usize::MAX),
            &type_facts,
            1,
        );

        assert!(
            report
                .warnings
                .iter()
                .any(|warning| warning == "seed warning")
        );
        assert!(
            report.warnings.iter().any(|warning| {
                warning.contains("type declaration report truncated from 2 to 1")
            })
        );
        assert!(
            report.warnings.iter().any(|warning| {
                warning.contains("global type-link report truncated from 2 to 1")
            })
        );
    }

    #[test]
    fn mutation_plan_respects_global_type_link_budget() {
        let mut plan = empty_writeback_plan("dbg.links");
        plan.global_type_links = vec![
            GlobalTypeLinkCandidate {
                addr: 0x404000,
                target_type: "struct a *".to_string(),
                confidence: 90,
                source: WritebackSource::ExternalTypeDb,
            },
            GlobalTypeLinkCandidate {
                addr: 0x404008,
                target_type: "struct b *".to_string(),
                confidence: 90,
                source: WritebackSource::ExternalTypeDb,
            },
        ];

        let limited = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(1, usize::MAX, usize::MAX),
            &FunctionTypeFacts::default(),
        );
        let all = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(2, usize::MAX, usize::MAX),
            &FunctionTypeFacts::default(),
        );

        assert_eq!(
            limited
                .mutations
                .iter()
                .filter(|mutation| mutation.kind == TypeWritebackMutationKind::TypeLink)
                .count(),
            1
        );
        assert_eq!(
            all.mutations
                .iter()
                .filter(|mutation| mutation.kind == TypeWritebackMutationKind::TypeLink)
                .count(),
            2
        );
        assert!(
            all.diagnostics
                .iter()
                .all(|diagnostic| !diagnostic.contains("global type-link mutation plan truncated")),
            "{:?}",
            all.diagnostics
        );
        assert!(limited.diagnostics.iter().any(|diagnostic| {
            diagnostic == "global type-link mutation plan truncated from 2 to 1 item(s)"
        }));
    }

    #[test]
    fn mutation_plan_exact_type_decl_budget_does_not_report_truncation() {
        let mut plan = empty_writeback_plan("dbg.types_exact");
        plan.struct_decls = vec![
            StructDeclCandidate {
                name: "struct a".to_string(),
                decl: "typedef struct a { int x; } a;".to_string(),
                confidence: 90,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            },
            StructDeclCandidate {
                name: "struct b".to_string(),
                decl: "typedef struct b { int y; } b;".to_string(),
                confidence: 90,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            },
        ];

        let mutation_plan = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(64, 2, usize::MAX),
            &FunctionTypeFacts::default(),
        );

        assert_eq!(
            mutation_plan
                .mutations
                .iter()
                .filter(|mutation| mutation.kind == TypeWritebackMutationKind::TypeDecl)
                .count(),
            2
        );
        assert!(
            mutation_plan
                .diagnostics
                .iter()
                .all(|diagnostic| !diagnostic.contains("type declaration mutation plan truncated")),
            "{:?}",
            mutation_plan.diagnostics
        );
    }

    #[test]
    fn mutation_plan_truncates_declarations_and_budgeted_mutations() {
        let mut plan = empty_writeback_plan("dbg.types");
        plan.struct_decls = vec![
            StructDeclCandidate {
                name: "struct a".to_string(),
                decl: "typedef struct a { int x; } a;".to_string(),
                confidence: 90,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            },
            StructDeclCandidate {
                name: "struct b".to_string(),
                decl: "typedef struct b { int y; } b;".to_string(),
                confidence: 90,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            },
        ];
        plan.var_type_candidates.push(VarTypeCandidate {
            name: "var_8h".to_string(),
            kind: "b".to_string(),
            delta: -8,
            var_type: "int32_t".to_string(),
            isarg: false,
            reg: None,
            size: 4,
            confidence: MATERIALIZED_VAR_MUTATION_MIN_CONFIDENCE,
            source: WritebackSource::ExternalTypeDb,
            evidence: vec![WritebackEvidence::ExternalStackAnnotation],
        });

        let mutation_plan = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(64, 1, 1),
            &FunctionTypeFacts::default(),
        );

        assert_eq!(
            mutation_plan
                .mutations
                .iter()
                .filter(|mutation| mutation.kind == TypeWritebackMutationKind::TypeDecl)
                .count(),
            1
        );
        assert!(mutation_plan.diagnostics.iter().any(|diagnostic| {
            diagnostic == "type declaration mutation plan truncated from 2 to 1 item(s)"
        }));
        assert!(mutation_plan.diagnostics.iter().any(|diagnostic| {
            diagnostic == "non-signature mutation plan truncated to 1 item(s)"
        }));
    }

    #[test]
    fn mutation_plan_first_budget_overflow_reports_single_skip() {
        let mut plan = empty_writeback_plan("dbg.one_skip");
        plan.struct_decls = vec![
            StructDeclCandidate {
                name: "struct a".to_string(),
                decl: "typedef struct a { int x; } a;".to_string(),
                confidence: 90,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            },
            StructDeclCandidate {
                name: "struct b".to_string(),
                decl: "typedef struct b { int y; } b;".to_string(),
                confidence: 90,
                source: StructDeclSource::ExternalTypeDb,
                fields: Vec::new(),
            },
        ];

        let mutation_plan = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(64, 2, 1),
            &FunctionTypeFacts::default(),
        );

        assert_eq!(
            mutation_plan
                .mutations
                .iter()
                .filter(|mutation| mutation.kind == TypeWritebackMutationKind::TypeDecl)
                .count(),
            1
        );
        assert_eq!(
            mutation_plan
                .diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic.as_str() == "non-signature mutation plan truncated to 1 item(s)"
                })
                .count(),
            1,
            "{:?}",
            mutation_plan.diagnostics
        );
    }

    #[test]
    fn materialized_var_mutation_requires_high_confidence() {
        let mut plan = empty_writeback_plan("dbg.var");
        plan.var_type_candidates.push(VarTypeCandidate {
            name: "var_8h".to_string(),
            kind: "b".to_string(),
            delta: -8,
            var_type: "int32_t".to_string(),
            isarg: false,
            reg: None,
            size: 4,
            confidence: MATERIALIZED_VAR_MUTATION_MIN_CONFIDENCE - 1,
            source: WritebackSource::ExternalTypeDb,
            evidence: vec![WritebackEvidence::ExternalStackAnnotation],
        });

        let mutation_plan = type_writeback_mutation_plan(
            &plan,
            TypeWritebackMutationBudget::new(64, usize::MAX, usize::MAX),
            &FunctionTypeFacts::default(),
        );

        assert!(
            mutation_plan
                .mutations
                .iter()
                .all(|mutation| mutation.kind != TypeWritebackMutationKind::Var),
            "{:?}",
            mutation_plan.mutations
        );
        assert!(
            mutation_plan
                .mutations
                .iter()
                .any(|mutation| mutation.kind == TypeWritebackMutationKind::VarType),
            "{:?}",
            mutation_plan.mutations
        );
    }

    #[test]
    fn signature_type_parser_preserves_source_width_typedefs() {
        assert_eq!(
            parse_signature_type_preserving_c_typedefs("long", 64),
            Some(typedef_type("long"))
        );
        assert_eq!(
            parse_signature_type_preserving_c_typedefs("unsigned long int", 64),
            Some(typedef_type("unsigned long"))
        );
        assert_eq!(
            parse_signature_type_preserving_c_typedefs("short", 64),
            Some(typedef_type("short"))
        );
        assert_eq!(
            parse_signature_type_preserving_c_typedefs("size_t", 64),
            Some(typedef_type("size_t"))
        );
        assert_eq!(
            parse_signature_type_preserving_c_typedefs("ptrdiff_t", 64),
            Some(typedef_type("ptrdiff_t"))
        );
    }

    #[test]
    fn local_struct_decl_preserves_sparse_offsets_with_padding() {
        let decl = build_struct_decl(
            "sla_struct_sparse",
            &[
                StructFieldCandidate {
                    name: "f_8".to_string(),
                    offset: 8,
                    field_type: "int32_t".to_string(),
                    confidence: 95,
                },
                StructFieldCandidate {
                    name: "f_34".to_string(),
                    offset: 0x34,
                    field_type: "int32_t".to_string(),
                    confidence: 95,
                },
            ],
            64,
        )
        .expect("struct decl");

        assert!(decl.contains("uint8_t _pad_0[8];"), "{decl}");
        assert!(decl.contains("int32_t f_8;"), "{decl}");
        assert!(decl.contains("uint8_t _pad_c[40];"), "{decl}");
        assert!(decl.contains("int32_t f_34;"), "{decl}");
    }

    fn test_native_summary(slice_class: r2sym::SliceClass) -> r2sym::NativeFunctionSummary {
        r2sym::NativeFunctionSummary {
            slice_class,
            role_identity: None,
            closure_functions: 1,
            helper_functions: 0,
            derived_summaries: 0,
            derived_diagnostics: Default::default(),
            region_summaries: Vec::new(),
            worker_summaries: Vec::new(),
        }
    }

    fn test_artifact(
        stage: r2sym::RefinementStage,
        slice_class: r2sym::SliceClass,
        skipped_large_cfg: bool,
        residual_reasons: Vec<r2sym::ResidualReason>,
        regions: Vec<r2sym::SemanticRegion>,
    ) -> r2sym::SemanticArtifact {
        let regions = regions
            .into_iter()
            .map(|region| (region.key(), region))
            .collect::<BTreeMap<_, _>>();
        r2sym::SemanticArtifact {
            stage,
            granularity: r2sym::ArtifactGranularity::Regioned,
            execution: r2sym::ExecutionModel::Native,
            body: r2sym::SemanticArtifactBody::Native(r2sym::NativeArtifactBody {
                summary: test_native_summary(slice_class),
                regions,
            }),
            diagnostics: r2sym::SemanticArtifactDiagnostics {
                branches_evaluated: 0,
                branches_pruned: 0,
                branches_unknown: 0,
                skipped_missing_arch: false,
                skipped_large_cfg,
                residual_reasons,
                interpreter: None,
                ambiguous_targets: Vec::new(),
                cache_hit: false,
            },
        }
    }

    fn test_artifact_with_role_identity(
        role_name: &str,
        summary_kind: r2sym::NativeWorkerSummaryKind,
    ) -> r2sym::SemanticArtifact {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let evidence =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget);
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native.summary.role_identity = Some(Box::new(r2sym::NativeWorkerRoleIdentity {
            role_name: role_name.to_string(),
            source: r2sym::NativeWorkerRoleSource::Structural,
            confidence: r2sym::SemanticConfidence::Likely,
            source_names: vec![role_name.to_string()],
            summary_kinds: BTreeSet::from([summary_kind]),
            evidence: evidence.clone(),
        }));
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: summary_kind,
                dst: None,
                src: None,
                memory: None,
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence,
            });
        artifact
    }

    fn build_type_writeback_analysis_with_role_identity(
        input: TypeWritebackAnalysisInput<'_>,
        role_name: &str,
        summary_kind: r2sym::NativeWorkerSummaryKind,
    ) -> TypeWritebackAnalysis {
        let artifact = test_artifact_with_role_identity(role_name, summary_kind);
        build_type_writeback_analysis_with_semantics(
            input,
            TypeWritebackSemanticInputs {
                artifact: &artifact,
                local_field_accesses: &[],
            },
        )
    }

    #[test]
    fn native_worker_summary_projection_marks_transfer_params() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Residual,
            r2sym::SliceClass::Worker,
            true,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::MemoryTransfer,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                src: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: None,
                }),
                memory: None,
                len: Some(r2ssa::SummaryTransferLength::Arg(2)),
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

        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(None),
            Some(&artifact),
            64,
        );

        assert!(projection.pointer_param_indices.contains(&0));
        assert!(projection.pointer_param_indices.contains(&1));
        assert!(!projection.pointer_param_indices.contains(&2));
        assert!(projection.out_param_indices.contains(&0));
        assert!(!projection.out_param_indices.contains(&1));
        assert_eq!(
            projection.param_type_hints.get(&0),
            Some(&byte_pointer_type())
        );
        assert_eq!(
            projection.param_type_hints.get(&1),
            Some(&byte_pointer_type())
        );
        assert_eq!(projection.param_type_hints.get(&2), Some(&size_type(64)));
    }

    #[test]
    fn generic_memory_worker_summary_does_not_create_pointer_type_hint() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Residual,
            r2sym::SliceClass::Worker,
            true,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401008,
                kind: r2sym::NativeWorkerSummaryKind::MemoryRead,
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

        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(None),
            Some(&artifact),
            64,
        );

        assert!(!projection.pointer_param_indices.contains(&0));
        assert!(!projection.param_type_hints.contains_key(&0));
    }

    #[test]
    fn generic_memory_write_worker_refuses_unsafe_out_pointer_projection() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Residual,
            r2sym::SliceClass::Worker,
            true,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401020,
                kind: r2sym::NativeWorkerSummaryKind::MemoryWrite,
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

        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(None),
            Some(&artifact),
            64,
        );

        assert!(!projection.pointer_param_indices.contains(&0));
        assert!(!projection.out_param_indices.contains(&0));
        assert!(!projection.param_type_hints.contains_key(&0));
        assert!(projection.refusal_warnings().iter().any(|warning| {
            warning.contains("generic memory summary") && warning.contains("out-pointer projection")
        }));

        let plan = build_semantic_type_fallback_plan("fcn.401020", "x86-64", 64, &artifact);
        assert!(
            plan.signature.params.is_empty(),
            "generic memory write must not fabricate fallback pointer params"
        );
        assert!(plan.diagnostics.warnings.iter().any(|warning| {
            warning.contains("generic memory summary") && warning.contains("out-pointer projection")
        }));
    }

    #[test]
    fn native_worker_string_scan_projection_marks_char_pointer() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Residual,
            r2sym::SliceClass::Worker,
            true,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401010,
                kind: r2sym::NativeWorkerSummaryKind::StringScan,
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
                loop_summary: Some(r2sym::NativeWorkerLoopSummary {
                    header: 0x401010,
                    exit_target: None,
                    iterations: None,
                    length_arg: None,
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::ZeroByte),
                    fold: None,
                    table_walk: None,
                }),
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });

        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(None),
            Some(&artifact),
            64,
        );

        assert!(projection.pointer_param_indices.contains(&0));
        assert_eq!(
            projection.param_type_hints.get(&0),
            Some(&signed_byte_pointer_type())
        );
    }

    #[test]
    fn native_worker_numeric_parser_projection_marks_char_pointer() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Residual,
            r2sym::SliceClass::Worker,
            true,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401030,
                kind: r2sym::NativeWorkerSummaryKind::Parser,
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
                parser: Some(r2sym::NativeParserSummary {
                    kind: r2sym::NativeParserKind::Numeric,
                    cursor_arg: Some(0),
                    base: Some(10),
                    digit_min: Some(b'0'),
                    digit_max: Some(b'9'),
                    accepts_sign: true,
                    return_predicate: None,
                }),
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });

        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(None),
            Some(&artifact),
            64,
        );

        assert!(projection.pointer_param_indices.contains(&0));
        assert_eq!(
            projection.param_type_hints.get(&0),
            Some(&signed_byte_pointer_type())
        );
    }

    #[test]
    fn token_parser_summary_projection_names_output_and_stream_params() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        artifact.granularity = r2sym::ArtifactGranularity::SummaryOnly;
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401030,
                kind: r2sym::NativeWorkerSummaryKind::Parser,
                dst: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                    range: None,
                }),
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                    range: Some(r2ssa::SummaryMemoryRange {
                        offset_lo: 0,
                        offset_hi: 0,
                        width: Some(1),
                    }),
                }),
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: Some(r2sym::NativeParserSummary {
                    kind: r2sym::NativeParserKind::Token,
                    cursor_arg: Some(1),
                    base: None,
                    digit_min: None,
                    digit_max: None,
                    accepts_sign: false,
                    return_predicate: None,
                }),
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });
        native
            .summary
            .region_summaries
            .push(r2sym::NativeRegionSummary {
                stable_id: 0x401030,
                anchor: 0x401030,
                kind: r2sym::NativeWorkerSummaryKind::Parser,
                blocks: BTreeSet::from([0x401030]),
                entries: BTreeSet::from([0x401030]),
                exits: BTreeSet::new(),
                memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                    kind: r2sym::NativeMemoryAccessKind::Read,
                    location: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                        range: Some(r2ssa::SummaryMemoryRange {
                            offset_lo: 0,
                            offset_hi: 0,
                            width: Some(1),
                        }),
                    }),
                    dst: None,
                    src: None,
                    len: None,
                    width: Some(1),
                }],
                loop_summary: None,
                reductions: Vec::new(),
                parser: Some(r2sym::NativeParserSummary {
                    kind: r2sym::NativeParserKind::Token,
                    cursor_arg: Some(1),
                    base: None,
                    digit_min: None,
                    digit_max: None,
                    accepts_sign: false,
                    return_predicate: None,
                }),
                residual_reasons: Vec::new(),
                confidence: r2sym::SemanticConfidence::Likely,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });

        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(None),
            Some(&artifact),
            64,
        );

        assert_eq!(
            projection.param_name_hints.get(&0).map(String::as_str),
            Some("output")
        );
        assert_eq!(
            projection.param_name_hints.get(&1).map(String::as_str),
            Some("stream")
        );
        assert_eq!(
            projection.param_type_hints.get(&0),
            Some(&byte_pointer_type())
        );
        assert_eq!(
            projection.param_type_hints.get(&1),
            Some(&byte_pointer_type())
        );

        let plan =
            build_semantic_type_fallback_plan("readlinebuffer_delim", "x86-64", 64, &artifact);
        assert_eq!(plan.signature.params.len(), 2);
        assert_eq!(plan.signature.ret_type, "void");
        assert_eq!(plan.signature.params[0].name, "output");
        assert_eq!(plan.signature.params[1].name, "stream");
        assert_eq!(plan.signature.params[0].param_type, "uint8_t*");
        assert_eq!(plan.signature.params[1].param_type, "uint8_t*");
    }

    #[test]
    fn native_region_summary_projection_preferred_over_worker_projection() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Residual,
            r2sym::SliceClass::Worker,
            true,
            vec![r2sym::ResidualReason::LargeCfg],
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .region_summaries
            .push(r2sym::NativeRegionSummary {
                stable_id: 0x401010,
                anchor: 0x401010,
                kind: r2sym::NativeWorkerSummaryKind::StringScan,
                blocks: BTreeSet::from([0x401010]),
                entries: BTreeSet::from([0x401010]),
                exits: BTreeSet::new(),
                memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                    kind: r2sym::NativeMemoryAccessKind::Read,
                    location: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: None,
                    }),
                    dst: None,
                    src: None,
                    len: None,
                    width: Some(1),
                }],
                loop_summary: Some(r2sym::NativeLoopSummary {
                    header: 0x401010,
                    body: BTreeSet::from([0x401010]),
                    entries: BTreeSet::from([0x401010]),
                    exits: BTreeSet::new(),
                    iterations: None,
                    length_arg: Some(1),
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::ZeroByte),
                }),
                reductions: Vec::new(),
                parser: None,
                residual_reasons: vec![r2sym::ResidualReason::LargeCfg],
                confidence: r2sym::SemanticConfidence::Likely,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });

        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(None),
            Some(&artifact),
            64,
        );

        assert_eq!(
            projection.param_type_hints.get(&0),
            Some(&signed_byte_pointer_type())
        );
        assert_eq!(projection.param_type_hints.get(&1), Some(&size_type(64)));
        assert!(!projection.pointer_param_indices.contains(&1));
    }

    fn test_arg_memory_term(offset: i64, size: u32) -> r2sym::BackwardMemoryCondition {
        r2sym::BackwardMemoryCondition {
            region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
            offset_lo: offset,
            offset_hi: offset,
            size,
            exact_offset: true,
            evidence: r2sym::SemanticEvidence::exact(),
            binding: None,
            expr: format!("*(arg0 + {offset})"),
            value_expr: None,
            exact_value: false,
        }
    }

    fn test_exact_compiled_condition(
        simplified: &str,
        memory_terms: Vec<r2sym::BackwardMemoryCondition>,
    ) -> r2sym::BackwardConditionSummary {
        r2sym::BackwardConditionSummary {
            simplified: simplified.to_string(),
            terms: vec![simplified.to_string()],
            memory_terms,
            backward_memory_substitutions: 1,
            backward_memory_candidate_enumerations: 1,
            backward_memory_residual_fallbacks: 0,
            precision: r2sym::BackwardConditionPrecision::Exact,
            supported_paths: 1,
            total_paths: 1,
        }
    }

    fn test_region_with_control(
        anchor: u64,
        target: u64,
        condition: &str,
        compiled: r2sym::BackwardConditionSummary,
    ) -> r2sym::SemanticRegion {
        r2sym::SemanticRegion {
            anchor,
            frontier: BTreeSet::from([target]),
            control: vec![r2sym::Judged::new(
                r2sym::ControlFact {
                    target,
                    status: r2sym::SymbolicReachabilityStatus::Reachable,
                    branch_truth: Some(true),
                    condition: Some(condition.to_string()),
                    compiled: Some(compiled),
                },
                r2sym::SemanticEvidence::exact(),
            )],
            memory: Vec::new(),
            pre: Vec::new(),
            post: Vec::new(),
            targets: vec![r2sym::Judged::new(
                r2sym::TargetFact {
                    target,
                    status: r2sym::SymbolicReachabilityStatus::Reachable,
                    branch_truth: Some(true),
                },
                r2sym::SemanticEvidence::exact(),
            )],
        }
    }

    #[test]
    fn main_name_without_signature_evidence_does_not_fabricate_signature_output() {
        let parsed_context = ParsedExternalContext::default();
        let root = r2ssa::InterprocFunctionId(0x401000);
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(root, Some("dbg.main".to_string()));
        summary.arg_effects.insert(
            0,
            r2ssa::SummaryArgEffect {
                read: true,
                ..Default::default()
            },
        );
        let summary_set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, summary)]),
            diagnostics: Default::default(),
        };
        let input = TypeWritebackAnalysisInput {
            function_name: "sym.main",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.main".to_string(),
                signature: "void sym.main ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        };
        let analysis = build_type_writeback_analysis(input);
        assert_eq!(analysis.signature.ret_type, "void");
        assert!(
            analysis.signature.params.is_empty(),
            "main name alone must not fabricate argc/argv/envp parameters"
        );
        assert!(
            analysis
                .type_facts
                .signature_certificate
                .as_ref()
                .is_none_or(|certificate| !certificate
                    .sources
                    .contains(&SignatureCertificateSource::ExternalContext)),
            "name-only main canonicalization must not create external-context authority"
        );
    }

    #[test]
    fn main_signature_canonicalization_survives_semantic_projection_and_context() {
        let parsed_context = ParsedExternalContext {
            current_signature: Some(FunctionSignatureSpec {
                ret_type: Some(c_int_type()),
                params: vec![
                    FunctionParamSpec {
                        name: "argc".to_string(),
                        ty: Some(signed_byte_pointer_type()),
                    },
                    FunctionParamSpec {
                        name: "argv".to_string(),
                        ty: Some(signed_byte_pointer_pointer_type()),
                    },
                    FunctionParamSpec {
                        name: "envp".to_string(),
                        ty: Some(signed_byte_pointer_pointer_type()),
                    },
                ],
            }),
            ..ParsedExternalContext::default()
        };
        let parsed_context = ParsedExternalContext {
            merged_signature: parsed_context.current_signature.clone(),
            ..parsed_context
        };
        let root = r2ssa::InterprocFunctionId(0x401000);
        let summary = r2ssa::FunctionSemanticSummary::unknown(root, Some("dbg.main".to_string()));
        let summary_set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, summary)]),
            diagnostics: Default::default(),
        };
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::MemoryRead,
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
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::ProgramOrchestrator,
                dst: None,
                src: None,
                memory: None,
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

        let analysis = build_type_writeback_analysis_with_semantics(
            TypeWritebackAnalysisInput {
                function_name: "dbg.main",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "dbg.main".to_string(),
                    signature: "int dbg.main (int8_t* argc, int8_t** argv, int8_t** envp)"
                        .to_string(),
                    ret_type: "int".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "argc".to_string(),
                            param_type: "int8_t*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "argv".to_string(),
                            param_type: "int8_t**".to_string(),
                        },
                        InferredSignatureParam {
                            name: "envp".to_string(),
                            param_type: "int8_t**".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 96,
                    callconv_confidence: 92,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context,
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: Some(summary_set),
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            TypeWritebackSemanticInputs {
                artifact: &artifact,
                local_field_accesses: &[],
            },
        );

        assert_eq!(analysis.signature.params[0].param_type, "int");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .unwrap()
                .params[0]
                .ty
                .as_ref()
                .map(|ty| render_signature_type(ty, 64)),
            Some("int".to_string())
        );
    }

    #[test]
    fn user_type_hint_assumptions_apply_without_semantic_corroboration() {
        let mut parsed_context = ParsedExternalContext {
            assumptions: r2ssa::AssumptionSet::new(vec![r2ssa::AnalysisAssumption {
                id: Some("param0-char-ptr".to_string()),
                subject: r2ssa::AssumptionSubject::Parameter { index: 0 },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "char *".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::User,
            }]),
            ..ParsedExternalContext::default()
        };
        let mut inferred_signature = InferredSignature {
            function_name: "sym.demo".to_string(),
            signature: "void sym.demo(void *)".to_string(),
            ret_type: "void".to_string(),
            params: vec![InferredSignatureParam {
                name: "arg1".to_string(),
                param_type: "void *".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 80,
            callconv_confidence: 80,
        };

        let usage = apply_type_hint_assumptions_to_context(
            &mut parsed_context,
            &mut inferred_signature,
            64,
            Some(&SemanticTypeProjection::default()),
        );

        assert_eq!(usage.applied.len(), 1);
        assert!(usage.ignored.is_empty());
        assert!(usage.conflicts.is_empty());
        assert_eq!(inferred_signature.params[0].param_type, "int8_t*");
        assert_eq!(
            render_signature_type(
                parsed_context
                    .merged_signature
                    .as_ref()
                    .expect("merged signature")
                    .params[0]
                    .ty
                    .as_ref()
                    .expect("hinted param type"),
                64
            ),
            "int8_t*"
        );
    }

    #[test]
    fn derived_type_hint_assumptions_still_require_corroboration() {
        let mut parsed_context = ParsedExternalContext {
            assumptions: r2ssa::AssumptionSet::new(vec![r2ssa::AnalysisAssumption {
                id: Some("param0-char-ptr".to_string()),
                subject: r2ssa::AssumptionSubject::Parameter { index: 0 },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "char *".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::Derived,
            }]),
            ..ParsedExternalContext::default()
        };
        let mut inferred_signature = InferredSignature {
            function_name: "sym.demo".to_string(),
            signature: "void sym.demo(void *)".to_string(),
            ret_type: "void".to_string(),
            params: vec![InferredSignatureParam {
                name: "arg1".to_string(),
                param_type: "void *".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 80,
            callconv_confidence: 80,
        };

        let usage = apply_type_hint_assumptions_to_context(
            &mut parsed_context,
            &mut inferred_signature,
            64,
            Some(&SemanticTypeProjection::default()),
        );

        assert!(usage.applied.is_empty());
        assert_eq!(usage.ignored.len(), 1);
        assert!(usage.conflicts.is_empty());
        assert_eq!(inferred_signature.params[0].param_type, "void *");
        assert!(parsed_context.merged_signature.is_none());
    }

    #[test]
    fn user_type_hint_replaces_weak_pointer_sized_generic_arg() {
        let mut parsed_context = ParsedExternalContext {
            assumptions: r2ssa::AssumptionSet::new(vec![r2ssa::AnalysisAssumption {
                id: Some("rdi-int32".to_string()),
                subject: r2ssa::AssumptionSubject::Register {
                    name: "rdi".to_string(),
                },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "int32_t".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::User,
            }]),
            register_params: vec![crate::context::ExternalRegisterParamSpec {
                name: "arg1".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Signed,
                }),
                reg: "RDI".to_string(),
            }],
            ..ParsedExternalContext::default()
        };
        let mut inferred_signature = InferredSignature {
            function_name: "sym.demo".to_string(),
            signature: "int64_t sym.demo(int64_t)".to_string(),
            ret_type: "int64_t".to_string(),
            params: vec![InferredSignatureParam {
                name: "arg1".to_string(),
                param_type: "int64_t".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 80,
            callconv_confidence: 80,
        };

        let usage = apply_type_hint_assumptions_to_context(
            &mut parsed_context,
            &mut inferred_signature,
            64,
            Some(&SemanticTypeProjection::default()),
        );

        assert_eq!(usage.applied.len(), 1);
        assert!(usage.ignored.is_empty());
        assert!(usage.conflicts.is_empty());
        assert_eq!(inferred_signature.params[0].param_type, "int32_t");
        assert_eq!(
            render_signature_type(
                parsed_context.register_params[0]
                    .ty
                    .as_ref()
                    .expect("register type"),
                64
            ),
            "int32_t"
        );
    }

    #[test]
    fn imported_size_t_type_hint_matches_preserved_source_typedef() {
        let mut parsed_context = ParsedExternalContext {
            assumptions: r2ssa::AssumptionSet::new(vec![r2ssa::AnalysisAssumption {
                id: Some("rsi-size".to_string()),
                subject: r2ssa::AssumptionSubject::Register {
                    name: "rsi".to_string(),
                },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "size_t".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::ImportedContext,
            }]),
            register_params: vec![crate::context::ExternalRegisterParamSpec {
                name: "n".to_string(),
                ty: Some(CTypeLike::Typedef("size_t".to_string())),
                reg: "rsi".to_string(),
            }],
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Typedef("size_t".to_string())),
                params: vec![FunctionParamSpec {
                    name: "n".to_string(),
                    ty: Some(CTypeLike::Typedef("size_t".to_string())),
                }],
            }),
            ..ParsedExternalContext::default()
        };
        let mut inferred_signature = InferredSignature {
            function_name: "sym.scan_example".to_string(),
            signature: "size_t sym.scan_example(size_t n)".to_string(),
            ret_type: "size_t".to_string(),
            params: vec![InferredSignatureParam {
                name: "n".to_string(),
                param_type: "size_t".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 96,
            callconv_confidence: 92,
        };

        let usage = apply_type_hint_assumptions_to_context(
            &mut parsed_context,
            &mut inferred_signature,
            64,
            Some(&SemanticTypeProjection::default()),
        );

        assert_eq!(usage.applied.len(), 1);
        assert!(usage.ignored.is_empty());
        assert!(usage.conflicts.is_empty());
        assert_eq!(
            parsed_context.register_params[0]
                .ty
                .as_ref()
                .map(|ty| render_signature_type(ty, 64))
                .as_deref(),
            Some("size_t")
        );
    }

    #[test]
    fn corroborated_type_hint_assumptions_update_signature_and_usage() {
        let mut parsed_context = ParsedExternalContext {
            assumptions: r2ssa::AssumptionSet::new(vec![r2ssa::AnalysisAssumption {
                id: Some("param0-char-ptr".to_string()),
                subject: r2ssa::AssumptionSubject::Parameter { index: 0 },
                value: r2ssa::AssumptionValue::TypeHint {
                    ty: "char *".to_string(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::User,
            }]),
            ..ParsedExternalContext::default()
        };
        let mut inferred_signature = InferredSignature {
            function_name: "sym.demo".to_string(),
            signature: "void sym.demo(void *)".to_string(),
            ret_type: "void".to_string(),
            params: vec![InferredSignatureParam {
                name: "arg1".to_string(),
                param_type: "void *".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 80,
            callconv_confidence: 80,
        };
        let root = r2ssa::InterprocFunctionId(0x401000);
        let summary_set = InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(
                root,
                FunctionSemanticSummary {
                    id: root,
                    name: Some("sym.demo".to_string()),
                    linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                    arg_count_hint: Some(1),
                    direct_callees: BTreeSet::new(),
                    callsite_count: 0,
                    has_unknown_calls: false,
                    arg_effects: BTreeMap::from([(
                        0,
                        SummaryArgEffect {
                            read: true,
                            write: true,
                            escape: false,
                            free: false,
                        },
                    )]),
                    memory_effects: Vec::new(),
                    transfer_effects: Vec::new(),
                    allocation_effects: Vec::new(),
                    lifetime_effects: Vec::new(),
                    sync_effects: Vec::new(),
                    atomic_effects: Vec::new(),
                    return_relation: SummaryReturnRelation::Void,
                    reads_global_memory: false,
                    writes_global_memory: false,
                    touches_unknown_memory: false,
                },
            )]),
            diagnostics: Default::default(),
        };
        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(Some(summary_set)),
            None,
            64,
        );

        let usage = apply_type_hint_assumptions_to_context(
            &mut parsed_context,
            &mut inferred_signature,
            64,
            Some(&projection),
        );

        assert_eq!(usage.applied.len(), 1);
        assert!(usage.ignored.is_empty());
        assert!(usage.conflicts.is_empty());
        assert_eq!(inferred_signature.params[0].param_type, "int8_t*");
        assert_eq!(
            render_signature_type(
                parsed_context
                    .merged_signature
                    .as_ref()
                    .expect("merged signature")
                    .params[0]
                    .ty
                    .as_ref()
                    .expect("hinted param type"),
                64
            ),
            "int8_t*"
        );
    }

    #[test]
    fn interproc_heap_alloc_summary_upgrades_pointer_sized_scalar_return() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let summary_set = InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(
                root,
                FunctionSemanticSummary {
                    id: root,
                    name: Some("sym.alloc_wrapper".to_string()),
                    linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                    arg_count_hint: Some(1),
                    direct_callees: BTreeSet::from([0x5000]),
                    callsite_count: 1,
                    has_unknown_calls: false,
                    arg_effects: BTreeMap::new(),
                    memory_effects: Vec::new(),
                    transfer_effects: Vec::new(),
                    allocation_effects: Vec::new(),
                    lifetime_effects: Vec::new(),
                    sync_effects: Vec::new(),
                    atomic_effects: Vec::new(),
                    return_relation: SummaryReturnRelation::HeapAlloc,
                    reads_global_memory: false,
                    writes_global_memory: false,
                    touches_unknown_memory: false,
                },
            )]),
            diagnostics: Default::default(),
        };
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.alloc_wrapper",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.alloc_wrapper".to_string(),
                signature: "int64_t sym.alloc_wrapper ()".to_string(),
                ret_type: "int64_t".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "allocation_ptr");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.ret_type.clone()),
            Some(CTypeLike::Typedef("allocation_ptr".to_string()))
        );
    }

    #[test]
    fn interproc_returned_arg_summary_propagates_param_type_and_callee_facts() {
        let root = r2ssa::InterprocFunctionId(0x401100);
        let helper = r2ssa::InterprocFunctionId(0x401200);
        let summary_set = InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([
                (
                    root,
                    FunctionSemanticSummary {
                        id: root,
                        name: Some("sym.identity".to_string()),
                        linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                        arg_count_hint: Some(1),
                        direct_callees: BTreeSet::from([helper.0]),
                        callsite_count: 1,
                        has_unknown_calls: false,
                        arg_effects: BTreeMap::new(),
                        memory_effects: Vec::new(),
                        transfer_effects: Vec::new(),
                        allocation_effects: Vec::new(),
                        lifetime_effects: Vec::new(),
                        sync_effects: Vec::new(),
                        atomic_effects: Vec::new(),
                        return_relation: SummaryReturnRelation::Arg(0),
                        reads_global_memory: false,
                        writes_global_memory: false,
                        touches_unknown_memory: false,
                    },
                ),
                (
                    helper,
                    FunctionSemanticSummary {
                        id: helper,
                        name: Some("sym.helper".to_string()),
                        linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                        arg_count_hint: Some(1),
                        direct_callees: BTreeSet::new(),
                        callsite_count: 0,
                        has_unknown_calls: false,
                        arg_effects: BTreeMap::from([(
                            0,
                            SummaryArgEffect {
                                read: true,
                                write: false,
                                escape: false,
                                free: false,
                            },
                        )]),
                        memory_effects: Vec::new(),
                        transfer_effects: Vec::new(),
                        allocation_effects: Vec::new(),
                        lifetime_effects: Vec::new(),
                        sync_effects: Vec::new(),
                        atomic_effects: Vec::new(),
                        return_relation: SummaryReturnRelation::Arg(0),
                        reads_global_memory: false,
                        writes_global_memory: false,
                        touches_unknown_memory: false,
                    },
                ),
            ]),
            diagnostics: Default::default(),
        };
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.identity",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.identity".to_string(),
                signature: "int64_t sym.identity (char * src)".to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "src".to_string(),
                    param_type: "char *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "int8_t*");
        let callee = analysis
            .type_facts
            .callee_facts
            .get(&helper.0)
            .expect("helper callee fact");
        assert_eq!(callee.name.as_deref(), Some("sym.helper"));
        assert!(callee.arg_effects.get(&0).is_some_and(|effect| effect.read));
        assert_eq!(callee.return_relation, CalleeReturnRelation::Arg(0));
    }

    #[test]
    fn local_inferred_scalar_param_narrows_external_wide_signature() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arg1".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                }),
            }],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let vars = [RecoveredVariable {
            name: "arg0".to_string(),
            kind: "r".to_string(),
            delta: 0,
            var_type: "int32_t".to_string(),
            isarg: true,
            reg: Some("x0".to_string()),
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym._check_secret",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym._check_secret".to_string(),
                signature: "int64_t sym._check_secret (int32_t arg1)".to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "int32_t".to_string(),
                }],
                callconv: String::new(),
                arch: "aarch64".to_string(),
                confidence: 90,
                callconv_confidence: 0,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params[0].param_type, "int32_t");
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        let merged = analysis
            .type_facts
            .merged_signature
            .as_ref()
            .expect("merged signature");
        assert_eq!(
            merged.params[0].ty,
            Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            })
        );
    }

    #[test]
    fn recovered_arg_types_narrow_external_signature_when_local_signature_is_still_wide() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arg1".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                }),
            }],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let vars = [RecoveredVariable {
            name: "arg0".to_string(),
            kind: "r".to_string(),
            delta: 0,
            var_type: "int32_t".to_string(),
            isarg: true,
            reg: Some("x0".to_string()),
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym._check_secret",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym._check_secret".to_string(),
                signature: "int64_t sym._check_secret (uint64_t arg1)".to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "uint64_t".to_string(),
                }],
                callconv: String::new(),
                arch: "aarch64".to_string(),
                confidence: 90,
                callconv_confidence: 0,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params[0].param_type, "int32_t");
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.params.first())
                .and_then(|param| param.ty.clone()),
            Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            })
        );
    }

    #[test]
    fn exact_named_external_size_signature_blocks_local_byte_narrowing() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(typedef_type("size_t")),
            params: vec![
                FunctionParamSpec {
                    name: "buf".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Unsigned,
                    }))),
                },
                FunctionParamSpec {
                    name: "n".to_string(),
                    ty: Some(typedef_type("size_t")),
                },
                FunctionParamSpec {
                    name: "a".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Unsigned,
                    }),
                },
                FunctionParamSpec {
                    name: "b".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Unsigned,
                    }),
                },
            ],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let vars = [RecoveredVariable {
            name: "arg1".to_string(),
            kind: "r".to_string(),
            delta: 0,
            var_type: "uint8_t".to_string(),
            isarg: true,
            reg: Some("rsi".to_string()),
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "dbg.scan_example",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "dbg.scan_example".to_string(),
                signature:
                    "uint8_t dbg.scan_example (uint8_t* buf, uint8_t n, uint8_t a, uint8_t b)"
                        .to_string(),
                ret_type: "uint8_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "buf".to_string(),
                        param_type: "uint8_t*".to_string(),
                    },
                    InferredSignatureParam {
                        name: "n".to_string(),
                        param_type: "uint8_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "a".to_string(),
                        param_type: "uint8_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "b".to_string(),
                        param_type: "uint8_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "size_t");
        assert_eq!(analysis.signature.params[1].name, "n");
        assert_eq!(analysis.signature.params[1].param_type, "size_t");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.params.get(1))
                .and_then(|param| param.ty.clone()),
            Some(typedef_type("size_t"))
        );
    }

    #[test]
    fn authoritative_external_signature_keeps_param_count_over_longer_local_signature() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Signed,
            }))),
            params: vec![
                FunctionParamSpec {
                    name: "src".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Signed,
                    }))),
                },
                FunctionParamSpec {
                    name: "len".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 64,
                        signedness: Signedness::Unsigned,
                    }),
                },
            ],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.alloc_and_copy",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.alloc_and_copy".to_string(),
                signature: "int8_t * sym.alloc_and_copy (int8_t * src, uint8_t len, int64_t arg3, int64_t arg4)".to_string(),
                ret_type: "int8_t *".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "src".to_string(),
                        param_type: "int8_t *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "len".to_string(),
                        param_type: "uint8_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "arg3".to_string(),
                        param_type: "int64_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "arg4".to_string(),
                        param_type: "int64_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params.len(), 2);
        assert_eq!(analysis.signature.params[0].name, "src");
        assert_eq!(analysis.signature.params[1].name, "len");
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(|binding| matches!(binding.kind, VisibleBindingKind::Param)
                    && binding.param_index == Some(0)
                    && binding.name == "src"),
            "expected visible param binding for src, got {:?}",
            analysis.type_facts.visible_bindings
        );
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(|binding| matches!(binding.kind, VisibleBindingKind::Param)
                    && binding.param_index == Some(1)
                    && binding.name == "len"),
            "expected visible param binding for len, got {:?}",
            analysis.type_facts.visible_bindings
        );
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .expect("merged signature")
                .params
                .len(),
            2
        );
    }

    #[test]
    fn stack_var_preference_renames_and_types_generic_stack_slots() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context
            .external_stack_vars
            .insert(-0x10, spec.clone());
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x10,
            },
            spec,
        );
        let vars = [RecoveredVariable {
            name: "var_10h".to_string(),
            kind: "b".to_string(),
            delta: -0x10,
            var_type: "byte[4]".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f".to_string().as_str(),
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: String::new(),
                arch: String::new(),
                confidence: 0,
                callconv_confidence: 0,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        assert_eq!(analysis.plan.var_rename_candidates[0].target_name, "count");
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(|binding| matches!(binding.kind, VisibleBindingKind::Local)
                    && binding
                        .stack_slot
                        .as_ref()
                        .is_some_and(|slot| slot.base == ExternalStackBase::FramePointer
                            && slot.offset == -0x10)
                    && binding.name == "count"),
            "expected visible local binding for count, got {:?}",
            analysis.type_facts.visible_bindings
        );
        let count_binding = analysis
            .type_facts
            .visible_bindings
            .iter()
            .find(|binding| binding.name == "count")
            .expect("count visible binding");
        assert_eq!(
            count_binding.ty,
            Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            "renamed visible locals must keep the strongest canonical type"
        );
    }

    #[test]
    fn visible_binding_merge_prefers_typed_pointer_over_void_pointer() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "buf".to_string(),
            ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x8,
            },
            spec,
        );
        let vars = [
            RecoveredVariable {
                name: "var_8h".to_string(),
                kind: "b".to_string(),
                delta: -0x8,
                var_type: "int8_t *".to_string(),
                isarg: false,
                reg: None,
            },
            RecoveredVariable {
                name: "var_8h".to_string(),
                kind: "s".to_string(),
                delta: 0x8,
                var_type: "int64_t".to_string(),
                isarg: false,
                reg: None,
            },
        ];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f".to_string().as_str(),
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: String::new(),
                arch: String::new(),
                confidence: 0,
                callconv_confidence: 0,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        let binding = analysis
            .type_facts
            .visible_bindings
            .iter()
            .find(|binding| binding.name == "buf")
            .expect("buf visible binding");
        assert_eq!(
            binding.ty,
            Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Signed,
            }))),
            "visible binding merge must keep the typed pointer, got {:?}",
            analysis.type_facts.visible_bindings
        );
    }

    #[test]
    fn param_home_slots_do_not_surface_as_visible_local_writeback_candidates() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "arr_home".to_string(),
            ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::ParamHome,
            param_index: Some(0),
            param_name: Some("arr".to_string()),
            source_reg: Some("rdi".to_string()),
        };
        parsed_context
            .external_stack_vars
            .insert(0x10, spec.clone());
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: 0x10,
            },
            spec,
        );

        let vars = [RecoveredVariable {
            name: "var_10h".to_string(),
            kind: "b".to_string(),
            delta: 0x10,
            var_type: "void *".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert!(
            analysis.plan.var_type_candidates.is_empty(),
            "param-home slots should not emit visible local type candidates: {:?}",
            analysis.plan.var_type_candidates
        );
        assert!(
            analysis.plan.var_rename_candidates.is_empty(),
            "param-home slots should not emit visible local rename candidates: {:?}",
            analysis.plan.var_rename_candidates
        );
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(
                    |binding| matches!(binding.kind, VisibleBindingKind::HiddenHome)
                        && binding.name == "arr_home"
                ),
            "expected hidden param-home binding, got {:?}",
            analysis.type_facts.visible_bindings
        );
    }

    #[test]
    fn unproven_stack_pointer_zero_slot_is_hidden_saved_frame_state() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::StackPointer,
                offset: 0,
            },
            ExternalStackVarSpec {
                name: "var_8h".to_string(),
                ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
                base: ExternalStackBase::StackPointer,
                role: ExternalStackSlotRole::Unknown,
                param_index: None,
                param_name: None,
                source_reg: None,
            },
        );
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -8,
            },
            ExternalStackVarSpec {
                name: "arr".to_string(),
                ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
                base: ExternalStackBase::FramePointer,
                role: ExternalStackSlotRole::ParamHome,
                param_index: Some(0),
                param_name: Some("arr".to_string()),
                source_reg: Some("rdi".to_string()),
            },
        );

        let vars = [RecoveredVariable {
            name: "var_8h".to_string(),
            kind: "s".to_string(),
            delta: 0,
            var_type: "void *".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature:
                    "int32_t sym.test_struct_array_index(void * arr, int32_t idx, int32_t v)"
                        .to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "arr".to_string(),
                        param_type: "void *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "idx".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "v".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        let slot = analysis
            .type_facts
            .stack_slots
            .get(&StackSlotKey {
                base: ExternalStackBase::StackPointer,
                offset: 0,
            })
            .expect("canonicalized stack slot");
        assert_eq!(slot.role, ExternalStackSlotRole::SavedFp);
        assert_eq!(slot.name, "saved_fp");
        assert!(
            analysis.plan.var_type_candidates.is_empty(),
            "hidden saved frame state must not emit visible type candidates: {:?}",
            analysis.plan.var_type_candidates
        );
        assert!(
            analysis.plan.var_rename_candidates.is_empty(),
            "hidden saved frame state must not emit visible rename candidates: {:?}",
            analysis.plan.var_rename_candidates
        );
        assert!(
            analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(
                    |binding| matches!(binding.kind, VisibleBindingKind::HiddenSaved)
                        && binding.name == "saved_fp"
                ),
            "expected hidden saved-frame binding, got {:?}",
            analysis.type_facts.visible_bindings
        );
        assert!(
            !analysis
                .type_facts
                .visible_bindings
                .iter()
                .any(|binding| binding.name == "var_8h"),
            "raw stack artifact name must not remain visible: {:?}",
            analysis.type_facts.visible_bindings
        );
    }

    #[test]
    fn generic_unknown_param_home_slots_are_canonicalized_from_entry_stores() {
        let mut parsed_context = ParsedExternalContext {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                }),
                params: vec![
                    FunctionParamSpec {
                        name: "arr".to_string(),
                        ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
                    },
                    FunctionParamSpec {
                        name: "idx".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 32,
                            signedness: Signedness::Signed,
                        }),
                    },
                    FunctionParamSpec {
                        name: "v".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 32,
                            signedness: Signedness::Signed,
                        }),
                    },
                ],
            }),
            register_params: vec![
                crate::context::ExternalRegisterParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
                    reg: "rdi".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "arg2".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    reg: "rsi".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "arg3".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    reg: "rdx".to_string(),
                },
            ],
            ..Default::default()
        };
        for (offset, name) in [(-8, "arr"), (-12, "var_ch"), (-16, "var_10h")] {
            parsed_context.stack_slots.insert(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset,
                },
                ExternalStackVarSpec {
                    name: name.to_string(),
                    ty: None,
                    base: ExternalStackBase::FramePointer,
                    role: ExternalStackSlotRole::Unknown,
                    param_index: None,
                    param_name: None,
                    source_reg: None,
                },
            );
        }

        let ssa_blocks = [SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 1, 8),
                    val: SSAVar::new("RDI", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 2, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 2, 8),
                    val: SSAVar::new("ESI", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 3, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 3, 8),
                    val: SSAVar::new("EDX", 0, 4),
                },
            ],
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature:
                    "int32_t sym.test_struct_array_index(void * arr, int32_t idx, int32_t v)"
                        .to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "arr".to_string(),
                        param_type: "void *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "idx".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "v".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &ssa_blocks,
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        for (offset, expected_name, expected_idx) in
            [(-8, "arr", 0usize), (-12, "idx", 1), (-16, "v", 2)]
        {
            let slot = analysis
                .type_facts
                .stack_slots
                .get(&StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset,
                })
                .expect("canonicalized slot");
            assert_eq!(slot.role, ExternalStackSlotRole::ParamHome);
            assert_eq!(slot.param_index, Some(expected_idx));
            assert_eq!(slot.param_name.as_deref(), Some(expected_name));
        }
    }

    #[test]
    fn generic_unknown_param_home_slots_are_canonicalized_from_entry_store_copies() {
        let mut parsed_context = ParsedExternalContext {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: Signedness::Signed,
                }),
                params: vec![
                    FunctionParamSpec {
                        name: "arr".to_string(),
                        ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
                    },
                    FunctionParamSpec {
                        name: "idx".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 32,
                            signedness: Signedness::Signed,
                        }),
                    },
                    FunctionParamSpec {
                        name: "v".to_string(),
                        ty: Some(CTypeLike::Int {
                            bits: 32,
                            signedness: Signedness::Signed,
                        }),
                    },
                ],
            }),
            register_params: vec![
                crate::context::ExternalRegisterParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Unknown))),
                    reg: "rdi".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "arg2".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    reg: "rsi".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "arg3".to_string(),
                    ty: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    reg: "rdx".to_string(),
                },
            ],
            ..Default::default()
        };
        for (offset, name) in [(-8, "arr"), (-12, "var_ch"), (-16, "var_10h")] {
            parsed_context.stack_slots.insert(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset,
                },
                ExternalStackVarSpec {
                    name: name.to_string(),
                    ty: None,
                    base: ExternalStackBase::FramePointer,
                    role: ExternalStackSlotRole::Unknown,
                    param_index: None,
                    param_name: None,
                    source_reg: None,
                },
            );
        }

        let ssa_blocks = [SSABlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:spill_arr", 1, 8),
                    src: SSAVar::new("RDI", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 1, 8),
                    val: SSAVar::new("tmp:spill_arr", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 2, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:spill_idx", 1, 4),
                    src: SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 2, 8),
                    val: SSAVar::new("tmp:spill_idx", 1, 4),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot", 3, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff0", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:spill_v", 1, 4),
                    src: SSAVar::new("EDX", 0, 4),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot", 3, 8),
                    val: SSAVar::new("tmp:spill_v", 1, 4),
                },
            ],
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature:
                    "int32_t sym.test_struct_array_index(void * arr, int32_t idx, int32_t v)"
                        .to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "arr".to_string(),
                        param_type: "void *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "idx".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "v".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &ssa_blocks,
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        for (offset, expected_name, expected_idx) in
            [(-8, "arr", 0usize), (-12, "idx", 1), (-16, "v", 2)]
        {
            let slot = analysis
                .type_facts
                .stack_slots
                .get(&StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset,
                })
                .expect("canonicalized slot");
            assert_eq!(slot.role, ExternalStackSlotRole::ParamHome);
            assert_eq!(slot.param_index, Some(expected_idx));
            assert_eq!(slot.param_name.as_deref(), Some(expected_name));
        }
    }

    #[test]
    fn writeback_does_not_cross_apply_frame_slots_to_stack_pointer_temps() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "len".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Unsigned,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context.external_stack_vars.insert(-8, spec.clone());
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -8,
            },
            spec,
        );

        let vars = [RecoveredVariable {
            name: "var_8h".to_string(),
            kind: "s".to_string(),
            delta: -8,
            var_type: "void *".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.plan.var_type_candidates.len(), 1);
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "void *");
        assert_eq!(
            analysis.plan.var_type_candidates[0].source,
            WritebackSource::LocalInferred
        );
        assert!(
            analysis.plan.var_rename_candidates.is_empty(),
            "stack-pointer temps must not inherit frame-slot names: {:?}",
            analysis.plan.var_rename_candidates
        );
    }

    #[test]
    fn writeback_does_not_use_offset_only_legacy_slots_when_canonical_slots_exist() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "len".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Unsigned,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context.external_stack_vars.insert(-8, spec.clone());
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -8,
            },
            spec,
        );

        let vars = [RecoveredVariable {
            name: "var_8h".to_string(),
            kind: "x".to_string(),
            delta: -8,
            var_type: "void *".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.plan.var_type_candidates.len(), 1);
        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "void *");
        assert_eq!(
            analysis.plan.var_type_candidates[0].source,
            WritebackSource::LocalInferred
        );
        assert!(
            analysis.plan.var_rename_candidates.is_empty(),
            "unknown-base recovered vars must not inherit names from offset-only legacy slots when canonical slots exist: {:?}",
            analysis.plan.var_rename_candidates
        );
    }

    #[test]
    fn writeback_canonicalizes_legacy_only_stack_var_input() {
        let mut parsed_context = ParsedExternalContext::default();
        let spec = ExternalStackVarSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        parsed_context.external_stack_vars.insert(-0x10, spec);

        let vars = [RecoveredVariable {
            name: "var_10h".to_string(),
            kind: "b".to_string(),
            delta: -0x10,
            var_type: "byte[4]".to_string(),
            isarg: false,
            reg: None,
        }];
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &vars,
            ssa_blocks: &[],
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.plan.var_type_candidates[0].var_type, "int32_t");
        assert_eq!(analysis.plan.var_rename_candidates[0].target_name, "count");
        assert!(
            analysis.type_facts.stack_slots.contains_key(&StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x10,
            }),
            "legacy-only input should be canonicalized into stack_slots: {:?}",
            analysis.type_facts.stack_slots
        );
    }

    #[test]
    fn local_external_struct_reconciliation_prefers_external_names() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.external_type_db.structs.insert(
            "node".to_string(),
            ExternalStruct {
                name: "node".to_string(),
                fields: BTreeMap::from([
                    (
                        0,
                        ExternalField {
                            name: "value".to_string(),
                            offset: 0,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        8,
                        ExternalField {
                            name: "next".to_string(),
                            offset: 8,
                            ty: Some("struct node *".to_string()),
                        },
                    ),
                ]),
            },
        );
        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_deadbeef".to_string(),
                decl: "struct sla_struct_deadbeef { int32_t f_0; struct node *f_8; };".to_string(),
                confidence: 90,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_0".to_string(),
                        offset: 0,
                        field_type: "int32_t".to_string(),
                        confidence: 90,
                    },
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "struct node *".to_string(),
                        confidence: 90,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                0usize,
                "struct sla_struct_deadbeef *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (0u64, "int32_t".to_string()),
                    (8u64, "struct node *".to_string()),
                ]),
            )]),
        };
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.f",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.f".to_string(),
                signature: "void sym.f ()".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: String::new(),
                arch: String::new(),
                confidence: 0,
                callconv_confidence: 0,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });
        assert_eq!(
            analysis
                .type_facts
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct node *")
        );
    }

    #[test]
    fn local_generated_struct_replaces_stale_generated_external_layout() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.external_type_db.structs.insert(
            "sla_struct_420703e08f70f00e".to_string(),
            ExternalStruct {
                name: "sla_struct_420703e08f70f00e".to_string(),
                fields: BTreeMap::from([
                    (
                        0,
                        ExternalField {
                            name: "_pad_0".to_string(),
                            offset: 0,
                            ty: Some("uint8_t".to_string()),
                        },
                    ),
                    (
                        4,
                        ExternalField {
                            name: "f_8".to_string(),
                            offset: 4,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        8,
                        ExternalField {
                            name: "_pad_c".to_string(),
                            offset: 8,
                            ty: Some("uint8_t".to_string()),
                        },
                    ),
                    (
                        12,
                        ExternalField {
                            name: "f_34".to_string(),
                            offset: 12,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                ]),
            },
        );
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arr".to_string(),
                ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
            }],
        });

        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_420703e08f70f00e".to_string(),
                decl: "struct sla_struct_420703e08f70f00e { int32_t f_8; int32_t f_34; };"
                    .to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidate {
                        name: "f_34".to_string(),
                        offset: 0x34,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                0usize,
                "struct sla_struct_420703e08f70f00e *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (8u64, "int32_t".to_string()),
                    (0x34u64, "int32_t".to_string()),
                ]),
            )]),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature: "int32_t sym.test_struct_array_index (void * arr)".to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arr".to_string(),
                    param_type: "void *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        let struct_entry = analysis
            .type_facts
            .external_type_db
            .structs
            .get("sla_struct_420703e08f70f00e")
            .expect("expected merged local struct entry");
        assert_eq!(
            struct_entry.fields.get(&8).map(|field| field.name.as_str()),
            Some("f_8")
        );
        assert_eq!(
            struct_entry
                .fields
                .get(&0x34)
                .map(|field| field.name.as_str()),
            Some("f_34")
        );
        assert!(
            !struct_entry.fields.contains_key(&4) && !struct_entry.fields.contains_key(&12),
            "stale generated external layout should be replaced, got {:?}",
            struct_entry.fields
        );
        assert!(
            analysis
                .plan
                .struct_decls
                .iter()
                .find(|decl| decl.name == "sla_struct_420703e08f70f00e")
                .is_some_and(|decl| decl.source == StructDeclSource::LocalInferred),
            "expected plan to keep the current local synthetic struct"
        );
    }

    #[test]
    fn debug_typedef_alias_beats_generated_local_struct_override() {
        let parsed_context = crate::parse_external_context_json(
            r#"{
                "signature":{
                    "ret":"int32_t",
                    "params":[{"name":"arr","type":"DemoStruct *"}]
                },
                "base_types":[
                    {
                        "kind":"struct",
                        "name":"type_0x261",
                        "members":[
                            {"name":"third","type":"int","offset":8},
                            {"name":"fourteenth","type":"int","offset":52}
                        ]
                    },
                    {"kind":"typedef","name":"DemoStruct","type":"type_0x261"}
                ]
            }"#,
            64,
        );
        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_420703e08f70f00e".to_string(),
                decl: "struct sla_struct_420703e08f70f00e { int32_t f_8; int32_t f_34; };"
                    .to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidate {
                        name: "f_34".to_string(),
                        offset: 0x34,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                0usize,
                "struct sla_struct_420703e08f70f00e *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (8u64, "int32_t".to_string()),
                    (0x34u64, "int32_t".to_string()),
                ]),
            )]),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature: "int32_t sym.test_struct_array_index (void * arr)".to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arr".to_string(),
                    param_type: "void *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params[0].param_type, "DemoStruct*");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|signature| signature.params[0].ty.as_ref()),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Typedef(
                "DemoStruct".to_string()
            ))))
        );
        let external = analysis
            .type_facts
            .external_type_db
            .structs
            .get("demostruct")
            .expect("typedef-backed struct alias");
        assert_eq!(
            external.fields.get(&8).map(|field| field.name.as_str()),
            Some("third")
        );
        assert_eq!(
            external.fields.get(&0x34).map(|field| field.name.as_str()),
            Some("fourteenth")
        );
        assert!(
            !analysis
                .type_facts
                .slot_type_overrides
                .values()
                .any(|ty| ty.contains("sla_struct_")),
            "source typedef layout should prevent selected synthetic struct overrides"
        );
        assert_eq!(
            analysis.type_facts.array_index_certificates,
            vec![
                ArrayIndexCertificate {
                    slot: 0,
                    base: Some(ArrayIndexBase::Param { index: 0 }),
                    field_offset: 8,
                    element_stride: 56,
                },
                ArrayIndexCertificate {
                    slot: 0,
                    base: Some(ArrayIndexBase::Param { index: 0 }),
                    field_offset: 0x34,
                    element_stride: 56,
                },
            ],
            "source typedef layout plus local indexed field evidence should certify struct-array indexing"
        );
        let signature_certificate = analysis
            .type_facts
            .signature_certificate
            .as_ref()
            .expect("strong typed external signature should produce SignatureCertificate");
        assert!(
            signature_certificate
                .sources
                .contains(&SignatureCertificateSource::ExternalContext),
            "strong typed external signature certificate should record its source"
        );
    }

    #[test]
    fn unresolved_named_pointer_materializes_local_struct_layout() {
        let mut parsed_context = crate::parse_external_context_json(
            r#"{
                "signature":{
                    "ret":"int32_t",
                    "params":[{"name":"obj","type":"DemoStruct *"}]
                }
            }"#,
            64,
        );
        parsed_context.external_type_db.structs.insert(
            "demostruct".to_string(),
            ExternalStruct {
                name: "DemoStruct".to_string(),
                fields: BTreeMap::new(),
            },
        );

        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_420703e08f70f00e".to_string(),
                decl: "struct sla_struct_420703e08f70f00e { int32_t f_0; int32_t f_c; };"
                    .to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_0".to_string(),
                        offset: 0,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidate {
                        name: "f_c".to_string(),
                        offset: 12,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                0usize,
                "struct sla_struct_420703e08f70f00e *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (0u64, "int32_t".to_string()),
                    (12u64, "int32_t".to_string()),
                ]),
            )]),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_demo_struct",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_demo_struct".to_string(),
                signature: "int32_t sym.test_demo_struct (void * obj)".to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "obj".to_string(),
                    param_type: "void *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 90,
                callconv_confidence: 90,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params[0].param_type, "DemoStruct*");
        let layout = analysis
            .type_facts
            .external_type_db
            .structs
            .get("demostruct")
            .expect("unresolved signature type should receive inferred layout");
        assert_eq!(
            layout.fields.get(&0).map(|field| field.name.as_str()),
            Some("f_0")
        );
        assert_eq!(
            layout.fields.get(&12).map(|field| field.name.as_str()),
            Some("f_c")
        );
        assert_eq!(
            analysis
                .type_facts
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct DemoStruct *")
        );
        assert!(
            !analysis
                .type_facts
                .slot_type_overrides
                .values()
                .any(|ty| ty.contains("sla_struct_")),
            "unresolved named signature type should own the materialized layout"
        );
        assert_eq!(
            analysis.type_facts.array_index_certificates,
            vec![
                ArrayIndexCertificate {
                    slot: 0,
                    base: Some(ArrayIndexBase::Param { index: 0 }),
                    field_offset: 0,
                    element_stride: 16,
                },
                ArrayIndexCertificate {
                    slot: 0,
                    base: Some(ArrayIndexBase::Param { index: 0 }),
                    field_offset: 12,
                    element_stride: 16,
                },
            ],
            "materialized layout should keep struct-array indexing evidence"
        );
    }

    #[test]
    fn inferred_signature_certificate_records_local_source() {
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.local_exact",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.local_exact".to_string(),
                signature: "int32_t sym.local_exact (int32_t value)".to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "value".to_string(),
                    param_type: "int32_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        let signature_certificate = analysis
            .type_facts
            .signature_certificate
            .as_ref()
            .expect("exact local inferred signature should carry a certificate");
        assert_eq!(
            signature_certificate.sources,
            vec![SignatureCertificateSource::LocalInference]
        );
    }

    #[test]
    fn local_struct_override_replaces_weak_generic_ptr_sized_integer_param() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.current_signature = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            params: vec![FunctionParamSpec {
                name: "arg1".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Signed,
                }),
            }],
        });
        parsed_context.merged_signature = parsed_context.current_signature.clone();

        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_deadbeef".to_string(),
                decl: "struct sla_struct_deadbeef { int32_t f_8; int32_t f_34; };".to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidate {
                        name: "f_34".to_string(),
                        offset: 52,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                0usize,
                "struct sla_struct_deadbeef *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (8u64, "int32_t".to_string()),
                    (52u64, "int32_t".to_string()),
                ]),
            )]),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.test_struct_array_index",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.test_struct_array_index".to_string(),
                signature: "int32_t sym.test_struct_array_index (int64_t arg1)".to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "int64_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context,
            local_structs,
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(
            analysis
                .type_facts
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct sla_struct_deadbeef *")
        );
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.params.first())
                .and_then(|param| param.ty.as_ref()),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Struct(
                "sla_struct_deadbeef".to_string(),
            ))))
        );
    }

    #[test]
    fn interproc_heap_alloc_summary_upgrades_generic_return_type() {
        let mut summary_set = r2ssa::InterprocSummarySet::default();
        let root = r2ssa::InterprocFunctionId(0x401000);
        summary_set.root = Some(root);
        summary_set.summaries.insert(
            root,
            r2ssa::FunctionSemanticSummary {
                id: root,
                name: Some("sym.alloc_wrapper".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                arg_count_hint: Some(1),
                direct_callees: BTreeSet::new(),
                callsite_count: 1,
                has_unknown_calls: false,
                arg_effects: BTreeMap::new(),
                memory_effects: Vec::new(),
                transfer_effects: Vec::new(),
                allocation_effects: Vec::new(),
                lifetime_effects: Vec::new(),
                sync_effects: Vec::new(),
                atomic_effects: Vec::new(),
                return_relation: r2ssa::SummaryReturnRelation::HeapAlloc,
                reads_global_memory: false,
                writes_global_memory: false,
                touches_unknown_memory: false,
            },
        );
        summary_set.diagnostics = r2ssa::InterprocSummaryDiagnostics {
            iterations: 2,
            max_iterations: 8,
            converged: true,
            scope_size: 1,
            scc_count: 1,
            max_scc_size: 1,
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.alloc_wrapper",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.alloc_wrapper".to_string(),
                signature: "void * sym.alloc_wrapper (int64_t n)".to_string(),
                ret_type: "unknown_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "n".to_string(),
                    param_type: "int64_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.ret_type.as_ref()),
            Some(&CTypeLike::Typedef("allocation_ptr".to_string()))
        );
        assert_eq!(analysis.type_facts.interproc_diagnostics.scope_size, 1);
    }

    #[test]
    fn interproc_void_return_summary_replaces_weak_scalar_return_type() {
        let mut summary_set = r2ssa::InterprocSummarySet::default();
        let root = r2ssa::InterprocFunctionId(0x401500);
        summary_set.root = Some(root);
        summary_set.summaries.insert(
            root,
            r2ssa::FunctionSemanticSummary {
                id: root,
                name: Some("sym.side_effect_worker".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                arg_count_hint: Some(1),
                direct_callees: BTreeSet::new(),
                callsite_count: 0,
                has_unknown_calls: false,
                arg_effects: BTreeMap::new(),
                memory_effects: Vec::new(),
                transfer_effects: Vec::new(),
                allocation_effects: Vec::new(),
                lifetime_effects: Vec::new(),
                sync_effects: Vec::new(),
                atomic_effects: Vec::new(),
                return_relation: r2ssa::SummaryReturnRelation::Void,
                reads_global_memory: false,
                writes_global_memory: false,
                touches_unknown_memory: false,
            },
        );

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.side_effect_worker",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.side_effect_worker".to_string(),
                signature: "int64_t sym.side_effect_worker (int64_t arg1)".to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "int64_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 70,
                callconv_confidence: 70,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "void");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.ret_type.as_ref()),
            Some(&CTypeLike::Void)
        );
    }

    fn semantic_role_summary_set(
        name: &str,
        arg_count_hint: Option<usize>,
    ) -> r2ssa::InterprocSummarySet {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let mut summary = r2ssa::FunctionSemanticSummary::unknown(root, Some(name.to_string()));
        summary.arg_count_hint = arg_count_hint;
        summary.reads_global_memory = true;
        r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, summary)]),
            diagnostics: Default::default(),
        }
    }

    #[test]
    fn interproc_summary_name_does_not_project_role_out_param_type() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(root, Some("dbg.open_input_files".to_string()));
        summary.arg_count_hint = Some(3);
        summary.arg_effects.insert(
            2,
            r2ssa::SummaryArgEffect {
                read: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        let summary_set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, summary.clone())]),
            diagnostics: Default::default(),
        };
        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(Some(summary_set)),
            None,
            64,
        );

        assert!(!projection.param_type_hints.contains_key(&2));
        assert!(projection.pointer_param_indices.contains(&2));
        assert!(!projection.out_param_indices.contains(&2));
        assert!(projection.refusal_warnings().is_empty());

        summary.arg_effects.insert(
            2,
            r2ssa::SummaryArgEffect {
                write: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        let summary_set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, summary)]),
            diagnostics: Default::default(),
        };
        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(Some(summary_set)),
            None,
            64,
        );

        assert!(projection.out_param_indices.contains(&2));
        assert!(!projection.param_type_hints.contains_key(&2));
        assert!(projection.refusal_warnings().is_empty());
    }

    #[test]
    fn interproc_escape_only_does_not_certify_out_param() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(root, Some("sym.escape_user".to_string()));
        summary.arg_count_hint = Some(1);
        summary.arg_effects.insert(
            0,
            r2ssa::SummaryArgEffect {
                escape: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        let summary_set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, summary)]),
            diagnostics: Default::default(),
        };
        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(Some(summary_set.clone())),
            None,
            64,
        );

        assert!(projection.pointer_param_indices.contains(&0));
        assert!(!projection.out_param_indices.contains(&0));
        assert!(!projection.out_param_evidence.contains_key(&0));

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.escape_user",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.escape_user".to_string(),
                signature: "void sym.escape_user (int64_t p)".to_string(),
                ret_type: "void".to_string(),
                params: vec![InferredSignatureParam {
                    name: "p".to_string(),
                    param_type: "int64_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 70,
                callconv_confidence: 70,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert!(
            analysis.type_facts.out_param_certificates.is_empty(),
            "escape proves pointer flow, not writeback"
        );
    }

    #[test]
    fn interproc_arg_write_out_param_certificate_records_write_evidence() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(root, Some("sym.write_user".to_string()));
        summary.arg_count_hint = Some(1);
        summary.arg_effects.insert(
            0,
            r2ssa::SummaryArgEffect {
                write: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        let summary_set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, summary)]),
            diagnostics: Default::default(),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.write_user",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.write_user".to_string(),
                signature: "void sym.write_user (void *out)".to_string(),
                ret_type: "void".to_string(),
                params: vec![InferredSignatureParam {
                    name: "out".to_string(),
                    param_type: "void *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.type_facts.out_param_certificates.len(), 1);
        let cert = &analysis.type_facts.out_param_certificates[0];
        assert_eq!(cert.param_index, 0);
        assert_eq!(cert.param_name, "out");
        assert_eq!(cert.pointee_type.as_deref(), Some("void"));
        assert_eq!(
            cert.evidence,
            vec![OutParamCertificateEvidence::InterprocArgWrite]
        );
        assert_eq!(
            cert.sources,
            vec![OutParamCertificateSource::InterprocSummaryEffect {
                function_id: root.0,
                evidence: OutParamCertificateEvidence::InterprocArgWrite,
                param_index: 0,
                effect_index: 0,
            }]
        );
    }

    #[test]
    fn interproc_memory_write_out_param_certificate_records_memory_write_evidence() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(root, Some("sym.write_user".to_string()));
        summary.arg_count_hint = Some(1);
        summary.memory_effects.push(r2ssa::SummaryMemoryEffect {
            kind: r2ssa::SummaryMemoryEffectKind::Write,
            location: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                range: Some(r2ssa::SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 3,
                    width: Some(4),
                }),
            },
        });
        let summary_set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, summary)]),
            diagnostics: Default::default(),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.write_user",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.write_user".to_string(),
                signature: "void sym.write_user (void *out)".to_string(),
                ret_type: "void".to_string(),
                params: vec![InferredSignatureParam {
                    name: "out".to_string(),
                    param_type: "void *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.type_facts.out_param_certificates.len(), 1);
        let cert = &analysis.type_facts.out_param_certificates[0];
        assert_eq!(cert.param_index, 0);
        assert_eq!(cert.param_name, "out");
        assert_eq!(
            cert.evidence,
            vec![OutParamCertificateEvidence::InterprocMemoryWrite]
        );
        assert_eq!(
            cert.sources,
            vec![OutParamCertificateSource::InterprocSummaryEffect {
                function_id: root.0,
                evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                param_index: 0,
                effect_index: 0,
            }]
        );
    }

    #[test]
    fn name_hint_worker_summary_does_not_project_type_hints() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::FormatRender,
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
                evidence: r2sym::SemanticEvidence::heuristic(
                    r2sym::SemanticEvidenceReason::NameHint,
                ),
            });

        let projection = SemanticTypeProjection::from_inputs(
            &InterprocSummaryView::new(None),
            Some(&artifact),
            64,
        );

        assert!(projection.param_name_hints.is_empty());
        assert!(projection.param_type_hints.is_empty());
        assert!(projection.pointer_param_indices.is_empty());
    }

    #[test]
    fn worker_summary_type_projection_requires_exact_summary_role_certificate() {
        let summary = r2sym::NativeWorkerSummary {
            anchor: 0x401000,
            kind: r2sym::NativeWorkerSummaryKind::FormatRender,
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
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
        };
        let mut other_summary = summary.clone();
        other_summary.memory = Some(r2ssa::SummaryMemoryLocation {
            region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
            range: None,
        });

        let mut projection = SemanticTypeProjection::default();
        let certified = BTreeSet::from([SummaryRoleKey::from_worker_summary(&other_summary)]);
        collect_worker_summary_type_hints(&summary, &mut projection, 64, &certified);
        assert!(projection.param_name_hints.is_empty());
        assert!(projection.param_type_hints.is_empty());
        assert!(projection.pointer_param_indices.is_empty());

        let mut projection = SemanticTypeProjection::default();
        let certified = BTreeSet::from([SummaryRoleKey::from_worker_summary(&summary)]);
        collect_worker_summary_type_hints(&summary, &mut projection, 64, &certified);
        assert_eq!(
            projection.param_name_hints.get(&0).map(String::as_str),
            Some("format_input")
        );
        assert!(projection.pointer_param_indices.contains(&0));
    }

    #[test]
    fn native_worker_out_param_certificate_records_exact_summary_source() {
        let summary = r2sym::NativeWorkerSummary {
            anchor: 0x401000,
            kind: r2sym::NativeWorkerSummaryKind::NumericTransform,
            dst: Some(r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                range: None,
            }),
            src: None,
            memory: None,
            len: None,
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: None,
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
        };
        let mut projection = SemanticTypeProjection::default();
        let certified = BTreeSet::from([SummaryRoleKey::from_worker_summary(&summary)]);

        collect_worker_summary_type_hints(&summary, &mut projection, 64, &certified);

        assert!(projection.out_param_indices.contains(&0));
        assert_eq!(
            projection
                .out_param_sources
                .get(&0)
                .cloned()
                .unwrap_or_default(),
            BTreeSet::from([OutParamCertificateSource::NativeWorkerSummary {
                stable_id: summary.summary_role_certificate_id(),
                anchor: summary.anchor,
                summary_kind: summary.kind,
                param_index: 0,
            }])
        );
    }

    #[test]
    fn native_summary_memory_writes_project_external_field_certificates() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        for (offset, width) in [(0, 4), (8, 8)] {
            native
                .summary
                .worker_summaries
                .push(r2sym::NativeWorkerSummary {
                    anchor: 0x401000 + offset,
                    kind: r2sym::NativeWorkerSummaryKind::MemoryWrite,
                    dst: None,
                    src: None,
                    memory: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                        range: Some(r2ssa::SummaryMemoryRange {
                            offset_lo: offset as i64,
                            offset_hi: offset as i64,
                            width: Some(width),
                        }),
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
        let mut type_db = ExternalTypeDb::default();
        type_db.structs.insert(
            "result".to_string(),
            ExternalStruct {
                name: "Result".to_string(),
                fields: BTreeMap::from([
                    (
                        0,
                        ExternalField {
                            name: "code".to_string(),
                            offset: 0,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        8,
                        ExternalField {
                            name: "hash".to_string(),
                            offset: 8,
                            ty: Some("uint64_t".to_string()),
                        },
                    ),
                ]),
            },
        );

        let analysis = build_type_writeback_analysis_with_semantics(
            TypeWritebackAnalysisInput {
                function_name: "sym.out_param_parse",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.out_param_parse".to_string(),
                    signature: "int32_t sym.out_param_parse (int8_t* s, Result* out)".to_string(),
                    ret_type: "int32_t".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "s".to_string(),
                            param_type: "int8_t*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "out".to_string(),
                            param_type: "Result*".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 95,
                    callconv_confidence: 90,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext {
                    external_type_db: type_db,
                    ..ParsedExternalContext::default()
                },
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            TypeWritebackSemanticInputs {
                artifact: &artifact,
                local_field_accesses: &[],
            },
        );

        let fields = analysis
            .type_facts
            .field_access_certificates
            .iter()
            .map(|cert| (cert.slot, cert.field_offset, cert.field_name.as_str()))
            .collect::<BTreeSet<_>>();
        assert!(fields.contains(&(1, 0, "code")));
        assert!(fields.contains(&(1, 8, "hash")));
    }

    #[test]
    fn mixed_name_hint_worker_does_not_drive_summary_kind_signature() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::FormatArgumentFetch,
                dst: None,
                src: None,
                memory: None,
                len: None,
                allocation: None,
                lifetime: None,
                sync: None,
                atomic: None,
                parser: None,
                loop_summary: None,
                evidence: r2sym::SemanticEvidence::heuristic(
                    r2sym::SemanticEvidenceReason::NameHint,
                ),
            });
        native
            .summary
            .region_summaries
            .push(r2sym::NativeRegionSummary {
                stable_id: 0x401020,
                anchor: 0x401020,
                kind: r2sym::NativeWorkerSummaryKind::StringScan,
                blocks: BTreeSet::from([0x401020]),
                entries: BTreeSet::from([0x401020]),
                exits: BTreeSet::new(),
                memory_accesses: vec![r2sym::NativeMemoryAccessSummary {
                    kind: r2sym::NativeMemoryAccessKind::Read,
                    location: Some(r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: None,
                    }),
                    dst: None,
                    src: None,
                    len: None,
                    width: Some(1),
                }],
                loop_summary: Some(r2sym::NativeLoopSummary {
                    header: 0x401020,
                    body: BTreeSet::from([0x401020]),
                    entries: BTreeSet::from([0x401020]),
                    exits: BTreeSet::new(),
                    iterations: None,
                    length_arg: Some(1),
                    stride: Some(1),
                    terminator: Some(r2sym::NativeWorkerTerminator::ZeroByte),
                }),
                reductions: Vec::new(),
                parser: None,
                residual_reasons: Vec::new(),
                confidence: r2sym::SemanticConfidence::Likely,
                evidence: r2sym::SemanticEvidence::likely(
                    r2sym::SemanticEvidenceReason::SummaryBudget,
                ),
            });

        let mut signature = InferredSignature {
            function_name: "sym.mixed_summary".to_string(),
            signature: "int64_t sym.mixed_summary(int64_t arg1, int64_t arg2, int64_t arg3)"
                .to_string(),
            ret_type: "int64_t".to_string(),
            params: vec![
                InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "int64_t".to_string(),
                },
                InferredSignatureParam {
                    name: "arg2".to_string(),
                    param_type: "int64_t".to_string(),
                },
                InferredSignatureParam {
                    name: "arg3".to_string(),
                    param_type: "int64_t".to_string(),
                },
            ],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 40,
            callconv_confidence: 40,
        };

        assert!(apply_semantic_artifact_signature_hint_to_inferred(
            &mut signature,
            &artifact,
            64
        ));
        assert_eq!(signature.params[0].name, "string");
        assert_eq!(signature.params[1].name, "len");
        assert_eq!(signature.params[2].name, "flags");
        assert!(
            signature
                .params
                .iter()
                .all(|param| param.name != "arguments_out")
        );
        assert_eq!(
            signature.ret_type, "int64_t",
            "name-hint format-fetch summary must not replace the return type"
        );
    }

    #[test]
    fn name_hint_role_identity_does_not_apply_signature_hint() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native.summary.role_identity = Some(Box::new(r2sym::NativeWorkerRoleIdentity {
            role_name: "printf_fetchargs".to_string(),
            source: r2sym::NativeWorkerRoleSource::NameHint,
            confidence: r2sym::SemanticConfidence::Heuristic,
            source_names: vec!["sym.printf_fetchargs".to_string()],
            summary_kinds: BTreeSet::from([r2sym::NativeWorkerSummaryKind::FormatArgumentFetch]),
            evidence: r2sym::SemanticEvidence::heuristic(r2sym::SemanticEvidenceReason::NameHint),
        }));

        let mut signature = InferredSignature {
            function_name: "sym.printf_fetchargs".to_string(),
            signature: "int64_t sym.printf_fetchargs(int64_t arg1)".to_string(),
            ret_type: "int64_t".to_string(),
            params: vec![InferredSignatureParam {
                name: "arg1".to_string(),
                param_type: "int64_t".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 40,
            callconv_confidence: 40,
        };

        assert!(!apply_semantic_artifact_signature_hint_to_inferred(
            &mut signature,
            &artifact,
            64
        ));
        assert_eq!(signature.ret_type, "int64_t");
        assert_eq!(signature.params.len(), 1);
        assert_eq!(signature.params[0].name, "arg1");
        assert_eq!(signature.params[0].param_type, "int64_t");
    }

    #[test]
    fn uncertified_role_identity_does_not_apply_signature_hint() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            vec![r2sym::SemanticRegion {
                anchor: 0x401000,
                frontier: BTreeSet::new(),
                control: Vec::new(),
                memory: vec![r2sym::Judged::new(
                    r2sym::MemoryFact {
                        term: test_arg_memory_term(0, 8),
                    },
                    r2sym::SemanticEvidence::exact(),
                )],
                pre: Vec::new(),
                post: Vec::new(),
                targets: Vec::new(),
            }],
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native.summary.role_identity = Some(Box::new(r2sym::NativeWorkerRoleIdentity {
            role_name: "printf_fetchargs".to_string(),
            source: r2sym::NativeWorkerRoleSource::Structural,
            confidence: r2sym::SemanticConfidence::Likely,
            source_names: Vec::new(),
            summary_kinds: BTreeSet::from([r2sym::NativeWorkerSummaryKind::FormatArgumentFetch]),
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
        }));
        let claims = artifact.semantic_claim_summary();
        assert!(claims.has_type_projection_claims());
        assert!(claims.summary_role_certificates.is_empty());

        let mut signature = InferredSignature {
            function_name: "sym.printf_fetchargs".to_string(),
            signature: "int64_t sym.printf_fetchargs(int64_t arg1)".to_string(),
            ret_type: "int64_t".to_string(),
            params: vec![InferredSignatureParam {
                name: "arg1".to_string(),
                param_type: "int64_t".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 40,
            callconv_confidence: 40,
        };

        assert!(!apply_semantic_artifact_signature_hint_to_inferred(
            &mut signature,
            &artifact,
            64
        ));
        assert_eq!(signature.ret_type, "int64_t");
        assert_eq!(signature.params.len(), 1);
        assert_eq!(signature.params[0].name, "arg1");
        assert_eq!(signature.params[0].param_type, "int64_t");
    }

    #[test]
    fn diagnostic_role_signature_hint_names_and_types_variadic_slots() {
        let params = (0..11)
            .map(|idx| InferredSignatureParam {
                name: if idx == 0 {
                    "status".to_string()
                } else {
                    format!("arg{}", idx + 1)
                },
                param_type: if idx == 0 {
                    "int32_t".to_string()
                } else {
                    "int64_t".to_string()
                },
            })
            .collect::<Vec<_>>();
        let parsed_context = ParsedExternalContext {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Void),
                params: params
                    .iter()
                    .map(|param| FunctionParamSpec {
                        name: param.name.clone(),
                        ty: Some(CTypeLike::Typedef(param.param_type.clone())),
                    })
                    .collect(),
            }),
            assumptions: r2ssa::AssumptionSet::new(
                ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
                    .into_iter()
                    .enumerate()
                    .map(|(idx, reg)| r2ssa::AnalysisAssumption {
                        id: None,
                        scope: r2ssa::AssumptionScope::Function,
                        provenance: r2ssa::AssumptionProvenance::ImportedContext,
                        subject: r2ssa::AssumptionSubject::Register {
                            name: reg.to_string(),
                        },
                        value: r2ssa::AssumptionValue::TypeHint {
                            ty: params[idx].param_type.clone(),
                        },
                    })
                    .collect(),
            ),
            ..Default::default()
        };
        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "fcn.00004bc0",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.diagnose".to_string(),
                    signature: "void sym.diagnose (int32_t status)".to_string(),
                    ret_type: "void".to_string(),
                    params,
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context,
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "sym.diagnose",
            r2sym::NativeWorkerSummaryKind::DiagnosticWrapper,
        );

        let params = &analysis.signature.params;
        assert_eq!(params[0].name, "errnum");
        assert_eq!(params[0].param_type, "errno_t");
        assert_eq!(params[1].name, "fmt");
        assert_eq!(params[1].param_type, "int8_t*");
        assert_eq!(params[2].name, "diag_value1");
        assert_eq!(params[2].param_type, "uintptr_t");
        assert_eq!(params[10].name, "diag_value9");
        assert_eq!(params[10].param_type, "uintptr_t");
        let merged = analysis
            .type_facts
            .merged_signature
            .as_ref()
            .expect("semantic role should update merged signature");
        assert_eq!(merged.params[0].name, "errnum");
        assert_eq!(merged.params[1].name, "fmt");
    }

    #[test]
    fn interproc_summary_name_does_not_project_role_signature() {
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.limfield.isra.0",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.limfield.isra.0".to_string(),
                signature: "int64_t sym.limfield.isra.0(int64_t arg1, int64_t arg2, int64_t arg3)"
                    .to_string(),
                ret_type: "int64_t".to_string(),
                params: (0..3)
                    .map(|idx| InferredSignatureParam {
                        name: format!("arg{}", idx + 1),
                        param_type: "int64_t".to_string(),
                    })
                    .collect(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(semantic_role_summary_set("limfield", Some(3))),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "int64_t");
        assert_eq!(analysis.signature.params.len(), 3);
        assert_eq!(analysis.signature.params[0].name, "arg1");
        assert_eq!(analysis.signature.params[1].name, "arg2");
        assert_eq!(analysis.signature.params[2].name, "arg3");
    }

    #[test]
    fn diagnostic_worker_artifact_drives_typed_hints_without_exact_signature() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::DiagnosticWrapper,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
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
        let params = (0..4)
            .map(|idx| InferredSignatureParam {
                name: if idx == 0 {
                    "status".to_string()
                } else {
                    format!("arg{}", idx + 1)
                },
                param_type: if idx == 0 {
                    "int32_t".to_string()
                } else {
                    "int64_t".to_string()
                },
            })
            .collect::<Vec<_>>();

        let analysis = build_type_writeback_analysis_with_semantics(
            TypeWritebackAnalysisInput {
                function_name: "sym.diagnose",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.diagnose".to_string(),
                    signature: "void sym.diagnose (int32_t status, int64_t arg2)".to_string(),
                    ret_type: "void".to_string(),
                    params,
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            TypeWritebackSemanticInputs {
                artifact: &artifact,
                local_field_accesses: &[],
            },
        );

        assert_eq!(analysis.signature.params[0].name, "status");
        assert_eq!(analysis.signature.params[0].param_type, "int32_t");
        assert_eq!(analysis.signature.params[1].name, "fmt");
        assert_eq!(analysis.signature.params[1].param_type, "int8_t*");
        assert_eq!(analysis.signature.params[2].param_type, "int64_t");
    }

    #[test]
    fn semantic_type_fallback_plan_uses_worker_role_signature_hint() {
        let mut artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::DiagnosticWrapper,
                dst: None,
                src: None,
                memory: Some(r2ssa::SummaryMemoryLocation {
                    region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
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

        let plan = build_semantic_type_fallback_plan("sym.diagnose", "x86-64", 64, &artifact);

        assert_eq!(plan.signature.params.len(), 2);
        assert_eq!(plan.signature.params[0].name, "errnum");
        assert_eq!(plan.signature.params[0].param_type, "errno_t");
        assert_eq!(plan.signature.params[1].name, "fmt");
        assert_eq!(plan.signature.params[1].param_type, "int8_t*");

        let mut main_artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            Vec::new(),
        );
        let r2sym::SemanticArtifactBody::Native(native) = &mut main_artifact.body else {
            panic!("expected native artifact");
        };
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::MemoryRead,
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
        native
            .summary
            .worker_summaries
            .push(r2sym::NativeWorkerSummary {
                anchor: 0x401000,
                kind: r2sym::NativeWorkerSummaryKind::ProgramOrchestrator,
                dst: None,
                src: None,
                memory: None,
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

        let main_plan = build_semantic_type_fallback_plan("dbg.main", "x86-64", 64, &main_artifact);
        assert_eq!(main_plan.signature.ret_type, "void");
        assert!(main_plan.signature.params.is_empty());
    }

    #[test]
    fn semantic_role_signature_hint_does_not_truncate_named_authoritative_signature() {
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.printf_fetchargs",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.printf_fetchargs".to_string(),
                signature: "int32_t sym.printf_fetchargs (struct parser *parser, struct slot *slot, uint32_t flags)"
                    .to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "parser".to_string(),
                        param_type: "struct parser *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "slot".to_string(),
                        param_type: "struct slot *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "flags".to_string(),
                        param_type: "uint32_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext {
                merged_signature: Some(FunctionSignatureSpec {
                    ret_type: Some(CTypeLike::Int {
                        bits: 32,
                        signedness: Signedness::Signed,
                    }),
                    params: vec![
                        FunctionParamSpec {
                            name: "parser".to_string(),
                            ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Struct(
                                "parser".to_string(),
                            )))),
                        },
                        FunctionParamSpec {
                            name: "slot".to_string(),
                            ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Struct(
                                "slot".to_string(),
                            )))),
                        },
                        FunctionParamSpec {
                            name: "flags".to_string(),
                            ty: Some(CTypeLike::Int {
                                bits: 32,
                                signedness: Signedness::Unsigned,
                            }),
                        },
                    ],
                }),
                ..Default::default()
            },
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(semantic_role_summary_set("sym.printf_fetchargs", None)),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params.len(), 3);
        assert_eq!(analysis.signature.params[0].name, "parser");
        assert_eq!(analysis.signature.params[1].name, "slot");
        assert_eq!(analysis.signature.params[2].name, "flags");
    }

    #[test]
    fn interproc_summary_name_does_not_truncate_weak_entry_signature() {
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "entry.init0",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "entry.init0".to_string(),
                signature: "int64_t entry.init0(void *arg1)".to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "arg1".to_string(),
                    param_type: "void *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 40,
                callconv_confidence: 40,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(semantic_role_summary_set("entry.init0", Some(1))),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "int64_t");
        assert_eq!(analysis.signature.params.len(), 1);
        assert_eq!(analysis.signature.params[0].name, "arg1");
        assert_eq!(analysis.signature.params[0].param_type, "void *");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|signature| signature.ret_type.as_ref()),
            Some(&CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            })
        );
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .map(|signature| signature.params.len()),
            Some(1)
        );
    }

    #[test]
    fn interproc_summary_name_does_not_prune_generated_surplus_slots() {
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "dbg.or",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "dbg.or".to_string(),
                signature: "bool dbg.or(void *arg1, struct sla_struct_deadbeef *arg2)".to_string(),
                ret_type: "bool".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "arg1".to_string(),
                        param_type: "void *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "arg2".to_string(),
                        param_type: "struct sla_struct_deadbeef *".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 40,
                callconv_confidence: 40,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts {
                slot_type_overrides: HashMap::from([(
                    5usize,
                    "struct sla_struct_0e18b2bc34030602 *".to_string(),
                )]),
                ..Default::default()
            },
            interproc_summary_set: Some(semantic_role_summary_set("dbg.or", Some(2))),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "bool");
        assert_eq!(analysis.signature.params.len(), 2);
    }

    #[test]
    fn interproc_summary_name_does_not_replace_weak_scalar_return() {
        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "dbg.verror_at_line",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "dbg.verror_at_line".to_string(),
                signature:
                    "int64_t dbg.verror_at_line(int status, int errnum, int8_t *file_name, unsigned int line_number, int8_t *message, struct __va_list_tag *args)"
                        .to_string(),
                ret_type: "int64_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "status".to_string(),
                        param_type: "int".to_string(),
                    },
                    InferredSignatureParam {
                        name: "errnum".to_string(),
                        param_type: "int".to_string(),
                    },
                    InferredSignatureParam {
                        name: "file_name".to_string(),
                        param_type: "int8_t *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "line_number".to_string(),
                        param_type: "unsigned int".to_string(),
                    },
                    InferredSignatureParam {
                        name: "message".to_string(),
                        param_type: "int8_t *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "args".to_string(),
                        param_type: "struct __va_list_tag *".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 92,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(semantic_role_summary_set("dbg.verror_at_line", Some(6))),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.ret_type, "int64_t");
        assert_eq!(analysis.signature.params.len(), 6);
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|signature| signature.ret_type.as_ref()),
            Some(&CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            })
        );
    }

    #[test]
    fn accepted_type_quality_roles_replace_generic_signatures_with_role_identity() {
        fn assert_projection(
            name: &str,
            weak_param_count: usize,
            expected_ret: &str,
            expected_params: &[(&str, &str)],
        ) {
            let params = (0..weak_param_count)
                .map(|idx| InferredSignatureParam {
                    name: format!("arg{}", idx + 1),
                    param_type: "int64_t".to_string(),
                })
                .collect::<Vec<_>>();
            let artifact = test_artifact_with_role_identity(
                name,
                r2sym::NativeWorkerSummaryKind::ProgramOrchestrator,
            );
            let analysis = build_type_writeback_analysis_with_semantics(
                TypeWritebackAnalysisInput {
                    function_name: name,
                    ptr_bits: 64,
                    inferred_signature: InferredSignature {
                        function_name: name.to_string(),
                        signature: format!("int64_t {name}(...)"),
                        ret_type: "int64_t".to_string(),
                        params,
                        callconv: "amd64".to_string(),
                        arch: "x86-64".to_string(),
                        confidence: 80,
                        callconv_confidence: 80,
                    },
                    recovered_vars: &[],
                    ssa_blocks: &[],
                    parsed_context: ParsedExternalContext::default(),
                    local_structs: LocalStructArtifacts::default(),
                    interproc_summary_set: None,
                    diagnostics: TypeWritebackDiagnostics::default(),
                },
                TypeWritebackSemanticInputs {
                    artifact: &artifact,
                    local_field_accesses: &[],
                },
            );

            assert_eq!(analysis.signature.ret_type, expected_ret, "{name} return");
            assert_eq!(
                analysis.signature.params.len(),
                expected_params.len(),
                "{name} arity"
            );
            for (idx, (expected_name, expected_ty)) in expected_params.iter().enumerate() {
                assert_eq!(
                    analysis.signature.params[idx].name, *expected_name,
                    "{name} param {idx} name"
                );
                assert_eq!(
                    analysis.signature.params[idx].param_type, *expected_ty,
                    "{name} param {idx} type"
                );
            }
        }

        assert_projection(
            "dbg.xnumtoumax",
            8,
            "uintmax_t",
            &[
                ("n_str", "int8_t*"),
                ("base", "int"),
                ("min", "uintmax_t"),
                ("max", "uintmax_t"),
                ("suffixes", "int8_t*"),
                ("err", "int8_t*"),
                ("err_exit", "int"),
                ("flags", "int"),
            ],
        );
        assert_projection(
            "sym.setlocale_null_r_unlocked",
            4,
            "int",
            &[
                ("category", "int"),
                ("buf", "int8_t*"),
                ("bufsize", "size_t"),
            ],
        );
        assert_projection(
            "dbg.areadlink_with_size",
            3,
            "int8_t*",
            &[("filename", "int8_t*"), ("size_hint", "size_t")],
        );
        assert_projection("sym.hard_locale", 2, "bool", &[("category", "int")]);
        assert_projection("sym.set_program_name", 2, "void", &[("argv0", "int8_t*")]);
        assert_projection(
            "sym.nstrftime",
            7,
            "ptrdiff_t",
            &[
                ("s", "int8_t*"),
                ("maxsize", "size_t"),
                ("format", "int8_t*"),
                ("tp", "tm*"),
                ("tz", "timezone_t"),
                ("ns", "int"),
            ],
        );
        assert_projection("dbg.hash_free", 2, "void", &[("table", "hash_table*")]);
        assert_projection(
            "dbg.num_processors",
            2,
            "unsigned long",
            &[("query", "enum nproc_query")],
        );
        assert_projection(
            "dbg.open_input_files",
            4,
            "size_t",
            &[
                ("files", "sortfile*"),
                ("nfiles", "size_t"),
                ("pfps", "FILE***"),
            ],
        );
        assert_projection(
            "dbg.physmem_claimable",
            2,
            "double",
            &[("aggressivity", "double")],
        );
        assert_projection(
            "dbg.randread_new",
            3,
            "randread_source*",
            &[("name", "int8_t*"), ("bytes_bound", "size_t")],
        );
    }

    #[test]
    fn weak_summary_kind_projection_does_not_widen_authoritative_anonymous_signature() {
        let mut facts = FunctionTypeFacts {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Void),
                params: vec![
                    FunctionParamSpec {
                        name: "dst".to_string(),
                        ty: Some(void_pointer_type()),
                    },
                    FunctionParamSpec {
                        name: "src".to_string(),
                        ty: Some(void_pointer_type()),
                    },
                ],
            }),
            ..FunctionTypeFacts::default()
        };
        let projected = FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Void),
            params: vec![
                FunctionParamSpec {
                    name: "dst".to_string(),
                    ty: Some(void_pointer_type()),
                },
                FunctionParamSpec {
                    name: "src".to_string(),
                    ty: Some(void_pointer_type()),
                },
                FunctionParamSpec {
                    name: "len".to_string(),
                    ty: Some(typedef_type("size_t")),
                },
            ],
        };

        let result = facts.apply_signature_projection(
            "fcn.0000a200",
            FunctionSignatureProjection::weak_summary_kind(projected),
            64,
        );

        assert!(result.rejected.is_some());
        assert_eq!(
            facts
                .merged_signature
                .as_ref()
                .map(|signature| signature.params.len()),
            Some(2)
        );
    }

    #[test]
    fn exact_role_signature_replaces_weak_role_identity_signature_slots() {
        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "sym.quotearg_buffer_restyled",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.quotearg_buffer_restyled".to_string(),
                    signature: "void* sym.quotearg_buffer_restyled (int8_t* arg1, int64_t arg2, int8_t* arg3, uint64_t arg4)"
                        .to_string(),
                    ret_type: "void*".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "arg1".to_string(),
                            param_type: "int8_t*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg2".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg3".to_string(),
                            param_type: "int8_t*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg4".to_string(),
                            param_type: "uint64_t".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "sym.quotearg_buffer_restyled",
            r2sym::NativeWorkerSummaryKind::FormatRender,
        );

        assert_eq!(analysis.signature.ret_type, "size_t");
        assert_eq!(analysis.signature.params.len(), 9);
        assert_eq!(analysis.signature.params[0].name, "buffer");
        assert_eq!(analysis.signature.params[1].param_type, "size_t");
        assert_eq!(
            analysis.signature.params[4].param_type,
            "enum quoting_style"
        );
        assert_eq!(analysis.signature.params[6].param_type, "unsigned int*");
    }

    #[test]
    fn exact_role_signature_replaces_single_letter_weak_slots() {
        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "sym.streamsavedir",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.streamsavedir".to_string(),
                    signature: "int32_t sym.streamsavedir (int32_t a, int32_t b)".to_string(),
                    ret_type: "int32_t".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "a".to_string(),
                            param_type: "int32_t".to_string(),
                        },
                        InferredSignatureParam {
                            name: "b".to_string(),
                            param_type: "int32_t".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "sym.streamsavedir",
            r2sym::NativeWorkerSummaryKind::DirectoryTraversal,
        );

        assert_eq!(analysis.signature.ret_type, "int8_t*");
        assert_eq!(analysis.signature.params[0].name, "dirp");
        assert_eq!(analysis.signature.params[0].param_type, "DIR*");
        assert_eq!(analysis.signature.params[1].name, "option");
        assert_eq!(
            analysis.signature.params[1].param_type,
            "enum savedir_option"
        );
    }

    #[test]
    fn exact_role_signature_truncates_weak_surplus_slots() {
        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "sym.rpl_fts_read",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.rpl_fts_read".to_string(),
                    signature: "FTSENT* sym.rpl_fts_read (void* sp, int64_t arg2)".to_string(),
                    ret_type: "FTSENT*".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "sp".to_string(),
                            param_type: "void*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg2".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "sym.rpl_fts_read",
            r2sym::NativeWorkerSummaryKind::DirectoryTraversal,
        );

        assert_eq!(analysis.signature.params.len(), 1);
        assert_eq!(analysis.signature.params[0].name, "sp");
        assert_eq!(analysis.signature.params[0].param_type, "FTS*");
    }

    #[test]
    fn mbrtoc32_role_signature_refines_parser_projection_slots() {
        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "sym.rpl_mbrtoc32",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.rpl_mbrtoc32".to_string(),
                    signature: "void* sym.rpl_mbrtoc32 (uint8_t* output, uint8_t* stream, uint64_t arg3, int64_t arg4)"
                        .to_string(),
                    ret_type: "void*".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "output".to_string(),
                            param_type: "uint8_t*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "stream".to_string(),
                            param_type: "uint8_t*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg3".to_string(),
                            param_type: "uint64_t".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg4".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "sym.rpl_mbrtoc32",
            r2sym::NativeWorkerSummaryKind::Parser,
        );

        assert_eq!(analysis.signature.ret_type, "size_t");
        assert_eq!(analysis.signature.params[0].name, "pwc");
        assert_eq!(analysis.signature.params[0].param_type, "char32_t*");
        assert_eq!(analysis.signature.params[1].name, "s");
        assert_eq!(analysis.signature.params[1].param_type, "int8_t*");
        assert_eq!(analysis.signature.params[2].param_type, "size_t");
        assert_eq!(analysis.signature.params[3].param_type, "mbstate_t*");
    }

    #[test]
    fn explicit_role_type_hint_blocks_generic_pointer_upgrade() {
        let mut projection = SemanticTypeProjection::default();
        projection.pointer_param_indices.insert(0);
        projection.param_type_hints.insert(0, c_int_type());
        projection.param_name_hints.insert(0, "argc".to_string());

        let mut signature = InferredSignature {
            function_name: "dbg.main".to_string(),
            signature: "int dbg.main (int argc)".to_string(),
            ret_type: "int".to_string(),
            params: vec![InferredSignatureParam {
                name: "argc".to_string(),
                param_type: "int".to_string(),
            }],
            callconv: "amd64".to_string(),
            arch: "x86-64".to_string(),
            confidence: 96,
            callconv_confidence: 92,
        };
        let mut merged = inferred_signature_to_spec(&signature, 64);

        upgrade_param_indices_to_pointer(
            projection_pointer_upgrade_indices(&projection),
            &mut merged,
            &mut signature,
            64,
        );

        assert_eq!(signature.params[0].param_type, "int");
        assert_eq!(
            merged
                .as_ref()
                .and_then(|sig| sig.params[0].ty.as_ref())
                .map(|ty| render_signature_type(ty, 64)),
            Some("int".to_string())
        );

        let mut summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x401000),
            Some("dbg.main".to_string()),
        );
        summary.arg_effects.insert(
            0,
            r2ssa::SummaryArgEffect {
                read: true,
                ..Default::default()
            },
        );
        maybe_upgrade_param_to_pointer(&summary, &mut merged, &mut signature, 64);

        assert_eq!(signature.params[0].param_type, "int");

        let mut fallback_signature = InferredSignature {
            function_name: "dbg.main".to_string(),
            signature: "int dbg.main (int argc)".to_string(),
            ret_type: "int".to_string(),
            params: vec![InferredSignatureParam {
                name: "argc".to_string(),
                param_type: "int".to_string(),
            }],
            callconv: "unknown".to_string(),
            arch: "x86-64".to_string(),
            confidence: 80,
            callconv_confidence: 0,
        };
        let mut fallback_projection = SemanticTypeProjection::default();
        fallback_projection
            .param_type_hints
            .insert(0, signed_byte_pointer_type());
        assert!(!apply_semantic_projection_to_fallback_signature(
            &mut fallback_signature,
            &fallback_projection,
            64
        ));
        assert_eq!(fallback_signature.params[0].param_type, "int");
        assert_eq!(fallback_signature.confidence, 80);
    }

    #[test]
    fn printf_fetchargs_role_signature_hint_replaces_generic_dense_switch_signature() {
        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "sym.printf_fetchargs",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.printf_fetchargs".to_string(),
                    signature:
                        "void sym.printf_fetchargs (int64_t arg1, int64_t arg2, int64_t arg3)"
                            .to_string(),
                    ret_type: "void".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "arg1".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg2".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg3".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs: LocalStructArtifacts::default(),
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "sym.printf_fetchargs",
            r2sym::NativeWorkerSummaryKind::FormatArgumentFetch,
        );

        assert_eq!(analysis.signature.ret_type, "printf_status_t");
        assert_eq!(analysis.signature.params.len(), 2);
        assert_eq!(analysis.signature.params[0].name, "args");
        assert_eq!(analysis.signature.params[0].param_type, "__va_list_tag*");
        assert_eq!(analysis.signature.params[1].name, "arguments_out");
        assert_eq!(analysis.signature.params[1].param_type, "arguments*");
    }

    #[test]
    fn semantic_role_typedef_blocks_local_generated_struct_override() {
        let local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_deadbeef".to_string(),
                decl: "struct sla_struct_deadbeef { int32_t f_0; int32_t f_8; };".to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_0".to_string(),
                        offset: 0,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(
                1usize,
                "struct sla_struct_deadbeef *".to_string(),
            )]),
            slot_field_profiles: HashMap::from([(
                1usize,
                BTreeMap::from([(0u64, "int32_t".to_string()), (8u64, "int32_t".to_string())]),
            )]),
        };

        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "sym.printf_fetchargs",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "sym.printf_fetchargs".to_string(),
                    signature:
                        "void sym.printf_fetchargs (int64_t arg1, int64_t arg2, int64_t arg3)"
                            .to_string(),
                    ret_type: "void".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "arg1".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg2".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                        InferredSignatureParam {
                            name: "arg3".to_string(),
                            param_type: "int64_t".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs,
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "sym.printf_fetchargs",
            r2sym::NativeWorkerSummaryKind::FormatArgumentFetch,
        );

        assert_eq!(analysis.signature.params[1].param_type, "arguments*");
        assert!(!analysis.type_facts.slot_type_overrides.contains_key(&1));
        assert!(
            !analysis
                .plan
                .struct_decls
                .iter()
                .any(|decl| decl.name == "sla_struct_deadbeef")
        );
    }

    #[test]
    fn exact_role_signature_prunes_generated_aggregate_override() {
        let fts_local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_fts".to_string(),
                decl: "struct sla_struct_fts { int32_t f_8; int32_t f_34; };".to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![
                    StructFieldCandidate {
                        name: "f_8".to_string(),
                        offset: 8,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                    StructFieldCandidate {
                        name: "f_34".to_string(),
                        offset: 52,
                        field_type: "int32_t".to_string(),
                        confidence: 95,
                    },
                ],
            }],
            slot_type_overrides: HashMap::from([(0usize, "struct sla_struct_fts *".to_string())]),
            slot_field_profiles: HashMap::from([(
                0usize,
                BTreeMap::from([
                    (8u64, "int32_t".to_string()),
                    (52u64, "int32_t".to_string()),
                ]),
            )]),
        };

        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "dbg.fts_build",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "dbg.fts_build".to_string(),
                    signature: "FTSENT* dbg.fts_build (struct sla_struct_fts * sp, int32_t type)"
                        .to_string(),
                    ret_type: "FTSENT*".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "sp".to_string(),
                            param_type: "struct sla_struct_fts *".to_string(),
                        },
                        InferredSignatureParam {
                            name: "type".to_string(),
                            param_type: "int32_t".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 80,
                    callconv_confidence: 80,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs: fts_local_structs,
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "dbg.fts_build",
            r2sym::NativeWorkerSummaryKind::DirectoryTraversal,
        );

        assert_eq!(analysis.signature.params[0].param_type, "FTS*");
        assert!(!analysis.type_facts.slot_type_overrides.contains_key(&0));
        assert!(
            !analysis
                .plan
                .struct_decls
                .iter()
                .any(|decl| decl.name == "sla_struct_fts")
        );

        let bool_local_structs = LocalStructArtifacts {
            struct_decls: vec![StructDeclCandidate {
                name: "sla_struct_bool".to_string(),
                decl: "struct sla_struct_bool { int32_t f_0; };".to_string(),
                confidence: 95,
                source: StructDeclSource::LocalInferred,
                fields: vec![StructFieldCandidate {
                    name: "f_0".to_string(),
                    offset: 0,
                    field_type: "int32_t".to_string(),
                    confidence: 95,
                }],
            }],
            slot_type_overrides: HashMap::from([(2usize, "struct sla_struct_bool *".to_string())]),
            slot_field_profiles: HashMap::from([(
                2usize,
                BTreeMap::from([(0u64, "int32_t".to_string())]),
            )]),
        };

        let analysis = build_type_writeback_analysis_with_role_identity(
            TypeWritebackAnalysisInput {
                function_name: "dbg.skip_whitespace_run",
                ptr_bits: 64,
                inferred_signature: InferredSignature {
                    function_name: "dbg.skip_whitespace_run".to_string(),
                    signature: "enum field_terminator dbg.skip_whitespace_run (mbbuf_t* mbuf, struct mbfield_parser* parser, _Bool* have_pending_line, _Bool have_initial_whitespace)"
                        .to_string(),
                    ret_type: "enum field_terminator".to_string(),
                    params: vec![
                        InferredSignatureParam {
                            name: "mbuf".to_string(),
                            param_type: "mbbuf_t*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "parser".to_string(),
                            param_type: "struct mbfield_parser*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "have_pending_line".to_string(),
                            param_type: "_Bool*".to_string(),
                        },
                        InferredSignatureParam {
                            name: "have_initial_whitespace".to_string(),
                            param_type: "_Bool".to_string(),
                        },
                    ],
                    callconv: "amd64".to_string(),
                    arch: "x86-64".to_string(),
                    confidence: 96,
                    callconv_confidence: 92,
                },
                recovered_vars: &[],
                ssa_blocks: &[],
                parsed_context: ParsedExternalContext::default(),
                local_structs: bool_local_structs,
                interproc_summary_set: None,
                diagnostics: TypeWritebackDiagnostics::default(),
            },
            "dbg.skip_whitespace_run",
            r2sym::NativeWorkerSummaryKind::FieldSelection,
        );

        assert_eq!(analysis.signature.params[2].param_type, "bool*");
        assert!(!analysis.type_facts.slot_type_overrides.contains_key(&2));
        assert!(
            !analysis
                .plan
                .struct_decls
                .iter()
                .any(|decl| decl.name == "sla_struct_bool")
        );
    }

    #[test]
    fn summary_to_callee_fact_does_not_infer_import_linkage_from_summary_name() {
        let summary = r2ssa::FunctionSemanticSummary {
            id: r2ssa::InterprocFunctionId(0x401080),
            name: Some("sym.imp.memcpy".to_string()),
            linkage: r2ssa::FunctionSemanticLinkage::Unknown,
            arg_count_hint: Some(3),
            direct_callees: BTreeSet::new(),
            callsite_count: 1,
            has_unknown_calls: false,
            arg_effects: BTreeMap::new(),
            memory_effects: Vec::new(),
            transfer_effects: Vec::new(),
            allocation_effects: Vec::new(),
            lifetime_effects: Vec::new(),
            sync_effects: Vec::new(),
            atomic_effects: Vec::new(),
            return_relation: r2ssa::SummaryReturnRelation::Unknown,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        };

        let fact = summary_to_callee_fact(&summary);

        assert_eq!(fact.name.as_deref(), Some("sym.imp.memcpy"));
        assert_eq!(fact.linkage, crate::CalleeLinkage::Unknown);
        assert!(
            !fact.linkage.authorizes_import_policy(),
            "summary names are not typed import-linkage evidence",
        );
        assert!(
            fact.authorizes_model_policy(),
            "interproc summaries are explicit model-policy evidence"
        );
    }

    #[test]
    fn summary_to_callee_fact_exports_explicit_import_linkage() {
        let mut summary = r2ssa::FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x401088),
            Some("memcpy".to_string()),
        );
        summary.linkage = r2ssa::FunctionSemanticLinkage::Imported;

        let fact = summary_to_callee_fact(&summary);

        assert_eq!(fact.name.as_deref(), Some("memcpy"));
        assert_eq!(fact.linkage, crate::CalleeLinkage::Imported);
        assert!(
            fact.linkage.authorizes_import_policy(),
            "only explicit summary linkage should certify imported-call policy",
        );
        assert!(
            fact.authorizes_model_policy(),
            "summary-derived callee facts should retain explicit model evidence"
        );
    }

    #[test]
    fn interproc_returned_arg_summary_exports_callee_facts() {
        let mut summary_set = r2ssa::InterprocSummarySet::default();
        let root = r2ssa::InterprocFunctionId(0x401000);
        let helper = r2ssa::InterprocFunctionId(0x401080);
        summary_set.root = Some(root);
        summary_set.summaries.insert(
            root,
            r2ssa::FunctionSemanticSummary {
                id: root,
                name: Some("sym.wrapper_user".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                arg_count_hint: Some(2),
                direct_callees: BTreeSet::from([helper.0]),
                callsite_count: 1,
                has_unknown_calls: false,
                arg_effects: BTreeMap::new(),
                memory_effects: Vec::new(),
                transfer_effects: Vec::new(),
                allocation_effects: Vec::new(),
                lifetime_effects: Vec::new(),
                sync_effects: Vec::new(),
                atomic_effects: Vec::new(),
                return_relation: r2ssa::SummaryReturnRelation::Unknown,
                reads_global_memory: false,
                writes_global_memory: false,
                touches_unknown_memory: false,
            },
        );
        summary_set.summaries.insert(
            helper,
            r2ssa::FunctionSemanticSummary {
                id: helper,
                name: Some("sym.memcpy_like".to_string()),
                linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                arg_count_hint: Some(2),
                direct_callees: BTreeSet::new(),
                callsite_count: 1,
                has_unknown_calls: false,
                arg_effects: BTreeMap::from([
                    (
                        0,
                        r2ssa::SummaryArgEffect {
                            read: false,
                            write: true,
                            escape: true,
                            free: false,
                        },
                    ),
                    (
                        1,
                        r2ssa::SummaryArgEffect {
                            read: true,
                            write: false,
                            escape: false,
                            free: false,
                        },
                    ),
                ]),
                memory_effects: vec![
                    r2ssa::SummaryMemoryEffect {
                        kind: r2ssa::SummaryMemoryEffectKind::Write,
                        location: r2ssa::SummaryMemoryLocation {
                            region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                            range: None,
                        },
                    },
                    r2ssa::SummaryMemoryEffect {
                        kind: r2ssa::SummaryMemoryEffectKind::Read,
                        location: r2ssa::SummaryMemoryLocation {
                            region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                            range: None,
                        },
                    },
                ],
                transfer_effects: vec![r2ssa::SummaryTransferEffect {
                    dst: r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                        range: None,
                    },
                    src: r2ssa::SummaryMemoryLocation {
                        region: r2ssa::SummaryMemoryRegion::Arg { index: 1 },
                        range: None,
                    },
                    len: r2ssa::SummaryTransferLength::Arg(2),
                }],
                allocation_effects: Vec::new(),
                lifetime_effects: Vec::new(),
                sync_effects: Vec::new(),
                atomic_effects: Vec::new(),
                return_relation: r2ssa::SummaryReturnRelation::Arg(0),
                reads_global_memory: false,
                writes_global_memory: false,
                touches_unknown_memory: false,
            },
        );

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.wrapper_user",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.wrapper_user".to_string(),
                signature: "void * sym.wrapper_user (void * dst, void * src)".to_string(),
                ret_type: "void *".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "dst".to_string(),
                        param_type: "void *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "src".to_string(),
                        param_type: "void *".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 85,
                callconv_confidence: 85,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        let helper_fact = analysis
            .type_facts
            .callee_facts
            .get(&helper.0)
            .expect("helper callee fact");
        assert_eq!(helper_fact.return_relation, CalleeReturnRelation::Arg(0));
        assert!(
            helper_fact
                .arg_effects
                .get(&0)
                .is_some_and(|effect| effect.write && effect.escape)
        );
        assert!(
            helper_fact
                .arg_effects
                .get(&1)
                .is_some_and(|effect| effect.read && !effect.write)
        );
        assert!(helper_fact.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                crate::facts::CalleeMemoryEffect {
                    kind: crate::facts::CalleeMemoryEffectKind::Write,
                    location: crate::facts::CalleeMemoryLocation {
                        region: crate::facts::CalleeMemoryRegion::Arg { index: 0 },
                        ..
                    },
                }
            )
        }));
        assert!(helper_fact.memory_effects.iter().any(|effect| {
            matches!(
                effect,
                crate::facts::CalleeMemoryEffect {
                    kind: crate::facts::CalleeMemoryEffectKind::Read,
                    location: crate::facts::CalleeMemoryLocation {
                        region: crate::facts::CalleeMemoryRegion::Arg { index: 1 },
                        ..
                    },
                }
            )
        }));
        assert_eq!(
            helper_fact.transfer_effects,
            vec![crate::facts::CalleeTransferEffect {
                dst: crate::facts::CalleeMemoryLocation {
                    region: crate::facts::CalleeMemoryRegion::Arg { index: 0 },
                    range: None,
                },
                src: crate::facts::CalleeMemoryLocation {
                    region: crate::facts::CalleeMemoryRegion::Arg { index: 1 },
                    range: None,
                },
                len: crate::facts::CalleeTransferLength::Arg(2),
            }]
        );
    }

    #[test]
    fn interproc_summary_name_does_not_export_role_callee_type_facts() {
        let root = r2ssa::InterprocFunctionId(0x402000);
        let helper = r2ssa::InterprocFunctionId(0x402080);
        let mut root_summary =
            r2ssa::FunctionSemanticSummary::unknown(root, Some("sym.sort_driver".to_string()));
        root_summary.direct_callees.insert(helper.0);
        let mut helper_summary = r2ssa::FunctionSemanticSummary::unknown(
            helper,
            Some("dbg.open_input_files".to_string()),
        );
        helper_summary.arg_count_hint = Some(3);
        helper_summary.arg_effects.insert(
            2,
            SummaryArgEffect {
                write: true,
                ..SummaryArgEffect::default()
            },
        );
        let summary_set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(root, root_summary), (helper, helper_summary)]),
            diagnostics: Default::default(),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.sort_driver",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.sort_driver".to_string(),
                signature: "void sym.sort_driver(void)".to_string(),
                ret_type: "void".to_string(),
                params: Vec::new(),
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 80,
                callconv_confidence: 80,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        let helper_fact = analysis
            .type_facts
            .callee_facts
            .get(&helper.0)
            .expect("helper callee fact");
        assert_eq!(helper_fact.return_type_hint, None);
        assert_eq!(helper_fact.param_type_hints.get(&0), None);
        assert_eq!(
            helper_fact.param_type_hints.get(&2),
            Some(&void_pointer_type())
        );
        assert!(
            helper_fact
                .arg_effects
                .get(&2)
                .is_some_and(|effect| effect.write && !effect.free)
        );
    }

    #[test]
    fn interproc_summary_name_does_not_fabricate_callee_out_param_writes() {
        let helper = r2ssa::InterprocFunctionId(0x402080);
        let mut helper_summary = r2ssa::FunctionSemanticSummary::unknown(
            helper,
            Some("dbg.open_input_files".to_string()),
        );
        helper_summary.arg_count_hint = Some(3);
        helper_summary.arg_effects.insert(
            2,
            r2ssa::SummaryArgEffect {
                read: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );

        let helper_fact = summary_to_callee_fact(&helper_summary);

        assert_eq!(
            helper_fact.param_type_hints.get(&2),
            Some(&void_pointer_type())
        );
        assert!(
            !helper_fact
                .arg_effects
                .get(&2)
                .is_some_and(|effect| effect.write)
        );
    }

    #[test]
    fn interproc_memory_effect_summary_upgrades_generic_pointer_like_params() {
        let root = r2ssa::InterprocFunctionId(0x401300);
        let summary_set = InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([(
                root,
                FunctionSemanticSummary {
                    id: root,
                    name: Some("sym.ptr_user".to_string()),
                    linkage: r2ssa::FunctionSemanticLinkage::Unknown,
                    arg_count_hint: Some(1),
                    direct_callees: BTreeSet::new(),
                    callsite_count: 0,
                    has_unknown_calls: false,
                    arg_effects: BTreeMap::from([(
                        0,
                        SummaryArgEffect {
                            read: true,
                            write: true,
                            escape: false,
                            free: false,
                        },
                    )]),
                    memory_effects: vec![r2ssa::SummaryMemoryEffect {
                        kind: r2ssa::SummaryMemoryEffectKind::Write,
                        location: r2ssa::SummaryMemoryLocation {
                            region: r2ssa::SummaryMemoryRegion::Arg { index: 0 },
                            range: Some(r2ssa::SummaryMemoryRange {
                                offset_lo: 0,
                                offset_hi: 7,
                                width: Some(8),
                            }),
                        },
                    }],
                    transfer_effects: Vec::new(),
                    allocation_effects: Vec::new(),
                    lifetime_effects: Vec::new(),
                    sync_effects: Vec::new(),
                    atomic_effects: Vec::new(),
                    return_relation: SummaryReturnRelation::Void,
                    reads_global_memory: false,
                    writes_global_memory: false,
                    touches_unknown_memory: false,
                },
            )]),
            diagnostics: Default::default(),
        };

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.ptr_user",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.ptr_user".to_string(),
                signature: "void sym.ptr_user (int64_t p)".to_string(),
                ret_type: "void".to_string(),
                params: vec![InferredSignatureParam {
                    name: "p".to_string(),
                    param_type: "int64_t".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 70,
                callconv_confidence: 70,
            },
            recovered_vars: &[],
            ssa_blocks: &[],
            parsed_context: ParsedExternalContext::default(),
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: Some(summary_set),
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert_eq!(analysis.signature.params[0].param_type, "void*");
        assert_eq!(
            analysis
                .type_facts
                .merged_signature
                .as_ref()
                .and_then(|sig| sig.params.first())
                .and_then(|param| param.ty.as_ref()),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Void)))
        );
    }

    #[test]
    fn symbolic_actionable_memory_terms_seed_local_struct_profiles() {
        let compiled =
            test_exact_compiled_condition("arg0->f_8 == 0", vec![test_arg_memory_term(8, 4)]);
        let artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            vec![test_region_with_control(
                0x401000,
                0x401020,
                "arg0->f_8 == 0",
                compiled,
            )],
        );
        let mut local_structs = LocalStructArtifacts::default();

        augment_local_struct_artifacts_with_semantics(&mut local_structs, &artifact, 64);

        assert_eq!(
            local_structs
                .slot_field_profiles
                .get(&0)
                .and_then(|profile| profile.get(&8))
                .map(String::as_str),
            Some("int32_t")
        );
        assert_eq!(
            local_structs
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct sla_struct_symbolic_arg1 *")
        );
        assert!(
            local_structs
                .struct_decls
                .iter()
                .any(|decl| decl.name == "sla_struct_symbolic_arg1")
        );
    }

    #[test]
    fn symbolic_memory_without_control_or_post_support_is_rejected() {
        let artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            vec![r2sym::SemanticRegion {
                anchor: 0x401000,
                frontier: BTreeSet::new(),
                control: Vec::new(),
                memory: vec![r2sym::Judged::new(
                    r2sym::MemoryFact {
                        term: test_arg_memory_term(8, 4),
                    },
                    r2sym::SemanticEvidence::exact(),
                )],
                pre: Vec::new(),
                post: Vec::new(),
                targets: Vec::new(),
            }],
        );
        let mut local_structs = LocalStructArtifacts::default();

        augment_local_struct_artifacts_with_semantics(&mut local_structs, &artifact, 64);

        assert!(
            local_structs.slot_field_profiles.is_empty(),
            "memory-only regions without control/post support must not project struct fields"
        );
    }

    #[test]
    fn symbolic_postconditions_seed_local_struct_profiles_without_control_islands() {
        let artifact = test_artifact(
            r2sym::RefinementStage::Compiled,
            r2sym::SliceClass::Worker,
            false,
            Vec::new(),
            vec![r2sym::SemanticRegion {
                anchor: 0x401000,
                frontier: BTreeSet::new(),
                control: Vec::new(),
                memory: Vec::new(),
                pre: Vec::new(),
                post: vec![r2sym::Judged::new(
                    r2sym::SemanticPredicate {
                        expr: "post(arg0->f_8)".to_string(),
                        compiled: Some(test_exact_compiled_condition(
                            "post(arg0->f_8)",
                            vec![test_arg_memory_term(8, 4)],
                        )),
                    },
                    r2sym::SemanticEvidence::exact(),
                )],
                targets: Vec::new(),
            }],
        );
        let mut local_structs = LocalStructArtifacts::default();

        augment_local_struct_artifacts_with_semantics(&mut local_structs, &artifact, 64);

        assert_eq!(
            local_structs
                .slot_field_profiles
                .get(&0)
                .and_then(|profile| profile.get(&8))
                .map(String::as_str),
            Some("int32_t")
        );
    }

    #[test]
    fn semantic_type_fallback_plan_uses_typed_symbolic_summary() {
        let artifact = test_artifact(
            r2sym::RefinementStage::Residual,
            r2sym::SliceClass::Worker,
            true,
            vec![r2sym::ResidualReason::LargeCfg],
            vec![r2sym::SemanticRegion {
                anchor: 0x401000,
                frontier: BTreeSet::from([0x401010]),
                control: vec![r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x401010,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                        condition: Some("x == 0".to_string()),
                        compiled: Some(test_exact_compiled_condition("x == 0", Vec::new())),
                    },
                    r2sym::SemanticEvidence::exact(),
                )],
                memory: vec![r2sym::Judged::new(
                    r2sym::MemoryFact {
                        term: test_arg_memory_term(8, 4),
                    },
                    r2sym::SemanticEvidence::exact(),
                )],
                pre: Vec::new(),
                post: Vec::new(),
                targets: vec![r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x401010,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                    },
                    r2sym::SemanticEvidence::exact(),
                )],
            }],
        );

        let plan = build_semantic_type_fallback_plan("fcn.401000", "x86-64", 64, &artifact);

        assert_eq!(plan.signature.params.len(), 1);
        assert!(plan.signature.params[0].param_type.contains("struct "));
        assert_eq!(plan.struct_decls.len(), 1);
        assert!(plan
            .diagnostics
            .warnings
            .iter()
            .any(|warning| warning.contains("semantic fallback: worker slice in residual mode")));
        assert!(
            plan.diagnostics
                .warnings
                .iter()
                .any(|warning| warning.contains("regions=1"))
        );
        assert!(
            plan.diagnostics
                .warnings
                .iter()
                .any(|warning| warning.contains("projected 1 struct candidate"))
        );
    }

    #[test]
    fn local_field_access_certificates_derive_from_type_artifacts() {
        let mut local_structs = LocalStructArtifacts::default();
        local_structs
            .slot_field_profiles
            .insert(0, BTreeMap::from([(8, "int32_t".to_string())]));

        let accesses = local_field_accesses_from_struct_artifacts(&local_structs);
        assert_eq!(
            accesses,
            vec![LocalFieldAccessFact {
                slot: 0,
                field_offset: 8,
                field_name: "f_8".to_string(),
                field_type: Some("int32_t".to_string()),
            }]
        );

        let certificates = field_access_certificates_from_struct_artifacts(&local_structs);
        assert_eq!(
            certificates,
            vec![crate::FieldAccessCertificate {
                slot: 0,
                field_offset: 8,
                field_name: "f_8".to_string(),
                field_type: Some("int32_t".to_string()),
            }]
        );
    }

    #[test]
    fn local_struct_inference_handles_x86_strength_reduced_index_scale() {
        let ssa_blocks = [SSABlock {
            addr: 0x40182f,
            size: 124,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot_arr", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:spill_arr", 1, 8),
                    src: SSAVar::new("RDI", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot_arr", 1, 8),
                    val: SSAVar::new("tmp:spill_arr", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot_idx", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Copy {
                    dst: SSAVar::new("tmp:spill_idx", 1, 4),
                    src: SSAVar::new("ESI", 0, 4),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot_idx", 1, 8),
                    val: SSAVar::new("tmp:spill_idx", 1, 4),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot_idx", 2, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff4", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("idx32", 1, 4),
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot_idx", 2, 8),
                },
                SSAOp::IntSExt {
                    dst: SSAVar::new("idx64", 1, 8),
                    src: SSAVar::new("idx32", 1, 4),
                },
                SSAOp::IntLeft {
                    dst: SSAVar::new("idx8", 1, 8),
                    a: SSAVar::new("idx64", 1, 8),
                    b: SSAVar::new("const:3", 0, 4),
                },
                SSAOp::IntSub {
                    dst: SSAVar::new("idx7", 1, 8),
                    a: SSAVar::new("idx8", 1, 8),
                    b: SSAVar::new("idx64", 1, 8),
                },
                SSAOp::IntLeft {
                    dst: SSAVar::new("idx56", 1, 8),
                    a: SSAVar::new("idx7", 1, 8),
                    b: SSAVar::new("const:3", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:slot_arr", 2, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("arr", 1, 8),
                    space: "ram".to_string(),
                    addr: SSAVar::new("tmp:slot_arr", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("elem", 1, 8),
                    a: SSAVar::new("idx56", 1, 8),
                    b: SSAVar::new("arr", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("field8", 1, 8),
                    a: SSAVar::new("elem", 1, 8),
                    b: SSAVar::new("const:8", 0, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("field8", 1, 8),
                    val: SSAVar::new("EDX", 0, 4),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("field34", 1, 8),
                    a: SSAVar::new("elem", 1, 8),
                    b: SSAVar::new("const:34", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("field34_val", 1, 4),
                    space: "ram".to_string(),
                    addr: SSAVar::new("field34", 1, 8),
                },
            ],
        }];
        let mut diagnostics = TypeWritebackDiagnostics::default();

        let local_structs = infer_local_struct_artifacts_from_ssa(
            &ssa_blocks,
            Some("x86-64"),
            64,
            &mut diagnostics,
        );

        assert_eq!(
            local_structs
                .slot_field_profiles
                .get(&0)
                .cloned()
                .unwrap_or_default(),
            BTreeMap::from([(8, "int32_t".to_string()), (0x34, "int32_t".to_string())]),
            "diagnostics={diagnostics:?}"
        );
        assert_eq!(
            local_structs
                .slot_type_overrides
                .get(&0)
                .map(String::as_str),
            Some("struct sla_struct_420703e08f70f00e *")
        );
    }

    #[test]
    fn typed_stack_pointer_index_access_certifies_scalar_array_index() {
        let mut parsed_context = ParsedExternalContext::default();
        let buf_slot = StackSlotKey {
            base: ExternalStackBase::FramePointer,
            offset: -8,
        };
        parsed_context.stack_slots.insert(
            buf_slot.clone(),
            crate::ExternalStackSlotSpec {
                name: "buf".to_string(),
                ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                    bits: 8,
                    signedness: Signedness::Signed,
                }))),
                base: ExternalStackBase::FramePointer,
                role: ExternalStackSlotRole::Local,
                param_index: None,
                param_name: None,
                source_reg: None,
            },
        );
        parsed_context.stack_slots.insert(
            StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x20,
            },
            crate::ExternalStackSlotSpec {
                name: "len_home".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                }),
                base: ExternalStackBase::FramePointer,
                role: ExternalStackSlotRole::ParamHome,
                param_index: Some(1),
                param_name: Some("len".to_string()),
                source_reg: Some("rsi".to_string()),
            },
        );
        let ssa_blocks = [SSABlock {
            addr: 0x4013b1,
            size: 32,
            ops: vec![
                SSAOp::IntAdd {
                    dst: SSAVar::new("buf_slot_addr", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:fffffffffffffff8", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("buf", 1, 8),
                    space: "ram".to_string(),
                    addr: SSAVar::new("buf_slot_addr", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("len_slot_addr", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::new("const:ffffffffffffffe0", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("len", 1, 8),
                    space: "ram".to_string(),
                    addr: SSAVar::new("len_slot_addr", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("nul_addr", 1, 8),
                    a: SSAVar::new("buf", 1, 8),
                    b: SSAVar::new("len", 1, 8),
                },
                SSAOp::Store {
                    space: "ram".to_string(),
                    addr: SSAVar::new("nul_addr", 1, 8),
                    val: SSAVar::new("const:0", 0, 1),
                },
            ],
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.alloc_and_copy",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.alloc_and_copy".to_string(),
                signature: "int8_t * sym.alloc_and_copy (int8_t * src, size_t len)".to_string(),
                ret_type: "int8_t *".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "src".to_string(),
                        param_type: "int8_t *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "len".to_string(),
                        param_type: "size_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 92,
            },
            recovered_vars: &[],
            ssa_blocks: &ssa_blocks,
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert!(
            analysis
                .type_facts
                .array_index_certificates
                .iter()
                .any(|cert| {
                    cert.element_stride == 1
                        && cert.field_offset == 0
                        && matches!(
                            cert.base,
                            Some(ArrayIndexBase::StackSlot { ref slot }) if *slot == buf_slot
                        )
                }),
            "expected scalar typed stack pointer index certificate, got {:?}",
            analysis.type_facts.array_index_certificates
        );
    }

    #[test]
    fn typed_pointer_induction_access_certifies_scalar_array_index() {
        let parsed_context = ParsedExternalContext {
            register_params: vec![
                crate::context::ExternalRegisterParamSpec {
                    name: "buf".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Unsigned,
                    }))),
                    reg: "RDI".to_string(),
                },
                crate::context::ExternalRegisterParamSpec {
                    name: "n".to_string(),
                    ty: Some(CTypeLike::Typedef("size_t".to_string())),
                    reg: "RSI".to_string(),
                },
            ],
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                }),
                params: vec![
                    FunctionParamSpec {
                        name: "buf".to_string(),
                        ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                            bits: 8,
                            signedness: Signedness::Unsigned,
                        }))),
                    },
                    FunctionParamSpec {
                        name: "n".to_string(),
                        ty: Some(CTypeLike::Typedef("size_t".to_string())),
                    },
                ],
            }),
            ..ParsedExternalContext::default()
        };
        let ssa_blocks = [SSABlock {
            addr: 0x401500,
            size: 32,
            ops: vec![
                SSAOp::Phi {
                    dst: SSAVar::new("RDI", 2, 8),
                    sources: vec![SSAVar::new("RDI", 0, 8), SSAVar::new("RDI", 1, 8)],
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("RDI", 1, 8),
                    a: SSAVar::new("RDI", 2, 8),
                    b: SSAVar::new("const:1", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("byte", 1, 1),
                    space: "ram".to_string(),
                    addr: SSAVar::new("RDI", 2, 8),
                },
            ],
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.pointer_induction",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.pointer_induction".to_string(),
                signature: "uint64_t sym.pointer_induction(uint8_t *buf, size_t n)".to_string(),
                ret_type: "uint64_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "buf".to_string(),
                        param_type: "uint8_t *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "n".to_string(),
                        param_type: "size_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 92,
            },
            recovered_vars: &[],
            ssa_blocks: &ssa_blocks,
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert!(
            analysis
                .type_facts
                .array_index_certificates
                .iter()
                .any(|cert| {
                    cert.element_stride == 1
                        && cert.field_offset == 0
                        && matches!(cert.base, Some(ArrayIndexBase::Param { index: 0 }))
                }),
            "expected typed pointer induction array certificate, got {:?}",
            analysis.type_facts.array_index_certificates
        );
    }

    #[test]
    fn typed_argument_phi_livein_access_certifies_scalar_array_index() {
        let parsed_context = ParsedExternalContext {
            register_params: vec![crate::context::ExternalRegisterParamSpec {
                name: "buf".to_string(),
                ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                    bits: 8,
                    signedness: Signedness::Unsigned,
                }))),
                reg: "RDI".to_string(),
            }],
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Int {
                    bits: 64,
                    signedness: Signedness::Unsigned,
                }),
                params: vec![FunctionParamSpec {
                    name: "buf".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Unsigned,
                    }))),
                }],
            }),
            ..ParsedExternalContext::default()
        };
        let ssa_blocks = [SSABlock {
            addr: 0x401500,
            size: 8,
            ops: vec![SSAOp::Load {
                dst: SSAVar::new("byte", 1, 1),
                space: "ram".to_string(),
                addr: SSAVar::new("RDI", 1, 8),
            }],
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.pointer_livein",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.pointer_livein".to_string(),
                signature: "uint64_t sym.pointer_livein(uint8_t *buf)".to_string(),
                ret_type: "uint64_t".to_string(),
                params: vec![InferredSignatureParam {
                    name: "buf".to_string(),
                    param_type: "uint8_t *".to_string(),
                }],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 92,
            },
            recovered_vars: &[],
            ssa_blocks: &ssa_blocks,
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert!(
            analysis
                .type_facts
                .array_index_certificates
                .iter()
                .any(|cert| {
                    cert.element_stride == 1
                        && cert.field_offset == 0
                        && matches!(cert.base, Some(ArrayIndexBase::Param { index: 0 }))
                }),
            "expected typed argument phi/live-in array certificate, got {:?}",
            analysis.type_facts.array_index_certificates
        );
    }

    #[test]
    fn external_struct_pointer_strength_reduced_index_certifies_nested_array_fields() {
        let mut parsed_context = ParsedExternalContext::default();
        parsed_context.external_type_db.structs.insert(
            "item".to_string(),
            ExternalStruct {
                name: "Item".to_string(),
                fields: BTreeMap::from([
                    (
                        0,
                        ExternalField {
                            name: "id".to_string(),
                            offset: 0,
                            ty: Some("int32_t".to_string()),
                        },
                    ),
                    (
                        4,
                        ExternalField {
                            name: "flags".to_string(),
                            offset: 4,
                            ty: Some("uint16_t".to_string()),
                        },
                    ),
                    (
                        6,
                        ExternalField {
                            name: "len".to_string(),
                            offset: 6,
                            ty: Some("uint16_t".to_string()),
                        },
                    ),
                    (
                        8,
                        ExternalField {
                            name: "scores".to_string(),
                            offset: 8,
                            ty: Some("int32_t[4]".to_string()),
                        },
                    ),
                    (
                        24,
                        ExternalField {
                            name: "name".to_string(),
                            offset: 24,
                            ty: Some("char *".to_string()),
                        },
                    ),
                    (
                        32,
                        ExternalField {
                            name: "next".to_string(),
                            offset: 32,
                            ty: Some("Item *".to_string()),
                        },
                    ),
                ]),
            },
        );

        let ssa_blocks = [SSABlock {
            addr: 0x4012d0,
            size: 64,
            ops: vec![
                SSAOp::IntSExt {
                    dst: SSAVar::new("RSI", 1, 8),
                    src: SSAVar::new("ESI", 0, 4),
                },
                SSAOp::IntMult {
                    dst: SSAVar::new("tmp:4900", 1, 8),
                    a: SSAVar::new("RSI", 1, 8),
                    b: SSAVar::new("const:4", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("tmp:4a00", 1, 8),
                    a: SSAVar::new("RSI", 1, 8),
                    b: SSAVar::new("tmp:4900", 1, 8),
                },
                SSAOp::IntMult {
                    dst: SSAVar::new("tmp:4900", 2, 8),
                    a: SSAVar::new("tmp:4a00", 1, 8),
                    b: SSAVar::new("const:8", 0, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("elem", 1, 8),
                    a: SSAVar::new("RDI", 0, 8),
                    b: SSAVar::new("tmp:4900", 2, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("scores2", 1, 8),
                    a: SSAVar::new("elem", 1, 8),
                    b: SSAVar::new("const:10", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("score", 1, 4),
                    space: "ram".to_string(),
                    addr: SSAVar::new("scores2", 1, 8),
                },
                SSAOp::IntAdd {
                    dst: SSAVar::new("flags", 1, 8),
                    a: SSAVar::new("elem", 1, 8),
                    b: SSAVar::new("const:4", 0, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("flagv", 1, 2),
                    space: "ram".to_string(),
                    addr: SSAVar::new("flags", 1, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("idv", 1, 4),
                    space: "ram".to_string(),
                    addr: SSAVar::new("elem", 1, 8),
                },
            ],
        }];

        let analysis = build_type_writeback_analysis(TypeWritebackAnalysisInput {
            function_name: "sym.struct_nested_array",
            ptr_bits: 64,
            inferred_signature: InferredSignature {
                function_name: "sym.struct_nested_array".to_string(),
                signature:
                    "int32_t sym.struct_nested_array (Item * items, int32_t idx, int32_t add)"
                        .to_string(),
                ret_type: "int32_t".to_string(),
                params: vec![
                    InferredSignatureParam {
                        name: "items".to_string(),
                        param_type: "Item *".to_string(),
                    },
                    InferredSignatureParam {
                        name: "idx".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                    InferredSignatureParam {
                        name: "add".to_string(),
                        param_type: "int32_t".to_string(),
                    },
                ],
                callconv: "amd64".to_string(),
                arch: "x86-64".to_string(),
                confidence: 96,
                callconv_confidence: 92,
            },
            recovered_vars: &[],
            ssa_blocks: &ssa_blocks,
            parsed_context,
            local_structs: LocalStructArtifacts::default(),
            interproc_summary_set: None,
            diagnostics: TypeWritebackDiagnostics::default(),
        });

        assert!(
            analysis
                .type_facts
                .array_index_certificates
                .iter()
                .any(|cert| cert.element_stride == 40 && cert.field_offset == 0x10),
            "expected idx * sizeof(Item) proof for scores[2], got {:?}",
            analysis.type_facts.array_index_certificates
        );
        let certified_names = analysis
            .type_facts
            .field_access_certificates
            .iter()
            .map(|cert| cert.field_name.as_str())
            .collect::<BTreeSet<_>>();
        assert!(certified_names.contains("scores[2]"), "{certified_names:?}");
        assert!(certified_names.contains("flags"), "{certified_names:?}");
        assert!(certified_names.contains("id"), "{certified_names:?}");
    }
}
