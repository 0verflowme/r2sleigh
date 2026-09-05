use std::collections::{BTreeMap, BTreeSet, HashMap};

use serde::{Deserialize, Serialize};

use crate::context::{
    ExternalRegisterParamSpec, ExternalStackSlotRole, ExternalStackSlotSpec, StackSlotKey,
};
use crate::convert::CTypeLike;
use crate::external::ExternalTypeDb;
use crate::model::Signedness;

pub const SIGNATURE_PROJECTION_WEAK_CONFIDENCE: u8 = 55;
pub const SIGNATURE_PROJECTION_STRONG_CONFIDENCE: u8 = 96;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub return_type: CTypeLike,
    pub params: Vec<CTypeLike>,
    pub variadic: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalFieldAccessFact {
    pub slot: usize,
    pub field_offset: u64,
    pub field_name: String,
    pub field_type: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldAccessCertificate {
    pub slot: usize,
    pub field_offset: u64,
    pub field_name: String,
    pub field_type: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayIndexBase {
    Param { index: usize },
    StackSlot { slot: StackSlotKey },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArrayIndexCertificate {
    pub slot: usize,
    pub base: Option<ArrayIndexBase>,
    pub field_offset: u64,
    pub element_stride: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScalarArrayRenderCandidate {
    pub slot: usize,
    pub block_addr: u64,
    pub op_index: usize,
    pub is_write: bool,
    pub field_offset: u64,
    pub element_stride: u64,
    pub access_width: u32,
    pub index_value: Option<r2ssa::ValueId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum OutParamCertificateEvidence {
    SemanticTypeSeed,
    InterprocArgWrite,
    InterprocMemoryWrite,
    InterprocTransferDst,
    NativeWorkerWrite,
    NativeRegionWrite,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum OutParamCertificateSource {
    SemanticClaim {
        stable_id: u64,
        anchor: u64,
    },
    NativeWorkerSummary {
        stable_id: u64,
        anchor: u64,
        summary_kind: r2sym::NativeWorkerSummaryKind,
        param_index: usize,
    },
    NativeRegionSummary {
        stable_id: u64,
        anchor: u64,
        summary_kind: r2sym::NativeWorkerSummaryKind,
        param_index: usize,
    },
    InterprocSummaryEffect {
        function_id: u64,
        evidence: OutParamCertificateEvidence,
        param_index: usize,
        effect_index: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OutParamCertificate {
    pub param_index: usize,
    pub param_name: String,
    pub pointee_type: Option<String>,
    pub evidence: Vec<OutParamCertificateEvidence>,
    pub sources: Vec<OutParamCertificateSource>,
}

impl OutParamCertificate {
    pub fn has_source_identity(&self) -> bool {
        !self.evidence.is_empty()
            && self.sources.iter().any(|source| match source {
                OutParamCertificateSource::SemanticClaim { .. } => true,
                OutParamCertificateSource::NativeWorkerSummary { param_index, .. } => {
                    *param_index == self.param_index
                        && self
                            .evidence
                            .contains(&OutParamCertificateEvidence::NativeWorkerWrite)
                }
                OutParamCertificateSource::NativeRegionSummary { param_index, .. } => {
                    *param_index == self.param_index
                        && self
                            .evidence
                            .contains(&OutParamCertificateEvidence::NativeRegionWrite)
                }
                OutParamCertificateSource::InterprocSummaryEffect {
                    evidence,
                    param_index,
                    ..
                } => *param_index == self.param_index && self.evidence.contains(evidence),
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureCertificate {
    pub signature: FunctionSignatureSpec,
    pub confidence: u8,
    pub sources: Vec<SignatureCertificateSource>,
}

impl SignatureCertificate {
    pub fn from_signature(
        signature: &FunctionSignatureSpec,
        sources: impl IntoIterator<Item = SignatureCertificateSource>,
    ) -> Option<Self> {
        let mut sources = sources.into_iter().collect::<Vec<_>>();
        if sources.is_empty() {
            sources.push(SignatureCertificateSource::LocalInference);
        }
        sources.sort();
        sources.dedup();

        let source_authorizes_empty_arity = signature.params.is_empty()
            && sources
                .iter()
                .any(|source| source.authorizes_signature_writeback());
        let local_evidence_authorizes_inferred_arity = !signature.params.is_empty()
            && sources.iter().any(|source| {
                matches!(
                    source,
                    SignatureCertificateSource::LocalInference
                        | SignatureCertificateSource::CalleeSignature
                        | SignatureCertificateSource::SlotTypeOverride
                        | SignatureCertificateSource::SemanticProjection
                        | SignatureCertificateSource::InterprocSummary
                        | SignatureCertificateSource::SourceInterface
                )
            })
            && signature.params.iter().all(|param| param.ty.is_some());
        if !(signature_param_count_is_authoritative(signature)
            || source_authorizes_empty_arity
            || local_evidence_authorizes_inferred_arity)
        {
            return None;
        }

        Some(Self {
            signature: signature.clone(),
            confidence: signature_strength(signature),
            sources,
        })
    }

    pub fn authorizes_signature_writeback(&self) -> bool {
        self.confidence >= SIGNATURE_PROJECTION_STRONG_CONFIDENCE
            && self
                .sources
                .iter()
                .any(|source| source.authorizes_signature_writeback())
            && !self.signature.params.iter().any(|param| {
                signature_param_type_uncertified(
                    param.ty.as_ref(),
                    self.sources.iter().any(|source| {
                        matches!(
                            source,
                            SignatureCertificateSource::ExternalContext
                                | SignatureCertificateSource::TypeAssumption
                        )
                    }),
                )
            })
    }

    pub fn authorizes_signature_render(&self) -> bool {
        self.confidence >= SIGNATURE_PROJECTION_STRONG_CONFIDENCE
    }
}

fn signature_param_type_uncertified(ty: Option<&CTypeLike>, allow_void_pointer: bool) -> bool {
    if allow_void_pointer
        && matches!(
            ty,
            Some(CTypeLike::Pointer(inner)) if matches!(inner.as_ref(), CTypeLike::Void)
        )
    {
        return false;
    }
    is_generic_signature_type(ty)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SignatureCertificateSource {
    ExternalContext,
    LocalInference,
    CalleeSignature,
    TypeAssumption,
    SlotTypeOverride,
    SummaryRole,
    SummaryKind,
    SemanticProjection,
    InterprocSummary,
    /// The return type alone is projected from the immutable source function
    /// interface and matched to exact native return-value certificates. This
    /// does not certify parameter types or authorize signature writeback by
    /// itself.
    SourceReturnType,
    /// The whole signature is projected from the immutable source function
    /// interface's type graph: every parameter and the return carry the exact
    /// declared type the binding layer already uses. radare2's spelled
    /// signature is only the fallback where no graph was captured.
    SourceInterface,
}

impl SignatureCertificateSource {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ExternalContext => "external_context",
            Self::LocalInference => "local_inference",
            Self::CalleeSignature => "callee_signature",
            Self::TypeAssumption => "type_assumption",
            Self::SlotTypeOverride => "slot_type_override",
            Self::SummaryRole => "summary_role",
            Self::SummaryKind => "summary_kind",
            Self::SemanticProjection => "semantic_projection",
            Self::InterprocSummary => "interproc_summary",
            Self::SourceReturnType => "source_return_type",
            Self::SourceInterface => "source_interface",
        }
    }

    pub fn authorizes_signature_writeback(self) -> bool {
        matches!(
            self,
            Self::ExternalContext
                | Self::SourceInterface
                | Self::TypeAssumption
                | Self::SlotTypeOverride
                | Self::SemanticProjection
                | Self::InterprocSummary
        )
    }
}

impl From<SignatureProjectionSource> for SignatureCertificateSource {
    fn from(source: SignatureProjectionSource) -> Self {
        match source {
            SignatureProjectionSource::SummaryRole => Self::SummaryRole,
            SignatureProjectionSource::SummaryKind => Self::SummaryKind,
            SignatureProjectionSource::SemanticProjection => Self::SemanticProjection,
            SignatureProjectionSource::InterprocSummary => Self::InterprocSummary,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResolvedFieldLayout {
    pub owner_name: Option<String>,
    pub field_name: String,
    pub field_offset: u64,
    pub element_stride: Option<u64>,
}

impl ResolvedFieldLayout {
    pub fn direct(
        owner_name: Option<String>,
        field_offset: u64,
        field_name: impl Into<String>,
    ) -> Self {
        Self {
            owner_name,
            field_name: field_name.into(),
            field_offset,
            element_stride: None,
        }
    }

    pub fn indexed(
        owner_name: Option<String>,
        element_stride: u64,
        field_offset: u64,
        field_name: impl Into<String>,
    ) -> Self {
        Self {
            owner_name,
            field_name: field_name.into(),
            field_offset,
            element_stride: Some(element_stride),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionParamSpec {
    pub name: String,
    pub ty: Option<CTypeLike>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionSignatureSpec {
    pub ret_type: Option<CTypeLike>,
    pub params: Vec<FunctionParamSpec>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureProjectionSource {
    SummaryRole,
    SummaryKind,
    SemanticProjection,
    InterprocSummary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureProjectionRejection {
    WeakAnonymousFunction,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SignatureProjectionResult {
    pub changed: bool,
    pub rejected: Option<SignatureProjectionRejection>,
}

impl SignatureProjectionResult {
    pub fn applied(changed: bool) -> Self {
        Self {
            changed,
            rejected: None,
        }
    }

    pub fn rejected(rejected: SignatureProjectionRejection) -> Self {
        Self {
            changed: false,
            rejected: Some(rejected),
        }
    }

    pub fn was_applied(&self) -> bool {
        self.rejected.is_none()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionSignatureProjection {
    pub signature: FunctionSignatureSpec,
    pub source: SignatureProjectionSource,
    pub return_confidence: u8,
    pub default_param_confidence: u8,
    pub param_confidences: Vec<u8>,
    pub exact_arity: bool,
    pub allow_anonymous_function: bool,
}

impl FunctionSignatureProjection {
    pub fn new(signature: FunctionSignatureSpec, source: SignatureProjectionSource) -> Self {
        Self {
            exact_arity: signature_projection_is_exact(&signature),
            signature,
            source,
            return_confidence: SIGNATURE_PROJECTION_STRONG_CONFIDENCE,
            default_param_confidence: SIGNATURE_PROJECTION_STRONG_CONFIDENCE,
            param_confidences: Vec::new(),
            allow_anonymous_function: true,
        }
    }

    pub fn strong_summary(signature: FunctionSignatureSpec) -> Self {
        Self::new(signature, SignatureProjectionSource::SummaryRole)
    }

    pub fn weak_summary_kind(signature: FunctionSignatureSpec) -> Self {
        Self::new(signature, SignatureProjectionSource::SummaryKind)
            .with_return_confidence(SIGNATURE_PROJECTION_WEAK_CONFIDENCE)
            .with_default_param_confidence(SIGNATURE_PROJECTION_WEAK_CONFIDENCE)
            .with_exact_arity(false)
            .allow_anonymous_function(false)
    }

    pub fn with_return_confidence(mut self, confidence: u8) -> Self {
        self.return_confidence = confidence;
        self
    }

    pub fn with_default_param_confidence(mut self, confidence: u8) -> Self {
        self.default_param_confidence = confidence;
        self
    }

    pub fn with_param_confidences(mut self, confidences: Vec<u8>) -> Self {
        self.param_confidences = confidences;
        self
    }

    pub fn with_exact_arity(mut self, exact_arity: bool) -> Self {
        self.exact_arity = exact_arity;
        self
    }

    pub fn allow_anonymous_function(mut self, allow: bool) -> Self {
        self.allow_anonymous_function = allow;
        self
    }

    pub fn param_confidence(&self, index: usize) -> u8 {
        self.param_confidences
            .get(index)
            .copied()
            .unwrap_or(self.default_param_confidence)
    }

    pub fn signature_confidence(&self) -> u8 {
        self.signature
            .params
            .iter()
            .enumerate()
            .map(|(idx, _)| self.param_confidence(idx))
            .chain(std::iter::once(self.return_confidence))
            .min()
            .unwrap_or(self.return_confidence)
    }

    pub fn has_strong_signature_confidence(&self) -> bool {
        self.signature_confidence() >= SIGNATURE_PROJECTION_STRONG_CONFIDENCE
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisibleBindingKind {
    Param,
    Local,
    StackObject,
    HiddenHome,
    HiddenSaved,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VisibleBinding {
    pub name: String,
    pub ty: Option<CTypeLike>,
    pub kind: VisibleBindingKind,
    pub stack_slot: Option<StackSlotKey>,
    pub param_index: Option<usize>,
    pub source_reg: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CalleeArgEffect {
    pub read: bool,
    pub write: bool,
    pub escape: bool,
    pub free: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeMemoryEffectKind {
    Read,
    Write,
    Escape,
    Free,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeMemoryRegion {
    Arg { index: usize },
    Global { address: u64 },
    HeapReturn,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryRange {
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub width: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryLocation {
    pub region: CalleeMemoryRegion,
    pub range: Option<CalleeMemoryRange>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryEffect {
    pub kind: CalleeMemoryEffectKind,
    pub location: CalleeMemoryLocation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeTransferLength {
    Arg(usize),
    Const(u64),
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeTransferEffect {
    pub dst: CalleeMemoryLocation,
    pub src: CalleeMemoryLocation,
    pub len: CalleeTransferLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeAllocationEffect {
    pub size_arg: Option<usize>,
    pub zeroed: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeLifetimeOp {
    Free,
    Retain,
    Release,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeLifetimeEffect {
    pub arg: usize,
    pub op: CalleeLifetimeOp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeSyncOp {
    Lock,
    Unlock,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeSyncEffect {
    pub arg: usize,
    pub op: CalleeSyncOp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeAtomicOp {
    LoadLinked,
    StoreConditional,
    CompareExchange,
    Fence,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeAtomicOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeAtomicEffect {
    pub op: CalleeAtomicOp,
    pub location: CalleeMemoryLocation,
    pub ordering: CalleeAtomicOrdering,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CalleeReturnRelation {
    Unknown,
    Void,
    Arg(usize),
    Const(u64),
    HeapAlloc,
    Global(u64),
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeLinkage {
    #[default]
    Unknown,
    Internal,
    Imported,
}

impl CalleeLinkage {
    pub fn authorizes_import_policy(self) -> bool {
        matches!(self, Self::Imported)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeModelPolicyEvidence {
    InterprocSummary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalleeFact {
    pub function_id: u64,
    pub name: Option<String>,
    pub linkage: CalleeLinkage,
    pub signature: Option<FunctionType>,
    pub signature_callconv: Option<String>,
    pub signature_noreturn: bool,
    pub model_policy_evidence: BTreeSet<CalleeModelPolicyEvidence>,
    pub direct_callees: Vec<u64>,
    pub callsite_count: usize,
    pub has_unknown_calls: bool,
    pub arg_effects: BTreeMap<usize, CalleeArgEffect>,
    pub memory_effects: Vec<CalleeMemoryEffect>,
    pub transfer_effects: Vec<CalleeTransferEffect>,
    pub allocation_effects: Vec<CalleeAllocationEffect>,
    pub lifetime_effects: Vec<CalleeLifetimeEffect>,
    pub sync_effects: Vec<CalleeSyncEffect>,
    pub atomic_effects: Vec<CalleeAtomicEffect>,
    pub param_type_hints: BTreeMap<usize, CTypeLike>,
    pub return_type_hint: Option<CTypeLike>,
    pub return_relation: CalleeReturnRelation,
    pub reads_global_memory: bool,
    pub writes_global_memory: bool,
    pub touches_unknown_memory: bool,
}

pub(crate) const fn model_policy_authorized_from_evidence_count(evidence_count: usize) -> bool {
    evidence_count > 0
}

impl CalleeFact {
    pub fn authorizes_model_policy(&self) -> bool {
        model_policy_authorized_from_evidence_count(self.model_policy_evidence.len())
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InterprocFactDiagnostics {
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub scope_size: usize,
    pub scc_count: usize,
    pub max_scc_size: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFacts {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub callconv: Option<String>,
    pub noreturn: bool,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub visible_bindings: Vec<VisibleBinding>,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    pub external_type_db: ExternalTypeDb,
    pub program_data_objects: crate::ProgramDataObjectTypeFacts,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub field_access_certificates: Vec<FieldAccessCertificate>,
    pub array_index_certificates: Vec<ArrayIndexCertificate>,
    pub scalar_array_render_candidates: Vec<ScalarArrayRenderCandidate>,
    pub out_param_certificates: Vec<OutParamCertificate>,
    pub signature_certificate: Option<SignatureCertificate>,
    pub interproc_diagnostics: InterprocFactDiagnostics,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFactInputs {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub callconv: Option<String>,
    pub noreturn: bool,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub visible_bindings: Vec<VisibleBinding>,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    pub external_type_db: ExternalTypeDb,
    pub program_data_objects: crate::ProgramDataObjectTypeFacts,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub local_field_accesses: Vec<LocalFieldAccessFact>,
    pub field_access_certificates: Vec<FieldAccessCertificate>,
    pub array_index_certificates: Vec<ArrayIndexCertificate>,
    pub scalar_array_render_candidates: Vec<ScalarArrayRenderCandidate>,
    pub out_param_certificates: Vec<OutParamCertificate>,
    pub signature_certificate: Option<SignatureCertificate>,
    pub interproc_diagnostics: InterprocFactDiagnostics,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct FunctionTypeFactsBuilder {
    inputs: FunctionTypeFactInputs,
}

impl FunctionTypeFacts {
    pub fn is_empty(&self) -> bool {
        self.merged_signature.is_none()
            && self.callconv.is_none()
            && !self.noreturn
            && self.known_function_signatures.is_empty()
            && self.register_params.is_empty()
            && self.stack_slots.is_empty()
            && self.visible_bindings.is_empty()
            && self.callee_facts.is_empty()
            && self.external_type_db.structs.is_empty()
            && self.external_type_db.unions.is_empty()
            && self.external_type_db.enums.is_empty()
            && self.external_type_db.typedefs.is_empty()
            && self.external_type_db.diagnostics.is_empty()
            && self.program_data_objects == crate::ProgramDataObjectTypeFacts::default()
            && self.slot_type_overrides.is_empty()
            && self.slot_field_profiles.is_empty()
            && self.field_access_certificates.is_empty()
            && self.array_index_certificates.is_empty()
            && self.scalar_array_render_candidates.is_empty()
            && self.out_param_certificates.is_empty()
            && self.signature_certificate.is_none()
            && self.interproc_diagnostics == InterprocFactDiagnostics::default()
            && self.diagnostics.is_empty()
    }

    pub fn canonicalized(self) -> Self {
        FunctionTypeFacts::builder(FunctionTypeFactInputs {
            merged_signature: self.merged_signature,
            callconv: self.callconv,
            noreturn: self.noreturn,
            known_function_signatures: self.known_function_signatures,
            register_params: self.register_params,
            stack_slots: self.stack_slots,
            visible_bindings: self.visible_bindings,
            callee_facts: self.callee_facts,
            external_type_db: self.external_type_db,
            program_data_objects: self.program_data_objects,
            slot_type_overrides: self.slot_type_overrides,
            slot_field_profiles: self.slot_field_profiles,
            local_field_accesses: Vec::new(),
            field_access_certificates: self.field_access_certificates,
            array_index_certificates: self.array_index_certificates,
            scalar_array_render_candidates: self.scalar_array_render_candidates,
            out_param_certificates: self.out_param_certificates,
            signature_certificate: self.signature_certificate,
            interproc_diagnostics: self.interproc_diagnostics,
            diagnostics: self.diagnostics,
        })
        .build()
    }

    pub fn builder(inputs: FunctionTypeFactInputs) -> FunctionTypeFactsBuilder {
        FunctionTypeFactsBuilder::new(inputs)
    }

    pub fn apply_signature_projection(
        &mut self,
        function_name: &str,
        projection: FunctionSignatureProjection,
        ptr_bits: u32,
    ) -> SignatureProjectionResult {
        if projection_rejected_for_function(function_name, &projection).is_some() {
            return SignatureProjectionResult::rejected(
                SignatureProjectionRejection::WeakAnonymousFunction,
            );
        }

        // Borrowed before the mutable one below: these are disjoint fields, so
        // the type database stays readable while the signature is edited.
        let type_db = &self.external_type_db;
        let Some(existing) = self.merged_signature.as_mut() else {
            self.merged_signature = Some(projection.signature);
            return SignatureProjectionResult::applied(true);
        };

        let changed =
            apply_signature_projection_to_existing(existing, &projection, ptr_bits, type_db);
        SignatureProjectionResult::applied(changed)
    }

    pub fn certify_current_signature_with_source(
        &mut self,
        source: SignatureCertificateSource,
    ) -> bool {
        let Some(signature) = self.merged_signature.as_ref() else {
            self.signature_certificate = None;
            return false;
        };
        let mut sources = self
            .signature_certificate
            .as_ref()
            .filter(|certificate| certificate.signature == *signature)
            .map(|certificate| certificate.sources.clone())
            .unwrap_or_default();
        if !sources.contains(&source) {
            sources.push(source);
        }
        self.signature_certificate = SignatureCertificate::from_signature(signature, sources);
        self.signature_certificate.is_some()
    }

    pub fn render_authorized_signature(&self) -> Option<&FunctionSignatureSpec> {
        let certificate = self.signature_certificate.as_ref()?;
        if !certificate.authorizes_signature_render() {
            return None;
        }
        let signature = self.merged_signature.as_ref()?;
        (certificate.signature == *signature).then_some(signature)
    }

    pub fn writeback_authorized_signature(&self) -> Option<&FunctionSignatureSpec> {
        let certificate = self.signature_certificate.as_ref()?;
        if !certificate.authorizes_signature_writeback() {
            return None;
        }
        let signature = self.merged_signature.as_ref()?;
        (certificate.signature == *signature).then_some(signature)
    }

    pub fn source_authorized_out_param_certificates(
        &self,
    ) -> impl Iterator<Item = &OutParamCertificate> {
        self.out_param_certificates
            .iter()
            .filter(|certificate| certificate.has_source_identity())
    }
}

pub fn signature_projection_is_exact(signature: &FunctionSignatureSpec) -> bool {
    signature.ret_type.is_some()
        && signature
            .params
            .iter()
            .all(|param| !crate::context::is_generic_arg_name(&param.name) && param.ty.is_some())
}

pub fn signature_param_name_is_weak(name: &str) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    normalized.is_empty()
        || crate::context::is_generic_arg_name(&normalized)
        || matches!(
            normalized.as_str(),
            "status"
                | "err"
                | "errno"
                | "input"
                | "output"
                | "stream"
                | "value"
                | "val"
                | "slot"
                | "tmp"
                | "a"
                | "b"
                | "c"
                | "d"
                | "e"
                | "f"
        )
}

pub fn signature_strength(signature: &FunctionSignatureSpec) -> u8 {
    let has_type_info =
        signature.ret_type.is_some() || signature.params.iter().any(|param| param.ty.is_some());
    let has_named_params = signature
        .params
        .iter()
        .any(|param| !crate::context::is_generic_arg_name(&param.name));
    if has_type_info || has_named_params {
        SIGNATURE_PROJECTION_STRONG_CONFIDENCE
    } else {
        80
    }
}

pub fn signature_param_count_is_authoritative(signature: &FunctionSignatureSpec) -> bool {
    if signature.params.is_empty() {
        return false;
    }
    signature
        .params
        .iter()
        .any(|param| !crate::context::is_generic_arg_name(&param.name))
        && signature_strength(signature) >= SIGNATURE_PROJECTION_STRONG_CONFIDENCE
}

pub fn is_generic_signature_type(ty: Option<&CTypeLike>) -> bool {
    match ty {
        None => true,
        Some(CTypeLike::Unknown | CTypeLike::Void) => true,
        Some(CTypeLike::Pointer(inner)) => {
            matches!(inner.as_ref(), CTypeLike::Unknown | CTypeLike::Void)
        }
        _ => false,
    }
}

pub fn signature_hint_can_replace_existing(
    existing: &CTypeLike,
    hint: Option<&CTypeLike>,
    ptr_bits: u32,
    type_db: &crate::ExternalTypeDb,
) -> bool {
    if is_generic_signature_type(Some(existing)) {
        return true;
    }
    let Some(hint) = hint else {
        return false;
    };
    if crate::signature_infer::signature_types_are_equivalent(existing, hint, ptr_bits) {
        return false;
    }
    if type_is_generated_local_struct_pointer(existing)
        && pointer_hint_is_authoritative(hint, ptr_bits, type_db)
    {
        return true;
    }
    match (existing, hint) {
        (
            CTypeLike::Int {
                bits,
                signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
            },
            CTypeLike::Typedef(name),
        ) => {
            let normalized = name.trim().to_ascii_lowercase();
            crate::writeback::type_db_resolves_type_name(type_db, &normalized, ptr_bits)
                || matches!(normalized.as_str(), "int" | "unsigned int")
                || (normalized == "uintptr_t" && *bits == ptr_bits)
        }
        (
            CTypeLike::Int {
                signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
                ..
            },
            CTypeLike::Bool,
        ) => true,
        (
            CTypeLike::Int {
                signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
                ..
            },
            CTypeLike::Enum(_),
        ) => true,
        (
            CTypeLike::Int {
                bits,
                signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
            },
            CTypeLike::Pointer(_),
        ) => *bits == ptr_bits,
        (CTypeLike::Pointer(inner), CTypeLike::Pointer(new_inner)) => {
            matches!(inner.as_ref(), CTypeLike::Void | CTypeLike::Unknown)
                && !matches!(new_inner.as_ref(), CTypeLike::Void | CTypeLike::Unknown)
                || signature_hint_can_replace_existing(
                    inner.as_ref(),
                    Some(new_inner.as_ref()),
                    ptr_bits,
                    type_db,
                )
                || (matches!(
                    (inner.as_ref(), new_inner.as_ref()),
                    (
                        CTypeLike::Int {
                            bits: 8,
                            signedness: _
                        },
                        CTypeLike::Int {
                            bits: 8,
                            signedness: _
                        }
                    )
                ) && !crate::signature_infer::signature_types_are_equivalent(
                    existing, hint, ptr_bits,
                ))
                || (matches!(
                    new_inner.as_ref(),
                    CTypeLike::Typedef(_)
                        | CTypeLike::Struct(_)
                        | CTypeLike::Union(_)
                        | CTypeLike::Enum(_)
                ) && !matches!(
                    inner.as_ref(),
                    CTypeLike::Typedef(_)
                        | CTypeLike::Struct(_)
                        | CTypeLike::Union(_)
                        | CTypeLike::Enum(_)
                ))
        }
        (CTypeLike::Typedef(existing_name), CTypeLike::Typedef(hint_name)) => {
            is_weak_storage_scalar_typedef(existing_name, ptr_bits)
                && crate::writeback::type_db_resolves_type_name(type_db, hint_name, ptr_bits)
        }
        (CTypeLike::Typedef(existing_name), CTypeLike::Pointer(_)) => {
            is_weak_pointer_sized_storage_typedef(existing_name, ptr_bits)
        }
        _ => false,
    }
}

pub fn signature_return_hint_can_replace_existing(
    existing: &CTypeLike,
    hint: Option<&CTypeLike>,
    ptr_bits: u32,
    type_db: &crate::ExternalTypeDb,
) -> bool {
    if signature_hint_can_replace_existing(existing, hint, ptr_bits, type_db) {
        return true;
    }
    matches!(hint, Some(CTypeLike::Void)) && is_weak_storage_scalar_type(existing, ptr_bits)
}

pub fn summary_hint_can_replace_weak_existing(
    existing: &CTypeLike,
    hint: &CTypeLike,
    ptr_bits: u32,
    type_db: &crate::ExternalTypeDb,
) -> bool {
    if is_generic_signature_type(Some(existing)) {
        return true;
    }
    match (existing, hint) {
        (CTypeLike::Pointer(inner), CTypeLike::Pointer(new_inner)) => {
            matches!(**inner, CTypeLike::Void | CTypeLike::Unknown)
                && !matches!(**new_inner, CTypeLike::Void | CTypeLike::Unknown)
        }
        (
            CTypeLike::Int {
                bits,
                signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
            },
            CTypeLike::Int {
                bits: hint_bits,
                signedness: Signedness::Unsigned,
            },
        ) => *bits == ptr_bits && *hint_bits == ptr_bits,
        (
            CTypeLike::Int {
                bits,
                signedness: Signedness::Signed | Signedness::Unsigned | Signedness::Unknown,
            },
            CTypeLike::Pointer(_),
        ) => *bits == ptr_bits,
        (CTypeLike::Typedef(existing_name), CTypeLike::Typedef(hint_name)) => {
            is_weak_storage_scalar_typedef(existing_name, ptr_bits)
                && crate::writeback::type_db_resolves_type_name(type_db, hint_name, ptr_bits)
        }
        (CTypeLike::Typedef(existing_name), CTypeLike::Pointer(_)) => {
            is_weak_pointer_sized_storage_typedef(existing_name, ptr_bits)
        }
        _ => false,
    }
}

pub fn type_is_generated_local_struct_pointer(ty: &CTypeLike) -> bool {
    matches!(
        ty,
        CTypeLike::Pointer(inner)
            if matches!(
                inner.as_ref(),
                CTypeLike::Struct(name) | CTypeLike::Typedef(name)
                    if generated_local_struct_name(name)
            )
    )
}

pub fn is_weak_storage_scalar_type(ty: &CTypeLike, ptr_bits: u32) -> bool {
    match ty {
        CTypeLike::Int { .. } => true,
        CTypeLike::Typedef(name) => is_weak_storage_scalar_typedef(name, ptr_bits),
        _ => false,
    }
}

pub fn is_weak_storage_scalar_typedef(name: &str, ptr_bits: u32) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    matches!(
        normalized.as_str(),
        "char"
            | "signed char"
            | "unsigned char"
            | "short"
            | "unsigned short"
            | "int"
            | "unsigned"
            | "unsigned int"
            | "int8_t"
            | "uint8_t"
            | "int16_t"
            | "uint16_t"
            | "int32_t"
            | "uint32_t"
    ) || (ptr_bits == 64
        && matches!(
            normalized.as_str(),
            "long" | "unsigned long" | "int64_t" | "uint64_t"
        ))
}

pub fn is_weak_pointer_sized_storage_typedef(name: &str, ptr_bits: u32) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    (ptr_bits == 64
        && matches!(
            normalized.as_str(),
            "long" | "unsigned long" | "int64_t" | "uint64_t"
        ))
        || (ptr_bits == 32
            && matches!(
                normalized.as_str(),
                "int" | "unsigned" | "unsigned int" | "int32_t" | "uint32_t"
            ))
}

fn apply_signature_projection_to_existing(
    existing: &mut FunctionSignatureSpec,
    projection: &FunctionSignatureProjection,
    ptr_bits: u32,
    type_db: &crate::ExternalTypeDb,
) -> bool {
    let mut changed = false;
    let hint = &projection.signature;
    let exact_strong_projection =
        projection.exact_arity && projection.has_strong_signature_confidence();
    let can_replace_signature = exact_strong_projection
        && signature_can_be_replaced_by_projection(existing, hint, ptr_bits, type_db);

    if can_replace_signature && existing.params.len() > hint.params.len() {
        existing.params.truncate(hint.params.len());
        changed = true;
    }

    if existing.params.len() < hint.params.len()
        && (can_replace_signature || !signature_param_count_is_authoritative(existing))
    {
        existing
            .params
            .resize_with(hint.params.len(), || FunctionParamSpec {
                name: String::new(),
                ty: None,
            });
        changed = true;
    }

    if projection.return_confidence >= SIGNATURE_PROJECTION_WEAK_CONFIDENCE {
        let should_replace_return = match existing.ret_type.as_ref() {
            None => hint.ret_type.is_some(),
            Some(existing_ty) => {
                if projection.return_confidence < SIGNATURE_PROJECTION_STRONG_CONFIDENCE {
                    is_generic_signature_type(Some(existing_ty)) && hint.ret_type.is_some()
                } else {
                    can_replace_signature
                        || signature_return_hint_can_replace_existing(
                            existing_ty,
                            hint.ret_type.as_ref(),
                            ptr_bits,
                            type_db,
                        )
                }
            }
        };
        let return_is_different = match (existing.ret_type.as_ref(), hint.ret_type.as_ref()) {
            (Some(existing), Some(hint)) => {
                !crate::signature_infer::signature_types_are_equivalent(existing, hint, ptr_bits)
            }
            (existing, hint) => existing != hint,
        };
        if should_replace_return && return_is_different {
            existing.ret_type = hint.ret_type.clone();
            changed = true;
        }
    }

    for (idx, hint_param) in hint.params.iter().enumerate() {
        let Some(existing_param) = existing.params.get_mut(idx) else {
            continue;
        };
        let confidence = projection.param_confidence(idx);
        if confidence < SIGNATURE_PROJECTION_WEAK_CONFIDENCE {
            continue;
        }

        if !hint_param.name.is_empty()
            && (existing_param.name.is_empty()
                || crate::context::is_generic_arg_name(&existing_param.name)
                || (can_replace_signature && signature_param_name_is_weak(&existing_param.name)))
            && existing_param.name != hint_param.name
        {
            existing_param.name = hint_param.name.clone();
            changed = true;
        }

        let Some(hint_ty) = hint_param.ty.as_ref() else {
            continue;
        };
        let should_replace_ty = match existing_param.ty.as_ref() {
            None => true,
            Some(existing_ty) if confidence < SIGNATURE_PROJECTION_STRONG_CONFIDENCE => {
                is_generic_signature_type(Some(existing_ty))
            }
            Some(existing_ty) => {
                can_replace_signature
                    || signature_hint_can_replace_existing(
                        existing_ty,
                        Some(hint_ty),
                        ptr_bits,
                        type_db,
                    )
            }
        };
        if should_replace_ty
            && existing_param.ty.as_ref().is_none_or(|existing_ty| {
                !crate::signature_infer::signature_types_are_equivalent(
                    existing_ty,
                    hint_ty,
                    ptr_bits,
                )
            })
        {
            existing_param.ty = Some(hint_ty.clone());
            changed = true;
        }
    }

    changed
}

fn signature_can_be_replaced_by_projection(
    existing: &FunctionSignatureSpec,
    hint: &FunctionSignatureSpec,
    ptr_bits: u32,
    type_db: &crate::ExternalTypeDb,
) -> bool {
    if existing.params.is_empty() {
        return true;
    }
    if existing.params.len() < hint.params.len() {
        return true;
    }
    existing.params.iter().enumerate().all(|(idx, param)| {
        let weak_name = signature_param_name_is_weak(&param.name);
        let hint_param = hint.params.get(idx);
        let compatible_name = weak_name
            || hint_param
                .is_some_and(|hint_param| param.name.eq_ignore_ascii_case(&hint_param.name));
        let weak_type = param.ty.as_ref().is_none_or(|ty| {
            is_generic_signature_type(Some(ty))
                || hint_param.is_some_and(|hint_param| {
                    signature_hint_can_replace_existing(
                        ty,
                        hint_param.ty.as_ref(),
                        ptr_bits,
                        type_db,
                    )
                })
                || (hint_param.is_none() && type_is_generated_local_struct_pointer(ty))
                || is_weak_storage_scalar_type(ty, ptr_bits)
        });
        compatible_name && weak_type
    })
}

fn projection_rejected_for_function(
    function_name: &str,
    projection: &FunctionSignatureProjection,
) -> Option<SignatureProjectionRejection> {
    if projection.allow_anonymous_function {
        return None;
    }
    if projection.signature_confidence() >= SIGNATURE_PROJECTION_STRONG_CONFIDENCE {
        return None;
    }
    anonymous_function_name(function_name)
        .then_some(SignatureProjectionRejection::WeakAnonymousFunction)
}

fn anonymous_function_name(function_name: &str) -> bool {
    let normalized = function_name.trim().to_ascii_lowercase();
    if normalized.is_empty() {
        return false;
    }
    matches!(
        normalized
            .strip_prefix("sym.")
            .or_else(|| normalized.strip_prefix("dbg."))
            .unwrap_or(&normalized),
        name if name.starts_with("fcn.") || name.starts_with("sub.") || name.starts_with("fcn_") || name.starts_with("sub_")
    )
}

fn pointer_hint_is_authoritative(
    hint: &CTypeLike,
    ptr_bits: u32,
    type_db: &crate::ExternalTypeDb,
) -> bool {
    let CTypeLike::Pointer(inner) = hint else {
        return false;
    };
    match inner.as_ref() {
        CTypeLike::Bool
        | CTypeLike::Int { .. }
        | CTypeLike::Struct(_)
        | CTypeLike::Union(_)
        | CTypeLike::Enum(_)
        | CTypeLike::Pointer(_) => true,
        CTypeLike::Typedef(name) => {
            crate::writeback::type_db_resolves_type_name(type_db, name, ptr_bits)
        }
        _ => false,
    }
}

fn generated_local_struct_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .trim_start_matches("struct ")
        .starts_with("sla_struct_")
}

impl FunctionTypeFactsBuilder {
    pub fn new(inputs: FunctionTypeFactInputs) -> Self {
        Self { inputs }
    }

    pub fn build(mut self) -> FunctionTypeFacts {
        merge_local_field_accesses(
            &mut self.inputs.slot_field_profiles,
            &self.inputs.local_field_accesses,
        );
        let mut field_access_certificates =
            std::mem::take(&mut self.inputs.field_access_certificates);
        field_access_certificates.extend(self.inputs.local_field_accesses.iter().map(|access| {
            FieldAccessCertificate {
                slot: access.slot,
                field_offset: access.field_offset,
                field_name: access.field_name.clone(),
                field_type: access.field_type.clone(),
            }
        }));
        field_access_certificates.sort();
        field_access_certificates.dedup();
        let mut array_index_certificates =
            std::mem::take(&mut self.inputs.array_index_certificates);
        array_index_certificates.sort();
        array_index_certificates.dedup();
        let mut scalar_array_render_candidates =
            std::mem::take(&mut self.inputs.scalar_array_render_candidates);
        scalar_array_render_candidates.sort();
        scalar_array_render_candidates.dedup();
        let mut out_param_certificates = std::mem::take(&mut self.inputs.out_param_certificates);
        out_param_certificates.retain(OutParamCertificate::has_source_identity);
        out_param_certificates.sort();
        out_param_certificates.dedup();

        let FunctionTypeFactInputs {
            mut merged_signature,
            callconv,
            noreturn,
            known_function_signatures,
            mut register_params,
            mut stack_slots,
            mut visible_bindings,
            callee_facts,
            external_type_db,
            program_data_objects,
            slot_type_overrides,
            slot_field_profiles,
            mut signature_certificate,
            interproc_diagnostics,
            diagnostics,
            ..
        } = self.inputs;

        canonicalize_generic_param_names(
            &mut merged_signature,
            &mut signature_certificate,
            &mut register_params,
            &mut stack_slots,
            &mut visible_bindings,
        );

        let mut diagnostics = diagnostics;
        diagnostics.extend(external_type_db.diagnostics.iter().cloned());
        dedup_preserving_order(&mut diagnostics);

        FunctionTypeFacts {
            merged_signature,
            callconv,
            noreturn,
            known_function_signatures,
            register_params,
            stack_slots,
            visible_bindings,
            callee_facts,
            external_type_db,
            program_data_objects,
            slot_type_overrides,
            slot_field_profiles,
            field_access_certificates,
            array_index_certificates,
            scalar_array_render_candidates,
            out_param_certificates,
            signature_certificate,
            interproc_diagnostics,
            diagnostics,
        }
    }
}

fn canonical_generic_param_name(index: usize, name: &str) -> String {
    if crate::context::is_generic_arg_name(name) {
        format!("arg{index}")
    } else {
        name.to_string()
    }
}

fn canonicalize_signature_generic_param_names(signature: &mut FunctionSignatureSpec) {
    for (index, param) in signature.params.iter_mut().enumerate() {
        param.name = canonical_generic_param_name(index, &param.name);
    }
}

fn canonicalize_generic_param_names(
    merged_signature: &mut Option<FunctionSignatureSpec>,
    signature_certificate: &mut Option<SignatureCertificate>,
    register_params: &mut [ExternalRegisterParamSpec],
    stack_slots: &mut BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    visible_bindings: &mut [VisibleBinding],
) {
    if let Some(signature) = merged_signature.as_mut() {
        canonicalize_signature_generic_param_names(signature);
    }
    if let Some(certificate) = signature_certificate.as_mut() {
        canonicalize_signature_generic_param_names(&mut certificate.signature);
    }
    for (index, param) in register_params.iter_mut().enumerate() {
        param.name = canonical_generic_param_name(index, &param.name);
    }
    for slot in stack_slots.values_mut() {
        let Some(index) = slot.param_index else {
            continue;
        };
        if let Some(name) = slot.param_name.as_mut() {
            *name = canonical_generic_param_name(index, name);
        }
        if matches!(slot.role, ExternalStackSlotRole::StackArg)
            && crate::context::is_generic_arg_name(&slot.name)
        {
            slot.name = format!("arg{index}");
        }
    }
    for binding in visible_bindings {
        let Some(index) = binding.param_index else {
            continue;
        };
        if matches!(binding.kind, VisibleBindingKind::Param) {
            binding.name = canonical_generic_param_name(index, &binding.name);
        }
    }
}

fn merge_local_field_accesses(
    slot_field_profiles: &mut HashMap<usize, BTreeMap<u64, String>>,
    local_field_accesses: &[LocalFieldAccessFact],
) {
    for access in local_field_accesses {
        slot_field_profiles
            .entry(access.slot)
            .or_default()
            .entry(access.field_offset)
            .or_insert_with(|| {
                access
                    .field_type
                    .clone()
                    .unwrap_or_else(|| access.field_name.clone())
            });
    }
}

fn dedup_preserving_order(items: &mut Vec<String>) {
    let mut seen = std::collections::HashSet::new();
    items.retain(|item| seen.insert(item.clone()));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ExternalStackBase, ExternalStackSlotRole};

    fn test_int(bits: u32) -> CTypeLike {
        CTypeLike::Int {
            bits,
            signedness: Signedness::Signed,
        }
    }

    fn test_typedef(name: &str) -> CTypeLike {
        CTypeLike::Typedef(name.to_string())
    }

    fn test_ptr(inner: CTypeLike) -> CTypeLike {
        CTypeLike::Pointer(Box::new(inner))
    }

    fn test_param(name: &str, ty: CTypeLike) -> FunctionParamSpec {
        FunctionParamSpec {
            name: name.to_string(),
            ty: Some(ty),
        }
    }

    fn exact_signature() -> FunctionSignatureSpec {
        FunctionSignatureSpec {
            ret_type: Some(test_int(32)),
            params: vec![test_param("value", test_int(32))],
        }
    }

    #[test]
    fn local_only_signature_certificate_does_not_authorize_writeback() {
        let certificate = SignatureCertificate::from_signature(
            &exact_signature(),
            [SignatureCertificateSource::LocalInference],
        )
        .expect("exact local signature should still be recorded as a certificate");

        assert!(
            !certificate.authorizes_signature_writeback(),
            "local inference alone is not enough evidence to mutate radare2 signature state"
        );
    }

    #[test]
    fn source_return_type_certificate_does_not_certify_parameter_writeback() {
        let certificate = SignatureCertificate::from_signature(
            &exact_signature(),
            [SignatureCertificateSource::SourceReturnType],
        )
        .expect("an exact return projection should remain renderable");

        assert!(certificate.authorizes_signature_render());
        assert!(!certificate.authorizes_signature_writeback());
        assert_eq!(
            SignatureCertificateSource::SourceReturnType.as_str(),
            "source_return_type"
        );
    }

    #[test]
    fn local_inference_certifies_typed_generic_parameter_names_for_rendering() {
        let signature = FunctionSignatureSpec {
            ret_type: Some(test_int(32)),
            params: vec![
                test_param("arg0", test_int(64)),
                test_param("arg1", test_int(32)),
            ],
        };
        let certificate = SignatureCertificate::from_signature(
            &signature,
            [SignatureCertificateSource::LocalInference],
        )
        .expect("SSA-proven typed parameters should certify rendering");

        assert!(certificate.authorizes_signature_render());
        assert!(!certificate.authorizes_signature_writeback());
    }

    #[test]
    fn external_signature_certificate_authorizes_writeback() {
        let certificate = SignatureCertificate::from_signature(
            &exact_signature(),
            [SignatureCertificateSource::ExternalContext],
        )
        .expect("exact external signature should be certifiable");

        assert!(
            certificate.authorizes_signature_writeback(),
            "external typed context is authoritative signature evidence"
        );
    }

    #[test]
    fn external_empty_signature_certificate_authorizes_exact_empty_arity() {
        let signature = FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Void),
            params: Vec::new(),
        };
        let certificate = SignatureCertificate::from_signature(
            &signature,
            [SignatureCertificateSource::ExternalContext],
        )
        .expect("external void(void) signature should certify exact empty arity");

        assert!(certificate.authorizes_signature_writeback());
        assert!(certificate.signature.params.is_empty());
    }

    #[test]
    fn external_void_pointer_params_are_certifiable_context_types() {
        let signature = FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Void),
            params: vec![FunctionParamSpec {
                name: "dst".to_string(),
                ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Void))),
            }],
        };
        let certificate = SignatureCertificate::from_signature(
            &signature,
            [SignatureCertificateSource::ExternalContext],
        )
        .expect("external void pointer parameters are explicit C types");

        assert!(certificate.authorizes_signature_writeback());
    }

    #[test]
    fn external_name_only_signature_authorizes_render_not_writeback() {
        let signature = FunctionSignatureSpec {
            ret_type: None,
            params: vec![FunctionParamSpec {
                name: "count".to_string(),
                ty: None,
            }],
        };
        let certificate = SignatureCertificate::from_signature(
            &signature,
            [SignatureCertificateSource::ExternalContext],
        )
        .expect("external name and arity evidence should be renderable");

        assert!(certificate.authorizes_signature_render());
        assert!(
            !certificate.authorizes_signature_writeback(),
            "incomplete parameter types must not mutate radare2 signature state"
        );
    }

    #[test]
    fn current_signature_certification_preserves_and_adds_sources() {
        let mut facts = FunctionTypeFacts {
            merged_signature: Some(exact_signature()),
            signature_certificate: SignatureCertificate::from_signature(
                &exact_signature(),
                [SignatureCertificateSource::ExternalContext],
            ),
            ..FunctionTypeFacts::default()
        };

        assert!(
            facts.certify_current_signature_with_source(
                SignatureCertificateSource::SemanticProjection
            )
        );
        let certificate = facts
            .signature_certificate
            .expect("current signature should remain certified");

        assert_eq!(
            certificate.sources,
            vec![
                SignatureCertificateSource::ExternalContext,
                SignatureCertificateSource::SemanticProjection,
            ]
        );
    }

    #[test]
    fn render_authorized_signature_requires_matching_certificate() {
        let signature = exact_signature();
        let different_signature = FunctionSignatureSpec {
            ret_type: Some(test_int(32)),
            params: vec![test_param("other", test_int(32))],
        };
        let facts = FunctionTypeFacts {
            merged_signature: Some(signature),
            signature_certificate: SignatureCertificate::from_signature(
                &different_signature,
                [SignatureCertificateSource::ExternalContext],
            ),
            ..FunctionTypeFacts::default()
        };

        assert!(
            facts.render_authorized_signature().is_none(),
            "consumers must not render a merged signature that is not the certified signature"
        );
    }

    #[test]
    fn render_authorized_signature_returns_certified_current_signature() {
        let signature = exact_signature();
        let facts = FunctionTypeFacts {
            merged_signature: Some(signature.clone()),
            signature_certificate: SignatureCertificate::from_signature(
                &signature,
                [SignatureCertificateSource::ExternalContext],
            ),
            ..FunctionTypeFacts::default()
        };

        assert_eq!(facts.render_authorized_signature(), Some(&signature));
    }

    #[test]
    fn writeback_authorized_signature_rejects_render_only_certificate() {
        let signature = FunctionSignatureSpec {
            ret_type: None,
            params: vec![FunctionParamSpec {
                name: "count".to_string(),
                ty: None,
            }],
        };
        let facts = FunctionTypeFacts {
            merged_signature: Some(signature),
            signature_certificate: SignatureCertificate::from_signature(
                &FunctionSignatureSpec {
                    ret_type: None,
                    params: vec![FunctionParamSpec {
                        name: "count".to_string(),
                        ty: None,
                    }],
                },
                [SignatureCertificateSource::ExternalContext],
            ),
            ..FunctionTypeFacts::default()
        };

        assert!(facts.render_authorized_signature().is_some());
        assert!(facts.writeback_authorized_signature().is_none());
    }

    #[test]
    fn out_param_certificate_requires_source_identity() {
        let unsourced = OutParamCertificate {
            param_index: 0,
            param_name: "out".to_string(),
            pointee_type: Some("int".to_string()),
            evidence: vec![OutParamCertificateEvidence::InterprocArgWrite],
            sources: Vec::new(),
        };
        assert!(!unsourced.has_source_identity());

        let mismatched_source = OutParamCertificate {
            sources: vec![OutParamCertificateSource::InterprocSummaryEffect {
                function_id: 0x401000,
                evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                param_index: 1,
                effect_index: 0,
            }],
            ..unsourced.clone()
        };
        assert!(!mismatched_source.has_source_identity());

        let sourced = OutParamCertificate {
            sources: vec![OutParamCertificateSource::InterprocSummaryEffect {
                function_id: 0x401000,
                evidence: OutParamCertificateEvidence::InterprocArgWrite,
                param_index: 0,
                effect_index: 0,
            }],
            ..unsourced.clone()
        };
        assert!(sourced.has_source_identity());

        let mismatched_native_param = OutParamCertificate {
            param_index: 0,
            param_name: "out".to_string(),
            pointee_type: Some("int".to_string()),
            evidence: vec![OutParamCertificateEvidence::NativeWorkerWrite],
            sources: vec![OutParamCertificateSource::NativeWorkerSummary {
                stable_id: 0x55,
                anchor: 0x401000,
                summary_kind: r2sym::NativeWorkerSummaryKind::MemoryWrite,
                param_index: 1,
            }],
        };
        assert!(!mismatched_native_param.has_source_identity());

        let mismatched_native_evidence = OutParamCertificate {
            evidence: vec![OutParamCertificateEvidence::NativeRegionWrite],
            sources: vec![OutParamCertificateSource::NativeWorkerSummary {
                stable_id: 0x55,
                anchor: 0x401000,
                summary_kind: r2sym::NativeWorkerSummaryKind::MemoryWrite,
                param_index: 0,
            }],
            ..mismatched_native_param
        };
        assert!(!mismatched_native_evidence.has_source_identity());
    }

    #[test]
    fn builder_rejects_unsourced_out_param_certificates() {
        let unsourced = OutParamCertificate {
            param_index: 0,
            param_name: "out".to_string(),
            pointee_type: Some("int".to_string()),
            evidence: vec![OutParamCertificateEvidence::InterprocArgWrite],
            sources: Vec::new(),
        };
        let sourced = OutParamCertificate {
            param_index: 1,
            param_name: "written".to_string(),
            pointee_type: Some("char".to_string()),
            evidence: vec![OutParamCertificateEvidence::NativeWorkerWrite],
            sources: vec![OutParamCertificateSource::NativeWorkerSummary {
                stable_id: 0x55,
                anchor: 0x401000,
                summary_kind: r2sym::NativeWorkerSummaryKind::MemoryWrite,
                param_index: 1,
            }],
        };

        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            out_param_certificates: vec![unsourced, sourced.clone()],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(facts.out_param_certificates, vec![sourced]);
        assert_eq!(
            facts
                .source_authorized_out_param_certificates()
                .collect::<Vec<_>>(),
            facts.out_param_certificates.iter().collect::<Vec<_>>()
        );
    }

    #[test]
    fn builder_merges_local_field_accesses_into_slot_profiles() {
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            local_field_accesses: vec![
                LocalFieldAccessFact {
                    slot: 1,
                    field_offset: 0,
                    field_name: "first".to_string(),
                    field_type: None,
                },
                LocalFieldAccessFact {
                    slot: 1,
                    field_offset: 8,
                    field_name: "second".to_string(),
                    field_type: None,
                },
            ],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .slot_field_profiles
                .get(&1)
                .and_then(|profile| profile.get(&0)),
            Some(&"first".to_string())
        );
        assert_eq!(
            facts
                .slot_field_profiles
                .get(&1)
                .and_then(|profile| profile.get(&8)),
            Some(&"second".to_string())
        );
        assert_eq!(
            facts.field_access_certificates,
            vec![
                FieldAccessCertificate {
                    slot: 1,
                    field_offset: 0,
                    field_name: "first".to_string(),
                    field_type: None,
                },
                FieldAccessCertificate {
                    slot: 1,
                    field_offset: 8,
                    field_name: "second".to_string(),
                    field_type: None,
                },
            ],
            "local field facts should remain as explicit r2types-owned layout certificates"
        );
    }

    #[test]
    fn builder_preserves_explicit_slot_profile_names() {
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            slot_field_profiles: HashMap::from([(
                2,
                BTreeMap::from([(0, "explicit".to_string())]),
            )]),
            local_field_accesses: vec![LocalFieldAccessFact {
                slot: 2,
                field_offset: 0,
                field_name: "local".to_string(),
                field_type: None,
            }],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .slot_field_profiles
                .get(&2)
                .and_then(|profile| profile.get(&0)),
            Some(&"explicit".to_string())
        );
    }

    #[test]
    fn builder_prefers_local_field_access_type_when_present() {
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            local_field_accesses: vec![LocalFieldAccessFact {
                slot: 3,
                field_offset: 4,
                field_name: "f_4".to_string(),
                field_type: Some("int32_t".to_string()),
            }],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .slot_field_profiles
                .get(&3)
                .and_then(|profile| profile.get(&4)),
            Some(&"int32_t".to_string())
        );
    }

    #[test]
    fn builder_merges_external_diagnostics_once() {
        let external = ExternalTypeDb {
            diagnostics: vec!["warning".to_string(), "warning".to_string()],
            ..ExternalTypeDb::default()
        };
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            external_type_db: external,
            diagnostics: vec!["warning".to_string(), "local".to_string()],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts.diagnostics,
            vec!["warning".to_string(), "local".to_string()]
        );
    }

    #[test]
    fn builder_canonicalizes_generic_parameter_names_by_slot() {
        let signature = FunctionSignatureSpec {
            ret_type: Some(test_int(32)),
            params: vec![
                FunctionParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(test_int(64)),
                },
                FunctionParamSpec {
                    name: "arg2".to_string(),
                    ty: Some(test_int(32)),
                },
            ],
        };
        let certificate = SignatureCertificate::from_signature(
            &signature,
            [SignatureCertificateSource::LocalInference],
        );
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            merged_signature: Some(signature),
            signature_certificate: certificate,
            register_params: vec![
                ExternalRegisterParamSpec {
                    name: "arg1".to_string(),
                    ty: Some(test_int(64)),
                    reg: "rdi".to_string(),
                },
                ExternalRegisterParamSpec {
                    name: "arg2".to_string(),
                    ty: Some(test_int(32)),
                    reg: "rsi".to_string(),
                },
            ],
            visible_bindings: vec![VisibleBinding {
                name: "arg1".to_string(),
                ty: Some(test_int(64)),
                kind: VisibleBindingKind::Param,
                stack_slot: None,
                param_index: Some(0),
                source_reg: Some("rdi".to_string()),
            }],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        let signature = facts.render_authorized_signature().expect("signature");
        assert_eq!(signature.params[0].name, "arg0");
        assert_eq!(signature.params[1].name, "arg1");
        assert_eq!(facts.register_params[0].name, "arg0");
        assert_eq!(facts.register_params[1].name, "arg1");
        assert_eq!(facts.visible_bindings[0].name, "arg0");
    }

    #[test]
    fn builder_preserves_structural_stack_slot_root() {
        let spec = ExternalStackSlotSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            stack_slots: BTreeMap::from([(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -0x10,
                },
                spec.clone(),
            )]),
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .stack_slots
                .get(&StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -0x10,
                })
                .map(|slot| slot.name.as_str()),
            Some("count")
        );
        assert!(!facts.stack_slots.contains_key(&StackSlotKey {
            base: ExternalStackBase::StackPointer,
            offset: -0x10,
        }));
    }

    #[test]
    fn weak_summary_kind_projection_rejects_anonymous_fcn_signature() {
        let original = FunctionSignatureSpec {
            ret_type: Some(test_int(64)),
            params: vec![test_param("arg1", test_int(64))],
        };
        let mut facts = FunctionTypeFacts {
            merged_signature: Some(original.clone()),
            ..FunctionTypeFacts::default()
        };
        let projection = FunctionSignatureProjection::weak_summary_kind(FunctionSignatureSpec {
            ret_type: None,
            params: vec![
                test_param("dst", test_ptr(CTypeLike::Void)),
                test_param("src", test_ptr(CTypeLike::Void)),
                test_param("len", test_typedef("size_t")),
            ],
        });

        let result = facts.apply_signature_projection("fcn.00401000", projection, 64);

        assert_eq!(
            result.rejected,
            Some(SignatureProjectionRejection::WeakAnonymousFunction)
        );
        assert_eq!(facts.merged_signature, Some(original));
    }

    #[test]
    fn generated_typed_arg_names_do_not_make_arity_authoritative() {
        let generated = FunctionSignatureSpec {
            ret_type: Some(test_int(64)),
            params: vec![test_param("arg1", test_int(64))],
        };
        let named = FunctionSignatureSpec {
            ret_type: Some(test_int(64)),
            params: vec![test_param("value", test_int(64))],
        };

        assert!(!signature_param_count_is_authoritative(&generated));
        assert!(signature_param_count_is_authoritative(&named));
    }

    #[test]
    fn strong_summary_projection_preserves_exact_arity_and_names() {
        let mut facts = FunctionTypeFacts {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(test_int(64)),
                params: vec![
                    test_param("arg1", test_int(64)),
                    test_param("arg2", test_int(64)),
                ],
            }),
            ..FunctionTypeFacts::default()
        };
        let projection = FunctionSignatureProjection::strong_summary(FunctionSignatureSpec {
            ret_type: Some(test_typedef("size_t")),
            params: vec![test_param(
                "buffer",
                test_ptr(CTypeLike::Int {
                    bits: 8,
                    signedness: Signedness::Signed,
                }),
            )],
        });

        let result = facts.apply_signature_projection("sym.render_buffer", projection, 64);
        let signature = facts.merged_signature.expect("signature");

        assert!(result.was_applied());
        assert_eq!(signature.ret_type, Some(test_typedef("size_t")));
        assert_eq!(signature.params.len(), 1);
        assert_eq!(signature.params[0].name, "buffer");
        assert_eq!(
            signature.params[0].ty,
            Some(test_ptr(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Signed,
            }))
        );
    }

    #[test]
    fn strong_summary_projection_upgrades_nested_storage_pointers_to_typedefs() {
        let mut facts = FunctionTypeFacts {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(test_typedef("size_t")),
                params: vec![test_param(
                    "token_lengths",
                    test_ptr(test_ptr(CTypeLike::Int {
                        bits: 64,
                        signedness: Signedness::Unsigned,
                    })),
                )],
            }),
            ..FunctionTypeFacts::default()
        };
        let projection = FunctionSignatureProjection::strong_summary(FunctionSignatureSpec {
            ret_type: Some(test_typedef("size_t")),
            params: vec![test_param(
                "token_lengths",
                test_ptr(test_ptr(test_typedef("size_t"))),
            )],
        });

        let result = facts.apply_signature_projection("dbg.readtokens", projection, 64);
        let signature = facts.merged_signature.expect("signature");

        assert!(result.was_applied());
        assert_eq!(
            signature.params[0].ty,
            Some(test_ptr(test_ptr(test_typedef("size_t"))))
        );
    }

    #[test]
    fn signature_projection_uses_explicit_return_and_param_confidence() {
        let mut facts = FunctionTypeFacts {
            merged_signature: Some(FunctionSignatureSpec {
                ret_type: Some(test_typedef("ssize_t")),
                params: vec![test_param("arg1", test_int(64))],
            }),
            ..FunctionTypeFacts::default()
        };
        let projection = FunctionSignatureProjection::strong_summary(FunctionSignatureSpec {
            ret_type: Some(test_typedef("size_t")),
            params: vec![test_param("count", test_typedef("size_t"))],
        })
        .with_return_confidence(10)
        .with_default_param_confidence(SIGNATURE_PROJECTION_STRONG_CONFIDENCE);

        let result = facts.apply_signature_projection("sym.count_items", projection, 64);
        let signature = facts.merged_signature.expect("signature");

        assert!(result.was_applied());
        assert_eq!(signature.ret_type, Some(test_typedef("ssize_t")));
        assert_eq!(signature.params[0].name, "count");
        assert_eq!(signature.params[0].ty, Some(test_typedef("size_t")));
    }

    #[test]
    fn equivalent_signature_spellings_do_not_report_a_rewrite() {
        let source_int = test_typedef("int");
        let canonical_int = test_int(32);
        let original = FunctionSignatureSpec {
            ret_type: Some(source_int.clone()),
            params: vec![test_param("value", source_int)],
        };
        let mut facts = FunctionTypeFacts {
            merged_signature: Some(original.clone()),
            ..FunctionTypeFacts::default()
        };
        let projection = FunctionSignatureProjection::strong_summary(FunctionSignatureSpec {
            ret_type: Some(canonical_int.clone()),
            params: vec![test_param("value", canonical_int)],
        });

        let result = facts.apply_signature_projection("sym.identity", projection, 64);

        assert!(result.was_applied());
        assert!(!result.changed);
        assert_eq!(facts.merged_signature, Some(original));
    }
}
