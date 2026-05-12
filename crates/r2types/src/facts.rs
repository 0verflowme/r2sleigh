use std::collections::{BTreeMap, HashMap};

use crate::context::{
    ExternalRegisterParamSpec, ExternalStackSlotSpec, ExternalStackVarSpec, StackSlotKey,
    legacy_external_stack_vars_from_slots, stack_slots_from_legacy_external_stack_vars,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalleeFact {
    pub function_id: u64,
    pub name: Option<String>,
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
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub visible_bindings: Vec<VisibleBinding>,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    // Legacy compatibility view derived from canonical stack_slots when available.
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub interproc_diagnostics: InterprocFactDiagnostics,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFactInputs {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub visible_bindings: Vec<VisibleBinding>,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub local_field_accesses: Vec<LocalFieldAccessFact>,
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
            && self.known_function_signatures.is_empty()
            && self.register_params.is_empty()
            && self.stack_slots.is_empty()
            && self.visible_bindings.is_empty()
            && self.callee_facts.is_empty()
            && self.external_stack_vars.is_empty()
            && self.external_type_db.structs.is_empty()
            && self.external_type_db.unions.is_empty()
            && self.external_type_db.enums.is_empty()
            && self.external_type_db.diagnostics.is_empty()
            && self.slot_type_overrides.is_empty()
            && self.slot_field_profiles.is_empty()
            && self.interproc_diagnostics == InterprocFactDiagnostics::default()
            && self.diagnostics.is_empty()
    }

    pub fn canonicalized(self) -> Self {
        FunctionTypeFacts::builder(FunctionTypeFactInputs {
            merged_signature: self.merged_signature,
            known_function_signatures: self.known_function_signatures,
            register_params: self.register_params,
            stack_slots: self.stack_slots,
            visible_bindings: self.visible_bindings,
            callee_facts: self.callee_facts,
            external_stack_vars: self.external_stack_vars,
            external_type_db: self.external_type_db,
            slot_type_overrides: self.slot_type_overrides,
            slot_field_profiles: self.slot_field_profiles,
            local_field_accesses: Vec::new(),
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

        let Some(existing) = self.merged_signature.as_mut() else {
            self.merged_signature = Some(projection.signature);
            return SignatureProjectionResult::applied(true);
        };

        let changed = apply_signature_projection_to_existing(existing, &projection, ptr_bits);
        SignatureProjectionResult::applied(changed)
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
    signature_strength(signature) >= SIGNATURE_PROJECTION_STRONG_CONFIDENCE
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
) -> bool {
    if is_generic_signature_type(Some(existing)) {
        return true;
    }
    let Some(hint) = hint else {
        return false;
    };
    if crate::signature_infer::render_signature_type(existing, ptr_bits)
        == crate::signature_infer::render_signature_type(hint, ptr_bits)
    {
        return false;
    }
    if type_is_generated_local_struct_pointer(existing) && pointer_hint_is_authoritative(hint) {
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
            semantic_typedef_is_authoritative(&normalized)
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
                ) && crate::signature_infer::render_signature_type(existing, ptr_bits)
                    != crate::signature_infer::render_signature_type(hint, ptr_bits))
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
                && semantic_typedef_is_authoritative(hint_name)
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
) -> bool {
    if signature_hint_can_replace_existing(existing, hint, ptr_bits) {
        return true;
    }
    matches!(hint, Some(CTypeLike::Void)) && is_weak_storage_scalar_type(existing, ptr_bits)
}

pub fn summary_hint_can_replace_weak_existing(
    existing: &CTypeLike,
    hint: &CTypeLike,
    ptr_bits: u32,
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
                && semantic_typedef_is_authoritative(hint_name)
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
        "int" | "unsigned" | "unsigned int" | "int32_t" | "uint32_t"
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
) -> bool {
    let mut changed = false;
    let hint = &projection.signature;
    let exact_strong_projection =
        projection.exact_arity && projection.has_strong_signature_confidence();
    let can_replace_signature = exact_strong_projection
        && signature_can_be_replaced_by_projection(existing, hint, ptr_bits);

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
                        )
                }
            }
        };
        if should_replace_return && existing.ret_type != hint.ret_type {
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
                    || signature_hint_can_replace_existing(existing_ty, Some(hint_ty), ptr_bits)
            }
        };
        if should_replace_ty && existing_param.ty.as_ref() != Some(hint_ty) {
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
                    signature_hint_can_replace_existing(ty, hint_param.ty.as_ref(), ptr_bits)
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

fn pointer_hint_is_authoritative(hint: &CTypeLike) -> bool {
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
        CTypeLike::Typedef(name) => semantic_typedef_is_authoritative(name),
        _ => false,
    }
}

fn semantic_typedef_is_authoritative(name: &str) -> bool {
    crate::role_registry::semantic_typedef_is_authoritative(name)
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

        let FunctionTypeFactInputs {
            merged_signature,
            known_function_signatures,
            register_params,
            mut stack_slots,
            visible_bindings,
            callee_facts,
            external_stack_vars,
            external_type_db,
            slot_type_overrides,
            slot_field_profiles,
            interproc_diagnostics,
            diagnostics,
            ..
        } = self.inputs;

        if stack_slots.is_empty() && !external_stack_vars.is_empty() {
            stack_slots = stack_slots_from_legacy_external_stack_vars(&external_stack_vars);
        }

        let external_stack_vars = if stack_slots.is_empty() {
            external_stack_vars
        } else {
            legacy_external_stack_vars_from_slots(&stack_slots)
        };

        let mut diagnostics = diagnostics;
        diagnostics.extend(external_type_db.diagnostics.iter().cloned());
        dedup_preserving_order(&mut diagnostics);

        FunctionTypeFacts {
            merged_signature,
            known_function_signatures,
            register_params,
            stack_slots,
            visible_bindings,
            callee_facts,
            external_stack_vars,
            external_type_db,
            slot_type_overrides,
            slot_field_profiles,
            interproc_diagnostics,
            diagnostics,
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

pub fn parse_type_like_spec(spec: &str, ptr_bits: u32) -> Option<CTypeLike> {
    let mut ty = spec.trim();
    if ty.is_empty() {
        return None;
    }

    let mut array_size = None;
    if let Some(start) = ty.rfind('[')
        && ty.ends_with(']')
    {
        let len_str = &ty[start + 1..ty.len() - 1];
        array_size = if len_str.is_empty() {
            Some(None)
        } else {
            len_str.parse::<usize>().ok().map(Some)
        };
        ty = ty[..start].trim_end();
    }

    let mut ptr_count = 0usize;
    while let Some(rest) = ty.strip_suffix('*') {
        ptr_count += 1;
        ty = rest.trim_end();
    }
    let qualifier_filtered = ty
        .split_whitespace()
        .filter(|token| {
            !matches!(
                token.to_ascii_lowercase().as_str(),
                "const"
                    | "volatile"
                    | "restrict"
                    | "__restrict"
                    | "__restrict__"
                    | "__const"
                    | "__const__"
                    | "__volatile"
                    | "__volatile__"
            )
        })
        .collect::<Vec<_>>();
    let qualifier_filtered_storage = (qualifier_filtered.len() != ty.split_whitespace().count())
        .then(|| qualifier_filtered.join(" "));
    if let Some(filtered) = qualifier_filtered_storage.as_deref() {
        ty = filtered.trim();
    }

    let normalize_base = |raw: &str| {
        raw.chars()
            .filter(|ch| !ch.is_whitespace())
            .collect::<String>()
            .to_ascii_lowercase()
    };
    let base_key = normalize_base(ty);

    let mut base = if let Some(rest) = base_key.strip_prefix("int")
        && let Some(bits) = rest.strip_suffix("_t")
    {
        bits.parse::<u32>().ok().map(|bits| CTypeLike::Int {
            bits,
            signedness: Signedness::Signed,
        })
    } else if let Some(rest) = base_key.strip_prefix("uint")
        && let Some(bits) = rest.strip_suffix("_t")
    {
        bits.parse::<u32>().ok().map(|bits| CTypeLike::Int {
            bits,
            signedness: Signedness::Unsigned,
        })
    } else {
        match base_key.as_str() {
            "void" => Some(CTypeLike::Void),
            "bool" | "_bool" => Some(CTypeLike::Bool),
            "char" | "signedchar" => Some(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Signed,
            }),
            "unsignedchar" => Some(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Unsigned,
            }),
            "short" | "shortint" | "signedshort" | "signedshortint" => Some(CTypeLike::Int {
                bits: 16,
                signedness: Signedness::Signed,
            }),
            "unsignedshort" | "unsignedshortint" => Some(CTypeLike::Int {
                bits: 16,
                signedness: Signedness::Unsigned,
            }),
            "signed" | "int" | "signedint" => Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            "unsigned" | "unsignedint" => Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Unsigned,
            }),
            "long" | "longint" | "signedlong" | "signedlongint" | "longlong" | "longlongint"
            | "signedlonglong" | "signedlonglongint" => Some(CTypeLike::Int {
                bits: ptr_bits,
                signedness: Signedness::Signed,
            }),
            "unsignedlong"
            | "unsignedlongint"
            | "unsignedlonglong"
            | "unsignedlonglongint"
            | "size_t" => Some(CTypeLike::Int {
                bits: ptr_bits,
                signedness: Signedness::Unsigned,
            }),
            "ssize_t" => Some(CTypeLike::Int {
                bits: ptr_bits,
                signedness: Signedness::Signed,
            }),
            "float" => Some(CTypeLike::Float(32)),
            "double" => Some(CTypeLike::Float(64)),
            "unknown" | "unknown_t" | "undefined" | "undefined_t" => Some(CTypeLike::Unknown),
            _ if ty.to_ascii_lowercase().starts_with("struct ") => ty
                .split_whitespace()
                .nth(1)
                .map(|name| CTypeLike::Struct(name.to_string())),
            _ if ty.to_ascii_lowercase().starts_with("union ") => ty
                .split_whitespace()
                .nth(1)
                .map(|name| CTypeLike::Union(name.to_string())),
            _ if ty.to_ascii_lowercase().starts_with("enum ") => ty
                .split_whitespace()
                .nth(1)
                .map(|name| CTypeLike::Enum(name.to_string())),
            _ if is_c_typedef_name(ty) => Some(CTypeLike::Typedef(ty.to_string())),
            _ => None,
        }
    }?;

    if let Some(size) = array_size {
        base = CTypeLike::Array(Box::new(base), size);
    }
    for _ in 0..ptr_count {
        base = CTypeLike::Pointer(Box::new(base));
    }
    Some(base)
}

fn is_c_typedef_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
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
    fn builder_derives_legacy_stack_var_view_from_canonical_slots() {
        let spec = ExternalStackSlotSpec {
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
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            stack_slots: BTreeMap::from([(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -0x10,
                },
                spec.clone(),
            )]),
            external_stack_vars: HashMap::from([(
                -0x10,
                ExternalStackSlotSpec {
                    name: "stale".to_string(),
                    ..spec.clone()
                },
            )]),
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .external_stack_vars
                .get(&-0x10)
                .map(|slot| slot.name.as_str()),
            Some("count")
        );
    }

    #[test]
    fn builder_canonicalizes_stack_slots_from_legacy_input() {
        let spec = ExternalStackSlotSpec {
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
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            external_stack_vars: HashMap::from([(-0x10, spec)]),
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts.stack_slots.get(&StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x10,
            }),
            facts.external_stack_vars.get(&-0x10)
        );
    }

    #[test]
    fn parse_type_like_spec_accepts_const_qualified_pointers() {
        let signed_char_ptr = CTypeLike::Pointer(Box::new(CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Signed,
        }));
        let void_ptr = CTypeLike::Pointer(Box::new(CTypeLike::Void));

        assert_eq!(
            parse_type_like_spec("char const *", 64),
            Some(signed_char_ptr.clone())
        );
        assert_eq!(
            parse_type_like_spec("const char *", 64),
            Some(signed_char_ptr)
        );
        assert_eq!(parse_type_like_spec("void const *", 64), Some(void_ptr));
    }

    #[test]
    fn parse_type_like_spec_accepts_external_typedef_pointers() {
        assert_eq!(
            parse_type_like_spec("FILE *", 64),
            Some(CTypeLike::Pointer(Box::new(CTypeLike::Typedef(
                "FILE".to_string()
            ))))
        );
    }

    #[test]
    fn parse_type_like_spec_canonicalizes_c_bool_spelling() {
        assert_eq!(parse_type_like_spec("_Bool", 64), Some(CTypeLike::Bool));
        assert_eq!(
            parse_type_like_spec("_Bool *", 64),
            Some(CTypeLike::Pointer(Box::new(CTypeLike::Bool)))
        );
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
}
