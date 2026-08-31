use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::convert::CTypeLike;
use crate::external::{
    ExternalEnum, ExternalField, ExternalStruct, ExternalTypeDb, ExternalUnion,
    normalize_external_type_name,
};
use crate::facts::{
    CalleeFact, CalleeLinkage, CalleeReturnRelation, FunctionParamSpec, FunctionSignatureSpec,
    FunctionType, FunctionTypeFacts, SignatureCertificate, SignatureCertificateSource,
    parse_type_like_spec,
};
use crate::signature_infer::render_signature_type;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExternalRegisterParamSpec {
    pub name: String,
    pub ty: Option<CTypeLike>,
    pub reg: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExternalStackSlotSpec {
    pub name: String,
    pub ty: Option<CTypeLike>,
    pub base: ExternalStackBase,
    pub role: ExternalStackSlotRole,
    pub param_index: Option<usize>,
    pub param_name: Option<String>,
    pub source_reg: Option<String>,
}

pub type ExternalStackVarSpec = ExternalStackSlotSpec;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ParsedExternalContext {
    pub context_schema_version: Option<u64>,
    pub context_dirty_epoch: Option<u64>,
    pub type_dirty_epoch: Option<u64>,
    pub context_hash: Option<u64>,
    pub current_signature: Option<FunctionSignatureSpec>,
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    // Legacy compatibility view derived from canonical stack_slots.
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    pub assumptions: r2ssa::AssumptionSet,
    pub diagnostics: Vec<String>,
    pub callconv: Option<String>,
    pub noreturn: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExternalStackBase {
    FramePointer,
    StackPointer,
    Named(String),
}

impl Default for ExternalStackBase {
    fn default() -> Self {
        Self::Named("stack".to_string())
    }
}

impl ExternalStackBase {
    pub fn assumption_base(&self) -> Option<r2ssa::StackAddressBase> {
        match self {
            Self::FramePointer => Some(r2ssa::StackAddressBase::FramePointer),
            Self::StackPointer => Some(r2ssa::StackAddressBase::StackPointer),
            Self::Named(_) => None,
        }
    }

    pub fn legacy_name(&self) -> Option<String> {
        match self {
            Self::FramePointer => Some("rbp".to_string()),
            Self::StackPointer => Some("rsp".to_string()),
            Self::Named(name) if !name.is_empty() => Some(name.clone()),
            Self::Named(_) => None,
        }
    }
}

impl From<r2ssa::StackAddressBase> for ExternalStackBase {
    fn from(base: r2ssa::StackAddressBase) -> Self {
        match base {
            r2ssa::StackAddressBase::FramePointer => Self::FramePointer,
            r2ssa::StackAddressBase::StackPointer => Self::StackPointer,
        }
    }
}

#[derive(
    Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
#[serde(rename_all = "snake_case")]
pub enum ExternalStackSlotRole {
    Local,
    StackArg,
    ParamHome,
    SavedReg,
    SavedFp,
    #[default]
    Unknown,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StackSlotKey {
    pub base: ExternalStackBase,
    pub offset: i64,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExternalVarKind {
    Register,
    #[default]
    Stack,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalSignatureParamJson {
    pub name: Option<String>,
    #[serde(default, rename = "type")]
    pub ty: Option<String>,
    #[serde(default)]
    pub cc_reg: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalSignatureJson {
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default, rename = "ret")]
    pub ret_type: Option<String>,
    #[serde(default)]
    pub callconv: Option<String>,
    #[serde(default)]
    pub noreturn: bool,
    #[serde(default)]
    pub params: Vec<ExternalSignatureParamJson>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalContextMetadataJson {
    #[serde(default)]
    pub schema_version: Option<u64>,
    #[serde(default)]
    pub dirty_epoch: Option<u64>,
    #[serde(default)]
    pub type_dirty_epoch: Option<u64>,
    #[serde(default)]
    pub context_hash: Option<u64>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalVarJson {
    pub kind: ExternalVarKind,
    pub name: String,
    #[serde(default, rename = "type")]
    pub ty: Option<String>,
    #[serde(default)]
    pub is_arg: bool,
    #[serde(default)]
    pub reg: Option<String>,
    #[serde(default)]
    pub base: Option<String>,
    #[serde(default)]
    pub offset: Option<i64>,
    #[serde(default)]
    pub role: Option<ExternalStackSlotRole>,
    #[serde(default)]
    pub param_index: Option<usize>,
    #[serde(default)]
    pub param_name: Option<String>,
    #[serde(default)]
    pub source_reg: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalBaseTypeMemberJson {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub offset: u64,
    #[serde(default)]
    pub size_bits: Option<u64>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalEnumVariantJson {
    pub name: String,
    pub value: i64,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExternalBaseTypeKind {
    #[default]
    Struct,
    Union,
    Enum,
    Typedef,
    Atomic,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalBaseTypeJson {
    pub kind: ExternalBaseTypeKind,
    pub name: String,
    #[serde(default)]
    pub members: Vec<ExternalBaseTypeMemberJson>,
    #[serde(default)]
    pub variants: Vec<ExternalEnumVariantJson>,
    #[serde(default, rename = "type")]
    pub ty: Option<String>,
    #[serde(default)]
    pub size_bits: Option<u64>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct KnownSignatureJson {
    pub name: String,
    #[serde(default, rename = "ret")]
    pub ret_type: Option<String>,
    #[serde(default)]
    pub args: Vec<ExternalSignatureParamJson>,
    #[serde(default)]
    pub variadic: bool,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExternalCalleeLinkageJson {
    #[default]
    Unknown,
    Internal,
    Imported,
}

impl From<ExternalCalleeLinkageJson> for CalleeLinkage {
    fn from(value: ExternalCalleeLinkageJson) -> Self {
        match value {
            ExternalCalleeLinkageJson::Unknown => Self::Unknown,
            ExternalCalleeLinkageJson::Internal => Self::Internal,
            ExternalCalleeLinkageJson::Imported => Self::Imported,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalCalleeJson {
    #[serde(default)]
    pub call_addr: Option<u64>,
    pub addr: u64,
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default)]
    pub linkage: ExternalCalleeLinkageJson,
    #[serde(default)]
    pub signature: Option<ExternalSignatureJson>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternalContextJson {
    #[serde(default)]
    pub context: Option<ExternalContextMetadataJson>,
    #[serde(default)]
    pub signature: Option<ExternalSignatureJson>,
    #[serde(default)]
    pub vars: Vec<ExternalVarJson>,
    #[serde(default)]
    pub base_types: Vec<ExternalBaseTypeJson>,
    #[serde(default)]
    pub callees: Vec<ExternalCalleeJson>,
    #[serde(default)]
    pub known_signatures: Vec<KnownSignatureJson>,
    #[serde(default)]
    pub assumptions: Vec<r2ssa::AnalysisAssumption>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalAssumptionPayloadParseError {
    InvalidAssumptionArray,
}

impl ExternalAssumptionPayloadParseError {
    pub fn message(self) -> &'static str {
        match self {
            Self::InvalidAssumptionArray => "assumptions json is invalid",
        }
    }
}

impl fmt::Display for ExternalAssumptionPayloadParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.message())
    }
}

impl std::error::Error for ExternalAssumptionPayloadParseError {}

pub fn normalize_function_basename(name: &str) -> String {
    let mut lower = name.trim().to_ascii_lowercase();
    for prefix in ["sym.imp.", "sym.", "dbg.", "fcn.", "imp."] {
        if let Some(rest) = lower.strip_prefix(prefix) {
            lower = rest.to_string();
            break;
        }
    }
    if let Some(rest) = lower.strip_prefix('_')
        && rest == "main"
    {
        return "main".to_string();
    }
    lower
}

fn function_signature_lookup_names(name: &str) -> Vec<String> {
    let trimmed = name.trim();
    if trimmed.is_empty() {
        return Vec::new();
    }

    let mut candidates = Vec::new();

    push_signature_lookup_name(&mut candidates, trimmed);

    let mut stripped = trimmed;
    loop {
        let Some(next) = ["sym.imp.", "sym.", "dbg.", "fcn.", "imp."]
            .into_iter()
            .find_map(|prefix| stripped.strip_prefix(prefix))
        else {
            break;
        };
        push_signature_lookup_name(&mut candidates, next);
        stripped = next;
    }

    let snapshot = candidates.clone();
    for candidate in snapshot {
        if let Some(alias) = compiler_helper_signature_alias(&candidate) {
            push_signature_lookup_name(&mut candidates, alias);
        }
    }

    candidates
}

fn push_signature_lookup_name(candidates: &mut Vec<String>, candidate: &str) {
    let candidate = candidate.trim();
    if candidate.is_empty() {
        return;
    }
    if !candidates.iter().any(|existing| existing == candidate) {
        candidates.push(candidate.to_string());
    }
}

fn compiler_helper_signature_alias(name: &str) -> Option<&str> {
    for prefix in ["__isoc99_", "__libc_", "__GI_"] {
        if let Some(rest) = name.strip_prefix(prefix)
            && !rest.is_empty()
            && (prefix != "__libc_" || !rest.contains("_main"))
        {
            return Some(rest);
        }
    }
    let stripped = name.trim_start_matches('_');
    if stripped.len() < name.len() && !stripped.is_empty() {
        return Some(stripped);
    }
    None
}

pub fn is_c_main_function(name: &str) -> bool {
    normalize_function_basename(name) == "main"
}

pub fn canonical_main_signature_spec() -> FunctionSignatureSpec {
    let char_ptr = CTypeLike::Pointer(Box::new(CTypeLike::Int {
        bits: 8,
        signedness: crate::Signedness::Signed,
    }));
    let char_pp = CTypeLike::Pointer(Box::new(char_ptr));
    FunctionSignatureSpec {
        ret_type: Some(CTypeLike::Typedef("int".to_string())),
        params: vec![
            FunctionParamSpec {
                name: "argc".to_string(),
                ty: Some(CTypeLike::Typedef("int".to_string())),
            },
            FunctionParamSpec {
                name: "argv".to_string(),
                ty: Some(char_pp.clone()),
            },
            FunctionParamSpec {
                name: "envp".to_string(),
                ty: Some(char_pp),
            },
        ],
    }
}

pub fn merge_signature_with_register_params(
    signature: Option<FunctionSignatureSpec>,
    register_params: &[ExternalRegisterParamSpec],
) -> Option<FunctionSignatureSpec> {
    if register_params.is_empty() {
        return signature;
    }

    let mut signature = signature.unwrap_or_default();
    if signature.params.is_empty() {
        signature.params = register_params
            .iter()
            .map(|param| FunctionParamSpec {
                name: param.name.clone(),
                ty: param.ty.clone(),
            })
            .collect();
        return Some(signature);
    }

    let allow_param_count_extension = !signature_param_count_is_authoritative(&signature);
    for (idx, reg_param) in register_params.iter().enumerate() {
        if let Some(existing) = signature.params.get_mut(idx) {
            if is_generic_signature_type(existing.ty.as_ref())
                && !is_generic_signature_type(reg_param.ty.as_ref())
            {
                existing.ty = reg_param.ty.clone();
            }
            if is_generic_arg_name(&existing.name) && !is_generic_arg_name(&reg_param.name) {
                existing.name = reg_param.name.clone();
            }
        } else if allow_param_count_extension {
            signature.params.push(FunctionParamSpec {
                name: reg_param.name.clone(),
                ty: reg_param.ty.clone(),
            });
        }
    }

    Some(signature)
}

fn normalize_signature_param_name(name: &str) -> String {
    name.trim()
        .trim_start_matches('_')
        .to_ascii_lowercase()
        .replace('-', "_")
}

fn signature_spec_has_main_abi_evidence(signature: &FunctionSignatureSpec) -> bool {
    let mut names = signature
        .params
        .iter()
        .map(|param| normalize_signature_param_name(&param.name))
        .collect::<Vec<_>>();
    names.retain(|name| !name.is_empty());
    let has_argc = names.iter().any(|name| name == "argc");
    let has_argv = names.iter().any(|name| name == "argv");
    let has_envp = names.iter().any(|name| name == "envp" || name == "env");
    has_argc && (has_argv || has_envp)
}

pub fn apply_main_signature_override(
    function_name: &str,
    merged_signature: &mut Option<FunctionSignatureSpec>,
) -> bool {
    if !is_c_main_function(function_name) {
        return false;
    }
    let Some(signature) = merged_signature.as_ref() else {
        return false;
    };
    if !signature_spec_has_main_abi_evidence(signature) {
        return false;
    }
    let canonical = canonical_main_signature_spec();
    if merged_signature.as_ref() == Some(&canonical) {
        return false;
    }
    *merged_signature = Some(canonical);
    true
}

pub fn function_type_facts_from_parsed_context(
    function_name: &str,
    parsed_context: &ParsedExternalContext,
) -> FunctionTypeFacts {
    let mut merged_signature = parsed_context
        .merged_signature
        .clone()
        .or_else(|| parsed_context.current_signature.clone());
    apply_main_signature_override(function_name, &mut merged_signature);
    let signature_certificate = merged_signature.as_ref().and_then(|signature| {
        SignatureCertificate::from_signature(
            signature,
            [SignatureCertificateSource::ExternalContext],
        )
    });
    FunctionTypeFacts {
        merged_signature,
        callconv: parsed_context.callconv.clone(),
        noreturn: parsed_context.noreturn,
        signature_certificate,
        known_function_signatures: parsed_context.known_function_signatures.clone(),
        register_params: parsed_context.register_params.clone(),
        stack_slots: parsed_context.stack_slots.clone(),
        external_stack_vars: parsed_context.external_stack_vars.clone(),
        external_type_db: parsed_context.external_type_db.clone(),
        callee_facts: parsed_context.callee_facts.clone(),
        diagnostics: parsed_context.diagnostics.clone(),
        ..FunctionTypeFacts::default()
    }
}

pub fn parse_external_context_json(json_str: &str, ptr_bits: u32) -> ParsedExternalContext {
    let trimmed = json_str.trim();
    if trimmed.is_empty() || trimmed == "{}" || trimmed == "[]" {
        return ParsedExternalContext::default();
    }

    let Ok(raw) = serde_json::from_str::<ExternalContextJson>(trimmed) else {
        let mut parsed = ParsedExternalContext::default();
        parsed
            .diagnostics
            .push("failed to parse external context json".to_string());
        return parsed;
    };

    parse_external_context(raw, ptr_bits)
}

pub fn parse_external_assumption_payload_json(
    json_str: &str,
    ptr_bits: u32,
) -> Result<r2ssa::AssumptionSet, ExternalAssumptionPayloadParseError> {
    let trimmed = json_str.trim();
    if trimmed.is_empty() {
        return Ok(r2ssa::AssumptionSet::default());
    }

    if trimmed.starts_with('[') {
        let raw_items = serde_json::from_str::<Vec<serde_json::Value>>(trimmed)
            .map_err(|_| ExternalAssumptionPayloadParseError::InvalidAssumptionArray)?;
        let assumptions = raw_items
            .into_iter()
            .map(|item| {
                let has_provenance = item
                    .as_object()
                    .is_some_and(|object| object.contains_key("provenance"));
                let mut assumption = serde_json::from_value::<r2ssa::AnalysisAssumption>(item)
                    .map_err(|_| ExternalAssumptionPayloadParseError::InvalidAssumptionArray)?;
                if !has_provenance {
                    assumption.provenance = r2ssa::AssumptionProvenance::User;
                }
                Ok(assumption)
            })
            .collect::<Result<Vec<_>, ExternalAssumptionPayloadParseError>>()?;
        return Ok(r2ssa::AssumptionSet::new(assumptions));
    }

    Ok(parse_external_context_json(trimmed, ptr_bits).assumptions)
}

pub fn parse_external_context(raw: ExternalContextJson, ptr_bits: u32) -> ParsedExternalContext {
    let mut parsed = ParsedExternalContext::default();

    if let Some(context) = raw.context.as_ref() {
        parsed.context_schema_version = context.schema_version;
        parsed.context_dirty_epoch = context.dirty_epoch;
        parsed.type_dirty_epoch = context.type_dirty_epoch;
        parsed.context_hash = context.context_hash;
    }

    if let Some(signature) = raw.signature.as_ref() {
        parsed.current_signature = parse_signature_json(signature, ptr_bits);
        parsed.callconv = signature.callconv.clone();
        parsed.noreturn = signature.noreturn;
    }

    parsed.external_type_db = external_type_db_from_base_types(&raw.base_types, ptr_bits);
    parsed.callee_facts = parse_external_callees(&raw.callees, ptr_bits);
    parsed.known_function_signatures = parse_known_signatures(&raw.known_signatures, ptr_bits);
    if parsed.current_signature.is_none()
        && let Some(signature) = raw.signature.as_ref()
        && let Some(name) = signature.name.as_deref()
    {
        parsed.current_signature =
            signature_spec_from_known_name(name, &parsed.known_function_signatures);
    }
    if let Some(signature) = parsed.current_signature.as_mut() {
        resolve_signature_aliases_from_type_db(signature, &parsed.external_type_db);
    }

    let max_register_params = parsed
        .current_signature
        .as_ref()
        .filter(|signature| signature_param_count_is_authoritative(signature))
        .map(|signature| signature.params.len());
    let (register_params, stack_slots) = parse_external_vars(
        &raw.vars,
        ptr_bits,
        max_register_params,
        parsed.current_signature.as_ref(),
    );
    parsed.register_params = register_params;
    parsed.stack_slots = stack_slots;
    resolve_register_param_aliases_from_type_db(
        &mut parsed.register_params,
        &parsed.external_type_db,
    );
    resolve_stack_slot_aliases_from_type_db(&mut parsed.stack_slots, &parsed.external_type_db);
    parsed.merged_signature = merge_signature_with_register_params(
        parsed.current_signature.clone(),
        &parsed.register_params,
    );
    parsed.assumptions = imported_assumptions_from_context(
        &raw.assumptions,
        &parsed.register_params,
        &parsed.stack_slots,
        &parsed.external_type_db,
        ptr_bits,
    );

    parsed
}

fn callee_linkage_rank(linkage: CalleeLinkage) -> u8 {
    match linkage {
        CalleeLinkage::Unknown => 0,
        CalleeLinkage::Internal => 1,
        CalleeLinkage::Imported => 2,
    }
}

fn merge_callee_linkage(existing: CalleeLinkage, incoming: CalleeLinkage) -> CalleeLinkage {
    if callee_linkage_rank(incoming) > callee_linkage_rank(existing) {
        incoming
    } else {
        existing
    }
}

fn parse_external_callees(
    callees: &[ExternalCalleeJson],
    ptr_bits: u32,
) -> BTreeMap<u64, CalleeFact> {
    let mut facts = BTreeMap::new();
    let mut seen_call_addrs: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
    for callee in callees {
        let name = callee
            .name
            .as_deref()
            .map(str::trim)
            .filter(|name| !name.is_empty())
            .map(ToOwned::to_owned);
        let linkage = CalleeLinkage::from(callee.linkage);
        let entry = facts.entry(callee.addr).or_insert_with(|| CalleeFact {
            function_id: callee.addr,
            name: name.clone(),
            linkage,
            signature: None,
            signature_callconv: None,
            signature_noreturn: false,
            model_policy_evidence: BTreeSet::new(),
            direct_callees: Vec::new(),
            callsite_count: 0,
            has_unknown_calls: false,
            arg_effects: BTreeMap::new(),
            memory_effects: Vec::new(),
            transfer_effects: Vec::new(),
            allocation_effects: Vec::new(),
            lifetime_effects: Vec::new(),
            sync_effects: Vec::new(),
            atomic_effects: Vec::new(),
            param_type_hints: BTreeMap::new(),
            return_type_hint: None,
            return_relation: CalleeReturnRelation::Unknown,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        });
        if entry.name.is_none() {
            entry.name = name;
        }
        entry.linkage = merge_callee_linkage(entry.linkage, linkage);
        if let Some(signature) = callee.signature.as_ref() {
            if entry.signature.is_none() {
                entry.signature = function_type_from_signature_json(signature, ptr_bits);
            }
            if entry.signature_callconv.is_none() {
                entry.signature_callconv = signature
                    .callconv
                    .as_deref()
                    .map(str::trim)
                    .filter(|callconv| !callconv.is_empty())
                    .map(ToOwned::to_owned);
            }
            entry.signature_noreturn |= signature.noreturn;
        }
        if let Some(call_addr) = callee.call_addr {
            let seen = seen_call_addrs.entry(callee.addr).or_default();
            if seen.insert(call_addr) {
                entry.callsite_count = entry.callsite_count.saturating_add(1);
            }
        } else {
            entry.callsite_count = entry.callsite_count.saturating_add(1);
        }
    }
    facts
}

fn function_type_from_signature_json(
    signature: &ExternalSignatureJson,
    ptr_bits: u32,
) -> Option<FunctionType> {
    let return_type = signature
        .ret_type
        .as_deref()
        .and_then(|raw| parse_context_type_spec(raw, ptr_bits))
        .unwrap_or(CTypeLike::Unknown);
    let params = signature
        .params
        .iter()
        .map(|param| {
            param
                .ty
                .as_deref()
                .and_then(|raw| parse_context_type_spec(raw, ptr_bits))
                .unwrap_or(CTypeLike::Unknown)
        })
        .collect::<Vec<_>>();
    (return_type != CTypeLike::Unknown || !params.is_empty()).then_some(FunctionType {
        return_type,
        params,
        variadic: false,
    })
}

fn resolve_signature_aliases_from_type_db(
    signature: &mut FunctionSignatureSpec,
    type_db: &ExternalTypeDb,
) {
    if let Some(ret_ty) = signature.ret_type.as_mut() {
        resolve_type_alias_from_type_db(ret_ty, type_db);
    }
    for param in &mut signature.params {
        if let Some(ty) = param.ty.as_mut() {
            resolve_type_alias_from_type_db(ty, type_db);
        }
    }
}

fn resolve_register_param_aliases_from_type_db(
    register_params: &mut [ExternalRegisterParamSpec],
    type_db: &ExternalTypeDb,
) {
    for param in register_params {
        if let Some(ty) = param.ty.as_mut() {
            resolve_type_alias_from_type_db(ty, type_db);
        }
    }
}

fn resolve_stack_slot_aliases_from_type_db(
    stack_slots: &mut BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    type_db: &ExternalTypeDb,
) {
    for slot in stack_slots.values_mut() {
        if let Some(ty) = slot.ty.as_mut() {
            resolve_type_alias_from_type_db(ty, type_db);
        }
    }
}

fn resolve_type_alias_from_type_db(ty: &mut CTypeLike, type_db: &ExternalTypeDb) {
    match ty {
        CTypeLike::Pointer(inner) | CTypeLike::Array(inner, _) => {
            resolve_type_alias_from_type_db(inner, type_db);
        }
        CTypeLike::Typedef(name) => {
            if type_db.is_aggregate_typedef(name) {
                return;
            }
            let key = name.trim().to_ascii_lowercase();
            if let Some(st) = type_db.structs.get(&key) {
                *ty = CTypeLike::Struct(st.name.clone());
            } else if let Some(un) = type_db.unions.get(&key) {
                *ty = CTypeLike::Union(un.name.clone());
            } else if let Some(en) = type_db.enums.get(&key) {
                *ty = CTypeLike::Enum(en.name.clone());
            }
        }
        _ => {}
    }
}

fn imported_assumptions_from_context(
    explicit: &[r2ssa::AnalysisAssumption],
    register_params: &[ExternalRegisterParamSpec],
    stack_slots: &BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    type_db: &ExternalTypeDb,
    ptr_bits: u32,
) -> r2ssa::AssumptionSet {
    let mut assumptions = r2ssa::AssumptionSet::new(explicit.to_vec());
    let mut maybe_push_type_hints = |subject: r2ssa::AssumptionSubject, ty: &CTypeLike| {
        let ty_name = render_signature_type(ty, ptr_bits);
        assumptions.push(r2ssa::AnalysisAssumption {
            id: None,
            subject: subject.clone(),
            value: r2ssa::AssumptionValue::TypeHint { ty: ty_name },
            scope: r2ssa::AssumptionScope::Function,
            provenance: r2ssa::AssumptionProvenance::ImportedContext,
        });
        if let CTypeLike::Enum(name) = ty
            && let Some(external_enum) = type_db.enums.get(name)
        {
            assumptions.push(r2ssa::AnalysisAssumption {
                id: None,
                subject,
                value: r2ssa::AssumptionValue::EnumDomain {
                    name: Some(external_enum.name.clone()),
                    values: external_enum.variants.keys().copied().collect(),
                },
                scope: r2ssa::AssumptionScope::Function,
                provenance: r2ssa::AssumptionProvenance::ImportedContext,
            });
        }
    };
    for reg in register_params {
        if let Some(ty) = reg.ty.as_ref()
            && context_binding_type_is_meaningful(&reg.name, ty, ptr_bits)
        {
            maybe_push_type_hints(
                r2ssa::AssumptionSubject::Register {
                    name: reg.reg.clone(),
                },
                ty,
            );
        }
    }
    for (slot_key, slot) in stack_slots {
        if let Some(ty) = slot.ty.as_ref()
            && context_binding_type_is_meaningful(&slot.name, ty, ptr_bits)
        {
            if let Some(base) = slot_key.base.assumption_base() {
                maybe_push_type_hints(
                    r2ssa::AssumptionSubject::StackSlot {
                        base,
                        offset: slot_key.offset,
                    },
                    ty,
                );
            }
            if let Some(index) = slot.param_index {
                maybe_push_type_hints(r2ssa::AssumptionSubject::Parameter { index }, ty);
            }
        }
    }
    assumptions
}

fn context_binding_type_is_meaningful(name: &str, ty: &CTypeLike, ptr_bits: u32) -> bool {
    let low_quality_name = is_generic_arg_name(name) || is_low_quality_stack_name(name);
    if !low_quality_name {
        return true;
    }
    !matches!(
        ty,
        CTypeLike::Int { bits, .. } if *bits == ptr_bits
    ) && !matches!(
        ty,
        CTypeLike::Pointer(inner) if matches!(inner.as_ref(), CTypeLike::Unknown | CTypeLike::Void)
    )
}

fn parse_signature_json(
    signature: &ExternalSignatureJson,
    ptr_bits: u32,
) -> Option<FunctionSignatureSpec> {
    let mut used_names = HashSet::new();
    let mut params: Vec<_> = signature
        .params
        .iter()
        .enumerate()
        .map(|(idx, arg)| {
            let fallback = format!("arg{}", idx + 1);
            let raw_name = arg.name.clone().unwrap_or(fallback);
            let mut name =
                sanitize_c_identifier(&raw_name).unwrap_or_else(|| format!("arg{}", idx + 1));
            if !is_generic_arg_name(&name) {
                name = uniquify_name(name, &mut used_names);
            }
            FunctionParamSpec {
                name,
                ty: arg
                    .ty
                    .as_deref()
                    .and_then(|raw| parse_context_type_spec(raw, ptr_bits)),
            }
        })
        .collect();

    if params.len() == 1
        && params[0].ty == Some(CTypeLike::Void)
        && is_generic_arg_name(&params[0].name)
    {
        params.clear();
    }

    let ret_type = signature
        .ret_type
        .as_deref()
        .and_then(|raw| parse_context_type_spec(raw, ptr_bits));

    if params.is_empty() && ret_type.is_none() {
        return None;
    }

    Some(FunctionSignatureSpec { ret_type, params })
}

fn parse_context_type_spec(spec: &str, ptr_bits: u32) -> Option<CTypeLike> {
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
    let normalized = qualifier_filtered.join(" ");
    let normalized_key = normalized
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .to_ascii_lowercase();

    let mut base = match normalized_key.as_str() {
        "short" | "short int" => Some(CTypeLike::Typedef("short".to_string())),
        "unsigned short" | "unsigned short int" => {
            Some(CTypeLike::Typedef("unsigned short".to_string()))
        }
        "long" | "long int" => Some(CTypeLike::Typedef("long".to_string())),
        "unsigned long" | "unsigned long int" => {
            Some(CTypeLike::Typedef("unsigned long".to_string()))
        }
        "size_t" => Some(CTypeLike::Typedef("size_t".to_string())),
        "ssize_t" => Some(CTypeLike::Typedef("ssize_t".to_string())),
        "ptrdiff_t" => Some(CTypeLike::Typedef("ptrdiff_t".to_string())),
        "uintptr_t" => Some(CTypeLike::Typedef("uintptr_t".to_string())),
        "intptr_t" => Some(CTypeLike::Typedef("intptr_t".to_string())),
        _ => parse_type_like_spec(&normalized, ptr_bits),
    }?;

    if let Some(size) = array_size {
        base = CTypeLike::Array(Box::new(base), size);
    }
    for _ in 0..ptr_count {
        base = CTypeLike::Pointer(Box::new(base));
    }
    Some(base)
}

fn parse_external_vars(
    vars: &[ExternalVarJson],
    ptr_bits: u32,
    max_register_params: Option<usize>,
    signature: Option<&FunctionSignatureSpec>,
) -> (
    Vec<ExternalRegisterParamSpec>,
    BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
) {
    let mut register_params_by_index = BTreeMap::<usize, (i32, ExternalRegisterParamSpec)>::new();
    let mut inferred_register_index = 0usize;
    let mut stack_slots = BTreeMap::new();
    let mut used_names = HashSet::new();

    for (idx, var) in vars.iter().enumerate() {
        let sanitized_name =
            sanitize_c_identifier(&var.name).unwrap_or_else(|| format!("arg{}", idx + 1));
        let name = if is_generic_arg_name(&sanitized_name) {
            sanitized_name
        } else {
            uniquify_name(sanitized_name, &mut used_names)
        };
        let ty = var
            .ty
            .as_deref()
            .and_then(|raw| parse_context_type_spec(raw, ptr_bits));

        match var.kind {
            ExternalVarKind::Register => {
                let param_index = var.param_index.unwrap_or(inferred_register_index);
                let matches_expected_param_reg = expected_sysv64_param_reg(param_index)
                    .is_some_and(|expected| {
                        register_name_matches(var.reg.as_deref().unwrap_or_default(), expected)
                    });
                if max_register_params.is_some()
                    && !var.is_arg
                    && var.param_index.is_none()
                    && !matches_expected_param_reg
                {
                    continue;
                }
                inferred_register_index = inferred_register_index.max(param_index + 1);
                if max_register_params.is_some_and(|limit| param_index >= limit) {
                    continue;
                }
                let candidate = ExternalRegisterParamSpec {
                    name,
                    ty,
                    reg: var.reg.clone().unwrap_or_default(),
                };
                let score = register_param_candidate_score(
                    var,
                    &candidate,
                    signature,
                    param_index,
                    ptr_bits,
                );
                register_params_by_index
                    .entry(param_index)
                    .and_modify(|(existing_score, existing)| {
                        if score > *existing_score
                            || (score == *existing_score && candidate.reg < existing.reg)
                        {
                            *existing_score = score;
                            *existing = candidate.clone();
                        }
                    })
                    .or_insert((score, candidate));
            }
            ExternalVarKind::Stack => {
                let Some(offset) = var.offset else {
                    continue;
                };
                let base = parse_external_stack_base(var.base.as_deref());
                let role = var.role.unwrap_or({
                    if var.is_arg {
                        ExternalStackSlotRole::StackArg
                    } else {
                        ExternalStackSlotRole::Unknown
                    }
                });
                let param_index = var.param_index.or_else(|| {
                    matches!(role, ExternalStackSlotRole::StackArg)
                        .then(|| sysv64_stack_arg_index(&base, offset, ptr_bits))
                        .flatten()
                });
                let param_name = var.param_name.clone().or_else(|| {
                    if !matches!(role, ExternalStackSlotRole::StackArg) {
                        return None;
                    }
                    let param_index = param_index?;
                    signature
                        .and_then(|signature| signature.params.get(param_index))
                        .filter(|param| !is_generic_arg_name(&param.name))
                        .map(|param| param.name.clone())
                        .or_else(|| {
                            is_low_quality_stack_name(&name)
                                .then(|| format!("arg{}", param_index + 1))
                        })
                });
                let candidate = ExternalStackSlotSpec {
                    name,
                    ty,
                    base: base.clone(),
                    role,
                    param_index,
                    param_name,
                    source_reg: var.source_reg.clone(),
                };
                let key = StackSlotKey { base, offset };
                merge_stack_slot_candidate(&mut stack_slots, key, candidate.clone());
            }
        }
    }

    let register_params = register_params_by_index
        .into_iter()
        .map(|(param_index, (_, mut param))| {
            apply_signature_param_to_register_param(signature, param_index, &mut param);
            param
        })
        .collect();
    (register_params, stack_slots)
}

fn apply_signature_param_to_register_param(
    signature: Option<&FunctionSignatureSpec>,
    param_index: usize,
    reg_param: &mut ExternalRegisterParamSpec,
) {
    let Some(param) = signature
        .filter(|signature| signature_param_count_is_authoritative(signature))
        .and_then(|signature| signature.params.get(param_index))
    else {
        return;
    };
    if !is_generic_arg_name(&param.name) {
        reg_param.name = param.name.clone();
    }
    if !is_generic_signature_type(param.ty.as_ref()) {
        reg_param.ty = param.ty.clone();
    }
}

fn register_param_candidate_score(
    var: &ExternalVarJson,
    candidate: &ExternalRegisterParamSpec,
    signature: Option<&FunctionSignatureSpec>,
    param_index: usize,
    ptr_bits: u32,
) -> i32 {
    let mut score = 0;
    if var.is_arg {
        score += 20;
    }
    if var.param_index.is_some() {
        score += 20;
    }
    if !is_generic_arg_name(&candidate.name) {
        score += 5;
    }
    if !is_generic_signature_type(candidate.ty.as_ref()) {
        score += 5;
    }
    if let Some(expected) = expected_sysv64_param_reg(param_index)
        && register_name_matches(&candidate.reg, expected)
    {
        score += 30;
    }
    if let Some(param) = signature.and_then(|signature| signature.params.get(param_index)) {
        if !is_generic_arg_name(&param.name) && candidate.name.eq_ignore_ascii_case(&param.name) {
            score += 20;
        }
        if let (Some(left), Some(right)) = (candidate.ty.as_ref(), param.ty.as_ref())
            && crate::signature_infer::signature_types_are_equivalent(left, right, ptr_bits)
        {
            score += 10;
        }
    }
    score
}

fn expected_sysv64_param_reg(index: usize) -> Option<&'static str> {
    ["rdi", "rsi", "rdx", "rcx", "r8", "r9"].get(index).copied()
}

fn register_name_matches(actual: &str, expected: &str) -> bool {
    let actual = actual.trim().to_ascii_lowercase();
    if actual == expected {
        return true;
    }
    matches!(
        (actual.as_str(), expected),
        ("edi" | "di" | "dil", "rdi")
            | ("esi" | "si" | "sil", "rsi")
            | ("edx" | "dx" | "dl", "rdx")
            | ("ecx" | "cx" | "cl", "rcx")
            | ("r8d" | "r8w" | "r8b", "r8")
            | ("r9d" | "r9w" | "r9b", "r9")
    )
}

fn sysv64_stack_arg_index(base: &ExternalStackBase, offset: i64, ptr_bits: u32) -> Option<usize> {
    if !matches!(base, ExternalStackBase::StackPointer) || ptr_bits != 64 {
        return None;
    }
    let ptr_bytes = i64::from(ptr_bits / 8);
    if offset < ptr_bytes || (offset - ptr_bytes) % ptr_bytes != 0 {
        return None;
    }
    Some(6 + ((offset - ptr_bytes) / ptr_bytes) as usize)
}

fn parse_external_stack_base(raw: Option<&str>) -> ExternalStackBase {
    let lower = raw.unwrap_or_default().trim().to_ascii_lowercase();
    match lower.as_str() {
        "" => ExternalStackBase::default(),
        "bp" | "ebp" | "rbp" | "fp" => ExternalStackBase::FramePointer,
        "sp" | "esp" | "rsp" => ExternalStackBase::StackPointer,
        _ => ExternalStackBase::Named(raw.unwrap_or_default().to_string()),
    }
}

fn stack_slot_role_rank(role: ExternalStackSlotRole) -> u8 {
    match role {
        ExternalStackSlotRole::ParamHome => 5,
        ExternalStackSlotRole::StackArg => 4,
        ExternalStackSlotRole::Local => 3,
        ExternalStackSlotRole::SavedReg | ExternalStackSlotRole::SavedFp => 2,
        ExternalStackSlotRole::Unknown => 1,
    }
}

fn base_rank(base: &ExternalStackBase) -> u8 {
    match base {
        ExternalStackBase::FramePointer => 3,
        ExternalStackBase::StackPointer => 2,
        ExternalStackBase::Named(_) => 1,
    }
}

fn is_low_quality_stack_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower.starts_with("var_")
        || lower.starts_with("local_")
        || lower.starts_with("stack_")
        || lower.starts_with("arg_")
        || lower == "saved_fp"
        || is_generic_arg_name(&lower)
}

fn prefer_stack_slot_candidate(
    existing: &ExternalStackSlotSpec,
    candidate: &ExternalStackSlotSpec,
) -> bool {
    let existing_rank = stack_slot_role_rank(existing.role);
    let candidate_rank = stack_slot_role_rank(candidate.role);
    if candidate_rank != existing_rank {
        return candidate_rank > existing_rank;
    }
    let existing_name_quality = !is_low_quality_stack_name(&existing.name);
    let candidate_name_quality = !is_low_quality_stack_name(&candidate.name);
    if existing_name_quality != candidate_name_quality {
        return candidate_name_quality;
    }
    base_rank(&candidate.base) > base_rank(&existing.base)
}

fn merge_stack_slot_candidate(
    slots: &mut BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    key: StackSlotKey,
    candidate: ExternalStackSlotSpec,
) {
    match slots.get(&key) {
        None => {
            slots.insert(key, candidate);
        }
        Some(existing) if prefer_stack_slot_candidate(existing, &candidate) => {
            slots.insert(key, candidate);
        }
        _ => {}
    }
}

fn merge_legacy_stack_slot(
    slots: &mut HashMap<i64, ExternalStackVarSpec>,
    offset: i64,
    candidate: ExternalStackVarSpec,
) {
    match slots.get(&offset) {
        None => {
            slots.insert(offset, candidate);
        }
        Some(existing) if prefer_stack_slot_candidate(existing, &candidate) => {
            slots.insert(offset, candidate);
        }
        _ => {}
    }
}

pub(crate) fn legacy_external_stack_vars_from_slots(
    stack_slots: &BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
) -> HashMap<i64, ExternalStackVarSpec> {
    let mut legacy = HashMap::new();
    for (slot_key, slot_spec) in stack_slots {
        merge_legacy_stack_slot(&mut legacy, slot_key.offset, slot_spec.clone());
    }
    legacy
}

pub(crate) fn stack_slots_from_legacy_external_stack_vars(
    legacy_stack_vars: &HashMap<i64, ExternalStackVarSpec>,
) -> BTreeMap<StackSlotKey, ExternalStackSlotSpec> {
    let mut stack_slots = BTreeMap::new();
    for (offset, slot_spec) in legacy_stack_vars {
        merge_stack_slot_candidate(
            &mut stack_slots,
            StackSlotKey {
                base: slot_spec.base.clone(),
                offset: *offset,
            },
            slot_spec.clone(),
        );
    }
    stack_slots
}

fn parse_known_signatures(
    entries: &[KnownSignatureJson],
    ptr_bits: u32,
) -> HashMap<String, FunctionType> {
    let mut out = HashMap::new();

    for entry in entries {
        if entry.name.trim().is_empty() {
            continue;
        }

        let params = entry
            .args
            .iter()
            .map(|arg| {
                arg.ty
                    .as_deref()
                    .and_then(|raw| parse_context_type_spec(raw, ptr_bits))
                    .unwrap_or(CTypeLike::Unknown)
            })
            .collect::<Vec<_>>();
        let return_type = entry
            .ret_type
            .as_deref()
            .and_then(|raw| parse_context_type_spec(raw, ptr_bits))
            .unwrap_or(CTypeLike::Unknown);
        let sig = FunctionType {
            return_type,
            params,
            variadic: entry.variadic,
        };
        maybe_insert_known_signature(&mut out, &entry.name, sig);
    }

    out
}

fn maybe_insert_known_signature(
    known: &mut HashMap<String, FunctionType>,
    name: &str,
    sig: FunctionType,
) {
    for candidate in function_signature_lookup_names(name) {
        known.insert(candidate, sig.clone());
    }
}

fn signature_spec_from_known_name(
    name: &str,
    known: &HashMap<String, FunctionType>,
) -> Option<FunctionSignatureSpec> {
    let sig = function_signature_lookup_names(name)
        .into_iter()
        .find_map(|candidate| known.get(&candidate))?;
    Some(FunctionSignatureSpec {
        ret_type: Some(sig.return_type.clone()),
        params: sig
            .params
            .iter()
            .enumerate()
            .map(|(idx, ty)| FunctionParamSpec {
                name: format!("arg{}", idx + 1),
                ty: Some(ty.clone()),
            })
            .collect(),
    })
}

fn external_member_type(member: &ExternalBaseTypeMemberJson, ptr_bits: u32) -> String {
    let normalized = normalize_external_type_name(&member.ty);
    let Some(size_bits) = member.size_bits else {
        return normalized;
    };
    let Some(parsed) = parse_type_like_spec(&normalized, ptr_bits) else {
        return normalized;
    };
    if matches!(parsed, CTypeLike::Array(_, _)) {
        return normalized;
    }
    let Some(elem_bits) = type_like_size_bits(&parsed, ptr_bits) else {
        return normalized;
    };
    if elem_bits == 0 || size_bits <= elem_bits || size_bits % elem_bits != 0 {
        return normalized;
    }
    let count = size_bits / elem_bits;
    if count <= 1 {
        return normalized;
    }
    format!("{normalized}[{count}]")
}

fn type_like_size_bits(ty: &CTypeLike, ptr_bits: u32) -> Option<u64> {
    match ty {
        CTypeLike::Void | CTypeLike::Function | CTypeLike::Unknown => None,
        CTypeLike::Bool => Some(1),
        CTypeLike::Int { bits, .. } | CTypeLike::Float(bits) => Some(u64::from(*bits)),
        CTypeLike::Pointer(_) => Some(u64::from(ptr_bits)),
        CTypeLike::Array(inner, Some(len)) => type_like_size_bits(inner, ptr_bits)
            .and_then(|elem_bits| elem_bits.checked_mul(*len as u64)),
        CTypeLike::Array(_, None) => None,
        CTypeLike::Struct(_) | CTypeLike::Union(_) | CTypeLike::Enum(_) | CTypeLike::Typedef(_) => {
            None
        }
    }
}

fn external_type_db_from_base_types(
    base_types: &[ExternalBaseTypeJson],
    ptr_bits: u32,
) -> ExternalTypeDb {
    let mut out = ExternalTypeDb::default();

    for base_type in base_types {
        match base_type.kind {
            ExternalBaseTypeKind::Struct => {
                let name = normalize_aggregate_name(&base_type.name, "struct");
                if name.is_empty() {
                    continue;
                }
                let mut fields = BTreeMap::new();
                for member in &base_type.members {
                    fields.insert(
                        member.offset,
                        ExternalField {
                            name: member.name.clone(),
                            offset: member.offset,
                            ty: Some(external_member_type(member, ptr_bits)),
                        },
                    );
                }
                out.structs
                    .insert(name.to_ascii_lowercase(), ExternalStruct { name, fields });
            }
            ExternalBaseTypeKind::Union => {
                let name = normalize_aggregate_name(&base_type.name, "union");
                if name.is_empty() {
                    continue;
                }
                let mut fields = BTreeMap::new();
                for member in &base_type.members {
                    fields.insert(
                        member.offset,
                        ExternalField {
                            name: member.name.clone(),
                            offset: member.offset,
                            ty: Some(external_member_type(member, ptr_bits)),
                        },
                    );
                }
                out.unions
                    .insert(name.to_ascii_lowercase(), ExternalUnion { name, fields });
            }
            ExternalBaseTypeKind::Enum => {
                let name = normalize_aggregate_name(&base_type.name, "enum");
                if name.is_empty() {
                    continue;
                }
                let mut variants = BTreeMap::new();
                for variant in &base_type.variants {
                    variants.insert(variant.value, variant.name.clone());
                }
                out.enums
                    .insert(name.to_ascii_lowercase(), ExternalEnum { name, variants });
            }
            ExternalBaseTypeKind::Typedef | ExternalBaseTypeKind::Atomic => {}
        }
    }

    for base_type in base_types {
        if !matches!(base_type.kind, ExternalBaseTypeKind::Typedef) {
            continue;
        }
        let Some(target) = base_type.ty.as_deref() else {
            continue;
        };
        out.insert_typedef(base_type.name.clone(), target.to_string());
    }
    out.materialize_typedef_aggregate_aliases();

    out
}

fn normalize_aggregate_name(name: &str, prefix: &str) -> String {
    let normalized = normalize_external_type_name(name);
    normalized
        .strip_prefix(&format!("{prefix} "))
        .unwrap_or(name)
        .trim()
        .to_string()
}

fn sanitize_c_identifier(name: &str) -> Option<String> {
    let trimmed = name.trim();
    if trimmed.is_empty() {
        return None;
    }

    let mut out = String::new();
    for (idx, ch) in trimmed.chars().enumerate() {
        let normalized = if ch.is_ascii_alphanumeric() || ch == '_' {
            ch
        } else {
            '_'
        };
        if idx == 0 && normalized.is_ascii_digit() {
            out.push('_');
        }
        out.push(normalized);
    }

    if out.chars().all(|c| c == '_') {
        None
    } else {
        Some(out)
    }
}

fn uniquify_name(base: String, used: &mut HashSet<String>) -> String {
    if used.insert(base.clone()) {
        return base;
    }
    let mut idx = 2usize;
    loop {
        let candidate = format!("{base}_{idx}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
        idx += 1;
    }
}

pub fn is_generic_arg_name(name: &str) -> bool {
    let lower = name.trim().to_ascii_lowercase();
    lower
        .strip_prefix("arg")
        .map(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
        .unwrap_or(false)
}

fn is_generic_signature_type(ty: Option<&CTypeLike>) -> bool {
    match ty {
        None => true,
        Some(CTypeLike::Unknown | CTypeLike::Void) => true,
        Some(CTypeLike::Pointer(inner)) => {
            matches!(inner.as_ref(), CTypeLike::Unknown | CTypeLike::Void)
        }
        _ => false,
    }
}

fn signature_param_count_is_authoritative(signature: &FunctionSignatureSpec) -> bool {
    crate::facts::signature_param_count_is_authoritative(signature)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_external_context_merges_register_params() {
        let ctx = parse_external_context_json(
            r#"{
                "signature":{"ret":"int32_t","params":[{"name":"arg1","type":"void *"}]},
                "vars":[
                    {"kind":"register","name":"count","type":"int32_t","reg":"rdi"},
                    {"kind":"stack","name":"local_10h","type":"int32_t","base":"rbp","offset":-16}
                ]
            }"#,
            64,
        );

        let merged = ctx.merged_signature.expect("merged signature");
        assert_eq!(merged.params[0].name, "count");
        assert_eq!(
            merged.params[0].ty,
            Some(CTypeLike::Int {
                bits: 32,
                signedness: crate::Signedness::Signed,
            })
        );
        assert_eq!(
            ctx.stack_slots
                .get(&StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -16,
                })
                .map(|var| var.name.as_str()),
            Some("local_10h")
        );
    }

    #[test]
    fn parse_external_context_caps_register_params_with_authoritative_signature() {
        let ctx = parse_external_context_json(
            r#"{
                "signature":{
                    "ret":"FILE *",
                    "params":[
                        {"name":"filename","type":"char const *"},
                        {"name":"mode","type":"char const *"}
                    ]
                },
                "vars":[
                    {"kind":"register","name":"filename","type":"char const *","reg":"rdi","param_index":0},
                    {"kind":"register","name":"mode","type":"char const *","reg":"rsi","param_index":1},
                    {"kind":"register","name":"arg3","type":"uint32_t","reg":"rcx","param_index":2}
                ]
            }"#,
            64,
        );

        let merged = ctx.merged_signature.expect("merged signature");
        assert_eq!(
            merged.ret_type,
            Some(CTypeLike::Pointer(Box::new(CTypeLike::Typedef(
                "FILE".to_string()
            ))))
        );
        assert_eq!(merged.params.len(), 2);
        assert_eq!(ctx.register_params.len(), 2);
        assert_eq!(ctx.register_params[0].reg, "rdi");
        assert_eq!(ctx.register_params[1].reg, "rsi");
    }

    #[test]
    fn parse_external_context_indexes_polluted_register_params_by_authoritative_signature_order() {
        let ctx = parse_external_context_json(
            r#"{
                "signature":{
                    "ret":"int32_t",
                    "params":[
                        {"name":"arr","type":"DemoStruct *"},
                        {"name":"idx","type":"int32_t"},
                        {"name":"v","type":"int32_t"}
                    ]
                },
                "vars":[
                    {"kind":"register","name":"v","type":"int32_t","reg":"AL"},
                    {"kind":"register","name":"arg0","type":"void *","reg":"RDI","is_arg":true,"param_index":0},
                    {"kind":"register","name":"arg1","type":"int64_t","reg":"RSI","is_arg":true,"param_index":1},
                    {"kind":"register","name":"arg2","type":"void *","reg":"RDX","is_arg":true,"param_index":2},
                    {"kind":"register","name":"arr","type":"DemoStruct *","reg":"rdi","is_arg":true,"param_index":0}
                ]
            }"#,
            64,
        );

        assert_eq!(ctx.register_params.len(), 3);
        assert_eq!(ctx.register_params[0].name, "arr");
        assert_eq!(ctx.register_params[0].reg, "rdi");
        assert_eq!(ctx.register_params[1].reg, "RSI");
        assert_eq!(ctx.register_params[2].reg, "RDX");
        let merged = ctx.merged_signature.expect("merged signature");
        assert_eq!(merged.params[1].name, "idx");
        assert_eq!(merged.params[2].name, "v");
    }

    #[test]
    fn parse_external_context_preserves_source_typedefs_over_narrow_register_vars() {
        let ctx = parse_external_context_json(
            r#"{
                "signature":{
                    "ret":"size_t",
                    "params":[
                        {"name":"buf","type":"unsigned char const *"},
                        {"name":"n","type":"size_t"},
                        {"name":"a","type":"unsigned char"},
                        {"name":"b","type":"unsigned char"}
                    ]
                },
                "vars":[
                    {"kind":"register","name":"arg0","type":"uint8_t *","reg":"rdi","is_arg":true,"param_index":0},
                    {"kind":"register","name":"arg1","type":"uint8_t","reg":"rsi","is_arg":true,"param_index":1},
                    {"kind":"register","name":"arg2","type":"uint8_t","reg":"rdx","is_arg":true,"param_index":2},
                    {"kind":"register","name":"arg3","type":"uint8_t","reg":"rcx","is_arg":true,"param_index":3}
                ]
            }"#,
            64,
        );

        let signature = ctx.current_signature.as_ref().expect("current signature");
        assert_eq!(
            signature
                .ret_type
                .as_ref()
                .map(|ty| render_signature_type(ty, 64))
                .as_deref(),
            Some("size_t")
        );
        assert_eq!(signature.params[1].name, "n");
        assert_eq!(
            signature.params[1]
                .ty
                .as_ref()
                .map(|ty| render_signature_type(ty, 64))
                .as_deref(),
            Some("size_t")
        );
        assert_eq!(ctx.register_params[1].name, "n");
        assert_eq!(
            ctx.register_params[1]
                .ty
                .as_ref()
                .map(|ty| render_signature_type(ty, 64))
                .as_deref(),
            Some("size_t")
        );
    }

    #[test]
    fn parse_external_context_resolves_known_aggregate_typedef_aliases() {
        let ctx = parse_external_context_json(
            r#"{
                "signature":{
                    "ret":"int32_t",
                    "params":[{"name":"obj","type":"DemoStruct *"}]
                },
                "base_types":[
                    {
                        "kind":"struct",
                        "name":"DemoStruct",
                        "members":[{"name":"value","type":"int32_t","offset":0}]
                    }
                ]
            }"#,
            64,
        );

        let merged = ctx.merged_signature.expect("merged signature");
        assert_eq!(
            merged.params.first().and_then(|param| param.ty.as_ref()),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Struct(
                "DemoStruct".to_string()
            ))))
        );
    }

    #[test]
    fn parse_external_context_preserves_debug_typedef_alias_to_placeholder_struct() {
        let ctx = parse_external_context_json(
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

        let merged = ctx.merged_signature.expect("merged signature");
        assert_eq!(
            merged.params.first().and_then(|param| param.ty.as_ref()),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Typedef(
                "DemoStruct".to_string()
            ))))
        );
        let alias = ctx
            .external_type_db
            .structs
            .get("demostruct")
            .expect("typedef-backed aggregate alias");
        assert_eq!(
            alias.fields.get(&8).map(|field| field.name.as_str()),
            Some("third")
        );
        assert_eq!(
            alias.fields.get(&52).map(|field| field.name.as_str()),
            Some("fourteenth")
        );
    }

    #[test]
    fn parse_external_context_recovers_import_signature_from_known_alias() {
        let ctx = parse_external_context_json(
            r#"{
                "signature":{"name":"sym.imp.__stack_chk_fail","noreturn":true},
                "known_signatures":[{"name":"stack_chk_fail","ret":"void","args":[]}]
            }"#,
            64,
        );

        let signature = ctx
            .current_signature
            .as_ref()
            .expect("known signature should seed missing typed signature");
        assert_eq!(signature.ret_type, Some(CTypeLike::Void));
        assert!(signature.params.is_empty());
        assert!(ctx.noreturn);

        let merged = ctx.merged_signature.expect("merged signature");
        assert_eq!(merged.ret_type, Some(CTypeLike::Void));
        assert!(merged.params.is_empty());
    }

    #[test]
    fn function_type_facts_preserve_current_callconv_and_noreturn() {
        let ctx = parse_external_context_json(
            r#"{
                "signature":{
                    "name":"sym.imp.__stack_chk_fail",
                    "ret":"void",
                    "callconv":"amd64",
                    "noreturn":true,
                    "params":[]
                }
            }"#,
            64,
        );

        let facts = function_type_facts_from_parsed_context("sym.imp.__stack_chk_fail", &ctx);
        assert_eq!(facts.callconv.as_deref(), Some("amd64"));
        assert!(facts.noreturn);
        assert_eq!(
            facts
                .render_authorized_signature()
                .and_then(|signature| signature.ret_type.as_ref()),
            Some(&CTypeLike::Void)
        );
    }

    #[test]
    fn parse_external_context_requires_typed_callee_linkage_for_import_policy() {
        let ctx = parse_external_context_json(
            r#"{
                "callees":[
                    {"addr":4198752,"name":"sym.imp.setlocale"},
                    {"addr":4198760,"name":"setlocale","linkage":"imported"}
                ]
            }"#,
            64,
        );

        let raw_name_only = ctx
            .callee_facts
            .get(&4198752)
            .expect("name-only callee fact");
        assert_eq!(raw_name_only.name.as_deref(), Some("sym.imp.setlocale"));
        assert_eq!(raw_name_only.linkage, CalleeLinkage::Unknown);
        assert!(!raw_name_only.linkage.authorizes_import_policy());
        assert!(!raw_name_only.authorizes_model_policy());

        let imported = ctx
            .callee_facts
            .get(&4198760)
            .expect("typed imported callee fact");
        assert_eq!(imported.name.as_deref(), Some("setlocale"));
        assert_eq!(imported.linkage, CalleeLinkage::Imported);
        assert!(imported.linkage.authorizes_import_policy());
        assert!(
            !imported.authorizes_model_policy(),
            "external callee presence/linkage is not modeled-summary evidence"
        );

        let facts = function_type_facts_from_parsed_context("dbg.wrapper", &ctx);
        assert_eq!(
            facts.callee_facts.get(&4198760).map(|fact| fact.linkage),
            Some(CalleeLinkage::Imported)
        );
    }

    #[test]
    fn parse_external_context_counts_distinct_typed_callee_callsites() {
        let ctx = parse_external_context_json(
            r#"{
                "callees":[
                    {"call_addr":4096,"addr":4198760,"name":"setlocale","linkage":"imported"},
                    {"call_addr":4100,"addr":4198760,"name":"setlocale","linkage":"imported"},
                    {"call_addr":4100,"addr":4198760,"name":"setlocale","linkage":"imported"}
                ]
            }"#,
            64,
        );

        let imported = ctx
            .callee_facts
            .get(&4198760)
            .expect("typed imported callee fact");
        assert_eq!(imported.callsite_count, 2);
        assert_eq!(imported.linkage, CalleeLinkage::Imported);
    }

    #[test]
    fn parse_external_context_preserves_typed_callee_signature_facts() {
        let ctx = parse_external_context_json(
            r#"{
                "callees":[{
                    "call_addr":4096,
                    "addr":4198760,
                    "name":"setlocale",
                    "linkage":"imported",
                    "signature":{
                        "name":"setlocale",
                        "ret":"char *",
                        "callconv":"amd64",
                        "noreturn":true,
                        "params":[
                            {"name":"category","type":"int"},
                            {"name":"locale","type":"char *"}
                        ]
                    }
                }]
            }"#,
            64,
        );

        let imported = ctx
            .callee_facts
            .get(&4198760)
            .expect("typed imported callee fact");
        assert_eq!(imported.signature_callconv.as_deref(), Some("amd64"));
        assert!(imported.signature_noreturn);
        let signature = imported.signature.as_ref().expect("callee signature");
        assert_eq!(
            signature.return_type,
            CTypeLike::Pointer(Box::new(CTypeLike::Int {
                bits: 8,
                signedness: crate::Signedness::Signed,
            }))
        );
        assert_eq!(signature.params.len(), 2);
        assert_eq!(
            signature.params[0],
            CTypeLike::Int {
                bits: 32,
                signedness: crate::Signedness::Signed,
            }
        );
        assert_eq!(
            signature.params[1],
            CTypeLike::Pointer(Box::new(CTypeLike::Int {
                bits: 8,
                signedness: crate::Signedness::Signed,
            }))
        );
    }

    #[test]
    fn known_signature_aliases_include_import_and_compiler_helper_names() {
        let ctx = parse_external_context_json(
            r#"{
                "known_signatures":[
                    {"name":"sym.imp.__stack_chk_fail","ret":"void","args":[]}
                ]
            }"#,
            64,
        );

        assert!(
            ctx.known_function_signatures
                .contains_key("sym.imp.__stack_chk_fail")
        );
        assert!(
            ctx.known_function_signatures
                .contains_key("__stack_chk_fail")
        );
        assert!(ctx.known_function_signatures.contains_key("stack_chk_fail"));
    }

    #[test]
    fn apply_main_signature_override_refuses_name_only_main() {
        let mut merged = None;
        assert!(!apply_main_signature_override("dbg.main", &mut merged));
        assert!(merged.is_none());
    }

    #[test]
    fn apply_main_signature_override_canonicalizes_main_shaped_signature() {
        let mut merged = Some(FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Typedef("int".into())),
            params: vec![
                FunctionParamSpec {
                    name: "argc".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                        bits: 8,
                        signedness: crate::Signedness::Signed,
                    }))),
                },
                FunctionParamSpec {
                    name: "argv".to_string(),
                    ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Pointer(Box::new(
                        CTypeLike::Int {
                            bits: 8,
                            signedness: crate::Signedness::Signed,
                        },
                    ))))),
                },
            ],
        });
        assert!(apply_main_signature_override("dbg.main", &mut merged));
        let merged = merged.expect("main signature");
        assert_eq!(merged.params.len(), 3);
        assert_eq!(merged.params[0].name, "argc");
        assert_eq!(merged.params[0].ty, Some(CTypeLike::Typedef("int".into())));
        assert_eq!(merged.params[1].name, "argv");
        assert_eq!(merged.params[2].name, "envp");
    }

    #[test]
    fn function_type_facts_from_context_canonicalizes_main_signature() {
        let parsed = parse_external_context_json(
            r#"{
                "signature":{
                    "ret":"int",
                    "params":[
                        {"name":"argc","type":"char *"},
                        {"name":"argv","type":"char **"},
                        {"name":"envp","type":"char **"}
                    ]
                }
            }"#,
            64,
        );

        let facts = function_type_facts_from_parsed_context("dbg.main", &parsed);
        let certificate = facts
            .signature_certificate
            .as_ref()
            .expect("external main signature should carry a certificate");
        assert_eq!(
            certificate.sources,
            vec![SignatureCertificateSource::ExternalContext]
        );
        assert!(certificate.authorizes_signature_writeback());
        let signature = facts.merged_signature.expect("main signature");
        assert_eq!(signature.ret_type, Some(CTypeLike::Typedef("int".into())));
        assert_eq!(signature.params[0].name, "argc");
        assert_eq!(
            signature.params[0].ty,
            Some(CTypeLike::Typedef("int".into()))
        );
        assert_eq!(
            render_signature_type(signature.params[1].ty.as_ref().unwrap(), 64),
            "int8_t**"
        );

        let helper = function_type_facts_from_parsed_context("dbg.helper", &parsed)
            .merged_signature
            .expect("helper signature");
        assert_eq!(
            render_signature_type(helper.params[0].ty.as_ref().unwrap(), 64),
            "int8_t*"
        );
    }

    #[test]
    fn parse_external_assumption_payload_reads_external_context_payload() {
        let assumptions = parse_external_assumption_payload_json(
            r#"{"assumptions":[{"subject":{"register":{"name":"rdi"}},"value":{"constant":{"value":4660}}}]}"#,
            64,
        )
        .expect("assumptions");

        assert_eq!(assumptions.items.len(), 1);
        assert_eq!(
            assumptions.items[0].subject,
            r2ssa::AssumptionSubject::Register {
                name: "rdi".to_string()
            }
        );
    }

    #[test]
    fn parse_external_assumption_payload_reads_direct_assumption_array() {
        let assumptions = parse_external_assumption_payload_json(
            r#"[{"subject":{"register":{"name":"rdi"}},"value":{"constant":{"value":4660}}}]"#,
            64,
        )
        .expect("assumptions");

        assert_eq!(assumptions.items.len(), 1);
        assert_eq!(
            assumptions.items[0].value,
            r2ssa::AssumptionValue::Constant { value: 4660 }
        );
        assert_eq!(
            assumptions.items[0].provenance,
            r2ssa::AssumptionProvenance::User
        );
    }

    #[test]
    fn parse_external_assumption_payload_preserves_explicit_direct_provenance() {
        let assumptions = parse_external_assumption_payload_json(
            r#"[{"subject":{"register":{"name":"rdi"}},"value":{"constant":{"value":4660}},"provenance":"replay"}]"#,
            64,
        )
        .expect("assumptions");

        assert_eq!(assumptions.items.len(), 1);
        assert_eq!(
            assumptions.items[0].provenance,
            r2ssa::AssumptionProvenance::Replay
        );
    }

    #[test]
    fn parse_external_assumption_payload_rejects_invalid_direct_array() {
        let err =
            parse_external_assumption_payload_json(r#"[{"subject":"not an assumption"}]"#, 64)
                .expect_err("invalid direct assumption arrays should fail");

        assert_eq!(
            err,
            ExternalAssumptionPayloadParseError::InvalidAssumptionArray
        );
        assert_eq!(err.message(), "assumptions json is invalid");
        assert_eq!(err.to_string(), "assumptions json is invalid");
    }

    #[test]
    fn function_type_facts_preserve_current_signature_when_no_merged_signature() {
        let parsed = ParsedExternalContext {
            current_signature: Some(FunctionSignatureSpec {
                ret_type: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                    bits: 8,
                    signedness: crate::Signedness::Signed,
                }))),
                params: vec![
                    FunctionParamSpec {
                        name: "name".to_string(),
                        ty: Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                            bits: 8,
                            signedness: crate::Signedness::Signed,
                        }))),
                    },
                    FunctionParamSpec {
                        name: "can_mode".to_string(),
                        ty: Some(CTypeLike::Typedef("canonicalize_mode_t".to_string())),
                    },
                ],
            }),
            merged_signature: None,
            ..ParsedExternalContext::default()
        };

        let facts =
            function_type_facts_from_parsed_context("dbg.canonicalize_filename_mode", &parsed);
        let certificate = facts
            .signature_certificate
            .as_ref()
            .expect("current external signature should seed a certificate");
        assert_eq!(
            certificate.sources,
            vec![SignatureCertificateSource::ExternalContext]
        );
        let signature = facts
            .merged_signature
            .expect("current signature should seed function facts");

        assert_eq!(
            signature
                .ret_type
                .as_ref()
                .map(|ty| render_signature_type(ty, 64))
                .as_deref(),
            Some("int8_t*")
        );
        assert_eq!(signature.params.len(), 2);
        assert_eq!(signature.params[0].name, "name");
        assert_eq!(signature.params[1].name, "can_mode");
    }

    #[test]
    fn parse_external_context_preserves_stack_slot_identity_and_role_metadata() {
        let ctx = parse_external_context_json(
            r#"{
                "vars":[
                    {
                        "kind":"stack",
                        "name":"spill_arr",
                        "type":"void *",
                        "base":"rbp",
                        "offset":16,
                        "role":"param_home",
                        "param_index":0,
                        "param_name":"arr",
                        "source_reg":"rdi"
                    },
                    {
                        "kind":"stack",
                        "name":"sp_local",
                        "type":"int32_t",
                        "base":"rsp",
                        "offset":16,
                        "role":"local"
                    }
                ]
            }"#,
            64,
        );

        let home = ctx
            .stack_slots
            .get(&StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: 16,
            })
            .expect("frame-based param home slot");
        assert_eq!(home.role, ExternalStackSlotRole::ParamHome);
        assert_eq!(home.param_index, Some(0));
        assert_eq!(home.param_name.as_deref(), Some("arr"));
        assert_eq!(home.source_reg.as_deref(), Some("rdi"));

        let sp_local = ctx
            .stack_slots
            .get(&StackSlotKey {
                base: ExternalStackBase::StackPointer,
                offset: 16,
            })
            .expect("stack-pointer local slot");
        assert_eq!(sp_local.role, ExternalStackSlotRole::Local);
        assert_eq!(sp_local.name, "sp_local");

        assert!(ctx.external_stack_vars.is_empty());
        assert!(ctx.assumptions.items.iter().any(|assumption| {
            matches!(
                &assumption.subject,
                r2ssa::AssumptionSubject::StackSlot {
                    base: r2ssa::StackAddressBase::FramePointer,
                    offset: 16,
                }
            )
        }));
        assert!(ctx.assumptions.items.iter().any(|assumption| {
            matches!(
                &assumption.subject,
                r2ssa::AssumptionSubject::StackSlot {
                    base: r2ssa::StackAddressBase::StackPointer,
                    offset: 16,
                }
            )
        }));
    }

    #[test]
    fn named_external_stack_base_does_not_become_a_semantic_assumption() {
        let ctx = parse_external_context_json(
            r#"{
                "vars":[{
                    "kind":"stack",
                    "name":"local_value",
                    "type":"int32_t",
                    "base":"custom_stack_base",
                    "offset":-8,
                    "role":"local"
                }]
            }"#,
            64,
        );

        assert!(ctx.stack_slots.keys().any(|slot| {
            slot.base == ExternalStackBase::Named("custom_stack_base".to_string())
                && slot.offset == -8
        }));
        assert!(ctx.assumptions.is_empty());
    }

    #[test]
    fn parse_external_context_derives_sysv_stack_arg_index() {
        let ctx = parse_external_context_json(
            r#"{
                "vars":[
                    {
                        "kind":"stack",
                        "name":"arg_8h",
                        "type":"int64_t",
                        "base":"rsp",
                        "offset":8,
                        "role":"stack_arg",
                        "is_arg":true
                    }
                ]
            }"#,
            64,
        );

        let stack_arg = ctx
            .stack_slots
            .get(&StackSlotKey {
                base: ExternalStackBase::StackPointer,
                offset: 8,
            })
            .expect("stack-pointer argument slot");

        assert_eq!(stack_arg.role, ExternalStackSlotRole::StackArg);
        assert_eq!(stack_arg.param_index, Some(6));
        assert_eq!(stack_arg.param_name.as_deref(), Some("arg7"));
        assert_eq!(stack_arg.name, "arg_8h");
    }

    #[test]
    fn generated_carrier_types_do_not_become_imported_type_assumptions() {
        let ctx = parse_external_context_json(
            r#"{
                "signature": {
                    "ret": "int64_t",
                    "params": [{"name": "arg1", "type": "int64_t"}]
                },
                "vars": [
                    {
                        "kind": "register",
                        "name": "arg1",
                        "type": "int64_t",
                        "reg": "rdi",
                        "is_arg": true
                    },
                    {
                        "kind": "stack",
                        "name": "var_10h",
                        "type": "int64_t",
                        "base": "rbp",
                        "offset": -16
                    }
                ]
            }"#,
            64,
        );

        assert!(ctx.assumptions.is_empty());
    }

    #[test]
    fn parse_external_context_preserves_sized_padding_members_as_arrays() {
        let ctx = parse_external_context_json(
            r#"{
                "base_types": [
                    {
                        "kind": "struct",
                        "name": "sla_struct_420703e08f70f00e",
                        "members": [
                            {"name": "_pad_0", "offset": 0, "type": "uint8_t", "size_bits": 64},
                            {"name": "f_8", "offset": 8, "type": "int32_t", "size_bits": 32},
                            {"name": "_pad_c", "offset": 12, "type": "uint8_t", "size_bits": 320},
                            {"name": "f_34", "offset": 52, "type": "int32_t", "size_bits": 32}
                        ]
                    }
                ]
            }"#,
            64,
        );

        let st = ctx
            .external_type_db
            .structs
            .get("sla_struct_420703e08f70f00e")
            .expect("expected parsed synthetic struct");
        assert_eq!(
            st.fields.get(&0).and_then(|field| field.ty.as_deref()),
            Some("uint8_t[8]")
        );
        assert_eq!(
            st.fields.get(&8).and_then(|field| field.ty.as_deref()),
            Some("int32_t")
        );
        assert_eq!(
            st.fields.get(&12).and_then(|field| field.ty.as_deref()),
            Some("uint8_t[40]")
        );
        assert_eq!(
            st.fields.get(&52).and_then(|field| field.ty.as_deref()),
            Some("int32_t")
        );
    }
}
