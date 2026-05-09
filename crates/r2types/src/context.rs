use std::collections::{BTreeMap, HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::convert::CTypeLike;
use crate::external::{
    ExternalEnum, ExternalField, ExternalStruct, ExternalTypeDb, ExternalUnion,
    normalize_external_type_name,
};
use crate::facts::{FunctionParamSpec, FunctionSignatureSpec, FunctionType, parse_type_like_spec};
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
    pub context_hash: Option<u64>,
    pub current_signature: Option<FunctionSignatureSpec>,
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    // Legacy compatibility view derived from canonical stack_slots.
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
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
    pub fn legacy_name(&self) -> Option<String> {
        match self {
            Self::FramePointer => Some("rbp".to_string()),
            Self::StackPointer => Some("rsp".to_string()),
            Self::Named(name) if !name.is_empty() => Some(name.clone()),
            Self::Named(_) => None,
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
    pub known_signatures: Vec<KnownSignatureJson>,
    #[serde(default)]
    pub assumptions: Vec<r2ssa::AnalysisAssumption>,
}

pub fn normalize_function_basename(name: &str) -> String {
    let mut lower = name.trim().to_ascii_lowercase();
    for prefix in ["sym.imp.", "sym.", "dbg.", "fcn."] {
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
        ret_type: Some(CTypeLike::Int {
            bits: 32,
            signedness: crate::Signedness::Signed,
        }),
        params: vec![
            FunctionParamSpec {
                name: "argc".to_string(),
                ty: Some(CTypeLike::Int {
                    bits: 32,
                    signedness: crate::Signedness::Signed,
                }),
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

pub fn apply_main_signature_override(
    function_name: &str,
    merged_signature: &mut Option<FunctionSignatureSpec>,
) {
    if is_c_main_function(function_name) {
        *merged_signature = Some(canonical_main_signature_spec());
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

pub fn parse_external_context(raw: ExternalContextJson, ptr_bits: u32) -> ParsedExternalContext {
    let mut parsed = ParsedExternalContext::default();

    if let Some(context) = raw.context.as_ref() {
        parsed.context_schema_version = context.schema_version;
        parsed.context_dirty_epoch = context.dirty_epoch;
        parsed.context_hash = context.context_hash;
    }

    if let Some(signature) = raw.signature.as_ref() {
        parsed.current_signature = parse_signature_json(signature, ptr_bits);
        parsed.callconv = signature.callconv.clone();
        parsed.noreturn = signature.noreturn;
    }

    parsed.external_type_db = external_type_db_from_base_types(&raw.base_types, ptr_bits);
    if let Some(signature) = parsed.current_signature.as_mut() {
        resolve_signature_aliases_from_type_db(signature, &parsed.external_type_db);
    }

    let max_register_params = parsed
        .current_signature
        .as_ref()
        .filter(|signature| signature_param_count_is_authoritative(signature))
        .map(|signature| signature.params.len());
    let (register_params, stack_slots) =
        parse_external_vars(&raw.vars, ptr_bits, max_register_params);
    parsed.register_params = register_params;
    parsed.stack_slots = stack_slots;
    resolve_register_param_aliases_from_type_db(
        &mut parsed.register_params,
        &parsed.external_type_db,
    );
    resolve_stack_slot_aliases_from_type_db(&mut parsed.stack_slots, &parsed.external_type_db);
    parsed.known_function_signatures = parse_known_signatures(&raw.known_signatures, ptr_bits);
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
        if let Some(ty) = reg.ty.as_ref() {
            maybe_push_type_hints(
                r2ssa::AssumptionSubject::Register {
                    name: reg.reg.clone(),
                },
                ty,
            );
        }
    }
    for (slot_key, slot) in stack_slots {
        if let Some(ty) = slot.ty.as_ref() {
            maybe_push_type_hints(
                r2ssa::AssumptionSubject::StackSlot {
                    base: slot_key
                        .base
                        .legacy_name()
                        .unwrap_or_else(|| "stack".to_string()),
                    offset: slot_key.offset,
                },
                ty,
            );
            if let Some(index) = slot.param_index {
                maybe_push_type_hints(r2ssa::AssumptionSubject::Parameter { index }, ty);
            }
        }
    }
    assumptions
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
                    .and_then(|raw| parse_type_like_spec(raw, ptr_bits)),
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
        .and_then(|raw| parse_type_like_spec(raw, ptr_bits));

    if params.is_empty() && ret_type.is_none() {
        return None;
    }

    Some(FunctionSignatureSpec { ret_type, params })
}

fn parse_external_vars(
    vars: &[ExternalVarJson],
    ptr_bits: u32,
    max_register_params: Option<usize>,
) -> (
    Vec<ExternalRegisterParamSpec>,
    BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
) {
    let mut register_params = Vec::new();
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
            .and_then(|raw| parse_type_like_spec(raw, ptr_bits));

        match var.kind {
            ExternalVarKind::Register => {
                let param_index = var.param_index.unwrap_or(register_params.len());
                if max_register_params.is_some_and(|limit| param_index >= limit) {
                    continue;
                }
                register_params.push(ExternalRegisterParamSpec {
                    name,
                    ty,
                    reg: var.reg.clone().unwrap_or_default(),
                });
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
                let candidate = ExternalStackSlotSpec {
                    name,
                    ty,
                    base: base.clone(),
                    role,
                    param_index: var.param_index,
                    param_name: var.param_name.clone(),
                    source_reg: var.source_reg.clone(),
                };
                let key = StackSlotKey { base, offset };
                merge_stack_slot_candidate(&mut stack_slots, key, candidate.clone());
            }
        }
    }

    (register_params, stack_slots)
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
                    .and_then(|raw| parse_type_like_spec(raw, ptr_bits))
                    .unwrap_or(CTypeLike::Unknown)
            })
            .collect::<Vec<_>>();
        let return_type = entry
            .ret_type
            .as_deref()
            .and_then(|raw| parse_type_like_spec(raw, ptr_bits))
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
    if name.is_empty() {
        return;
    }
    known.insert(name.to_string(), sig.clone());

    for prefix in ["sym.imp.", "sym.", "dbg.", "fcn."] {
        if let Some(stripped) = name.strip_prefix(prefix)
            && !stripped.is_empty()
        {
            known.insert(stripped.to_string(), sig.clone());
        }
    }
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

fn signature_strength(signature: &FunctionSignatureSpec) -> u8 {
    let has_type_info =
        signature.ret_type.is_some() || signature.params.iter().any(|param| param.ty.is_some());
    let has_named_params = signature
        .params
        .iter()
        .any(|param| !is_generic_arg_name(&param.name));
    if has_type_info || has_named_params {
        96
    } else {
        80
    }
}

fn signature_param_count_is_authoritative(signature: &FunctionSignatureSpec) -> bool {
    if signature.params.is_empty() {
        return false;
    }
    signature_strength(signature) >= 96
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
    fn apply_main_signature_override_uses_canonical_signature() {
        let mut merged = None;
        apply_main_signature_override("dbg.main", &mut merged);
        let merged = merged.expect("main signature");
        assert_eq!(merged.params.len(), 3);
        assert_eq!(merged.params[0].name, "argc");
        assert_eq!(merged.params[1].name, "argv");
        assert_eq!(merged.params[2].name, "envp");
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
