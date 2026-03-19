use std::collections::{BTreeMap, HashMap};

use crate::context::{
    ExternalRegisterParamSpec, ExternalStackSlotSpec, ExternalStackVarSpec, StackSlotKey,
};
use crate::convert::CTypeLike;
use crate::external::ExternalTypeDb;
use crate::model::Signedness;

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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFacts {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    // Compatibility view for offset-only decompiler consumers during the Wave 2A migration.
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFactInputs {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub local_field_accesses: Vec<LocalFieldAccessFact>,
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
            && self.external_stack_vars.is_empty()
            && self.external_type_db.structs.is_empty()
            && self.external_type_db.unions.is_empty()
            && self.external_type_db.enums.is_empty()
            && self.external_type_db.diagnostics.is_empty()
            && self.slot_type_overrides.is_empty()
            && self.slot_field_profiles.is_empty()
            && self.diagnostics.is_empty()
    }

    pub fn builder(inputs: FunctionTypeFactInputs) -> FunctionTypeFactsBuilder {
        FunctionTypeFactsBuilder::new(inputs)
    }
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

        let mut diagnostics = self.inputs.diagnostics;
        diagnostics.extend(self.inputs.external_type_db.diagnostics.iter().cloned());
        dedup_preserving_order(&mut diagnostics);

        FunctionTypeFacts {
            merged_signature: self.inputs.merged_signature,
            known_function_signatures: self.inputs.known_function_signatures,
            register_params: self.inputs.register_params,
            stack_slots: self.inputs.stack_slots,
            external_stack_vars: self.inputs.external_stack_vars,
            external_type_db: self.inputs.external_type_db,
            slot_type_overrides: self.inputs.slot_type_overrides,
            slot_field_profiles: self.inputs.slot_field_profiles,
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
            .or_insert_with(|| access.field_name.clone());
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
            "bool" => Some(CTypeLike::Bool),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder_merges_local_field_accesses_into_slot_profiles() {
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            local_field_accesses: vec![
                LocalFieldAccessFact {
                    slot: 1,
                    field_offset: 0,
                    field_name: "first".to_string(),
                },
                LocalFieldAccessFact {
                    slot: 1,
                    field_offset: 8,
                    field_name: "second".to_string(),
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
}
