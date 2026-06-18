use std::collections::BTreeSet;

use r2ssa::SSAVarNameKind;

use crate::{FunctionType, SignatureCertificateSource};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallsiteKey {
    pub block_addr: u64,
    pub op_index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeIdentityKey {
    DirectAddress(u64),
    IndirectSite(CallsiteKey),
    Named(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeClass {
    Internal,
    Imported,
    ExternalSymbol,
    RawAddress,
    Indirect,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeIdentityEvidence {
    DirectTarget,
    RawMemoryName,
    RawConstantName,
    ImportedNameHint,
    InternalNameHint,
    KnownSignature,
    FunctionName,
    SymbolName,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalleeIdentity {
    pub target_addr: Option<u64>,
    pub raw_name: Option<String>,
    pub display_name: Option<String>,
    pub normalized_name: Option<String>,
    pub aliases: BTreeSet<String>,
    pub class: CalleeClass,
    pub is_recursive: bool,
    pub signature: Option<FunctionType>,
    pub signature_source: Option<SignatureCertificateSource>,
    pub evidence: BTreeSet<CalleeIdentityEvidence>,
}

impl CalleeIdentity {
    pub fn from_name(name: &str) -> Self {
        let lower = name.trim().to_ascii_lowercase();
        let storage_kind = SSAVarNameKind::classify(&lower);
        let target_addr = parse_raw_address_name(name);
        let imported_hint =
            lower.strip_prefix("sym.imp.").is_some() || lower.strip_prefix("imp.").is_some();
        let internal_hint =
            lower.strip_prefix("fcn.").is_some() || lower.strip_prefix("sym.").is_some();
        let (class, classification_evidence) =
            classify_callee_name(storage_kind, imported_hint, internal_hint);
        let mut evidence = BTreeSet::new();
        if let Some(classification_evidence) = classification_evidence {
            evidence.insert(classification_evidence);
        }
        let raw_name = name.trim().to_string();
        let normalized_name = normalize_callee_name(name);
        let mut aliases = BTreeSet::new();
        if !raw_name.is_empty() {
            aliases.insert(raw_name.clone());
        }
        if !normalized_name.is_empty() {
            aliases.insert(normalized_name.clone());
        }

        Self {
            target_addr,
            raw_name: Some(raw_name.clone()),
            display_name: Some(raw_name),
            normalized_name: Some(normalized_name),
            aliases,
            class,
            is_recursive: false,
            signature: None,
            signature_source: None,
            evidence,
        }
    }

    pub fn raw_name(&self) -> &str {
        self.raw_name.as_deref().unwrap_or("")
    }

    pub fn normalized_name(&self) -> &str {
        self.normalized_name.as_deref().unwrap_or("")
    }

    pub fn class(&self) -> CalleeClass {
        self.class
    }

    pub fn is_raw_storage_target(&self) -> bool {
        self.class == CalleeClass::RawAddress
            && self.evidence.iter().any(|evidence| {
                matches!(
                    evidence,
                    CalleeIdentityEvidence::RawMemoryName | CalleeIdentityEvidence::RawConstantName
                )
            })
    }

    pub fn is_imported_name_hint(&self) -> bool {
        self.class == CalleeClass::Imported
            && self
                .evidence
                .contains(&CalleeIdentityEvidence::ImportedNameHint)
    }

    pub fn is_internal_name_hint(&self) -> bool {
        self.class == CalleeClass::Internal
            && self
                .evidence
                .contains(&CalleeIdentityEvidence::InternalNameHint)
    }
}

fn classify_callee_name(
    storage_kind: SSAVarNameKind,
    imported_hint: bool,
    internal_hint: bool,
) -> (CalleeClass, Option<CalleeIdentityEvidence>) {
    match storage_kind {
        SSAVarNameKind::Memory => (
            CalleeClass::RawAddress,
            Some(CalleeIdentityEvidence::RawMemoryName),
        ),
        SSAVarNameKind::Constant => (
            CalleeClass::RawAddress,
            Some(CalleeIdentityEvidence::RawConstantName),
        ),
        _ if imported_hint => (
            CalleeClass::Imported,
            Some(CalleeIdentityEvidence::ImportedNameHint),
        ),
        _ if internal_hint => (
            CalleeClass::Internal,
            Some(CalleeIdentityEvidence::InternalNameHint),
        ),
        _ => (CalleeClass::Unknown, None),
    }
}

pub fn normalize_callee_name(name: &str) -> String {
    let raw = name.trim();
    if let Some(addr) = parse_raw_address_name(raw) {
        return format!("addr:{addr:x}");
    }
    if let Some(addr) = raw
        .to_ascii_lowercase()
        .strip_prefix("sub_")
        .and_then(|suffix| suffix.split('_').next())
        .and_then(|suffix| u64::from_str_radix(suffix, 16).ok())
    {
        return format!("addr:{addr:x}");
    }

    let mut normalized = raw.to_ascii_lowercase();
    for prefix in ["sym.imp.", "sym.", "imp.", "dbg.", "fcn."] {
        while let Some(rest) = normalized.strip_prefix(prefix) {
            normalized = rest.to_string();
        }
    }
    while let Some(rest) = normalized.strip_suffix("@plt") {
        normalized = rest.to_string();
    }
    while let Some(rest) = normalized.strip_suffix(".plt") {
        normalized = rest.to_string();
    }
    if let Some((base, suffix)) = normalized.rsplit_once('_')
        && !base.is_empty()
        && !suffix.is_empty()
        && suffix.chars().all(|ch| ch.is_ascii_digit())
    {
        normalized = base.to_string();
    }

    normalized
}

fn parse_raw_address_name(name: &str) -> Option<u64> {
    let lower = name.trim().to_ascii_lowercase();
    let kind = SSAVarNameKind::classify(&lower);
    let payload = match kind {
        SSAVarNameKind::Memory => lower.strip_prefix("ram:")?,
        SSAVarNameKind::Constant => lower.strip_prefix("const:")?,
        _ => return None,
    };
    parse_address_payload(payload)
}

fn parse_address_payload(payload: &str) -> Option<u64> {
    let value = payload.split('_').next().unwrap_or(payload);
    if let Some(hex) = value.strip_prefix("0x") {
        return u64::from_str_radix(hex, 16).ok();
    }
    if value.chars().all(|ch| ch.is_ascii_hexdigit()) {
        return u64::from_str_radix(value, 16).ok();
    }
    value.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn callee_identity_classifies_raw_storage_imports_and_internal_names() {
        let cases = [
            ("ram:401000_0", CalleeClass::RawAddress, "addr:401000"),
            ("const:0x401000", CalleeClass::RawAddress, "addr:401000"),
            ("sym.imp.printf", CalleeClass::Imported, "printf"),
            ("imp.printf", CalleeClass::Imported, "printf"),
            ("sym.helper", CalleeClass::Internal, "helper"),
            ("fcn.401000", CalleeClass::Internal, "401000"),
            ("helper", CalleeClass::Unknown, "helper"),
        ];

        for (name, class, normalized) in cases {
            let identity = CalleeIdentity::from_name(name);
            assert_eq!(identity.raw_name(), name);
            assert_eq!(identity.class(), class, "{name}");
            assert_eq!(identity.normalized_name(), normalized, "{name}");
            assert!(identity.aliases.contains(name), "{name}");
            assert!(identity.aliases.contains(normalized), "{name}");
            assert_eq!(
                identity.is_raw_storage_target(),
                class == CalleeClass::RawAddress,
                "{name}",
            );
            assert_eq!(
                identity.is_imported_name_hint(),
                class == CalleeClass::Imported,
                "{name}",
            );
            assert_eq!(
                identity.is_internal_name_hint(),
                class == CalleeClass::Internal,
                "{name}",
            );
        }
    }

    #[test]
    fn callee_identity_normalizes_address_and_plt_aliases() {
        assert_eq!(normalize_callee_name("sub_00401000"), "addr:401000");
        assert_eq!(normalize_callee_name("sym.imp.printf@plt"), "printf");
        assert_eq!(normalize_callee_name("sym.imp.printf.plt"), "printf");
        assert_eq!(normalize_callee_name("sym.helper_2"), "helper");
    }

    #[test]
    fn callee_identity_predicates_require_matching_evidence() {
        let base = CalleeIdentity {
            target_addr: None,
            raw_name: None,
            display_name: None,
            normalized_name: None,
            aliases: BTreeSet::new(),
            class: CalleeClass::RawAddress,
            is_recursive: false,
            signature: None,
            signature_source: None,
            evidence: BTreeSet::new(),
        };

        assert!(!base.is_raw_storage_target());

        let mut imported_without_evidence = base.clone();
        imported_without_evidence.class = CalleeClass::Imported;
        assert!(!imported_without_evidence.is_imported_name_hint());

        let mut internal_without_evidence = base.clone();
        internal_without_evidence.class = CalleeClass::Internal;
        assert!(!internal_without_evidence.is_internal_name_hint());

        let mut raw_with_evidence = base.clone();
        raw_with_evidence
            .evidence
            .insert(CalleeIdentityEvidence::RawMemoryName);
        assert!(raw_with_evidence.is_raw_storage_target());

        let mut imported_with_evidence = imported_without_evidence;
        imported_with_evidence
            .evidence
            .insert(CalleeIdentityEvidence::ImportedNameHint);
        assert!(imported_with_evidence.is_imported_name_hint());

        let mut internal_with_evidence = internal_without_evidence;
        internal_with_evidence
            .evidence
            .insert(CalleeIdentityEvidence::InternalNameHint);
        assert!(internal_with_evidence.is_internal_name_hint());
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    fn pick_name_kind(tag: u8) -> SSAVarNameKind {
        match tag % 10 {
            0 => SSAVarNameKind::RegisterAlias,
            1 => SSAVarNameKind::Temporary,
            2 => SSAVarNameKind::Constant,
            3 => SSAVarNameKind::Memory,
            4 => SSAVarNameKind::AddressSpace,
            5 => SSAVarNameKind::Symbol,
            6 => SSAVarNameKind::Object,
            7 => SSAVarNameKind::Data,
            8 => SSAVarNameKind::Got,
            _ => SSAVarNameKind::Ordinary,
        }
    }

    #[kani::proof]
    fn callee_name_classification_precedence_is_total() {
        let storage_kind = pick_name_kind(kani::any());
        let imported_hint: bool = kani::any();
        let internal_hint: bool = kani::any();

        let (class, evidence) = classify_callee_name(storage_kind, imported_hint, internal_hint);

        match storage_kind {
            SSAVarNameKind::Memory => {
                assert_eq!(class, CalleeClass::RawAddress);
                assert_eq!(evidence, Some(CalleeIdentityEvidence::RawMemoryName));
            }
            SSAVarNameKind::Constant => {
                assert_eq!(class, CalleeClass::RawAddress);
                assert_eq!(evidence, Some(CalleeIdentityEvidence::RawConstantName));
            }
            _ if imported_hint => {
                assert_eq!(class, CalleeClass::Imported);
                assert_eq!(evidence, Some(CalleeIdentityEvidence::ImportedNameHint));
            }
            _ if internal_hint => {
                assert_eq!(class, CalleeClass::Internal);
                assert_eq!(evidence, Some(CalleeIdentityEvidence::InternalNameHint));
            }
            _ => {
                assert_eq!(class, CalleeClass::Unknown);
                assert_eq!(evidence, None);
            }
        }
    }
}
