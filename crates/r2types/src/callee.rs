use std::collections::{BTreeMap, BTreeSet, HashMap};

use r2ssa::SSAVarNameKind;

use crate::{CalleeFact, FunctionType, SignatureCertificateSource};

const CALLEE_IMPORT_PREFIXES: [&str; 3] = ["sym.imp.", "imp.", "reloc."];
const CALLEE_NAMESPACE_PREFIXES: [&str; 6] = ["sym.imp.", "sym.", "imp.", "reloc.", "dbg.", "fcn."];
const WINDOWS_RUNTIME_REGISTRATION_SUFFIX: &str = "addvectoredexceptionhandler";

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
    CalleeFactName,
    KnownSignature,
    FunctionName,
    SymbolName,
}

#[derive(Debug, Clone, Copy)]
pub struct CalleeIdentityContext<'a> {
    pub function_names: &'a HashMap<u64, String>,
    pub symbols: &'a HashMap<u64, String>,
    pub callee_facts: &'a BTreeMap<u64, CalleeFact>,
    pub known_function_signatures: &'a HashMap<String, FunctionType>,
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
        let imported_hint = callee_name_is_import_like(&lower);
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

    pub fn from_direct_target(addr: u64, ctx: &CalleeIdentityContext<'_>) -> Self {
        let mut evidence = BTreeSet::from([CalleeIdentityEvidence::DirectTarget]);
        let fact_name = ctx
            .callee_facts
            .get(&addr)
            .and_then(|fact| fact.name.as_deref())
            .filter(|name| !name.trim().is_empty());
        let function_name = ctx
            .function_names
            .get(&addr)
            .map(String::as_str)
            .filter(|name| !name.trim().is_empty());
        let symbol_name = ctx
            .symbols
            .get(&addr)
            .map(String::as_str)
            .filter(|name| !name.trim().is_empty());

        let (name, name_evidence) = if let Some(name) = fact_name {
            (name, CalleeIdentityEvidence::CalleeFactName)
        } else if let Some(name) = function_name {
            (name, CalleeIdentityEvidence::FunctionName)
        } else if let Some(name) = symbol_name {
            (name, CalleeIdentityEvidence::SymbolName)
        } else {
            ("", CalleeIdentityEvidence::DirectTarget)
        };

        let mut identity = if name.is_empty() {
            let display_name = format!("sub_{addr:x}");
            let mut aliases = BTreeSet::from([format!("addr:{addr:x}"), display_name.clone()]);
            aliases.insert(format!("0x{addr:x}"));
            CalleeIdentity {
                target_addr: Some(addr),
                raw_name: Some(display_name.clone()),
                display_name: Some(display_name),
                normalized_name: Some(format!("addr:{addr:x}")),
                aliases,
                class: CalleeClass::RawAddress,
                is_recursive: false,
                signature: None,
                signature_source: None,
                evidence,
            }
        } else {
            evidence.insert(name_evidence);
            let mut identity = Self::from_name(name);
            identity.target_addr = Some(addr);
            identity.evidence.extend(evidence);
            identity
        };

        identity.insert_direct_target_aliases(addr);
        if let Some(name) = fact_name {
            identity.insert_name_alias(name);
        }
        if let Some(name) = function_name {
            identity.insert_name_alias(name);
        }
        if let Some(name) = symbol_name {
            identity.insert_name_alias(name);
            if identity.class == CalleeClass::Unknown {
                identity.class = CalleeClass::ExternalSymbol;
            }
        }
        identity.attach_known_signature(ctx.known_function_signatures);
        identity
    }

    pub fn with_known_signature(mut self, signatures: &HashMap<String, FunctionType>) -> Self {
        self.attach_known_signature(signatures);
        self
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

    pub fn has_known_signature(&self) -> bool {
        self.signature.is_some()
            && self
                .evidence
                .contains(&CalleeIdentityEvidence::KnownSignature)
    }

    pub fn known_signature(&self) -> Option<&FunctionType> {
        self.has_known_signature()
            .then_some(self.signature.as_ref())
            .flatten()
    }

    pub fn non_variadic_known_arity(&self) -> Option<usize> {
        self.known_signature()
            .and_then(|signature| (!signature.variadic).then_some(signature.params.len()))
    }

    pub fn matches_normalized_name(&self, normalized: &str) -> bool {
        let normalized = normalized.trim();
        !normalized.is_empty()
            && (self.normalized_name.as_deref() == Some(normalized)
                || self
                    .aliases
                    .iter()
                    .any(|alias| normalize_callee_name(alias) == normalized))
    }

    pub fn primary_key(&self) -> String {
        self.normalized_name
            .clone()
            .or_else(|| self.display_name.clone())
            .or_else(|| self.raw_name.clone())
            .or_else(|| self.target_addr.map(|addr| format!("addr:{addr:x}")))
            .unwrap_or_default()
    }

    pub fn matches_identity(&self, other: &Self) -> bool {
        let left = self.primary_key();
        let right = other.primary_key();
        (!left.is_empty() && left == right)
            || self
                .aliases
                .iter()
                .any(|alias| other.aliases.contains(alias))
    }

    fn insert_direct_target_aliases(&mut self, addr: u64) {
        self.aliases.insert(format!("addr:{addr:x}"));
        self.aliases.insert(format!("sub_{addr:x}"));
        self.aliases.insert(format!("0x{addr:x}"));
    }

    fn insert_name_alias(&mut self, name: &str) {
        let trimmed = name.trim();
        if trimmed.is_empty() {
            return;
        }
        self.aliases.insert(trimmed.to_string());
        let normalized = normalize_callee_name(trimmed);
        if !normalized.is_empty() {
            self.aliases.insert(normalized);
        }
    }

    fn attach_known_signature(&mut self, signatures: &HashMap<String, FunctionType>) {
        let mut candidates = self.aliases.iter().cloned().collect::<Vec<_>>();
        if let Some(name) = &self.raw_name {
            candidates.push(name.clone());
        }
        if let Some(name) = &self.display_name {
            candidates.push(name.clone());
        }
        if let Some(name) = &self.normalized_name {
            candidates.push(name.clone());
        }

        for candidate in candidates {
            let normalized = normalize_callee_name(&candidate);
            if let Some(signature) = signatures
                .get(&candidate)
                .or_else(|| signatures.get(&normalized))
            {
                self.signature = Some(signature.clone());
                self.signature_source = Some(SignatureCertificateSource::ExternalContext);
                self.evidence.insert(CalleeIdentityEvidence::KnownSignature);
                return;
            }
        }
    }
}

pub fn callee_name_is_import_like(name: &str) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    callee_lower_name_is_import_like(&normalized)
}

fn callee_lower_name_is_import_like(normalized: &str) -> bool {
    !normalized.is_empty()
        && CALLEE_IMPORT_PREFIXES
            .iter()
            .any(|prefix| normalized.starts_with(prefix))
}

pub fn callee_name_is_windows_runtime_registration(name: &str) -> bool {
    let normalized = normalize_callee_name(name);
    callee_normalized_name_is_windows_runtime_registration(&normalized)
}

fn callee_normalized_name_is_windows_runtime_registration(normalized: &str) -> bool {
    !normalized.is_empty() && normalized.ends_with(WINDOWS_RUNTIME_REGISTRATION_SUFFIX)
}

pub fn callee_name_is_runtime_copy(name: &str) -> bool {
    let normalized = normalize_callee_name(name);
    callee_normalized_name_is_runtime_copy(&normalized)
}

fn callee_normalized_name_is_runtime_copy(normalized: &str) -> bool {
    normalized == "memcpy" || normalized == "__memcpy_chk" || normalized.starts_with("memcpy")
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
    loop {
        let mut stripped = false;
        for prefix in CALLEE_NAMESPACE_PREFIXES {
            if let Some(rest) = normalized.strip_prefix(prefix) {
                normalized = rest.to_string();
                stripped = true;
                break;
            }
        }
        if !stripped {
            break;
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

    fn empty_identity_context<'a>(
        function_names: &'a HashMap<u64, String>,
        symbols: &'a HashMap<u64, String>,
        callee_facts: &'a BTreeMap<u64, CalleeFact>,
        known_signatures: &'a HashMap<String, FunctionType>,
    ) -> CalleeIdentityContext<'a> {
        CalleeIdentityContext {
            function_names,
            symbols,
            callee_facts,
            known_function_signatures: known_signatures,
        }
    }

    fn callee_fact(addr: u64, name: &str) -> CalleeFact {
        CalleeFact {
            function_id: addr,
            name: Some(name.to_string()),
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
            return_relation: crate::CalleeReturnRelation::Unknown,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        }
    }

    fn test_signature() -> FunctionType {
        FunctionType {
            return_type: crate::CTypeLike::Int {
                bits: 32,
                signedness: crate::Signedness::Signed,
            },
            params: Vec::new(),
            variadic: true,
        }
    }

    fn non_variadic_signature(param_count: usize) -> FunctionType {
        FunctionType {
            return_type: crate::CTypeLike::Void,
            params: vec![
                crate::CTypeLike::Int {
                    bits: 32,
                    signedness: crate::Signedness::Signed,
                };
                param_count
            ],
            variadic: false,
        }
    }

    fn minimal_identity_with_key(key: Option<&str>) -> CalleeIdentity {
        CalleeIdentity {
            target_addr: None,
            raw_name: None,
            display_name: None,
            normalized_name: key.map(str::to_string),
            aliases: BTreeSet::new(),
            class: CalleeClass::Unknown,
            is_recursive: false,
            signature: None,
            signature_source: None,
            evidence: BTreeSet::new(),
        }
    }

    #[test]
    fn callee_identity_classifies_raw_storage_imports_and_internal_names() {
        let cases = [
            ("ram:401000_0", CalleeClass::RawAddress, "addr:401000"),
            ("const:0x401000", CalleeClass::RawAddress, "addr:401000"),
            ("sym.imp.printf", CalleeClass::Imported, "printf"),
            ("imp.printf", CalleeClass::Imported, "printf"),
            ("reloc.memcpy", CalleeClass::Imported, "memcpy"),
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
        assert_eq!(normalize_callee_name("reloc.sym.imp.memcpy"), "memcpy");
        assert_eq!(normalize_callee_name("sym.helper_2"), "helper");
    }

    #[test]
    fn callee_scope_name_predicates_preserve_runtime_helper_contract() {
        assert!(callee_name_is_import_like("sym.imp.printf"));
        assert!(callee_name_is_import_like("imp.printf"));
        assert!(callee_name_is_import_like("reloc.memcpy"));
        assert!(!callee_name_is_import_like("sym.printf"));
        assert!(!callee_name_is_import_like("memcpy"));

        assert!(callee_name_is_windows_runtime_registration(
            "sym.imp.KERNEL32_AddVectoredExceptionHandler",
        ));
        assert!(callee_name_is_windows_runtime_registration(
            "reloc.AddVectoredExceptionHandler",
        ));
        assert!(!callee_name_is_windows_runtime_registration(
            "AddVectoredContinueHandler"
        ));

        assert!(callee_name_is_runtime_copy("memcpy"));
        assert!(callee_name_is_runtime_copy("__memcpy_chk"));
        assert!(callee_name_is_runtime_copy("reloc.memcpy_s"));
        assert!(!callee_name_is_runtime_copy("not_memcpy"));
    }

    #[test]
    fn direct_target_identity_uses_callee_fact_before_function_and_symbol_names() {
        let function_names = HashMap::from([(0x401000, "sym.function_name".to_string())]);
        let symbols = HashMap::from([(0x401000, "sym.symbol_name".to_string())]);
        let callee_facts = BTreeMap::from([(0x401000, callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x401000, &ctx);

        assert_eq!(identity.target_addr, Some(0x401000));
        assert_eq!(identity.display_name.as_deref(), Some("sym.imp.printf"));
        assert_eq!(identity.normalized_name(), "printf");
        assert_eq!(identity.class(), CalleeClass::Imported);
        assert!(
            identity
                .evidence
                .contains(&CalleeIdentityEvidence::DirectTarget)
        );
        assert!(
            identity
                .evidence
                .contains(&CalleeIdentityEvidence::CalleeFactName)
        );
        assert!(identity.aliases.contains("addr:401000"));
        assert!(identity.aliases.contains("sym.function_name"));
        assert!(identity.aliases.contains("sym.symbol_name"));
    }

    #[test]
    fn direct_target_identity_attaches_known_signature_by_normalized_alias() {
        let function_names = HashMap::from([(0x401030, "sym.imp.printf@plt".to_string())]);
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::from([("printf".to_string(), test_signature())]);
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x401030, &ctx);

        assert!(identity.has_known_signature());
        assert_eq!(
            identity.signature_source,
            Some(SignatureCertificateSource::ExternalContext)
        );
        assert!(
            identity
                .evidence
                .contains(&CalleeIdentityEvidence::KnownSignature)
        );
        assert_eq!(identity.primary_key(), "printf");
        assert!(identity.matches_identity(&CalleeIdentity::from_name("printf")));
    }

    #[test]
    fn known_signature_predicate_requires_signature_and_evidence() {
        let mut signature_without_evidence = CalleeIdentity::from_name("printf");
        signature_without_evidence.signature = Some(test_signature());
        assert!(!signature_without_evidence.has_known_signature());
        assert!(signature_without_evidence.known_signature().is_none());
        assert_eq!(signature_without_evidence.non_variadic_known_arity(), None);

        let mut evidence_without_signature = CalleeIdentity::from_name("printf");
        evidence_without_signature
            .evidence
            .insert(CalleeIdentityEvidence::KnownSignature);
        assert!(!evidence_without_signature.has_known_signature());
        assert!(evidence_without_signature.known_signature().is_none());

        let mut complete = CalleeIdentity::from_name("printf");
        complete.signature = Some(test_signature());
        complete
            .evidence
            .insert(CalleeIdentityEvidence::KnownSignature);
        assert!(complete.has_known_signature());
        assert!(complete.known_signature().is_some());
        assert_eq!(complete.non_variadic_known_arity(), None);

        let mut non_variadic = CalleeIdentity::from_name("strcmp");
        non_variadic.signature = Some(non_variadic_signature(2));
        non_variadic
            .evidence
            .insert(CalleeIdentityEvidence::KnownSignature);
        assert_eq!(non_variadic.non_variadic_known_arity(), Some(2));
    }

    #[test]
    fn direct_target_identity_does_not_insert_empty_normalized_aliases() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(0x401040, callee_fact(0x401040, "sym.imp."))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x401040, &ctx);

        assert!(!identity.aliases.contains(""));
    }

    #[test]
    fn callee_identity_matching_separates_exact_alias_and_negative_cases() {
        let exact_left = minimal_identity_with_key(Some("printf"));
        let exact_right = minimal_identity_with_key(Some("printf"));
        assert!(exact_left.matches_identity(&exact_right));

        let mut alias_left = minimal_identity_with_key(Some("fact_helper"));
        alias_left.aliases.insert("sym.function_name".to_string());
        let mut alias_right = minimal_identity_with_key(Some("function_name"));
        alias_right.aliases.insert("sym.function_name".to_string());
        assert!(alias_left.matches_identity(&alias_right));

        let unrelated_left = CalleeIdentity::from_name("sym.imp.printf");
        let unrelated_right = CalleeIdentity::from_name("sym.imp.puts");
        assert!(!unrelated_left.matches_identity(&unrelated_right));

        let empty_left = minimal_identity_with_key(None);
        let empty_right = minimal_identity_with_key(None);
        assert!(!empty_left.matches_identity(&empty_right));
    }

    #[test]
    fn normalized_name_matching_uses_canonical_aliases_only() {
        let identity = CalleeIdentity::from_name("sym.imp.printf@plt");

        assert!(identity.matches_normalized_name("printf"));
        assert!(!identity.matches_normalized_name(""));
        assert!(!identity.matches_normalized_name("puts"));

        let normalized_only = minimal_identity_with_key(Some("strcmp"));
        assert!(normalized_only.matches_normalized_name("strcmp"));

        let mut alias_only = minimal_identity_with_key(Some("fact_helper"));
        alias_only.aliases.insert("sym.imp.memcpy@plt".to_string());
        assert!(alias_only.matches_normalized_name("memcpy"));
        assert!(!alias_only.matches_normalized_name("fact_helper_and_memcpy"));
    }

    #[test]
    fn direct_target_identity_without_names_remains_address_keyed() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x401050, &ctx);

        assert_eq!(identity.target_addr, Some(0x401050));
        assert_eq!(identity.primary_key(), "addr:401050");
        assert_eq!(identity.display_name.as_deref(), Some("sub_401050"));
        assert!(
            identity
                .evidence
                .contains(&CalleeIdentityEvidence::DirectTarget)
        );
        assert!(identity.aliases.contains("addr:401050"));
        assert!(identity.aliases.contains("sub_401050"));
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

    fn proof_identity(key: Option<&str>) -> CalleeIdentity {
        CalleeIdentity {
            target_addr: None,
            raw_name: None,
            display_name: None,
            normalized_name: key.map(str::to_string),
            aliases: BTreeSet::new(),
            class: CalleeClass::Unknown,
            is_recursive: false,
            signature: None,
            signature_source: None,
            evidence: BTreeSet::new(),
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

    #[kani::proof]
    fn identity_matching_requires_nonempty_equal_key_or_alias_overlap() {
        let left = proof_identity(Some("printf"));
        let same = proof_identity(Some("printf"));
        let different = proof_identity(Some("puts"));
        let empty_left = proof_identity(None);
        let empty_right = proof_identity(None);

        assert!(left.matches_identity(&same));
        assert!(!left.matches_identity(&different));
        assert!(!empty_left.matches_identity(&empty_right));
    }

    #[kani::proof]
    fn callee_scope_name_predicates_preserve_required_helper_cases() {
        assert!(callee_lower_name_is_import_like("reloc.memcpy"));
        assert!(callee_lower_name_is_import_like("sym.imp.printf"));
        assert!(callee_lower_name_is_import_like("imp.printf"));
        assert!(!callee_lower_name_is_import_like("sym.printf"));
        assert!(!callee_lower_name_is_import_like(""));
        assert!(callee_normalized_name_is_windows_runtime_registration(
            "kernel32_addvectoredexceptionhandler"
        ));
        assert!(callee_normalized_name_is_runtime_copy("memcpy_s"));
        assert!(callee_normalized_name_is_runtime_copy("__memcpy_chk"));
        assert!(!callee_normalized_name_is_runtime_copy("not_memcpy"));
    }
}
