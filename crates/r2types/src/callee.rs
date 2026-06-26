use std::collections::{BTreeMap, BTreeSet, HashMap};

use r2ssa::SSAVarNameKind;

use crate::{
    CalleeFact, CalleeLinkage, FunctionType, InterprocSummaryView, SignatureCertificateSource,
    SignatureRegistry,
};

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
    ImportLinkage,
    InternalNameHint,
    CalleeFactName,
    KnownSignature,
    FunctionName,
    SymbolName,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeAritySource {
    KnownSignature,
    SummaryHint,
    SignatureRegistry,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CalleeArityDecision {
    pub arity: usize,
    pub source: CalleeAritySource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeTargetPolicySource {
    ImportLinkage,
    CalleeFact,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeCallArgPolicy {
    Standard,
    ImportedLike,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CalleeTargetResolutionSource {
    PreparedIdentity,
    CallsiteResolution,
    PreparedDirectTarget,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CalleeTargetPolicyDecision {
    pub imported: bool,
    pub modeled: bool,
    pub modeled_addr: Option<u64>,
    pub sources: BTreeSet<CalleeTargetPolicySource>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedCalleeIdentity {
    pub key: Option<CalleeIdentityKey>,
    pub identity: CalleeIdentity,
    pub source: CalleeTargetResolutionSource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedCalleeTarget {
    pub key: Option<CalleeIdentityKey>,
    pub identity: CalleeIdentity,
    pub source: CalleeTargetResolutionSource,
    pub policy: CalleeTargetPolicyDecision,
}

#[derive(Debug, Clone, Copy)]
pub struct CalleeTargetIdentityRequest<'a> {
    pub resolution: Option<&'a CalleeResolutionFacts>,
    pub callsite: Option<CallsiteKey>,
    pub prepared_identity: Option<&'a CalleeIdentity>,
    pub prepared_direct_target: Option<u64>,
    pub direct_target_context: Option<&'a CalleeIdentityContext<'a>>,
}

#[derive(Debug, Clone, Copy)]
pub struct CalleeTargetResolutionRequest<'a> {
    pub identity: CalleeTargetIdentityRequest<'a>,
    pub callee_facts: &'a BTreeMap<u64, CalleeFact>,
}

impl CalleeTargetPolicyDecision {
    pub fn imported_or_modeled(&self) -> bool {
        self.imported || self.modeled
    }

    pub fn arg_policy(&self) -> CalleeCallArgPolicy {
        if self.imported_or_modeled() {
            CalleeCallArgPolicy::ImportedLike
        } else {
            CalleeCallArgPolicy::Standard
        }
    }
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

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CalleeResolutionFacts {
    pub by_key: BTreeMap<CalleeIdentityKey, CalleeIdentity>,
    pub by_direct_addr: BTreeMap<u64, CalleeIdentityKey>,
    pub by_callsite: BTreeMap<CallsiteKey, CalleeIdentityKey>,
    pub by_name: BTreeMap<String, CalleeIdentityKey>,
}

fn import_policy_authorized_from_evidence(class: CalleeClass, has_import_linkage: bool) -> bool {
    class == CalleeClass::Imported && has_import_linkage
}

impl CalleeResolutionFacts {
    pub fn is_empty(&self) -> bool {
        self.by_key.is_empty()
            && self.by_direct_addr.is_empty()
            && self.by_callsite.is_empty()
            && self.by_name.is_empty()
    }

    pub fn from_direct_call_targets<I>(targets: I, ctx: &CalleeIdentityContext<'_>) -> Self
    where
        I: IntoIterator<Item = (CallsiteKey, u64)>,
    {
        let mut facts = Self::default();
        facts.index_context(ctx);
        for (callsite, addr) in targets {
            let _ = facts.insert_direct_callsite(callsite, addr, ctx);
        }
        facts
    }

    pub fn from_context(ctx: &CalleeIdentityContext<'_>) -> Self {
        let mut facts = Self::default();
        facts.index_context(ctx);
        facts
    }

    pub fn index_context(&mut self, ctx: &CalleeIdentityContext<'_>) {
        let mut direct_addrs = BTreeSet::new();
        direct_addrs.extend(ctx.callee_facts.keys().copied());
        direct_addrs.extend(ctx.function_names.keys().copied());
        direct_addrs.extend(ctx.symbols.keys().copied());
        for addr in direct_addrs {
            self.ensure_direct_identity(addr, ctx);
        }
        self.index_known_signatures(ctx.known_function_signatures);
    }

    pub fn insert_direct_callsite(
        &mut self,
        callsite: CallsiteKey,
        addr: u64,
        ctx: &CalleeIdentityContext<'_>,
    ) -> Option<&CalleeIdentity> {
        let key = CalleeIdentityKey::DirectAddress(addr);
        if Self::callsite_binding_conflicts(self.by_callsite.get(&callsite), &key) {
            return None;
        }
        let key = self.ensure_direct_identity(addr, ctx);
        self.bind_callsite(callsite, key.clone());
        self.by_key.get(&key)
    }

    pub fn identity_for_callsite(&self, callsite: CallsiteKey) -> Option<&CalleeIdentity> {
        self.by_callsite
            .get(&callsite)
            .and_then(|key| self.by_key.get(key))
    }

    pub fn identity_for_direct_addr(&self, addr: u64) -> Option<&CalleeIdentity> {
        self.by_direct_addr
            .get(&addr)
            .and_then(|key| self.by_key.get(key))
    }

    pub fn identity_for_direct_target_in_context(
        resolution: Option<&Self>,
        addr: u64,
        ctx: &CalleeIdentityContext<'_>,
    ) -> CalleeIdentity {
        resolution
            .and_then(|facts| facts.identity_for_direct_addr(addr))
            .cloned()
            .unwrap_or_else(|| CalleeIdentity::from_direct_target(addr, ctx))
    }

    pub fn identity_for_name(&self, name: &str) -> Option<&CalleeIdentity> {
        let raw = name.trim();
        if raw.is_empty() {
            return None;
        }
        self.by_name
            .get(raw)
            .or_else(|| {
                let normalized = normalize_callee_name(raw);
                self.by_name.get(&normalized)
            })
            .and_then(|key| self.by_key.get(key))
    }

    pub fn identity_for_name_in_context(
        name: &str,
        ctx: &CalleeIdentityContext<'_>,
    ) -> Option<CalleeIdentity> {
        let raw = name.trim();
        if raw.is_empty() {
            return None;
        }
        let normalized = normalize_callee_name(raw);

        let mut direct_addrs = BTreeSet::new();
        direct_addrs.extend(ctx.callee_facts.keys().copied());
        direct_addrs.extend(ctx.function_names.keys().copied());
        direct_addrs.extend(ctx.symbols.keys().copied());
        for addr in direct_addrs {
            let identity = CalleeIdentity::from_direct_target(addr, ctx);
            if Self::identity_matches_raw_or_normalized_name(&identity, raw, &normalized) {
                return Some(identity);
            }
        }

        let mut signature_names = ctx
            .known_function_signatures
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>();
        signature_names.sort_unstable();
        for signature_name in signature_names {
            let identity = CalleeIdentity::from_name(signature_name)
                .with_known_signature(ctx.known_function_signatures);
            if identity.has_known_signature()
                && Self::identity_matches_raw_or_normalized_name(&identity, raw, &normalized)
            {
                return Some(identity);
            }
        }
        None
    }

    pub fn target_resolution_source_for_presence(
        has_prepared_identity: bool,
        has_callsite_identity: bool,
        has_prepared_direct_target_identity: bool,
    ) -> Option<CalleeTargetResolutionSource> {
        if has_prepared_identity {
            Some(CalleeTargetResolutionSource::PreparedIdentity)
        } else if has_callsite_identity {
            Some(CalleeTargetResolutionSource::CallsiteResolution)
        } else if has_prepared_direct_target_identity {
            Some(CalleeTargetResolutionSource::PreparedDirectTarget)
        } else {
            None
        }
    }

    fn key_for_prepared_identity(identity: &CalleeIdentity) -> Option<CalleeIdentityKey> {
        identity
            .target_addr
            .map(CalleeIdentityKey::DirectAddress)
            .or_else(|| {
                let key = identity.primary_key();
                (!key.trim().is_empty()).then_some(CalleeIdentityKey::Named(key))
            })
    }

    fn direct_target_identity_from_request(
        request: CalleeTargetIdentityRequest<'_>,
    ) -> Option<(CalleeIdentityKey, CalleeIdentity)> {
        let addr = request.prepared_direct_target?;
        if let Some(identity) = request
            .resolution
            .and_then(|facts| facts.identity_for_direct_addr(addr))
        {
            return Some((CalleeIdentityKey::DirectAddress(addr), identity.clone()));
        }
        request.direct_target_context.map(|ctx| {
            (
                CalleeIdentityKey::DirectAddress(addr),
                CalleeIdentity::from_direct_target(addr, ctx),
            )
        })
    }

    pub fn resolve_target_identity(
        request: CalleeTargetIdentityRequest<'_>,
    ) -> Option<ResolvedCalleeIdentity> {
        let callsite_identity = request.callsite.and_then(|callsite| {
            let facts = request.resolution?;
            let key = facts.key_for_callsite(callsite)?.clone();
            let identity = facts.by_key.get(&key)?.clone();
            Some((key, identity))
        });
        let direct_target_identity = Self::direct_target_identity_from_request(request);
        let source = Self::target_resolution_source_for_presence(
            request.prepared_identity.is_some(),
            callsite_identity.is_some(),
            direct_target_identity.is_some(),
        )?;
        let (key, identity) = match source {
            CalleeTargetResolutionSource::PreparedIdentity => {
                let identity = request.prepared_identity?.clone();
                (Self::key_for_prepared_identity(&identity), identity)
            }
            CalleeTargetResolutionSource::CallsiteResolution => {
                let (key, identity) = callsite_identity?;
                (Some(key), identity)
            }
            CalleeTargetResolutionSource::PreparedDirectTarget => {
                let (key, identity) = direct_target_identity?;
                (Some(key), identity)
            }
        };
        Some(ResolvedCalleeIdentity {
            key,
            identity,
            source,
        })
    }

    pub fn resolve_target_policy(
        request: CalleeTargetResolutionRequest<'_>,
    ) -> Option<ResolvedCalleeTarget> {
        let resolved = Self::resolve_target_identity(request.identity)?;
        let policy = resolved
            .identity
            .target_policy_decision(request.identity.resolution, request.callee_facts);
        Some(ResolvedCalleeTarget {
            key: resolved.key,
            identity: resolved.identity,
            source: resolved.source,
            policy,
        })
    }

    pub fn key_for_callsite(&self, callsite: CallsiteKey) -> Option<&CalleeIdentityKey> {
        self.by_callsite.get(&callsite)
    }

    fn identity_matches_raw_or_normalized_name(
        identity: &CalleeIdentity,
        raw: &str,
        normalized: &str,
    ) -> bool {
        identity.aliases.contains(raw)
            || identity.raw_name.as_deref() == Some(raw)
            || identity.display_name.as_deref() == Some(raw)
            || (!normalized.is_empty() && identity.matches_normalized_name(normalized))
    }

    fn ensure_direct_identity(
        &mut self,
        addr: u64,
        ctx: &CalleeIdentityContext<'_>,
    ) -> CalleeIdentityKey {
        let key = CalleeIdentityKey::DirectAddress(addr);
        if self.by_key.contains_key(&key) {
            return key;
        }

        let identity = CalleeIdentity::from_direct_target(addr, ctx);
        self.index_identity_aliases(&key, &identity);
        self.by_direct_addr.insert(addr, key.clone());
        self.by_key.insert(key.clone(), identity);
        key
    }

    fn bind_callsite(&mut self, callsite: CallsiteKey, key: CalleeIdentityKey) {
        self.by_callsite.entry(callsite).or_insert(key);
    }

    fn callsite_binding_conflicts(
        existing: Option<&CalleeIdentityKey>,
        key: &CalleeIdentityKey,
    ) -> bool {
        existing.is_some_and(|existing| existing != key)
    }

    fn index_known_signatures(&mut self, signatures: &HashMap<String, FunctionType>) {
        let mut names = signatures.keys().map(String::as_str).collect::<Vec<_>>();
        names.sort_unstable();
        for name in names {
            let trimmed = name.trim();
            if trimmed.is_empty() {
                continue;
            }
            let normalized = normalize_callee_name(trimmed);
            let key_name = if normalized.is_empty() {
                trimmed.to_string()
            } else {
                normalized
            };
            let key = CalleeIdentityKey::Named(key_name);
            if self.by_key.contains_key(&key) {
                continue;
            }
            let identity = CalleeIdentity::from_name(trimmed).with_known_signature(signatures);
            if !identity.has_known_signature() {
                continue;
            }
            self.index_identity_aliases(&key, &identity);
            self.by_key.insert(key, identity);
        }
    }

    fn index_identity_aliases(&mut self, key: &CalleeIdentityKey, identity: &CalleeIdentity) {
        for alias in identity.aliases.iter() {
            self.insert_name_alias(alias, key);
        }
        if let Some(name) = &identity.raw_name {
            self.insert_name_alias(name, key);
        }
        if let Some(name) = &identity.display_name {
            self.insert_name_alias(name, key);
        }
        if let Some(name) = &identity.normalized_name {
            self.insert_name_alias(name, key);
        }
    }

    fn insert_name_alias(&mut self, name: &str, key: &CalleeIdentityKey) {
        let raw = name.trim();
        if raw.is_empty() {
            return;
        }
        self.by_name
            .entry(raw.to_string())
            .or_insert_with(|| key.clone());
        let normalized = normalize_callee_name(raw);
        if !normalized.is_empty() {
            self.by_name
                .entry(normalized)
                .or_insert_with(|| key.clone());
        }
    }
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
        let callee_fact = ctx.callee_facts.get(&addr);
        let fact_name = callee_fact
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
        if callee_fact.is_some_and(|fact| fact.linkage.authorizes_import_policy()) {
            identity = identity.with_import_linkage_evidence();
        } else if callee_fact.is_some_and(|fact| fact.linkage == CalleeLinkage::Internal)
            && identity.class == CalleeClass::Unknown
        {
            identity.class = CalleeClass::Internal;
            identity
                .evidence
                .insert(CalleeIdentityEvidence::InternalNameHint);
        }
        if let Some(signature) = callee_fact.and_then(|fact| fact.signature.as_ref()) {
            identity.signature = Some(signature.clone());
            identity.signature_source = Some(SignatureCertificateSource::ExternalContext);
            identity
                .evidence
                .insert(CalleeIdentityEvidence::KnownSignature);
        } else {
            identity.attach_known_signature(ctx.known_function_signatures);
        }
        identity
    }

    pub fn with_known_signature(mut self, signatures: &HashMap<String, FunctionType>) -> Self {
        self.attach_known_signature(signatures);
        self
    }

    pub fn with_import_linkage_evidence(mut self) -> Self {
        self.class = CalleeClass::Imported;
        self.evidence.insert(CalleeIdentityEvidence::ImportLinkage);
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

    pub fn is_import_policy_authorized(&self) -> bool {
        import_policy_authorized_from_evidence(
            self.class,
            self.evidence
                .contains(&CalleeIdentityEvidence::ImportLinkage),
        )
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

    pub fn non_variadic_arity_decision(
        &self,
        _summary_view: Option<&InterprocSummaryView>,
        _signature_registry: &SignatureRegistry,
        _ptr_bits: u32,
    ) -> Option<CalleeArityDecision> {
        self.non_variadic_known_arity()
            .map(|arity| CalleeArityDecision {
                arity,
                source: CalleeAritySource::KnownSignature,
            })
    }

    pub fn target_policy_decision(
        &self,
        _callee_resolution: Option<&CalleeResolutionFacts>,
        callee_facts: &BTreeMap<u64, CalleeFact>,
    ) -> CalleeTargetPolicyDecision {
        let mut decision = CalleeTargetPolicyDecision::default();
        if self.is_import_policy_authorized() {
            decision.imported = true;
            decision
                .sources
                .insert(CalleeTargetPolicySource::ImportLinkage);
        }

        if let Some(addr) = self.modeled_target_addr(callee_facts) {
            decision.modeled = true;
            decision.modeled_addr = Some(addr);
            decision
                .sources
                .insert(CalleeTargetPolicySource::CalleeFact);
        }

        decision
    }

    pub fn modeled_target_addr(&self, callee_facts: &BTreeMap<u64, CalleeFact>) -> Option<u64> {
        if let Some(addr) = self.target_addr
            && callee_facts
                .get(&addr)
                .is_some_and(CalleeFact::authorizes_model_policy)
        {
            return Some(addr);
        }
        None
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

    fn callee_fact_with_linkage(addr: u64, name: &str, linkage: CalleeLinkage) -> CalleeFact {
        CalleeFact {
            function_id: addr,
            name: Some(name.to_string()),
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
            return_relation: crate::CalleeReturnRelation::Unknown,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        }
    }

    fn callee_fact(addr: u64, name: &str) -> CalleeFact {
        callee_fact_with_linkage(addr, name, CalleeLinkage::Unknown)
    }

    fn imported_callee_fact(addr: u64, name: &str) -> CalleeFact {
        callee_fact_with_linkage(addr, name, CalleeLinkage::Imported)
    }

    fn modeled_callee_fact(addr: u64, name: &str) -> CalleeFact {
        let mut fact = callee_fact(addr, name);
        fact.model_policy_evidence
            .insert(crate::CalleeModelPolicyEvidence::InterprocSummary);
        fact
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
            assert!(
                !identity.is_import_policy_authorized(),
                "raw name hints must not authorize imported-call policy for {name}",
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
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
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
        assert!(
            identity
                .evidence
                .contains(&CalleeIdentityEvidence::ImportLinkage)
        );
        assert!(identity.is_import_policy_authorized());
        assert!(identity.aliases.contains("addr:401000"));
        assert!(identity.aliases.contains("sym.function_name"));
        assert!(identity.aliases.contains("sym.symbol_name"));
    }

    #[test]
    fn import_looking_callee_fact_name_without_linkage_is_hint_only() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(0x401020, callee_fact(0x401020, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x401020, &ctx);

        assert!(identity.is_imported_name_hint());
        assert!(
            !identity.is_import_policy_authorized(),
            "import-looking callee-fact names are aliases until typed linkage certifies them",
        );
        assert!(
            !identity
                .evidence
                .contains(&CalleeIdentityEvidence::ImportLinkage),
            "unknown linkage must not mint import-linkage evidence",
        );
    }

    #[test]
    fn explicit_import_linkage_authorizes_policy_without_import_name_shape() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(0x401028, imported_callee_fact(0x401028, "printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x401028, &ctx);

        assert_eq!(identity.normalized_name(), "printf");
        assert!(identity.is_import_policy_authorized());
        assert!(
            identity
                .evidence
                .contains(&CalleeIdentityEvidence::ImportLinkage),
            "explicit linkage must mint import-linkage evidence independent of name shape",
        );
    }

    #[test]
    fn internal_linkage_classifies_plain_callee_fact_as_internal() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(
            0x40102c,
            callee_fact_with_linkage(0x40102c, "helper", CalleeLinkage::Internal),
        )]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x40102c, &ctx);

        assert_eq!(identity.class(), CalleeClass::Internal);
        assert!(identity.is_internal_name_hint());
        assert!(!identity.is_import_policy_authorized());
    }

    #[test]
    fn unknown_linkage_plain_callee_fact_remains_unknown() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(0x40102d, callee_fact(0x40102d, "helper"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x40102d, &ctx);

        assert_eq!(identity.class(), CalleeClass::Unknown);
        assert!(!identity.is_internal_name_hint());
        assert!(!identity.is_import_policy_authorized());
    }

    #[test]
    fn symbol_names_promote_only_unknown_callee_identities_to_external() {
        let function_names = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::new();
        let external_symbols = HashMap::from([(0x40102e, "external_helper".to_string())]);
        let external_ctx = empty_identity_context(
            &function_names,
            &external_symbols,
            &callee_facts,
            &known_signatures,
        );

        let external = CalleeIdentity::from_direct_target(0x40102e, &external_ctx);

        assert_eq!(external.class(), CalleeClass::ExternalSymbol);

        let internal_symbols = HashMap::from([(0x40102f, "sym.helper".to_string())]);
        let internal_ctx = empty_identity_context(
            &function_names,
            &internal_symbols,
            &callee_facts,
            &known_signatures,
        );

        let internal = CalleeIdentity::from_direct_target(0x40102f, &internal_ctx);

        assert_eq!(internal.class(), CalleeClass::Internal);
        assert!(internal.is_internal_name_hint());
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
        assert!(
            !identity.is_import_policy_authorized(),
            "function-name imports are hints until a typed callee fact certifies import linkage"
        );
    }

    #[test]
    fn direct_target_identity_prefers_typed_callee_fact_signature() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let mut fact = callee_fact(0x401000, "sym.imp.printf");
        fact.signature = Some(non_variadic_signature(2));
        fact.signature_callconv = Some("amd64".to_string());
        let callee_facts = BTreeMap::from([(0x401000, fact)]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeIdentity::from_direct_target(0x401000, &ctx);

        assert_eq!(
            identity
                .known_signature()
                .map(|signature| signature.params.len()),
            Some(2)
        );
        assert_eq!(
            identity.signature_source,
            Some(SignatureCertificateSource::ExternalContext)
        );
        assert!(
            identity
                .evidence
                .contains(&CalleeIdentityEvidence::KnownSignature)
        );
        assert!(
            !identity.is_import_policy_authorized(),
            "typed callee signatures do not imply imported-call policy"
        );
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
    fn callee_resolution_context_name_resolves_normalized_callee_fact_alias() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(0x401000, callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeResolutionFacts::identity_for_name_in_context("printf", &ctx)
            .expect("normalized callee-fact alias should resolve");

        assert_eq!(identity.target_addr, Some(0x401000));
        assert_eq!(identity.normalized_name(), "printf");
        assert!(
            !identity.is_import_policy_authorized(),
            "import-looking aliases are not import authority without typed linkage",
        );
    }

    #[test]
    fn callee_resolution_context_name_authorizes_explicit_import_linkage() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let identity = CalleeResolutionFacts::identity_for_name_in_context("printf", &ctx)
            .expect("normalized imported callee-fact alias should resolve");

        assert_eq!(identity.target_addr, Some(0x401000));
        assert_eq!(identity.normalized_name(), "printf");
        assert!(
            identity.is_import_policy_authorized(),
            "typed import linkage is the authority for imported-call policy",
        );
    }

    #[test]
    fn callee_resolution_context_name_rejects_empty_normalized_alias_collision() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "imp."))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        assert!(
            CalleeResolutionFacts::identity_for_name_in_context("sym.imp.", &ctx).is_none(),
            "empty normalized aliases must not bind unrelated import-looking callee facts",
        );
    }

    #[test]
    fn callee_resolution_context_name_rejects_unmatched_known_signatures() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::from([
            ("aaa".to_string(), non_variadic_signature(1)),
            ("bbb".to_string(), non_variadic_signature(2)),
        ]);
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        assert!(
            CalleeResolutionFacts::identity_for_name_in_context("missing", &ctx).is_none(),
            "known signatures must not resolve unrelated names just because they are signed"
        );
    }

    fn summary_view_with_helper_arity(name: &str, arity: usize) -> InterprocSummaryView {
        let id = r2ssa::InterprocFunctionId(0x401000);
        let mut summary = r2ssa::FunctionSemanticSummary::unknown(id, Some(name.to_string()));
        summary.arg_count_hint = Some(arity);
        let mut set = r2ssa::InterprocSummarySet::default();
        set.summaries.insert(id, summary);
        InterprocSummaryView::new(Some(set))
    }

    fn registry_with_non_variadic_arity(name: &str, arity: usize) -> SignatureRegistry {
        let mut registry = SignatureRegistry::default();
        registry.insert_raw(name, "void", vec!["int".to_string(); arity], false);
        registry
    }

    #[test]
    fn callee_arity_decision_prefers_known_signature_over_summary_and_registry() {
        let known_signatures = HashMap::from([("helper".to_string(), non_variadic_signature(3))]);
        let identity = CalleeIdentity::from_name("helper").with_known_signature(&known_signatures);
        let summary_view = summary_view_with_helper_arity("helper", 1);
        let registry = registry_with_non_variadic_arity("helper", 2);

        assert_eq!(
            identity.non_variadic_arity_decision(Some(&summary_view), &registry, 64),
            Some(CalleeArityDecision {
                arity: 3,
                source: CalleeAritySource::KnownSignature,
            }),
        );
    }

    #[test]
    fn callee_arity_decision_rejects_summary_hint_without_known_signature() {
        let identity = CalleeIdentity::from_name("helper");
        let summary_view = summary_view_with_helper_arity("helper", 4);
        let registry = registry_with_non_variadic_arity("helper", 2);

        assert_eq!(
            identity.non_variadic_arity_decision(Some(&summary_view), &registry, 64),
            None,
        );
    }

    #[test]
    fn callee_arity_decision_rejects_registry_without_known_signature() {
        let identity = CalleeIdentity::from_name("helper");
        let registry = registry_with_non_variadic_arity("helper", 2);

        assert_eq!(
            identity.non_variadic_arity_decision(None, &registry, 64),
            None,
        );
    }

    #[test]
    fn callee_target_policy_does_not_import_from_name_hint_alone() {
        let identity = CalleeIdentity::from_name("sym.imp.printf");
        let callee_facts = BTreeMap::new();

        let decision = identity.target_policy_decision(None, &callee_facts);

        assert!(!decision.imported);
        assert!(!decision.modeled);
        assert!(
            !decision.imported_or_modeled(),
            "import-looking names are hints until typed linkage or modeled evidence exists",
        );
    }

    #[test]
    fn callee_target_policy_authorizes_import_from_typed_linkage() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let identity = CalleeIdentity::from_direct_target(0x401000, &ctx);

        let decision = identity.target_policy_decision(None, &callee_facts);

        assert!(decision.imported);
        assert!(!decision.modeled);
        assert_eq!(decision.modeled_addr, None);
        assert!(decision.imported_or_modeled());
        assert!(
            decision
                .sources
                .contains(&CalleeTargetPolicySource::ImportLinkage)
        );
        assert!(
            !decision
                .sources
                .contains(&CalleeTargetPolicySource::CalleeFact),
            "typed import linkage is import-policy evidence, not model-policy evidence"
        );
    }

    #[test]
    fn callee_target_policy_does_not_model_from_summary_helper_name_without_resolution() {
        let identity = CalleeIdentity::from_name("helper.summary");
        let callee_facts = BTreeMap::new();

        let decision = identity.target_policy_decision(None, &callee_facts);

        assert!(!decision.imported);
        assert!(
            !decision.modeled,
            "summary helper names must not authorize modeled policy without typed resolution"
        );
        assert_eq!(decision.modeled_addr, None);
        assert!(!decision.imported_or_modeled());
        assert!(decision.sources.is_empty());
    }

    #[test]
    fn callee_target_policy_does_not_model_from_callee_fact_presence_without_evidence() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::from([(0x401000, callee_fact(0x401000, "sym.memcpy"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let resolution = CalleeResolutionFacts::from_context(&ctx);
        let identity = CalleeIdentity::from_name("memcpy");

        let decision = identity.target_policy_decision(Some(&resolution), &callee_facts);

        assert!(!decision.imported);
        assert!(!decision.modeled);
        assert_eq!(decision.modeled_addr, None);
        assert!(decision.sources.is_empty());
    }

    #[test]
    fn callee_target_policy_models_from_explicit_callee_fact_evidence_through_resolution() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, modeled_callee_fact(0x401000, "sym.memcpy"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let identity = CalleeIdentity::from_direct_target(0x401000, &ctx);

        let decision = identity.target_policy_decision(None, &callee_facts);

        assert!(!decision.imported);
        assert!(decision.modeled);
        assert_eq!(decision.modeled_addr, Some(0x401000));
        assert_eq!(
            decision.sources,
            BTreeSet::from([CalleeTargetPolicySource::CalleeFact]),
        );
    }

    #[test]
    fn callee_resolution_source_precedence_truth_table_is_exhaustive() {
        for mask in 0u8..8 {
            let has_prepared_identity = mask & 0b0001 != 0;
            let has_callsite_identity = mask & 0b0010 != 0;
            let has_prepared_direct_target = mask & 0b0100 != 0;

            let expected = if has_prepared_identity {
                Some(CalleeTargetResolutionSource::PreparedIdentity)
            } else if has_callsite_identity {
                Some(CalleeTargetResolutionSource::CallsiteResolution)
            } else if has_prepared_direct_target {
                Some(CalleeTargetResolutionSource::PreparedDirectTarget)
            } else {
                None
            };

            assert_eq!(
                CalleeResolutionFacts::target_resolution_source_for_presence(
                    has_prepared_identity,
                    has_callsite_identity,
                    has_prepared_direct_target,
                ),
                expected,
                "wrong source precedence for mask {mask:04b}",
            );
        }
    }

    #[test]
    fn callee_resolution_policy_prefers_prepared_identity_over_callsite_resolution() {
        let function_names = HashMap::from([(0x402000, "sym.local".to_string())]);
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let callsite = CallsiteKey {
            block_addr: 0x10,
            op_index: 0,
        };
        let resolution =
            CalleeResolutionFacts::from_direct_call_targets([(callsite, 0x402000)], &ctx);
        let prepared_identity = CalleeIdentity::from_direct_target(0x401000, &ctx);

        let resolved =
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: Some(&resolution),
                    callsite: Some(callsite),
                    prepared_identity: Some(&prepared_identity),
                    prepared_direct_target: None,
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .expect("prepared identity should resolve");

        assert_eq!(
            resolved.source,
            CalleeTargetResolutionSource::PreparedIdentity,
        );
        assert_eq!(resolved.identity.target_addr, Some(0x401000));
        assert_eq!(
            resolved.policy.arg_policy(),
            CalleeCallArgPolicy::ImportedLike
        );
    }

    #[test]
    fn callee_resolution_policy_prefers_callsite_identity_over_other_typed_inputs() {
        let function_names = HashMap::from([(0x402000, "sym.local".to_string())]);
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let callsite = CallsiteKey {
            block_addr: 0x10,
            op_index: 0,
        };
        let resolution =
            CalleeResolutionFacts::from_direct_call_targets([(callsite, 0x402000)], &ctx);

        let resolved =
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: Some(&resolution),
                    callsite: Some(callsite),
                    prepared_identity: None,
                    prepared_direct_target: Some(0x401000),
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .expect("callsite identity should resolve");

        assert_eq!(
            resolved.source,
            CalleeTargetResolutionSource::CallsiteResolution,
        );
        assert_eq!(resolved.identity.target_addr, Some(0x402000));
        assert_eq!(resolved.policy.arg_policy(), CalleeCallArgPolicy::Standard);
        assert!(!resolved.policy.imported);
    }

    #[test]
    fn callee_resolution_policy_keeps_imported_callsite_over_prepared_direct_target() {
        let function_names = HashMap::from([(0x402000, "sym.local".to_string())]);
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let callsite = CallsiteKey {
            block_addr: 0x10,
            op_index: 0,
        };
        let resolution =
            CalleeResolutionFacts::from_direct_call_targets([(callsite, 0x401000)], &ctx);

        let resolved =
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: Some(&resolution),
                    callsite: Some(callsite),
                    prepared_identity: None,
                    prepared_direct_target: Some(0x402000),
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .expect("callsite identity should resolve");

        assert_eq!(
            resolved.source,
            CalleeTargetResolutionSource::CallsiteResolution,
        );
        assert_eq!(resolved.identity.target_addr, Some(0x401000));
        assert!(resolved.policy.imported);
        assert_eq!(
            resolved.policy.arg_policy(),
            CalleeCallArgPolicy::ImportedLike
        );
    }

    #[test]
    fn callee_resolution_policy_uses_prepared_direct_target_without_display_fallback() {
        let function_names = HashMap::from([(0x402000, "sym.local".to_string())]);
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let resolved =
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: None,
                    callsite: None,
                    prepared_identity: None,
                    prepared_direct_target: Some(0x401000),
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .expect("prepared direct target should resolve");

        assert_eq!(
            resolved.source,
            CalleeTargetResolutionSource::PreparedDirectTarget,
        );
        assert_eq!(resolved.identity.target_addr, Some(0x401000));
        assert!(resolved.policy.imported);
    }

    #[test]
    fn callee_resolution_policy_fails_closed_after_typed_sources_fail() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        assert!(
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: None,
                    callsite: None,
                    prepared_identity: None,
                    prepared_direct_target: None,
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .is_none(),
            "rendered/display identities must not be an authoritative fallback",
        );
    }

    #[test]
    fn callee_resolution_policy_does_not_authorize_plain_rendered_names_for_unresolved_sites() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let unresolved_site = CallsiteKey {
            block_addr: 0x10,
            op_index: 0,
        };
        assert!(
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: None,
                    callsite: Some(unresolved_site),
                    prepared_identity: None,
                    prepared_direct_target: None,
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .is_none(),
            "a rendered name must not resolve an unresolved callsite",
        );
    }

    #[test]
    fn callee_resolution_policy_allows_explicit_prepared_direct_targets() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let resolved =
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: None,
                    callsite: None,
                    prepared_identity: None,
                    prepared_direct_target: Some(0x401000),
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .expect("raw rendered target should resolve");

        assert_eq!(
            resolved.source,
            CalleeTargetResolutionSource::PreparedDirectTarget,
        );
        assert!(resolved.policy.imported);
        assert_eq!(
            resolved.policy.arg_policy(),
            CalleeCallArgPolicy::ImportedLike,
        );
    }

    #[test]
    fn callee_resolution_policy_unresolved_callsite_does_not_inherit_other_site_policy() {
        let function_names = HashMap::from([(0x402000, "sym.local".to_string())]);
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let imported_site = CallsiteKey {
            block_addr: 0x10,
            op_index: 0,
        };
        let unresolved_site = CallsiteKey {
            block_addr: 0x20,
            op_index: 0,
        };
        let resolution =
            CalleeResolutionFacts::from_direct_call_targets([(imported_site, 0x401000)], &ctx);

        assert!(
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: Some(&resolution),
                    callsite: Some(unresolved_site),
                    prepared_identity: None,
                    prepared_direct_target: None,
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .is_none(),
            "unresolved callsites must not inherit policy from unrelated typed or rendered facts",
        );
    }

    #[test]
    fn callee_resolution_policy_preserves_modeled_callee_fact_through_callsite() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, modeled_callee_fact(0x401000, "sym.memcpy"))]);
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let callsite = CallsiteKey {
            block_addr: 0x10,
            op_index: 0,
        };
        let resolution =
            CalleeResolutionFacts::from_direct_call_targets([(callsite, 0x401000)], &ctx);

        let resolved =
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: Some(&resolution),
                    callsite: Some(callsite),
                    prepared_identity: None,
                    prepared_direct_target: None,
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .expect("callsite identity should resolve");

        assert_eq!(
            resolved.source,
            CalleeTargetResolutionSource::CallsiteResolution,
        );
        assert!(resolved.policy.modeled);
        assert_eq!(resolved.policy.modeled_addr, Some(0x401000));
        assert!(
            resolved
                .policy
                .sources
                .contains(&CalleeTargetPolicySource::CalleeFact)
        );
    }

    #[test]
    fn callee_resolution_policy_returns_none_without_any_identity_source() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        assert!(
            CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: None,
                    callsite: None,
                    prepared_identity: None,
                    prepared_direct_target: None,
                    direct_target_context: Some(&ctx),
                },
                callee_facts: &callee_facts,
            })
            .is_none()
        );
    }

    #[test]
    fn callee_identity_raw_or_normalized_name_matching_is_disjunctive() {
        let mut alias_only = minimal_identity_with_key(None);
        alias_only.aliases.insert("sym.alias_only".to_string());
        assert!(
            CalleeResolutionFacts::identity_matches_raw_or_normalized_name(
                &alias_only,
                "sym.alias_only",
                "",
            )
        );
        assert!(
            !CalleeResolutionFacts::identity_matches_raw_or_normalized_name(
                &alias_only,
                "sym.other",
                "",
            )
        );

        let mut raw_only = minimal_identity_with_key(None);
        raw_only.raw_name = Some("sym.raw_only".to_string());
        assert!(
            CalleeResolutionFacts::identity_matches_raw_or_normalized_name(
                &raw_only,
                "sym.raw_only",
                "",
            )
        );

        let mut display_only = minimal_identity_with_key(None);
        display_only.display_name = Some("sym.display_only".to_string());
        assert!(
            CalleeResolutionFacts::identity_matches_raw_or_normalized_name(
                &display_only,
                "sym.display_only",
                "",
            )
        );

        let normalized_only = minimal_identity_with_key(Some("printf"));
        assert!(
            CalleeResolutionFacts::identity_matches_raw_or_normalized_name(
                &normalized_only,
                "sym.imp.printf",
                "printf",
            )
        );
        assert!(
            !CalleeResolutionFacts::identity_matches_raw_or_normalized_name(
                &normalized_only,
                "sym.imp.printf",
                "",
            )
        );
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
    fn callee_resolution_facts_index_direct_call_targets_deterministically() {
        let function_names = HashMap::from([(0x401000, "sym.function_name".to_string())]);
        let symbols = HashMap::from([(0x401000, "sym.symbol_name".to_string())]);
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_signatures = HashMap::from([("printf".to_string(), non_variadic_signature(2))]);
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let callsite = CallsiteKey {
            block_addr: 0x402000,
            op_index: 4,
        };

        let facts = CalleeResolutionFacts::from_direct_call_targets([(callsite, 0x401000)], &ctx);

        assert_eq!(
            facts.key_for_callsite(callsite),
            Some(&CalleeIdentityKey::DirectAddress(0x401000))
        );
        let by_site = facts
            .identity_for_callsite(callsite)
            .expect("callsite identity should be indexed");
        assert_eq!(by_site.display_name.as_deref(), Some("sym.imp.printf"));
        assert_eq!(by_site.primary_key(), "printf");
        assert_eq!(by_site.non_variadic_known_arity(), Some(2));
        assert!(by_site.is_imported_name_hint());
        assert!(by_site.is_import_policy_authorized());

        let by_addr = facts
            .identity_for_direct_addr(0x401000)
            .expect("direct address identity should be indexed");
        assert_eq!(by_addr, by_site);
        assert_eq!(facts.identity_for_name("printf"), Some(by_site));
        assert_eq!(facts.identity_for_name("sym.imp.printf@plt"), Some(by_site));
        assert_eq!(facts.identity_for_name("sym.function_name"), Some(by_site));
    }

    #[test]
    fn callee_resolution_facts_index_named_known_signatures_deterministically() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::from([
            ("sym.imp.printf".to_string(), non_variadic_signature(1)),
            ("strcmp".to_string(), non_variadic_signature(2)),
        ]);
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let facts = CalleeResolutionFacts::from_context(&ctx);

        let printf = facts
            .identity_for_name("printf")
            .expect("known signature should be indexed as named identity");
        assert_eq!(printf.non_variadic_known_arity(), Some(1));
        assert!(printf.is_imported_name_hint());
        assert!(
            !printf.is_import_policy_authorized(),
            "known signature evidence alone must not authorize import policy"
        );
        let strcmp = facts
            .identity_for_name("sym.imp.strcmp@plt")
            .expect("normalized known signature alias should resolve");
        assert_eq!(strcmp.non_variadic_known_arity(), Some(2));
        assert_eq!(
            facts.by_key.keys().cloned().collect::<Vec<_>>(),
            vec![
                CalleeIdentityKey::Named("printf".to_string()),
                CalleeIdentityKey::Named("strcmp".to_string()),
            ]
        );
    }

    #[test]
    fn callee_resolution_facts_direct_identity_wins_over_named_signature_alias() {
        let function_names = HashMap::from([(0x401000, "sym.imp.printf@plt".to_string())]);
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::from([("printf".to_string(), non_variadic_signature(2))]);
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);

        let facts = CalleeResolutionFacts::from_context(&ctx);

        let by_addr = facts
            .identity_for_direct_addr(0x401000)
            .expect("function-name address should be indexed");
        assert_eq!(facts.identity_for_name("printf"), Some(by_addr));
        assert_eq!(by_addr.non_variadic_known_arity(), Some(2));
        assert!(
            facts
                .by_key
                .contains_key(&CalleeIdentityKey::Named("printf".to_string())),
            "named signature identity remains available, but aliases prefer direct evidence"
        );
    }

    #[test]
    fn callee_resolution_facts_reject_conflicting_callsite_owner() {
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_signatures = HashMap::new();
        let ctx =
            empty_identity_context(&function_names, &symbols, &callee_facts, &known_signatures);
        let callsite = CallsiteKey {
            block_addr: 0x402000,
            op_index: 4,
        };
        let mut facts = CalleeResolutionFacts::default();

        assert!(
            facts
                .insert_direct_callsite(callsite, 0x401000, &ctx)
                .is_some()
        );
        assert!(
            facts
                .insert_direct_callsite(callsite, 0x401000, &ctx)
                .is_some()
        );
        assert!(
            facts
                .insert_direct_callsite(callsite, 0x401010, &ctx)
                .is_none()
        );

        assert_eq!(
            facts.key_for_callsite(callsite),
            Some(&CalleeIdentityKey::DirectAddress(0x401000))
        );
        assert!(facts.identity_for_direct_addr(0x401010).is_none());
        assert_eq!(
            facts
                .identity_for_callsite(callsite)
                .map(CalleeIdentity::primary_key),
            Some("addr:401000".to_string())
        );
    }

    #[test]
    fn callee_resolution_facts_index_normalized_aliases() {
        let mut facts = CalleeResolutionFacts::default();
        let key = CalleeIdentityKey::DirectAddress(0x401000);

        facts.insert_name_alias("sym.imp.printf@plt", &key);

        assert_eq!(facts.by_name.get("printf"), Some(&key));
        assert_eq!(facts.by_name.get("sym.imp.printf@plt"), Some(&key));
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
        assert!(!imported_with_evidence.is_import_policy_authorized());

        let import_policy_authorized = imported_with_evidence.with_import_linkage_evidence();
        assert!(import_policy_authorized.is_imported_name_hint());
        assert!(import_policy_authorized.is_import_policy_authorized());

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

    fn pick_callee_class(tag: u8) -> CalleeClass {
        match tag % 6 {
            0 => CalleeClass::Internal,
            1 => CalleeClass::Imported,
            2 => CalleeClass::ExternalSymbol,
            3 => CalleeClass::RawAddress,
            4 => CalleeClass::Indirect,
            _ => CalleeClass::Unknown,
        }
    }

    fn pick_callee_linkage(tag: u8) -> CalleeLinkage {
        match tag % 3 {
            0 => CalleeLinkage::Unknown,
            1 => CalleeLinkage::Internal,
            _ => CalleeLinkage::Imported,
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

    #[kani::proof]
    fn callee_resolution_callsite_binding_is_fail_closed() {
        let addr_a = u64::from(kani::any::<u16>());
        let addr_b = u64::from(kani::any::<u16>()) + 0x1_0000;
        let key_a = CalleeIdentityKey::DirectAddress(addr_a);
        let key_a_repeat = CalleeIdentityKey::DirectAddress(addr_a);
        let key_b = CalleeIdentityKey::DirectAddress(addr_b);

        assert!(!CalleeResolutionFacts::callsite_binding_conflicts(
            None, &key_a,
        ));
        assert!(!CalleeResolutionFacts::callsite_binding_conflicts(
            Some(&key_a),
            &key_a_repeat,
        ));
        assert!(CalleeResolutionFacts::callsite_binding_conflicts(
            Some(&key_a),
            &key_b,
        ));
    }

    #[kani::proof]
    fn imported_name_hint_alone_does_not_authorize_import_policy() {
        let class = pick_callee_class(kani::any());
        let has_import_name_hint: bool = kani::any();
        let has_import_linkage: bool = kani::any();

        let authorized = import_policy_authorized_from_evidence(class, has_import_linkage);

        if !has_import_linkage {
            assert!(!authorized);
        }
        if authorized {
            assert_eq!(class, CalleeClass::Imported);
            assert!(has_import_linkage);
        }
        if has_import_name_hint && !has_import_linkage {
            assert!(!authorized);
        }
    }

    #[kani::proof]
    fn callee_linkage_is_exact_import_policy_authority() {
        let linkage = pick_callee_linkage(kani::any());

        assert_eq!(
            linkage.authorizes_import_policy(),
            linkage == CalleeLinkage::Imported,
        );
    }

    #[kani::proof]
    fn call_target_contract_arg_policy_requires_import_or_model_evidence() {
        let decision = CalleeTargetPolicyDecision {
            imported: kani::any(),
            modeled: kani::any(),
            modeled_addr: None,
            sources: BTreeSet::new(),
        };

        assert_eq!(
            decision.arg_policy(),
            if decision.imported || decision.modeled {
                CalleeCallArgPolicy::ImportedLike
            } else {
                CalleeCallArgPolicy::Standard
            },
        );
        if decision.arg_policy() == CalleeCallArgPolicy::ImportedLike {
            assert!(decision.imported || decision.modeled);
        }
    }

    #[kani::proof]
    fn modeled_policy_requires_explicit_callee_fact_evidence() {
        let evidence_count: usize = kani::any();
        let authorized = crate::facts::model_policy_authorized_from_evidence_count(evidence_count);

        assert_eq!(authorized, evidence_count > 0);
        if evidence_count == 0 {
            assert!(!authorized);
        }
    }

    #[kani::proof]
    fn call_target_contract_standard_policy_has_no_target_policy_sources() {
        let decision = CalleeTargetPolicyDecision {
            imported: false,
            modeled: false,
            modeled_addr: None,
            sources: BTreeSet::new(),
        };

        assert_eq!(decision.arg_policy(), CalleeCallArgPolicy::Standard);
        assert!(!decision.imported_or_modeled());
        assert!(decision.sources.is_empty());
    }

    #[kani::proof]
    fn callee_resolution_source_precedence_is_total() {
        let has_prepared_identity: bool = kani::any();
        let has_callsite_identity: bool = kani::any();
        let has_prepared_direct_target: bool = kani::any();

        let source = CalleeResolutionFacts::target_resolution_source_for_presence(
            has_prepared_identity,
            has_callsite_identity,
            has_prepared_direct_target,
        );

        if has_prepared_identity {
            assert_eq!(source, Some(CalleeTargetResolutionSource::PreparedIdentity));
        } else if has_callsite_identity {
            assert_eq!(
                source,
                Some(CalleeTargetResolutionSource::CallsiteResolution)
            );
        } else if has_prepared_direct_target {
            assert_eq!(
                source,
                Some(CalleeTargetResolutionSource::PreparedDirectTarget)
            );
        } else {
            assert_eq!(source, None);
        }
    }

    #[kani::proof]
    fn callee_resolution_source_returns_none_only_without_inputs() {
        let has_prepared_identity: bool = kani::any();
        let has_callsite_identity: bool = kani::any();
        let has_prepared_direct_target: bool = kani::any();

        let source = CalleeResolutionFacts::target_resolution_source_for_presence(
            has_prepared_identity,
            has_callsite_identity,
            has_prepared_direct_target,
        );

        assert_eq!(
            source.is_none(),
            !has_prepared_identity && !has_callsite_identity && !has_prepared_direct_target,
        );
    }

    #[kani::proof]
    fn callee_resolution_source_never_skips_higher_priority_inputs() {
        let has_prepared_identity: bool = kani::any();
        let has_callsite_identity: bool = kani::any();
        let has_prepared_direct_target: bool = kani::any();

        let source = CalleeResolutionFacts::target_resolution_source_for_presence(
            has_prepared_identity,
            has_callsite_identity,
            has_prepared_direct_target,
        );

        if source == Some(CalleeTargetResolutionSource::CallsiteResolution) {
            assert!(!has_prepared_identity);
            assert!(has_callsite_identity);
        }
        if source == Some(CalleeTargetResolutionSource::PreparedDirectTarget) {
            assert!(!has_prepared_identity);
            assert!(!has_callsite_identity);
            assert!(has_prepared_direct_target);
        }
    }

    #[kani::proof]
    fn callee_resolution_has_no_rendered_expression_source() {
        let has_prepared_identity: bool = kani::any();
        let has_callsite_identity: bool = kani::any();
        let has_prepared_direct_target: bool = kani::any();

        let source = CalleeResolutionFacts::target_resolution_source_for_presence(
            has_prepared_identity,
            has_callsite_identity,
            has_prepared_direct_target,
        );

        assert!(
            matches!(
                source,
                Some(CalleeTargetResolutionSource::PreparedIdentity)
                    | Some(CalleeTargetResolutionSource::CallsiteResolution)
                    | Some(CalleeTargetResolutionSource::PreparedDirectTarget)
                    | None
            ),
            "authoritative callee resolution must stay limited to typed sources",
        );
    }
}
