use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::artifact::{
    SemanticEvidence, SemanticEvidenceCoverage, SemanticEvidenceProvenance, SemanticEvidenceReason,
    SemanticEvidenceSoundness,
};
use super::facts::SymbolicReachabilityStatus;
use super::region::{
    NativeArtifactBody, NativeMemoryAccessKind, NativeRegionSummary, NativeWorkerSummary,
    NativeWorkerSummaryKind, RegionKey, SemanticRegion,
};

pub const SEMANTIC_CLAIM_SCHEMA_VERSION: u32 = 2;
pub const PROOF_COVERAGE_SCHEMA_VERSION: u32 = 3;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticClaimKind {
    Control,
    Memory,
    Value,
    TypeSeed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticClaimSource {
    Structural,
    Replay,
    TypedContext,
    InterprocSummary,
    Summary,
    NameHint,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticTypeSeedKind {
    Pointer,
    ReadOnlyPointer,
    OutParam,
    Size,
    Return,
    StructField,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ProofOwner {
    Radare2,
    R2ssa,
    R2sym,
    R2types,
    R2engine,
    R2dec,
    R2plugin,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ProofObligationKind {
    Control,
    Loop,
    Switch,
    Expression,
    MemoryAccess,
    StackSlot,
    FieldAccess,
    ArrayIndex,
    Callsite,
    ReturnValue,
    Signature,
    SummaryRole,
    SummaryRoute,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofObligation {
    pub kind: ProofObligationKind,
    pub owner: ProofOwner,
    pub anchor: u64,
    pub label: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofFailure {
    pub obligation: ProofObligation,
    pub reason: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RenderPermissionKind {
    CertifiedC,
    SummaryComment,
    Residual,
    Refuse,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RenderPermission {
    pub kind: RenderPermissionKind,
    pub owner: ProofOwner,
    pub reason: String,
}

impl RenderPermission {
    pub fn certified(owner: ProofOwner, reason: impl Into<String>) -> Self {
        Self {
            kind: RenderPermissionKind::CertifiedC,
            owner,
            reason: reason.into(),
        }
    }

    pub fn summary(owner: ProofOwner, reason: impl Into<String>) -> Self {
        Self {
            kind: RenderPermissionKind::SummaryComment,
            owner,
            reason: reason.into(),
        }
    }

    pub fn residual(owner: ProofOwner, reason: impl Into<String>) -> Self {
        Self {
            kind: RenderPermissionKind::Residual,
            owner,
            reason: reason.into(),
        }
    }

    pub fn refuse(owner: ProofOwner, reason: impl Into<String>) -> Self {
        Self {
            kind: RenderPermissionKind::Refuse,
            owner,
            reason: reason.into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedClaim<T> {
    pub value: T,
    pub permission: RenderPermission,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub obligations: Vec<ProofObligation>,
}

impl<T> CheckedClaim<T> {
    pub fn new(value: T, permission: RenderPermission) -> Self {
        Self {
            value,
            permission,
            obligations: Vec::new(),
        }
    }

    pub fn with_obligations<I>(mut self, obligations: I) -> Self
    where
        I: IntoIterator<Item = ProofObligation>,
    {
        self.obligations = obligations.into_iter().collect();
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofCoverage {
    pub schema_version: u32,
    pub certified_loops: usize,
    pub certified_switches: usize,
    pub certified_if_regions: usize,
    pub certified_expressions: usize,
    pub certified_memory_accesses: usize,
    pub certified_stack_slots: usize,
    pub certified_callsites: usize,
    pub certified_returns: usize,
    pub certified_field_accesses: usize,
    pub certified_array_indexes: usize,
    pub certified_out_params: usize,
    pub certified_signatures: usize,
    pub certified_summary_roles: usize,
    /// Semantic summary claims that can explain a summary route. This is not
    /// proof that native control/dataflow was reconstructed as certified C.
    #[serde(alias = "summary_comments")]
    pub semantic_summary_comments: usize,
    /// Honest semantic residuals/refusals emitted by analysis. This is not a
    /// certified render/writeback fact.
    #[serde(alias = "residuals")]
    pub semantic_residuals: usize,
    pub refusals: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub failures: Vec<ProofFailure>,
}

impl Default for ProofCoverage {
    fn default() -> Self {
        Self {
            schema_version: PROOF_COVERAGE_SCHEMA_VERSION,
            certified_loops: 0,
            certified_switches: 0,
            certified_if_regions: 0,
            certified_expressions: 0,
            certified_memory_accesses: 0,
            certified_stack_slots: 0,
            certified_callsites: 0,
            certified_returns: 0,
            certified_field_accesses: 0,
            certified_array_indexes: 0,
            certified_out_params: 0,
            certified_signatures: 0,
            certified_summary_roles: 0,
            semantic_summary_comments: 0,
            semantic_residuals: 0,
            refusals: 0,
            failures: Vec::new(),
        }
    }
}

impl ProofCoverage {
    pub fn from_prepared_certificates(certificates: &r2ssa::PreparedFunctionCertificates) -> Self {
        let mut failures = Vec::new();
        for failure in &certificates.failures {
            failures.push(ProofFailure {
                obligation: ProofObligation {
                    kind: proof_obligation_kind_from_label(failure.obligation),
                    owner: proof_owner_from_label(failure.owner),
                    anchor: failure.anchor,
                    label: failure.obligation.to_string(),
                },
                reason: failure.reason.clone(),
            });
        }
        Self {
            certified_loops: certificates.loops.len(),
            certified_switches: certificates.switches.len(),
            certified_if_regions: certificates.if_regions.len(),
            certified_expressions: certificates.expressions.len(),
            certified_memory_accesses: certificates.memory_accesses.len(),
            certified_stack_slots: certificates.stack_slots.len(),
            certified_callsites: certificates.callsites.len(),
            certified_returns: certificates.returns.len(),
            failures,
            ..Self::default()
        }
    }

    pub fn from_semantic_claims(claims: &SemanticClaimSummary) -> Self {
        let certified_summary_roles = claims.summary_role_certificates.len();
        Self {
            semantic_summary_comments: claims.renderable_summary_claims,
            semantic_residuals: claims.residual_claims,
            certified_summary_roles,
            failures: claims
                .claims
                .iter()
                .filter(|claim| claim.is_name_hint_only())
                .map(|claim| ProofFailure {
                    obligation: ProofObligation {
                        kind: match claim.kind {
                            SemanticClaimKind::Control => ProofObligationKind::Control,
                            SemanticClaimKind::Memory => ProofObligationKind::MemoryAccess,
                            SemanticClaimKind::Value => ProofObligationKind::Expression,
                            SemanticClaimKind::TypeSeed => ProofObligationKind::SummaryRole,
                        },
                        owner: ProofOwner::R2sym,
                        anchor: claim.anchor,
                        label: claim.label.clone(),
                    },
                    reason: "name hint is weak evidence and cannot certify rendering".to_string(),
                })
                .collect(),
            ..Self::default()
        }
    }

    pub fn merge(mut self, other: Self) -> Self {
        self.schema_version = self.schema_version.max(other.schema_version);
        self.certified_loops += other.certified_loops;
        self.certified_switches += other.certified_switches;
        self.certified_if_regions += other.certified_if_regions;
        self.certified_expressions += other.certified_expressions;
        self.certified_memory_accesses += other.certified_memory_accesses;
        self.certified_stack_slots += other.certified_stack_slots;
        self.certified_callsites += other.certified_callsites;
        self.certified_returns += other.certified_returns;
        self.certified_field_accesses += other.certified_field_accesses;
        self.certified_array_indexes += other.certified_array_indexes;
        self.certified_out_params += other.certified_out_params;
        self.certified_signatures += other.certified_signatures;
        self.certified_summary_roles += other.certified_summary_roles;
        self.semantic_summary_comments += other.semantic_summary_comments;
        self.semantic_residuals += other.semantic_residuals;
        self.refusals += other.refusals;
        self.failures.extend(other.failures);
        self
    }

    pub fn has_fake_semantics_risk(&self) -> bool {
        !self.failures.is_empty() || self.refusals > 0
    }

    pub fn standard_control_render_permission(
        &self,
        cfg_summary: &r2ssa::CFGRiskSummary,
        prepared_available: bool,
    ) -> RenderPermission {
        let cfg_loop_obligations = if cfg_summary.loop_count > 0 {
            cfg_summary.loop_count
        } else if cfg_summary.back_edge_count > 0 {
            1
        } else {
            0
        };
        let cfg_switch_obligations = cfg_summary.switch_block_count;
        if cfg_loop_obligations == 0 && cfg_switch_obligations == 0 {
            return RenderPermission::certified(
                ProofOwner::R2engine,
                "standard route has no structured-control proof obligations",
            );
        }
        if !prepared_available {
            return RenderPermission::residual(
                ProofOwner::R2engine,
                "missing prepared SSA certificates for structured control",
            );
        }

        let mut reasons = Vec::new();
        if cfg_loop_obligations > 0 && self.certified_loops < cfg_loop_obligations {
            reasons.push(format!(
                "loop CFG requires {} LoopCertificate(s), found {}",
                cfg_loop_obligations, self.certified_loops
            ));
        }
        if cfg_switch_obligations > 0 && self.certified_switches < cfg_switch_obligations {
            reasons.push(format!(
                "switch CFG requires {} SwitchCertificate(s), found {}",
                cfg_switch_obligations, self.certified_switches
            ));
        }

        if reasons.is_empty() {
            RenderPermission::certified(
                ProofOwner::R2engine,
                "standard route structured control is certificate-backed",
            )
        } else {
            RenderPermission::residual(
                ProofOwner::R2engine,
                format!("uncertified structured control: {}", reasons.join(", ")),
            )
        }
    }
}

fn proof_owner_from_label(owner: &str) -> ProofOwner {
    match owner {
        "radare2" => ProofOwner::Radare2,
        "r2ssa" => ProofOwner::R2ssa,
        "r2sym" => ProofOwner::R2sym,
        "r2types" => ProofOwner::R2types,
        "r2engine" => ProofOwner::R2engine,
        "r2dec" => ProofOwner::R2dec,
        "r2plugin" => ProofOwner::R2plugin,
        _ => ProofOwner::R2engine,
    }
}

fn proof_obligation_kind_from_label(kind: &str) -> ProofObligationKind {
    match kind {
        "control" => ProofObligationKind::Control,
        "loop" => ProofObligationKind::Loop,
        "switch" => ProofObligationKind::Switch,
        "expression" => ProofObligationKind::Expression,
        "memory_access" => ProofObligationKind::MemoryAccess,
        "stack_slot" => ProofObligationKind::StackSlot,
        "field_access" => ProofObligationKind::FieldAccess,
        "array_index" => ProofObligationKind::ArrayIndex,
        "callsite" => ProofObligationKind::Callsite,
        "return_value" => ProofObligationKind::ReturnValue,
        "signature" => ProofObligationKind::Signature,
        "summary_role" => ProofObligationKind::SummaryRole,
        "summary_route" => ProofObligationKind::SummaryRoute,
        _ => ProofObligationKind::Control,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticClaim {
    pub stable_id: u64,
    pub kind: SemanticClaimKind,
    pub source: SemanticClaimSource,
    pub evidence: SemanticEvidence,
    pub anchor: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arg_index: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub width: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary_kind: Option<NativeWorkerSummaryKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_seed: Option<SemanticTypeSeedKind>,
    pub label: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryRoleCertificate {
    pub stable_id: u64,
    pub anchor: u64,
    pub summary_kind: NativeWorkerSummaryKind,
    pub source: SemanticClaimSource,
    pub label: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SummaryRouteCertificateKind {
    Standard,
    DirectSummary,
    PreferFull,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryRouteCertificate {
    pub stable_id: u64,
    pub anchor: u64,
    pub route_kind: SummaryRouteCertificateKind,
    pub source: SemanticClaimSource,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalized_name: Option<String>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub route_evidence_kinds: BTreeSet<NativeWorkerSummaryKind>,
    pub evidence: SemanticEvidence,
    pub label: String,
}

impl SummaryRouteCertificate {
    pub fn new(
        anchor: u64,
        route_kind: SummaryRouteCertificateKind,
        source: SemanticClaimSource,
        normalized_name: Option<String>,
        route_evidence_kinds: BTreeSet<NativeWorkerSummaryKind>,
        evidence: SemanticEvidence,
        label: impl Into<String>,
    ) -> Self {
        let label = label.into();
        let name_hash = normalized_name
            .as_deref()
            .map(stable_text_hash)
            .unwrap_or_default();
        let route_evidence_hash = stable_summary_kind_set_hash(&route_evidence_kinds);
        Self {
            stable_id: stable_claim_id(
                0x60 + route_kind as u64,
                anchor,
                name_hash,
                route_evidence_hash,
            ),
            anchor,
            route_kind,
            source,
            normalized_name,
            route_evidence_kinds,
            evidence,
            label,
        }
    }
}

fn stable_summary_kind_set_hash(kinds: &BTreeSet<NativeWorkerSummaryKind>) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    for kind in kinds {
        hash ^= *kind as u64 + 1;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

impl SemanticClaim {
    pub fn allows_type_projection(&self) -> bool {
        !matches!(self.source, SemanticClaimSource::NameHint)
            && self.evidence.allows_narrowing()
            && !self
                .evidence
                .reasons
                .contains(&SemanticEvidenceReason::NameHint)
    }

    pub fn allows_structured_rendering(&self) -> bool {
        !matches!(self.source, SemanticClaimSource::NameHint)
            && self.evidence.allows_guarded_structuring()
            && !self
                .evidence
                .reasons
                .contains(&SemanticEvidenceReason::NameHint)
    }

    pub fn is_name_hint_only(&self) -> bool {
        matches!(self.source, SemanticClaimSource::NameHint)
            || self
                .evidence
                .reasons
                .contains(&SemanticEvidenceReason::NameHint)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticClaimSummary {
    pub schema_version: u32,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub claims: Vec<SemanticClaim>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub summary_role_certificates: Vec<SummaryRoleCertificate>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub pointer_param_indices: BTreeSet<usize>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub out_param_indices: BTreeSet<usize>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub size_param_indices: BTreeSet<usize>,
    pub structural_control_claims: usize,
    pub structural_memory_claims: usize,
    pub structural_value_claims: usize,
    pub renderable_summary_claims: usize,
    pub name_hint_claims: usize,
    pub residual_claims: usize,
}

impl SemanticClaimSummary {
    pub fn empty() -> Self {
        Self {
            schema_version: SEMANTIC_CLAIM_SCHEMA_VERSION,
            ..Self::default()
        }
    }

    pub fn from_native_body(body: &NativeArtifactBody) -> Self {
        let mut summary = Self::empty();
        for (key, region) in &body.regions {
            summary.collect_region(key, region);
        }
        for region_summary in &body.summary.region_summaries {
            summary.collect_native_region_summary(region_summary);
        }
        for worker_summary in &body.summary.worker_summaries {
            summary.collect_native_worker_summary(worker_summary);
        }
        summary.claims.sort_by_key(|claim| {
            (
                claim.kind,
                claim.anchor,
                claim.target,
                claim.arg_index,
                claim.summary_kind,
                claim.stable_id,
            )
        });
        summary
            .summary_role_certificates
            .sort_by_key(|cert| (cert.anchor, cert.summary_kind, cert.source, cert.stable_id));
        summary
    }

    pub fn has_renderable_non_name_claim(&self) -> bool {
        self.renderable_summary_claims > 0
            || self.claims.iter().any(|claim| {
                claim.allows_structured_rendering()
                    && matches!(
                        claim.kind,
                        SemanticClaimKind::Control
                            | SemanticClaimKind::Memory
                            | SemanticClaimKind::Value
                    )
            })
    }

    pub fn has_type_projection_claims(&self) -> bool {
        !self.pointer_param_indices.is_empty()
            || !self.out_param_indices.is_empty()
            || !self.size_param_indices.is_empty()
            || self.claims.iter().any(|claim| {
                claim.kind == SemanticClaimKind::TypeSeed && claim.allows_type_projection()
            })
    }

    pub fn arg_has_pointer_evidence(&self, index: usize) -> bool {
        self.pointer_param_indices.contains(&index)
            || self.claims.iter().any(|claim| {
                claim.arg_index == Some(index)
                    && matches!(
                        claim.type_seed,
                        Some(
                            SemanticTypeSeedKind::Pointer
                                | SemanticTypeSeedKind::ReadOnlyPointer
                                | SemanticTypeSeedKind::OutParam
                                | SemanticTypeSeedKind::StructField
                        )
                    )
                    && claim.allows_type_projection()
            })
    }

    pub fn arg_has_out_param_evidence(&self, index: usize) -> bool {
        self.out_param_indices.contains(&index)
            || self.claims.iter().any(|claim| {
                claim.arg_index == Some(index)
                    && claim.type_seed == Some(SemanticTypeSeedKind::OutParam)
                    && claim.allows_type_projection()
            })
    }

    fn collect_region(&mut self, key: &RegionKey, region: &SemanticRegion) {
        for fact in &region.control {
            if !fact.evidence.is_usable() {
                self.residual_claims += 1;
                continue;
            }
            let source = claim_source_for_evidence(&fact.evidence, true);
            if fact.evidence.allows_narrowing()
                && matches!(fact.value.status, SymbolicReachabilityStatus::Reachable)
            {
                self.push_claim(SemanticClaim {
                    stable_id: stable_claim_id(
                        0x10,
                        region.anchor,
                        fact.value.target,
                        fact.value.branch_truth.map(u64::from).unwrap_or(2),
                    ),
                    kind: SemanticClaimKind::Control,
                    source,
                    evidence: fact.evidence.clone(),
                    anchor: key.anchor_block,
                    target: Some(fact.value.target),
                    arg_index: None,
                    width: None,
                    summary_kind: None,
                    type_seed: None,
                    label: "reachable control target".to_string(),
                });
            }
        }
        for fact in &region.memory {
            let evidence = fact.value.term.evidence().combined_with(&fact.evidence);
            if !evidence.is_usable() {
                self.residual_claims += 1;
                continue;
            }
            if let Some(index) = backward_memory_arg_index(&fact.value.term.region) {
                self.push_type_seed(
                    key.anchor_block,
                    index,
                    Some(fact.value.term.size),
                    SemanticTypeSeedKind::ReadOnlyPointer,
                    evidence.clone(),
                    claim_source_for_evidence(&evidence, true),
                );
            }
        }
    }

    fn collect_native_worker_summary(&mut self, summary: &NativeWorkerSummary) {
        let source = claim_source_for_evidence(&summary.evidence, false);
        if summary.is_primary_render_summary() {
            self.push_claim(SemanticClaim {
                stable_id: summary.summary_role_certificate_id(),
                kind: SemanticClaimKind::Value,
                source,
                evidence: summary.evidence.clone(),
                anchor: summary.anchor,
                target: None,
                arg_index: None,
                width: None,
                summary_kind: Some(summary.kind),
                type_seed: None,
                label: summary.kind.canonical_role_name().to_string(),
            });
        }
        if !summary.is_generic_memory_summary() {
            for location in [
                summary.dst.as_ref(),
                summary.src.as_ref(),
                summary.memory.as_ref(),
                summary.atomic.as_ref().map(|effect| &effect.location),
            ]
            .into_iter()
            .flatten()
            {
                if let Some(index) = summary_location_arg_index(location) {
                    self.push_type_seed(
                        summary.anchor,
                        index,
                        location.range.and_then(|range| range.width),
                        SemanticTypeSeedKind::Pointer,
                        summary.evidence.clone(),
                        source,
                    );
                }
            }
            for index in summary.out_param_indices() {
                self.push_type_seed(
                    summary.anchor,
                    index,
                    None,
                    SemanticTypeSeedKind::OutParam,
                    summary.evidence.clone(),
                    source,
                );
            }
            if let Some(lifetime) = summary.lifetime {
                self.push_type_seed(
                    summary.anchor,
                    lifetime.arg,
                    None,
                    SemanticTypeSeedKind::Pointer,
                    summary.evidence.clone(),
                    source,
                );
            }
            if let Some(sync) = summary.sync {
                self.push_type_seed(
                    summary.anchor,
                    sync.arg,
                    None,
                    SemanticTypeSeedKind::Pointer,
                    summary.evidence.clone(),
                    source,
                );
            }
        }
        if let Some(r2ssa::SummaryTransferLength::Arg(index)) = summary.len {
            self.push_type_seed(
                summary.anchor,
                index,
                None,
                SemanticTypeSeedKind::Size,
                summary.evidence.clone(),
                source,
            );
        }
        if let Some(index) = summary
            .loop_summary
            .as_ref()
            .and_then(|loop_summary| loop_summary.length_arg)
        {
            self.push_type_seed(
                summary.anchor,
                index,
                None,
                SemanticTypeSeedKind::Size,
                summary.evidence.clone(),
                source,
            );
        }
    }

    fn collect_native_region_summary(&mut self, summary: &NativeRegionSummary) {
        let source = claim_source_for_evidence(&summary.evidence, false);
        if summary.is_primary_render_summary() {
            self.push_claim(SemanticClaim {
                stable_id: summary.summary_role_certificate_id(),
                kind: SemanticClaimKind::Value,
                source,
                evidence: summary.evidence.clone(),
                anchor: summary.anchor,
                target: None,
                arg_index: None,
                width: None,
                summary_kind: Some(summary.kind),
                type_seed: None,
                label: summary.kind.canonical_role_name().to_string(),
            });
        }
        for access in &summary.memory_accesses {
            if !summary.is_generic_memory_summary() {
                let seed = match access.kind {
                    NativeMemoryAccessKind::Write
                    | NativeMemoryAccessKind::Transfer
                    | NativeMemoryAccessKind::Atomic => SemanticTypeSeedKind::OutParam,
                    NativeMemoryAccessKind::Read => SemanticTypeSeedKind::ReadOnlyPointer,
                    _ => SemanticTypeSeedKind::Pointer,
                };
                for location in [
                    access.location.as_ref(),
                    access.dst.as_ref(),
                    access.src.as_ref(),
                ]
                .into_iter()
                .flatten()
                {
                    if let Some(index) = summary_location_arg_index(location) {
                        self.push_type_seed(
                            summary.anchor,
                            index,
                            access
                                .width
                                .or_else(|| location.range.and_then(|range| range.width)),
                            seed,
                            summary.evidence.clone(),
                            source,
                        );
                    }
                }
            }
            if let Some(r2ssa::SummaryTransferLength::Arg(index)) = access.len {
                self.push_type_seed(
                    summary.anchor,
                    index,
                    None,
                    SemanticTypeSeedKind::Size,
                    summary.evidence.clone(),
                    source,
                );
            }
        }
        if let Some(index) = summary
            .loop_summary
            .as_ref()
            .and_then(|loop_summary| loop_summary.length_arg)
        {
            self.push_type_seed(
                summary.anchor,
                index,
                None,
                SemanticTypeSeedKind::Size,
                summary.evidence.clone(),
                source,
            );
        }
    }

    fn push_type_seed(
        &mut self,
        anchor: u64,
        index: usize,
        width: Option<u32>,
        seed: SemanticTypeSeedKind,
        evidence: SemanticEvidence,
        source: SemanticClaimSource,
    ) {
        self.push_claim(SemanticClaim {
            stable_id: stable_claim_id(
                0x40 + seed as u64,
                anchor,
                index as u64,
                width.unwrap_or(0) as u64,
            ),
            kind: SemanticClaimKind::TypeSeed,
            source,
            evidence,
            anchor,
            target: None,
            arg_index: Some(index),
            width,
            summary_kind: None,
            type_seed: Some(seed),
            label: type_seed_label(seed).to_string(),
        });
    }

    fn push_claim(&mut self, claim: SemanticClaim) {
        if claim.is_name_hint_only() {
            self.name_hint_claims += 1;
        }
        if claim.kind == SemanticClaimKind::Value
            && claim.allows_structured_rendering()
            && let Some(summary_kind) = claim.summary_kind
        {
            self.summary_role_certificates.push(SummaryRoleCertificate {
                stable_id: claim.stable_id,
                anchor: claim.anchor,
                summary_kind,
                source: claim.source,
                label: claim.label.clone(),
            });
        }
        if !claim.evidence.is_usable() {
            self.residual_claims += 1;
        }
        if claim.allows_structured_rendering() {
            match claim.kind {
                SemanticClaimKind::Control => self.structural_control_claims += 1,
                SemanticClaimKind::Memory => self.structural_memory_claims += 1,
                SemanticClaimKind::Value => {
                    self.structural_value_claims += 1;
                    if claim.summary_kind.is_some() {
                        self.renderable_summary_claims += 1;
                    }
                }
                SemanticClaimKind::TypeSeed => {}
            }
        }
        if claim.allows_type_projection()
            && let Some(index) = claim.arg_index
        {
            match claim.type_seed {
                Some(
                    SemanticTypeSeedKind::Pointer
                    | SemanticTypeSeedKind::ReadOnlyPointer
                    | SemanticTypeSeedKind::StructField,
                ) => {
                    self.pointer_param_indices.insert(index);
                }
                Some(SemanticTypeSeedKind::OutParam) => {
                    self.pointer_param_indices.insert(index);
                    self.out_param_indices.insert(index);
                }
                Some(SemanticTypeSeedKind::Size) => {
                    self.size_param_indices.insert(index);
                }
                Some(SemanticTypeSeedKind::Return) | None => {}
            }
        }
        self.claims.push(claim);
    }
}

fn type_seed_label(seed: SemanticTypeSeedKind) -> &'static str {
    match seed {
        SemanticTypeSeedKind::Pointer => "semantic pointer seed",
        SemanticTypeSeedKind::ReadOnlyPointer => "semantic read-only pointer seed",
        SemanticTypeSeedKind::OutParam => "semantic out-param seed",
        SemanticTypeSeedKind::Size => "semantic size seed",
        SemanticTypeSeedKind::Return => "semantic return seed",
        SemanticTypeSeedKind::StructField => "semantic struct-field seed",
    }
}

fn claim_source_for_evidence(
    evidence: &SemanticEvidence,
    structural_default: bool,
) -> SemanticClaimSource {
    if evidence.reasons.contains(&SemanticEvidenceReason::NameHint) {
        return SemanticClaimSource::NameHint;
    }
    if matches!(
        evidence.soundness,
        SemanticEvidenceSoundness::Proven | SemanticEvidenceSoundness::UnderApprox
    ) && matches!(
        evidence.coverage,
        SemanticEvidenceCoverage::Full | SemanticEvidenceCoverage::Bounded
    ) && matches!(
        evidence.provenance,
        SemanticEvidenceProvenance::Stable | SemanticEvidenceProvenance::Normalized
    ) {
        return SemanticClaimSource::Structural;
    }
    if structural_default && evidence.allows_narrowing() {
        SemanticClaimSource::Structural
    } else {
        SemanticClaimSource::Summary
    }
}

fn summary_location_arg_index(location: &r2ssa::SummaryMemoryLocation) -> Option<usize> {
    match location.region {
        r2ssa::SummaryMemoryRegion::Arg { index } => Some(index),
        _ => None,
    }
}

fn backward_memory_arg_index(region: &crate::backward::BackwardMemoryRegion) -> Option<usize> {
    match region {
        crate::backward::BackwardMemoryRegion::Argument { index } => Some(*index),
        crate::backward::BackwardMemoryRegion::Region(_) => None,
    }
}

fn stable_claim_id(tag: u64, a: u64, b: u64, c: u64) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    for value in [tag, a, b, c] {
        for byte in value.to_le_bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    hash
}

fn stable_text_hash(text: &str) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    for byte in text.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::semantics::{NativeFunctionSummary, SliceClass};

    fn arg_location(index: usize) -> r2ssa::SummaryMemoryLocation {
        r2ssa::SummaryMemoryLocation {
            region: r2ssa::SummaryMemoryRegion::Arg { index },
            range: Some(r2ssa::SummaryMemoryRange {
                offset_lo: 0,
                offset_hi: 0,
                width: Some(1),
            }),
        }
    }

    fn native_body(worker: NativeWorkerSummary) -> NativeArtifactBody {
        NativeArtifactBody {
            summary: NativeFunctionSummary {
                slice_class: SliceClass::Worker,
                role_identity: None,
                closure_functions: 0,
                helper_functions: 0,
                derived_summaries: 0,
                derived_diagnostics: Default::default(),
                region_summaries: Vec::new(),
                worker_summaries: vec![worker],
            },
            regions: BTreeMap::new(),
        }
    }

    #[test]
    fn claim_summary_projects_non_name_worker_evidence() {
        let worker = NativeWorkerSummary {
            anchor: 0x1000,
            kind: NativeWorkerSummaryKind::HashFold,
            dst: None,
            src: None,
            memory: Some(arg_location(0)),
            len: Some(r2ssa::SummaryTransferLength::Arg(1)),
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: None,
            evidence: SemanticEvidence::likely(SemanticEvidenceReason::SummaryBudget)
                .with_coverage(SemanticEvidenceCoverage::Bounded),
        };
        let claims = SemanticClaimSummary::from_native_body(&native_body(worker.clone()));

        assert!(claims.has_renderable_non_name_claim());
        assert_eq!(claims.summary_role_certificates.len(), 1);
        assert_eq!(
            claims.summary_role_certificates[0].summary_kind,
            NativeWorkerSummaryKind::HashFold
        );
        assert_eq!(
            claims.summary_role_certificates[0].stable_id,
            worker.summary_role_certificate_id()
        );
        assert!(claims.arg_has_pointer_evidence(0));
        assert!(claims.size_param_indices.contains(&1));
        assert_eq!(claims.name_hint_claims, 0);

        let coverage = ProofCoverage::from_semantic_claims(&claims);
        assert_eq!(coverage.certified_summary_roles, 1);
    }

    #[test]
    fn proof_coverage_does_not_certify_out_params_from_semantic_claims() {
        let worker = NativeWorkerSummary {
            anchor: 0x1000,
            kind: NativeWorkerSummaryKind::NumericTransform,
            dst: Some(arg_location(0)),
            src: None,
            memory: None,
            len: None,
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: None,
            evidence: SemanticEvidence::likely(SemanticEvidenceReason::SummaryBudget)
                .with_coverage(SemanticEvidenceCoverage::Bounded),
        };
        let claims = SemanticClaimSummary::from_native_body(&native_body(worker));

        assert!(claims.arg_has_out_param_evidence(0));
        let coverage = ProofCoverage::from_semantic_claims(&claims);
        assert_eq!(
            coverage.certified_out_params, 0,
            "r2types::FunctionTypeFacts owns certified out-param proof"
        );
    }

    #[test]
    fn proof_coverage_does_not_certify_field_accesses_from_semantic_claims() {
        let mut claims = SemanticClaimSummary::empty();
        claims.claims.push(SemanticClaim {
            stable_id: 0x44,
            kind: SemanticClaimKind::TypeSeed,
            source: SemanticClaimSource::Structural,
            evidence: SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage)
                .with_coverage(SemanticEvidenceCoverage::Bounded),
            anchor: 0x1000,
            target: None,
            arg_index: Some(0),
            width: Some(8),
            summary_kind: None,
            type_seed: Some(SemanticTypeSeedKind::StructField),
            label: "semantic struct-field seed".to_string(),
        });

        let coverage = ProofCoverage::from_semantic_claims(&claims);
        assert_eq!(
            coverage.certified_field_accesses, 0,
            "r2types::FunctionTypeFacts owns certified field/layout proof"
        );
    }

    #[test]
    fn proof_coverage_keeps_semantic_report_counters_out_of_certified_counts() {
        let mut claims = SemanticClaimSummary::empty();
        claims.renderable_summary_claims = 2;
        claims.residual_claims = 3;

        let coverage = ProofCoverage::from_semantic_claims(&claims);

        assert_eq!(coverage.semantic_summary_comments, 2);
        assert_eq!(coverage.semantic_residuals, 3);
        assert_eq!(coverage.certified_loops, 0);
        assert_eq!(coverage.certified_expressions, 0);
        assert_eq!(coverage.certified_memory_accesses, 0);
        assert_eq!(coverage.certified_summary_roles, 0);
    }

    #[test]
    fn claim_summary_keeps_name_hints_weak() {
        let worker = NativeWorkerSummary {
            anchor: 0x1000,
            kind: NativeWorkerSummaryKind::HashFold,
            dst: None,
            src: None,
            memory: Some(arg_location(0)),
            len: Some(r2ssa::SummaryTransferLength::Arg(1)),
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: None,
            evidence: SemanticEvidence::heuristic(SemanticEvidenceReason::NameHint)
                .with_coverage(SemanticEvidenceCoverage::Bounded),
        };
        let claims = SemanticClaimSummary::from_native_body(&native_body(worker));

        assert!(!claims.has_renderable_non_name_claim());
        assert!(claims.summary_role_certificates.is_empty());
        assert!(!claims.arg_has_pointer_evidence(0));
        assert!(claims.name_hint_claims > 0);

        let coverage = ProofCoverage::from_semantic_claims(&claims);
        assert_eq!(coverage.certified_summary_roles, 0);
    }

    #[test]
    fn claim_summary_uses_current_schema_version() {
        let claims = SemanticClaimSummary::empty();
        assert_eq!(claims.schema_version, SEMANTIC_CLAIM_SCHEMA_VERSION);
    }

    #[test]
    fn proof_coverage_uses_current_schema_version() {
        assert_eq!(
            ProofCoverage::default().schema_version,
            PROOF_COVERAGE_SCHEMA_VERSION
        );
    }

    #[test]
    fn proof_coverage_refuses_standard_control_without_prepared_certificates() {
        let permission = ProofCoverage::default().standard_control_render_permission(
            &r2ssa::CFGRiskSummary {
                block_count: 3,
                loop_count: 1,
                back_edge_count: 1,
                switch_block_count: 0,
                max_switch_cases: 0,
            },
            false,
        );

        assert_eq!(permission.kind, RenderPermissionKind::Residual);
        assert!(
            permission
                .reason
                .contains("missing prepared SSA certificates")
        );
    }

    #[test]
    fn proof_coverage_certifies_standard_control_when_counts_cover_cfg() {
        let permission = ProofCoverage {
            certified_loops: 1,
            certified_switches: 1,
            ..ProofCoverage::default()
        }
        .standard_control_render_permission(
            &r2ssa::CFGRiskSummary {
                block_count: 4,
                loop_count: 1,
                back_edge_count: 1,
                switch_block_count: 1,
                max_switch_cases: 2,
            },
            true,
        );

        assert_eq!(permission.kind, RenderPermissionKind::CertifiedC);
    }
}
