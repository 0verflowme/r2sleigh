use std::sync::Arc;

use r2ssa::{InterprocFunctionId, PreparedInterprocSummarySet, SsaArtifact};
use serde::{Deserialize, Serialize};

use super::claims::SemanticClaimSummary;
use super::plan::{
    ArtifactBuildPlan, DecompilePlan, QueryPlan, TargetQueryPlan, TargetQueryRoutePlan, TypePlan,
    derive_artifact_build_plan, derive_decompile_plan, derive_query_plan, derive_target_query_plan,
    derive_target_query_route_plan, derive_type_plan,
};
use super::region::{
    ArtifactGranularity, ExecutionModel, NativeArtifactBody, RefinementStage,
    SemanticArtifactDiagnostics, SemanticRegion, SemanticTargetConditionSource, VmArtifactBody,
};
use super::vm::InterpreterKind;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SliceClass {
    Wrapper,
    Worker,
    InterpreterSwitch,
    InterpreterIndirect,
    GenericLarge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ResidualReason {
    MissingArch,
    LargeCfg,
    InterpreterRequiresStepSummary,
}

pub const SEMANTIC_ARTIFACT_SCHEMA_VERSION: u32 = 14;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticConfidence {
    Exact,
    Likely,
    Heuristic,
    Residual,
}

impl SemanticConfidence {
    pub fn is_reliable(self) -> bool {
        matches!(self, Self::Exact | Self::Likely)
    }

    pub fn is_usable(self) -> bool {
        !matches!(self, Self::Residual)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemanticEvidenceSoundness {
    Proven,
    UnderApprox,
    OverApprox,
    Ranked,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemanticEvidenceCoverage {
    Full,
    Partial,
    Bounded,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticEvidenceProvenance {
    Stable,
    Normalized,
    Ranked,
    Unstable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticEvidenceAmbiguity {
    Single,
    Bounded,
    Ranked,
    Multiple,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SemanticEvidenceReason {
    LargeCfg,
    SummaryBudget,
    NameHint,
    AliasAmbiguity,
    ConflictingTargetSources,
    ReplayOverlap,
    HeapIdentityWeak,
    GuardOpaque,
    ValueOpaque,
    TruncatedTransfer,
    DerivedFromRanking,
    PartialPathCoverage,
    ResidualSearchRequired,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SemanticEvidence {
    pub tier: SemanticConfidence,
    pub soundness: SemanticEvidenceSoundness,
    pub coverage: SemanticEvidenceCoverage,
    pub provenance: SemanticEvidenceProvenance,
    pub ambiguity: SemanticEvidenceAmbiguity,
    pub budget_limited: bool,
    pub reasons: Vec<SemanticEvidenceReason>,
}

impl Default for SemanticEvidence {
    fn default() -> Self {
        Self::exact()
    }
}

impl SemanticEvidence {
    pub fn is_default_exact(&self) -> bool {
        *self == Self::exact()
    }

    pub fn exact() -> Self {
        Self {
            tier: SemanticConfidence::Exact,
            soundness: SemanticEvidenceSoundness::Proven,
            coverage: SemanticEvidenceCoverage::Full,
            provenance: SemanticEvidenceProvenance::Stable,
            ambiguity: SemanticEvidenceAmbiguity::Single,
            budget_limited: false,
            reasons: Vec::new(),
        }
    }

    pub fn likely(reason: SemanticEvidenceReason) -> Self {
        Self {
            tier: SemanticConfidence::Likely,
            soundness: SemanticEvidenceSoundness::OverApprox,
            coverage: SemanticEvidenceCoverage::Full,
            provenance: SemanticEvidenceProvenance::Normalized,
            ambiguity: SemanticEvidenceAmbiguity::Single,
            budget_limited: false,
            reasons: vec![reason],
        }
    }

    pub fn heuristic(reason: SemanticEvidenceReason) -> Self {
        Self {
            tier: SemanticConfidence::Heuristic,
            soundness: SemanticEvidenceSoundness::Ranked,
            coverage: SemanticEvidenceCoverage::Partial,
            provenance: SemanticEvidenceProvenance::Ranked,
            ambiguity: SemanticEvidenceAmbiguity::Ranked,
            budget_limited: false,
            reasons: vec![reason],
        }
    }

    pub fn residual(reason: SemanticEvidenceReason) -> Self {
        Self {
            tier: SemanticConfidence::Residual,
            soundness: SemanticEvidenceSoundness::Unknown,
            coverage: SemanticEvidenceCoverage::Partial,
            provenance: SemanticEvidenceProvenance::Unstable,
            ambiguity: SemanticEvidenceAmbiguity::Multiple,
            budget_limited: false,
            reasons: vec![reason],
        }
    }

    pub fn with_coverage(mut self, coverage: SemanticEvidenceCoverage) -> Self {
        self.coverage = coverage;
        self
    }

    pub fn with_provenance(mut self, provenance: SemanticEvidenceProvenance) -> Self {
        self.provenance = provenance;
        self
    }

    pub fn with_ambiguity(mut self, ambiguity: SemanticEvidenceAmbiguity) -> Self {
        self.ambiguity = ambiguity;
        self
    }

    pub fn with_budget_limited(mut self, budget_limited: bool) -> Self {
        self.budget_limited = budget_limited;
        self
    }

    pub fn with_reason(mut self, reason: SemanticEvidenceReason) -> Self {
        if !self.reasons.contains(&reason) {
            self.reasons.push(reason);
        }
        self
    }

    pub fn is_reliable(&self) -> bool {
        self.tier.is_reliable()
            && matches!(
                self.soundness,
                SemanticEvidenceSoundness::Proven | SemanticEvidenceSoundness::OverApprox
            )
            && !matches!(self.ambiguity, SemanticEvidenceAmbiguity::Multiple)
    }

    pub fn is_usable(&self) -> bool {
        self.tier.is_usable() && !matches!(self.soundness, SemanticEvidenceSoundness::Unknown)
    }

    pub fn allows_hard_proof(&self) -> bool {
        matches!(self.tier, SemanticConfidence::Exact)
            && matches!(self.soundness, SemanticEvidenceSoundness::Proven)
            && matches!(self.coverage, SemanticEvidenceCoverage::Full)
            && !matches!(self.ambiguity, SemanticEvidenceAmbiguity::Multiple)
    }

    pub fn allows_narrowing(&self) -> bool {
        matches!(
            self.tier,
            SemanticConfidence::Exact | SemanticConfidence::Likely
        ) && matches!(
            self.soundness,
            SemanticEvidenceSoundness::Proven | SemanticEvidenceSoundness::OverApprox
        ) && !matches!(self.coverage, SemanticEvidenceCoverage::Partial)
            && !matches!(self.ambiguity, SemanticEvidenceAmbiguity::Multiple)
    }

    pub fn allows_guarded_structuring(&self) -> bool {
        matches!(
            self.tier,
            SemanticConfidence::Exact | SemanticConfidence::Likely
        ) && matches!(
            self.soundness,
            SemanticEvidenceSoundness::Proven
                | SemanticEvidenceSoundness::UnderApprox
                | SemanticEvidenceSoundness::OverApprox
        ) && matches!(
            self.coverage,
            SemanticEvidenceCoverage::Full | SemanticEvidenceCoverage::Bounded
        ) && !matches!(self.ambiguity, SemanticEvidenceAmbiguity::Multiple)
            && !self
                .reasons
                .contains(&SemanticEvidenceReason::ConflictingTargetSources)
    }

    pub fn allows_ranking(&self) -> bool {
        !matches!(self.tier, SemanticConfidence::Residual)
            && !matches!(self.soundness, SemanticEvidenceSoundness::Unknown)
    }

    pub fn combined_with(&self, other: &Self) -> Self {
        let mut reasons = self.reasons.clone();
        reasons.extend(other.reasons.iter().copied());
        reasons.sort_unstable();
        reasons.dedup();
        Self {
            tier: weaker_confidence(self.tier, other.tier),
            soundness: weaker_soundness(self.soundness, other.soundness),
            coverage: weaker_coverage(self.coverage, other.coverage),
            provenance: weaker_provenance(self.provenance, other.provenance),
            ambiguity: weaker_ambiguity(self.ambiguity, other.ambiguity),
            budget_limited: self.budget_limited || other.budget_limited,
            reasons,
        }
    }

    pub fn downgraded_for_conflict(&self) -> Self {
        self.combined_with(
            &Self::residual(SemanticEvidenceReason::ConflictingTargetSources)
                .with_budget_limited(self.budget_limited),
        )
    }

    pub fn refused(reason: SemanticEvidenceReason) -> Self {
        Self::residual(reason)
    }

    pub fn strength_rank(&self) -> (u8, u8, u8, u8, u8, u8) {
        let tier_rank = match self.tier {
            SemanticConfidence::Exact => 4,
            SemanticConfidence::Likely => 3,
            SemanticConfidence::Heuristic => 2,
            SemanticConfidence::Residual => 1,
        };
        let soundness_rank = match self.soundness {
            SemanticEvidenceSoundness::Proven => 5,
            SemanticEvidenceSoundness::UnderApprox => 4,
            SemanticEvidenceSoundness::OverApprox => 3,
            SemanticEvidenceSoundness::Ranked => 2,
            SemanticEvidenceSoundness::Unknown => 1,
        };
        let coverage_rank = match self.coverage {
            SemanticEvidenceCoverage::Full => 3,
            SemanticEvidenceCoverage::Bounded => 2,
            SemanticEvidenceCoverage::Partial => 1,
        };
        let provenance_rank = match self.provenance {
            SemanticEvidenceProvenance::Stable => 4,
            SemanticEvidenceProvenance::Normalized => 3,
            SemanticEvidenceProvenance::Ranked => 2,
            SemanticEvidenceProvenance::Unstable => 1,
        };
        let ambiguity_rank = match self.ambiguity {
            SemanticEvidenceAmbiguity::Single => 4,
            SemanticEvidenceAmbiguity::Bounded => 3,
            SemanticEvidenceAmbiguity::Ranked => 2,
            SemanticEvidenceAmbiguity::Multiple => 1,
        };
        (
            self.allows_hard_proof() as u8,
            self.allows_narrowing() as u8,
            soundness_rank,
            tier_rank,
            coverage_rank,
            provenance_rank * 4 + ambiguity_rank - u8::from(self.budget_limited),
        )
    }
}

fn weaker_confidence(left: SemanticConfidence, right: SemanticConfidence) -> SemanticConfidence {
    match (left, right) {
        (SemanticConfidence::Residual, _) | (_, SemanticConfidence::Residual) => {
            SemanticConfidence::Residual
        }
        (SemanticConfidence::Heuristic, _) | (_, SemanticConfidence::Heuristic) => {
            SemanticConfidence::Heuristic
        }
        (SemanticConfidence::Likely, _) | (_, SemanticConfidence::Likely) => {
            SemanticConfidence::Likely
        }
        _ => SemanticConfidence::Exact,
    }
}

fn weaker_soundness(
    left: SemanticEvidenceSoundness,
    right: SemanticEvidenceSoundness,
) -> SemanticEvidenceSoundness {
    use SemanticEvidenceSoundness as Soundness;
    match (left, right) {
        (Soundness::Unknown, _) | (_, Soundness::Unknown) => Soundness::Unknown,
        (Soundness::Ranked, _) | (_, Soundness::Ranked) => Soundness::Ranked,
        (Soundness::OverApprox, Soundness::UnderApprox)
        | (Soundness::UnderApprox, Soundness::OverApprox) => Soundness::Ranked,
        (Soundness::OverApprox, _) | (_, Soundness::OverApprox) => Soundness::OverApprox,
        (Soundness::UnderApprox, _) | (_, Soundness::UnderApprox) => Soundness::UnderApprox,
        _ => Soundness::Proven,
    }
}

fn weaker_coverage(
    left: SemanticEvidenceCoverage,
    right: SemanticEvidenceCoverage,
) -> SemanticEvidenceCoverage {
    use SemanticEvidenceCoverage as Coverage;
    match (left, right) {
        (Coverage::Partial, _) | (_, Coverage::Partial) => Coverage::Partial,
        (Coverage::Bounded, _) | (_, Coverage::Bounded) => Coverage::Bounded,
        _ => Coverage::Full,
    }
}

fn weaker_provenance(
    left: SemanticEvidenceProvenance,
    right: SemanticEvidenceProvenance,
) -> SemanticEvidenceProvenance {
    left.max(right)
}

fn weaker_ambiguity(
    left: SemanticEvidenceAmbiguity,
    right: SemanticEvidenceAmbiguity,
) -> SemanticEvidenceAmbiguity {
    left.max(right)
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SemanticArtifactBody {
    Native(NativeArtifactBody),
    Vm(Box<VmArtifactBody>),
}

/// Serializable semantic analysis data. This report is non-authoritative and
/// cannot be promoted into a runtime artifact without recompiling against an
/// exact prepared SSA owner.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticArtifactReport {
    pub schema_version: u32,
    pub stage: RefinementStage,
    pub granularity: ArtifactGranularity,
    pub execution: ExecutionModel,
    pub body: SemanticArtifactBody,
    pub diagnostics: SemanticArtifactDiagnostics,
}

impl SemanticArtifactReport {
    pub fn normalized(mut self) -> Self {
        self.diagnostics = self.diagnostics.normalized();
        self
    }
}

/// Runtime semantic analysis bound to the exact immutable SSA owner from
/// which it was compiled.
///
/// Construction is crate-private, the retained owner is never serialized,
/// and deserialized reports cannot regain runtime authority.
#[derive(Debug, Clone)]
pub struct SemanticArtifact {
    prepared: Arc<SsaArtifact>,
    report: SemanticArtifactReport,
    provenance: SemanticArtifactProvenance,
}

#[derive(Debug, Clone, Default)]
struct SemanticArtifactProvenance {
    interproc: Vec<PreparedInterprocSummarySet>,
}

impl PartialEq for SemanticArtifact {
    fn eq(&self, other: &Self) -> bool {
        self.prepared.authority() == other.prepared.authority() && self.report == other.report
    }
}

impl Eq for SemanticArtifact {}

impl std::ops::Deref for SemanticArtifact {
    type Target = SemanticArtifactReport;

    fn deref(&self) -> &Self::Target {
        &self.report
    }
}

impl SemanticArtifact {
    pub(crate) fn new(prepared: Arc<SsaArtifact>, report: SemanticArtifactReport) -> Option<Self> {
        if report.schema_version != crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION {
            return None;
        }
        Some(Self {
            prepared,
            report,
            provenance: SemanticArtifactProvenance::default(),
        })
    }

    pub(crate) fn new_with_interproc_provenance(
        prepared: Arc<SsaArtifact>,
        report: SemanticArtifactReport,
        summaries: &PreparedInterprocSummarySet,
    ) -> Option<Self> {
        let mut artifact = Self::new(prepared, report)?;
        artifact
            .retain_interproc_provenance(summaries)
            .then_some(artifact)
    }

    pub fn normalized(mut self) -> Self {
        self.report = self.report.normalized();
        self
    }

    pub fn report(&self) -> &SemanticArtifactReport {
        &self.report
    }

    pub fn prepared(&self) -> &SsaArtifact {
        self.prepared.as_ref()
    }

    pub fn shared_prepared(&self) -> Arc<SsaArtifact> {
        Arc::clone(&self.prepared)
    }

    pub fn shares_artifact(&self, prepared: &SsaArtifact) -> bool {
        self.prepared.authority() == prepared.authority()
    }

    #[cfg(test)]
    pub(crate) fn has_helper_provenance(&self) -> bool {
        !self.provenance.interproc.is_empty()
    }

    pub(crate) fn retain_interproc_provenance(
        &mut self,
        summaries: &PreparedInterprocSummarySet,
    ) -> bool {
        if !summaries.matches_root(&self.prepared) {
            return false;
        }
        if !interproc_summary_uses_owned_helper(summaries) {
            return true;
        }
        if !self
            .provenance
            .interproc
            .iter()
            .any(|retained| same_interproc_owners(retained, summaries))
        {
            self.provenance.interproc.push(summaries.clone());
        }
        true
    }

    pub(crate) fn report_mut(&mut self) -> &mut SemanticArtifactReport {
        &mut self.report
    }
}

fn interproc_summary_uses_owned_helper(summaries: &PreparedInterprocSummarySet) -> bool {
    let Some(root) = summaries.report().root else {
        return false;
    };
    let mut pending = vec![root];
    let mut visited = std::collections::BTreeSet::new();
    while let Some(function) = pending.pop() {
        if !visited.insert(function) {
            continue;
        }
        let Some(summary) = summaries.report().summaries.get(&function) else {
            continue;
        };
        for callee in &summary.direct_callees {
            let callee = InterprocFunctionId(*callee);
            if callee != root && summaries.owner(callee).is_some() {
                return true;
            }
            pending.push(callee);
        }
    }
    false
}

fn same_interproc_owners(
    left: &PreparedInterprocSummarySet,
    right: &PreparedInterprocSummarySet,
) -> bool {
    left.owners().len() == right.owners().len()
        && left.owners().iter().all(|(id, owner)| {
            right
                .owner(*id)
                .is_some_and(|candidate| Arc::ptr_eq(owner, candidate))
        })
}

impl SemanticArtifactReport {
    fn has_native_semantics(&self) -> bool {
        self.native_body()
            .is_some_and(|body| !body.regions.is_empty() || body.has_summary_islands())
    }

    fn supports_native_semantic_structuring(&self) -> bool {
        self.native_body()
            .is_some_and(NativeArtifactBody::supports_guarded_structuring)
    }

    fn has_query_support(&self) -> bool {
        self.native_body()
            .is_some_and(NativeArtifactBody::supports_query_guidance)
    }

    pub fn slice_class(&self) -> Option<SliceClass> {
        match &self.body {
            SemanticArtifactBody::Native(body) => Some(body.summary.slice_class),
            SemanticArtifactBody::Vm(body) => body
                .step_summary
                .as_ref()
                .map(|summary| slice_class_for_interpreter_kind(summary.kind))
                .or_else(|| {
                    body.transfer_summary
                        .as_ref()
                        .map(|summary| slice_class_for_interpreter_kind(summary.kind))
                })
                .or_else(|| {
                    body.interpreter
                        .as_ref()
                        .map(|summary| slice_class_for_interpreter_kind(summary.kind))
                }),
        }
    }

    pub fn build_plan(&self) -> ArtifactBuildPlan {
        derive_artifact_build_plan(self.stage, &self.diagnostics)
    }

    pub fn query_plan(&self) -> QueryPlan {
        derive_query_plan(
            self.stage,
            self.execution,
            &self.diagnostics,
            self.has_query_support(),
        )
    }

    pub fn target_query_plan(&self, target_addr: u64) -> TargetQueryPlan {
        let query_plan = self.query_plan();
        let has_guidance = self
            .native_body()
            .is_some_and(|body| body.has_target_guidance(target_addr, false));
        let necessary_for_target = self
            .native_body()
            .is_some_and(|body| body.target_guidance_is_necessary(target_addr, false));
        let has_source_conflict = self.target_has_ambiguous_sources(target_addr);
        derive_target_query_plan(
            &query_plan,
            has_guidance,
            has_source_conflict,
            necessary_for_target,
        )
    }

    pub fn target_query_route_plan(&self, target_addr: u64) -> TargetQueryRoutePlan {
        let query_plan = self.query_plan();
        let target_plan = self.target_query_plan(target_addr);
        let condition_source = self.target_condition_source(target_addr, false);
        let authoritative_memory_region = self.authoritative_memory_region_for_target(target_addr);
        let has_memory_guidance = authoritative_memory_region.is_some_and(|region| {
            !region
                .actionable_memory_terms_for_target(target_addr)
                .is_empty()
        });
        derive_target_query_route_plan(
            &query_plan,
            &target_plan,
            self.execution,
            condition_source.is_some(),
            has_memory_guidance,
        )
    }

    pub fn type_plan(&self) -> TypePlan {
        derive_type_plan(
            self.stage,
            self.execution,
            &self.diagnostics,
            self.has_native_semantics(),
        )
    }

    pub fn decompile_plan(&self) -> DecompilePlan {
        derive_decompile_plan(
            self.stage,
            self.execution,
            &self.diagnostics,
            self.has_native_semantics(),
            self.native_body()
                .is_some_and(NativeArtifactBody::has_summary_islands),
            self.supports_native_semantic_structuring(),
        )
    }

    pub fn native_body(&self) -> Option<&NativeArtifactBody> {
        match &self.body {
            SemanticArtifactBody::Native(body) => Some(body),
            // A VM function's native regions are the same regions any other function
            // would have, so a consumer asking for them gets them.
            SemanticArtifactBody::Vm(body) => body.native.as_deref(),
        }
    }

    pub fn semantic_claim_summary(&self) -> SemanticClaimSummary {
        self.native_body()
            .map(SemanticClaimSummary::from_native_body)
            .unwrap_or_else(SemanticClaimSummary::empty)
    }

    pub fn vm_body(&self) -> Option<&VmArtifactBody> {
        match &self.body {
            SemanticArtifactBody::Native(_) => None,
            SemanticArtifactBody::Vm(body) => Some(body.as_ref()),
        }
    }

    pub fn exact_reachable_target_for_block(&self, block_addr: u64) -> Option<u64> {
        self.native_body()?
            .exact_reachable_target_for_block(block_addr)
    }

    pub fn actionable_reachable_target_for_block(&self, block_addr: u64) -> Option<u64> {
        self.native_body()?
            .actionable_reachable_target_for_block(block_addr)
    }

    pub fn exact_branch_truth_for_block(&self, block_addr: u64) -> Option<bool> {
        self.native_body()?.exact_branch_truth_for_block(block_addr)
    }

    pub fn exact_compiled_condition_for_block(
        &self,
        block_addr: u64,
    ) -> Option<&crate::backward::BackwardConditionSummary> {
        self.native_body()?
            .exact_compiled_condition_for_block(block_addr)
    }

    pub fn actionable_compiled_condition_for_block(
        &self,
        block_addr: u64,
    ) -> Option<&crate::backward::BackwardConditionSummary> {
        self.native_body()?
            .actionable_compiled_condition_for_block(block_addr)
    }

    pub fn actionable_memory_terms_for_block(
        &self,
        block_addr: u64,
    ) -> Vec<&crate::backward::BackwardMemoryCondition> {
        self.native_body()
            .map(|body| body.actionable_memory_terms_for_block(block_addr))
            .unwrap_or_default()
    }

    pub fn exact_control_count(&self) -> usize {
        self.native_body()
            .map(NativeArtifactBody::exact_control_count)
            .unwrap_or_default()
    }

    pub fn actionable_control_count(&self) -> usize {
        self.native_body()
            .map(NativeArtifactBody::actionable_control_count)
            .unwrap_or_default()
    }

    pub fn actionable_regions(&self) -> Vec<&SemanticRegion> {
        self.native_body()
            .map(|body| body.actionable_regions().collect())
            .unwrap_or_default()
    }

    pub fn target_condition_source(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Option<SemanticTargetConditionSource<'_>> {
        self.native_body()?
            .target_condition_source(target_addr, proof_only)
    }

    pub fn actionable_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&crate::backward::BackwardConditionSummary> {
        self.native_body()?
            .actionable_compiled_condition_for_target(target_addr)
    }

    pub fn exact_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&crate::backward::BackwardConditionSummary> {
        self.native_body()?
            .exact_compiled_condition_for_target(target_addr)
    }

    pub fn actionable_memory_terms_for_target(
        &self,
        target_addr: u64,
    ) -> Vec<&crate::backward::BackwardMemoryCondition> {
        self.native_body()
            .map(|body| body.actionable_memory_terms_for_target(target_addr))
            .unwrap_or_default()
    }

    pub fn authoritative_memory_region_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&SemanticRegion> {
        self.native_body()?
            .authoritative_memory_region_for_target(target_addr)
    }

    pub fn authoritative_region_for_target(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Option<&SemanticRegion> {
        self.native_body()?
            .authoritative_region_for_target(target_addr, proof_only)
    }

    pub fn ambiguous_targets(&self) -> Vec<u64> {
        if !self.diagnostics.ambiguous_targets.is_empty() {
            return self.diagnostics.ambiguous_targets.clone();
        }
        self.native_body()
            .map(|body| body.conflicting_targets(false).into_iter().collect())
            .unwrap_or_default()
    }

    pub fn target_has_ambiguous_sources(&self, target_addr: u64) -> bool {
        self.diagnostics.ambiguous_targets.contains(&target_addr)
            || self
                .native_body()
                .is_some_and(|body| body.target_source_conflict(target_addr, false))
    }

    pub fn vm_step_for_dispatch_header(
        &self,
        dispatch_header: u64,
    ) -> Option<&crate::VmStepSummary> {
        self.vm_body()?
            .step_summary
            .as_ref()
            .filter(|summary| summary.dispatch_header == dispatch_header)
    }

    pub fn vm_transfer_for_dispatch_header(
        &self,
        dispatch_header: u64,
    ) -> Option<&crate::VmStepSummary> {
        self.vm_body()?
            .transfer_summary
            .as_ref()
            .filter(|summary| summary.dispatch_header == dispatch_header)
    }

    pub fn supports_guarded_structuring(&self) -> bool {
        self.decompile_plan().allows_native_structuring()
    }

    pub fn supports_native_semantic_linearization(&self) -> bool {
        self.decompile_plan().allows_native_linearization()
    }

    pub fn vm_summary_only_type_plan(&self) -> bool {
        self.type_plan().is_vm_summary_only()
    }

    pub fn vm_summary_only_decompile_plan(&self) -> bool {
        self.decompile_plan().is_vm_summary_only()
    }
}

fn slice_class_for_interpreter_kind(kind: InterpreterKind) -> SliceClass {
    match kind {
        InterpreterKind::SwitchDispatch => SliceClass::InterpreterSwitch,
        InterpreterKind::IndirectDispatch => SliceClass::InterpreterIndirect,
    }
}

impl SemanticArtifactDiagnostics {
    pub fn normalized(mut self) -> Self {
        self.residual_reasons.sort_unstable();
        self.residual_reasons.dedup();
        self.ambiguous_targets.sort_unstable();
        self.ambiguous_targets.dedup();
        self
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use proptest::prelude::*;
    use r2il::{R2ILBlock, R2ILOp, Varnode};
    use r2ssa::SsaArtifact;

    use super::{
        ResidualReason, SemanticArtifact, SemanticArtifactBody, SemanticArtifactDiagnostics,
        SemanticArtifactReport, SemanticConfidence, SemanticEvidence, SemanticEvidenceAmbiguity,
        SemanticEvidenceCoverage, SemanticEvidenceProvenance, SemanticEvidenceReason,
        SemanticEvidenceSoundness, SliceClass,
    };
    use crate::{
        ArtifactGranularity, ExecutionModel, NativeArtifactBody, NativeFunctionSummary,
        RefinementStage,
    };

    fn test_prepared() -> Arc<SsaArtifact> {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        Arc::new(SsaArtifact::for_symbolic(&[block], None).expect("test SSA"))
    }

    fn native_report(diagnostics: SemanticArtifactDiagnostics) -> SemanticArtifactReport {
        SemanticArtifactReport {
            schema_version: crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION,
            stage: RefinementStage::Compiled,
            granularity: ArtifactGranularity::WholeFunction,
            execution: ExecutionModel::Native,
            body: SemanticArtifactBody::Native(NativeArtifactBody {
                summary: NativeFunctionSummary {
                    slice_class: SliceClass::Worker,
                    role_identity: None,
                    closure_functions: 0,
                    helper_functions: 0,
                    region_summaries: Vec::new(),
                    worker_summaries: Vec::new(),
                },
                regions: Default::default(),
            }),
            diagnostics,
        }
    }

    fn native_artifact(diagnostics: SemanticArtifactDiagnostics) -> SemanticArtifact {
        SemanticArtifact::new(test_prepared(), native_report(diagnostics))
            .expect("current test semantic artifact schema")
    }

    fn empty_diagnostics() -> SemanticArtifactDiagnostics {
        SemanticArtifactDiagnostics {
            branches_evaluated: 0,
            branches_pruned: 0,
            branches_unknown: 0,
            skipped_missing_arch: false,
            skipped_large_cfg: false,
            residual_reasons: Vec::new(),
            interpreter: None,
            ambiguous_targets: Vec::new(),
        }
    }

    #[test]
    fn report_round_trip_does_not_reconstruct_runtime_authority() {
        let report = native_report(empty_diagnostics());
        let encoded = serde_json::to_string(&report).expect("serialize report");
        let decoded: SemanticArtifactReport =
            serde_json::from_str(&encoded).expect("deserialize report");

        assert_eq!(decoded, report);
        assert_eq!(
            decoded.schema_version,
            crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION
        );
        assert_eq!(decoded.slice_class(), Some(SliceClass::Worker));
        assert!(decoded.native_body().is_some());
        assert!(decoded.vm_body().is_none());
        assert!(decoded.semantic_claim_summary().claims.is_empty());
        assert_eq!(decoded.exact_control_count(), 0);
        assert_eq!(decoded.actionable_control_count(), 0);
        let _ = decoded.build_plan();
        let _ = decoded.query_plan();
        let _ = decoded.target_query_plan(0x1000);
        let _ = decoded.target_query_route_plan(0x1000);
        let _ = decoded.type_plan();
        let _ = decoded.decompile_plan();
    }

    #[test]
    fn semantic_artifact_refuses_noncurrent_report_schema() {
        for schema_version in [
            crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION.saturating_sub(1),
            crate::SEMANTIC_ARTIFACT_SCHEMA_VERSION.saturating_add(1),
        ] {
            let mut report = native_report(empty_diagnostics());
            report.schema_version = schema_version;
            assert!(SemanticArtifact::new(test_prepared(), report).is_none());
        }
    }

    fn evidence_from_seed(seed: u8) -> SemanticEvidence {
        let tier = match seed % 4 {
            0 => SemanticConfidence::Exact,
            1 => SemanticConfidence::Likely,
            2 => SemanticConfidence::Heuristic,
            _ => SemanticConfidence::Residual,
        };
        let soundness = match (seed / 4) % 5 {
            0 => SemanticEvidenceSoundness::Proven,
            1 => SemanticEvidenceSoundness::UnderApprox,
            2 => SemanticEvidenceSoundness::OverApprox,
            3 => SemanticEvidenceSoundness::Ranked,
            _ => SemanticEvidenceSoundness::Unknown,
        };
        let coverage = match (seed / 20) % 3 {
            0 => SemanticEvidenceCoverage::Full,
            1 => SemanticEvidenceCoverage::Bounded,
            _ => SemanticEvidenceCoverage::Partial,
        };
        let provenance = match (seed / 60) % 4 {
            0 => SemanticEvidenceProvenance::Stable,
            1 => SemanticEvidenceProvenance::Normalized,
            2 => SemanticEvidenceProvenance::Ranked,
            _ => SemanticEvidenceProvenance::Unstable,
        };
        let ambiguity = match (seed / 120) % 4 {
            0 => SemanticEvidenceAmbiguity::Single,
            1 => SemanticEvidenceAmbiguity::Bounded,
            2 => SemanticEvidenceAmbiguity::Ranked,
            _ => SemanticEvidenceAmbiguity::Multiple,
        };
        SemanticEvidence {
            tier,
            soundness,
            coverage,
            provenance,
            ambiguity,
            budget_limited: seed.is_multiple_of(2),
            reasons: vec![
                SemanticEvidenceReason::LargeCfg,
                SemanticEvidenceReason::AliasAmbiguity,
            ],
        }
    }

    proptest! {
        #[test]
        fn evidence_combine_is_monotone(left in any::<u8>(), right in any::<u8>()) {
            let left = evidence_from_seed(left);
            let right = evidence_from_seed(right);
            let combined = left.combined_with(&right);
            prop_assert!(combined.strength_rank() <= left.strength_rank());
            prop_assert!(combined.strength_rank() <= right.strength_rank());
        }

        #[test]
        fn artifact_normalization_is_idempotent(
            residuals in proptest::collection::vec(prop_oneof![
                Just(ResidualReason::MissingArch),
                Just(ResidualReason::LargeCfg),
                Just(ResidualReason::InterpreterRequiresStepSummary),
            ], 0..8),
            ambiguous in proptest::collection::vec(any::<u64>(), 0..8),
        ) {
            let artifact = native_artifact(SemanticArtifactDiagnostics {
                branches_evaluated: 0,
                branches_pruned: 0,
                branches_unknown: 0,
                skipped_missing_arch: false,
                skipped_large_cfg: false,
                residual_reasons: residuals,
                interpreter: None,
                ambiguous_targets: ambiguous,
            });
            let normalized = artifact.clone().normalized();
            prop_assert_eq!(normalized.clone().normalized(), normalized);
        }
    }

    #[test]
    fn conflict_downgrade_refuses_narrowing() {
        let evidence = SemanticEvidence::exact().downgraded_for_conflict();
        assert!(!evidence.allows_narrowing());
        assert!(
            evidence
                .reasons
                .contains(&SemanticEvidenceReason::ConflictingTargetSources)
        );
    }
}
