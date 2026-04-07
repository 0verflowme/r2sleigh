use serde::{Deserialize, Serialize};

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
    RecursiveGroup,
    InterpreterSwitch,
    InterpreterIndirect,
    GenericLarge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ResidualReason {
    MissingArch,
    LargeCfg,
    SummaryBudgetExhausted,
    SccBudgetExhausted,
    InterpreterRequiresStepSummary,
}

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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticArtifact {
    pub stage: RefinementStage,
    pub granularity: ArtifactGranularity,
    pub execution: ExecutionModel,
    pub body: SemanticArtifactBody,
    pub diagnostics: SemanticArtifactDiagnostics,
}

impl SemanticArtifact {
    pub fn normalized(mut self) -> Self {
        self.diagnostics = self.diagnostics.normalized();
        self
    }

    fn has_native_semantics(&self) -> bool {
        self.native_body()
            .is_some_and(|body| !body.regions.is_empty())
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
        let authoritative_region = self.authoritative_region_for_target(target_addr, false);
        let authoritative_memory_region = self.authoritative_memory_region_for_target(target_addr);
        let has_memory_guidance = authoritative_memory_region.is_some_and(|region| {
            !region
                .actionable_memory_terms_for_target(target_addr)
                .is_empty()
        });
        derive_target_query_route_plan(
            &query_plan,
            &target_plan,
            authoritative_region.is_some() || authoritative_memory_region.is_some(),
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
            self.supports_native_semantic_structuring(),
        )
    }

    pub fn native_body(&self) -> Option<&NativeArtifactBody> {
        match &self.body {
            SemanticArtifactBody::Native(body) => Some(body),
            SemanticArtifactBody::Vm(_) => None,
        }
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
    use proptest::prelude::*;

    use super::{
        ResidualReason, SemanticArtifact, SemanticArtifactBody, SemanticArtifactDiagnostics,
        SemanticConfidence, SemanticEvidence, SemanticEvidenceAmbiguity, SemanticEvidenceCoverage,
        SemanticEvidenceProvenance, SemanticEvidenceReason, SemanticEvidenceSoundness, SliceClass,
    };
    use crate::sim::DerivedSummaryDiagnostics;
    use crate::{
        ArtifactGranularity, ExecutionModel, NativeArtifactBody, NativeFunctionSummary,
        RefinementStage,
    };

    fn native_artifact(diagnostics: SemanticArtifactDiagnostics) -> SemanticArtifact {
        SemanticArtifact {
            stage: RefinementStage::Compiled,
            granularity: ArtifactGranularity::WholeFunction,
            execution: ExecutionModel::Native,
            body: SemanticArtifactBody::Native(NativeArtifactBody {
                summary: NativeFunctionSummary {
                    slice_class: SliceClass::Worker,
                    closure_functions: 0,
                    helper_functions: 0,
                    derived_summaries: 0,
                    derived_diagnostics: DerivedSummaryDiagnostics::default(),
                },
                regions: Default::default(),
            }),
            diagnostics,
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
                Just(ResidualReason::SummaryBudgetExhausted),
                Just(ResidualReason::SccBudgetExhausted),
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
                ambiguous_targets: ambiguous,
                cache_hit: false,
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
