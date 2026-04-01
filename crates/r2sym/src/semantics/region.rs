use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::backward::{BackwardConditionSummary, BackwardMemoryCondition};
use crate::sim::DerivedSummaryDiagnostics;

use super::artifact::{ResidualReason, SemanticEvidence, SliceClass};
use super::facts::SymbolicReachabilityStatus;
use super::vm::{InterpreterDispatchSummary, VmStepSummary};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RefinementStage {
    Raw,
    Compiled,
    Residual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ArtifactGranularity {
    WholeFunction,
    Regioned,
    SummaryOnly,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ExecutionModel {
    Native,
    Vm,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RegionKey {
    pub anchor_block: u64,
    pub frontier: BTreeSet<u64>,
}

impl RegionKey {
    pub fn new(anchor_block: u64, frontier: BTreeSet<u64>) -> Self {
        Self {
            anchor_block,
            frontier,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Judged<T> {
    pub value: T,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl<T> Judged<T> {
    pub fn new(value: T, evidence: SemanticEvidence) -> Self {
        Self { value, evidence }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ControlFact {
    pub target: u64,
    pub status: SymbolicReachabilityStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_truth: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiled: Option<BackwardConditionSummary>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryFact {
    pub term: BackwardMemoryCondition,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticPredicate {
    pub expr: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiled: Option<BackwardConditionSummary>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetFact {
    pub target: u64,
    pub status: SymbolicReachabilityStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch_truth: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticRegion {
    pub anchor: u64,
    pub frontier: BTreeSet<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub control: Vec<Judged<ControlFact>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory: Vec<Judged<MemoryFact>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub pre: Vec<Judged<SemanticPredicate>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub post: Vec<Judged<SemanticPredicate>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub targets: Vec<Judged<TargetFact>>,
}

impl SemanticRegion {
    pub fn key(&self) -> RegionKey {
        RegionKey::new(self.anchor, self.frontier.clone())
    }

    fn compiled_condition_for_target(
        &self,
        target: u64,
        proof_only: bool,
    ) -> Option<&BackwardConditionSummary> {
        self.control
            .iter()
            .find(|fact| fact.value.target == target)
            .and_then(|fact| {
                let allowed = if proof_only {
                    fact.evidence.allows_hard_proof()
                } else {
                    fact.evidence.allows_narrowing()
                };
                allowed.then_some(fact.value.compiled.as_ref()).flatten()
            })
    }

    fn unique_compiled_condition(&self, proof_only: bool) -> Option<&BackwardConditionSummary> {
        let mut candidates = self.control.iter().filter_map(|fact| {
            let allowed = if proof_only {
                fact.evidence.allows_hard_proof()
            } else {
                fact.evidence.allows_narrowing()
            };
            allowed.then_some(fact.value.compiled.as_ref()).flatten()
        });
        let first = candidates.next()?;
        candidates
            .all(|candidate| candidate == first)
            .then_some(first)
    }

    fn unique_reachable_target(&self, proof_only: bool) -> Option<u64> {
        let mut candidates = self.control.iter().filter_map(|fact| {
            let allowed = if proof_only {
                fact.evidence.allows_hard_proof()
            } else {
                fact.evidence.allows_narrowing()
            };
            allowed
                .then_some(matches!(
                    fact.value.status,
                    SymbolicReachabilityStatus::Reachable
                ))
                .and_then(|reachable| reachable.then_some(fact.value.target))
        });
        let first = candidates.next()?;
        candidates
            .all(|candidate| candidate == first)
            .then_some(first)
    }

    pub fn exact_reachable_target(&self) -> Option<u64> {
        self.unique_reachable_target(true)
    }

    pub fn actionable_reachable_target(&self) -> Option<u64> {
        self.unique_reachable_target(false)
    }

    pub fn exact_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        self.unique_compiled_condition(true)
    }

    pub fn actionable_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        self.unique_compiled_condition(false)
    }

    pub fn exact_compiled_condition_for_target(
        &self,
        target: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.compiled_condition_for_target(target, true)
    }

    pub fn actionable_compiled_condition_for_target(
        &self,
        target: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.compiled_condition_for_target(target, false)
    }

    pub fn exact_memory_terms(&self) -> Vec<&BackwardMemoryCondition> {
        self.memory
            .iter()
            .filter(|term| term.evidence.allows_hard_proof())
            .map(|term| &term.value.term)
            .collect()
    }

    pub fn actionable_memory_terms(&self) -> Vec<&BackwardMemoryCondition> {
        self.memory
            .iter()
            .filter(|term| term.evidence.allows_narrowing())
            .map(|term| &term.value.term)
            .collect()
    }

    pub fn exact_memory_terms_for_target(&self, target: u64) -> Vec<&BackwardMemoryCondition> {
        self.exact_compiled_condition_for_target(target)
            .map(|compiled| {
                compiled
                    .memory_terms
                    .iter()
                    .filter(|term| term.evidence().allows_hard_proof())
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn actionable_memory_terms_for_target(&self, target: u64) -> Vec<&BackwardMemoryCondition> {
        match self.actionable_compiled_condition_for_target(target) {
            Some(compiled) if !compiled.memory_terms.is_empty() => compiled
                .memory_terms
                .iter()
                .filter(|term| term.evidence().allows_narrowing())
                .collect(),
            Some(_) => Vec::new(),
            None => {
                if self.actionable_reachable_target() == Some(target) {
                    self.actionable_memory_terms()
                } else {
                    Vec::new()
                }
            }
        }
    }

    pub fn branch_truth_for_target(&self, target: u64) -> Option<bool> {
        self.control
            .iter()
            .find(|fact| fact.value.target == target)
            .and_then(|fact| fact.value.branch_truth)
    }

    pub fn supports_guarded_structuring(&self) -> bool {
        let reachable_target = self
            .exact_reachable_target()
            .or_else(|| self.actionable_reachable_target());
        let has_condition = reachable_target
            .and_then(|target| self.actionable_compiled_condition_for_target(target))
            .is_some();
        let has_memory_support = reachable_target
            .map(|target| !self.actionable_memory_terms_for_target(target).is_empty())
            .unwrap_or(false);
        self.control
            .iter()
            .any(|fact| fact.evidence.allows_guarded_structuring())
            && has_condition
            && has_memory_support
    }

    pub fn supports_query_guidance(&self) -> bool {
        self.control
            .iter()
            .any(|fact| fact.evidence.allows_narrowing() && fact.value.compiled.is_some())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeFunctionSummary {
    pub slice_class: SliceClass,
    pub closure_functions: usize,
    pub helper_functions: usize,
    pub derived_summaries: usize,
    pub derived_diagnostics: DerivedSummaryDiagnostics,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeArtifactBody {
    pub summary: NativeFunctionSummary,
    #[serde(
        default,
        skip_serializing_if = "BTreeMap::is_empty",
        serialize_with = "serialize_region_map",
        deserialize_with = "deserialize_region_map"
    )]
    pub regions: BTreeMap<RegionKey, SemanticRegion>,
}

fn serialize_region_map<S>(
    regions: &BTreeMap<RegionKey, SemanticRegion>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    regions
        .values()
        .cloned()
        .collect::<Vec<_>>()
        .serialize(serializer)
}

fn deserialize_region_map<'de, D>(
    deserializer: D,
) -> Result<BTreeMap<RegionKey, SemanticRegion>, D::Error>
where
    D: Deserializer<'de>,
{
    let regions = Vec::<SemanticRegion>::deserialize(deserializer)?;
    Ok(regions
        .into_iter()
        .map(|region| (region.key(), region))
        .collect())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SemanticTargetConditionSource<'a> {
    pub block_addr: u64,
    pub branch_truth: bool,
    pub summary: &'a BackwardConditionSummary,
    pub necessary_for_target: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SemanticTargetRegionSource<'a> {
    pub region: &'a SemanticRegion,
    pub branch_truth: Option<bool>,
    pub summary: &'a BackwardConditionSummary,
    pub necessary_for_target: bool,
}

fn summary_strength_rank(
    summary: &BackwardConditionSummary,
) -> (u8, u8, usize, usize, usize, usize) {
    let strength = summary.evidence().strength_rank();
    (
        strength.0,
        strength.1,
        summary.memory_terms.len(),
        summary.supported_paths,
        usize::MAX.saturating_sub(summary.total_paths),
        usize::MAX.saturating_sub(summary.simplified.len()),
    )
}

impl NativeArtifactBody {
    fn target_source_region(&self, target_addr: u64, proof_only: bool) -> Option<&SemanticRegion> {
        self.authoritative_target_region_source(target_addr, proof_only)
            .map(|source| source.region)
    }

    fn target_memory_region_candidates(&self, target_addr: u64) -> Vec<&SemanticRegion> {
        self.regions
            .values()
            .filter(|region| {
                !region
                    .actionable_memory_terms_for_target(target_addr)
                    .is_empty()
            })
            .collect()
    }

    fn target_memory_sources_are_equivalent(
        candidates: &[&SemanticRegion],
        target_addr: u64,
    ) -> bool {
        let Some(first) = candidates.first() else {
            return true;
        };
        let first_terms = first.actionable_memory_terms_for_target(target_addr);
        candidates.iter().all(|candidate| {
            candidate.actionable_memory_terms_for_target(target_addr) == first_terms
        })
    }

    fn authoritative_memory_region(&self, target_addr: u64) -> Option<&SemanticRegion> {
        let candidates = self.target_memory_region_candidates(target_addr);
        if candidates.is_empty() {
            return None;
        }
        if !Self::target_memory_sources_are_equivalent(&candidates, target_addr) {
            return None;
        }
        candidates.into_iter().next()
    }

    fn target_region_candidates(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Vec<SemanticTargetRegionSource<'_>> {
        self.regions
            .values()
            .filter_map(|region| {
                let necessary_for_target = if proof_only {
                    region.exact_reachable_target() == Some(target_addr)
                } else {
                    region.actionable_reachable_target() == Some(target_addr)
                };
                let summary = if proof_only {
                    region.exact_compiled_condition_for_target(target_addr)
                } else {
                    region.actionable_compiled_condition_for_target(target_addr)
                }?;
                Some(SemanticTargetRegionSource {
                    region,
                    branch_truth: region.branch_truth_for_target(target_addr),
                    summary,
                    necessary_for_target,
                })
            })
            .collect()
    }

    fn target_sources_are_equivalent(candidates: &[SemanticTargetRegionSource<'_>]) -> bool {
        let Some(first) = candidates.first() else {
            return true;
        };
        candidates.iter().all(|candidate| {
            candidate.summary == first.summary
                && !matches!(
                    (candidate.branch_truth, first.branch_truth),
                    (Some(left), Some(right)) if left != right
                )
        })
    }

    fn authoritative_target_region_source(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Option<SemanticTargetRegionSource<'_>> {
        let candidates = self.target_region_candidates(target_addr, proof_only);
        if candidates.is_empty() {
            return None;
        }
        if proof_only
            && candidates
                .iter()
                .any(|candidate| !candidate.necessary_for_target)
        {
            return None;
        }
        if !Self::target_sources_are_equivalent(&candidates) {
            return None;
        }
        let representative = candidates.iter().copied().max_by(|left, right| {
            (
                usize::from(left.necessary_for_target),
                summary_strength_rank(left.summary),
                usize::MAX.saturating_sub(left.region.anchor as usize),
                usize::from(left.branch_truth.unwrap_or(false)),
            )
                .cmp(&(
                    usize::from(right.necessary_for_target),
                    summary_strength_rank(right.summary),
                    usize::MAX.saturating_sub(right.region.anchor as usize),
                    usize::from(right.branch_truth.unwrap_or(false)),
                ))
        })?;
        Some(SemanticTargetRegionSource {
            necessary_for_target: candidates
                .iter()
                .all(|candidate| candidate.necessary_for_target),
            ..representative
        })
    }

    pub fn target_source_conflict(&self, target_addr: u64, proof_only: bool) -> bool {
        let candidates = self.target_region_candidates(target_addr, proof_only);
        candidates.len() > 1 && !Self::target_sources_are_equivalent(&candidates)
    }

    pub fn conflicting_targets(&self, proof_only: bool) -> BTreeSet<u64> {
        self.regions
            .values()
            .flat_map(|region| region.control.iter().map(|fact| fact.value.target))
            .filter(|target| self.target_source_conflict(*target, proof_only))
            .collect()
    }

    pub fn region_for_anchor(&self, anchor: u64) -> Option<&SemanticRegion> {
        self.regions.values().find(|region| region.anchor == anchor)
    }

    pub fn exact_control_count(&self) -> usize {
        self.regions
            .values()
            .flat_map(|region| region.control.iter())
            .filter(|fact| fact.evidence.allows_hard_proof())
            .count()
    }

    pub fn actionable_control_count(&self) -> usize {
        self.regions
            .values()
            .flat_map(|region| region.control.iter())
            .filter(|fact| fact.evidence.allows_narrowing())
            .count()
    }

    pub fn supports_guarded_structuring(&self) -> bool {
        self.regions.values().any(|region| {
            region.supports_guarded_structuring()
                && region
                    .actionable_reachable_target()
                    .is_some_and(|target| !self.target_source_conflict(target, false))
        })
    }

    pub fn supports_query_guidance(&self) -> bool {
        self.regions
            .values()
            .any(SemanticRegion::supports_query_guidance)
    }

    pub fn has_target_guidance(&self, target_addr: u64, proof_only: bool) -> bool {
        self.target_source_region(target_addr, proof_only).is_some()
    }

    pub fn target_guidance_is_necessary(&self, target_addr: u64, proof_only: bool) -> bool {
        self.target_source_region(target_addr, proof_only)
            .is_some_and(|region| {
                if proof_only {
                    region.exact_reachable_target() == Some(target_addr)
                } else {
                    region.actionable_reachable_target() == Some(target_addr)
                }
            })
    }

    pub fn exact_reachable_target_for_block(&self, block_addr: u64) -> Option<u64> {
        self.region_for_anchor(block_addr)
            .and_then(SemanticRegion::exact_reachable_target)
    }

    pub fn exact_branch_truth_for_block(&self, block_addr: u64) -> Option<bool> {
        let region = self.region_for_anchor(block_addr)?;
        let target = region.exact_reachable_target()?;
        region.branch_truth_for_target(target)
    }

    pub fn actionable_reachable_target_for_block(&self, block_addr: u64) -> Option<u64> {
        self.region_for_anchor(block_addr)
            .and_then(SemanticRegion::actionable_reachable_target)
    }

    pub fn exact_compiled_condition_for_block(
        &self,
        block_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.region_for_anchor(block_addr)
            .and_then(SemanticRegion::exact_compiled_condition)
    }

    pub fn actionable_compiled_condition_for_block(
        &self,
        block_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.region_for_anchor(block_addr)
            .and_then(SemanticRegion::actionable_compiled_condition)
    }

    pub fn actionable_memory_terms_for_block(
        &self,
        block_addr: u64,
    ) -> Vec<&BackwardMemoryCondition> {
        self.region_for_anchor(block_addr)
            .map(SemanticRegion::actionable_memory_terms)
            .unwrap_or_default()
    }

    pub fn actionable_regions(&self) -> impl Iterator<Item = &SemanticRegion> {
        self.regions.values().filter(|region| {
            region.supports_guarded_structuring()
                && region
                    .actionable_reachable_target()
                    .is_some_and(|target| !self.target_source_conflict(target, false))
        })
    }

    pub fn target_condition_source(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Option<SemanticTargetConditionSource<'_>> {
        let representative = self.authoritative_target_region_source(target_addr, proof_only)?;
        let branch_truth = representative.branch_truth?;
        Some(SemanticTargetConditionSource {
            block_addr: representative.region.anchor,
            branch_truth,
            summary: representative.summary,
            necessary_for_target: representative.necessary_for_target,
        })
    }

    pub fn actionable_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.target_source_region(target_addr, false)?
            .actionable_compiled_condition_for_target(target_addr)
    }

    pub fn exact_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        self.target_source_region(target_addr, true)?
            .exact_compiled_condition_for_target(target_addr)
    }

    pub fn actionable_memory_terms_for_target(
        &self,
        target_addr: u64,
    ) -> Vec<&BackwardMemoryCondition> {
        self.authoritative_memory_region(target_addr)
            .map(|region| region.actionable_memory_terms_for_target(target_addr))
            .unwrap_or_default()
    }

    pub fn authoritative_region_for_target(
        &self,
        target_addr: u64,
        proof_only: bool,
    ) -> Option<&SemanticRegion> {
        self.target_source_region(target_addr, proof_only)
    }

    pub fn authoritative_memory_region_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&SemanticRegion> {
        self.authoritative_memory_region(target_addr)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmArtifactBody {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interpreter: Option<InterpreterDispatchSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub step_summary: Option<VmStepSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub transfer_summary: Option<VmStepSummary>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticArtifactDiagnostics {
    pub branches_evaluated: usize,
    pub branches_pruned: usize,
    pub branches_unknown: usize,
    pub skipped_missing_arch: bool,
    pub skipped_large_cfg: bool,
    pub residual_reasons: Vec<ResidualReason>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ambiguous_targets: Vec<u64>,
    pub cache_hit: bool,
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use proptest::prelude::*;

    use super::{
        ControlFact, Judged, MemoryFact, NativeArtifactBody, NativeFunctionSummary, RegionKey,
        SemanticRegion, TargetFact,
    };
    use crate::sim::DerivedSummaryDiagnostics;
    use crate::{
        BackwardConditionPrecision, BackwardConditionSummary, BackwardMemoryCondition,
        BackwardMemoryRegion, SemanticEvidence, SliceClass, SymbolicReachabilityStatus,
    };

    fn compiled_summary(tag: u64) -> BackwardConditionSummary {
        BackwardConditionSummary {
            simplified: format!("cond_{tag}"),
            terms: vec![format!("term_{tag}")],
            memory_terms: vec![BackwardMemoryCondition {
                region: BackwardMemoryRegion::Argument { index: 0 },
                offset_lo: tag as i64,
                offset_hi: tag as i64,
                size: 8,
                exact_offset: true,
                evidence: SemanticEvidence::exact(),
                binding: Some(format!("arg0_{tag}")),
                expr: format!("*(arg0 + 0x{tag:x})"),
                value_expr: None,
                exact_value: false,
            }],
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: BackwardConditionPrecision::Exact,
            supported_paths: 1,
            total_paths: 1,
        }
    }

    fn worker_body(regions: impl IntoIterator<Item = SemanticRegion>) -> NativeArtifactBody {
        NativeArtifactBody {
            summary: NativeFunctionSummary {
                slice_class: SliceClass::Worker,
                closure_functions: 0,
                helper_functions: 0,
                derived_summaries: 0,
                derived_diagnostics: DerivedSummaryDiagnostics::default(),
            },
            regions: regions
                .into_iter()
                .map(|region| {
                    (
                        RegionKey::new(region.anchor, region.frontier.clone()),
                        region,
                    )
                })
                .collect(),
        }
    }

    fn guided_region(anchor: u64, target: u64, branch_truth: bool) -> SemanticRegion {
        let compiled = compiled_summary(anchor ^ target);
        SemanticRegion {
            anchor,
            frontier: BTreeSet::from([target]),
            control: vec![Judged::new(
                ControlFact {
                    target,
                    status: SymbolicReachabilityStatus::Reachable,
                    branch_truth: Some(branch_truth),
                    condition: Some(compiled.simplified.clone()),
                    compiled: Some(compiled.clone()),
                },
                SemanticEvidence::exact(),
            )],
            memory: compiled
                .memory_terms
                .iter()
                .cloned()
                .map(|term| Judged::new(MemoryFact { term }, SemanticEvidence::exact()))
                .collect(),
            pre: Vec::new(),
            post: Vec::new(),
            targets: vec![Judged::new(
                TargetFact {
                    target,
                    status: SymbolicReachabilityStatus::Reachable,
                    branch_truth: Some(branch_truth),
                },
                SemanticEvidence::exact(),
            )],
        }
    }

    proptest! {
        #[test]
        fn conflicting_targets_are_reported_deterministically(
            targets in proptest::collection::vec(0x401000u64..0x401100, 1..6),
        ) {
            let regions = targets
                .iter()
                .enumerate()
                .flat_map(|(idx, target)| {
                    [
                        guided_region(0x5000 + (idx as u64) * 2, *target, true),
                        guided_region(0x5001 + (idx as u64) * 2, *target, false),
                    ]
                })
                .collect::<Vec<_>>();
            let reversed = regions.iter().cloned().rev().collect::<Vec<_>>();
            let expected = targets
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();

            let forward = worker_body(regions);
            let backward = worker_body(reversed);

            prop_assert_eq!(
                forward.conflicting_targets(false).into_iter().collect::<Vec<_>>(),
                expected
            );
            prop_assert_eq!(forward.conflicting_targets(false), backward.conflicting_targets(false));
        }
    }

    #[test]
    fn conflicting_target_sources_disable_guidance_and_structuring() {
        let body = worker_body([
            guided_region(0x401000, 0x401100, true),
            guided_region(0x401010, 0x401100, false),
        ]);

        assert!(body.target_source_conflict(0x401100, false));
        assert!(!body.has_target_guidance(0x401100, false));
        assert!(!body.supports_guarded_structuring());
    }
}
