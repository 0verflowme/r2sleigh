use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use r2il::ArchSpec;
use r2ssa::{InterprocFunctionId, SsaArtifact};
use serde::{Deserialize, Serialize};
use z3::Context;

use crate::SymState;
use crate::backward::{
    BackwardConditionPrecision, BackwardConditionSummary, BackwardMemoryCondition,
    compile_branch_precondition_with_summaries,
};
use crate::path::{ExploreConfig, PathExplorer};
use crate::runtime::seed_default_state_for_arch;
use crate::semantics::{
    SemanticConfidence, SemanticEvidence, SemanticEvidenceCoverage, SemanticEvidenceProvenance,
    SemanticEvidenceReason,
};
use crate::sim::{
    DerivedSummaryCompletion, DerivedSummarySet, PreparedFunctionScope, SummaryProfile,
    SummaryRegistry,
};
use crate::solver::SatResult;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolicReachabilityStatus {
    Reachable,
    Unreachable,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicBranchFact {
    pub block_addr: u64,
    pub true_target: u64,
    pub false_target: u64,
    pub true_status: SymbolicReachabilityStatus,
    pub false_status: SymbolicReachabilityStatus,
    pub true_condition: Option<String>,
    pub false_condition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub true_compiled: Option<BackwardConditionSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub false_compiled: Option<BackwardConditionSummary>,
}

impl SymbolicBranchFact {
    pub fn exact_reachable_target(&self) -> Option<u64> {
        match (self.true_status, self.false_status) {
            (SymbolicReachabilityStatus::Reachable, SymbolicReachabilityStatus::Unreachable) => {
                Some(self.true_target)
            }
            (SymbolicReachabilityStatus::Unreachable, SymbolicReachabilityStatus::Reachable) => {
                Some(self.false_target)
            }
            _ => None,
        }
    }

    pub fn actionable_reachable_target(&self) -> Option<u64> {
        match (self.true_status, self.false_status) {
            (SymbolicReachabilityStatus::Reachable, SymbolicReachabilityStatus::Unreachable)
                if self
                    .true_compiled
                    .as_ref()
                    .is_some_and(|compiled| compiled.evidence().allows_narrowing()) =>
            {
                Some(self.true_target)
            }
            (SymbolicReachabilityStatus::Unreachable, SymbolicReachabilityStatus::Reachable)
                if self
                    .false_compiled
                    .as_ref()
                    .is_some_and(|compiled| compiled.evidence().allows_narrowing()) =>
            {
                Some(self.false_target)
            }
            _ => None,
        }
    }

    pub fn exact_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        match (self.true_status, self.false_status) {
            (SymbolicReachabilityStatus::Reachable, SymbolicReachabilityStatus::Unreachable) => {
                self.true_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence().allows_hard_proof())
            }
            (SymbolicReachabilityStatus::Unreachable, SymbolicReachabilityStatus::Reachable) => {
                self.false_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence().allows_hard_proof())
            }
            _ => None,
        }
    }

    pub fn actionable_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        match (self.true_status, self.false_status) {
            (SymbolicReachabilityStatus::Reachable, SymbolicReachabilityStatus::Unreachable) => {
                self.true_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence().allows_narrowing())
            }
            (SymbolicReachabilityStatus::Unreachable, SymbolicReachabilityStatus::Reachable) => {
                self.false_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence().allows_narrowing())
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolicControlIslandKind {
    BranchFrontier,
    LargeCfgBranchFrontier,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolicMemoryIslandKind {
    ConditionFrontier,
    LargeCfgConditionFrontier,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicControlFact {
    pub target: u64,
    pub status: SymbolicReachabilityStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiled: Option<BackwardConditionSummary>,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl SymbolicControlFact {
    pub fn exact_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        self.evidence
            .allows_hard_proof()
            .then_some(self.compiled.as_ref())
            .flatten()
    }

    pub fn actionable_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        self.evidence
            .allows_narrowing()
            .then_some(self.compiled.as_ref())
            .flatten()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicControlIsland {
    pub kind: SymbolicControlIslandKind,
    pub anchor_block: u64,
    pub frontier_targets: Vec<u64>,
    pub facts: Vec<SymbolicControlFact>,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl SymbolicControlIsland {
    pub fn exact_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        unique_compiled_condition(self.facts.iter(), true)
    }

    pub fn actionable_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        unique_compiled_condition(self.facts.iter(), false)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicMemoryIsland {
    pub kind: SymbolicMemoryIslandKind,
    pub anchor_block: u64,
    pub terms: Vec<BackwardMemoryCondition>,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl SymbolicMemoryIsland {
    pub fn exact_terms(&self) -> Vec<&BackwardMemoryCondition> {
        self.terms
            .iter()
            .filter(|term| term.evidence().allows_hard_proof())
            .collect()
    }

    pub fn actionable_terms(&self) -> Vec<&BackwardMemoryCondition> {
        self.terms
            .iter()
            .filter(|term| term.evidence().allows_narrowing())
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicWorkerIsland {
    pub anchor_block: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub control_kind: Option<SymbolicControlIslandKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub memory_kind: Option<SymbolicMemoryIslandKind>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub frontier_targets: Vec<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub control_facts: Vec<SymbolicControlFact>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory_terms: Vec<BackwardMemoryCondition>,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
}

impl SymbolicWorkerIsland {
    pub fn exact_reachable_target(&self) -> Option<u64> {
        unique_reachable_control_target(self.control_facts.iter(), true)
    }

    pub fn actionable_reachable_target(&self) -> Option<u64> {
        unique_reachable_control_target(self.control_facts.iter(), false)
    }

    pub fn exact_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        unique_compiled_condition(self.control_facts.iter(), true)
    }

    pub fn actionable_compiled_condition(&self) -> Option<&BackwardConditionSummary> {
        unique_compiled_condition(self.control_facts.iter(), false)
    }

    pub fn exact_memory_terms(&self) -> Vec<&BackwardMemoryCondition> {
        self.memory_terms
            .iter()
            .filter(|term| term.evidence().allows_hard_proof())
            .collect()
    }

    pub fn actionable_memory_terms(&self) -> Vec<&BackwardMemoryCondition> {
        self.memory_terms
            .iter()
            .filter(|term| term.evidence().allows_narrowing())
            .collect()
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicFunctionFactDiagnostics {
    pub branches_evaluated: usize,
    pub branches_pruned: usize,
    pub branches_unknown: usize,
    pub skipped_missing_arch: bool,
    pub skipped_large_cfg: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicFunctionFacts {
    pub branch_facts: Vec<SymbolicBranchFact>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub worker_islands: Vec<SymbolicWorkerIsland>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub control_islands: Vec<SymbolicControlIsland>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory_islands: Vec<SymbolicMemoryIsland>,
    pub diagnostics: SymbolicFunctionFactDiagnostics,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolicTargetConditionSource<'a> {
    pub block_addr: u64,
    pub branch_truth: bool,
    pub summary: &'a BackwardConditionSummary,
    pub necessary_for_target: bool,
}

impl SymbolicFunctionFacts {
    pub fn branch_fact_for_block(&self, block_addr: u64) -> Option<&SymbolicBranchFact> {
        self.branch_facts
            .iter()
            .find(|fact| fact.block_addr == block_addr)
    }

    pub fn worker_island_for_block(&self, block_addr: u64) -> Option<&SymbolicWorkerIsland> {
        self.worker_islands
            .iter()
            .find(|island| island.anchor_block == block_addr)
    }

    pub fn best_worker_island_for_target(
        &self,
        target_addr: u64,
        hard_proof_only: bool,
    ) -> Option<&SymbolicWorkerIsland> {
        best_worker_island_for_target(self, target_addr, hard_proof_only)
    }

    pub fn control_island_for_block(&self, block_addr: u64) -> Option<&SymbolicControlIsland> {
        self.control_islands
            .iter()
            .find(|island| island.anchor_block == block_addr)
    }

    pub fn memory_island_for_block(&self, block_addr: u64) -> Option<&SymbolicMemoryIsland> {
        self.memory_islands
            .iter()
            .find(|island| island.anchor_block == block_addr)
    }

    pub fn actionable_memory_terms_for_block(
        &self,
        block_addr: u64,
    ) -> Vec<&BackwardMemoryCondition> {
        self.worker_island_for_block(block_addr)
            .map(SymbolicWorkerIsland::actionable_memory_terms)
            .or_else(|| {
                self.memory_island_for_block(block_addr)
                    .map(SymbolicMemoryIsland::actionable_terms)
            })
            .unwrap_or_default()
    }

    pub fn actionable_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        target_compiled_condition(self, target_addr, false)
    }

    pub fn exact_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&BackwardConditionSummary> {
        target_compiled_condition(self, target_addr, true)
    }

    pub fn actionable_condition_source_for_target(
        &self,
        target_addr: u64,
    ) -> Option<SymbolicTargetConditionSource<'_>> {
        target_condition_source(self, target_addr, false)
    }

    pub fn exact_condition_source_for_target(
        &self,
        target_addr: u64,
    ) -> Option<SymbolicTargetConditionSource<'_>> {
        target_condition_source(self, target_addr, true)
    }

    pub fn actionable_memory_terms_for_target(
        &self,
        target_addr: u64,
    ) -> Vec<&BackwardMemoryCondition> {
        self.actionable_condition_source_for_target(target_addr)
            .map(|source| self.actionable_memory_terms_for_block(source.block_addr))
            .or_else(|| {
                best_worker_island_for_target(self, target_addr, false)
                    .map(SymbolicWorkerIsland::actionable_memory_terms)
            })
            .or_else(|| {
                best_legacy_memory_island_for_target(self, target_addr)
                    .map(SymbolicMemoryIsland::actionable_terms)
            })
            .unwrap_or_default()
    }

    pub fn exact_memory_terms_for_target(&self, target_addr: u64) -> Vec<&BackwardMemoryCondition> {
        self.exact_condition_source_for_target(target_addr)
            .and_then(|source| self.worker_island_for_block(source.block_addr))
            .map(SymbolicWorkerIsland::exact_memory_terms)
            .or_else(|| {
                best_worker_island_for_target(self, target_addr, true)
                    .map(SymbolicWorkerIsland::exact_memory_terms)
            })
            .or_else(|| {
                best_legacy_memory_island_for_target(self, target_addr)
                    .map(SymbolicMemoryIsland::exact_terms)
            })
            .unwrap_or_default()
    }
}

fn control_fact_evidence(
    summary: Option<&BackwardConditionSummary>,
    condition: Option<&str>,
    diagnostics: &SymbolicFunctionFactDiagnostics,
) -> SemanticEvidence {
    let branch_budget_limited = diagnostics.skipped_large_cfg;
    match summary {
        Some(summary) => match summary.precision {
            BackwardConditionPrecision::Exact => summary.evidence(),
            BackwardConditionPrecision::OverApprox => summary
                .evidence()
                .with_budget_limited(branch_budget_limited)
                .with_reason(SemanticEvidenceReason::PartialPathCoverage),
            BackwardConditionPrecision::ResidualSearchRequired => {
                let simplified = summary.simplified.trim();
                let has_guard = !simplified.is_empty() && simplified != "true" && simplified != "1";
                if summary.supported_paths > 0
                    && has_guard
                    && summary.backward_memory_residual_fallbacks == 0
                {
                    SemanticEvidence::likely(SemanticEvidenceReason::ResidualSearchRequired)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_provenance(SemanticEvidenceProvenance::Normalized)
                        .with_budget_limited(branch_budget_limited)
                        .with_reason(SemanticEvidenceReason::PartialPathCoverage)
                } else if summary.supported_paths > 0 && has_guard {
                    SemanticEvidence::heuristic(SemanticEvidenceReason::ResidualSearchRequired)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_provenance(SemanticEvidenceProvenance::Normalized)
                        .with_budget_limited(branch_budget_limited)
                } else if condition.is_some() {
                    SemanticEvidence::heuristic(SemanticEvidenceReason::GuardOpaque)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_budget_limited(branch_budget_limited)
                } else {
                    SemanticEvidence::residual(SemanticEvidenceReason::ResidualSearchRequired)
                        .with_budget_limited(branch_budget_limited)
                }
            }
            BackwardConditionPrecision::Unsupported => {
                if condition.is_some() {
                    SemanticEvidence::heuristic(SemanticEvidenceReason::GuardOpaque)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_budget_limited(branch_budget_limited)
                } else {
                    SemanticEvidence::residual(SemanticEvidenceReason::ValueOpaque)
                        .with_budget_limited(branch_budget_limited)
                }
            }
        },
        None => condition
            .map(|_| {
                SemanticEvidence::heuristic(SemanticEvidenceReason::GuardOpaque)
                    .with_coverage(SemanticEvidenceCoverage::Bounded)
                    .with_budget_limited(branch_budget_limited)
            })
            .unwrap_or_else(|| {
                SemanticEvidence::residual(SemanticEvidenceReason::GuardOpaque)
                    .with_budget_limited(branch_budget_limited)
            }),
    }
}

fn island_evidence(facts: &[SymbolicControlFact]) -> SemanticEvidence {
    facts
        .iter()
        .map(|fact| fact.evidence.clone())
        .max_by_key(|evidence| {
            (
                match evidence.tier {
                    SemanticConfidence::Exact => 3,
                    SemanticConfidence::Likely => 2,
                    SemanticConfidence::Heuristic => 1,
                    SemanticConfidence::Residual => 0,
                },
                evidence.allows_hard_proof() as u8,
                evidence.allows_narrowing() as u8,
            )
        })
        .unwrap_or_else(|| SemanticEvidence::residual(SemanticEvidenceReason::GuardOpaque))
}

fn memory_island_evidence(terms: &[BackwardMemoryCondition]) -> SemanticEvidence {
    terms
        .iter()
        .map(BackwardMemoryCondition::evidence)
        .max_by_key(|evidence| {
            (
                match evidence.tier {
                    SemanticConfidence::Exact => 3,
                    SemanticConfidence::Likely => 2,
                    SemanticConfidence::Heuristic => 1,
                    SemanticConfidence::Residual => 0,
                },
                evidence.allows_hard_proof() as u8,
                evidence.allows_narrowing() as u8,
            )
        })
        .unwrap_or_else(|| SemanticEvidence::residual(SemanticEvidenceReason::ValueOpaque))
}

fn unique_compiled_condition<'a>(
    facts: impl Iterator<Item = &'a SymbolicControlFact>,
    hard_proof_only: bool,
) -> Option<&'a BackwardConditionSummary> {
    let mut candidates = facts.filter_map(|fact| {
        if hard_proof_only {
            fact.exact_compiled_condition()
        } else {
            fact.actionable_compiled_condition()
        }
    });
    let first = candidates.next()?;
    candidates.next().is_none().then_some(first)
}

fn unique_reachable_control_target<'a>(
    facts: impl Iterator<Item = &'a SymbolicControlFact>,
    hard_proof_only: bool,
) -> Option<u64> {
    let mut candidates = facts.filter_map(|fact| {
        let condition = if hard_proof_only {
            fact.evidence.allows_hard_proof()
        } else {
            fact.evidence.allows_narrowing()
        };
        condition
            .then_some(matches!(fact.status, SymbolicReachabilityStatus::Reachable))
            .and_then(|reachable| reachable.then_some(fact.target))
    });
    let first = candidates.next()?;
    candidates.next().is_none().then_some(first)
}

fn summary_precision_rank(summary: &BackwardConditionSummary) -> u8 {
    match summary.precision {
        BackwardConditionPrecision::Exact => 3,
        BackwardConditionPrecision::OverApprox => 2,
        BackwardConditionPrecision::ResidualSearchRequired => 1,
        BackwardConditionPrecision::Unsupported => 0,
    }
}

fn summary_evidence_rank(summary: &BackwardConditionSummary) -> u8 {
    match summary.evidence().tier {
        SemanticConfidence::Exact => 3,
        SemanticConfidence::Likely => 2,
        SemanticConfidence::Heuristic => 1,
        SemanticConfidence::Residual => 0,
    }
}

fn best_target_compiled_condition<'a>(
    candidates: impl Iterator<Item = &'a BackwardConditionSummary>,
) -> Option<&'a BackwardConditionSummary> {
    candidates.max_by(|left, right| {
        (
            summary_evidence_rank(left),
            summary_precision_rank(left),
            std::cmp::Reverse(left.backward_memory_residual_fallbacks),
            left.memory_terms.len(),
            left.supported_paths,
            std::cmp::Reverse(left.total_paths),
            std::cmp::Reverse(left.simplified.len()),
        )
            .cmp(&(
                summary_evidence_rank(right),
                summary_precision_rank(right),
                std::cmp::Reverse(right.backward_memory_residual_fallbacks),
                right.memory_terms.len(),
                right.supported_paths,
                std::cmp::Reverse(right.total_paths),
                std::cmp::Reverse(right.simplified.len()),
            ))
    })
}

fn target_compiled_condition(
    facts: &SymbolicFunctionFacts,
    target_addr: u64,
    hard_proof_only: bool,
) -> Option<&BackwardConditionSummary> {
    let branch_candidates = facts.branch_facts.iter().flat_map(|fact| {
        let mut candidates = Vec::new();
        if fact.true_target == target_addr {
            let compiled = if hard_proof_only {
                fact.true_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence().allows_hard_proof())
            } else {
                fact.true_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence().allows_narrowing())
            };
            if let Some(compiled) = compiled {
                candidates.push(compiled);
            }
        }
        if fact.false_target == target_addr {
            let compiled = if hard_proof_only {
                fact.false_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence().allows_hard_proof())
            } else {
                fact.false_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence().allows_narrowing())
            };
            if let Some(compiled) = compiled {
                candidates.push(compiled);
            }
        }
        candidates
    });
    let control_candidates = facts
        .worker_islands
        .iter()
        .flat_map(|island| island.control_facts.iter())
        .chain(
            facts
                .control_islands
                .iter()
                .flat_map(|island| island.facts.iter()),
        )
        .filter_map(move |fact| {
            (fact.target == target_addr)
                .then_some(if hard_proof_only {
                    fact.exact_compiled_condition()
                } else {
                    fact.actionable_compiled_condition()
                })
                .flatten()
        });
    best_target_compiled_condition(branch_candidates.chain(control_candidates))
}

fn best_worker_island_for_target(
    facts: &SymbolicFunctionFacts,
    target_addr: u64,
    hard_proof_only: bool,
) -> Option<&SymbolicWorkerIsland> {
    facts
        .worker_islands
        .iter()
        .filter(|island| {
            island.control_facts.iter().any(|fact| {
                fact.target == target_addr
                    && if hard_proof_only {
                        fact.evidence.allows_hard_proof()
                    } else {
                        fact.evidence.allows_narrowing()
                    }
            })
        })
        .max_by(|left, right| {
            (
                left.evidence.allows_hard_proof() as u8,
                left.evidence.allows_narrowing() as u8,
                left.evidence.tier,
                left.memory_terms.len(),
                left.control_facts.len(),
            )
                .cmp(&(
                    right.evidence.allows_hard_proof() as u8,
                    right.evidence.allows_narrowing() as u8,
                    right.evidence.tier,
                    right.memory_terms.len(),
                    right.control_facts.len(),
                ))
        })
}

fn best_legacy_memory_island_for_target(
    facts: &SymbolicFunctionFacts,
    target_addr: u64,
) -> Option<&SymbolicMemoryIsland> {
    facts
        .branch_facts
        .iter()
        .filter(|fact| fact.true_target == target_addr || fact.false_target == target_addr)
        .filter_map(|fact| facts.memory_island_for_block(fact.block_addr))
        .max_by(|left, right| {
            (
                left.evidence.allows_hard_proof() as u8,
                left.evidence.allows_narrowing() as u8,
                left.evidence.tier,
                left.terms.len(),
            )
                .cmp(&(
                    right.evidence.allows_hard_proof() as u8,
                    right.evidence.allows_narrowing() as u8,
                    right.evidence.tier,
                    right.terms.len(),
                ))
        })
}

fn target_condition_source(
    facts: &SymbolicFunctionFacts,
    target_addr: u64,
    hard_proof_only: bool,
) -> Option<SymbolicTargetConditionSource<'_>> {
    let branch_candidates = facts
        .branch_facts
        .iter()
        .filter_map(|fact| {
            let (branch_truth, compiled) = if fact.true_target == target_addr {
                let compiled = if hard_proof_only {
                    fact.true_compiled
                        .as_ref()
                        .filter(|compiled| compiled.evidence().allows_hard_proof())
                } else {
                    fact.true_compiled
                        .as_ref()
                        .filter(|compiled| compiled.evidence().allows_narrowing())
                };
                (Some(true), compiled)
            } else if fact.false_target == target_addr {
                let compiled = if hard_proof_only {
                    fact.false_compiled
                        .as_ref()
                        .filter(|compiled| compiled.evidence().allows_hard_proof())
                } else {
                    fact.false_compiled
                        .as_ref()
                        .filter(|compiled| compiled.evidence().allows_narrowing())
                };
                (Some(false), compiled)
            } else {
                (None, None)
            };
            Some(SymbolicTargetConditionSource {
                block_addr: fact.block_addr,
                branch_truth: branch_truth?,
                summary: compiled?,
                necessary_for_target: false,
            })
        })
        .collect::<Vec<_>>();
    if let Some(first) = branch_candidates.first().copied() {
        let necessary_for_target = branch_candidates.iter().all(|candidate| {
            candidate.block_addr == first.block_addr
                && candidate.branch_truth == first.branch_truth
                && candidate.summary == first.summary
        });
        if hard_proof_only && !necessary_for_target {
            return None;
        }
        let mut best = branch_candidates.into_iter().max_by(|left, right| {
            (
                summary_evidence_rank(left.summary),
                summary_precision_rank(left.summary),
                std::cmp::Reverse(left.summary.backward_memory_residual_fallbacks),
                left.summary.memory_terms.len(),
                left.summary.supported_paths,
                std::cmp::Reverse(left.summary.total_paths),
                std::cmp::Reverse(left.block_addr),
                left.branch_truth,
            )
                .cmp(&(
                    summary_evidence_rank(right.summary),
                    summary_precision_rank(right.summary),
                    std::cmp::Reverse(right.summary.backward_memory_residual_fallbacks),
                    right.summary.memory_terms.len(),
                    right.summary.supported_paths,
                    std::cmp::Reverse(right.summary.total_paths),
                    std::cmp::Reverse(right.block_addr),
                    right.branch_truth,
                ))
        })?;
        best.necessary_for_target = necessary_for_target;
        return Some(best);
    }

    let candidates = facts
        .worker_islands
        .iter()
        .filter_map(|island| {
            let branch = facts.branch_fact_for_block(island.anchor_block)?;
            let necessary_for_target = if hard_proof_only {
                island.exact_reachable_target() == Some(target_addr)
            } else {
                island.actionable_reachable_target() == Some(target_addr)
            };
            island.control_facts.iter().find_map(|fact| {
                if fact.target != target_addr {
                    return None;
                }
                let summary = if hard_proof_only {
                    fact.exact_compiled_condition()
                } else {
                    fact.actionable_compiled_condition()
                }?;
                let branch_truth = if branch.true_target == target_addr {
                    Some(true)
                } else if branch.false_target == target_addr {
                    Some(false)
                } else {
                    None
                }?;
                Some(SymbolicTargetConditionSource {
                    block_addr: island.anchor_block,
                    branch_truth,
                    summary,
                    necessary_for_target,
                })
            })
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return None;
    }
    if hard_proof_only
        && candidates
            .iter()
            .any(|candidate| !candidate.necessary_for_target)
    {
        return None;
    }
    candidates.into_iter().max_by(|left, right| {
        (
            left.necessary_for_target as u8,
            summary_evidence_rank(left.summary),
            summary_precision_rank(left.summary),
            left.summary.memory_terms.len(),
            left.summary.supported_paths,
            std::cmp::Reverse(left.summary.total_paths),
            std::cmp::Reverse(left.block_addr),
            left.branch_truth,
        )
            .cmp(&(
                right.necessary_for_target as u8,
                summary_evidence_rank(right.summary),
                summary_precision_rank(right.summary),
                right.summary.memory_terms.len(),
                right.summary.supported_paths,
                std::cmp::Reverse(right.summary.total_paths),
                std::cmp::Reverse(right.block_addr),
                right.branch_truth,
            ))
    })
}

fn default_control_island_kind(
    diagnostics: &SymbolicFunctionFactDiagnostics,
) -> SymbolicControlIslandKind {
    if diagnostics.skipped_large_cfg {
        SymbolicControlIslandKind::LargeCfgBranchFrontier
    } else {
        SymbolicControlIslandKind::BranchFrontier
    }
}

fn control_facts_for_branch(
    branch: &SymbolicBranchFact,
    diagnostics: &SymbolicFunctionFactDiagnostics,
) -> Vec<SymbolicControlFact> {
    vec![
        SymbolicControlFact {
            target: branch.true_target,
            status: branch.true_status,
            condition: branch.true_condition.clone(),
            compiled: branch.true_compiled.clone(),
            evidence: control_fact_evidence(
                branch.true_compiled.as_ref(),
                branch.true_condition.as_deref(),
                diagnostics,
            ),
        },
        SymbolicControlFact {
            target: branch.false_target,
            status: branch.false_status,
            condition: branch.false_condition.clone(),
            compiled: branch.false_compiled.clone(),
            evidence: control_fact_evidence(
                branch.false_compiled.as_ref(),
                branch.false_condition.as_deref(),
                diagnostics,
            ),
        },
    ]
}

fn derived_summary_memory_term_evidence(
    completion: DerivedSummaryCompletion,
    exact_value: bool,
) -> SemanticEvidence {
    match completion {
        DerivedSummaryCompletion::Exact if exact_value => SemanticEvidence::exact(),
        DerivedSummaryCompletion::Exact => SemanticEvidence::exact(),
        DerivedSummaryCompletion::OverApprox => {
            SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
                .with_provenance(SemanticEvidenceProvenance::Normalized)
        }
        DerivedSummaryCompletion::BudgetExhausted => {
            SemanticEvidence::heuristic(SemanticEvidenceReason::SummaryBudget)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
                .with_provenance(SemanticEvidenceProvenance::Normalized)
                .with_budget_limited(true)
        }
        DerivedSummaryCompletion::Unknown => {
            SemanticEvidence::heuristic(SemanticEvidenceReason::ValueOpaque)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
        }
    }
}

fn merge_memory_islands(
    mut islands: Vec<SymbolicMemoryIsland>,
    additions: impl IntoIterator<Item = SymbolicMemoryIsland>,
) -> Vec<SymbolicMemoryIsland> {
    let mut by_anchor = BTreeMap::<u64, SymbolicMemoryIsland>::new();
    for island in islands.drain(..).chain(additions) {
        let entry = by_anchor
            .entry(island.anchor_block)
            .or_insert_with(|| SymbolicMemoryIsland {
                kind: island.kind,
                anchor_block: island.anchor_block,
                terms: Vec::new(),
                evidence: island.evidence.clone(),
            });
        if matches!(entry.kind, SymbolicMemoryIslandKind::ConditionFrontier)
            && matches!(
                island.kind,
                SymbolicMemoryIslandKind::LargeCfgConditionFrontier
            )
        {
            entry.kind = island.kind;
        }
        for term in island.terms {
            if !entry.terms.contains(&term) {
                entry.terms.push(term);
            }
        }
        entry.evidence = memory_island_evidence(&entry.terms);
    }
    by_anchor.into_values().collect()
}

fn push_unique_memory_terms(
    dst: &mut Vec<BackwardMemoryCondition>,
    terms: impl IntoIterator<Item = BackwardMemoryCondition>,
) {
    for term in terms {
        if !dst.contains(&term) {
            dst.push(term);
        }
    }
}

fn worker_island_evidence(
    control_facts: &[SymbolicControlFact],
    memory_terms: &[BackwardMemoryCondition],
) -> SemanticEvidence {
    let control = island_evidence(control_facts);
    let memory = memory_island_evidence(memory_terms);
    let control_rank = (
        control.allows_hard_proof() as u8,
        control.allows_narrowing() as u8,
        match control.tier {
            SemanticConfidence::Exact => 3,
            SemanticConfidence::Likely => 2,
            SemanticConfidence::Heuristic => 1,
            SemanticConfidence::Residual => 0,
        },
    );
    let memory_rank = (
        memory.allows_hard_proof() as u8,
        memory.allows_narrowing() as u8,
        match memory.tier {
            SemanticConfidence::Exact => 3,
            SemanticConfidence::Likely => 2,
            SemanticConfidence::Heuristic => 1,
            SemanticConfidence::Residual => 0,
        },
    );
    if memory_rank > control_rank {
        memory
    } else {
        control
    }
}

fn derive_worker_islands(
    branch_facts: &[SymbolicBranchFact],
    preseeded_memory_islands: &[SymbolicMemoryIsland],
    diagnostics: &SymbolicFunctionFactDiagnostics,
) -> Vec<SymbolicWorkerIsland> {
    let mut by_anchor = BTreeMap::<u64, SymbolicWorkerIsland>::new();
    for branch in branch_facts {
        let entry = by_anchor
            .entry(branch.block_addr)
            .or_insert_with(|| SymbolicWorkerIsland {
                anchor_block: branch.block_addr,
                control_kind: None,
                memory_kind: None,
                frontier_targets: Vec::new(),
                control_facts: Vec::new(),
                memory_terms: Vec::new(),
                evidence: SemanticEvidence::residual(SemanticEvidenceReason::GuardOpaque),
            });
        entry.control_kind = Some(default_control_island_kind(diagnostics));
        entry.frontier_targets = vec![branch.true_target, branch.false_target];
        entry.control_facts = control_facts_for_branch(branch, diagnostics);
        push_unique_memory_terms(
            &mut entry.memory_terms,
            entry
                .control_facts
                .iter()
                .filter_map(SymbolicControlFact::actionable_compiled_condition)
                .flat_map(|compiled| compiled.memory_terms.iter().cloned()),
        );
        entry.evidence = worker_island_evidence(&entry.control_facts, &entry.memory_terms);
    }
    for island in preseeded_memory_islands {
        let entry = by_anchor
            .entry(island.anchor_block)
            .or_insert_with(|| SymbolicWorkerIsland {
                anchor_block: island.anchor_block,
                control_kind: None,
                memory_kind: None,
                frontier_targets: Vec::new(),
                control_facts: Vec::new(),
                memory_terms: Vec::new(),
                evidence: island.evidence.clone(),
            });
        entry.memory_kind = Some(island.kind);
        push_unique_memory_terms(&mut entry.memory_terms, island.terms.iter().cloned());
        entry.evidence = worker_island_evidence(&entry.control_facts, &entry.memory_terms);
    }
    by_anchor.into_values().collect()
}

fn project_control_islands(worker_islands: &[SymbolicWorkerIsland]) -> Vec<SymbolicControlIsland> {
    worker_islands
        .iter()
        .filter(|island| !island.control_facts.is_empty())
        .map(|island| SymbolicControlIsland {
            kind: island
                .control_kind
                .unwrap_or(SymbolicControlIslandKind::BranchFrontier),
            anchor_block: island.anchor_block,
            frontier_targets: island.frontier_targets.clone(),
            facts: island.control_facts.clone(),
            evidence: island_evidence(&island.control_facts),
        })
        .collect()
}

fn project_memory_islands(worker_islands: &[SymbolicWorkerIsland]) -> Vec<SymbolicMemoryIsland> {
    worker_islands
        .iter()
        .filter(|island| !island.memory_terms.is_empty())
        .map(|island| SymbolicMemoryIsland {
            kind: island
                .memory_kind
                .unwrap_or(SymbolicMemoryIslandKind::ConditionFrontier),
            anchor_block: island.anchor_block,
            terms: island.memory_terms.clone(),
            evidence: memory_island_evidence(&island.memory_terms),
        })
        .collect()
}

fn summary_memory_location_expr(arg_index: usize, offset: i64) -> String {
    if offset == 0 {
        format!("*arg{arg_index}")
    } else if offset > 0 {
        format!("*(arg{arg_index} + 0x{:x})", offset as u64)
    } else {
        format!("*(arg{arg_index} - 0x{:x})", offset.unsigned_abs())
    }
}

fn derive_summary_memory_islands<'ctx>(
    func: &SsaArtifact,
    branch_blocks: &[(u64, u64, u64)],
    derived: &DerivedSummarySet<'ctx>,
    diagnostics: &SymbolicFunctionFactDiagnostics,
) -> Vec<SymbolicMemoryIsland> {
    let hot_blocks = branch_blocks
        .iter()
        .flat_map(|(block, true_target, false_target)| [*block, *true_target, *false_target])
        .collect::<BTreeSet<_>>();
    let mut by_anchor = BTreeMap::<u64, Vec<BackwardMemoryCondition>>::new();
    let max_islands = branch_blocks.len().max(1) * 3;

    let mut call_blocks = func
        .call_sites()
        .by_id
        .values()
        .filter_map(|call| {
            let target = call.direct_target?;
            let summary = derived.summaries.get(&InterprocFunctionId(target))?;
            if summary
                .cases
                .iter()
                .all(|case| case.memory_writes.is_empty())
            {
                return None;
            }
            let (block_addr, _) = func.inst_op_site(call.at)?;
            Some((!hot_blocks.contains(&block_addr), block_addr, summary))
        })
        .collect::<Vec<_>>();
    call_blocks.sort_by_key(|(cold_block, block_addr, _)| (*cold_block, *block_addr));

    for (_, block_addr, summary) in call_blocks.into_iter().take(max_islands) {
        let terms = by_anchor.entry(block_addr).or_default();
        for case in &summary.cases {
            for write in &case.memory_writes {
                let exact_value = write.value.is_concrete();
                let evidence =
                    derived_summary_memory_term_evidence(summary.completion, exact_value);
                let term = BackwardMemoryCondition {
                    region: crate::BackwardMemoryRegion::Argument {
                        index: write.arg_index,
                    },
                    offset_lo: write.offset,
                    offset_hi: write.offset,
                    size: write.size,
                    exact_offset: matches!(summary.completion, DerivedSummaryCompletion::Exact),
                    evidence,
                    binding: None,
                    expr: summary_memory_location_expr(write.arg_index, write.offset),
                    value_expr: Some(write.value.to_string()),
                    exact_value,
                };
                if !terms.contains(&term) {
                    terms.push(term);
                }
            }
        }
    }

    by_anchor
        .into_iter()
        .filter_map(|(anchor_block, terms)| {
            (!terms.is_empty()).then(|| SymbolicMemoryIsland {
                kind: if diagnostics.skipped_large_cfg {
                    SymbolicMemoryIslandKind::LargeCfgConditionFrontier
                } else {
                    SymbolicMemoryIslandKind::ConditionFrontier
                },
                anchor_block,
                evidence: memory_island_evidence(&terms),
                terms,
            })
        })
        .collect()
}

fn finalize_symbolic_function_facts(mut facts: SymbolicFunctionFacts) -> SymbolicFunctionFacts {
    let preseeded_memory_islands = std::mem::take(&mut facts.memory_islands);
    facts.worker_islands = derive_worker_islands(
        &facts.branch_facts,
        &preseeded_memory_islands,
        &facts.diagnostics,
    );
    facts.control_islands = project_control_islands(&facts.worker_islands);
    facts.memory_islands = project_memory_islands(&facts.worker_islands);
    facts
}

fn symbolic_condition_hint(summary: Option<&BackwardConditionSummary>) -> Option<String> {
    summary
        .map(|compiled| compiled.simplified.trim().to_string())
        .filter(|text| !text.is_empty() && text != "true")
}

fn symbolic_fact_explorer<'ctx>(ctx: &'ctx Context) -> PathExplorer<'ctx> {
    let mut explorer = PathExplorer::with_config(
        ctx,
        ExploreConfig {
            subsumption_states: true,
            max_states: 256,
            max_depth: 96,
            max_completed_paths: Some(8),
            merge_states: false,
            ..ExploreConfig::default()
        },
    );
    explorer.set_target_guided_queries(true);
    explorer
}

fn collect_branch_blocks(func: &SsaArtifact) -> Vec<(u64, u64, u64)> {
    func.cfg()
        .block_addrs()
        .filter_map(|block_addr| {
            let block = func.cfg().get_block(block_addr)?;
            match block.terminator {
                r2ssa::BlockTerminator::ConditionalBranch {
                    true_target,
                    false_target,
                } => Some((block_addr, true_target, false_target)),
                _ => None,
            }
        })
        .collect()
}

fn large_cfg_branch_limit(func: &SsaArtifact) -> usize {
    let summary = func.function().cfg_risk_summary();
    match summary.switch_block_count {
        0 => 8,
        1..=2 => 10,
        _ => 12,
    }
}

fn limited_branch_blocks(func: &SsaArtifact, limit: usize) -> Vec<(u64, u64, u64)> {
    if limit == 0 {
        return Vec::new();
    }

    let mut queue = VecDeque::from([func.entry]);
    let mut visited = BTreeSet::new();
    let mut selected = Vec::new();

    while let Some(block_addr) = queue.pop_front() {
        if !visited.insert(block_addr) {
            continue;
        }

        if let Some(block) = func.cfg().get_block(block_addr)
            && let r2ssa::BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } = block.terminator
        {
            selected.push((block_addr, true_target, false_target));
            if selected.len() >= limit {
                break;
            }
        }

        for successor in func.successors(block_addr) {
            if !visited.contains(&successor) {
                queue.push_back(successor);
            }
        }
    }

    if selected.is_empty() {
        collect_branch_blocks(func)
            .into_iter()
            .take(limit)
            .collect()
    } else {
        selected
    }
}

fn symbolic_reachability_status(
    feasible_paths: usize,
    budget_exhausted: bool,
) -> SymbolicReachabilityStatus {
    if feasible_paths > 0 {
        SymbolicReachabilityStatus::Reachable
    } else if budget_exhausted {
        SymbolicReachabilityStatus::Unknown
    } else {
        SymbolicReachabilityStatus::Unreachable
    }
}

fn collect_symbolic_function_facts_for_branch_blocks<'ctx, F>(
    ctx: &'ctx Context,
    func: &SsaArtifact,
    arch: &ArchSpec,
    branch_blocks: &[(u64, u64, u64)],
    install_hooks: F,
) -> SymbolicFunctionFacts
where
    F: Fn(&mut PathExplorer<'ctx>),
{
    let mut facts = SymbolicFunctionFacts::default();

    for &(block_addr, true_target, false_target) in branch_blocks {
        facts.diagnostics.branches_evaluated += 1;
        let predicate_uses_call_result = predicate_depends_on_call_result(func, block_addr);

        let make_state = || {
            let mut state = SymState::new(ctx, func.entry);
            seed_default_state_for_arch(&mut state, func, Some(arch));
            state
        };

        let mut true_explorer = symbolic_fact_explorer(ctx);
        install_hooks(&mut true_explorer);
        let true_initial_state = make_state();
        let (compiled_true_status, true_compiled) = compiled_branch_reachability_status(
            &true_explorer,
            func,
            &true_initial_state,
            block_addr,
            true,
        );
        let true_condition = symbolic_condition_hint(true_compiled.as_ref());
        let true_status = if let Some(status) = compiled_true_status {
            status
        } else if predicate_uses_call_result || func_contains_calls(func) {
            SymbolicReachabilityStatus::Unknown
        } else {
            let paths = true_explorer.find_paths_to(func, make_state(), true_target);
            symbolic_reachability_status(paths.len(), true_explorer.budget_exhausted())
        };

        let mut false_explorer = symbolic_fact_explorer(ctx);
        install_hooks(&mut false_explorer);
        let false_initial_state = make_state();
        let (compiled_false_status, false_compiled) = compiled_branch_reachability_status(
            &false_explorer,
            func,
            &false_initial_state,
            block_addr,
            false,
        );
        let false_condition = symbolic_condition_hint(false_compiled.as_ref());
        let false_status = if let Some(status) = compiled_false_status {
            status
        } else if predicate_uses_call_result || func_contains_calls(func) {
            SymbolicReachabilityStatus::Unknown
        } else {
            let paths = false_explorer.find_paths_to(func, make_state(), false_target);
            symbolic_reachability_status(paths.len(), false_explorer.budget_exhausted())
        };

        if matches!(true_status, SymbolicReachabilityStatus::Unknown)
            || matches!(false_status, SymbolicReachabilityStatus::Unknown)
        {
            facts.diagnostics.branches_unknown += 1;
        }
        if matches!(
            (true_status, false_status),
            (
                SymbolicReachabilityStatus::Reachable,
                SymbolicReachabilityStatus::Unreachable
            ) | (
                SymbolicReachabilityStatus::Unreachable,
                SymbolicReachabilityStatus::Reachable
            )
        ) {
            facts.diagnostics.branches_pruned += 1;
        }

        facts.branch_facts.push(SymbolicBranchFact {
            block_addr,
            true_target,
            false_target,
            true_status,
            false_status,
            true_condition,
            false_condition,
            true_compiled,
            false_compiled,
        });
    }

    facts
}

fn install_derived_summary_set<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    registry: &SummaryRegistry<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    derived: &DerivedSummarySet<'ctx>,
    symbol_map: &HashMap<u64, String>,
) {
    let prepared = scope
        .and_then(|scope| scope.root())
        .map(|root| &root.prepared)
        .unwrap_or(func);
    let _ = registry.install_interproc_summaries_for_function(
        explorer,
        prepared,
        &derived.interproc,
        symbol_map,
    );
    let _ = registry.install_derived_summaries_for_function(
        explorer,
        prepared,
        &derived.summaries,
        symbol_map,
    );
    let _ = registry.install_known_symbols_for_function(explorer, prepared, symbol_map);
}

fn install_symbolic_fact_hooks<'ctx>(
    ctx: &'ctx Context,
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    summary_profile: SummaryProfile,
    symbol_map: &HashMap<u64, String>,
) {
    let Some(registry) = SummaryRegistry::with_profile_for_arch(arch, summary_profile) else {
        return;
    };
    if let Some(scope) = scope {
        let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
        install_derived_summary_set(explorer, &registry, func, Some(scope), &derived, symbol_map);
        return;
    }
    let _ = registry.install_known_symbols_for_function(explorer, func, symbol_map);
}

fn compiled_branch_reachability_status<'ctx>(
    explorer: &PathExplorer<'ctx>,
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    block_addr: u64,
    truth: bool,
) -> (
    Option<SymbolicReachabilityStatus>,
    Option<BackwardConditionSummary>,
) {
    let derived_summaries = explorer.derived_call_summary_views();
    if func_contains_calls(func) && derived_summaries.is_empty() {
        return (None, None);
    }
    let Some(compiled) = compile_branch_precondition_with_summaries(
        func,
        initial_state,
        block_addr,
        truth,
        &derived_summaries,
    ) else {
        return (None, None);
    };
    let summary = compiled.summary;
    if !matches!(summary.precision, BackwardConditionPrecision::Exact) {
        return (None, Some(summary));
    }
    let status = match explorer
        .solver()
        .sat_with_constraint(initial_state, &compiled.predicate)
    {
        SatResult::Sat => Some(SymbolicReachabilityStatus::Reachable),
        SatResult::Unsat => Some(SymbolicReachabilityStatus::Unreachable),
        SatResult::Unknown => None,
    };
    (status, Some(summary))
}

fn func_contains_calls(func: &SsaArtifact) -> bool {
    func.blocks().any(|block| {
        block
            .ops
            .iter()
            .any(|op| matches!(op, r2ssa::SSAOp::Call { .. } | r2ssa::SSAOp::CallInd { .. }))
    })
}

fn local_memory_store_value_ids(
    func: &SsaArtifact,
    inst_id: r2ssa::graph::InstId,
    size: u32,
) -> Vec<r2ssa::graph::ValueId> {
    let Some(uses) = func.memory().uses_by_inst.get(&inst_id) else {
        return Vec::new();
    };
    let mut values = Vec::new();
    for use_fact in uses {
        if use_fact.location.size != size {
            continue;
        }
        for (def_inst, defs) in &func.memory().defs_by_inst {
            for def in defs {
                if def.next_version != use_fact.version || def.location != use_fact.location {
                    continue;
                }
                let Some(inst) = func.graph().inst(*def_inst) else {
                    continue;
                };
                let r2ssa::graph::InstPayload::Op(r2ssa::SSAOp::Store { val, .. }) = &inst.payload
                else {
                    continue;
                };
                if let Some(value_id) = func.graph().value_id_for_var(val) {
                    values.push(value_id);
                }
            }
        }
    }
    values
}

fn value_depends_on_call_result(
    func: &SsaArtifact,
    value_id: r2ssa::graph::ValueId,
    visited: &mut BTreeSet<r2ssa::graph::ValueId>,
) -> bool {
    if !visited.insert(value_id) {
        return false;
    }

    let Some(inst_id) = func.graph().def_inst(value_id) else {
        return false;
    };
    let Some(inst) = func.graph().inst(inst_id) else {
        return false;
    };

    match &inst.payload {
        r2ssa::graph::InstPayload::Phi { .. } => inst
            .inputs
            .iter()
            .copied()
            .any(|input| value_depends_on_call_result(func, input, visited)),
        r2ssa::graph::InstPayload::Op(op) => match op {
            r2ssa::SSAOp::CallDefine { .. } => true,
            r2ssa::SSAOp::Load { dst, .. } => local_memory_store_value_ids(func, inst_id, dst.size)
                .into_iter()
                .any(|stored| value_depends_on_call_result(func, stored, visited)),
            _ => inst
                .inputs
                .iter()
                .copied()
                .any(|input| value_depends_on_call_result(func, input, visited)),
        },
    }
}

fn predicate_depends_on_call_result(func: &SsaArtifact, block_addr: u64) -> bool {
    let Some(predicate) = func
        .predicates()
        .predicates
        .values()
        .find(|fact| fact.block_addr == block_addr)
    else {
        return false;
    };
    let mut visited = BTreeSet::new();
    value_depends_on_call_result(func, predicate.condition, &mut visited)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn collect_symbolic_function_facts_with_derived<'ctx>(
    ctx: &'ctx Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    registry: &SummaryRegistry<'ctx>,
    derived: &DerivedSummarySet<'ctx>,
) -> SymbolicFunctionFacts {
    collect_symbolic_function_facts_with_derived_for_branch_blocks(
        ctx,
        func,
        scope,
        arch,
        &collect_branch_blocks(func),
        summary_profile,
        registry,
        derived,
        symbol_map,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn collect_symbolic_function_facts_with_derived_for_branch_blocks<'ctx>(
    ctx: &'ctx Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    branch_blocks: &[(u64, u64, u64)],
    summary_profile: SummaryProfile,
    registry: &SummaryRegistry<'ctx>,
    derived: &DerivedSummarySet<'ctx>,
    symbol_map: &HashMap<u64, String>,
) -> SymbolicFunctionFacts {
    let mut facts = collect_symbolic_function_facts_for_branch_blocks(
        ctx,
        func,
        arch,
        branch_blocks,
        |explorer| {
            install_derived_summary_set(explorer, registry, func, scope, derived, symbol_map);
        },
    );
    facts.memory_islands = merge_memory_islands(
        facts.memory_islands,
        derive_summary_memory_islands(func, branch_blocks, derived, &facts.diagnostics),
    );
    let _ = summary_profile;
    finalize_symbolic_function_facts(facts)
}

fn collect_large_cfg_symbolic_function_facts(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> SymbolicFunctionFacts {
    collect_large_cfg_symbolic_function_facts_with_limit(
        ctx,
        func,
        scope,
        arch,
        symbol_map,
        summary_profile,
        large_cfg_branch_limit(func),
    )
}

pub(super) fn collect_large_cfg_symbolic_function_facts_with_limit(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: &ArchSpec,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
    branch_limit: usize,
) -> SymbolicFunctionFacts {
    let branch_blocks = limited_branch_blocks(func, branch_limit.max(1));
    let mut facts = if let Some(scope) = scope {
        if let Some(registry) = SummaryRegistry::with_profile_for_arch(arch, summary_profile) {
            let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
            collect_symbolic_function_facts_with_derived_for_branch_blocks(
                ctx,
                func,
                Some(scope),
                arch,
                &branch_blocks,
                summary_profile,
                &registry,
                &derived,
                symbol_map,
            )
        } else {
            collect_symbolic_function_facts_for_branch_blocks(
                ctx,
                func,
                arch,
                &branch_blocks,
                |explorer| {
                    install_symbolic_fact_hooks(
                        ctx,
                        explorer,
                        func,
                        None,
                        arch,
                        summary_profile,
                        symbol_map,
                    );
                },
            )
        }
    } else {
        collect_symbolic_function_facts_for_branch_blocks(
            ctx,
            func,
            arch,
            &branch_blocks,
            |explorer| {
                install_symbolic_fact_hooks(
                    ctx,
                    explorer,
                    func,
                    None,
                    arch,
                    summary_profile,
                    symbol_map,
                );
            },
        )
    };
    facts.diagnostics.skipped_large_cfg = true;
    finalize_symbolic_function_facts(facts)
}

pub fn collect_symbolic_function_facts(
    ctx: &Context,
    func: &SsaArtifact,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
) -> SymbolicFunctionFacts {
    collect_symbolic_function_facts_with_scope_and_profile(
        ctx,
        func,
        None,
        arch,
        symbol_map,
        SummaryProfile::Default,
    )
}

pub fn collect_symbolic_function_facts_with_scope(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
) -> SymbolicFunctionFacts {
    collect_symbolic_function_facts_with_scope_and_profile(
        ctx,
        func,
        scope,
        arch,
        symbol_map,
        SummaryProfile::Default,
    )
}

pub fn collect_symbolic_function_facts_with_scope_and_profile(
    ctx: &Context,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    symbol_map: &HashMap<u64, String>,
    summary_profile: SummaryProfile,
) -> SymbolicFunctionFacts {
    let mut facts = SymbolicFunctionFacts::default();
    let Some(arch) = arch else {
        facts.diagnostics.skipped_missing_arch = true;
        return finalize_symbolic_function_facts(facts);
    };

    let cfg_summary = func.function().cfg_risk_summary();
    if cfg_summary.block_count > 96 || cfg_summary.switch_block_count > 8 {
        return collect_large_cfg_symbolic_function_facts(
            ctx,
            func,
            scope,
            arch,
            symbol_map,
            summary_profile,
        );
    }

    if let Some(scope) = scope {
        let Some(registry) = SummaryRegistry::with_profile_for_arch(arch, summary_profile) else {
            return finalize_symbolic_function_facts(facts);
        };
        let derived = registry.derive_symbolic_summaries(ctx, scope, Some(arch), symbol_map);
        return collect_symbolic_function_facts_with_derived(
            ctx,
            func,
            Some(scope),
            arch,
            symbol_map,
            summary_profile,
            &registry,
            &derived,
        );
    }
    finalize_symbolic_function_facts(collect_symbolic_function_facts_for_branch_blocks(
        ctx,
        func,
        arch,
        &collect_branch_blocks(func),
        |explorer| {
            install_symbolic_fact_hooks(
                ctx,
                explorer,
                func,
                None,
                arch,
                summary_profile,
                symbol_map,
            );
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BackwardMemoryRegion;

    fn residual_summary(expr: &str) -> BackwardConditionSummary {
        BackwardConditionSummary {
            simplified: expr.to_string(),
            terms: vec![expr.to_string()],
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: BackwardConditionPrecision::ResidualSearchRequired,
            supported_paths: 1,
            total_paths: 2,
        }
    }

    #[test]
    fn large_cfg_control_island_promotes_single_bounded_guard_to_likely() {
        let facts = finalize_symbolic_function_facts(SymbolicFunctionFacts {
            branch_facts: vec![SymbolicBranchFact {
                block_addr: 0x1000,
                true_target: 0x1010,
                false_target: 0x1020,
                true_status: SymbolicReachabilityStatus::Unknown,
                false_status: SymbolicReachabilityStatus::Unknown,
                true_condition: Some("sel == 3".to_string()),
                false_condition: None,
                true_compiled: Some(residual_summary("sel == 3")),
                false_compiled: None,
            }],
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: Vec::new(),
            diagnostics: SymbolicFunctionFactDiagnostics {
                skipped_large_cfg: true,
                ..SymbolicFunctionFactDiagnostics::default()
            },
        });

        let island = facts
            .control_island_for_block(0x1000)
            .expect("control island");
        assert_eq!(
            island.kind,
            SymbolicControlIslandKind::LargeCfgBranchFrontier
        );
        assert_eq!(island.evidence.tier, SemanticConfidence::Likely);
        assert!(island.actionable_compiled_condition().is_some());
    }

    #[test]
    fn control_island_requires_unique_actionable_condition() {
        let facts = finalize_symbolic_function_facts(SymbolicFunctionFacts {
            branch_facts: vec![SymbolicBranchFact {
                block_addr: 0x2000,
                true_target: 0x2010,
                false_target: 0x2020,
                true_status: SymbolicReachabilityStatus::Unknown,
                false_status: SymbolicReachabilityStatus::Unknown,
                true_condition: Some("x < 4".to_string()),
                false_condition: Some("x >= 4".to_string()),
                true_compiled: Some(BackwardConditionSummary {
                    simplified: "x < 4".to_string(),
                    terms: vec!["x < 4".to_string()],
                    memory_terms: Vec::new(),
                    backward_memory_substitutions: 0,
                    backward_memory_candidate_enumerations: 0,
                    backward_memory_residual_fallbacks: 0,
                    precision: BackwardConditionPrecision::OverApprox,
                    supported_paths: 1,
                    total_paths: 2,
                }),
                false_compiled: Some(BackwardConditionSummary {
                    simplified: "x >= 4".to_string(),
                    terms: vec!["x >= 4".to_string()],
                    memory_terms: Vec::new(),
                    backward_memory_substitutions: 0,
                    backward_memory_candidate_enumerations: 0,
                    backward_memory_residual_fallbacks: 0,
                    precision: BackwardConditionPrecision::OverApprox,
                    supported_paths: 1,
                    total_paths: 2,
                }),
            }],
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: Vec::new(),
            diagnostics: SymbolicFunctionFactDiagnostics::default(),
        });

        let island = facts
            .control_island_for_block(0x2000)
            .expect("control island");
        assert!(island.actionable_compiled_condition().is_none());
    }

    #[test]
    fn actionable_memory_terms_derive_memory_island_for_block() {
        let facts = finalize_symbolic_function_facts(SymbolicFunctionFacts {
            branch_facts: vec![SymbolicBranchFact {
                block_addr: 0x3000,
                true_target: 0x3010,
                false_target: 0x3020,
                true_status: SymbolicReachabilityStatus::Unknown,
                false_status: SymbolicReachabilityStatus::Unknown,
                true_condition: Some("arg0->f_8 == 0".to_string()),
                false_condition: None,
                true_compiled: Some(BackwardConditionSummary {
                    simplified: "arg0->f_8 == 0".to_string(),
                    terms: vec!["arg0->f_8 == 0".to_string()],
                    memory_terms: vec![BackwardMemoryCondition {
                        region: BackwardMemoryRegion::Argument { index: 0 },
                        offset_lo: 8,
                        offset_hi: 8,
                        size: 4,
                        exact_offset: true,
                        evidence: SemanticEvidence::exact(),
                        binding: None,
                        expr: "*(arg0 + 8)".to_string(),
                        value_expr: Some("*(arg0 + 8)".to_string()),
                        exact_value: false,
                    }],
                    backward_memory_substitutions: 1,
                    backward_memory_candidate_enumerations: 1,
                    backward_memory_residual_fallbacks: 0,
                    precision: BackwardConditionPrecision::OverApprox,
                    supported_paths: 1,
                    total_paths: 1,
                }),
                false_compiled: None,
            }],
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: Vec::new(),
            diagnostics: SymbolicFunctionFactDiagnostics::default(),
        });

        let island = facts
            .memory_island_for_block(0x3000)
            .expect("memory island");
        assert_eq!(island.kind, SymbolicMemoryIslandKind::ConditionFrontier);
        assert_eq!(island.terms.len(), 1);
        assert_eq!(island.actionable_terms().len(), 1);
        assert_eq!(island.evidence.tier, SemanticConfidence::Exact);
    }

    #[test]
    fn actionable_memory_terms_for_target_follow_actionable_source_block() {
        let facts = finalize_symbolic_function_facts(SymbolicFunctionFacts {
            branch_facts: vec![SymbolicBranchFact {
                block_addr: 0x3500,
                true_target: 0x3600,
                false_target: 0x3610,
                true_status: SymbolicReachabilityStatus::Reachable,
                false_status: SymbolicReachabilityStatus::Unreachable,
                true_condition: Some("x == 0".to_string()),
                false_condition: None,
                true_compiled: Some(BackwardConditionSummary {
                    simplified: "x == 0".to_string(),
                    terms: vec!["x == 0".to_string()],
                    memory_terms: Vec::new(),
                    backward_memory_substitutions: 0,
                    backward_memory_candidate_enumerations: 0,
                    backward_memory_residual_fallbacks: 0,
                    precision: BackwardConditionPrecision::Exact,
                    supported_paths: 1,
                    total_paths: 1,
                }),
                false_compiled: None,
            }],
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: vec![SymbolicMemoryIsland {
                kind: SymbolicMemoryIslandKind::ConditionFrontier,
                anchor_block: 0x3500,
                terms: vec![BackwardMemoryCondition {
                    region: BackwardMemoryRegion::Argument { index: 0 },
                    offset_lo: 4,
                    offset_hi: 4,
                    size: 4,
                    exact_offset: true,
                    evidence: SemanticEvidence::exact(),
                    binding: Some("sym_mem".to_string()),
                    expr: "0x2a".to_string(),
                    value_expr: Some("0x2a".to_string()),
                    exact_value: true,
                }],
                evidence: SemanticEvidence::exact(),
            }],
            diagnostics: SymbolicFunctionFactDiagnostics::default(),
        });

        let terms = facts.actionable_memory_terms_for_target(0x3600);
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0].binding.as_deref(), Some("sym_mem"));
        assert_eq!(terms[0].value_expr.as_deref(), Some("0x2a"));
    }

    #[test]
    fn finalize_symbolic_function_facts_preserves_preseeded_memory_islands() {
        let facts = finalize_symbolic_function_facts(SymbolicFunctionFacts {
            branch_facts: Vec::new(),
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: vec![SymbolicMemoryIsland {
                kind: SymbolicMemoryIslandKind::LargeCfgConditionFrontier,
                anchor_block: 0x3500,
                terms: vec![BackwardMemoryCondition {
                    region: BackwardMemoryRegion::Argument { index: 1 },
                    offset_lo: 0x10,
                    offset_hi: 0x10,
                    size: 8,
                    exact_offset: true,
                    evidence: SemanticEvidence::exact(),
                    binding: None,
                    expr: "arg1->f_10".to_string(),
                    value_expr: Some("arg1->f_10".to_string()),
                    exact_value: false,
                }],
                evidence: SemanticEvidence::exact(),
            }],
            diagnostics: SymbolicFunctionFactDiagnostics::default(),
        });

        let island = facts
            .memory_island_for_block(0x3500)
            .expect("preseeded memory island");
        assert_eq!(island.terms.len(), 1);
        assert_eq!(
            island.kind,
            SymbolicMemoryIslandKind::LargeCfgConditionFrontier
        );
        assert_eq!(island.terms[0].offset_lo, 0x10);
    }

    #[test]
    fn actionable_condition_source_for_target_tracks_branch_frontier() {
        let compiled = BackwardConditionSummary {
            simplified: "x == 0".to_string(),
            terms: vec!["x == 0".to_string()],
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: BackwardConditionPrecision::Exact,
            supported_paths: 1,
            total_paths: 1,
        };
        let facts = finalize_symbolic_function_facts(SymbolicFunctionFacts {
            branch_facts: vec![SymbolicBranchFact {
                block_addr: 0x4000,
                true_target: 0x4010,
                false_target: 0x4020,
                true_status: SymbolicReachabilityStatus::Reachable,
                false_status: SymbolicReachabilityStatus::Unreachable,
                true_condition: Some("x == 0".to_string()),
                false_condition: Some("x != 0".to_string()),
                true_compiled: Some(compiled.clone()),
                false_compiled: None,
            }],
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: Vec::new(),
            diagnostics: SymbolicFunctionFactDiagnostics::default(),
        });

        let source = facts
            .actionable_condition_source_for_target(0x4010)
            .expect("target source");
        assert_eq!(source.block_addr, 0x4000);
        assert!(source.branch_truth);
        assert!(source.necessary_for_target);
        assert_eq!(source.summary.simplified, "x == 0");
    }

    #[test]
    fn actionable_condition_source_prefers_best_candidate_but_marks_non_unique_sources() {
        let exact = BackwardConditionSummary {
            simplified: "x == 0".to_string(),
            terms: vec!["x == 0".to_string()],
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: BackwardConditionPrecision::Exact,
            supported_paths: 1,
            total_paths: 1,
        };
        let likely = BackwardConditionSummary {
            simplified: "x <= 1".to_string(),
            terms: vec!["x <= 1".to_string()],
            memory_terms: vec![BackwardMemoryCondition {
                region: BackwardMemoryRegion::Argument { index: 0 },
                offset_lo: 8,
                offset_hi: 12,
                size: 4,
                exact_offset: false,
                evidence: SemanticEvidence::likely(SemanticEvidenceReason::DerivedFromRanking)
                    .with_coverage(SemanticEvidenceCoverage::Bounded)
                    .with_provenance(SemanticEvidenceProvenance::Normalized),
                binding: None,
                expr: "*(arg0 + [8,12])".to_string(),
                value_expr: Some("*(arg0 + [8,12])".to_string()),
                exact_value: false,
            }],
            backward_memory_substitutions: 1,
            backward_memory_candidate_enumerations: 1,
            backward_memory_residual_fallbacks: 0,
            precision: BackwardConditionPrecision::OverApprox,
            supported_paths: 1,
            total_paths: 2,
        };
        let facts = finalize_symbolic_function_facts(SymbolicFunctionFacts {
            branch_facts: vec![
                SymbolicBranchFact {
                    block_addr: 0x4000,
                    true_target: 0x4010,
                    false_target: 0x4020,
                    true_status: SymbolicReachabilityStatus::Reachable,
                    false_status: SymbolicReachabilityStatus::Unreachable,
                    true_condition: Some("x == 0".to_string()),
                    false_condition: Some("x != 0".to_string()),
                    true_compiled: Some(exact.clone()),
                    false_compiled: None,
                },
                SymbolicBranchFact {
                    block_addr: 0x4018,
                    true_target: 0x4010,
                    false_target: 0x4030,
                    true_status: SymbolicReachabilityStatus::Reachable,
                    false_status: SymbolicReachabilityStatus::Unreachable,
                    true_condition: Some("x <= 1".to_string()),
                    false_condition: None,
                    true_compiled: Some(likely),
                    false_compiled: None,
                },
            ],
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: Vec::new(),
            diagnostics: SymbolicFunctionFactDiagnostics::default(),
        });

        let source = facts
            .actionable_condition_source_for_target(0x4010)
            .expect("target source");
        assert_eq!(source.block_addr, 0x4000);
        assert!(source.branch_truth);
        assert!(!source.necessary_for_target);
        assert_eq!(source.summary.simplified, "x == 0");
    }
}
