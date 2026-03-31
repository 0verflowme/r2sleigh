use serde::{Deserialize, Serialize};

use crate::sim::DerivedSummaryDiagnostics;

use super::facts::SymbolicFunctionFacts;
use super::vm::{InterpreterDispatchSummary, VmStepSummary};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemanticMode {
    Raw,
    Compiled,
    Residual,
    VmSummary,
}

pub type CompiledSemanticMode = SemanticMode;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SliceClass {
    Wrapper,
    Worker,
    RecursiveGroup,
    InterpreterSwitch,
    InterpreterIndirect,
    GenericLarge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemanticEvidenceProvenance {
    Stable,
    Normalized,
    Ranked,
    Unstable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemanticEvidenceAmbiguity {
    Single,
    Bounded,
    Ranked,
    Multiple,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemanticEvidenceReason {
    LargeCfg,
    SummaryBudget,
    AliasAmbiguity,
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
    }

    pub fn is_usable(&self) -> bool {
        self.tier.is_usable()
    }

    pub fn allows_hard_proof(&self) -> bool {
        matches!(self.tier, SemanticConfidence::Exact)
    }

    pub fn allows_narrowing(&self) -> bool {
        matches!(
            self.tier,
            SemanticConfidence::Exact | SemanticConfidence::Likely
        )
    }

    pub fn allows_ranking(&self) -> bool {
        !matches!(self.tier, SemanticConfidence::Residual)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticCapability {
    pub query_ready: bool,
    pub type_ready: bool,
    pub decompile_ready: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSemanticArtifact {
    pub mode: SemanticMode,
    pub slice_class: SliceClass,
    pub capability: SemanticCapability,
    pub residual_reasons: Vec<ResidualReason>,
    pub closure_functions: usize,
    pub helper_functions: usize,
    pub derived_summaries: usize,
    pub derived_diagnostics: DerivedSummaryDiagnostics,
    pub symbolic_facts: SymbolicFunctionFacts,
    pub interpreter: Option<InterpreterDispatchSummary>,
    pub vm_step: Option<VmStepSummary>,
    pub vm_transfer: Option<VmStepSummary>,
    pub cache_hit: bool,
}

pub type CompiledFunctionSemantics = CompiledSemanticArtifact;
