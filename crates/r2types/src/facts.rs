use std::collections::{BTreeMap, HashMap};

use crate::context::{
    ExternalRegisterParamSpec, ExternalStackSlotSpec, ExternalStackVarSpec, StackSlotKey,
    legacy_external_stack_vars_from_slots, stack_slots_from_legacy_external_stack_vars,
};
use crate::convert::CTypeLike;
use crate::external::ExternalTypeDb;
use crate::model::Signedness;

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicReachabilityStatus {
    Reachable,
    Unreachable,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticMode {
    Raw,
    Compiled,
    IslandCompiled,
    Residual,
    VmSummary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticSliceClass {
    Wrapper,
    Worker,
    RecursiveGroup,
    InterpreterSwitch,
    InterpreterIndirect,
    GenericLarge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
pub struct SymbolicSemanticCapability {
    pub query_ready: bool,
    pub type_ready: bool,
    pub decompile_ready: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticResidualReason {
    MissingArch,
    LargeCfg,
    SummaryBudgetExhausted,
    SccBudgetExhausted,
    InterpreterRequiresStepSummary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicConditionPrecision {
    Exact,
    OverApprox,
    ResidualSearchRequired,
    Unsupported,
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum SymbolicSemanticConfidence {
    Exact,
    Likely,
    Heuristic,
    Residual,
}

const fn default_symbolic_confidence_exact() -> SymbolicSemanticConfidence {
    SymbolicSemanticConfidence::Exact
}

impl SymbolicSemanticConfidence {
    pub fn is_reliable(self) -> bool {
        matches!(self, Self::Exact | Self::Likely)
    }

    pub fn is_usable(self) -> bool {
        !matches!(self, Self::Residual)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticEvidenceSoundness {
    Proven,
    OverApprox,
    Ranked,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticEvidenceCoverage {
    Full,
    Partial,
    Bounded,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticEvidenceProvenance {
    Stable,
    Normalized,
    Ranked,
    Unstable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticEvidenceAmbiguity {
    Single,
    Bounded,
    Ranked,
    Multiple,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicSemanticEvidenceReason {
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

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicSemanticEvidence {
    pub tier: SymbolicSemanticConfidence,
    pub soundness: SymbolicSemanticEvidenceSoundness,
    pub coverage: SymbolicSemanticEvidenceCoverage,
    pub provenance: SymbolicSemanticEvidenceProvenance,
    pub ambiguity: SymbolicSemanticEvidenceAmbiguity,
    #[serde(default)]
    pub budget_limited: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub reasons: Vec<SymbolicSemanticEvidenceReason>,
}

impl Default for SymbolicSemanticEvidence {
    fn default() -> Self {
        Self::exact()
    }
}

impl SymbolicSemanticEvidence {
    pub fn exact() -> Self {
        Self {
            tier: SymbolicSemanticConfidence::Exact,
            soundness: SymbolicSemanticEvidenceSoundness::Proven,
            coverage: SymbolicSemanticEvidenceCoverage::Full,
            provenance: SymbolicSemanticEvidenceProvenance::Stable,
            ambiguity: SymbolicSemanticEvidenceAmbiguity::Single,
            budget_limited: false,
            reasons: Vec::new(),
        }
    }

    pub fn likely(reason: SymbolicSemanticEvidenceReason) -> Self {
        Self {
            tier: SymbolicSemanticConfidence::Likely,
            soundness: SymbolicSemanticEvidenceSoundness::OverApprox,
            coverage: SymbolicSemanticEvidenceCoverage::Full,
            provenance: SymbolicSemanticEvidenceProvenance::Normalized,
            ambiguity: SymbolicSemanticEvidenceAmbiguity::Single,
            budget_limited: false,
            reasons: vec![reason],
        }
    }

    pub fn heuristic(reason: SymbolicSemanticEvidenceReason) -> Self {
        Self {
            tier: SymbolicSemanticConfidence::Heuristic,
            soundness: SymbolicSemanticEvidenceSoundness::Ranked,
            coverage: SymbolicSemanticEvidenceCoverage::Partial,
            provenance: SymbolicSemanticEvidenceProvenance::Ranked,
            ambiguity: SymbolicSemanticEvidenceAmbiguity::Ranked,
            budget_limited: false,
            reasons: vec![reason],
        }
    }

    pub fn residual(reason: SymbolicSemanticEvidenceReason) -> Self {
        Self {
            tier: SymbolicSemanticConfidence::Residual,
            soundness: SymbolicSemanticEvidenceSoundness::Unknown,
            coverage: SymbolicSemanticEvidenceCoverage::Partial,
            provenance: SymbolicSemanticEvidenceProvenance::Unstable,
            ambiguity: SymbolicSemanticEvidenceAmbiguity::Multiple,
            budget_limited: false,
            reasons: vec![reason],
        }
    }

    pub fn with_reason(mut self, reason: SymbolicSemanticEvidenceReason) -> Self {
        if !self.reasons.contains(&reason) {
            self.reasons.push(reason);
        }
        self
    }

    pub fn is_default_exact(&self) -> bool {
        *self == Self::exact()
    }

    pub fn is_reliable(&self) -> bool {
        self.tier.is_reliable()
    }

    pub fn is_usable(&self) -> bool {
        self.tier.is_usable()
    }

    pub fn allows_hard_proof(&self) -> bool {
        matches!(self.tier, SymbolicSemanticConfidence::Exact)
    }

    pub fn allows_narrowing(&self) -> bool {
        matches!(
            self.tier,
            SymbolicSemanticConfidence::Exact | SymbolicSemanticConfidence::Likely
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicVmUnaryOp {
    Neg,
    Not,
    BoolNot,
    ZExt,
    SExt,
    Trunc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicVmBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    SDiv,
    Rem,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    PtrAdd,
    PtrSub,
    Piece,
    Concat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicMemoryRegionKind {
    Stack,
    Global,
    Input,
    Heap,
    Replay,
    EscapedUnknown,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicMemoryRegionRef {
    pub id: u32,
    pub kind: SymbolicMemoryRegionKind,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicMemoryRegion {
    Argument { index: usize },
    Region(SymbolicMemoryRegionRef),
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicMemoryCondition {
    pub region: SymbolicMemoryRegion,
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub size: u32,
    pub exact_offset: bool,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binding: Option<String>,
    pub expr: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub value_expr: Option<String>,
    #[serde(default)]
    pub exact_value: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicCompiledCondition {
    pub simplified: String,
    pub terms: Vec<String>,
    pub memory_terms: Vec<SymbolicMemoryCondition>,
    pub backward_memory_substitutions: usize,
    pub backward_memory_candidate_enumerations: usize,
    pub backward_memory_residual_fallbacks: usize,
    pub precision: SymbolicConditionPrecision,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
    pub supported_paths: usize,
    pub total_paths: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicInterpreterKind {
    SwitchDispatch,
    IndirectDispatch,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicInterpreterDispatch {
    pub kind: SymbolicInterpreterKind,
    pub dispatch_header: u64,
    pub dispatch_targets: usize,
    pub selector: Option<String>,
    pub back_edges: usize,
    pub score: i32,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicVmValueExpr {
    Const(u64),
    Var(String),
    Expr(String),
    Unary {
        op: SymbolicVmUnaryOp,
        expr: Box<SymbolicVmValueExpr>,
    },
    Binary {
        op: SymbolicVmBinaryOp,
        left: Box<SymbolicVmValueExpr>,
        right: Box<SymbolicVmValueExpr>,
    },
}

impl SymbolicVmValueExpr {
    fn split_version(name: &str) -> (&str, Option<&str>) {
        name.rsplit_once('_')
            .filter(|(_, version)| version.chars().all(|ch| ch.is_ascii_digit()))
            .map_or((name, None), |(base, version)| (base, Some(version)))
    }

    fn same_logical_name(left: &str, right: &str) -> bool {
        Self::split_version(left)
            .0
            .eq_ignore_ascii_case(Self::split_version(right).0)
    }

    fn lookup_binding(bindings: &BTreeMap<String, u64>, name: &str) -> Option<u64> {
        bindings.get(name).copied().or_else(|| {
            bindings.iter().find_map(|(candidate, value)| {
                Self::same_logical_name(candidate, name).then_some(*value)
            })
        })
    }

    pub fn render(&self) -> String {
        match self {
            Self::Const(value) => format!("0x{value:x}"),
            Self::Var(name) | Self::Expr(name) => name.clone(),
            Self::Unary { op, expr } => {
                let inner = expr.render();
                match op {
                    SymbolicVmUnaryOp::Neg => format!("(-{inner})"),
                    SymbolicVmUnaryOp::Not => format!("(~{inner})"),
                    SymbolicVmUnaryOp::BoolNot => format!("(!{inner})"),
                    SymbolicVmUnaryOp::ZExt => format!("zext({inner})"),
                    SymbolicVmUnaryOp::SExt => format!("sext({inner})"),
                    SymbolicVmUnaryOp::Trunc => format!("trunc({inner})"),
                }
            }
            Self::Binary { op, left, right } => {
                let left = left.render();
                let right = right.render();
                let symbol = match op {
                    SymbolicVmBinaryOp::Add => "+",
                    SymbolicVmBinaryOp::Sub => "-",
                    SymbolicVmBinaryOp::Mul => "*",
                    SymbolicVmBinaryOp::Div | SymbolicVmBinaryOp::SDiv => "/",
                    SymbolicVmBinaryOp::Rem | SymbolicVmBinaryOp::SRem => "%",
                    SymbolicVmBinaryOp::And => "&",
                    SymbolicVmBinaryOp::Or => "|",
                    SymbolicVmBinaryOp::Xor => "^",
                    SymbolicVmBinaryOp::Shl => "<<",
                    SymbolicVmBinaryOp::Shr => ">>",
                    SymbolicVmBinaryOp::Eq => "==",
                    SymbolicVmBinaryOp::Ne => "!=",
                    SymbolicVmBinaryOp::Lt => "<",
                    SymbolicVmBinaryOp::Le => "<=",
                    SymbolicVmBinaryOp::Gt => ">",
                    SymbolicVmBinaryOp::Ge => ">=",
                    SymbolicVmBinaryOp::PtrAdd => "+",
                    SymbolicVmBinaryOp::PtrSub => "-",
                    SymbolicVmBinaryOp::Piece => "piece",
                    SymbolicVmBinaryOp::Concat => "concat",
                };
                match op {
                    SymbolicVmBinaryOp::Piece | SymbolicVmBinaryOp::Concat => {
                        format!("{symbol}({left}, {right})")
                    }
                    SymbolicVmBinaryOp::PtrAdd | SymbolicVmBinaryOp::PtrSub => {
                        format!("({left} {symbol} {right})")
                    }
                    _ => format!("({left} {symbol} {right})"),
                }
            }
        }
    }

    pub fn evaluate_u64(&self, bindings: &BTreeMap<String, u64>) -> Option<u64> {
        match self {
            Self::Const(value) => Some(*value),
            Self::Var(name) => Self::lookup_binding(bindings, name),
            Self::Unary { op, expr } => {
                let value = expr.evaluate_u64(bindings)?;
                Some(match op {
                    SymbolicVmUnaryOp::Neg => value.wrapping_neg(),
                    SymbolicVmUnaryOp::Not => !value,
                    SymbolicVmUnaryOp::BoolNot => u64::from(value == 0),
                    SymbolicVmUnaryOp::ZExt
                    | SymbolicVmUnaryOp::SExt
                    | SymbolicVmUnaryOp::Trunc => value,
                })
            }
            Self::Binary { op, left, right } => {
                let left = left.evaluate_u64(bindings)?;
                let right = right.evaluate_u64(bindings)?;
                Some(match op {
                    SymbolicVmBinaryOp::Add | SymbolicVmBinaryOp::PtrAdd => {
                        left.wrapping_add(right)
                    }
                    SymbolicVmBinaryOp::Sub | SymbolicVmBinaryOp::PtrSub => {
                        left.wrapping_sub(right)
                    }
                    SymbolicVmBinaryOp::Mul => left.wrapping_mul(right),
                    SymbolicVmBinaryOp::Div => left.checked_div(right)?,
                    SymbolicVmBinaryOp::SDiv => ((left as i64).checked_div(right as i64)?) as u64,
                    SymbolicVmBinaryOp::Rem => left.checked_rem(right)?,
                    SymbolicVmBinaryOp::SRem => ((left as i64).checked_rem(right as i64)?) as u64,
                    SymbolicVmBinaryOp::And => left & right,
                    SymbolicVmBinaryOp::Or => left | right,
                    SymbolicVmBinaryOp::Xor => left ^ right,
                    SymbolicVmBinaryOp::Shl => left.wrapping_shl((right & 63) as u32),
                    SymbolicVmBinaryOp::Shr => left.wrapping_shr((right & 63) as u32),
                    SymbolicVmBinaryOp::Eq => u64::from(left == right),
                    SymbolicVmBinaryOp::Ne => u64::from(left != right),
                    SymbolicVmBinaryOp::Lt => u64::from(left < right),
                    SymbolicVmBinaryOp::Le => u64::from(left <= right),
                    SymbolicVmBinaryOp::Gt => u64::from(left > right),
                    SymbolicVmBinaryOp::Ge => u64::from(left >= right),
                    SymbolicVmBinaryOp::Piece | SymbolicVmBinaryOp::Concat => return None,
                })
            }
            Self::Expr(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicVmStateUpdate {
    pub output: String,
    pub expr: String,
    pub value: SymbolicVmValueExpr,
    pub exact: bool,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicVmGuardCondition {
    pub expr: String,
    pub value: SymbolicVmValueExpr,
    pub expect_nonzero: bool,
    pub exact: bool,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
}

impl SymbolicVmGuardCondition {
    pub fn evaluate(&self, bindings: &BTreeMap<String, u64>) -> Option<bool> {
        let value = self.value.evaluate_u64(bindings)?;
        Some((value != 0) == self.expect_nonzero)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicVmGuardedExit {
    pub target: u64,
    pub guard: SymbolicVmGuardCondition,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicVmTransferArm {
    pub handler_target: u64,
    pub case_values: Vec<u64>,
    pub region_blocks: Vec<u64>,
    pub exit_targets: Vec<u64>,
    pub exit_guards: Vec<SymbolicVmGuardedExit>,
    pub state_updates: Vec<SymbolicVmStateUpdate>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selector_update: Option<SymbolicVmStateUpdate>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory_reads: Vec<SymbolicMemoryCondition>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory_writes: Vec<SymbolicMemoryCondition>,
    #[serde(default)]
    pub residual_guards: bool,
    #[serde(default)]
    pub residual_memory_effects: bool,
    pub exact: bool,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
    pub redispatch: bool,
    pub may_return: bool,
    pub truncated: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicVmStepSummary {
    pub kind: SymbolicInterpreterKind,
    pub loop_header: u64,
    pub dispatch_header: u64,
    pub selector: Option<String>,
    pub dispatch_targets: Vec<u64>,
    pub default_target: Option<u64>,
    pub case_values_by_target: BTreeMap<u64, Vec<u64>>,
    pub loop_latches: Vec<u64>,
    pub state_inputs: Vec<String>,
    pub state_outputs: Vec<String>,
    pub step_blocks: Vec<u64>,
    pub handler_regions: BTreeMap<u64, Vec<u64>>,
    pub handler_state_inputs: BTreeMap<u64, Vec<String>>,
    pub handler_state_outputs: BTreeMap<u64, Vec<String>>,
    pub handler_state_updates: BTreeMap<u64, Vec<SymbolicVmStateUpdate>>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub handler_exit_guards: BTreeMap<u64, Vec<SymbolicVmGuardedExit>>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub handler_memory_read_effects: BTreeMap<u64, Vec<SymbolicMemoryCondition>>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub handler_memory_write_effects: BTreeMap<u64, Vec<SymbolicMemoryCondition>>,
    pub handler_memory_reads: BTreeMap<u64, usize>,
    pub handler_memory_writes: BTreeMap<u64, usize>,
    pub handler_calls: BTreeMap<u64, usize>,
    pub handler_conditional_branches: BTreeMap<u64, usize>,
    pub handler_exit_targets: BTreeMap<u64, Vec<u64>>,
    pub redispatch_handlers: Vec<u64>,
    pub returning_handlers: Vec<u64>,
    pub truncated_handlers: Vec<u64>,
    pub transfers: Vec<SymbolicVmTransferArm>,
}
pub type SymbolicVmTransferSummary = SymbolicVmStepSummary;

impl SymbolicVmTransferArm {
    pub fn exact_exit_guard_for_target(&self, target: u64) -> Option<&SymbolicVmGuardCondition> {
        self.exit_guards
            .iter()
            .find(|guard| guard.target == target && guard.guard.evidence.allows_hard_proof())
            .map(|guard| &guard.guard)
    }

    pub fn actionable_exit_guard_for_target(
        &self,
        target: u64,
    ) -> Option<&SymbolicVmGuardCondition> {
        self.exit_guards
            .iter()
            .find(|guard| guard.target == target && guard.guard.evidence.allows_narrowing())
            .map(|guard| &guard.guard)
    }

    pub fn exact_exit_guard_result_for_case(
        &self,
        selector: Option<&str>,
        case_value: u64,
        target: u64,
    ) -> Option<bool> {
        let guard = self.exact_exit_guard_for_target(target)?;
        let mut bindings = BTreeMap::new();
        if let Some(selector) = selector {
            bindings.insert(selector.to_string(), case_value);
        }
        guard.evaluate(&bindings)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicFactDiagnostics {
    pub branches_evaluated: usize,
    pub branches_pruned: usize,
    pub branches_unknown: usize,
    pub skipped_missing_arch: bool,
    pub skipped_large_cfg: bool,
    #[serde(default)]
    pub cache_hit: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_mode: Option<SymbolicSemanticMode>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_capability: Option<SymbolicSemanticCapability>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slice_class: Option<SymbolicSemanticSliceClass>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub residual_reasons: Vec<SymbolicSemanticResidualReason>,
    pub closure_functions: usize,
    pub helper_functions: usize,
    pub derived_summaries: usize,
    pub summary_attempted: usize,
    pub summary_budget_exhausted: usize,
    pub summary_scc_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicBranchFact {
    pub block_addr: u64,
    pub true_target: u64,
    pub false_target: u64,
    pub true_status: SymbolicReachabilityStatus,
    pub false_status: SymbolicReachabilityStatus,
    pub true_condition: Option<String>,
    pub false_condition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub true_compiled: Option<SymbolicCompiledCondition>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub false_compiled: Option<SymbolicCompiledCondition>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicControlIslandKind {
    BranchFrontier,
    LargeCfgBranchFrontier,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SymbolicMemoryIslandKind {
    ConditionFrontier,
    LargeCfgConditionFrontier,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicControlFact {
    pub target: u64,
    pub status: SymbolicReachabilityStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiled: Option<SymbolicCompiledCondition>,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
}

impl SymbolicControlFact {
    pub fn exact_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        self.evidence
            .allows_hard_proof()
            .then_some(self.compiled.as_ref())
            .flatten()
    }

    pub fn actionable_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        self.evidence
            .allows_narrowing()
            .then_some(self.compiled.as_ref())
            .flatten()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicControlIsland {
    pub kind: SymbolicControlIslandKind,
    pub anchor_block: u64,
    pub frontier_targets: Vec<u64>,
    pub facts: Vec<SymbolicControlFact>,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
}

impl SymbolicControlIsland {
    pub fn exact_reachable_target(&self) -> Option<u64> {
        unique_reachable_control_target(self.facts.iter(), true)
    }

    pub fn actionable_reachable_target(&self) -> Option<u64> {
        unique_reachable_control_target(self.facts.iter(), false)
    }

    pub fn exact_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        unique_compiled_control_condition(self.facts.iter(), true)
    }

    pub fn actionable_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        unique_compiled_control_condition(self.facts.iter(), false)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicMemoryIsland {
    pub kind: SymbolicMemoryIslandKind,
    pub anchor_block: u64,
    pub terms: Vec<SymbolicMemoryCondition>,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
}

impl SymbolicMemoryIsland {
    pub fn exact_terms(&self) -> Vec<&SymbolicMemoryCondition> {
        self.terms
            .iter()
            .filter(|term| term.evidence.allows_hard_proof())
            .collect()
    }

    pub fn actionable_terms(&self) -> Vec<&SymbolicMemoryCondition> {
        self.terms
            .iter()
            .filter(|term| term.evidence.allows_narrowing())
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
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
    pub memory_terms: Vec<SymbolicMemoryCondition>,
    #[serde(
        default,
        skip_serializing_if = "SymbolicSemanticEvidence::is_default_exact"
    )]
    pub evidence: SymbolicSemanticEvidence,
    #[serde(default = "default_symbolic_confidence_exact")]
    pub confidence: SymbolicSemanticConfidence,
}

impl SymbolicWorkerIsland {
    pub fn exact_reachable_target(&self) -> Option<u64> {
        unique_reachable_control_target(self.control_facts.iter(), true)
    }

    pub fn actionable_reachable_target(&self) -> Option<u64> {
        unique_reachable_control_target(self.control_facts.iter(), false)
    }

    pub fn exact_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        unique_compiled_control_condition(self.control_facts.iter(), true)
    }

    pub fn actionable_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        unique_compiled_control_condition(self.control_facts.iter(), false)
    }

    pub fn exact_terms(&self) -> Vec<&SymbolicMemoryCondition> {
        self.memory_terms
            .iter()
            .filter(|term| term.evidence.allows_hard_proof())
            .collect()
    }

    pub fn actionable_terms(&self) -> Vec<&SymbolicMemoryCondition> {
        self.memory_terms
            .iter()
            .filter(|term| term.evidence.allows_narrowing())
            .collect()
    }
}

fn worker_island_supporting_compiled_condition(
    island: &SymbolicWorkerIsland,
) -> Option<&SymbolicCompiledCondition> {
    let reachable_target = island
        .exact_reachable_target()
        .or_else(|| island.actionable_reachable_target())?;
    island
        .control_facts
        .iter()
        .find(|fact| fact.target == reachable_target)
        .and_then(SymbolicControlFact::actionable_compiled_condition)
}

fn worker_island_supports_structured_decompile(island: &SymbolicWorkerIsland) -> bool {
    let has_unique_target =
        island.exact_reachable_target().is_some() || island.actionable_reachable_target().is_some();
    let supporting_condition = worker_island_supporting_compiled_condition(island);
    let has_condition = supporting_condition.is_some();
    let has_memory_support = !island.actionable_terms().is_empty()
        || supporting_condition.is_some_and(|compiled| !compiled.memory_terms.is_empty());
    island.evidence.allows_narrowing() && has_unique_target && has_condition && has_memory_support
}

#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SymbolicSemanticFacts {
    pub branch_facts: Vec<SymbolicBranchFact>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub worker_islands: Vec<SymbolicWorkerIsland>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub control_islands: Vec<SymbolicControlIsland>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub memory_islands: Vec<SymbolicMemoryIsland>,
    pub diagnostics: SymbolicFactDiagnostics,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interpreter: Option<SymbolicInterpreterDispatch>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vm_step: Option<SymbolicVmStepSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vm_transfer: Option<SymbolicVmTransferSummary>,
}

impl SymbolicSemanticFacts {
    pub fn is_empty(&self) -> bool {
        self.branch_facts.is_empty()
            && self.worker_islands.is_empty()
            && self.control_islands.is_empty()
            && self.memory_islands.is_empty()
            && self.diagnostics == SymbolicFactDiagnostics::default()
            && self.interpreter.is_none()
            && self.vm_step.is_none()
            && self.vm_transfer.is_none()
    }

    pub fn branch_fact_for_block(&self, block_addr: u64) -> Option<&SymbolicBranchFact> {
        self.branch_facts
            .iter()
            .find(|fact| fact.block_addr == block_addr)
    }

    pub fn control_island_for_block(&self, block_addr: u64) -> Option<&SymbolicControlIsland> {
        self.control_islands
            .iter()
            .find(|island| island.anchor_block == block_addr)
    }

    pub fn worker_island_for_block(&self, block_addr: u64) -> Option<&SymbolicWorkerIsland> {
        self.worker_islands
            .iter()
            .find(|island| island.anchor_block == block_addr)
    }

    pub fn memory_island_for_block(&self, block_addr: u64) -> Option<&SymbolicMemoryIsland> {
        self.memory_islands
            .iter()
            .find(|island| island.anchor_block == block_addr)
    }

    pub fn exact_compiled_condition_for_block(
        &self,
        block_addr: u64,
    ) -> Option<&SymbolicCompiledCondition> {
        self.branch_fact_for_block(block_addr)
            .and_then(SymbolicBranchFact::exact_compiled_condition)
            .or_else(|| {
                self.worker_island_for_block(block_addr)
                    .and_then(SymbolicWorkerIsland::exact_compiled_condition)
            })
            .or_else(|| {
                self.control_island_for_block(block_addr)
                    .and_then(SymbolicControlIsland::exact_compiled_condition)
            })
    }

    pub fn exact_reachable_target_for_block(&self, block_addr: u64) -> Option<u64> {
        self.branch_fact_for_block(block_addr)
            .and_then(SymbolicBranchFact::exact_reachable_target)
            .or_else(|| {
                self.worker_island_for_block(block_addr)
                    .and_then(SymbolicWorkerIsland::exact_reachable_target)
            })
            .or_else(|| {
                self.control_island_for_block(block_addr)
                    .and_then(SymbolicControlIsland::exact_reachable_target)
            })
    }

    pub fn actionable_reachable_target_for_block(&self, block_addr: u64) -> Option<u64> {
        self.branch_fact_for_block(block_addr)
            .and_then(SymbolicBranchFact::actionable_reachable_target)
            .or_else(|| {
                self.worker_island_for_block(block_addr)
                    .and_then(SymbolicWorkerIsland::actionable_reachable_target)
            })
            .or_else(|| {
                self.control_island_for_block(block_addr)
                    .and_then(SymbolicControlIsland::actionable_reachable_target)
            })
    }

    pub fn actionable_compiled_condition_for_block(
        &self,
        block_addr: u64,
    ) -> Option<&SymbolicCompiledCondition> {
        self.branch_fact_for_block(block_addr)
            .and_then(SymbolicBranchFact::actionable_compiled_condition)
            .or_else(|| {
                self.worker_island_for_block(block_addr)
                    .and_then(SymbolicWorkerIsland::actionable_compiled_condition)
            })
            .or_else(|| {
                self.control_island_for_block(block_addr)
                    .and_then(SymbolicControlIsland::actionable_compiled_condition)
            })
    }

    pub fn actionable_memory_terms_for_block(
        &self,
        block_addr: u64,
    ) -> Vec<&SymbolicMemoryCondition> {
        self.worker_island_for_block(block_addr)
            .map(SymbolicWorkerIsland::actionable_terms)
            .or_else(|| {
                self.memory_island_for_block(block_addr)
                    .map(SymbolicMemoryIsland::actionable_terms)
            })
            .unwrap_or_default()
    }

    pub fn actionable_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&SymbolicCompiledCondition> {
        target_compiled_condition(self, target_addr, false)
    }

    pub fn exact_compiled_condition_for_target(
        &self,
        target_addr: u64,
    ) -> Option<&SymbolicCompiledCondition> {
        target_compiled_condition(self, target_addr, true)
    }

    pub fn vm_step_for_dispatch_header(
        &self,
        dispatch_header: u64,
    ) -> Option<&SymbolicVmStepSummary> {
        self.vm_step
            .as_ref()
            .filter(|vm_step| vm_step.dispatch_header == dispatch_header)
    }

    pub fn vm_transfer_for_dispatch_header(
        &self,
        dispatch_header: u64,
    ) -> Option<&SymbolicVmTransferSummary> {
        self.vm_transfer
            .as_ref()
            .filter(|vm_transfer| vm_transfer.dispatch_header == dispatch_header)
    }

    pub fn semantic_mode(&self) -> Option<SymbolicSemanticMode> {
        self.diagnostics.semantic_mode
    }

    pub fn semantic_capability(&self) -> Option<SymbolicSemanticCapability> {
        self.diagnostics.semantic_capability
    }

    pub fn island_compiled(&self) -> bool {
        matches!(
            self.semantic_mode(),
            Some(SymbolicSemanticMode::IslandCompiled)
        )
    }

    pub fn query_ready(&self) -> bool {
        self.semantic_capability()
            .is_some_and(|capability| capability.query_ready)
    }

    pub fn type_ready(&self) -> bool {
        self.semantic_capability()
            .is_some_and(|capability| capability.type_ready)
    }

    pub fn decompile_ready(&self) -> bool {
        self.semantic_capability()
            .is_some_and(|capability| capability.decompile_ready)
    }

    pub fn structured_decompile_ready(&self) -> bool {
        if !self.decompile_ready() || !self.diagnostics.skipped_large_cfg {
            return false;
        }
        self.worker_islands
            .iter()
            .any(worker_island_supports_structured_decompile)
    }

    pub fn slice_class(&self) -> Option<SymbolicSemanticSliceClass> {
        self.diagnostics.slice_class
    }

    pub fn requires_type_fallback(&self) -> bool {
        self.semantic_capability().is_some() && !self.type_ready()
    }

    pub fn prefers_bounded_type_plan(&self) -> bool {
        if self.requires_type_fallback() {
            return true;
        }
        matches!(
            self.semantic_mode(),
            Some(SymbolicSemanticMode::Residual | SymbolicSemanticMode::IslandCompiled)
        ) && self.diagnostics.skipped_large_cfg
            && matches!(self.slice_class(), Some(SymbolicSemanticSliceClass::Worker))
            && (!self.worker_islands.is_empty() || !self.memory_islands.is_empty())
            && (self.actionable_compiled_condition_count() > 0
                || self
                    .worker_islands
                    .iter()
                    .any(|island| !island.actionable_terms().is_empty())
                || self
                    .memory_islands
                    .iter()
                    .any(|island| !island.actionable_terms().is_empty()))
    }

    pub fn exact_compiled_condition_count(&self) -> usize {
        if self.worker_islands.is_empty() {
            self.control_islands
                .iter()
                .flat_map(|island| island.facts.iter())
                .filter(|fact| fact.evidence.allows_hard_proof())
                .count()
        } else {
            self.worker_islands
                .iter()
                .flat_map(|island| island.control_facts.iter())
                .filter(|fact| fact.evidence.allows_hard_proof())
                .count()
        }
    }

    pub fn actionable_compiled_condition_count(&self) -> usize {
        if self.worker_islands.is_empty() {
            self.control_islands
                .iter()
                .flat_map(|island| island.facts.iter())
                .filter(|fact| fact.evidence.allows_narrowing())
                .count()
        } else {
            self.worker_islands
                .iter()
                .flat_map(|island| island.control_facts.iter())
                .filter(|fact| fact.evidence.allows_narrowing())
                .count()
        }
    }
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
                    .is_some_and(|compiled| compiled.evidence.allows_narrowing()) =>
            {
                Some(self.true_target)
            }
            (SymbolicReachabilityStatus::Unreachable, SymbolicReachabilityStatus::Reachable)
                if self
                    .false_compiled
                    .as_ref()
                    .is_some_and(|compiled| compiled.evidence.allows_narrowing()) =>
            {
                Some(self.false_target)
            }
            _ => None,
        }
    }

    pub fn exact_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        match (self.true_status, self.false_status) {
            (SymbolicReachabilityStatus::Reachable, SymbolicReachabilityStatus::Unreachable) => {
                self.true_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence.allows_hard_proof())
            }
            (SymbolicReachabilityStatus::Unreachable, SymbolicReachabilityStatus::Reachable) => {
                self.false_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence.allows_hard_proof())
            }
            _ => None,
        }
    }

    pub fn actionable_compiled_condition(&self) -> Option<&SymbolicCompiledCondition> {
        match (self.true_status, self.false_status) {
            (SymbolicReachabilityStatus::Reachable, SymbolicReachabilityStatus::Unreachable) => {
                self.true_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence.allows_narrowing())
            }
            (SymbolicReachabilityStatus::Unreachable, SymbolicReachabilityStatus::Reachable) => {
                self.false_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence.allows_narrowing())
            }
            _ => None,
        }
    }
}

fn unique_compiled_control_condition<'a>(
    facts: impl Iterator<Item = &'a SymbolicControlFact>,
    hard_proof_only: bool,
) -> Option<&'a SymbolicCompiledCondition> {
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

fn compiled_condition_precision_rank(condition: &SymbolicCompiledCondition) -> u8 {
    match condition.precision {
        SymbolicConditionPrecision::Exact => 3,
        SymbolicConditionPrecision::OverApprox => 2,
        SymbolicConditionPrecision::ResidualSearchRequired => 1,
        SymbolicConditionPrecision::Unsupported => 0,
    }
}

fn compiled_condition_evidence_rank(condition: &SymbolicCompiledCondition) -> u8 {
    match condition.evidence.tier {
        SymbolicSemanticConfidence::Exact => 3,
        SymbolicSemanticConfidence::Likely => 2,
        SymbolicSemanticConfidence::Heuristic => 1,
        SymbolicSemanticConfidence::Residual => 0,
    }
}

fn best_target_compiled_condition<'a>(
    candidates: impl Iterator<Item = &'a SymbolicCompiledCondition>,
) -> Option<&'a SymbolicCompiledCondition> {
    candidates.max_by(|left, right| {
        (
            compiled_condition_evidence_rank(left),
            compiled_condition_precision_rank(left),
            std::cmp::Reverse(left.backward_memory_residual_fallbacks),
            left.memory_terms.len(),
            left.supported_paths,
            std::cmp::Reverse(left.total_paths),
            std::cmp::Reverse(left.simplified.len()),
        )
            .cmp(&(
                compiled_condition_evidence_rank(right),
                compiled_condition_precision_rank(right),
                std::cmp::Reverse(right.backward_memory_residual_fallbacks),
                right.memory_terms.len(),
                right.supported_paths,
                std::cmp::Reverse(right.total_paths),
                std::cmp::Reverse(right.simplified.len()),
            ))
    })
}

fn target_compiled_condition(
    facts: &SymbolicSemanticFacts,
    target_addr: u64,
    hard_proof_only: bool,
) -> Option<&SymbolicCompiledCondition> {
    let branch_candidates = facts.branch_facts.iter().flat_map(|fact| {
        let mut candidates = Vec::new();
        if fact.true_target == target_addr {
            let compiled = if hard_proof_only {
                fact.true_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence.allows_hard_proof())
            } else {
                fact.true_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence.allows_narrowing())
            };
            if let Some(compiled) = compiled {
                candidates.push(compiled);
            }
        }
        if fact.false_target == target_addr {
            let compiled = if hard_proof_only {
                fact.false_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence.allows_hard_proof())
            } else {
                fact.false_compiled
                    .as_ref()
                    .filter(|compiled| compiled.evidence.allows_narrowing())
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

fn unique_reachable_control_target<'a>(
    facts: impl Iterator<Item = &'a SymbolicControlFact>,
    hard_proof_only: bool,
) -> Option<u64> {
    let mut reachable_target = None;
    let mut saw_any = false;
    for fact in facts {
        saw_any = true;
        if hard_proof_only && !fact.evidence.allows_hard_proof() {
            return None;
        }
        if !hard_proof_only && !fact.evidence.allows_narrowing() {
            return None;
        }
        match fact.status {
            SymbolicReachabilityStatus::Reachable => {
                if reachable_target.replace(fact.target).is_some() {
                    return None;
                }
            }
            SymbolicReachabilityStatus::Unreachable => {}
            SymbolicReachabilityStatus::Unknown => return None,
        }
    }
    saw_any.then_some(reachable_target).flatten()
}

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
    pub field_type: Option<String>,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisibleBindingKind {
    Param,
    Local,
    StackObject,
    HiddenHome,
    HiddenSaved,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VisibleBinding {
    pub name: String,
    pub ty: Option<CTypeLike>,
    pub kind: VisibleBindingKind,
    pub stack_slot: Option<StackSlotKey>,
    pub param_index: Option<usize>,
    pub source_reg: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CalleeArgEffect {
    pub read: bool,
    pub write: bool,
    pub escape: bool,
    pub free: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeMemoryEffectKind {
    Read,
    Write,
    Escape,
    Free,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalleeMemoryRegion {
    Arg { index: usize },
    Global { address: u64 },
    HeapReturn,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryRange {
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub width: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryLocation {
    pub region: CalleeMemoryRegion,
    pub range: Option<CalleeMemoryRange>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeMemoryEffect {
    pub kind: CalleeMemoryEffectKind,
    pub location: CalleeMemoryLocation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CalleeReturnRelation {
    Unknown,
    Void,
    Arg(usize),
    Const(u64),
    HeapAlloc,
    Global(u64),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalleeFact {
    pub function_id: u64,
    pub name: Option<String>,
    pub direct_callees: Vec<u64>,
    pub callsite_count: usize,
    pub has_unknown_calls: bool,
    pub arg_effects: BTreeMap<usize, CalleeArgEffect>,
    pub memory_effects: Vec<CalleeMemoryEffect>,
    pub param_type_hints: BTreeMap<usize, CTypeLike>,
    pub return_type_hint: Option<CTypeLike>,
    pub return_relation: CalleeReturnRelation,
    pub reads_global_memory: bool,
    pub writes_global_memory: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InterprocFactDiagnostics {
    pub iterations: usize,
    pub max_iterations: usize,
    pub converged: bool,
    pub scope_size: usize,
    pub scc_count: usize,
    pub max_scc_size: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFacts {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub visible_bindings: Vec<VisibleBinding>,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    // Legacy compatibility view derived from canonical stack_slots when available.
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub symbolic_facts: SymbolicSemanticFacts,
    pub interproc_diagnostics: InterprocFactDiagnostics,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionTypeFactInputs {
    pub merged_signature: Option<FunctionSignatureSpec>,
    pub known_function_signatures: HashMap<String, FunctionType>,
    pub register_params: Vec<ExternalRegisterParamSpec>,
    pub stack_slots: BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub visible_bindings: Vec<VisibleBinding>,
    pub callee_facts: BTreeMap<u64, CalleeFact>,
    pub external_stack_vars: HashMap<i64, ExternalStackVarSpec>,
    pub external_type_db: ExternalTypeDb,
    pub slot_type_overrides: HashMap<usize, String>,
    pub slot_field_profiles: HashMap<usize, BTreeMap<u64, String>>,
    pub symbolic_facts: SymbolicSemanticFacts,
    pub local_field_accesses: Vec<LocalFieldAccessFact>,
    pub interproc_diagnostics: InterprocFactDiagnostics,
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
            && self.visible_bindings.is_empty()
            && self.callee_facts.is_empty()
            && self.external_stack_vars.is_empty()
            && self.external_type_db.structs.is_empty()
            && self.external_type_db.unions.is_empty()
            && self.external_type_db.enums.is_empty()
            && self.external_type_db.diagnostics.is_empty()
            && self.slot_type_overrides.is_empty()
            && self.slot_field_profiles.is_empty()
            && self.symbolic_facts.is_empty()
            && self.interproc_diagnostics == InterprocFactDiagnostics::default()
            && self.diagnostics.is_empty()
    }

    pub fn canonicalized(self) -> Self {
        FunctionTypeFacts::builder(FunctionTypeFactInputs {
            merged_signature: self.merged_signature,
            known_function_signatures: self.known_function_signatures,
            register_params: self.register_params,
            stack_slots: self.stack_slots,
            visible_bindings: self.visible_bindings,
            callee_facts: self.callee_facts,
            external_stack_vars: self.external_stack_vars,
            external_type_db: self.external_type_db,
            slot_type_overrides: self.slot_type_overrides,
            slot_field_profiles: self.slot_field_profiles,
            symbolic_facts: self.symbolic_facts,
            local_field_accesses: Vec::new(),
            interproc_diagnostics: self.interproc_diagnostics,
            diagnostics: self.diagnostics,
        })
        .build()
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

        let FunctionTypeFactInputs {
            merged_signature,
            known_function_signatures,
            register_params,
            mut stack_slots,
            visible_bindings,
            callee_facts,
            external_stack_vars,
            external_type_db,
            slot_type_overrides,
            slot_field_profiles,
            symbolic_facts,
            interproc_diagnostics,
            diagnostics,
            ..
        } = self.inputs;

        if stack_slots.is_empty() && !external_stack_vars.is_empty() {
            stack_slots = stack_slots_from_legacy_external_stack_vars(&external_stack_vars);
        }

        let external_stack_vars = if stack_slots.is_empty() {
            external_stack_vars
        } else {
            legacy_external_stack_vars_from_slots(&stack_slots)
        };

        let mut diagnostics = diagnostics;
        diagnostics.extend(external_type_db.diagnostics.iter().cloned());
        dedup_preserving_order(&mut diagnostics);

        FunctionTypeFacts {
            merged_signature,
            known_function_signatures,
            register_params,
            stack_slots,
            visible_bindings,
            callee_facts,
            external_stack_vars,
            external_type_db,
            slot_type_overrides,
            slot_field_profiles,
            symbolic_facts,
            interproc_diagnostics,
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
            .or_insert_with(|| {
                access
                    .field_type
                    .clone()
                    .unwrap_or_else(|| access.field_name.clone())
            });
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
    let qualifier_filtered = ty
        .split_whitespace()
        .filter(|token| {
            !matches!(
                token.to_ascii_lowercase().as_str(),
                "const"
                    | "volatile"
                    | "restrict"
                    | "__restrict"
                    | "__restrict__"
                    | "__const"
                    | "__const__"
                    | "__volatile"
                    | "__volatile__"
            )
        })
        .collect::<Vec<_>>();
    let qualifier_filtered_storage = (qualifier_filtered.len() != ty.split_whitespace().count())
        .then(|| qualifier_filtered.join(" "));
    if let Some(filtered) = qualifier_filtered_storage.as_deref() {
        ty = filtered.trim();
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
    use crate::{ExternalStackBase, ExternalStackSlotRole};

    #[test]
    fn builder_merges_local_field_accesses_into_slot_profiles() {
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            local_field_accesses: vec![
                LocalFieldAccessFact {
                    slot: 1,
                    field_offset: 0,
                    field_name: "first".to_string(),
                    field_type: None,
                },
                LocalFieldAccessFact {
                    slot: 1,
                    field_offset: 8,
                    field_name: "second".to_string(),
                    field_type: None,
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
                field_type: None,
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
    fn builder_prefers_local_field_access_type_when_present() {
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            local_field_accesses: vec![LocalFieldAccessFact {
                slot: 3,
                field_offset: 4,
                field_name: "f_4".to_string(),
                field_type: Some("int32_t".to_string()),
            }],
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .slot_field_profiles
                .get(&3)
                .and_then(|profile| profile.get(&4)),
            Some(&"int32_t".to_string())
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

    #[test]
    fn builder_derives_legacy_stack_var_view_from_canonical_slots() {
        let spec = ExternalStackSlotSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            stack_slots: BTreeMap::from([(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -0x10,
                },
                spec.clone(),
            )]),
            external_stack_vars: HashMap::from([(
                -0x10,
                ExternalStackSlotSpec {
                    name: "stale".to_string(),
                    ..spec.clone()
                },
            )]),
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts
                .external_stack_vars
                .get(&-0x10)
                .map(|slot| slot.name.as_str()),
            Some("count")
        );
    }

    #[test]
    fn builder_canonicalizes_stack_slots_from_legacy_input() {
        let spec = ExternalStackSlotSpec {
            name: "count".to_string(),
            ty: Some(CTypeLike::Int {
                bits: 32,
                signedness: Signedness::Signed,
            }),
            base: ExternalStackBase::FramePointer,
            role: ExternalStackSlotRole::Local,
            param_index: None,
            param_name: None,
            source_reg: None,
        };
        let facts = FunctionTypeFacts::builder(FunctionTypeFactInputs {
            external_stack_vars: HashMap::from([(-0x10, spec)]),
            ..FunctionTypeFactInputs::default()
        })
        .build();

        assert_eq!(
            facts.stack_slots.get(&StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset: -0x10,
            }),
            facts.external_stack_vars.get(&-0x10)
        );
    }

    #[test]
    fn parse_type_like_spec_accepts_const_qualified_pointers() {
        let signed_char_ptr = CTypeLike::Pointer(Box::new(CTypeLike::Int {
            bits: 8,
            signedness: Signedness::Signed,
        }));
        let void_ptr = CTypeLike::Pointer(Box::new(CTypeLike::Void));

        assert_eq!(
            parse_type_like_spec("char const *", 64),
            Some(signed_char_ptr.clone())
        );
        assert_eq!(
            parse_type_like_spec("const char *", 64),
            Some(signed_char_ptr)
        );
        assert_eq!(parse_type_like_spec("void const *", 64), Some(void_ptr));
    }

    #[test]
    fn symbolic_vm_value_expr_renders_recursive_forms() {
        let expr = SymbolicVmValueExpr::Binary {
            op: SymbolicVmBinaryOp::Add,
            left: Box::new(SymbolicVmValueExpr::Unary {
                op: SymbolicVmUnaryOp::Neg,
                expr: Box::new(SymbolicVmValueExpr::Const(0x10)),
            }),
            right: Box::new(SymbolicVmValueExpr::Binary {
                op: SymbolicVmBinaryOp::Xor,
                left: Box::new(SymbolicVmValueExpr::Var("state".to_string())),
                right: Box::new(SymbolicVmValueExpr::Expr("mask".to_string())),
            }),
        };

        assert_eq!(expr.render(), "((-0x10) + (state ^ mask))");
    }

    #[test]
    fn symbolic_vm_value_expr_evaluates_recursive_forms() {
        let expr = SymbolicVmValueExpr::Binary {
            op: SymbolicVmBinaryOp::Add,
            left: Box::new(SymbolicVmValueExpr::Var("state_0".to_string())),
            right: Box::new(SymbolicVmValueExpr::Binary {
                op: SymbolicVmBinaryOp::Mul,
                left: Box::new(SymbolicVmValueExpr::Const(2)),
                right: Box::new(SymbolicVmValueExpr::Const(3)),
            }),
        };
        let bindings = BTreeMap::from([(String::from("state"), 4u64)]);
        assert_eq!(expr.evaluate_u64(&bindings), Some(10));
    }

    #[test]
    fn symbolic_vm_transfer_arm_evaluates_exact_exit_guard_for_case() {
        let arm = SymbolicVmTransferArm {
            handler_target: 0x1004,
            case_values: vec![1],
            region_blocks: vec![0x1004],
            exit_targets: vec![0x1010],
            exit_guards: vec![SymbolicVmGuardedExit {
                target: 0x1010,
                guard: SymbolicVmGuardCondition {
                    expr: "(vm.sel == 0x1)".to_string(),
                    value: SymbolicVmValueExpr::Binary {
                        op: SymbolicVmBinaryOp::Eq,
                        left: Box::new(SymbolicVmValueExpr::Var("vm.sel".to_string())),
                        right: Box::new(SymbolicVmValueExpr::Const(1)),
                    },
                    expect_nonzero: true,
                    exact: true,
                    evidence: SymbolicSemanticEvidence::exact(),
                    confidence: SymbolicSemanticConfidence::Exact,
                },
            }],
            state_updates: Vec::new(),
            selector_update: None,
            memory_reads: Vec::new(),
            memory_writes: Vec::new(),
            residual_guards: false,
            residual_memory_effects: false,
            exact: true,
            evidence: SymbolicSemanticEvidence::exact(),
            confidence: SymbolicSemanticConfidence::Exact,
            redispatch: false,
            may_return: true,
            truncated: false,
        };

        assert_eq!(
            arm.exact_exit_guard_result_for_case(Some("vm.sel"), 1, 0x1010),
            Some(true)
        );
        assert_eq!(
            arm.exact_exit_guard_result_for_case(Some("vm.sel"), 2, 0x1010),
            Some(false)
        );
    }

    #[test]
    fn control_island_actionable_condition_requires_unique_fact() {
        let compiled = SymbolicCompiledCondition {
            simplified: "false".to_string(),
            terms: vec!["false".to_string()],
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: SymbolicConditionPrecision::OverApprox,
            evidence: SymbolicSemanticEvidence::likely(
                SymbolicSemanticEvidenceReason::PartialPathCoverage,
            ),
            confidence: SymbolicSemanticConfidence::Likely,
            supported_paths: 1,
            total_paths: 2,
        };
        let island = SymbolicControlIsland {
            kind: SymbolicControlIslandKind::LargeCfgBranchFrontier,
            anchor_block: 0x401000,
            frontier_targets: vec![0x401010, 0x401020],
            facts: vec![
                SymbolicControlFact {
                    target: 0x401010,
                    status: SymbolicReachabilityStatus::Unknown,
                    condition: Some("false".to_string()),
                    compiled: Some(compiled.clone()),
                    evidence: SymbolicSemanticEvidence::likely(
                        SymbolicSemanticEvidenceReason::PartialPathCoverage,
                    ),
                    confidence: SymbolicSemanticConfidence::Likely,
                },
                SymbolicControlFact {
                    target: 0x401020,
                    status: SymbolicReachabilityStatus::Unknown,
                    condition: None,
                    compiled: None,
                    evidence: SymbolicSemanticEvidence::residual(
                        SymbolicSemanticEvidenceReason::GuardOpaque,
                    ),
                    confidence: SymbolicSemanticConfidence::Residual,
                },
            ],
            evidence: SymbolicSemanticEvidence::likely(
                SymbolicSemanticEvidenceReason::PartialPathCoverage,
            ),
            confidence: SymbolicSemanticConfidence::Likely,
        };

        assert_eq!(
            island
                .actionable_compiled_condition()
                .map(|cond| cond.simplified.as_str()),
            Some("false")
        );
    }

    #[test]
    fn semantic_facts_actionable_condition_for_block_uses_control_island_fallback() {
        let compiled = SymbolicCompiledCondition {
            simplified: "x == 0".to_string(),
            terms: vec!["x == 0".to_string()],
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: SymbolicConditionPrecision::Exact,
            evidence: SymbolicSemanticEvidence::exact(),
            confidence: SymbolicSemanticConfidence::Exact,
            supported_paths: 1,
            total_paths: 1,
        };
        let facts = SymbolicSemanticFacts {
            branch_facts: Vec::new(),
            worker_islands: Vec::new(),
            control_islands: vec![SymbolicControlIsland {
                kind: SymbolicControlIslandKind::LargeCfgBranchFrontier,
                anchor_block: 0x401000,
                frontier_targets: vec![0x401020],
                facts: vec![SymbolicControlFact {
                    target: 0x401020,
                    status: SymbolicReachabilityStatus::Reachable,
                    condition: Some("x == 0".to_string()),
                    compiled: Some(compiled.clone()),
                    evidence: SymbolicSemanticEvidence::exact(),
                    confidence: SymbolicSemanticConfidence::Exact,
                }],
                evidence: SymbolicSemanticEvidence::exact(),
                confidence: SymbolicSemanticConfidence::Exact,
            }],
            memory_islands: Vec::new(),
            diagnostics: SymbolicFactDiagnostics::default(),
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        };

        assert_eq!(
            facts
                .actionable_compiled_condition_for_block(0x401000)
                .map(|cond| cond.simplified.as_str()),
            Some("x == 0")
        );
    }

    #[test]
    fn semantic_facts_actionable_condition_for_target_prefers_best_candidate() {
        let exact = SymbolicCompiledCondition {
            simplified: "x == 0".to_string(),
            terms: vec!["x == 0".to_string()],
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: SymbolicConditionPrecision::Exact,
            evidence: SymbolicSemanticEvidence::exact(),
            confidence: SymbolicSemanticConfidence::Exact,
            supported_paths: 1,
            total_paths: 1,
        };
        let likely = SymbolicCompiledCondition {
            simplified: "x <= 1".to_string(),
            terms: vec!["x <= 1".to_string()],
            memory_terms: vec![SymbolicMemoryCondition {
                region: SymbolicMemoryRegion::Argument { index: 0 },
                offset_lo: 8,
                offset_hi: 12,
                size: 4,
                exact_offset: false,
                expr: "*(arg0 + [8,12])".to_string(),
                binding: None,
                value_expr: None,
                exact_value: false,
                evidence: SymbolicSemanticEvidence::likely(
                    SymbolicSemanticEvidenceReason::DerivedFromRanking,
                ),
                confidence: SymbolicSemanticConfidence::Likely,
            }],
            backward_memory_substitutions: 1,
            backward_memory_candidate_enumerations: 1,
            backward_memory_residual_fallbacks: 0,
            precision: SymbolicConditionPrecision::OverApprox,
            evidence: SymbolicSemanticEvidence::likely(
                SymbolicSemanticEvidenceReason::PartialPathCoverage,
            ),
            confidence: SymbolicSemanticConfidence::Likely,
            supported_paths: 1,
            total_paths: 2,
        };
        let facts = SymbolicSemanticFacts {
            branch_facts: vec![
                SymbolicBranchFact {
                    block_addr: 0x401000,
                    true_target: 0x401010,
                    false_target: 0x401020,
                    true_status: SymbolicReachabilityStatus::Reachable,
                    false_status: SymbolicReachabilityStatus::Unreachable,
                    true_condition: Some("x == 0".to_string()),
                    false_condition: Some("x != 0".to_string()),
                    true_compiled: Some(exact.clone()),
                    false_compiled: None,
                },
                SymbolicBranchFact {
                    block_addr: 0x401030,
                    true_target: 0x401010,
                    false_target: 0x401040,
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
            diagnostics: SymbolicFactDiagnostics::default(),
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        };

        assert_eq!(
            facts
                .actionable_compiled_condition_for_target(0x401010)
                .map(|cond| cond.simplified.as_str()),
            Some("x == 0")
        );
    }

    #[test]
    fn semantic_facts_exact_reachable_target_for_block_uses_control_island_fallback() {
        let facts = SymbolicSemanticFacts {
            branch_facts: Vec::new(),
            worker_islands: Vec::new(),
            control_islands: vec![SymbolicControlIsland {
                kind: SymbolicControlIslandKind::LargeCfgBranchFrontier,
                anchor_block: 0x401000,
                frontier_targets: vec![0x401010, 0x401020],
                facts: vec![
                    SymbolicControlFact {
                        target: 0x401010,
                        status: SymbolicReachabilityStatus::Reachable,
                        condition: Some("x == 0".to_string()),
                        compiled: None,
                        evidence: SymbolicSemanticEvidence::exact(),
                        confidence: SymbolicSemanticConfidence::Exact,
                    },
                    SymbolicControlFact {
                        target: 0x401020,
                        status: SymbolicReachabilityStatus::Unreachable,
                        condition: Some("!(x == 0)".to_string()),
                        compiled: None,
                        evidence: SymbolicSemanticEvidence::exact(),
                        confidence: SymbolicSemanticConfidence::Exact,
                    },
                ],
                evidence: SymbolicSemanticEvidence::exact(),
                confidence: SymbolicSemanticConfidence::Exact,
            }],
            memory_islands: Vec::new(),
            diagnostics: SymbolicFactDiagnostics::default(),
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        };

        assert_eq!(
            facts.exact_reachable_target_for_block(0x401000),
            Some(0x401010)
        );
    }

    #[test]
    fn semantic_facts_actionable_reachable_target_for_block_uses_likely_control_island() {
        let compiled = SymbolicCompiledCondition {
            simplified: "x == 0".to_string(),
            terms: vec!["x == 0".to_string()],
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: SymbolicConditionPrecision::OverApprox,
            evidence: SymbolicSemanticEvidence::likely(
                SymbolicSemanticEvidenceReason::PartialPathCoverage,
            ),
            confidence: SymbolicSemanticConfidence::Likely,
            supported_paths: 1,
            total_paths: 2,
        };
        let facts = SymbolicSemanticFacts {
            branch_facts: Vec::new(),
            worker_islands: Vec::new(),
            control_islands: vec![SymbolicControlIsland {
                kind: SymbolicControlIslandKind::LargeCfgBranchFrontier,
                anchor_block: 0x401000,
                frontier_targets: vec![0x401010, 0x401020],
                facts: vec![
                    SymbolicControlFact {
                        target: 0x401010,
                        status: SymbolicReachabilityStatus::Reachable,
                        condition: Some("x == 0".to_string()),
                        compiled: Some(compiled.clone()),
                        evidence: SymbolicSemanticEvidence::likely(
                            SymbolicSemanticEvidenceReason::PartialPathCoverage,
                        ),
                        confidence: SymbolicSemanticConfidence::Likely,
                    },
                    SymbolicControlFact {
                        target: 0x401020,
                        status: SymbolicReachabilityStatus::Unreachable,
                        condition: Some("!(x == 0)".to_string()),
                        compiled: Some(compiled),
                        evidence: SymbolicSemanticEvidence::likely(
                            SymbolicSemanticEvidenceReason::PartialPathCoverage,
                        ),
                        confidence: SymbolicSemanticConfidence::Likely,
                    },
                ],
                evidence: SymbolicSemanticEvidence::likely(
                    SymbolicSemanticEvidenceReason::PartialPathCoverage,
                ),
                confidence: SymbolicSemanticConfidence::Likely,
            }],
            memory_islands: Vec::new(),
            diagnostics: SymbolicFactDiagnostics::default(),
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        };

        assert_eq!(
            facts.actionable_reachable_target_for_block(0x401000),
            Some(0x401010)
        );
    }

    #[test]
    fn semantic_facts_actionable_memory_terms_for_block_use_memory_island_fallback() {
        let facts = SymbolicSemanticFacts {
            branch_facts: Vec::new(),
            worker_islands: Vec::new(),
            control_islands: Vec::new(),
            memory_islands: vec![SymbolicMemoryIsland {
                kind: SymbolicMemoryIslandKind::LargeCfgConditionFrontier,
                anchor_block: 0x401000,
                terms: vec![SymbolicMemoryCondition {
                    region: SymbolicMemoryRegion::Argument { index: 0 },
                    offset_lo: 8,
                    offset_hi: 8,
                    size: 4,
                    exact_offset: true,
                    evidence: SymbolicSemanticEvidence::exact(),
                    confidence: SymbolicSemanticConfidence::Exact,
                    binding: Some("arg0".to_string()),
                    expr: "*(arg0 + 8)".to_string(),
                    value_expr: None,
                    exact_value: false,
                }],
                evidence: SymbolicSemanticEvidence::exact(),
                confidence: SymbolicSemanticConfidence::Exact,
            }],
            diagnostics: SymbolicFactDiagnostics::default(),
            interpreter: None,
            vm_step: None,
            vm_transfer: None,
        };

        let terms = facts.actionable_memory_terms_for_block(0x401000);
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0].offset_lo, 8);
        assert_eq!(terms[0].binding.as_deref(), Some("arg0"));
    }

    #[test]
    fn structured_decompile_ready_allows_supported_worker_with_wide_frontier() {
        let facts = SymbolicSemanticFacts {
            worker_islands: vec![SymbolicWorkerIsland {
                anchor_block: 0x401000,
                control_kind: Some(SymbolicControlIslandKind::LargeCfgBranchFrontier),
                memory_kind: Some(SymbolicMemoryIslandKind::LargeCfgConditionFrontier),
                frontier_targets: vec![0x401010, 0x401020, 0x401030],
                control_facts: vec![SymbolicControlFact {
                    target: 0x401010,
                    status: SymbolicReachabilityStatus::Reachable,
                    condition: Some("x == 0".to_string()),
                    compiled: Some(SymbolicCompiledCondition {
                        simplified: "x == 0".to_string(),
                        terms: vec!["x == 0".to_string()],
                        memory_terms: vec![SymbolicMemoryCondition {
                            region: SymbolicMemoryRegion::Argument { index: 0 },
                            offset_lo: 0,
                            offset_hi: 0,
                            size: 1,
                            exact_offset: true,
                            evidence: SymbolicSemanticEvidence::likely(
                                SymbolicSemanticEvidenceReason::PartialPathCoverage,
                            ),
                            confidence: SymbolicSemanticConfidence::Likely,
                            binding: None,
                            expr: "*arg0".to_string(),
                            value_expr: Some("0x0:8".to_string()),
                            exact_value: true,
                        }],
                        backward_memory_substitutions: 0,
                        backward_memory_candidate_enumerations: 0,
                        backward_memory_residual_fallbacks: 0,
                        precision: SymbolicConditionPrecision::OverApprox,
                        evidence: SymbolicSemanticEvidence::likely(
                            SymbolicSemanticEvidenceReason::PartialPathCoverage,
                        ),
                        confidence: SymbolicSemanticConfidence::Likely,
                        supported_paths: 1,
                        total_paths: 2,
                    }),
                    evidence: SymbolicSemanticEvidence::likely(
                        SymbolicSemanticEvidenceReason::PartialPathCoverage,
                    ),
                    confidence: SymbolicSemanticConfidence::Likely,
                }],
                memory_terms: vec![SymbolicMemoryCondition {
                    region: SymbolicMemoryRegion::Argument { index: 0 },
                    offset_lo: 0,
                    offset_hi: 0,
                    size: 1,
                    exact_offset: true,
                    evidence: SymbolicSemanticEvidence::likely(
                        SymbolicSemanticEvidenceReason::PartialPathCoverage,
                    ),
                    confidence: SymbolicSemanticConfidence::Likely,
                    binding: None,
                    expr: "*arg0".to_string(),
                    value_expr: Some("0x0:8".to_string()),
                    exact_value: true,
                }],
                evidence: SymbolicSemanticEvidence::likely(
                    SymbolicSemanticEvidenceReason::PartialPathCoverage,
                ),
                confidence: SymbolicSemanticConfidence::Likely,
            }],
            diagnostics: SymbolicFactDiagnostics {
                skipped_large_cfg: true,
                semantic_mode: Some(SymbolicSemanticMode::IslandCompiled),
                semantic_capability: Some(SymbolicSemanticCapability {
                    query_ready: true,
                    type_ready: true,
                    decompile_ready: true,
                }),
                slice_class: Some(SymbolicSemanticSliceClass::Worker),
                residual_reasons: Vec::new(),
                ..Default::default()
            },
            ..Default::default()
        };

        assert!(facts.structured_decompile_ready());
    }
}
