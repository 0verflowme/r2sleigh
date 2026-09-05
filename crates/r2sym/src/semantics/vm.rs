use std::collections::{BTreeMap, BTreeSet, VecDeque};

use r2ssa::cfg::BlockTerminator;
use r2ssa::{
    CFGEdge, CompareKind, InstPayload, ObjectKind, SSAOp, SSAVar, SsaArtifact, StackAddressBase,
    ValueId,
};
use serde::{Deserialize, Serialize};

use super::{
    SemanticConfidence, SemanticEvidence, SemanticEvidenceAmbiguity, SemanticEvidenceCoverage,
    SemanticEvidenceProvenance, SemanticEvidenceReason,
};
use crate::{MemoryRegionKind, SemanticMemoryAddress};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum InterpreterKind {
    SwitchDispatch,
    IndirectDispatch,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterpreterDispatchSummary {
    pub kind: InterpreterKind,
    pub dispatch_header: u64,
    pub dispatch_targets: usize,
    pub selector: Option<String>,
    pub back_edges: usize,
    pub score: i32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum VmUnaryOp {
    Neg,
    BitNot,
    BoolNot,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum VmBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
    Eq,
    Ne,
    Lt,
    SLt,
    Le,
    SLe,
    BoolAnd,
    BoolOr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum VmValueExpr {
    Const(u64),
    Var(String),
    Unary {
        op: VmUnaryOp,
        arg: Box<VmValueExpr>,
    },
    Binary {
        op: VmBinaryOp,
        lhs: Box<VmValueExpr>,
        rhs: Box<VmValueExpr>,
    },
    Select {
        cond: Box<VmValueExpr>,
        if_true: Box<VmValueExpr>,
        if_false: Box<VmValueExpr>,
    },
    Expr(String),
}

impl VmValueExpr {
    fn render_unary(op: &VmUnaryOp) -> &'static str {
        match op {
            VmUnaryOp::Neg => "-",
            VmUnaryOp::BitNot => "~",
            VmUnaryOp::BoolNot => "!",
        }
    }

    fn render_binary(op: &VmBinaryOp) -> &'static str {
        match op {
            VmBinaryOp::Add => "+",
            VmBinaryOp::Sub => "-",
            VmBinaryOp::Mul => "*",
            VmBinaryOp::Div => "/",
            VmBinaryOp::Rem => "%",
            VmBinaryOp::And => "&",
            VmBinaryOp::Or => "|",
            VmBinaryOp::Xor => "^",
            VmBinaryOp::Shl => "<<",
            VmBinaryOp::LShr | VmBinaryOp::AShr => ">>",
            VmBinaryOp::Eq => "==",
            VmBinaryOp::Ne => "!=",
            VmBinaryOp::Lt | VmBinaryOp::SLt => "<",
            VmBinaryOp::Le | VmBinaryOp::SLe => "<=",
            VmBinaryOp::BoolAnd => "&&",
            VmBinaryOp::BoolOr => "||",
        }
    }

    fn render(&self) -> String {
        match self {
            Self::Const(value) => format!("0x{value:x}"),
            Self::Var(name) | Self::Expr(name) => name.clone(),
            Self::Unary { op, arg } => {
                format!("({}{})", Self::render_unary(op), arg.render())
            }
            Self::Binary { op, lhs, rhs } => format!(
                "({} {} {})",
                lhs.render(),
                Self::render_binary(op),
                rhs.render()
            ),
            Self::Select {
                cond,
                if_true,
                if_false,
            } => format!(
                "({} ? {} : {})",
                cond.render(),
                if_true.render(),
                if_false.render()
            ),
        }
    }

    fn is_exact(&self) -> bool {
        match self {
            Self::Const(_) | Self::Var(_) => true,
            Self::Unary { arg, .. } => arg.is_exact(),
            Self::Binary { lhs, rhs, .. } => lhs.is_exact() && rhs.is_exact(),
            Self::Select {
                cond,
                if_true,
                if_false,
            } => cond.is_exact() && if_true.is_exact() && if_false.is_exact(),
            Self::Expr(_) => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmGuardCondition {
    pub expr: String,
    pub value: VmValueExpr,
    pub expect_nonzero: bool,
    pub exact: bool,
}

impl VmGuardCondition {
    pub fn evidence(&self) -> SemanticEvidence {
        if self.exact {
            SemanticEvidence::exact()
        } else if !matches!(self.value, VmValueExpr::Expr(_)) {
            SemanticEvidence::likely(SemanticEvidenceReason::GuardOpaque)
                .with_provenance(SemanticEvidenceProvenance::Normalized)
        } else {
            SemanticEvidence::heuristic(SemanticEvidenceReason::GuardOpaque)
                .with_provenance(SemanticEvidenceProvenance::Ranked)
        }
    }

    pub fn confidence(&self) -> SemanticConfidence {
        self.evidence().tier
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmGuardedExit {
    pub target: u64,
    pub guard: VmGuardCondition,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmMemoryRegionRef {
    pub id: u32,
    pub kind: MemoryRegionKind,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmMemoryCondition {
    pub region: VmMemoryRegionRef,
    #[serde(flatten)]
    pub address: SemanticMemoryAddress,
    pub size: u32,
    pub binding: Option<String>,
    pub expr: String,
    pub value_expr: Option<String>,
    pub value: Option<VmValueExpr>,
    pub exact_value: bool,
}

impl VmMemoryCondition {
    pub fn evidence(&self) -> SemanticEvidence {
        if self.address.has_exact_identity() && (self.value.is_none() || self.exact_value) {
            SemanticEvidence::exact()
        } else if self.binding.is_some() || self.address.has_exact_identity() {
            let reason = if self.address.has_exact_identity() {
                SemanticEvidenceReason::ValueOpaque
            } else {
                SemanticEvidenceReason::AliasAmbiguity
            };
            SemanticEvidence::likely(reason)
                .with_provenance(SemanticEvidenceProvenance::Normalized)
                .with_ambiguity(if self.address.has_exact_identity() {
                    SemanticEvidenceAmbiguity::Single
                } else {
                    SemanticEvidenceAmbiguity::Bounded
                })
        } else {
            SemanticEvidence::heuristic(SemanticEvidenceReason::AliasAmbiguity)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
        }
    }

    pub fn confidence(&self) -> SemanticConfidence {
        self.evidence().tier
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmStateUpdate {
    pub output: String,
    pub expr: String,
    pub value: VmValueExpr,
    pub exact: bool,
}

impl VmStateUpdate {
    pub fn evidence(&self) -> SemanticEvidence {
        if self.exact {
            SemanticEvidence::exact()
        } else if !matches!(self.value, VmValueExpr::Expr(_)) {
            SemanticEvidence::likely(SemanticEvidenceReason::ValueOpaque)
                .with_provenance(SemanticEvidenceProvenance::Normalized)
        } else {
            SemanticEvidence::heuristic(SemanticEvidenceReason::ValueOpaque)
                .with_provenance(SemanticEvidenceProvenance::Ranked)
        }
    }

    pub fn confidence(&self) -> SemanticConfidence {
        self.evidence().tier
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmTransferArm {
    pub handler_target: u64,
    pub case_values: Vec<u64>,
    pub region_blocks: Vec<u64>,
    pub exit_targets: Vec<u64>,
    pub exit_guards: Vec<VmGuardedExit>,
    pub state_updates: Vec<VmStateUpdate>,
    pub selector_update: Option<VmStateUpdate>,
    pub memory_reads: Vec<VmMemoryCondition>,
    pub memory_writes: Vec<VmMemoryCondition>,
    pub residual_guards: bool,
    pub residual_memory_effects: bool,
    pub exact: bool,
    pub redispatch: bool,
    pub may_return: bool,
    pub truncated: bool,
}

impl VmTransferArm {
    pub fn evidence(&self) -> SemanticEvidence {
        if self.exact {
            return SemanticEvidence::exact();
        }
        if self.truncated {
            return if self.case_values.is_empty()
                && self.exit_targets.is_empty()
                && self.state_updates.is_empty()
                && self.memory_reads.is_empty()
                && self.memory_writes.is_empty()
            {
                SemanticEvidence::residual(SemanticEvidenceReason::TruncatedTransfer)
                    .with_coverage(SemanticEvidenceCoverage::Partial)
                    .with_budget_limited(true)
            } else {
                SemanticEvidence::heuristic(SemanticEvidenceReason::TruncatedTransfer)
                    .with_coverage(SemanticEvidenceCoverage::Bounded)
                    .with_budget_limited(true)
            };
        }
        if !self.residual_guards
            && !self.residual_memory_effects
            && self
                .state_updates
                .iter()
                .all(|update| update.evidence().is_reliable())
            && self
                .selector_update
                .as_ref()
                .is_none_or(|update| update.evidence().is_reliable())
            && self
                .exit_guards
                .iter()
                .all(|guard| guard.guard.evidence().is_reliable())
            && self
                .memory_reads
                .iter()
                .all(|effect| effect.evidence().is_reliable())
            && self
                .memory_writes
                .iter()
                .all(|effect| effect.evidence().is_reliable())
        {
            let mut evidence =
                SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage)
                    .with_coverage(SemanticEvidenceCoverage::Bounded)
                    .with_provenance(SemanticEvidenceProvenance::Normalized);
            if self.redispatch || self.may_return {
                evidence = evidence.with_coverage(SemanticEvidenceCoverage::Partial);
            }
            return evidence;
        }
        if self.case_values.is_empty()
            && self.exit_targets.is_empty()
            && self.state_updates.is_empty()
            && self.memory_reads.is_empty()
            && self.memory_writes.is_empty()
        {
            SemanticEvidence::residual(SemanticEvidenceReason::PartialPathCoverage)
        } else {
            let mut evidence =
                SemanticEvidence::heuristic(SemanticEvidenceReason::DerivedFromRanking)
                    .with_coverage(SemanticEvidenceCoverage::Bounded);
            if self.residual_guards {
                evidence = evidence.with_reason(SemanticEvidenceReason::GuardOpaque);
            }
            if self.residual_memory_effects {
                evidence = evidence.with_reason(SemanticEvidenceReason::AliasAmbiguity);
            }
            evidence
        }
    }

    pub fn confidence(&self) -> SemanticConfidence {
        self.evidence().tier
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmStepSummary {
    pub kind: InterpreterKind,
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
    pub handler_state_updates: BTreeMap<u64, Vec<VmStateUpdate>>,
    pub handler_exit_guards: BTreeMap<u64, Vec<VmGuardedExit>>,
    pub handler_memory_read_effects: BTreeMap<u64, Vec<VmMemoryCondition>>,
    pub handler_memory_write_effects: BTreeMap<u64, Vec<VmMemoryCondition>>,
    pub handler_memory_reads: BTreeMap<u64, usize>,
    pub handler_memory_writes: BTreeMap<u64, usize>,
    pub handler_calls: BTreeMap<u64, usize>,
    pub handler_conditional_branches: BTreeMap<u64, usize>,
    pub handler_exit_targets: BTreeMap<u64, Vec<u64>>,
    pub redispatch_handlers: Vec<u64>,
    pub returning_handlers: Vec<u64>,
    pub truncated_handlers: Vec<u64>,
    pub transfers: Vec<VmTransferArm>,
}

impl VmStepSummary {
    pub fn has_strong_vm_evidence(&self) -> bool {
        let has_dispatch = self.dispatch_targets.len() >= 2 && !self.loop_latches.is_empty();
        let has_redispatch = !self.redispatch_handlers.is_empty()
            || self.transfers.iter().any(|transfer| transfer.redispatch);
        let has_handler_transfer_graph = !self.transfers.is_empty()
            && self
                .transfers
                .iter()
                .any(|transfer| !transfer.region_blocks.is_empty())
            && self
                .handler_regions
                .values()
                .any(|blocks| !blocks.is_empty());
        let has_state_update_evidence = self
            .handler_state_updates
            .values()
            .any(|updates| !updates.is_empty())
            || self
                .handler_memory_write_effects
                .values()
                .any(|writes| !writes.is_empty())
            || self.transfers.iter().any(|transfer| {
                !transfer.state_updates.is_empty()
                    || transfer.selector_update.is_some()
                    || !transfer.memory_writes.is_empty()
            });
        let has_selector_update_evidence = self.selector.as_ref().is_some_and(|selector| {
            self.handler_state_updates
                .values()
                .flatten()
                .any(|update| same_logical_name(&update.output, selector))
                || self
                    .transfers
                    .iter()
                    .any(|transfer| transfer.selector_update.is_some())
        });
        let distinct_cases = self
            .case_values_by_target
            .values()
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>();
        let has_proven_dispatch_partition = self.selector.is_some()
            && distinct_cases.len() >= self.dispatch_targets.len().saturating_sub(1)
            && !distinct_cases.is_empty();
        let has_usable_transfer = self.transfers.iter().any(|transfer| !transfer.truncated);

        has_dispatch
            && has_redispatch
            && has_handler_transfer_graph
            && has_state_update_evidence
            && has_proven_dispatch_partition
            && (has_selector_update_evidence || !self.loop_latches.is_empty())
            && has_usable_transfer
    }
}

pub fn strong_vm_step_summary(func: &SsaArtifact) -> Option<VmStepSummary> {
    classify_interpreter_like(func)
        .as_ref()
        .and_then(|dispatch| build_vm_step_summary(func, dispatch))
        .filter(VmStepSummary::has_strong_vm_evidence)
}

pub fn has_strong_vm_evidence(func: &SsaArtifact) -> bool {
    strong_vm_step_summary(func).is_some()
}

#[derive(Debug, Default)]
struct HandlerRegionSummary {
    blocks: Vec<u64>,
    state_inputs: Vec<String>,
    state_outputs: Vec<String>,
    state_updates: Vec<VmStateUpdate>,
    exit_guards: Vec<VmGuardedExit>,
    memory_read_effects: Vec<VmMemoryCondition>,
    memory_write_effects: Vec<VmMemoryCondition>,
    memory_reads: usize,
    memory_writes: usize,
    calls: usize,
    conditional_branches: usize,
    exit_targets: Vec<u64>,
    reenters_dispatch: bool,
    may_return: bool,
    truncated: bool,
    residual_guards: bool,
    residual_memory_effects: bool,
}

#[derive(Debug, Default)]
struct HandlerGraph {
    blocks: BTreeSet<u64>,
    internal_edges: BTreeMap<u64, BTreeSet<u64>>,
    exit_targets: BTreeSet<u64>,
    reenters_dispatch: bool,
    may_return: bool,
}

#[derive(Debug, Clone)]
struct HandlerScc {
    blocks: Vec<u64>,
}

#[derive(Debug, Default)]
struct HandlerSccSummary {
    blocks: BTreeSet<u64>,
    state_inputs: BTreeSet<String>,
    exit_guards: Vec<VmGuardedExit>,
    memory_read_effects: Vec<VmMemoryCondition>,
    memory_write_effects: Vec<VmMemoryCondition>,
    memory_reads: usize,
    memory_writes: usize,
    calls: usize,
    conditional_branches: usize,
    residual_guards: bool,
    residual_memory_effects: bool,
}

fn record_block_state(
    block: &r2ssa::function::SSABlock,
    state_inputs: &mut BTreeSet<String>,
    state_outputs: &mut BTreeSet<String>,
) {
    record_block_state_inputs(block, state_inputs);
    for phi in &block.phis {
        if is_vm_state_output_var(&phi.dst) {
            state_outputs.insert(phi.dst.display_name());
        }
    }
    for op in &block.ops {
        let Some(dst) = op.dst() else {
            continue;
        };
        if !is_vm_state_output_var(dst) {
            continue;
        }
        state_outputs.insert(dst.display_name());
    }
}

fn record_block_state_inputs(
    block: &r2ssa::function::SSABlock,
    state_inputs: &mut BTreeSet<String>,
) {
    block.for_each_source(|src| {
        if is_vm_state_input_var(src.var) {
            state_inputs.insert(src.var.display_name());
        }
    });
}

fn is_vm_state_input_var(var: &SSAVar) -> bool {
    (var.is_register() || var.is_memory()) && var.version == 0
}

fn is_vm_state_output_var(var: &SSAVar) -> bool {
    !var.is_const() && !var.is_temp() && !var.is_memory()
}

fn case_values_by_target(
    func: &SsaArtifact,
    dispatch_header: u64,
) -> (BTreeMap<u64, Vec<u64>>, Option<u64>) {
    let (cases, default_target) =
        if let Some((cases, default_target)) = func.function().switch_info(dispatch_header) {
            (cases, default_target)
        } else if let Some(ladder) = conditional_dispatch_ladder(func, dispatch_header) {
            return (ladder.case_values_by_target, Some(ladder.default_target));
        } else {
            return (BTreeMap::new(), None);
        };
    let mut case_values_by_target = BTreeMap::<u64, Vec<u64>>::new();
    for (value, target) in cases {
        case_values_by_target.entry(target).or_default().push(value);
    }
    for values in case_values_by_target.values_mut() {
        values.sort_unstable();
        values.dedup();
    }
    (case_values_by_target, default_target)
}

fn display_const(name: &str) -> Option<String> {
    let hex = name.strip_prefix("const:")?;
    let digits = hex.strip_prefix("0x").unwrap_or(hex);
    let value = u64::from_str_radix(digits, 16).ok()?;
    Some(format!("0x{value:x}"))
}

fn split_version(name: &str) -> (&str, Option<&str>) {
    name.rsplit_once('_')
        .filter(|(_, version)| version.chars().all(|ch| ch.is_ascii_digit()))
        .map_or((name, None), |(base, version)| (base, Some(version)))
}

fn same_logical_name(left: &str, right: &str) -> bool {
    split_version(left)
        .0
        .eq_ignore_ascii_case(split_version(right).0)
}

fn render_vm_var_expr(func: &SsaArtifact, var: &SSAVar, depth: u32) -> String {
    if depth > 4 {
        return var.display_name();
    }
    if var.is_const() {
        return display_const(&var.name).unwrap_or_else(|| var.display_name());
    }
    let Some(value_id) = func.graph().value_id_for_var(var) else {
        return var.display_name();
    };
    let Some(inst_id) = func.graph().def_inst(value_id) else {
        return var.display_name();
    };
    let Some(inst) = func.graph().inst(inst_id) else {
        return var.display_name();
    };
    let r2ssa::graph::InstPayload::Op(op) = &inst.payload else {
        return var.display_name();
    };
    render_vm_op_expr(func, op, depth + 1).unwrap_or_else(|| var.display_name())
}

fn classify_vm_var_value(func: &SsaArtifact, var: &SSAVar, depth: u32) -> VmValueExpr {
    if depth > 4 {
        return VmValueExpr::Var(var.display_name());
    }
    if var.is_const() {
        return display_const(&var.name)
            .and_then(|_| {
                let hex = var.name.strip_prefix("const:")?;
                let digits = hex.strip_prefix("0x").unwrap_or(hex);
                u64::from_str_radix(digits, 16).ok()
            })
            .map(VmValueExpr::Const)
            .unwrap_or_else(|| VmValueExpr::Expr(var.display_name()));
    }
    let Some(value_id) = func.graph().value_id_for_var(var) else {
        return VmValueExpr::Var(var.display_name());
    };
    let Some(inst_id) = func.graph().def_inst(value_id) else {
        return VmValueExpr::Var(var.display_name());
    };
    let Some(inst) = func.graph().inst(inst_id) else {
        return VmValueExpr::Var(var.display_name());
    };
    let r2ssa::graph::InstPayload::Op(op) = &inst.payload else {
        return VmValueExpr::Var(var.display_name());
    };
    if let Some((block_addr, op_idx)) = func.inst_op_site(inst_id)
        && let Some(value) = classify_vm_op_value_at_site(func, block_addr, op_idx, op, depth + 1)
    {
        return value;
    }
    classify_vm_op_value(func, op, depth + 1)
        .unwrap_or_else(|| VmValueExpr::Var(var.display_name()))
}

fn render_vm_binary_expr(
    func: &SsaArtifact,
    a: &SSAVar,
    op: &str,
    b: &SSAVar,
    depth: u32,
) -> String {
    format!(
        "({} {} {})",
        render_vm_var_expr(func, a, depth + 1),
        op,
        render_vm_var_expr(func, b, depth + 1)
    )
}

fn render_vm_op_expr(func: &SsaArtifact, op: &SSAOp, depth: u32) -> Option<String> {
    use SSAOp::*;

    Some(match op {
        Copy { src, .. } | IntZExt { src, .. } | IntSExt { src, .. } | Cast { src, .. } => {
            render_vm_var_expr(func, src, depth + 1)
        }
        Load { addr, .. } => format!("*{}", render_vm_var_expr(func, addr, depth + 1)),
        IntAdd { a, b, .. } | FloatAdd { a, b, .. } => {
            render_vm_binary_expr(func, a, "+", b, depth + 1)
        }
        IntSub { a, b, .. } | FloatSub { a, b, .. } => {
            render_vm_binary_expr(func, a, "-", b, depth + 1)
        }
        IntMult { a, b, .. } | FloatMult { a, b, .. } => {
            render_vm_binary_expr(func, a, "*", b, depth + 1)
        }
        IntDiv { a, b, .. } | IntSDiv { a, b, .. } | FloatDiv { a, b, .. } => {
            render_vm_binary_expr(func, a, "/", b, depth + 1)
        }
        IntRem { a, b, .. } | IntSRem { a, b, .. } => {
            render_vm_binary_expr(func, a, "%", b, depth + 1)
        }
        IntAnd { a, b, .. } => render_vm_binary_expr(func, a, "&", b, depth + 1),
        IntOr { a, b, .. } => render_vm_binary_expr(func, a, "|", b, depth + 1),
        IntXor { a, b, .. } | BoolXor { a, b, .. } => {
            render_vm_binary_expr(func, a, "^", b, depth + 1)
        }
        IntLeft { a, b, .. } => render_vm_binary_expr(func, a, "<<", b, depth + 1),
        IntRight { a, b, .. } | IntSRight { a, b, .. } => {
            render_vm_binary_expr(func, a, ">>", b, depth + 1)
        }
        IntEqual { a, b, .. } | FloatEqual { a, b, .. } => {
            render_vm_binary_expr(func, a, "==", b, depth + 1)
        }
        IntNotEqual { a, b, .. } | FloatNotEqual { a, b, .. } => {
            render_vm_binary_expr(func, a, "!=", b, depth + 1)
        }
        IntLess { a, b, .. } | IntSLess { a, b, .. } | FloatLess { a, b, .. } => {
            render_vm_binary_expr(func, a, "<", b, depth + 1)
        }
        IntLessEqual { a, b, .. } | IntSLessEqual { a, b, .. } | FloatLessEqual { a, b, .. } => {
            render_vm_binary_expr(func, a, "<=", b, depth + 1)
        }
        BoolAnd { a, b, .. } => render_vm_binary_expr(func, a, "&&", b, depth + 1),
        BoolOr { a, b, .. } => render_vm_binary_expr(func, a, "||", b, depth + 1),
        IntNegate { src, .. } | FloatNeg { src, .. } => {
            format!("(-{})", render_vm_var_expr(func, src, depth + 1))
        }
        IntNot { src, .. } => format!("(~{})", render_vm_var_expr(func, src, depth + 1)),
        BoolNot { src, .. } => format!("(!{})", render_vm_var_expr(func, src, depth + 1)),
        PtrAdd {
            base,
            index,
            element_size,
            ..
        } => format!(
            "({} + ({} * {}))",
            render_vm_var_expr(func, base, depth + 1),
            render_vm_var_expr(func, index, depth + 1),
            element_size
        ),
        PtrSub {
            base,
            index,
            element_size,
            ..
        } => format!(
            "({} - ({} * {}))",
            render_vm_var_expr(func, base, depth + 1),
            render_vm_var_expr(func, index, depth + 1),
            element_size
        ),
        Piece { hi, lo, .. } => format!(
            "piece({}, {})",
            render_vm_var_expr(func, hi, depth + 1),
            render_vm_var_expr(func, lo, depth + 1)
        ),
        Subpiece { src, offset, .. } => format!(
            "subpiece({}, {})",
            render_vm_var_expr(func, src, depth + 1),
            offset
        ),
        Select {
            cond,
            if_true,
            if_false,
            ..
        } => format!(
            "({} ? {} : {})",
            render_vm_var_expr(func, cond, depth + 1),
            render_vm_var_expr(func, if_true, depth + 1),
            render_vm_var_expr(func, if_false, depth + 1)
        ),
        _ => return None,
    })
}

fn classify_vm_op_value(func: &SsaArtifact, op: &SSAOp, depth: u32) -> Option<VmValueExpr> {
    use SSAOp::*;

    Some(match op {
        Copy { src, .. } | IntZExt { src, .. } | IntSExt { src, .. } | Cast { src, .. } => {
            classify_vm_var_value(func, src, depth + 1)
        }
        IntAdd { a, b, .. } | FloatAdd { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Add,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntSub { a, b, .. } | FloatSub { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Sub,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntMult { a, b, .. } | FloatMult { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Mul,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntDiv { a, b, .. } | IntSDiv { a, b, .. } | FloatDiv { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Div,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntRem { a, b, .. } | IntSRem { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Rem,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntAnd { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::And,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntOr { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Or,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntXor { a, b, .. } | BoolXor { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Xor,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntLeft { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Shl,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntRight { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::LShr,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntSRight { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::AShr,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntEqual { a, b, .. } | FloatEqual { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Eq,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntNotEqual { a, b, .. } | FloatNotEqual { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Ne,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntLess { a, b, .. } | FloatLess { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Lt,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntSLess { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::SLt,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntLessEqual { a, b, .. } | FloatLessEqual { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::Le,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntSLessEqual { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::SLe,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        BoolAnd { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::BoolAnd,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        BoolOr { a, b, .. } => VmValueExpr::Binary {
            op: VmBinaryOp::BoolOr,
            lhs: Box::new(classify_vm_var_value(func, a, depth + 1)),
            rhs: Box::new(classify_vm_var_value(func, b, depth + 1)),
        },
        IntNegate { src, .. } | FloatNeg { src, .. } => VmValueExpr::Unary {
            op: VmUnaryOp::Neg,
            arg: Box::new(classify_vm_var_value(func, src, depth + 1)),
        },
        IntNot { src, .. } => VmValueExpr::Unary {
            op: VmUnaryOp::BitNot,
            arg: Box::new(classify_vm_var_value(func, src, depth + 1)),
        },
        BoolNot { src, .. } => VmValueExpr::Unary {
            op: VmUnaryOp::BoolNot,
            arg: Box::new(classify_vm_var_value(func, src, depth + 1)),
        },
        Select {
            cond,
            if_true,
            if_false,
            ..
        } => VmValueExpr::Select {
            cond: Box::new(classify_vm_var_value(func, cond, depth + 1)),
            if_true: Box::new(classify_vm_var_value(func, if_true, depth + 1)),
            if_false: Box::new(classify_vm_var_value(func, if_false, depth + 1)),
        },
        _ => VmValueExpr::Expr(render_vm_op_expr(func, op, depth + 1)?),
    })
}

fn classify_vm_value_id(func: &SsaArtifact, value_id: r2ssa::ValueId, depth: u32) -> VmValueExpr {
    if let Some(var) = func.value_var(value_id) {
        return classify_vm_var_value(func, var, depth);
    }
    VmValueExpr::Expr(format!("value:{value_id:?}"))
}

fn stack_base_name(base: StackAddressBase) -> &'static str {
    match base {
        StackAddressBase::FramePointer => "fp",
        StackAddressBase::StackPointer => "sp",
    }
}

fn vm_memory_binding_name(
    region: &VmMemoryRegionRef,
    address: &SemanticMemoryAddress,
    size: u32,
) -> String {
    if address.terms().is_empty() {
        return format!("mem:r{}:{}:{size}", region.id, address.offset_lo());
    }
    let terms = address
        .terms()
        .iter()
        .map(|term| format!("v{}_c{}", term.value.0, term.coefficient))
        .collect::<Vec<_>>()
        .join("_");
    format!(
        "mem:r{}:affine_{terms}_offset_{}:{size}",
        region.id,
        address.offset_lo()
    )
}

fn vm_memory_region_ref_from_object(
    func: &SsaArtifact,
    object_id: r2ssa::ObjectId,
) -> Option<VmMemoryRegionRef> {
    let object = func.objects().object(object_id)?;
    let (kind, name) = match &object.kind {
        ObjectKind::StackSlot { base, offset, .. }
        | ObjectKind::FrameObject { base, offset, .. } => (
            MemoryRegionKind::Stack,
            format!("stack:{}{:+#x}", stack_base_name(*base), offset),
        ),
        ObjectKind::Global { space, address } => {
            (MemoryRegionKind::Global, format!("{space}:0x{address:x}"))
        }
        ObjectKind::Parameter { index, .. } => (MemoryRegionKind::Input, format!("arg{index}")),
        ObjectKind::HeapAlloc { call_site, .. } => (
            MemoryRegionKind::Heap,
            format!("heap_alloc@{}", call_site.0),
        ),
        ObjectKind::EscapedUnknown { .. } => return None,
        ObjectKind::Pointee { .. } => (
            MemoryRegionKind::Input,
            func.objects().access_path(object_id)?,
        ),
    };
    Some(VmMemoryRegionRef {
        id: object_id.0,
        kind,
        name,
    })
}

fn render_memory_access_expr(op: &SSAOp, func: &SsaArtifact) -> String {
    match op {
        SSAOp::Load { addr, .. }
        | SSAOp::Store { addr, .. }
        | SSAOp::LoadLinked { addr, .. }
        | SSAOp::StoreConditional { addr, .. }
        | SSAOp::AtomicCAS { addr, .. }
        | SSAOp::LoadGuarded { addr, .. }
        | SSAOp::StoreGuarded { addr, .. } => render_vm_var_expr(func, addr, 0),
        _ => "<mem>".to_string(),
    }
}

fn vm_memory_write_value(op: &SSAOp, func: &SsaArtifact) -> (Option<VmValueExpr>, bool) {
    match op {
        SSAOp::Store { val, .. } => {
            let value = classify_vm_var_value(func, val, 0);
            let exact = value.is_exact();
            (Some(value), exact)
        }
        _ => (None, false),
    }
}

fn classify_vm_op_value_at_site(
    func: &SsaArtifact,
    block_addr: u64,
    op_idx: usize,
    op: &SSAOp,
    depth: u32,
) -> Option<VmValueExpr> {
    match op {
        SSAOp::Load { .. } | SSAOp::LoadLinked { .. } => {
            let (reads, _writes, residual) =
                vm_memory_conditions_for_op(func, block_addr, op_idx, op);
            if !residual
                && let [read] = reads.as_slice()
                && let Some(binding) = read.binding.as_ref()
            {
                return Some(VmValueExpr::Var(binding.clone()));
            }
            classify_vm_op_value(func, op, depth)
        }
        _ => classify_vm_op_value(func, op, depth),
    }
}

fn vm_memory_conditions_for_op(
    func: &SsaArtifact,
    block_addr: u64,
    op_idx: usize,
    op: &SSAOp,
) -> (Vec<VmMemoryCondition>, Vec<VmMemoryCondition>, bool) {
    let expr = render_memory_access_expr(op, func);
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    let mut residual = false;

    if op.is_memory_read() {
        let Some(uses) = func.memory_uses_for_op_site(block_addr, op_idx) else {
            residual = true;
            return (reads, writes, residual);
        };
        let locations = uses
            .iter()
            .map(|use_fact| &use_fact.location)
            .collect::<BTreeSet<_>>();
        for location in locations {
            let Some(region) = vm_memory_region_ref_from_object(func, location.object) else {
                residual = true;
                continue;
            };
            let Some(address) = SemanticMemoryAddress::from_ssa(&location.address) else {
                residual = true;
                continue;
            };
            let binding = Some(vm_memory_binding_name(&region, &address, location.size));
            reads.push(VmMemoryCondition {
                region,
                address,
                size: location.size,
                binding,
                expr: expr.clone(),
                value_expr: None,
                value: None,
                exact_value: false,
            });
        }
    }

    if op.is_memory_write() {
        let Some(defs) = func.memory_defs_for_op_site(block_addr, op_idx) else {
            residual = true;
            return (reads, writes, residual);
        };
        let (write_value, exact_value) = vm_memory_write_value(op, func);
        if matches!(
            op,
            SSAOp::StoreConditional { .. } | SSAOp::StoreGuarded { .. } | SSAOp::AtomicCAS { .. }
        ) {
            residual = true;
        }
        let locations = defs
            .iter()
            .map(|def| &def.location)
            .collect::<BTreeSet<_>>();
        for location in locations {
            let Some(region) = vm_memory_region_ref_from_object(func, location.object) else {
                residual = true;
                continue;
            };
            let Some(address) = SemanticMemoryAddress::from_ssa(&location.address) else {
                residual = true;
                continue;
            };
            let binding = Some(vm_memory_binding_name(&region, &address, location.size));
            writes.push(VmMemoryCondition {
                region,
                address,
                size: location.size,
                binding,
                expr: expr.clone(),
                value_expr: write_value.as_ref().map(VmValueExpr::render),
                value: write_value.clone(),
                exact_value,
            });
        }
    }

    reads.sort_by(|lhs, rhs| {
        (
            lhs.region.id,
            &lhs.region.name,
            &lhs.address,
            lhs.size,
            lhs.binding.as_deref(),
            &lhs.expr,
        )
            .cmp(&(
                rhs.region.id,
                &rhs.region.name,
                &rhs.address,
                rhs.size,
                rhs.binding.as_deref(),
                &rhs.expr,
            ))
    });
    reads.dedup();
    writes.sort_by(|lhs, rhs| {
        (
            lhs.region.id,
            &lhs.region.name,
            &lhs.address,
            lhs.size,
            lhs.binding.as_deref(),
            &lhs.expr,
            lhs.value_expr.as_deref(),
            lhs.exact_value,
        )
            .cmp(&(
                rhs.region.id,
                &rhs.region.name,
                &rhs.address,
                rhs.size,
                rhs.binding.as_deref(),
                &rhs.expr,
                rhs.value_expr.as_deref(),
                rhs.exact_value,
            ))
    });
    writes.dedup();

    (reads, writes, residual)
}

fn vm_exit_guards_for_block(
    func: &SsaArtifact,
    block_addr: u64,
    seen_targets: &mut BTreeSet<(u64, bool, String)>,
) -> (Vec<VmGuardedExit>, bool) {
    let Some(predicate) = func
        .predicates()
        .predicates
        .values()
        .find(|fact| fact.block_addr == block_addr)
    else {
        return (Vec::new(), true);
    };
    let value = classify_vm_value_id(func, predicate.condition, 0);
    let base_expr = value.render();
    let exact = value.is_exact();
    let true_expr = base_expr.clone();
    let false_expr = format!("!({base_expr})");
    let mut guards = Vec::new();
    for (target, expect_nonzero, expr) in [
        (predicate.true_target, true, true_expr),
        (predicate.false_target, false, false_expr),
    ] {
        if seen_targets.insert((target, expect_nonzero, expr.clone())) {
            guards.push(VmGuardedExit {
                target,
                guard: VmGuardCondition {
                    expr,
                    value: value.clone(),
                    expect_nonzero,
                    exact,
                },
            });
        }
    }
    (guards, false)
}

fn build_handler_graph(
    func: &SsaArtifact,
    entry: u64,
    dispatch_header: u64,
    loop_header: u64,
    dispatch_targets: &BTreeSet<u64>,
) -> HandlerGraph {
    let mut graph = HandlerGraph::default();
    let mut queue = VecDeque::from([entry]);

    while let Some(block_addr) = queue.pop_front() {
        if !graph.blocks.insert(block_addr) {
            continue;
        }

        let Some(cfg_block) = func.cfg().get_block(block_addr) else {
            continue;
        };
        if matches!(cfg_block.terminator, BlockTerminator::Return) {
            graph.may_return = true;
        }

        for succ in func.successors(block_addr) {
            if succ == dispatch_header || succ == loop_header {
                graph.reenters_dispatch = true;
                graph.exit_targets.insert(succ);
                continue;
            }
            if dispatch_targets.contains(&succ) && succ != entry {
                graph.exit_targets.insert(succ);
                continue;
            }
            graph
                .internal_edges
                .entry(block_addr)
                .or_default()
                .insert(succ);
            if !graph.blocks.contains(&succ) {
                queue.push_back(succ);
            }
        }
    }

    for block in &graph.blocks {
        graph.internal_edges.entry(*block).or_default();
    }
    graph
}

fn handler_graph_sccs(graph: &HandlerGraph) -> Vec<HandlerScc> {
    struct Tarjan<'a> {
        graph: &'a HandlerGraph,
        next_index: usize,
        stack: Vec<u64>,
        on_stack: BTreeSet<u64>,
        index_by_block: BTreeMap<u64, usize>,
        lowlink_by_block: BTreeMap<u64, usize>,
        sccs: Vec<HandlerScc>,
    }

    impl<'a> Tarjan<'a> {
        fn strongconnect(&mut self, block: u64) {
            let index = self.next_index;
            self.next_index += 1;
            self.index_by_block.insert(block, index);
            self.lowlink_by_block.insert(block, index);
            self.stack.push(block);
            self.on_stack.insert(block);

            for succ in self
                .graph
                .internal_edges
                .get(&block)
                .into_iter()
                .flat_map(|succs| succs.iter().copied())
                .filter(|succ| self.graph.blocks.contains(succ))
            {
                if !self.index_by_block.contains_key(&succ) {
                    self.strongconnect(succ);
                    let succ_lowlink = self.lowlink_by_block[&succ];
                    let block_lowlink = self.lowlink_by_block[&block].min(succ_lowlink);
                    self.lowlink_by_block.insert(block, block_lowlink);
                } else if self.on_stack.contains(&succ) {
                    let succ_index = self.index_by_block[&succ];
                    let block_lowlink = self.lowlink_by_block[&block].min(succ_index);
                    self.lowlink_by_block.insert(block, block_lowlink);
                }
            }

            if self.lowlink_by_block[&block] == self.index_by_block[&block] {
                let mut blocks = Vec::new();
                while let Some(member) = self.stack.pop() {
                    self.on_stack.remove(&member);
                    blocks.push(member);
                    if member == block {
                        break;
                    }
                }
                blocks.sort_unstable();
                self.sccs.push(HandlerScc { blocks });
            }
        }
    }

    let mut tarjan = Tarjan {
        graph,
        next_index: 0,
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        index_by_block: BTreeMap::new(),
        lowlink_by_block: BTreeMap::new(),
        sccs: Vec::new(),
    };
    for block in &graph.blocks {
        if !tarjan.index_by_block.contains_key(block) {
            tarjan.strongconnect(*block);
        }
    }
    tarjan.sccs.sort_by_key(|scc| {
        (
            scc.blocks.first().copied().unwrap_or(u64::MAX),
            scc.blocks.len(),
        )
    });
    tarjan.sccs
}

fn join_vm_state_update_value(output: &str, left: &mut VmValueExpr, right: VmValueExpr) {
    if *left != right {
        *left = VmValueExpr::Expr(format!("summary({output})"));
    }
}

fn insert_vm_state_update(
    updates: &mut BTreeMap<String, VmValueExpr>,
    output: String,
    value: VmValueExpr,
) {
    if let Some(existing_output) = updates
        .keys()
        .find(|candidate| same_logical_name(candidate, &output))
        .cloned()
    {
        let existing = updates
            .get_mut(&existing_output)
            .expect("state update key was selected from the same map");
        join_vm_state_update_value(&existing_output, existing, value);
    } else {
        updates.insert(output, value);
    }
}

fn value_crosses_handler_boundary(
    func: &SsaArtifact,
    blocks: &BTreeSet<u64>,
    value: &SSAVar,
) -> bool {
    let Some(value_id) = func.graph().value_id_for_var(value) else {
        return false;
    };
    func.graph().use_sites(value_id).iter().any(|site| {
        func.graph()
            .inst(site.inst)
            .and_then(|inst| func.graph().block(inst.block))
            .is_some_and(|block| !blocks.contains(&block.addr))
    })
}

fn handler_boundary_state_updates(
    func: &SsaArtifact,
    blocks: &BTreeSet<u64>,
) -> BTreeMap<String, VmValueExpr> {
    let mut updates = BTreeMap::new();
    for block_addr in blocks {
        let Some(block) = func.get_block(*block_addr) else {
            continue;
        };
        for phi in &block.phis {
            if is_vm_state_output_var(&phi.dst)
                && value_crosses_handler_boundary(func, blocks, &phi.dst)
            {
                insert_vm_state_update(
                    &mut updates,
                    phi.dst.display_name(),
                    classify_vm_var_value(func, &phi.dst, 0),
                );
            }
        }
        for (op_idx, op) in block.ops.iter().enumerate() {
            let Some(dst) = op.dst() else {
                continue;
            };
            if !is_vm_state_output_var(dst) || !value_crosses_handler_boundary(func, blocks, dst) {
                continue;
            }
            let value = classify_vm_op_value_at_site(func, *block_addr, op_idx, op, 0)
                .unwrap_or_else(|| VmValueExpr::Var(dst.display_name()));
            insert_vm_state_update(&mut updates, dst.display_name(), value);
        }
    }
    updates
}

fn sort_vm_guarded_exits(guards: &mut Vec<VmGuardedExit>) {
    guards.sort_by(|lhs, rhs| {
        (lhs.target, &lhs.guard.expr, lhs.guard.expect_nonzero).cmp(&(
            rhs.target,
            &rhs.guard.expr,
            rhs.guard.expect_nonzero,
        ))
    });
    guards.dedup();
}

fn sort_vm_memory_conditions(conditions: &mut Vec<VmMemoryCondition>) {
    conditions.sort_by(|lhs, rhs| {
        (
            lhs.region.id,
            &lhs.region.name,
            &lhs.address,
            lhs.size,
            lhs.binding.as_deref(),
            &lhs.expr,
            lhs.value_expr.as_deref(),
            lhs.exact_value,
        )
            .cmp(&(
                rhs.region.id,
                &rhs.region.name,
                &rhs.address,
                rhs.size,
                rhs.binding.as_deref(),
                &rhs.expr,
                rhs.value_expr.as_deref(),
                rhs.exact_value,
            ))
    });
    conditions.dedup();
}

fn summarize_handler_scc(
    func: &SsaArtifact,
    scc: &HandlerScc,
    seen_exit_guards: &mut BTreeSet<(u64, bool, String)>,
) -> HandlerSccSummary {
    let mut summary = HandlerSccSummary::default();

    for block_addr in &scc.blocks {
        summary.blocks.insert(*block_addr);
        let Some(block) = func.get_block(*block_addr) else {
            continue;
        };
        let cfg_block = func.cfg().get_block(*block_addr);
        if matches!(
            cfg_block.map(|block| &block.terminator),
            Some(BlockTerminator::ConditionalBranch { .. })
        ) {
            summary.conditional_branches += 1;
            let (block_guards, residual) =
                vm_exit_guards_for_block(func, *block_addr, seen_exit_guards);
            if block_guards.is_empty() {
                summary.residual_guards |= residual;
            } else {
                summary.exit_guards.extend(block_guards);
            }
        }

        record_block_state_inputs(block, &mut summary.state_inputs);
        for (op_idx, op) in block.ops.iter().enumerate() {
            if op.is_memory_read() {
                summary.memory_reads += 1;
            }
            if op.is_memory_write() {
                summary.memory_writes += 1;
            }
            let (reads, writes, residual) =
                vm_memory_conditions_for_op(func, *block_addr, op_idx, op);
            summary.residual_memory_effects |= residual;
            summary.memory_read_effects.extend(reads);
            summary.memory_write_effects.extend(writes);
            if matches!(
                op,
                SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::CallOther { .. }
            ) {
                summary.calls += 1;
            }
        }
    }

    sort_vm_guarded_exits(&mut summary.exit_guards);
    sort_vm_memory_conditions(&mut summary.memory_read_effects);
    sort_vm_memory_conditions(&mut summary.memory_write_effects);
    summary
}

fn join_handler_scc_summary(acc: &mut HandlerSccSummary, summary: HandlerSccSummary) {
    acc.blocks.extend(summary.blocks);
    acc.state_inputs.extend(summary.state_inputs);
    acc.exit_guards.extend(summary.exit_guards);
    sort_vm_guarded_exits(&mut acc.exit_guards);
    acc.memory_read_effects.extend(summary.memory_read_effects);
    sort_vm_memory_conditions(&mut acc.memory_read_effects);
    acc.memory_write_effects
        .extend(summary.memory_write_effects);
    sort_vm_memory_conditions(&mut acc.memory_write_effects);
    acc.memory_reads += summary.memory_reads;
    acc.memory_writes += summary.memory_writes;
    acc.calls += summary.calls;
    acc.conditional_branches += summary.conditional_branches;
    acc.residual_guards |= summary.residual_guards;
    acc.residual_memory_effects |= summary.residual_memory_effects;
}

fn summarize_handler_region(
    func: &SsaArtifact,
    entry: u64,
    dispatch_header: u64,
    loop_header: u64,
    dispatch_targets: &BTreeSet<u64>,
) -> HandlerRegionSummary {
    let graph = build_handler_graph(func, entry, dispatch_header, loop_header, dispatch_targets);
    let sccs = handler_graph_sccs(&graph);
    let mut seen_exit_guards = BTreeSet::new();
    let mut joined = HandlerSccSummary::default();
    for scc in &sccs {
        let summary = summarize_handler_scc(func, scc, &mut seen_exit_guards);
        join_handler_scc_summary(&mut joined, summary);
    }
    let state_updates = handler_boundary_state_updates(func, &graph.blocks);
    let state_outputs = state_updates.keys().cloned().collect();

    HandlerRegionSummary {
        blocks: joined.blocks.into_iter().collect(),
        state_inputs: joined.state_inputs.into_iter().collect(),
        state_outputs,
        state_updates: state_updates
            .into_iter()
            .map(|(output, value)| VmStateUpdate {
                output,
                expr: value.render(),
                exact: value.is_exact(),
                value,
            })
            .collect(),
        exit_guards: joined.exit_guards,
        memory_read_effects: joined.memory_read_effects,
        memory_write_effects: joined.memory_write_effects,
        memory_reads: joined.memory_reads,
        memory_writes: joined.memory_writes,
        calls: joined.calls,
        conditional_branches: joined.conditional_branches,
        exit_targets: graph.exit_targets.into_iter().collect(),
        reenters_dispatch: graph.reenters_dispatch,
        may_return: graph.may_return,
        truncated: false,
        residual_guards: joined.residual_guards,
        residual_memory_effects: joined.residual_memory_effects,
    }
}

fn direct_loop_latches(func: &SsaArtifact, header: u64) -> Vec<u64> {
    func.predecessors(header)
        .into_iter()
        .filter(|pred| matches!(func.edge_type(*pred, header), Some(CFGEdge::Back)))
        .collect()
}

fn can_reach_within(
    func: &SsaArtifact,
    from: u64,
    target: u64,
    max_depth: usize,
    visited: &mut BTreeSet<u64>,
) -> bool {
    if from == target {
        return true;
    }
    if max_depth == 0 || !visited.insert(from) {
        return false;
    }
    func.successors(from)
        .into_iter()
        .any(|succ| can_reach_within(func, succ, target, max_depth - 1, visited))
}

fn enclosing_loop_header(func: &SsaArtifact, dispatch_header: u64) -> Option<(u64, Vec<u64>)> {
    let mut visited = BTreeSet::new();
    let mut frontier = func.predecessors(dispatch_header);
    let mut depth = 0usize;
    let dispatch_targets = func.successors(dispatch_header);

    while !frontier.is_empty() && depth < 8 {
        let mut next = Vec::new();
        for candidate in frontier {
            if !visited.insert(candidate) {
                continue;
            }
            let latches = direct_loop_latches(func, candidate);
            if !latches.is_empty() && func.dominates(candidate, dispatch_header) {
                return Some((candidate, latches));
            }
            if func.dominates(candidate, dispatch_header) {
                let returning_targets = dispatch_targets
                    .iter()
                    .copied()
                    .filter(|target| {
                        can_reach_within(func, *target, candidate, 4, &mut BTreeSet::new())
                    })
                    .collect::<Vec<_>>();
                if !returning_targets.is_empty() {
                    return Some((candidate, returning_targets));
                }
            }
            next.extend(func.predecessors(candidate));
        }
        frontier = next;
        depth += 1;
    }

    None
}

fn skip_dispatch_passthrough_blocks(func: &SsaArtifact, mut addr: u64) -> u64 {
    let mut visited = BTreeSet::new();
    for _ in 0..3 {
        if !visited.insert(addr) {
            break;
        }
        let Some(block) = func.cfg().get_block(addr) else {
            break;
        };
        if block.ops.len() > 1 {
            break;
        }
        let next = match block.terminator {
            BlockTerminator::Branch { target } | BlockTerminator::Fallthrough { next: target } => {
                target
            }
            _ => break,
        };
        addr = next;
    }
    addr
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ConditionalDispatchLadder {
    handlers: Vec<u64>,
    default_target: u64,
    selector: ValueId,
    case_values_by_target: BTreeMap<u64, Vec<u64>>,
}

fn conditional_dispatch_ladder(
    func: &SsaArtifact,
    dispatch_header: u64,
) -> Option<ConditionalDispatchLadder> {
    let (loop_header, _) = enclosing_loop_header(func, dispatch_header)?;
    let mut current = dispatch_header;
    let mut visited = BTreeSet::new();
    let mut handlers = Vec::new();
    let mut selector = None;
    let mut case_values_by_target = BTreeMap::<u64, Vec<u64>>::new();
    let mut seen_case_values = BTreeSet::new();

    for _ in 0..32 {
        if !visited.insert(current) {
            return None;
        }
        let block = func.cfg().get_block(current)?;
        let BlockTerminator::ConditionalBranch {
            true_target,
            false_target,
        } = block.terminator
        else {
            return None;
        };
        let predicate = func
            .predicates()
            .predicates
            .values()
            .find(|predicate| predicate.block_addr == current)?;
        let comparison = predicate.comparison.as_ref()?;
        let (raw_selector, case_value) = comparison_selector_and_constant(func, comparison)?;
        let canonical_selector = canonical_vm_selector(func, raw_selector);
        if selector
            .replace(canonical_selector)
            .is_some_and(|existing| existing != canonical_selector)
        {
            return None;
        }
        if !seen_case_values.insert(case_value) {
            return None;
        }
        let (handler, next) = match comparison.kind {
            CompareKind::Equal => (true_target, false_target),
            CompareKind::NotEqual => (false_target, true_target),
            _ => return None,
        };
        handlers.push(handler);
        case_values_by_target
            .entry(handler)
            .or_default()
            .push(case_value);

        let continuation = skip_dispatch_passthrough_blocks(func, next);
        if func.cfg().get_block(continuation).is_some_and(|candidate| {
            matches!(
                candidate.terminator,
                BlockTerminator::ConditionalBranch { .. }
            )
        }) {
            current = continuation;
            continue;
        }

        let redispatching_handlers = handlers
            .iter()
            .filter(|handler| {
                can_reach_within(func, **handler, loop_header, 8, &mut BTreeSet::new())
            })
            .count();
        if handlers.len() < 4 || redispatching_handlers < 3 {
            return None;
        }
        let default_target = next;
        handlers.push(default_target);
        handlers.sort_unstable();
        handlers.dedup();
        for values in case_values_by_target.values_mut() {
            values.sort_unstable();
            values.dedup();
        }
        return Some(ConditionalDispatchLadder {
            handlers,
            default_target,
            selector: selector?,
            case_values_by_target,
        });
    }

    None
}

fn comparison_selector_and_constant(
    func: &SsaArtifact,
    comparison: &r2ssa::CompareProvenance,
) -> Option<(ValueId, u64)> {
    let lhs_const = graph_value_constant(func, comparison.lhs);
    let rhs_const = graph_value_constant(func, comparison.rhs);
    match (lhs_const, rhs_const) {
        (None, Some(value)) => Some((comparison.lhs, value)),
        (Some(value), None) => Some((comparison.rhs, value)),
        _ => None,
    }
}

fn graph_value_constant(func: &SsaArtifact, value: ValueId) -> Option<u64> {
    let var = &func.graph().value(value)?.var;
    var.is_const()
        .then(|| r2ssa::parse_const_value(&var.name))
        .flatten()
}

fn canonical_vm_selector(func: &SsaArtifact, value: ValueId) -> ValueId {
    let mut current = value;
    let mut visited = BTreeSet::new();
    while visited.insert(current) {
        if let Some(reload) = func.certificates().stack_reloads.get(&current) {
            current = reload.canonical_source;
            continue;
        }
        let Some(inst) = func
            .graph()
            .def_inst(current)
            .and_then(|id| func.graph().inst(id))
        else {
            break;
        };
        let InstPayload::Op(op) = &inst.payload else {
            break;
        };
        let follows_first_input = matches!(
            op,
            SSAOp::Copy { .. }
                | SSAOp::IntZExt { .. }
                | SSAOp::IntSExt { .. }
                | SSAOp::Trunc { .. }
                | SSAOp::Cast { .. }
                | SSAOp::Subpiece { offset: 0, .. }
        );
        if !follows_first_input {
            break;
        }
        let Some(input) = inst.inputs.first().copied() else {
            break;
        };
        current = input;
    }
    current
}

fn interpreter_dispatch_targets(
    func: &SsaArtifact,
    interpreter: &InterpreterDispatchSummary,
) -> (Vec<u64>, Option<u64>) {
    if let Some(ladder) = conditional_dispatch_ladder(func, interpreter.dispatch_header) {
        return (ladder.handlers, Some(ladder.default_target));
    }
    let (_, default_target) = case_values_by_target(func, interpreter.dispatch_header);
    (func.successors(interpreter.dispatch_header), default_target)
}

pub(crate) fn classify_interpreter_like(func: &SsaArtifact) -> Option<InterpreterDispatchSummary> {
    let summary = func.function().cfg_risk_summary();
    if summary.block_count < 6 || summary.loop_count == 0 {
        return None;
    }

    let direct_call_diversity = func
        .call_sites()
        .by_id
        .values()
        .filter_map(|call| call.direct_target)
        .collect::<std::collections::HashSet<_>>()
        .len();

    let mut best: Option<InterpreterDispatchSummary> = None;
    let mut best_score = i32::MIN;
    for block_addr in func.cfg().block_addrs() {
        let Some(block) = func.cfg().get_block(block_addr) else {
            continue;
        };
        let mut selector = func
            .function()
            .infer_switch_selector_var(block_addr)
            .map(|var| var.name);
        let direct_dispatch_targets = func.successors(block_addr);
        let ladder = conditional_dispatch_ladder(func, block_addr);
        if selector.is_none()
            && let Some(ladder) = &ladder
        {
            selector = func
                .graph()
                .value(ladder.selector)
                .map(|value| value.var.display_name());
        }
        let is_ladder = ladder.is_some();
        let (kind, dispatch_targets) = match block.terminator {
            BlockTerminator::Switch { .. } => {
                (InterpreterKind::SwitchDispatch, direct_dispatch_targets)
            }
            BlockTerminator::IndirectBranch => {
                (InterpreterKind::IndirectDispatch, direct_dispatch_targets)
            }
            _ if ladder.is_some() => (
                InterpreterKind::SwitchDispatch,
                ladder
                    .as_ref()
                    .map(|ladder| ladder.handlers.clone())
                    .unwrap_or_default(),
            ),
            _ if direct_dispatch_targets.len() >= 4 && selector.is_some() => {
                (InterpreterKind::SwitchDispatch, direct_dispatch_targets)
            }
            _ => continue,
        };

        let preds = func.predecessors(block_addr);
        let back_edges = preds
            .iter()
            .filter(|pred| matches!(func.edge_type(**pred, block_addr), Some(CFGEdge::Back)))
            .count();
        let dispatch_fanout = dispatch_targets.len();

        let mut score = 0i32;
        if back_edges > 0 {
            score += 2;
        }
        if selector.is_some() {
            score += 2;
        }
        if matches!(kind, InterpreterKind::SwitchDispatch) {
            score += 2;
        }
        if is_ladder {
            score += 2;
        }
        if dispatch_fanout >= 4 {
            score += 1;
        }
        let dominated_targets = dispatch_targets
            .iter()
            .filter(|target| func.dominates(block_addr, **target))
            .count();
        if dispatch_fanout > 0 && dominated_targets * 2 >= dispatch_fanout {
            score += 1;
        }
        if direct_call_diversity <= 2 {
            score += 1;
        }
        if direct_call_diversity > dispatch_fanout.max(4) {
            score -= 2;
        }

        let threshold = match kind {
            InterpreterKind::SwitchDispatch => 6,
            InterpreterKind::IndirectDispatch => 5,
        };
        let is_better_tie = best.as_ref().is_none_or(|current| {
            dispatch_fanout > current.dispatch_targets
                || (dispatch_fanout == current.dispatch_targets
                    && block_addr < current.dispatch_header)
        });
        if score < threshold || score < best_score || (score == best_score && !is_better_tie) {
            continue;
        }

        best_score = score;
        best = Some(InterpreterDispatchSummary {
            kind,
            dispatch_header: block_addr,
            dispatch_targets: dispatch_fanout,
            selector,
            back_edges,
            score,
        });
    }

    if best.is_some() {
        return best;
    }

    let mut fallback: Option<InterpreterDispatchSummary> = None;
    let mut fallback_score = i32::MIN;
    for block_addr in func.cfg().block_addrs() {
        let dispatch_targets = func.successors(block_addr);
        if dispatch_targets.len() < 4 {
            continue;
        }
        let selector = func
            .function()
            .infer_switch_selector_var(block_addr)
            .map(|var| var.name);
        let back_edges = func
            .predecessors(block_addr)
            .iter()
            .filter(|pred| matches!(func.edge_type(**pred, block_addr), Some(CFGEdge::Back)))
            .count();
        let score = (dispatch_targets.len() as i32) + if selector.is_some() { 2 } else { 0 };
        if score < fallback_score {
            continue;
        }
        fallback_score = score;
        fallback = Some(InterpreterDispatchSummary {
            kind: InterpreterKind::SwitchDispatch,
            dispatch_header: block_addr,
            dispatch_targets: dispatch_targets.len(),
            selector,
            back_edges,
            score,
        });
    }

    fallback
}

pub(crate) fn build_vm_step_summary(
    func: &SsaArtifact,
    interpreter: &InterpreterDispatchSummary,
) -> Option<VmStepSummary> {
    let (dispatch_targets, ladder_default_target) = interpreter_dispatch_targets(func, interpreter);
    if dispatch_targets.len() < 2 {
        return None;
    }
    let (loop_header, loop_latches) = {
        let direct = direct_loop_latches(func, interpreter.dispatch_header);
        if direct.is_empty() {
            enclosing_loop_header(func, interpreter.dispatch_header)
                .unwrap_or((interpreter.dispatch_header, Vec::new()))
        } else {
            (interpreter.dispatch_header, direct)
        }
    };
    if loop_latches.is_empty() {
        return None;
    }

    let dispatch_target_set = dispatch_targets.iter().copied().collect::<BTreeSet<_>>();
    let (case_values_by_target, switch_default_target) =
        case_values_by_target(func, interpreter.dispatch_header);
    let default_target = switch_default_target.or(ladder_default_target);
    let mut handler_regions = BTreeMap::new();
    let mut handler_state_inputs = BTreeMap::new();
    let mut handler_state_outputs = BTreeMap::new();
    let mut handler_state_updates = BTreeMap::new();
    let mut handler_exit_guards = BTreeMap::new();
    let mut handler_memory_read_effects = BTreeMap::new();
    let mut handler_memory_write_effects = BTreeMap::new();
    let mut handler_memory_reads = BTreeMap::new();
    let mut handler_memory_writes = BTreeMap::new();
    let mut handler_calls = BTreeMap::new();
    let mut handler_conditional_branches = BTreeMap::new();
    let mut handler_exit_targets = BTreeMap::new();
    let mut redispatch_handlers = Vec::new();
    let mut returning_handlers = Vec::new();
    let mut truncated_handlers = Vec::new();
    let mut transfers = Vec::new();
    let mut step_block_set = BTreeSet::from([loop_header, interpreter.dispatch_header]);

    for target in dispatch_targets.iter().copied() {
        let summary = summarize_handler_region(
            func,
            target,
            interpreter.dispatch_header,
            loop_header,
            &dispatch_target_set,
        );
        step_block_set.extend(summary.blocks.iter().copied());
        if summary.reenters_dispatch {
            redispatch_handlers.push(target);
        }
        if summary.may_return {
            returning_handlers.push(target);
        }
        if summary.truncated {
            truncated_handlers.push(target);
        }
        let case_values = case_values_by_target
            .get(&target)
            .cloned()
            .unwrap_or_default();
        let selector_update = interpreter.selector.as_ref().and_then(|selector| {
            summary
                .state_updates
                .iter()
                .find(|update| same_logical_name(&update.output, selector))
                .cloned()
        });
        let exact_memory_effects = summary
            .memory_read_effects
            .iter()
            .all(|effect| effect.address.has_exact_identity())
            && summary
                .memory_write_effects
                .iter()
                .all(|effect| effect.address.has_exact_identity() && effect.exact_value);
        let exact = !summary.truncated
            && summary.calls == 0
            && summary.conditional_branches == 0
            && summary.state_updates.iter().all(|update| update.exact)
            && selector_update.as_ref().is_none_or(|update| update.exact)
            && summary.exit_guards.iter().all(|guard| guard.guard.exact)
            && !summary.residual_guards
            && exact_memory_effects
            && !summary.residual_memory_effects;
        transfers.push(VmTransferArm {
            handler_target: target,
            case_values,
            region_blocks: summary.blocks.clone(),
            exit_targets: summary.exit_targets.clone(),
            exit_guards: summary.exit_guards.clone(),
            state_updates: summary.state_updates.clone(),
            selector_update,
            memory_reads: summary.memory_read_effects.clone(),
            memory_writes: summary.memory_write_effects.clone(),
            residual_guards: summary.residual_guards,
            residual_memory_effects: summary.residual_memory_effects,
            exact,
            redispatch: summary.reenters_dispatch,
            may_return: summary.may_return,
            truncated: summary.truncated,
        });
        handler_regions.insert(target, summary.blocks);
        handler_state_inputs.insert(target, summary.state_inputs);
        handler_state_outputs.insert(target, summary.state_outputs);
        handler_state_updates.insert(target, summary.state_updates);
        handler_exit_guards.insert(target, summary.exit_guards);
        handler_memory_read_effects.insert(target, summary.memory_read_effects);
        handler_memory_write_effects.insert(target, summary.memory_write_effects);
        handler_memory_reads.insert(target, summary.memory_reads);
        handler_memory_writes.insert(target, summary.memory_writes);
        handler_calls.insert(target, summary.calls);
        handler_conditional_branches.insert(target, summary.conditional_branches);
        handler_exit_targets.insert(target, summary.exit_targets);
    }

    let step_blocks = step_block_set.into_iter().collect::<Vec<_>>();
    let mut state_inputs = BTreeSet::new();
    let mut state_outputs = BTreeSet::new();
    for block_addr in step_blocks.iter().copied() {
        let Some(block) = func.get_block(block_addr) else {
            continue;
        };
        record_block_state(block, &mut state_inputs, &mut state_outputs);
    }

    if state_inputs.is_empty() || state_outputs.is_empty() {
        return None;
    }

    redispatch_handlers.sort_unstable();
    redispatch_handlers.dedup();
    returning_handlers.sort_unstable();
    returning_handlers.dedup();
    truncated_handlers.sort_unstable();
    truncated_handlers.dedup();
    transfers.sort_by_key(|transfer| transfer.handler_target);

    Some(VmStepSummary {
        kind: interpreter.kind,
        loop_header,
        dispatch_header: interpreter.dispatch_header,
        selector: interpreter.selector.clone(),
        dispatch_targets,
        default_target,
        case_values_by_target,
        loop_latches,
        state_inputs: state_inputs.into_iter().collect(),
        state_outputs: state_outputs.into_iter().collect(),
        step_blocks,
        handler_regions,
        handler_state_inputs,
        handler_state_outputs,
        handler_state_updates,
        handler_exit_guards,
        handler_memory_read_effects,
        handler_memory_write_effects,
        handler_memory_reads,
        handler_memory_writes,
        handler_calls,
        handler_conditional_branches,
        handler_exit_targets,
        redispatch_handlers,
        returning_handlers,
        truncated_handlers,
        transfers,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceFunctionInterface,
        SourceFunctionReturn, SsaArtifact,
    };

    use super::*;

    const RAX: u64 = 0;
    const RDI: u64 = 8;

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn exact_affine_aarch64_fixture() -> (ArchSpec, SourceFunctionInterface) {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        arch.add_register(RegisterDef::new("x1", 0x08, 8));
        arch.add_register(RegisterDef::sub("w1", 0x08, 4, "x1"));
        arch.add_register(RegisterDef::new("sp", 0x10, 8));
        arch.add_register(RegisterDef::new("lr", 0x18, 8));
        let interface = SourceFunctionInterface::new_exact(
            b"affine-memory-evidence-v1".to_vec(),
            "aarch64",
            [
                SourceAbiParameterSpec::new(0, register_storage(0x00, 8)),
                SourceAbiParameterSpec::new(1, register_storage(0x08, 8)),
            ],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(0x18, 8)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(0x10, 8)))
        .expect("coherent affine memory interface");
        (arch, interface)
    }

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", RAX, 8));
        arch.add_register(RegisterDef::new("RDI", RDI, 8));
        arch
    }

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn make_const(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    fn branch_block(addr: u64, target: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(R2ILOp::Branch {
            target: make_const(target, 8),
        });
        block
    }

    fn conditional_dispatch_block(addr: u64, case_value: u64, handler: u64) -> R2ILBlock {
        conditional_dispatch_block_with_selector(addr, case_value, handler, RAX)
    }

    fn conditional_dispatch_block_with_selector(
        addr: u64,
        case_value: u64,
        handler: u64,
        selector: u64,
    ) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        let cond = Varnode::unique(addr, 1);
        block.push(R2ILOp::IntEqual {
            dst: cond.clone(),
            a: make_reg(selector, 8),
            b: make_const(case_value, 8),
        });
        block.push(R2ILOp::CBranch {
            target: make_const(handler, 8),
            cond,
        });
        block
    }

    fn redispatch_handler(addr: u64, value: u64, loop_header: u64) -> R2ILBlock {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(R2ILOp::IntAdd {
            dst: make_reg(RAX, 8),
            a: make_reg(RDI, 8),
            b: make_const(value, 8),
        });
        block.push(R2ILOp::Branch {
            target: make_const(loop_header, 8),
        });
        block
    }

    #[test]
    fn affine_parameter_memory_is_exact_vm_evidence() {
        let (arch, interface) = exact_affine_aarch64_fixture();

        let mut block = R2ILBlock::new(0x3000, 4);
        block.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
            val: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x20, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::IntSExt {
            dst: Varnode::unique(0x30, 8),
            src: Varnode::register(0x08, 4),
        });
        block.push(R2ILOp::IntMult {
            dst: Varnode::unique(0x40, 8),
            a: Varnode::unique(0x30, 8),
            b: Varnode::constant(40, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x50, 8),
            a: Varnode::unique(0x20, 8),
            b: Varnode::unique(0x40, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x60, 8),
            a: Varnode::unique(0x50, 8),
            b: Varnode::constant(16, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x60, 8),
            val: Varnode::constant(0x2a, 4),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x70, 8),
            a: Varnode::unique(0x50, 8),
            b: Varnode::constant(4, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x80, 2),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x70, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let func = SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("affine VM SSA fixture");
        assert_eq!(
            func.provenance_kind(),
            r2ssa::SsaArtifactProvenanceKind::Manual
        );
        let block = func.get_block(0x3000).expect("entry block");
        let mut affine_read = None;
        let mut affine_write = None;
        for (op_idx, op) in block.ops.iter().enumerate() {
            let (reads, writes, residual) =
                vm_memory_conditions_for_op(&func, block.addr, op_idx, op);
            for condition in reads {
                if !condition.address.terms().is_empty() {
                    let value = classify_vm_op_value_at_site(&func, block.addr, op_idx, op, 0);
                    affine_read = Some((condition, residual, value));
                }
            }
            for condition in writes {
                if !condition.address.terms().is_empty() {
                    affine_write = Some((condition, residual));
                }
            }
        }

        let (read, read_residual, read_value) = affine_read.expect("affine parameter read");
        assert!(!read_residual, "{read:#?}");
        assert_eq!(read.region.kind, MemoryRegionKind::Input);
        assert_eq!(read.region.name, "arg0");
        assert_eq!(read.address.offset_lo(), 4);
        assert!(!read.address.is_exact_offset());
        assert!(read.address.has_exact_identity());
        assert_eq!(read.address.terms().len(), 1);
        assert_eq!(read.address.terms()[0].coefficient, 40);
        assert!(read.evidence().is_default_exact());
        assert_eq!(
            read_value,
            read.binding
                .as_ref()
                .map(|binding| VmValueExpr::Var(binding.clone()))
        );

        let (write, write_residual) = affine_write.expect("affine parameter write");
        assert!(!write_residual, "{write:#?}");
        assert_eq!(write.region.kind, MemoryRegionKind::Input);
        assert_eq!(write.region.name, "arg0");
        assert_eq!(write.address.offset_lo(), 16);
        assert!(!write.address.is_exact_offset());
        assert!(write.address.has_exact_identity());
        assert_eq!(write.address.terms().len(), 1);
        assert_eq!(write.address.terms()[0].coefficient, 40);
        assert_eq!(write.value, Some(VmValueExpr::Const(0x2a)));
        assert!(write.exact_value);
        assert!(write.evidence().is_default_exact());
        assert_ne!(read.binding, write.binding);
    }

    #[test]
    fn conditional_dispatch_ladder_is_a_vm_dispatch() {
        let loop_header = 0x1000;
        let dispatch_header = 0x1010;
        let mut blocks = vec![branch_block(loop_header, dispatch_header)];
        for index in 0..5u64 {
            blocks.push(conditional_dispatch_block(
                dispatch_header + index * 4,
                index,
                0x2000 + index * 4,
            ));
            blocks.push(redispatch_handler(
                0x2000 + index * 4,
                index + 1,
                loop_header,
            ));
        }
        blocks.push(redispatch_handler(dispatch_header + 5 * 4, 6, loop_header));
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");

        let enclosing = enclosing_loop_header(&func, dispatch_header);
        assert!(
            enclosing
                .as_ref()
                .is_some_and(|(_, latches)| !latches.is_empty()),
            "enclosing={enclosing:?} cfg={:?}",
            func.function().cfg_risk_summary()
        );
        assert!(
            conditional_dispatch_ladder(&func, dispatch_header).is_some(),
            "cfg={:?}",
            func.function().cfg_risk_summary()
        );
        let interpreter = classify_interpreter_like(&func).expect("dispatch ladder");
        assert_eq!(interpreter.kind, InterpreterKind::SwitchDispatch);
        assert_eq!(interpreter.dispatch_header, dispatch_header);
        assert_eq!(interpreter.dispatch_targets, 6);

        let targets = interpreter_dispatch_targets(&func, &interpreter);
        assert_eq!(targets.0.len(), 6, "{targets:?}");

        let vm = build_vm_step_summary(&func, &interpreter).expect("vm step summary");
        assert!(vm.has_strong_vm_evidence(), "{vm:?}");
        assert_eq!(vm.transfers.len(), 6);
        assert!(vm.truncated_handlers.is_empty());
    }

    #[test]
    fn conditional_ladder_with_different_selectors_is_not_a_vm_dispatch() {
        let loop_header = 0x1000;
        let dispatch_header = 0x1010;
        let mut blocks = vec![branch_block(loop_header, dispatch_header)];
        for index in 0..5u64 {
            let selector = if index == 2 { RDI } else { RAX };
            blocks.push(conditional_dispatch_block_with_selector(
                dispatch_header + index * 4,
                index,
                0x2000 + index * 4,
                selector,
            ));
            blocks.push(redispatch_handler(
                0x2000 + index * 4,
                index + 1,
                loop_header,
            ));
        }
        blocks.push(redispatch_handler(dispatch_header + 5 * 4, 6, loop_header));
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");

        assert!(conditional_dispatch_ladder(&func, dispatch_header).is_none());
        assert!(classify_interpreter_like(&func).is_none());
        assert!(!has_strong_vm_evidence(&func));
    }

    #[test]
    fn handler_scc_summary_does_not_truncate_large_linear_handler() {
        let dispatch = 0x1000;
        let entry = 0x2000;
        let mut blocks = Vec::new();
        for index in 0..20 {
            let addr = entry + index * 4;
            let target = if index == 19 { dispatch } else { addr + 4 };
            blocks.push(branch_block(addr, target));
        }
        blocks.push(R2ILBlock::new(dispatch, 4));
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");

        let summary =
            summarize_handler_region(&func, entry, dispatch, dispatch, &BTreeSet::from([entry]));

        assert_eq!(summary.blocks.len(), 20);
        assert!(summary.reenters_dispatch);
        assert_eq!(summary.exit_targets, vec![dispatch]);
        assert!(!summary.truncated);
    }

    #[test]
    fn handler_scc_summary_handles_self_loop_and_redispatch_exit() {
        let dispatch = 0x1000;
        let entry = 0x2000;
        let mut loop_block = R2ILBlock::new(entry, 4);
        loop_block.push(R2ILOp::IntAdd {
            dst: make_reg(RAX, 8),
            a: make_reg(RAX, 8),
            b: make_const(1, 8),
        });
        loop_block.push(R2ILOp::CBranch {
            target: make_const(entry, 8),
            cond: make_reg(RAX, 1),
        });
        let blocks = vec![
            loop_block,
            branch_block(0x2004, dispatch),
            R2ILBlock::new(dispatch, 4),
        ];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");

        let summary =
            summarize_handler_region(&func, entry, dispatch, dispatch, &BTreeSet::from([entry]));

        assert_eq!(summary.blocks, vec![entry, 0x2004]);
        assert!(summary.reenters_dispatch);
        assert!(!summary.truncated);
        assert_eq!(summary.conditional_branches, 1);
        assert!(!summary.exit_guards.is_empty());
    }

    #[test]
    fn handler_state_updates_keep_only_the_live_final_definition() {
        let dispatch = 0x1000;
        let entry = 0x3000;
        let mut block = R2ILBlock::new(entry, 4);
        block.push(R2ILOp::Copy {
            dst: make_reg(RAX, 8),
            src: make_const(1, 8),
        });
        block.push(R2ILOp::Copy {
            dst: make_reg(RAX, 8),
            src: make_const(2, 8),
        });
        block.push(R2ILOp::Branch {
            target: make_const(dispatch, 8),
        });
        let mut dispatch_block = R2ILBlock::new(dispatch, 4);
        dispatch_block.push(R2ILOp::IntAdd {
            dst: make_reg(RDI, 8),
            a: make_reg(RAX, 8),
            b: make_const(1, 8),
        });
        dispatch_block.push(R2ILOp::Return {
            target: make_reg(RDI, 8),
        });
        let blocks = vec![block, dispatch_block];
        let func = SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa");

        let summary =
            summarize_handler_region(&func, entry, dispatch, dispatch, &BTreeSet::from([entry]));

        let update = summary
            .state_updates
            .iter()
            .find(|update| same_logical_name(&update.output, "RAX"))
            .expect("RAX update");
        assert!(update.exact, "{update:#?}");
        assert_eq!(update.value, VmValueExpr::Const(2));
        assert_eq!(summary.state_outputs, vec![update.output.clone()]);
        assert!(!summary.truncated);
    }
}
