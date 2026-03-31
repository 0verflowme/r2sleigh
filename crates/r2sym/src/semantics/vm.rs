use std::collections::{BTreeMap, BTreeSet, VecDeque};

use r2ssa::cfg::BlockTerminator;
use r2ssa::{CFGEdge, ObjectKind, SSAOp, SSAVar, SsaArtifact, StackAddressBase};
use serde::{Deserialize, Serialize};

use super::{
    SemanticConfidence, SemanticEvidence, SemanticEvidenceAmbiguity, SemanticEvidenceCoverage,
    SemanticEvidenceProvenance, SemanticEvidenceReason,
};
use crate::MemoryRegionKind;

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
        }
    }

    fn is_exact(&self) -> bool {
        match self {
            Self::Const(_) | Self::Var(_) => true,
            Self::Unary { arg, .. } => arg.is_exact(),
            Self::Binary { lhs, rhs, .. } => lhs.is_exact() && rhs.is_exact(),
            Self::Expr(_) => false,
        }
    }

    fn lookup_binding(bindings: &BTreeMap<String, u64>, name: &str) -> Option<u64> {
        bindings.get(name).copied().or_else(|| {
            bindings
                .iter()
                .find_map(|(candidate, value)| same_logical_name(candidate, name).then_some(*value))
        })
    }

    pub(crate) fn evaluate_u64(&self, bindings: &BTreeMap<String, u64>) -> Option<u64> {
        match self {
            Self::Const(value) => Some(*value),
            Self::Var(name) => Self::lookup_binding(bindings, name),
            Self::Unary { op, arg } => {
                let value = arg.evaluate_u64(bindings)?;
                Some(match op {
                    VmUnaryOp::Neg => value.wrapping_neg(),
                    VmUnaryOp::BitNot => !value,
                    VmUnaryOp::BoolNot => u64::from(value == 0),
                })
            }
            Self::Binary { op, lhs, rhs } => {
                let lhs = lhs.evaluate_u64(bindings)?;
                let rhs = rhs.evaluate_u64(bindings)?;
                Some(match op {
                    VmBinaryOp::Add => lhs.wrapping_add(rhs),
                    VmBinaryOp::Sub => lhs.wrapping_sub(rhs),
                    VmBinaryOp::Mul => lhs.wrapping_mul(rhs),
                    VmBinaryOp::Div => lhs.checked_div(rhs)?,
                    VmBinaryOp::Rem => lhs.checked_rem(rhs)?,
                    VmBinaryOp::And => lhs & rhs,
                    VmBinaryOp::Or => lhs | rhs,
                    VmBinaryOp::Xor => lhs ^ rhs,
                    VmBinaryOp::Shl => lhs.wrapping_shl((rhs & 63) as u32),
                    VmBinaryOp::LShr => lhs.wrapping_shr((rhs & 63) as u32),
                    VmBinaryOp::AShr => ((lhs as i64) >> ((rhs & 63) as u32)) as u64,
                    VmBinaryOp::Eq => u64::from(lhs == rhs),
                    VmBinaryOp::Ne => u64::from(lhs != rhs),
                    VmBinaryOp::Lt => u64::from(lhs < rhs),
                    VmBinaryOp::SLt => u64::from((lhs as i64) < (rhs as i64)),
                    VmBinaryOp::Le => u64::from(lhs <= rhs),
                    VmBinaryOp::SLe => u64::from((lhs as i64) <= (rhs as i64)),
                    VmBinaryOp::BoolAnd => u64::from(lhs != 0 && rhs != 0),
                    VmBinaryOp::BoolOr => u64::from(lhs != 0 || rhs != 0),
                })
            }
            Self::Expr(_) => None,
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
    pub(crate) fn evaluate(&self, bindings: &BTreeMap<String, u64>) -> Option<bool> {
        let value = self.value.evaluate_u64(bindings)?;
        Some((value != 0) == self.expect_nonzero)
    }

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
    pub offset_lo: i64,
    pub offset_hi: i64,
    pub size: u32,
    pub exact_offset: bool,
    pub binding: Option<String>,
    pub expr: String,
    pub value_expr: Option<String>,
    pub value: Option<VmValueExpr>,
    pub exact_value: bool,
}

impl VmMemoryCondition {
    pub fn evidence(&self) -> SemanticEvidence {
        if self.exact_offset && (self.value.is_none() || self.exact_value) {
            SemanticEvidence::exact()
        } else if self.binding.is_some() || self.exact_offset {
            let reason = if self.exact_offset {
                SemanticEvidenceReason::ValueOpaque
            } else {
                SemanticEvidenceReason::AliasAmbiguity
            };
            SemanticEvidence::likely(reason)
                .with_provenance(SemanticEvidenceProvenance::Normalized)
                .with_ambiguity(if self.exact_offset {
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

const MAX_HANDLER_REGION_BLOCKS: usize = 16;
const MAX_HANDLER_REGION_DEPTH: usize = 8;

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

fn record_block_state(
    block: &r2ssa::function::SSABlock,
    state_inputs: &mut BTreeSet<String>,
    state_outputs: &mut BTreeSet<String>,
) {
    block.for_each_source(|src| {
        if (!src.var.is_register() && !src.var.name.starts_with("ram:")) || src.var.version != 0 {
            return;
        }
        state_inputs.insert(src.var.display_name());
    });
    for phi in &block.phis {
        if !phi.dst.is_const() && !phi.dst.is_temp() && !phi.dst.name.starts_with("ram:") {
            state_outputs.insert(phi.dst.display_name());
        }
    }
    for op in &block.ops {
        let Some(dst) = op.dst() else {
            continue;
        };
        if dst.is_const() || dst.is_temp() || dst.name.starts_with("ram:") {
            continue;
        }
        state_outputs.insert(dst.display_name());
    }
}

fn case_values_by_target(
    func: &SsaArtifact,
    dispatch_header: u64,
) -> (BTreeMap<u64, Vec<u64>>, Option<u64>) {
    let Some((cases, default_target)) = func.function().switch_info(dispatch_header) else {
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

fn vm_memory_binding_name(region: &VmMemoryRegionRef, offset: i64, size: u32) -> String {
    format!("mem:r{}:{offset}:{size}", region.id)
}

fn vm_memory_region_ref_from_object(
    func: &SsaArtifact,
    object_id: r2ssa::ObjectId,
) -> Option<VmMemoryRegionRef> {
    let object = func.objects().object(object_id)?;
    let (kind, name) = match &object.kind {
        ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset } => (
            MemoryRegionKind::Stack,
            format!("stack:{}{:+#x}", stack_base_name(*base), offset),
        ),
        ObjectKind::Global { space, address } => {
            (MemoryRegionKind::Global, format!("{space}:0x{address:x}"))
        }
        ObjectKind::HeapAlloc { call_site } => (
            MemoryRegionKind::Heap,
            format!("heap_alloc@{}", call_site.0),
        ),
        ObjectKind::EscapedUnknown => return None,
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
        for use_fact in uses {
            let Some(region) = vm_memory_region_ref_from_object(func, use_fact.location.object)
            else {
                residual = true;
                continue;
            };
            let binding = Some(vm_memory_binding_name(
                &region,
                use_fact.location.offset,
                use_fact.location.size,
            ));
            reads.push(VmMemoryCondition {
                region,
                offset_lo: use_fact.location.offset,
                offset_hi: use_fact.location.offset,
                size: use_fact.location.size,
                exact_offset: true,
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
        for def in defs {
            let Some(region) = vm_memory_region_ref_from_object(func, def.location.object) else {
                residual = true;
                continue;
            };
            let binding = Some(vm_memory_binding_name(
                &region,
                def.location.offset,
                def.location.size,
            ));
            writes.push(VmMemoryCondition {
                region,
                offset_lo: def.location.offset,
                offset_hi: def.location.offset,
                size: def.location.size,
                exact_offset: true,
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
            lhs.offset_lo,
            lhs.size,
            lhs.binding.as_deref(),
            &lhs.expr,
        )
            .cmp(&(
                rhs.region.id,
                &rhs.region.name,
                rhs.offset_lo,
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
            lhs.offset_lo,
            lhs.size,
            lhs.binding.as_deref(),
            &lhs.expr,
            lhs.value_expr.as_deref(),
            lhs.exact_value,
        )
            .cmp(&(
                rhs.region.id,
                &rhs.region.name,
                rhs.offset_lo,
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

fn summarize_handler_region(
    func: &SsaArtifact,
    entry: u64,
    dispatch_header: u64,
    loop_header: u64,
    dispatch_targets: &BTreeSet<u64>,
) -> HandlerRegionSummary {
    let mut visited = BTreeSet::new();
    let mut queue = VecDeque::from([(entry, 0usize)]);
    let mut exit_targets = BTreeSet::new();
    let mut state_inputs = BTreeSet::new();
    let mut state_outputs = BTreeSet::new();
    let mut state_updates = BTreeMap::<String, VmValueExpr>::new();
    let mut exit_guards = Vec::new();
    let mut seen_exit_guards = BTreeSet::new();
    let mut memory_read_effects = Vec::new();
    let mut memory_write_effects = Vec::new();
    let mut memory_reads = 0usize;
    let mut memory_writes = 0usize;
    let mut calls = 0usize;
    let mut conditional_branches = 0usize;
    let mut reenters_dispatch = false;
    let mut may_return = false;
    let mut truncated = false;
    let mut residual_guards = false;
    let mut residual_memory_effects = false;

    while let Some((block_addr, depth)) = queue.pop_front() {
        if !visited.insert(block_addr) {
            continue;
        }
        if visited.len() > MAX_HANDLER_REGION_BLOCKS {
            truncated = true;
            visited.remove(&block_addr);
            continue;
        }

        let Some(block) = func.get_block(block_addr) else {
            continue;
        };
        let cfg_block = func.cfg().get_block(block_addr);
        if matches!(
            cfg_block.map(|block| &block.terminator),
            Some(BlockTerminator::ConditionalBranch { .. })
        ) {
            conditional_branches += 1;
            let (block_guards, residual) =
                vm_exit_guards_for_block(func, block_addr, &mut seen_exit_guards);
            if block_guards.is_empty() {
                residual_guards |= residual;
            } else {
                exit_guards.extend(block_guards);
            }
        }
        if matches!(
            cfg_block.map(|block| &block.terminator),
            Some(BlockTerminator::Return)
        ) {
            may_return = true;
        }

        record_block_state(block, &mut state_inputs, &mut state_outputs);
        for (op_idx, op) in block.ops.iter().enumerate() {
            if op.is_memory_read() {
                memory_reads += 1;
            }
            if op.is_memory_write() {
                memory_writes += 1;
            }
            let (reads, writes, residual) =
                vm_memory_conditions_for_op(func, block_addr, op_idx, op);
            if residual {
                residual_memory_effects = true;
            }
            memory_read_effects.extend(reads);
            memory_write_effects.extend(writes);
            if matches!(
                op,
                SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::CallOther { .. }
            ) {
                calls += 1;
            }
            if let Some(dst) = op.dst()
                && !dst.is_const()
                && !dst.is_temp()
                && !dst.name.starts_with("ram:")
            {
                let value = classify_vm_op_value_at_site(func, block_addr, op_idx, op, 0)
                    .unwrap_or_else(|| VmValueExpr::Var(dst.display_name()));
                state_updates.insert(dst.display_name(), value);
            }
        }

        let succs = func.successors(block_addr);
        if succs.is_empty() {
            continue;
        }
        for succ in succs {
            if succ == dispatch_header || succ == loop_header {
                reenters_dispatch = true;
                exit_targets.insert(succ);
                continue;
            }
            if dispatch_targets.contains(&succ) && succ != entry {
                exit_targets.insert(succ);
                continue;
            }
            if depth >= MAX_HANDLER_REGION_DEPTH {
                truncated = true;
                exit_targets.insert(succ);
                continue;
            }
            queue.push_back((succ, depth + 1));
        }
    }

    exit_guards.sort_by(|lhs, rhs| {
        (lhs.target, &lhs.guard.expr, lhs.guard.expect_nonzero).cmp(&(
            rhs.target,
            &rhs.guard.expr,
            rhs.guard.expect_nonzero,
        ))
    });
    memory_read_effects.sort_by(|lhs, rhs| {
        (
            lhs.region.id,
            &lhs.region.name,
            lhs.offset_lo,
            lhs.size,
            &lhs.expr,
        )
            .cmp(&(
                rhs.region.id,
                &rhs.region.name,
                rhs.offset_lo,
                rhs.size,
                &rhs.expr,
            ))
    });
    memory_read_effects.dedup();
    memory_write_effects.sort_by(|lhs, rhs| {
        (
            lhs.region.id,
            &lhs.region.name,
            lhs.offset_lo,
            lhs.size,
            &lhs.expr,
        )
            .cmp(&(
                rhs.region.id,
                &rhs.region.name,
                rhs.offset_lo,
                rhs.size,
                &rhs.expr,
            ))
    });
    memory_write_effects.dedup();

    HandlerRegionSummary {
        blocks: visited.into_iter().collect(),
        state_inputs: state_inputs.into_iter().collect(),
        state_outputs: state_outputs.into_iter().collect(),
        state_updates: state_updates
            .into_iter()
            .map(|(output, value)| VmStateUpdate {
                output,
                expr: value.render(),
                exact: value.is_exact(),
                value,
            })
            .collect(),
        exit_guards,
        memory_read_effects,
        memory_write_effects,
        memory_reads,
        memory_writes,
        calls,
        conditional_branches,
        exit_targets: exit_targets.into_iter().collect(),
        reenters_dispatch,
        may_return,
        truncated,
        residual_guards,
        residual_memory_effects,
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

pub(crate) fn classify_interpreter_like(func: &SsaArtifact) -> Option<InterpreterDispatchSummary> {
    let summary = func.function().cfg_risk_summary();
    if summary.block_count < 6 || summary.loop_count == 0 {
        return None;
    }

    let has_indirect = func
        .cfg()
        .block_addrs()
        .filter_map(|addr| func.cfg().get_block(addr))
        .any(|block| matches!(block.terminator, BlockTerminator::IndirectBranch));
    if summary.switch_block_count == 0 && !has_indirect {
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
        let selector = func
            .function()
            .infer_switch_selector_var(block_addr)
            .map(|var| var.name);
        let dispatch_targets = func.successors(block_addr);
        let kind = match block.terminator {
            BlockTerminator::Switch { .. } => InterpreterKind::SwitchDispatch,
            BlockTerminator::IndirectBranch => InterpreterKind::IndirectDispatch,
            _ if dispatch_targets.len() >= 4 && selector.is_some() => {
                InterpreterKind::SwitchDispatch
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
        if score < threshold || score < best_score {
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
    let dispatch_targets = func.successors(interpreter.dispatch_header);
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
    let (case_values_by_target, default_target) =
        case_values_by_target(func, interpreter.dispatch_header);
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
            .all(|effect| effect.exact_offset)
            && summary
                .memory_write_effects
                .iter()
                .all(|effect| effect.exact_offset && effect.exact_value);
        let exact = !summary.truncated
            && summary.calls == 0
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
