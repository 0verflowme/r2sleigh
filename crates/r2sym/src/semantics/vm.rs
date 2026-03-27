use std::collections::{BTreeMap, BTreeSet, VecDeque};

use r2ssa::cfg::BlockTerminator;
use r2ssa::{CFGEdge, SSAOp, SSAVar, SsaArtifact};
use serde::{Deserialize, Serialize};

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
pub enum VmValueExpr {
    Const(u64),
    Var(String),
    Expr(String),
}

impl VmValueExpr {
    fn render(&self) -> String {
        match self {
            Self::Const(value) => format!("0x{value:x}"),
            Self::Var(name) | Self::Expr(name) => name.clone(),
        }
    }

    fn is_exact(&self) -> bool {
        matches!(self, Self::Const(_) | Self::Var(_))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmStateUpdate {
    pub output: String,
    pub expr: String,
    pub value: VmValueExpr,
    pub exact: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmTransferArm {
    pub handler_target: u64,
    pub case_values: Vec<u64>,
    pub region_blocks: Vec<u64>,
    pub exit_targets: Vec<u64>,
    pub state_updates: Vec<VmStateUpdate>,
    pub selector_update: Option<VmStateUpdate>,
    pub exact: bool,
    pub redispatch: bool,
    pub may_return: bool,
    pub truncated: bool,
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
    memory_reads: usize,
    memory_writes: usize,
    calls: usize,
    conditional_branches: usize,
    exit_targets: Vec<u64>,
    reenters_dispatch: bool,
    may_return: bool,
    truncated: bool,
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
        _ => VmValueExpr::Expr(render_vm_op_expr(func, op, depth + 1)?),
    })
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
    let mut memory_reads = 0usize;
    let mut memory_writes = 0usize;
    let mut calls = 0usize;
    let mut conditional_branches = 0usize;
    let mut reenters_dispatch = false;
    let mut may_return = false;
    let mut truncated = false;

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
        }
        if matches!(
            cfg_block.map(|block| &block.terminator),
            Some(BlockTerminator::Return)
        ) {
            may_return = true;
        }

        record_block_state(block, &mut state_inputs, &mut state_outputs);
        for op in &block.ops {
            if op.is_memory_read() {
                memory_reads += 1;
            }
            if op.is_memory_write() {
                memory_writes += 1;
            }
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
                let value = classify_vm_op_value(func, op, 0)
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
        memory_reads,
        memory_writes,
        calls,
        conditional_branches,
        exit_targets: exit_targets.into_iter().collect(),
        reenters_dispatch,
        may_return,
        truncated,
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
        let exact = !summary.truncated
            && summary.state_updates.iter().all(|update| update.exact)
            && selector_update.as_ref().is_none_or(|update| update.exact);
        transfers.push(VmTransferArm {
            handler_target: target,
            case_values,
            region_blocks: summary.blocks.clone(),
            exit_targets: summary.exit_targets.clone(),
            state_updates: summary.state_updates.clone(),
            selector_update,
            exact,
            redispatch: summary.reenters_dispatch,
            may_return: summary.may_return,
            truncated: summary.truncated,
        });
        handler_regions.insert(target, summary.blocks);
        handler_state_inputs.insert(target, summary.state_inputs);
        handler_state_outputs.insert(target, summary.state_outputs);
        handler_state_updates.insert(target, summary.state_updates);
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
