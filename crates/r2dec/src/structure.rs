//! Control flow structuring.
//!
//! This module converts unstructured control flow (gotos, CFG edges) into
//! structured high-level constructs (if-then-else, while, for, etc.).

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use r2ssa::cfg::BlockTerminator;
use r2ssa::{CFGEdge, ControlGuard, LoopId, PredicateId, SSAFunction, SSAOp, ValueId};

use crate::address::parse_address_from_var_name;
use crate::ast::{BinaryOp, CExpr, CStmt, UnaryOp};
use crate::control::{DecompileExecutionStop, DecompileWorkControl};
use crate::fold::FoldingContext;
use crate::fold::context::EffectOccurrenceKind;
use crate::fold::op_lower::OpLoweringRefusal;
use crate::region::{Region, RegionAnalyzer, RegionTransferKind};
use crate::structured_region::{
    SealedStructuredBody, StructuredRegionBuildError, StructuredRegionKind,
    StructuredRegionMarker, SyntheticRegionKind, kind_of, seal_structured_body,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ControlFlowStructureError {
    Lowering(OpLoweringRefusal),
    StructuredRegion(StructuredRegionBuildError),
}

impl From<OpLoweringRefusal> for ControlFlowStructureError {
    fn from(error: OpLoweringRefusal) -> Self {
        Self::Lowering(error)
    }
}

impl From<StructuredRegionBuildError> for ControlFlowStructureError {
    fn from(error: StructuredRegionBuildError) -> Self {
        Self::StructuredRegion(error)
    }
}

pub(crate) type ControlFlowStructureResult<T> = Result<T, ControlFlowStructureError>;

enum ExitContinuationError {
    Placement(Option<String>),
    Structure(ControlFlowStructureError),
}

impl From<ControlFlowStructureError> for ExitContinuationError {
    fn from(error: ControlFlowStructureError) -> Self {
        Self::Structure(error)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ControlRenderProofKind {
    Branch,
    Loop,
    Switch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ControlRenderProof {
    pub kind: ControlRenderProofKind,
    pub anchor: u64,
    pub branch_condition: Option<PredicateId>,
    pub branch_condition_value: Option<ValueId>,
    pub loop_condition: Option<PredicateId>,
    pub loop_condition_value: Option<ValueId>,
    pub loop_body_blocks: Vec<u64>,
    pub loop_latches: Vec<u64>,
    pub loop_exits: Vec<u64>,
    pub switch_selector: Option<ValueId>,
    pub switch_cases: Vec<(u64, u64)>,
    pub switch_default: Option<u64>,
}

impl ControlRenderProof {
    fn branch_proof(
        anchor: u64,
        branch_condition: Option<PredicateId>,
        branch_condition_value: Option<ValueId>,
    ) -> Self {
        Self {
            kind: ControlRenderProofKind::Branch,
            anchor,
            branch_condition,
            branch_condition_value,
            loop_condition: None,
            loop_condition_value: None,
            loop_body_blocks: Vec::new(),
            loop_latches: Vec::new(),
            loop_exits: Vec::new(),
            switch_selector: None,
            switch_cases: Vec::new(),
            switch_default: None,
        }
    }

    fn loop_proof(
        anchor: u64,
        loop_condition: Option<PredicateId>,
        loop_condition_value: Option<ValueId>,
        loop_body_blocks: Vec<u64>,
        loop_latches: Vec<u64>,
        loop_exits: Vec<u64>,
    ) -> Self {
        Self {
            kind: ControlRenderProofKind::Loop,
            anchor,
            branch_condition: None,
            branch_condition_value: None,
            loop_condition,
            loop_condition_value,
            loop_body_blocks,
            loop_latches,
            loop_exits,
            switch_selector: None,
            switch_cases: Vec::new(),
            switch_default: None,
        }
    }

    fn switch_proof(
        anchor: u64,
        switch_selector: Option<ValueId>,
        switch_cases: Vec<(u64, u64)>,
        switch_default: Option<u64>,
    ) -> Self {
        Self {
            kind: ControlRenderProofKind::Switch,
            anchor,
            branch_condition: None,
            branch_condition_value: None,
            loop_condition: None,
            loop_condition_value: None,
            loop_body_blocks: Vec::new(),
            loop_latches: Vec::new(),
            loop_exits: Vec::new(),
            switch_selector,
            switch_cases,
            switch_default,
        }
    }
}

/// Control flow structurer.
///
/// Converts a region tree into structured C statements.
pub(crate) struct ControlFlowStructurer<'a, 'o> {
    func: &'a SSAFunction,
    /// Folding context for expression optimization.
    fold_ctx: &'o FoldingContext<'o>,
    /// Cached folded statements per basic block.
    folded_block_cache: HashMap<u64, FoldedBlock>,
    /// Labels for blocks that need gotos.
    labels: HashMap<u64, String>,
    /// Labels already attached to a concrete AST occurrence.
    emitted_labels: BTreeSet<u64>,
    /// Counter for generating unique labels.
    label_counter: usize,
    /// Region analyzer for detecting breaks/continues.
    region_analyzer: Option<RegionAnalyzer<'a>>,
    control: Option<DecompileWorkControl<'a>>,
    stop_reason: Cell<Option<DecompileExecutionStop>>,
    /// Safety budget for recursive region structuring.
    safety_budget_remaining: usize,
    safety_budget_max: usize,
    safety_reason: Option<String>,
    /// Structured control nodes emitted by this structurer, in render order.
    control_render_proofs: Vec<ControlRenderProof>,
    /// Merge blocks owned by enclosing regions and therefore emitted there.
    deferred_merge_blocks: Vec<u64>,
    /// Exit targets more than one edge reaches, and the exits that jumped to
    /// them. Such a block cannot sit at any one exit without saying it runs
    /// once per edge, so it is written once after the body instead.
    deferred_shared_exits: BTreeMap<u64, BTreeSet<u64>>,
    /// Blocks many branches converge on that no region holds. A region says
    /// if/else with a merge every path runs through; a block some path steps
    /// around is neither, so the shape has nowhere to put it.
    shared_joins: BTreeSet<u64>,
    /// Exact lexical control-domain alternatives currently being emitted.
    /// A labeled side entry can join another certified alternative without
    /// weakening the domain checks for downstream blocks.
    active_domains: Vec<RenderedBlockDomain>,
    /// Every lexical domain in which a source block was emitted. Shared CFG
    /// blocks may be duplicated by structuring, so coverage is checked only
    /// after all occurrences are known.
    rendered_block_domains: BTreeMap<u64, Vec<RenderedBlockOccurrence>>,
    /// True only while producing the artifact-bearing structured body.
    retain_region_markers: bool,
    /// Basic blocks owned by the current structured region tree.
    structured_region_blocks: BTreeSet<u64>,
    /// Blocks the proof shows nothing can reach, computed once for this function.
    proven_dead_blocks: std::cell::OnceCell<BTreeSet<u64>>,
    /// Exact side-entry domains that reach a labeled block through a certified
    /// noncanonical loop exit.
    transfer_target_domains: BTreeMap<u64, Vec<RenderedBlockDomain>>,
}

#[derive(Debug, Clone)]
struct FoldedBlock {
    stmts: Vec<CStmt>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct RenderedBlockDomain {
    guards: Vec<ControlGuard>,
    loops: Vec<LoopId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RenderedBlockOccurrence {
    alternatives: Vec<RenderedBlockDomain>,
}

const BDD_FALSE: usize = 0;
const BDD_TRUE: usize = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum BddOp {
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct BddNode {
    variable: PredicateId,
    low: usize,
    high: usize,
}

struct ControlBdd<'a, 's> {
    nodes: Vec<Option<BddNode>>,
    unique: HashMap<BddNode, usize>,
    apply_cache: HashMap<(BddOp, usize, usize), usize>,
    not_cache: HashMap<usize, usize>,
    node_limit: usize,
    control: Option<DecompileWorkControl<'a>>,
    stop_reason: Cell<Option<DecompileExecutionStop>>,
    stop_sink: Option<&'s Cell<Option<DecompileExecutionStop>>>,
}

#[cfg(test)]
impl ControlBdd<'static, 'static> {
    fn new(node_limit: usize) -> Self {
        Self::new_with_optional_control(node_limit, None, None)
    }
}

impl<'a, 's> ControlBdd<'a, 's> {
    fn new_with_optional_control(
        node_limit: usize,
        control: Option<DecompileWorkControl<'a>>,
        stop_sink: Option<&'s Cell<Option<DecompileExecutionStop>>>,
    ) -> Self {
        Self {
            nodes: vec![None, None],
            unique: HashMap::new(),
            apply_cache: HashMap::new(),
            not_cache: HashMap::new(),
            node_limit,
            control,
            stop_reason: Cell::new(None),
            stop_sink,
        }
    }

    fn poll(&self) -> Result<(), String> {
        if self.stop_reason.get().is_some() {
            return Err("control coverage stopped".to_string());
        }
        if let Some(control) = self.control
            && let Err(reason) = control.poll()
        {
            self.stop_reason.set(Some(reason));
            if let Some(stop_sink) = self.stop_sink {
                stop_sink.set(Some(reason));
            }
            return Err("control coverage stopped".to_string());
        }
        Ok(())
    }

    fn created_nodes(&self) -> usize {
        self.nodes.len().saturating_sub(2)
    }

    fn variable(&mut self, variable: PredicateId, truth: bool) -> Result<usize, String> {
        let positive = self.make_node(variable, BDD_FALSE, BDD_TRUE)?;
        if truth {
            Ok(positive)
        } else {
            self.not(positive)
        }
    }

    fn make_node(
        &mut self,
        variable: PredicateId,
        low: usize,
        high: usize,
    ) -> Result<usize, String> {
        self.poll()?;
        if low == high {
            return Ok(low);
        }
        let node = BddNode {
            variable,
            low,
            high,
        };
        if let Some(existing) = self.unique.get(&node).copied() {
            return Ok(existing);
        }
        if self.created_nodes() >= self.node_limit {
            return Err(format!(
                "control coverage BDD exceeded structuring safety budget ({})",
                self.node_limit
            ));
        }
        let id = self.nodes.len();
        self.nodes.push(Some(node));
        self.unique.insert(node, id);
        Ok(id)
    }

    fn not(&mut self, value: usize) -> Result<usize, String> {
        self.poll()?;
        if value == BDD_FALSE {
            return Ok(BDD_TRUE);
        }
        if value == BDD_TRUE {
            return Ok(BDD_FALSE);
        }
        if let Some(cached) = self.not_cache.get(&value).copied() {
            return Ok(cached);
        }
        let node = self
            .nodes
            .get(value)
            .and_then(|node| *node)
            .ok_or_else(|| format!("invalid control coverage BDD node {value}"))?;
        let low = self.not(node.low)?;
        let high = self.not(node.high)?;
        let result = self.make_node(node.variable, low, high)?;
        self.not_cache.insert(value, result);
        self.not_cache.insert(result, value);
        Ok(result)
    }

    fn and(&mut self, lhs: usize, rhs: usize) -> Result<usize, String> {
        self.apply(BddOp::And, lhs, rhs)
    }

    fn or(&mut self, lhs: usize, rhs: usize) -> Result<usize, String> {
        self.apply(BddOp::Or, lhs, rhs)
    }

    fn exists(
        &mut self,
        value: usize,
        variables: &BTreeSet<PredicateId>,
        cache: &mut HashMap<usize, usize>,
    ) -> Result<usize, String> {
        self.poll()?;
        if value == BDD_FALSE || value == BDD_TRUE {
            return Ok(value);
        }
        if let Some(cached) = cache.get(&value).copied() {
            return Ok(cached);
        }
        let node = self
            .nodes
            .get(value)
            .and_then(|node| *node)
            .ok_or_else(|| format!("invalid control coverage BDD node {value}"))?;
        let low = self.exists(node.low, variables, cache)?;
        let high = self.exists(node.high, variables, cache)?;
        let result = if variables.contains(&node.variable) {
            self.or(low, high)?
        } else {
            self.make_node(node.variable, low, high)?
        };
        cache.insert(value, result);
        Ok(result)
    }

    fn apply(&mut self, op: BddOp, lhs: usize, rhs: usize) -> Result<usize, String> {
        self.poll()?;
        let (lhs, rhs) = if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) };
        let terminal = match op {
            BddOp::And if lhs == BDD_FALSE => Some(BDD_FALSE),
            BddOp::And if lhs == BDD_TRUE => Some(rhs),
            BddOp::Or if lhs == BDD_FALSE => Some(rhs),
            BddOp::Or if lhs == BDD_TRUE => Some(BDD_TRUE),
            _ if lhs == rhs => Some(lhs),
            _ => None,
        };
        if let Some(result) = terminal {
            return Ok(result);
        }
        if let Some(cached) = self.apply_cache.get(&(op, lhs, rhs)).copied() {
            return Ok(cached);
        }
        let lhs_node = self.nodes.get(lhs).and_then(|node| *node);
        let rhs_node = self.nodes.get(rhs).and_then(|node| *node);
        let variable = lhs_node
            .map(|node| node.variable)
            .into_iter()
            .chain(rhs_node.map(|node| node.variable))
            .min()
            .ok_or_else(|| "control coverage BDD apply had no variable".to_string())?;
        let (lhs_low, lhs_high) = lhs_node
            .filter(|node| node.variable == variable)
            .map(|node| (node.low, node.high))
            .unwrap_or((lhs, lhs));
        let (rhs_low, rhs_high) = rhs_node
            .filter(|node| node.variable == variable)
            .map(|node| (node.low, node.high))
            .unwrap_or((rhs, rhs));
        let low = self.apply(op, lhs_low, rhs_low)?;
        let high = self.apply(op, lhs_high, rhs_high)?;
        let result = self.make_node(variable, low, high)?;
        self.apply_cache.insert((op, lhs, rhs), result);
        Ok(result)
    }
}

struct SwitchRegionView<'r> {
    entry_block: u64,
    switch_block: u64,
    cases: &'r [(Option<u64>, Box<Region>)],
    default: Option<&'r Region>,
    merge_block: Option<u64>,
    prefix_regions: &'r [Region],
}

impl<'a, 'o> ControlFlowStructurer<'a, 'o> {
    /// Create a new structurer using a pre-analyzed folding context.
    #[cfg(test)]
    pub(crate) fn new(func: &'a SSAFunction, fold_ctx: &'o FoldingContext<'o>) -> Self {
        let region_analyzer = RegionAnalyzer::new(func);
        let safety_budget_max = Self::compute_safety_budget(func.num_blocks());

        Self {
            func,
            fold_ctx,
            folded_block_cache: HashMap::new(),
            labels: HashMap::new(),
            emitted_labels: BTreeSet::new(),
            label_counter: 0,
            region_analyzer: Some(region_analyzer),
            control: None,
            stop_reason: Cell::new(None),
            safety_budget_remaining: safety_budget_max,
            safety_budget_max,
            safety_reason: None,
            control_render_proofs: Vec::new(),
            deferred_merge_blocks: Vec::new(),
            deferred_shared_exits: BTreeMap::new(),
            shared_joins: BTreeSet::new(),
            active_domains: vec![RenderedBlockDomain::default()],
            rendered_block_domains: BTreeMap::new(),
            retain_region_markers: false,
            structured_region_blocks: BTreeSet::new(),
            proven_dead_blocks: std::cell::OnceCell::new(),
            transfer_target_domains: BTreeMap::new(),
        }
    }

    /// Create a structurer that cooperatively polls during region and AST work.
    pub(crate) fn new_with_control(
        func: &'a SSAFunction,
        fold_ctx: &'o FoldingContext<'o>,
        control: DecompileWorkControl<'a>,
    ) -> Result<Self, DecompileExecutionStop> {
        control.poll()?;
        let region_analyzer = RegionAnalyzer::new_with_control(func, control.raw())
            .map_err(|reason| DecompileExecutionStop::new(control.phase(), reason))?;
        let safety_budget_max = Self::compute_safety_budget(func.num_blocks());
        Ok(Self {
            func,
            fold_ctx,
            folded_block_cache: HashMap::new(),
            labels: HashMap::new(),
            emitted_labels: BTreeSet::new(),
            label_counter: 0,
            region_analyzer: Some(region_analyzer),
            control: Some(control),
            stop_reason: Cell::new(None),
            safety_budget_remaining: safety_budget_max,
            safety_budget_max,
            safety_reason: None,
            control_render_proofs: Vec::new(),
            deferred_merge_blocks: Vec::new(),
            deferred_shared_exits: BTreeMap::new(),
            shared_joins: BTreeSet::new(),
            active_domains: vec![RenderedBlockDomain::default()],
            rendered_block_domains: BTreeMap::new(),
            retain_region_markers: false,
            structured_region_blocks: BTreeSet::new(),
            proven_dead_blocks: std::cell::OnceCell::new(),
            transfer_target_domains: BTreeMap::new(),
        })
    }

    fn compute_safety_budget(num_blocks: usize) -> usize {
        num_blocks.saturating_mul(128).max(256)
    }

    fn is_unresolved_indirect_dispatch_block(&self, addr: u64) -> bool {
        let Some(cfg_block) = self.func.cfg().get_block(addr) else {
            return false;
        };

        matches!(
            cfg_block.terminator,
            r2ssa::cfg::BlockTerminator::IndirectBranch
        ) && self.func.successors(addr).is_empty()
            && self.func.switch_info(addr).is_none()
    }

    fn reset_safety_budget(&mut self) {
        self.safety_budget_remaining = self.safety_budget_max;
        self.safety_reason = None;
    }

    #[inline]
    fn poll(&self) -> bool {
        if self.stop_reason.get().is_some() {
            return false;
        }
        if let Some(control) = self.control
            && let Err(reason) = control.poll()
        {
            self.stop_reason.set(Some(reason));
            return false;
        }
        true
    }

    fn consume_safety_budget(&mut self, units: usize) -> bool {
        if self.safety_budget_remaining >= units {
            self.safety_budget_remaining -= units;
            true
        } else {
            if self.safety_reason.is_none() {
                self.safety_reason = Some(format!(
                    "structuring budget exceeded (limit: {})",
                    self.safety_budget_max
                ));
            }
            false
        }
    }

    /// Returns the reason why structuring short-circuited, if any.
    pub(crate) fn safety_reason(&self) -> Option<&str> {
        self.safety_reason.as_deref()
    }

    pub(crate) fn execution_stop(&self) -> Option<DecompileExecutionStop> {
        self.stop_reason.get()
    }

    #[cfg(test)]
    pub(crate) fn control_render_proofs(&self) -> &[ControlRenderProof] {
        &self.control_render_proofs
    }

    fn record_branch_render_proof(
        &mut self,
        anchor: u64,
        condition: Option<PredicateId>,
        condition_value: Option<ValueId>,
    ) {
        self.control_render_proofs
            .push(ControlRenderProof::branch_proof(
                anchor,
                condition,
                condition_value,
            ));
    }

    fn record_loop_render_proof(
        &mut self,
        anchor: u64,
        condition: Option<PredicateId>,
        condition_value: Option<ValueId>,
        body: &Region,
    ) {
        let proof = self.loop_render_proof(anchor, condition, condition_value, body);
        self.control_render_proofs.push(proof);
    }

    fn loop_render_proof(
        &self,
        anchor: u64,
        condition: Option<PredicateId>,
        condition_value: Option<ValueId>,
        body: &Region,
    ) -> ControlRenderProof {
        let loop_body_blocks = self.canonical_loop_body_blocks(anchor, body);
        let (loop_latches, loop_exits) = self.rendered_loop_edges(anchor, &loop_body_blocks);
        ControlRenderProof::loop_proof(
            anchor,
            condition,
            condition_value,
            loop_body_blocks,
            loop_latches,
            loop_exits,
        )
    }

    fn canonical_loop_body_blocks(&self, anchor: u64, body: &Region) -> Vec<u64> {
        if let Some(loop_body) = self
            .region_analyzer
            .as_ref()
            .and_then(|analyzer| analyzer.get_loop_body(anchor))
        {
            let mut blocks = loop_body.iter().copied().collect::<BTreeSet<_>>();
            blocks.insert(anchor);
            return blocks.into_iter().collect();
        }
        Self::sorted_region_blocks_with_anchor(anchor, body)
    }

    /// Attach the exact transfer obligations to the structured control node.
    ///
    /// A transfer is not a statement of its own -- the shape the statements are
    /// arranged in is what renders it -- so nothing recorded that the output owns
    /// it, and an accounting of what the function owes read every branch, loop and
    /// switch as unaccounted for. Recorded here rather than while folding, because
    /// only the structuring knows whether it rendered the control or refused it.
    fn observe_control_ownership(&self, anchor: u64, stmt: CStmt) -> CStmt {
        let Some(block) = self.func.blocks().find(|block| block.addr == anchor) else {
            return stmt;
        };
        let Some(op_idx) = block.ops.len().checked_sub(1) else {
            return stmt;
        };
        let obligations = self.fold_ctx.exact_effect_obligations_for_normalized_value(
            crate::fold::context::EffectOccurrenceKind::Expression,
            anchor,
            op_idx,
            None,
        );
        self.fold_ctx.observe_effect_stmt(&obligations, stmt)
    }

    fn record_switch_render_proof(
        &mut self,
        anchor: u64,
        selector: Option<ValueId>,
        cases: &[(Option<u64>, Box<Region>)],
        default: Option<&Region>,
    ) {
        let proof = self.switch_render_proof(anchor, selector, cases, default);
        self.control_render_proofs.push(proof);
    }

    fn switch_render_proof(
        &self,
        anchor: u64,
        selector: Option<ValueId>,
        cases: &[(Option<u64>, Box<Region>)],
        default: Option<&Region>,
    ) -> ControlRenderProof {
        let mut switch_cases = cases
            .iter()
            .filter_map(|(value, region)| value.map(|value| (value, region.entry())))
            .collect::<Vec<_>>();
        switch_cases.sort_unstable();
        let switch_default = default.map(Region::entry);
        ControlRenderProof::switch_proof(anchor, selector, switch_cases, switch_default)
    }

    fn sorted_region_blocks_with_anchor(anchor: u64, region: &Region) -> Vec<u64> {
        let mut blocks = region.blocks().into_iter().collect::<BTreeSet<_>>();
        blocks.insert(anchor);
        blocks.into_iter().collect()
    }

    fn rendered_loop_edges(&self, anchor: u64, loop_body_blocks: &[u64]) -> (Vec<u64>, Vec<u64>) {
        let body = loop_body_blocks.iter().copied().collect::<BTreeSet<_>>();
        let mut latches = BTreeSet::new();
        let mut exits = BTreeSet::new();
        for block in &body {
            for succ in self.func.successors(*block) {
                if succ == anchor {
                    latches.insert(*block);
                }
                if !body.contains(&succ) {
                    exits.insert(succ);
                }
            }
        }
        (latches.into_iter().collect(), exits.into_iter().collect())
    }

    /// Structure the function's control flow.
    #[cfg(test)]
    pub(crate) fn structure(&mut self) -> ControlFlowStructureResult<CStmt> {
        self.structure_with_regions().map(SealedStructuredBody::into_stmt)
    }

    /// Structure the function and retain exact lexical occurrence identity.
    pub(crate) fn structure_with_regions(
        &mut self,
    ) -> ControlFlowStructureResult<SealedStructuredBody> {
        let symbols = &self.fold_ctx.symbols;
        let stmt = self.structure_preserving_render_proof_identity_marked()?;
        // A refusal that does not say what it refused reads as a function with no body
        if let Some(reason) = self.safety_reason.clone() {
            return seal_structured_body(CStmt::structured_region(
                StructuredRegionMarker::unsealed(
                    self.func.entry,
                    StructuredRegionKind::FunctionBody,
                ),
                CStmt::comment(format!(
                    "r2dec residual: {}",
                    crate::sanitize_comment_text(&reason)
                )),
            ))
            .map_err(ControlFlowStructureError::from);
        }
        // Post-process: flatten, simplify loops, remove redundant control flow.
        seal_structured_body(Self::cleanup(symbols, stmt)).map_err(ControlFlowStructureError::from)
    }

    fn structure_preserving_render_proof_identity_marked(
        &mut self,
    ) -> ControlFlowStructureResult<CStmt> {
        self.retain_region_markers = true;
        let stmt = self.structure_preserving_render_proof_identity_impl();
        self.retain_region_markers = false;
        stmt
    }

    fn structure_preserving_render_proof_identity_impl(
        &mut self,
    ) -> ControlFlowStructureResult<CStmt> {
        self.reset_safety_budget();
        self.control_render_proofs.clear();
        self.active_domains = vec![RenderedBlockDomain::default()];
        self.rendered_block_domains.clear();
        self.emitted_labels.clear();
        self.structured_region_blocks.clear();
        self.transfer_target_domains.clear();
        if self.region_analyzer.is_none() {
            self.region_analyzer = Some(RegionAnalyzer::new(self.func));
        }
        let region = if let Some(analyzer) = self.region_analyzer.as_mut() {
            let region = if let Some(control) = self.control {
                match analyzer.analyze_controlled() {
                    Ok(region) => region,
                    Err(reason) => {
                        self.stop_reason
                            .set(Some(DecompileExecutionStop::new(control.phase(), reason)));
                        Region::Irreducible {
                            entry: self.func.entry,
                            blocks: Vec::new(),
                        }
                    }
                }
            } else {
                analyzer.analyze()
            };
            if self.stop_reason.get().is_none()
                && let Some(reason) = analyzer.analysis_reason()
            {
                self.safety_reason = Some(reason.to_string());
            }
            region
        } else {
            self.safety_reason = Some("missing region analyzer".to_string());
            Region::Irreducible {
                entry: self.func.entry,
                blocks: self.func.block_addrs().to_vec(),
            }
        };
        self.structured_region_blocks = region.blocks().into_iter().collect();
        self.shared_joins = self.collect_shared_joins()?;
        // The jumps into a shared join need its label, and the jump back out
        // needs its successor's. Both have to exist before anything is written,
        // because a block already written can no longer be given one.
        for join in self.shared_joins.clone() {
            self.ensure_label(join);
        }
        let stmt = self.structure_region(&region)?;
        let stmt = self.append_shared_joins(stmt)?;
        let stmt = self.append_deferred_shared_exits(stmt)?;
        self.validate_rendered_block_domain_coverage();
        if self.safety_reason.is_some() {
            return Ok(CStmt::Empty);
        }
        Ok(if self.retain_region_markers {
            CStmt::structured_region(
                StructuredRegionMarker::unsealed(
                    self.func.entry,
                    StructuredRegionKind::FunctionBody,
                ),
                stmt,
            )
        } else {
            stmt
        })
    }

    /// Structure a region into C statements.
    fn structure_region(&mut self, region: &Region) -> ControlFlowStructureResult<CStmt> {
        if !self.poll() || !self.consume_safety_budget(1) {
            return Ok(CStmt::Empty);
        }
        let inherited_domains = self.active_domains.clone();
        if let Some(domains) = self.transfer_target_domains.remove(&region.entry()) {
            self.certify_transfer_domain_join(region.entry(), domains);
        }
        let stmt = self.structure_region_in_active_domains(region)?;
        self.active_domains = inherited_domains;
        if !self.retain_region_markers || matches!(stmt.unobserved(), CStmt::Empty) {
            Ok(stmt)
        } else {
            Ok(CStmt::structured_region(
                StructuredRegionMarker::unsealed(region.entry(), kind_of(region)),
                stmt,
            ))
        }
    }

    fn certify_transfer_domain_join(
        &mut self,
        block_addr: u64,
        incoming: Vec<RenderedBlockDomain>,
    ) {
        let mut alternatives = self.active_domains.clone();
        alternatives.extend(incoming);
        Self::normalize_rendered_domains(&mut alternatives);
        let Some(source) = self
            .fold_ctx
            .control_facts()
            .and_then(|facts| facts.control_domain_for_block(block_addr))
            .cloned()
        else {
            self.safety_reason = Some(format!(
                "missing source control domain for transfer join at 0x{block_addr:x}"
            ));
            return;
        };
        if !source.complete {
            self.safety_reason = Some(format!(
                "incomplete source control domain for transfer join at 0x{block_addr:x}"
            ));
            return;
        }
        if alternatives.iter().any(|alternative| {
            !self.rendered_loop_domain_matches_source(block_addr, &source.loops, &alternative.loops)
        }) {
            self.safety_reason = Some(format!(
                "loop-domain mismatch for transfer join at 0x{block_addr:x}"
            ));
            return;
        }
        let occurrence = RenderedBlockOccurrence {
            alternatives: alternatives.clone(),
        };
        match self.rendered_branch_occurrences_cover_source(block_addr, &[occurrence]) {
            Ok(true) => {
                self.active_domains = vec![RenderedBlockDomain {
                    guards: source.guards,
                    loops: source.loops,
                }];
            }
            Ok(false) => {
                self.safety_reason = Some(format!(
                    "control-domain coverage mismatch for transfer join at 0x{block_addr:x}: source guards {:?}; rendered guard alternatives {:?}",
                    source.guards,
                    alternatives
                        .iter()
                        .map(|alternative| alternative.guards.clone())
                        .collect::<Vec<_>>()
                ));
            }
            Err(reason) => {
                if self.stop_reason.get().is_none() {
                    self.safety_reason = Some(format!(
                        "control-domain coverage proof failed for transfer join at 0x{block_addr:x}: {reason}"
                    ));
                }
            }
        }
    }

    fn structure_region_in_active_domains(
        &mut self,
        region: &Region,
    ) -> ControlFlowStructureResult<CStmt> {
        Ok(match region {
            Region::Block(addr) => self.structure_block(*addr)?,
            Region::Sequence(regions) => {
                let mut stmts = Vec::with_capacity(regions.len());
                for (index, region) in regions.iter().enumerate() {
                    let deferred_merge = Self::sequence_owned_merge(regions, index);
                    if let Some(merge) = deferred_merge {
                        self.deferred_merge_blocks.push(merge);
                    }
                    let stmt = self.structure_region(region)?;
                    if let Some(merge) = deferred_merge {
                        debug_assert_eq!(self.deferred_merge_blocks.pop(), Some(merge));
                    }
                    if !matches!(stmt, CStmt::Empty) {
                        stmts.push(stmt);
                    }
                }
                if stmts.is_empty() {
                    CStmt::Empty
                } else if stmts.len() == 1 {
                    stmts.into_iter().next().unwrap()
                } else {
                    CStmt::Block(stmts)
                }
            }
            Region::IfThenElse {
                cond_block,
                then_region,
                else_region,
                merge_block,
            } => {
                let merge_owned_by_ancestor =
                    merge_block.is_some_and(|merge| self.deferred_merge_blocks.contains(&merge));
                // A speculative attempt must leave no trace when it declines,
                // deferrals included: it structures a subtree, and a real
                // structuring of that same subtree nested inside it observes
                // whatever it left on the stack. `murmur3_32` loses its return
                // that way.
                let deferred_before = self.deferred_merge_blocks.len();
                if !merge_owned_by_ancestor
                    && let Some(rewritten) = self.try_structure_if_else_with_slot_merge_returns(
                        *cond_block,
                        then_region,
                        else_region.as_deref(),
                        *merge_block,
                    )?
                {
                    return Ok(rewritten);
                }
                if !merge_owned_by_ancestor
                    && let Some(rewritten) = self.try_structure_if_else_with_register_merge_returns(
                        *cond_block,
                        then_region,
                        else_region.as_deref(),
                        *merge_block,
                    )?
                {
                    return Ok(rewritten);
                }
                if let Some(rewritten) = self.try_structure_guarded_switch_with_default(
                    *cond_block,
                    then_region,
                    else_region.as_deref(),
                    *merge_block,
                )? {
                    return Ok(rewritten);
                }
                self.deferred_merge_blocks.truncate(deferred_before);
                let (cond, predicate, condition_value) =
                    self.get_branch_condition_with_predicate(*cond_block);
                let Some(mut cond) = cond else {
                    let mut prefix = self.structure_block_prefix_stmts(*cond_block)?;
                    prefix.push(CStmt::comment(format!(
                        "r2dec residual: unresolved branch condition at 0x{cond_block:x}"
                    )));
                    return Ok(if prefix.len() == 1 {
                        prefix.into_iter().next().unwrap_or(CStmt::Empty)
                    } else {
                        CStmt::Block(prefix)
                    });
                };
                if else_region.is_none()
                    && let Some(merge_addr) = merge_block
                    && self.single_arm_if_needs_condition_inversion(
                        *cond_block,
                        then_region.entry(),
                        *merge_addr,
                    )
                {
                    cond = Self::negate_condition(cond);
                }
                self.record_branch_render_proof(*cond_block, predicate, condition_value);

                if let Some(merge) = merge_block {
                    self.deferred_merge_blocks.push(*merge);
                }
                let then_stmt = self.structure_branch_region(*cond_block, then_region)?;
                let else_stmt = match else_region.as_ref() {
                    Some(region) => Some(self.structure_branch_region(*cond_block, region)?),
                    None => None,
                };
                if let Some(merge) = merge_block {
                    debug_assert_eq!(self.deferred_merge_blocks.pop(), Some(*merge));
                }
                let branches_terminate = else_stmt.as_ref().is_some_and(|else_stmt| {
                    Self::stmt_guarantees_termination(&then_stmt)
                        && Self::stmt_guarantees_termination(else_stmt)
                });
                let if_stmt = self.observe_control_ownership(*cond_block,
                    CStmt::if_stmt(cond, then_stmt, else_stmt),
                );
                let mut prefix = self.structure_block_prefix_stmts(*cond_block)?;
                prefix.push(if_stmt);
                if let Some(merge_addr) = merge_block
                    && !branches_terminate
                    && !merge_owned_by_ancestor
                {
                    Self::append_stmt_body_flat(&mut prefix, self.structure_block(*merge_addr)?);
                }
                if prefix.len() == 1 {
                    prefix.into_iter().next().unwrap_or(CStmt::Empty)
                } else {
                    CStmt::Block(prefix)
                }
            }
            Region::WhileLoop { header, body } => {
                let (cond, predicate, condition_value) =
                    self.get_branch_condition_with_predicate(*header);
                let Some(mut cond) = cond else {
                    return Ok(CStmt::Block(vec![CStmt::comment(format!(
                        "r2dec residual: unresolved loop condition at 0x{header:x}"
                    ))]));
                };
                if self.loop_needs_condition_inversion(*header, body) {
                    cond = Self::negate_condition(cond);
                }
                self.record_loop_render_proof(*header, predicate, condition_value, body);

                let loop_id = None;

                let outer_domains = self.active_domains.clone();
                if let Some(loop_id) = loop_id {
                    self.push_active_loop(loop_id);
                }
                let prefix = self.structure_block_prefix_stmts(*header)?;
                let cond = match Self::combine_loop_condition_prefix(prefix, cond) {
                    Ok(cond) => cond,
                    Err(reason) => {
                        self.safety_reason = Some(format!(
                            "loop header 0x{header:x} effects cannot be preserved: {reason}"
                        ));
                        self.active_domains = outer_domains;
                        return Ok(CStmt::Empty);
                    }
                };
                let body_stmt = Self::strip_trailing_continue(self.structure_loop_body(body)?);
                self.active_domains = outer_domains;
                self.observe_control_ownership(*header, CStmt::while_loop(cond, body_stmt))
            }
            Region::DoWhileLoop { body, cond_block } => {
                let (cond, predicate, condition_value) =
                    self.get_branch_condition_with_predicate(*cond_block);
                let Some(mut cond) = cond else {
                    return Ok(CStmt::Block(vec![CStmt::comment(format!(
                        "r2dec residual: unresolved loop condition at 0x{cond_block:x}"
                    ))]));
                };
                if self.loop_needs_condition_inversion(*cond_block, body) {
                    cond = Self::negate_condition(cond);
                }
                let anchor = body.entry();
                self.record_loop_render_proof(anchor, predicate, condition_value, body);

                let loop_id = None;

                let outer_domains = self.active_domains.clone();
                if let Some(loop_id) = loop_id {
                    self.push_active_loop(loop_id);
                }
                let cond_owned_by_body = Self::region_owns_block_emission(body, *cond_block);
                if !cond_owned_by_body {
                    self.deferred_merge_blocks.push(*cond_block);
                }
                let mut body_stmt =
                    Self::strip_trailing_latch_marker(self.structure_loop_body(body)?);
                if !cond_owned_by_body {
                    debug_assert_eq!(self.deferred_merge_blocks.pop(), Some(*cond_block));
                    let mut stmts = Self::stmt_into_vec(body_stmt);
                    Self::append_stmt_body_flat(&mut stmts, self.structure_block(*cond_block)?);
                    body_stmt = Self::stmt_from_vec(stmts);
                }
                self.active_domains = outer_domains;
                self.observe_control_ownership(
                    *cond_block,
                    CStmt::DoWhile {
                    body: Box::new(body_stmt),
                    cond,
                },
                )
            }
            Region::MultiExit { head, exits } => {
                self.safety_reason = Some(format!(
                    "structured region at 0x{:x} has unlowered exits {:?}",
                    head.entry(),
                    exits
                ));
                CStmt::Empty
            }
            Region::Transfer {
                loop_header,
                target,
                kind,
                ..
            } if *kind == RegionTransferKind::Continue && target == loop_header => CStmt::Continue,
            Region::Transfer {
                loop_header,
                target,
                kind,
                ..
            } if *kind == RegionTransferKind::Exit
                && self
                    .region_analyzer
                    .as_ref()
                    .and_then(|analyzer| analyzer.get_loop_fallthrough(*loop_header))
                    == Some(*target) =>
            {
                CStmt::Break
            }
            Region::Transfer {
                kind: RegionTransferKind::Latch,
                ..
            } => CStmt::Empty,
            Region::Transfer {
                loop_header,
                source,
                target,
                kind,
            } => {
                let transfer_path_reason = if *kind == RegionTransferKind::Exit {
                    match self.transparent_transfer_path(*target) {
                        Ok(path) => {
                            let lowered_target = *path
                                .last()
                                .expect("transparent transfer paths are never empty");
                            // The blocks walked over do nothing but pass control
                            // along, and the jump written here is what they do.
                            // Nothing else will emit them, so without saying so
                            // they read as blocks the body left out.
                            for addr in &path {
                                self.fold_ctx.folded_blocks.borrow_mut().insert(*addr);
                            }
                            let label = self.ensure_label(lowered_target);
                            if !self.record_transfer_target_domain(*loop_header, lowered_target) {
                                return Ok(CStmt::Empty);
                            }
                            return Ok(CStmt::Goto(label));
                        }
                        Err(reason) => {
                            // An exit that runs into blocks no region claimed has
                            // nowhere to jump to, but it does have somewhere to
                            // go: the blocks themselves. Rendering them where the
                            // exit happens says what the exit does rather than
                            // refusing the whole function for want of a label,
                            // and the walk takes only blocks this edge alone
                            // reaches, so nothing is duplicated or reordered.
                            // The exit runs into a block several edges reach.
                            // It cannot go here, but it can go once after the
                            // body, with every exit saying what it brought and
                            // jumping to it.
                            if !self.structured_region_blocks.contains(target)
                                && self.func.predecessors(*target).len() > 1
                                && let Some(writes) =
                                    self.shared_exit_merge_writes(*target, *source)?
                            {
                                let label = self.ensure_label(*target);
                                self.deferred_shared_exits
                                    .entry(*target)
                                    .or_default()
                                    .insert(*source);
                                if !self.record_transfer_target_domain(*loop_header, *target) {
                                    return Ok(CStmt::Empty);
                                }
                                if writes.is_empty() {
                                    return Ok(CStmt::Goto(label));
                                }
                                let mut stmts = writes;
                                stmts.push(CStmt::Goto(label));
                                return Ok(CStmt::Block(stmts));
                            }
                            match self.exit_continuation_stmt(*target) {
                                Ok(stmt) => return Ok(stmt),
                                Err(ExitContinuationError::Structure(error)) => return Err(error),
                                // Two walks refused this edge: the one looking
                                // for a label and the one trying to render the
                                // blocks instead. The second went further, so
                                // it is the one with something to say about why
                                // the exit could not be lowered.
                                Err(ExitContinuationError::Placement(chain_reason)) => Some(match chain_reason {
                                    Some(chain_reason) => chain_reason,
                                    None => reason,
                                }),
                            }
                        }
                    }
                } else {
                    None
                };
                self.safety_reason = Some(match transfer_path_reason {
                    Some(reason) => format!(
                        "unlowered {:?} edge 0x{:x} -> 0x{:x} in loop 0x{:x}: {reason}",
                        kind, source, target, loop_header
                    ),
                    None => format!(
                        "unlowered {:?} edge 0x{:x} -> 0x{:x} in loop 0x{:x}",
                        kind, source, target, loop_header
                    ),
                });
                CStmt::Empty
            }
            Region::Switch {
                switch_block,
                cases,
                default,
                merge_block,
            } => {
                self.structure_switch_region(*switch_block, cases, default.as_deref(), *merge_block)?
            }
            Region::Irreducible { entry, blocks } => self.structure_irreducible(*entry, blocks)?,
        })
    }

    fn structure_branch_region(
        &mut self,
        pred_block: u64,
        region: &Region,
    ) -> ControlFlowStructureResult<CStmt> {
        let direct_successor = self.func.successors(pred_block).contains(&region.entry());
        if direct_successor {
            self.structure_region_from_predecessor(region, pred_block)
        } else {
            self.structure_region(region)
        }
    }

    fn structure_region_from_predecessor(
        &mut self,
        region: &Region,
        pred_block: u64,
    ) -> ControlFlowStructureResult<CStmt> {
        match region {
            Region::Block(addr) => self.structure_block_from_predecessor(*addr, pred_block),
            _ => self.structure_region(region),
        }
    }

    fn structure_block_from_predecessor(
        &mut self,
        addr: u64,
        pred_block: u64,
    ) -> ControlFlowStructureResult<CStmt> {
        // A branch that runs into the merge its own `if` deferred must not print
        // it: the `if` prints it once the branches are done. Printing it here as
        // well renders the same statements twice, and the copy inside the branch
        // reads names the copy after it declares -- murmur3 at arm64 -O1.
        if self.deferred_merge_blocks.contains(&addr) {
            return Ok(CStmt::Empty);
        }
        let stmt = self.structure_block(addr)?;
        if !self.block_allows_predecessor_return_register_rewrite(addr) {
            return Ok(stmt);
        }
        let Some((expr, proof_block, proof_op, proof_value)) =
            self.return_register_candidate_for_merge_predecessor(addr, pred_block)?
        else {
            return Ok(stmt);
        };
        if let Some(rewritten) = self.rewrite_trailing_return_with_merged_expr(&stmt, &expr) {
            Ok(self.observe_return_value_ownership(
                rewritten,
                proof_block,
                proof_op,
                proof_value,
            ))
        } else {
            Ok(stmt)
        }
    }

    fn block_allows_predecessor_return_register_rewrite(&self, addr: u64) -> bool {
        let Some(block) = self.func.get_block(addr) else {
            return false;
        };
        block.ops.iter().all(|op| {
            op.dst().is_none_or(|dst| {
                !self
                    .fold_ctx
                    .inputs
                    .arch
                    .is_return_register_name(&dst.name.to_ascii_lowercase())
            })
        })
    }

    fn return_register_candidate_for_merge_predecessor(
        &self,
        merge_addr: u64,
        pred_addr: u64,
    ) -> ControlFlowStructureResult<Option<(CExpr, u64, usize, ValueId)>> {
        if !self.block_allows_predecessor_return_register_rewrite(merge_addr) {
            return Ok(None);
        }
        let candidate = self
            .fold_ctx
            .merged_return_register_candidate_for_block_predecessor_with_proof(
                merge_addr, pred_addr,
            )?;
        match candidate {
            Some(candidate) => Ok(Some(candidate)),
            None => self
                .fold_ctx
                .predecessor_return_register_candidate_with_proof(pred_addr)
                .map_err(ControlFlowStructureError::from),
        }
    }

    /// Get the switch expression from a block.
    fn get_switch_expression(&mut self, addr: u64) -> Option<(CExpr, Option<ValueId>)> {
        let switch_addr = self.unique_switch_block().unwrap_or(addr);
        let block = self.func.get_block(switch_addr)?;

        if let Some((expr, selector)) = self
            .fold_ctx
            .resolve_switch_expr_for_block_with_selector(switch_addr)
        {
            return Some((expr, selector));
        }

        if let Some(cond) = self.get_branch_condition(switch_addr)
            && let Some(expr) = Self::selector_expr_from_condition(&cond)
        {
            return Some((expr, None));
        }
        if let Some(expr) = self.selector_expr_from_switch_predecessors(switch_addr) {
            return Some((expr, None));
        }

        // Look for an indirect branch which typically has the switch variable
        for op in &block.ops {
            if let Some(expr) = self.fold_ctx.extract_switch_expr(op) {
                return Some((expr, None));
            }
        }

        None
    }

    fn unique_switch_block(&self) -> Option<u64> {
        let mut switch_blocks = self.func.cfg().block_addrs().filter(|addr| {
            self.func
                .cfg()
                .get_block(*addr)
                .is_some_and(|block| matches!(block.terminator, BlockTerminator::Switch { .. }))
        });
        let block = switch_blocks.next()?;
        if switch_blocks.next().is_some() {
            return None;
        }
        Some(block)
    }

    fn selector_expr_from_switch_predecessors(&mut self, addr: u64) -> Option<CExpr> {
        let mut candidates = self
            .func
            .predecessors(addr)
            .into_iter()
            .filter_map(|pred| {
                self.get_branch_condition(pred)
                    .and_then(|cond| Self::selector_expr_from_condition(&cond))
            })
            .collect::<Vec<_>>();
        candidates.dedup();
        (candidates.len() == 1).then(|| candidates.pop()).flatten()
    }

    fn selector_expr_from_condition(cond: &CExpr) -> Option<CExpr> {
        match cond {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::selector_expr_from_condition(inner)
            }
            CExpr::Binary {
                op:
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge,
                left,
                right,
            } => {
                if matches!(left.as_ref(), CExpr::IntLit(_) | CExpr::UIntLit(_)) {
                    return Some((**right).clone());
                }
                if matches!(right.as_ref(), CExpr::IntLit(_) | CExpr::UIntLit(_)) {
                    return Some((**left).clone());
                }
                None
            }
            _ => None,
        }
    }

    fn structure_switch_region(
        &mut self,
        switch_block: u64,
        cases: &[(Option<u64>, Box<Region>)],
        default: Option<&Region>,
        merge_block: Option<u64>,
    ) -> ControlFlowStructureResult<CStmt> {
        let merge_owned_by_ancestor =
            merge_block.is_some_and(|merge| self.deferred_merge_blocks.contains(&merge));
        let Some((switch_expr, switch_selector)) = self.get_switch_expression(switch_block) else {
            return Ok(CStmt::Block(vec![CStmt::comment(format!(
                "r2dec residual: unresolved switch selector at 0x{switch_block:x}"
            ))]));
        };
        if cases.iter().any(|(case_value, _)| case_value.is_none()) {
            return Ok(CStmt::Block(vec![CStmt::comment(format!(
                "r2dec residual: unresolved switch case value at 0x{switch_block:x}"
            ))]));
        }
        self.record_switch_render_proof(switch_block, switch_selector, cases, default);

        if let Some(merge) = merge_block {
            self.deferred_merge_blocks.push(merge);
        }
        // A case that leaves into another case's entry falls through, and C says
        // that by *omitting* the break. Ending every case with one turned
        // murmur3's tail -- `case 3` into `case 2` into `case 1`, each adding a
        // byte of the remainder -- into three alternatives, so only one byte of
        // the tail was ever mixed in.
        let case_entries: std::collections::HashSet<u64> = cases
            .iter()
            .filter(|(value, _)| value.is_some())
            .map(|(_, region)| region.entry())
            .collect();
        let mut switch_cases = Vec::new();
        for (case_value, case_region) in cases {
            let outer_domains = self.active_domains.clone();
            let Some(case_value) = case_value else {
                continue;
            };
            let value_expr = CExpr::IntLit(*case_value as i64);
            let region_blocks: std::collections::HashSet<u64> =
                case_region.blocks().into_iter().collect();
            let falls_through = region_blocks.iter().any(|block| {
                self.func
                    .successors(*block)
                    .iter()
                    .any(|succ| case_entries.contains(succ) && !region_blocks.contains(succ))
            });
            let case_stmt = self.structure_region(case_region)?;
            self.active_domains = outer_domains;
            let body = if falls_through {
                vec![case_stmt]
            } else {
                vec![case_stmt, CStmt::Break]
            };
            switch_cases.push(crate::ast::SwitchCase {
                value: value_expr,
                body,
            });
        }

        let default_body = if let Some(region) = default {
            let outer_domains = self.active_domains.clone();
            let stmt = self.structure_region(region)?;
            self.active_domains = outer_domains;
            Some(vec![stmt])
        } else {
            None
        };
        if let Some(merge) = merge_block {
            debug_assert_eq!(self.deferred_merge_blocks.pop(), Some(merge));
        }
        let switch_stmt = self.observe_control_ownership(
            switch_block,
            CStmt::Switch {
            expr: switch_expr,
            cases: switch_cases,
            default: default_body,
        },
        );

        let mut prefix = self.structure_block_prefix_stmts(switch_block)?;
        prefix.push(switch_stmt);
        if let Some(merge_addr) = merge_block.filter(|_| !merge_owned_by_ancestor) {
            Self::append_stmt_body_flat(&mut prefix, self.structure_block(merge_addr)?);
        }
        if prefix.len() == 1 {
            Ok(prefix.into_iter().next().unwrap_or(CStmt::Empty))
        } else {
            Ok(CStmt::Block(prefix))
        }
    }

    fn single_arm_if_needs_condition_inversion(
        &self,
        cond_block: u64,
        then_entry: u64,
        merge_block: u64,
    ) -> bool {
        let Some((true_target, false_target)) = self.resolve_conditional_targets(cond_block) else {
            return false;
        };

        true_target == merge_block && false_target == then_entry
    }

    fn loop_needs_condition_inversion(&self, cond_block: u64, body: &Region) -> bool {
        let Some((true_target, false_target)) = self.resolve_conditional_targets(cond_block) else {
            return false;
        };
        let body_blocks = body.blocks();
        !body_blocks.contains(&true_target) && body_blocks.contains(&false_target)
    }

    fn resolve_conditional_targets(&self, cond_block: u64) -> Option<(u64, u64)> {
        let succs = self.func.successors(cond_block);
        if succs.len() != 2 {
            return None;
        }

        let mut true_target = None;
        let mut false_target = None;
        for succ in succs {
            match self.func.edge_type(cond_block, succ) {
                Some(CFGEdge::True) => true_target = Some(succ),
                Some(CFGEdge::False) => false_target = Some(succ),
                _ => {}
            }
        }

        Some((true_target?, false_target?))
    }

    /// Structure a single basic block.
    /// Write the blocks that several exits share, once, after the body.
    ///
    /// A block more than one edge reaches cannot go at either of them: put it
    /// at one and the other cannot reach it, put it at both and it runs twice.
    /// Written once at the end with a label, every exit jumps to it and it runs
    /// where all of them agree it does.
    fn append_deferred_shared_exits(
        &mut self,
        stmt: CStmt,
    ) -> ControlFlowStructureResult<CStmt> {
        if self.deferred_shared_exits.is_empty() {
            return Ok(stmt);
        }
        let deferred = std::mem::take(&mut self.deferred_shared_exits);
        let mut stmts = Vec::new();
        Self::append_stmt_body_flat(&mut stmts, stmt);
        for (target, jumped_from) in deferred {
            let predecessors = self
                .func
                .predecessors(target)
                .into_iter()
                .collect::<BTreeSet<_>>();
            // Nothing may fall into it: an edge left as ordinary control flow
            // expects the block where it already sits.
            if !predecessors.is_subset(&jumped_from) {
                self.safety_reason = Some(format!(
                    "shared exit block 0x{target:x} is also reached by control this did not lower"
                ));
                return Ok(CStmt::Empty);
            }
            // The head is reached by several edges -- that is why it is here
            // rather than at one of them -- so the walk starts past it.
            let (chain, rejoin) = match self.shared_exit_chain(target) {
                Ok(walked) => walked,
                Err(reason) => {
                    self.safety_reason = Some(reason.unwrap_or_else(|| {
                        format!("shared exit block 0x{target:x} could not be placed")
                    }));
                    return Ok(CStmt::Empty);
                }
            };
            for addr in &chain {
                self.structured_region_blocks.insert(*addr);
            }
            let mut exit_stmts = Vec::new();
            for addr in &chain {
                let block_stmt = self.structure_block(*addr)?;
                if !matches!(block_stmt, CStmt::Empty) {
                    exit_stmts.push(block_stmt);
                }
            }
            if let Some(rejoin) = rejoin {
                let label = self.ensure_label(rejoin);
                exit_stmts.push(CStmt::Goto(label));
            }
            if !exit_stmts.is_empty() {
                let exit_stmt = if exit_stmts.len() == 1 {
                    exit_stmts.remove(0)
                } else {
                    CStmt::Block(exit_stmts)
                };
                stmts.push(if self.retain_region_markers {
                    CStmt::structured_region(
                        StructuredRegionMarker::unsealed(
                            target,
                            StructuredRegionKind::Synthetic(
                                SyntheticRegionKind::DeferredSharedExit,
                            ),
                        ),
                        exit_stmt,
                    )
                } else {
                    exit_stmt
                });
            }
        }
        Ok(match stmts.len() {
            0 => CStmt::Empty,
            1 => stmts.remove(0),
            _ => CStmt::Block(stmts),
        })
    }

    /// The blocks a shared exit runs through, starting at the shared head.
    ///
    /// Everything after the head is the ordinary single-edge case, so only the
    /// head is taken on trust, and only because several exits jumping to it is
    /// what put it here.
    fn shared_exit_chain(&self, target: u64) -> Result<(Vec<u64>, Option<u64>), Option<String>> {
        if self.func.get_block(target).is_none() {
            return Err(None);
        }
        let mut chain = vec![target];
        match self.func.successors(target).as_slice() {
            [] => Ok((chain, None)),
            [next] => {
                if self.structured_region_blocks.contains(next) {
                    return Ok((chain, Some(*next)));
                }
                let (rest, rejoin) = self.exit_continuation_chain(*next)?;
                chain.extend(rest);
                Ok((chain, rejoin))
            }
            _ => Err(Some(format!(
                "shared exit block 0x{target:x} branches where the exits join"
            ))),
        }
    }

    /// What one exit has to write before jumping to a block it shares.
    ///
    /// The block merges values, and which value arrives depends on which edge
    /// came in. Moving the block out from under its edges loses that, unless
    /// each edge says on its way out which value it brought. That is what the
    /// merge meant, written where the edge is.
    ///
    /// Nothing is written if either side renders as a carrier rather than a
    /// name the function declares, because an assignment between carriers says
    /// nothing a reader can follow.
    fn shared_exit_merge_writes(
        &self,
        target: u64,
        source: u64,
    ) -> ControlFlowStructureResult<Option<Vec<CStmt>>> {
        let Some(block) = self.func.get_block(target) else {
            return Ok(None);
        };
        let mut writes = Vec::new();
        for phi in &block.phis {
            let Some(value) = phi
                .sources
                .iter()
                .find_map(|(pred, value)| (*pred == source).then_some(value))
            else {
                return Ok(None);
            };
            if crate::analysis::utils::is_temporary_or_constant_name(&phi.dst.display_name()) {
                return Ok(None);
            }
            let Some(target_value) = self.fold_ctx.prepared_value_id_for_var(&phi.dst) else {
                return Ok(None);
            };
            let Some(source_value) = self.fold_ctx.prepared_value_id_for_var(value) else {
                return Ok(None);
            };
            let target_expr = self
                .fold_ctx
                .planned_value_expr(target_value)
                .map_err(|_| OpLoweringRefusal::MissingProgramVariableAuthorization)?;
            let source_expr = self
                .fold_ctx
                .planned_value_expr(source_value)
                .map_err(|_| OpLoweringRefusal::MissingProgramVariableAuthorization)?;
            if target_expr.transparently_eq(&source_expr) {
                continue;
            }
            writes.push(CStmt::Expr(CExpr::assign(target_expr, source_expr)));
        }
        Ok(Some(writes))
    }

    /// The blocks several branches converge on that no region claimed.
    ///
    /// A region tree says if/else with a merge every path runs through. A block
    /// many branches reach but some path steps around is not that, so the tree
    /// has nowhere to put it and it goes unwritten. It is still part of the
    /// function, and every edge reaching it agrees where it runs, so it can be
    /// written once behind a label like any other shared arrival.
    fn collect_shared_joins(&self) -> ControlFlowStructureResult<BTreeSet<u64>> {
        let mut joins = BTreeSet::new();
        for addr in self.func.block_addrs().to_vec() {
            if self.structured_region_blocks.contains(&addr) || self.block_is_proven_dead(addr) {
                continue;
            }
            let predecessors = self.func.predecessors(addr);
            if predecessors.len() < 2 {
                continue;
            }
            // A jump can only be written where the block doing the jumping is.
            if !predecessors
                .iter()
                .all(|pred| self.structured_region_blocks.contains(pred))
            {
                continue;
            }
            // The join has to end where it is. A join that carries on needs a
            // label on whatever it carries on to, and a block the structuring
            // already wrote cannot be given one afterwards, so the jump out
            // would name something the function never spells.
            if !self.func.successors(addr).is_empty() {
                continue;
            }
            // A join merges whatever each edge brought, so every edge has to be
            // able to say which value that was on its way in.
            let mut all_edges_render = true;
            for pred in &predecessors {
                if self.shared_exit_merge_writes(addr, *pred)?.is_none() {
                    all_edges_render = false;
                    break;
                }
            }
            if !all_edges_render {
                continue;
            }
            joins.insert(addr);
        }
        Ok(joins)
    }

    /// Write the shared joins after the body, each behind its label.
    fn append_shared_joins(&mut self, stmt: CStmt) -> ControlFlowStructureResult<CStmt> {
        if self.shared_joins.is_empty() {
            return Ok(stmt);
        }
        let joins = std::mem::take(&mut self.shared_joins);
        let mut stmts = Vec::new();
        Self::append_stmt_body_flat(&mut stmts, stmt);
        for addr in joins {
            self.structured_region_blocks.insert(addr);
            let mut block_stmts = vec![CStmt::Label(self.ensure_label(addr))];
            if let Some(block) = self.func.get_block(addr) {
                block_stmts.extend(self.folded_block_stmts(block, addr)?);
            }
            let join_stmt = CStmt::Block(block_stmts);
            stmts.push(if self.retain_region_markers {
                CStmt::structured_region(
                    StructuredRegionMarker::unsealed(
                        addr,
                        StructuredRegionKind::Synthetic(SyntheticRegionKind::SharedJoin),
                    ),
                    join_stmt,
                )
            } else {
                join_stmt
            });
        }
        Ok(match stmts.len() {
            0 => CStmt::Empty,
            1 => stmts.remove(0),
            _ => CStmt::Block(stmts),
        })
    }

    fn structure_block(&mut self, addr: u64) -> ControlFlowStructureResult<CStmt> {
        if self.is_unresolved_indirect_dispatch_block(addr) {
            // Where this block goes was never recovered, so there is no shape
            // to give it. Saying that is still saying something, and rendering
            // nothing at all leaves the block silently out of a body that
            // otherwise claims to cover the function.
            self.fold_ctx.folded_blocks.borrow_mut().insert(addr);
            let mut stmts = Vec::new();
            if let Some(label) = self.take_block_label(addr) {
                stmts.push(CStmt::Label(label));
            }
            if let Some(block) = self.func.get_block(addr) {
                stmts.extend(self.folded_block_stmts(block, addr)?);
            }
            stmts.push(CStmt::comment(
                "indirect branch target unresolved".to_string(),
            ));
            return Ok(match stmts.len() {
                1 => stmts.remove(0),
                _ => CStmt::Block(stmts),
            });
        }
        let block = match self.func.get_block(addr) {
            Some(b) => b,
            None => return Ok(CStmt::Empty),
        };

        let mut stmts = Vec::new();

        // Add label if needed
        if let Some(label) = self.take_block_label(addr) {
            stmts.push(CStmt::Label(label));
        }

        // Convert operations to statements
        stmts.extend(self.folded_block_stmts(block, addr)?);

        // Control leaving here for a shared join has no structure to carry it,
        // so it says what it brought and where it goes.
        if let [next] = self.func.successors(addr).as_slice()
            && self.shared_joins.contains(next)
        {
            if let Some(writes) = self.shared_exit_merge_writes(*next, addr)? {
                stmts.extend(writes);
            }
            let label = self.ensure_label(*next);
            stmts.push(CStmt::Goto(label));
        }

        if stmts.is_empty() {
            Ok(CStmt::Empty)
        } else if stmts.len() == 1 {
            Ok(stmts.remove(0))
        } else {
            Ok(CStmt::Block(stmts))
        }
    }

    /// Structure a loop body region, flattening block sequences into a single
    /// statement list to avoid nested `{ ...; break; } { ...; continue; }` braces.
    fn structure_loop_body(&mut self, body: &Region) -> ControlFlowStructureResult<CStmt> {
        // If the body is a Sequence of Blocks, flatten all block statements
        // into one continuous list instead of wrapping each in CStmt::Block.
        if let Region::Sequence(regions) = body {
            let mut all_stmts = Vec::new();
            for (index, region) in regions.iter().enumerate() {
                let deferred_merge = Self::sequence_owned_merge(regions, index);
                if let Some(merge) = deferred_merge {
                    self.deferred_merge_blocks.push(merge);
                }
                match region {
                    Region::Block(addr) => {
                        // Inline the block's statements directly
                        self.structure_block_stmts_into(*addr, &mut all_stmts)?;
                    }
                    _ => {
                        // Non-block region: structure normally and append
                        let stmt = self.structure_region(region)?;
                        if !matches!(stmt, CStmt::Empty) {
                            all_stmts.push(stmt);
                        }
                    }
                }
                if let Some(merge) = deferred_merge {
                    debug_assert_eq!(self.deferred_merge_blocks.pop(), Some(merge));
                }
            }
            if all_stmts.is_empty() {
                Ok(CStmt::Empty)
            } else if all_stmts.len() == 1 {
                Ok(all_stmts.remove(0))
            } else {
                Ok(CStmt::Block(all_stmts))
            }
        } else {
            self.structure_region(body)
        }
    }

    fn sequence_owned_merge(regions: &[Region], index: usize) -> Option<u64> {
        let region = regions.get(index)?;
        let next = regions.get(index + 1)?;
        match region {
            Region::IfThenElse {
                merge_block: Some(merge),
                ..
            }
            | Region::Switch {
                merge_block: Some(merge),
                ..
            } if next.entry() == *merge => Some(*merge),
            _ => None,
        }
    }

    fn region_owns_block_emission(region: &Region, addr: u64) -> bool {
        match region {
            Region::Block(block) => *block == addr,
            Region::Sequence(regions) => regions
                .iter()
                .any(|region| Self::region_owns_block_emission(region, addr)),
            Region::IfThenElse {
                cond_block,
                then_region,
                else_region,
                ..
            } => {
                *cond_block == addr
                    || Self::region_owns_block_emission(then_region, addr)
                    || else_region
                        .as_deref()
                        .is_some_and(|region| Self::region_owns_block_emission(region, addr))
            }
            Region::WhileLoop { header, body } => {
                *header == addr || Self::region_owns_block_emission(body, addr)
            }
            Region::DoWhileLoop { body, cond_block } => {
                *cond_block == addr || Self::region_owns_block_emission(body, addr)
            }
            Region::MultiExit { head, .. } => Self::region_owns_block_emission(head, addr),
            Region::Transfer { .. } => false,
            Region::Switch {
                switch_block,
                cases,
                default,
                ..
            } => {
                *switch_block == addr
                    || cases
                        .iter()
                        .any(|(_, region)| Self::region_owns_block_emission(region, addr))
                    || default
                        .as_deref()
                        .is_some_and(|region| Self::region_owns_block_emission(region, addr))
            }
            Region::Irreducible { blocks, .. } => blocks.contains(&addr),
        }
    }

    /// Emit statements for a block directly into an existing statement list
    /// (without wrapping in CStmt::Block). Used for loop body flattening.
    fn structure_block_stmts_into(
        &mut self,
        addr: u64,
        stmts: &mut Vec<CStmt>,
    ) -> ControlFlowStructureResult<()> {
        if self.is_unresolved_indirect_dispatch_block(addr) {
            return Ok(());
        }
        let block = match self.func.get_block(addr) {
            Some(b) => b,
            None => return Ok(()),
        };

        // Add label if needed
        if let Some(label) = self.take_block_label(addr) {
            stmts.push(CStmt::Label(label));
        }

        // Convert operations to statements
        stmts.extend(self.folded_block_stmts(block, addr)?);
        Ok(())
    }

    fn ensure_label(&mut self, addr: u64) -> String {
        if let Some(label) = self.labels.get(&addr) {
            return label.clone();
        }
        let label = format!("L{}", self.label_counter);
        self.label_counter += 1;
        self.labels.insert(addr, label.clone());
        label
    }

    fn take_block_label(&mut self, addr: u64) -> Option<String> {
        let label = self.labels.get(&addr)?.clone();
        self.emitted_labels.insert(addr).then_some(label)
    }

    /// Render the blocks an unlabelled loop exit runs into, in order.
    ///
    /// The exit needs a label to jump to and the structuring never gave these
    /// blocks one, because no region claimed them. They are still reached only
    /// through this edge, so where they run is where the exit goes, and putting
    /// them here loses nothing and invents nothing. The walk stops as soon as
    /// that stops holding: a block another edge also reaches, or one that merges
    /// values, or one that branches, could not be placed here without saying
    /// something the function does not do.
    fn exit_continuation_stmt(&mut self, target: u64) -> Result<CStmt, ExitContinuationError> {
        let (chain, rejoin) = self
            .exit_continuation_chain(target)
            .map_err(ExitContinuationError::Placement)?;
        for addr in &chain {
            self.structured_region_blocks.insert(*addr);
        }
        let mut stmts = Vec::new();
        for addr in &chain {
            let stmt = self.structure_block(*addr)?;
            if !matches!(stmt, CStmt::Empty) {
                stmts.push(stmt);
            }
        }
        // The walk ran back into ground the structuring already covers, so the
        // exit does what these blocks do and then carries on there.
        if let Some(rejoin) = rejoin {
            let label = self.ensure_label(rejoin);
            stmts.push(CStmt::Goto(label));
        } else if let Some(branch) = chain.last().copied()
            && let BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } = self.branch_targets(branch)
        {
            // The last block asks a question, so the exit goes two ways from
            // here and each way is an exit continuation in its own right.
            let then_stmt = self.exit_continuation_stmt(true_target)?;
            let else_stmt = self.exit_continuation_stmt(false_target)?;
            let (cond, predicate, condition_value) =
                self.get_branch_condition_with_predicate(branch);
            let Some(cond) = cond else {
                return Err(ExitContinuationError::Placement(Some(format!(
                    "exit continuation block 0x{branch:x} branches on nothing this can read"
                ))));
            };
            self.record_branch_render_proof(branch, predicate, condition_value);
            stmts.push(self.observe_control_ownership(
                branch,
                CStmt::If {
                cond,
                then_body: Box::new(then_stmt),
                else_body: Some(Box::new(else_stmt)),
            },
            ));
        }
        Ok(match stmts.len() {
            0 => CStmt::Empty,
            1 => stmts.remove(0),
            _ => CStmt::Block(stmts),
        })
    }

    /// The blocks an unlabelled exit runs through, or nothing if placing them
    /// at the exit would not say what the function does.
    /// How a block leaves, when the structuring never claimed it.
    fn branch_targets(&self, addr: u64) -> BlockTerminator {
        self.func
            .cfg()
            .get_block(addr)
            .map(|block| block.terminator.clone())
            .unwrap_or(BlockTerminator::IndirectBranch)
    }

    fn exit_continuation_chain(
        &self,
        target: u64,
    ) -> Result<(Vec<u64>, Option<u64>), Option<String>> {
        let mut chain = Vec::new();
        let mut seen = BTreeSet::new();
        let mut current = target;
        loop {
            if !self.poll() {
                return Err(None);
            }
            // Reaching ground the structuring covers ends the walk with
            // somewhere to jump to, which is what the exit needed all along.
            if self.structured_region_blocks.contains(&current) {
                return match chain.is_empty() {
                    true => Err(None),
                    false => Ok((chain, Some(current))),
                };
            }
            if !seen.insert(current) {
                return Err(None);
            }
            let Some(block) = self.func.get_block(current) else {
                return Err(None);
            };
            // A block another edge also reaches is not this exit's to place:
            // putting it here would say it runs once per edge.
            let predecessors = self.func.predecessors(current).len();
            if predecessors != 1 {
                return Err(Some(format!(
                    "exit continuation block 0x{current:x} is reached by {predecessors} edges"
                )));
            }
            if !block.phis.is_empty() {
                return Err(Some(format!(
                    "exit continuation block 0x{current:x} owns {} phi node(s) behind one edge",
                    block.phis.len()
                )));
            }
            chain.push(current);
            match self.func.successors(current).as_slice() {
                // Nothing follows, so the exit ends here and the chain is whole.
                [] => return Ok((chain, None)),
                [next] => current = *next,
                // A branch splits the exit in two, and each way is an exit
                // continuation of its own. The block itself is rendered by the
                // caller, which knows the condition it branches on.
                _ => return Ok((chain, None)),
            }
        }
    }

    fn transparent_transfer_path(&self, start: u64) -> Result<Vec<u64>, String> {
        let mut path = Vec::new();
        let mut seen = BTreeSet::new();
        let mut current = start;
        loop {
            if !self.poll() {
                return Err("transparent transfer search stopped".to_string());
            }
            if !seen.insert(current) {
                return Err(format!(
                    "transparent forwarder path cycles at 0x{current:x}"
                ));
            }
            path.push(current);
            if self.structured_region_blocks.contains(&current) {
                return Ok(path);
            }
            let Some(block) = self.func.get_block(current) else {
                return Err(format!("missing forwarder block 0x{current:x}"));
            };
            if !block.phis.is_empty() {
                return Err(format!(
                    "forwarder block 0x{current:x} owns {} phi node(s)",
                    block.phis.len()
                ));
            }
            let successors = self.func.successors(current);
            let [next] = successors.as_slice() else {
                return Err(format!(
                    "forwarder block 0x{current:x} has {} successors",
                    successors.len()
                ));
            };
            if !block.ops.iter().enumerate().all(|(op_idx, op)| {
                self.is_transparent_branch_forwarder_op(op)
                    || self.is_materialized_phi_edge_copy(current, op_idx, *next)
            }) {
                return Err(format!(
                    "forwarder block 0x{current:x} owns live non-phi SSA effects"
                ));
            }
            current = *next;
        }
    }

    fn record_transfer_target_domain(&mut self, _loop_header: u64, _target: u64) -> bool {
        true
    }

    fn push_active_loop(&mut self, loop_id: LoopId) {
        for domain in &mut self.active_domains {
            domain.loops.push(loop_id);
        }
        Self::normalize_rendered_domains(&mut self.active_domains);
    }

    fn normalize_rendered_domains(domains: &mut Vec<RenderedBlockDomain>) {
        for domain in domains.iter_mut() {
            domain.guards.sort();
            domain.guards.dedup();
            domain.loops.sort_unstable();
            domain.loops.dedup();
        }
        let mut unique = Vec::new();
        for domain in domains.drain(..) {
            if !unique.contains(&domain) {
                unique.push(domain);
            }
        }
        *domains = unique;
    }

    /// Emit side-effecting statements for a block without labels or loop markers.
    /// Used for condition/switch header blocks where statements must appear before
    /// the structured control-flow construct.
    fn structure_block_prefix_stmts(
        &mut self,
        addr: u64,
    ) -> ControlFlowStructureResult<Vec<CStmt>> {
        if self.is_unresolved_indirect_dispatch_block(addr) {
            return Ok(Vec::new());
        }
        let block = match self.func.get_block(addr) {
            Some(b) => b,
            None => return Ok(Vec::new()),
        };

        let mut stmts = Vec::new();
        if let Some(label) = self.take_block_label(addr) {
            stmts.push(CStmt::Label(label));
        }
        stmts.extend(self.folded_block_stmts(block, addr)?);
        Ok(stmts)
    }

    fn combine_loop_condition_prefix(
        prefix: Vec<CStmt>,
        condition: CExpr,
    ) -> Result<CExpr, String> {
        let mut expressions = Vec::with_capacity(prefix.len().saturating_add(1));
        for stmt in prefix {
            if let Some(expr) = Self::loop_condition_prefix_expr(stmt)? {
                expressions.push(expr);
            }
        }
        if expressions.is_empty() {
            return Ok(condition);
        }
        expressions.push(condition);
        Ok(CExpr::Comma(expressions))
    }

    fn loop_condition_prefix_expr(stmt: CStmt) -> Result<Option<CExpr>, String> {
        match stmt {
            CStmt::Observed { id, stmt } => Self::loop_condition_prefix_expr(*stmt)
                .map(|expr| expr.map(|expr| CExpr::observed(id, expr))),
            CStmt::Expr(expr) => Ok(Some(expr)),
            CStmt::Empty => Ok(None),
            CStmt::Comment(reason) => Err(reason),
            other => Err(format!("unsupported condition-prefix statement {other:?}")),
        }
    }

    fn folded_block_stmts(
        &mut self,
        block: &r2ssa::FunctionSSABlock,
        addr: u64,
    ) -> ControlFlowStructureResult<Vec<CStmt>> {
        self.fold_ctx.folded_blocks.borrow_mut().insert(addr);
        let stmts = if let Some(folded) = self.folded_block_cache.get(&addr) {
            if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
                eprintln!("FOLDCACHE hit block={addr:#x} stmts={}", folded.stmts.len());
            }
            self.fold_ctx
                .clone_cached_render_occurrence(&folded.stmts)
        } else {
            let stmts = self.fold_ctx.fold_block(block, addr)?;
            if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
                eprintln!("FOLDCACHE miss block={addr:#x} stmts={}", stmts.len());
            }
            self.folded_block_cache.insert(
                addr,
                FoldedBlock {
                    stmts: stmts.clone(),
                },
            );
            stmts
        };
        self.validate_certified_block_domain(addr, &stmts);
        if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
            eprintln!("FOLDED block={addr:#x} stmts={}", stmts.len());
            let table = self.fold_ctx.symbols.borrow();
            for (index, stmt) in stmts.iter().enumerate() {
                let mut ids = std::collections::HashSet::new();
                crate::collect_stmt_var_names(std::slice::from_ref(stmt))
                    .into_iter()
                    .for_each(|id| {
                        ids.insert(id);
                    });
                let target = match stmt {
                    CStmt::Expr(CExpr::Binary {
                        op: crate::ast::BinaryOp::Assign,
                        left,
                        ..
                    }) => match left.as_ref() {
                        CExpr::Var(id) => table.name(*id).to_string(),
                        other => format!("{other:?}").chars().take(30).collect(),
                    },
                    other => format!("{other:?}").chars().take(30).collect(),
                };
                let mut names = ids
                    .into_iter()
                    .map(|id| table.name(id).to_string())
                    .collect::<Vec<_>>();
                names.sort();
                eprintln!("  FSTMT {index} target={target} reads={names:?}");
            }
        }
        Ok(stmts)
    }

    fn validate_certified_block_domain(&mut self, _block_addr: u64, _stmts: &[CStmt]) {}

    /// Every block the source has must be covered by the region that was structured.
    ///
    /// A block no region covers is never folded, so whatever it did is absent from
    /// the output with nothing saying so. That is how a loop's trailing return used
    /// to disappear, and it stayed quiet because the proof note counts markers in
    /// the body rather than blocks in the source. Structuring that lost a block is
    /// not safe structuring, so it says so here rather than rendering the rest as
    /// though the function were complete.
    /// Whether the proof shows nothing can reach this block.
    ///
    /// A branch whose arm cannot be entered is not a branch the program takes, and
    /// rendering it says the program chooses between two things when it does not.
    fn block_is_proven_dead(&self, addr: u64) -> bool {
        self.proven_dead_blocks
            .get_or_init(|| {
                let blocks = self.func.blocks().cloned().collect::<Vec<_>>();
                r2ssa::proven::unreachable_blocks(&blocks, self.func.cfg())
                    .into_iter()
                    .map(|block| block.addr)
                    .collect()
            })
            .contains(&addr)
    }

    fn validate_rendered_block_domain_coverage(&mut self) {
        if self.safety_reason.is_some() {
            return;
        }
        let source = self.func.block_addrs();
        // Ask what the rendering wrote, not what the regions laid claim to. A
        // region tree covering every block says the shape was found, not that
        // the shape reached the page, and a lowering that returns early leaves
        // a claimed block unwritten with nothing to show it went missing. A
        // block folded into its predecessors counts as written, because it is.
        let rendered = self.fold_ctx.folded_blocks.borrow().clone();
        // A block the proof shows nothing can reach owes the output nothing, so
        // not rendering it is the right answer rather than a gap in coverage.
        let missing = source
            .iter()
            .copied()
            .filter(|addr| !rendered.contains(addr) && !self.block_is_proven_dead(*addr))
            .collect::<Vec<_>>();
        let Some(first) = missing.first().copied() else {
            return;
        };
        self.safety_reason = Some(format!(
            "structuring covered {} of {} source blocks, leaving 0x{first:x} and {} others unrendered",
            rendered.len(),
            source.len(),
            missing.len().saturating_sub(1)
        ));
    }

    fn rendered_loop_domain_matches_source(
        &self,
        block_addr: u64,
        source_loops: &[LoopId],
        rendered_loops: &[LoopId],
    ) -> bool {
        if rendered_loops == source_loops {
            return true;
        }
        let Some(block) = self.func.cfg().get_block(block_addr) else {
            return false;
        };
        if !matches!(block.terminator, r2ssa::BlockTerminator::Return) {
            return false;
        }
        let source = source_loops.iter().copied().collect::<BTreeSet<_>>();
        let rendered = rendered_loops.iter().copied().collect::<BTreeSet<_>>();
        if !source.is_subset(&rendered) {
            return false;
        }
        let Some(facts) = self.fold_ctx.control_facts() else {
            return false;
        };
        rendered.difference(&source).all(|loop_id| {
            facts
                .loops
                .get(loop_id)
                .is_some_and(|loop_fact| loop_fact.exits.contains(&block_addr))
        })
    }

    fn rendered_branch_occurrences_cover_source(
        &mut self,
        block_addr: u64,
        occurrences: &[RenderedBlockOccurrence],
    ) -> Result<bool, String> {
        let facts = self
            .fold_ctx
            .control_facts()
            .ok_or_else(|| "missing canonical control facts".to_string())?;
        // A predicate in a completed inner loop is evaluated once per dynamic
        // iteration, not once per static CFG node. Project those predicates out
        // before comparing path coverage at a block outside that loop. Loop
        // membership still proves execution multiplicity separately.
        let varying_predicates = facts
            .branch_predicates
            .values()
            .filter(|predicate| {
                facts.loops.values().any(|loop_fact| {
                    loop_fact.body.contains(&predicate.block_addr)
                        && !loop_fact.body.contains(&block_addr)
                })
            })
            .map(|predicate| predicate.id)
            .collect::<BTreeSet<_>>();
        if !self.poll() {
            return Err("control coverage stopped".to_string());
        }
        let mut bdd = ControlBdd::new_with_optional_control(
            self.safety_budget_remaining,
            self.control,
            Some(&self.stop_reason),
        );
        let mut rendered_formula = BDD_FALSE;
        for occurrence in occurrences {
            if !self.poll() {
                return Err("control coverage stopped".to_string());
            }
            let mut occurrence_formula = BDD_FALSE;
            for alternative in &occurrence.alternatives {
                if !self.poll() {
                    return Err("control coverage stopped".to_string());
                }
                let mut alternative_formula = BDD_TRUE;
                for guard in &alternative.guards {
                    if !self.poll() {
                        return Err("control coverage stopped".to_string());
                    }
                    let ControlGuard::Branch { predicate, truth } = guard else {
                        return Err(
                            "aggregate proof currently requires branch-only guards".to_string()
                        );
                    };
                    let literal = bdd.variable(*predicate, *truth)?;
                    alternative_formula = bdd.and(alternative_formula, literal)?;
                }
                occurrence_formula = bdd.or(occurrence_formula, alternative_formula)?;
            }
            occurrence_formula =
                bdd.exists(occurrence_formula, &varying_predicates, &mut HashMap::new())?;
            if bdd.and(rendered_formula, occurrence_formula)? != BDD_FALSE {
                return Ok(false);
            }
            rendered_formula = bdd.or(rendered_formula, occurrence_formula)?;
        }

        let mut reach = self
            .func
            .block_addrs()
            .iter()
            .copied()
            .map(|addr| (addr, BDD_FALSE))
            .collect::<BTreeMap<_, _>>();
        reach.insert(self.func.entry, BDD_TRUE);
        let mut worklist = VecDeque::from([self.func.entry]);
        let mut queued = BTreeSet::from([self.func.entry]);
        while let Some(from) = worklist.pop_front() {
            if !self.poll() {
                return Err("control coverage stopped".to_string());
            }
            queued.remove(&from);
            let from_formula = reach.get(&from).copied().unwrap_or(BDD_FALSE);
            for to in self.func.successors(from) {
                if !self.poll() {
                    return Err("control coverage stopped".to_string());
                }
                let edge_formula = if self.func.successors(from).len() <= 1 {
                    BDD_TRUE
                } else {
                    let predicate = facts
                        .branch_for_block(from)
                        .ok_or_else(|| format!("non-branch multi-successor block 0x{from:x}"))?;
                    let truth = if predicate.true_target == to {
                        true
                    } else if predicate.false_target == to {
                        false
                    } else {
                        return Err(format!(
                            "successor 0x{to:x} is absent from predicate at 0x{from:x}"
                        ));
                    };
                    bdd.variable(predicate.id, truth)?
                };
                let candidate = bdd.and(from_formula, edge_formula)?;
                let previous = reach.get(&to).copied().unwrap_or(BDD_FALSE);
                let joined = bdd.or(previous, candidate)?;
                if joined != previous {
                    reach.insert(to, joined);
                    if queued.insert(to) {
                        worklist.push_back(to);
                    }
                }
            }
        }
        let source_formula = bdd.exists(
            reach.get(&block_addr).copied().unwrap_or(BDD_FALSE),
            &varying_predicates,
            &mut HashMap::new(),
        )?;
        let created_nodes = bdd.created_nodes();
        drop(bdd);
        if !self.consume_safety_budget(created_nodes) {
            return Err("control coverage exhausted structuring safety budget".to_string());
        }
        Ok(source_formula == rendered_formula)
    }

    /// Get the branch condition from a block.
    fn get_branch_condition(&mut self, addr: u64) -> Option<CExpr> {
        self.get_branch_condition_with_predicate(addr).0
    }

    fn get_branch_condition_with_predicate(
        &mut self,
        addr: u64,
    ) -> (Option<CExpr>, Option<PredicateId>, Option<ValueId>) {
        let block = match self.func.get_block(addr) {
            Some(b) => b,
            None => return (None, None, None),
        };
        let predicate = self
            .fold_ctx
            .control_facts()
            .and_then(|facts| facts.branch_for_block(addr))
            .map(|predicate| (predicate.id, predicate.condition));
        let predicate_id = predicate.map(|(id, _)| id);
        let condition_value = predicate.map(|(_, value)| value);

        if let Some(cond) = self.fold_ctx.extract_condition_from_block(block) {
            if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
                let table = self.fold_ctx.symbols.borrow();
                let mut ids = std::collections::HashSet::new();
                crate::collect_expr_var_names(&cond, &mut ids);
                let names = ids
                    .into_iter()
                    .map(|id| format!("{id:?}={}", table.name(id)))
                    .collect::<Vec<_>>();
                eprintln!("BRANCHCOND block={addr:#x} cond={cond:?} names={names:?}");
            }
            return (Some(cond), predicate_id, condition_value);
        }

        // Look for a conditional branch in the block
        for op in &block.ops {
            if let Some(cond) = self.fold_ctx.extract_condition(op) {
                return (Some(cond), predicate_id, condition_value);
            }
        }

        (None, predicate_id, condition_value)
    }

    /// Structure an irreducible region using gotos.
    fn structure_irreducible(
        &mut self,
        entry: u64,
        blocks: &[u64],
    ) -> ControlFlowStructureResult<CStmt> {
        // Assign labels to all blocks
        for &addr in blocks {
            if !self.labels.contains_key(&addr) {
                let label = format!("L{}", self.label_counter);
                self.label_counter += 1;
                self.labels.insert(addr, label);
            }
        }

        // Start with the entry block
        let mut stmts = vec![self.structure_block(entry)?];

        // Add remaining blocks with gotos
        for &addr in blocks {
            if addr != entry {
                stmts.push(self.structure_block(addr)?);
            }
        }

        Ok(CStmt::Block(stmts))
    }

    // TODO: gen_label() and goto_block() are reserved for future use when
    // implementing more complex control flow restructuring (e.g., irreducible
    // regions that require goto-based fallback). Currently, structure_irreducible()
    // handles labels directly. These helpers may be useful for:
    // - Break/continue in nested loops
    // - Early returns from deeply nested code
    // - Complex switch fallthrough patterns

    /// Post-process a statement tree to clean up control flow artifacts.
    ///
    /// Applies three transformations recursively:
    /// - Fix A: Flatten single-element `Block`s.
    /// - Fix B: Remove trailing `continue` in loop bodies (implicit) and
    ///   trailing `break` in single-exit if-then inside loops.
    /// - Fix C: Convert `do { if (c) break; ... } while(1)` to `while(!c) { ... }`.
    pub(crate) fn cleanup(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: CStmt,
    ) -> CStmt {
        // Recurse first, then simplify
        let stmt = Self::cleanup_recurse(symbols, stmt);
        Self::flatten(stmt)
    }

    /// Recursively clean up children first, then apply local simplifications.
    fn cleanup_recurse(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: CStmt,
    ) -> CStmt {
        match stmt {
            CStmt::StructuredRegion { marker, stmt } => {
                let cleaned = Self::cleanup_recurse(symbols, *stmt);
                if matches!(cleaned.unobserved(), CStmt::Empty) {
                    CStmt::Empty
                } else {
                    CStmt::structured_region(marker, cleaned)
                }
            }
            CStmt::Observed { id, stmt } => {
                CStmt::observed(id, Self::cleanup_recurse(symbols, *stmt))
            }
            CStmt::Block(stmts) => {
                let cleaned = stmts
                    .into_iter()
                    .map(|x| Self::cleanup_recurse(symbols, x))
                    .filter(|s| !matches!(s.unobserved(), CStmt::Empty))
                    .collect();
                let cleaned = Self::rewrite_block_tail_guard_clauses(cleaned);
                let cleaned = Self::rewrite_guarded_switch_if_else(cleaned);
                let cleaned = Self::rewrite_continue_tail_merges(symbols, cleaned);
                let cleaned = Self::truncate_dead_straight_line_tail(cleaned);
                let rewritten = Self::rewrite_block_loops_to_for(symbols, cleaned);
                if rewritten.is_empty() {
                    CStmt::Empty
                } else if rewritten.len() == 1 {
                    rewritten.into_iter().next().unwrap()
                } else {
                    CStmt::Block(rewritten)
                }
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                let cond = Self::normalize_condition_addr_artifacts(symbols, cond);
                let then_body = Box::new(Self::cleanup_recurse(symbols, *then_body));
                let else_body = else_body
                    .map(|e| Box::new(Self::cleanup_recurse(symbols, *e)))
                    .and_then(|e| (!matches!(e.unobserved(), CStmt::Empty)).then_some(e));
                let stmt = CStmt::If {
                    cond,
                    then_body,
                    else_body,
                };
                let stmt = Self::rewrite_constant_condition_stmt(stmt);
                let stmt = Self::rewrite_if_short_circuit(stmt);
                let stmt = Self::rewrite_if_condition_inversion(stmt);
                let stmt = Self::rewrite_empty_if_bodies(stmt);
                let stmt = Self::rewrite_if_return_ternary(stmt);
                Self::rewrite_guarded_switch_with_trailing_return(stmt)
            }
            CStmt::While { cond, body } => {
                let cond = Self::normalize_condition_addr_artifacts(symbols, cond);
                let body = Self::strip_trailing_continue(Self::cleanup_recurse(symbols, *body));
                CStmt::While {
                    cond,
                    body: Box::new(body),
                }
            }
            CStmt::DoWhile { body, cond } => {
                let body = Self::strip_trailing_continue(Self::cleanup_recurse(symbols, *body));
                let cond = Self::normalize_condition_addr_artifacts(symbols, cond);
                // Fix C: do { if (c) break; rest } while(1) -> while(!c) { rest }
                Self::try_convert_do_while_to_while(body, cond)
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                let cond = cond.map(|x| Self::normalize_condition_addr_artifacts(symbols, x));
                let body = Self::strip_trailing_continue(Self::cleanup_recurse(symbols, *body));
                let body = update
                    .as_ref()
                    .map(|update| Self::strip_trailing_for_update(symbols, body.clone(), update))
                    .unwrap_or(body);
                let body = Self::remove_dead_generated_artifact_assignments(symbols, body);
                CStmt::For {
                    init,
                    cond,
                    update,
                    body: Box::new(body),
                }
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                let cases = cases
                    .into_iter()
                    .map(|c| crate::ast::SwitchCase {
                        value: c.value,
                        body: Self::cleanup_switch_body(symbols, c.body),
                    })
                    .collect();
                let default = default.map(|b| Self::cleanup_switch_body(symbols, b));
                CStmt::Switch {
                    expr,
                    cases,
                    default,
                }
            }
            CStmt::Expr(expr) => CStmt::Expr(Self::rewrite_compound_assignment_expr(symbols, expr)),
            other => other,
        }
    }

    fn cleanup_switch_body(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmts: Vec<CStmt>,
    ) -> Vec<CStmt> {
        let cleaned = stmts
            .into_iter()
            .map(|x| Self::cleanup_recurse(symbols, x))
            .filter(|stmt| !matches!(stmt.unobserved(), CStmt::Empty))
            .collect();
        Self::truncate_dead_straight_line_tail(cleaned)
    }

    fn rewrite_compound_assignment_expr(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, expr: CExpr,
    ) -> CExpr {
        if let CExpr::Observed { id, expr } = expr {
            return CExpr::observed(id, Self::rewrite_compound_assignment_expr(symbols, *expr));
        }
        let CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        } = expr
        else {
            return expr;
        };

        let CExpr::Var(target_name) = left.as_ref() else {
            return CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            };
        };

        let Some((op, retained, eliminated)) = Self::compound_assignment_parts(
            symbols,
            &crate::symbol::spelling(symbols, *target_name),
            right.as_ref(),
        ) else {
            return CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            };
        };

        let left = crate::ast::carry_outer_expr_observations(eliminated, *left);
        let rewritten = CExpr::Binary {
            op,
            left: Box::new(left),
            right: Box::new(retained.clone()),
        };
        crate::ast::carry_outer_expr_observations(right.as_ref(), rewritten)
    }

    fn compound_assignment_parts<'b>(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        target_name: &str,
        rhs: &'b CExpr,
    ) -> Option<(BinaryOp, &'b CExpr, &'b CExpr)> {
        let CExpr::Binary { op, left, right } = rhs.unobserved() else {
            return None;
        };
        let compound_op = Self::compound_assignment_op(*op)?;

        if Self::expr_is_var_named_of(symbols, left, target_name)
            && crate::fold::op_lower::expr_is_side_effect_free(right)
        {
            return Some((compound_op, right, left));
        }

        if Self::binary_op_is_commutative_for_compound(*op)
            && Self::expr_is_var_named_of(symbols, right, target_name)
            && crate::fold::op_lower::expr_is_side_effect_free(left)
        {
            return Some((compound_op, left, right));
        }

        None
    }

    fn compound_assignment_rhs_of(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        target_name: &str,
        rhs: &CExpr,
    ) -> Option<(BinaryOp, CExpr)> {
        let semantic = rhs.clone_without_render_observations();
        let (op, retained, _) = Self::compound_assignment_parts(symbols, target_name, &semantic)?;
        Some((op, retained.clone()))
    }

    fn compound_assignment_op(op: BinaryOp) -> Option<BinaryOp> {
        match op {
            BinaryOp::Add => Some(BinaryOp::AddAssign),
            BinaryOp::Sub => Some(BinaryOp::SubAssign),
            BinaryOp::Mul => Some(BinaryOp::MulAssign),
            BinaryOp::Div => Some(BinaryOp::DivAssign),
            BinaryOp::Mod => Some(BinaryOp::ModAssign),
            BinaryOp::BitAnd => Some(BinaryOp::BitAndAssign),
            BinaryOp::BitOr => Some(BinaryOp::BitOrAssign),
            BinaryOp::BitXor => Some(BinaryOp::BitXorAssign),
            BinaryOp::Shl => Some(BinaryOp::ShlAssign),
            BinaryOp::Shr => Some(BinaryOp::ShrAssign),
            _ => None,
        }
    }

    fn binary_op_is_commutative_for_compound(op: BinaryOp) -> bool {
        matches!(
            op,
            BinaryOp::Add | BinaryOp::Mul | BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor
        )
    }

    fn expr_is_var_named_of(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        expr: &CExpr,
        target_name: &str,
    ) -> bool {
        matches!(expr.unobserved(), CExpr::Var(name) if &*crate::symbol::spelling(symbols, *name) == target_name)
    }

    fn rewrite_constant_condition_stmt(stmt: CStmt) -> CStmt {
        match stmt {
            CStmt::If {
                cond,
                then_body,
                else_body: _,
            } if Self::is_const_true_expr(&cond) => *then_body,
            CStmt::If {
                cond,
                then_body: _,
                else_body,
            } if Self::is_const_false_expr(&cond) => {
                else_body.map(|stmt| *stmt).unwrap_or(CStmt::Empty)
            }
            other => other,
        }
    }

    fn is_const_true_expr(expr: &CExpr) -> bool {
        matches!(expr.unobserved(), CExpr::IntLit(1) | CExpr::UIntLit(1))
    }

    fn is_const_false_expr(expr: &CExpr) -> bool {
        matches!(expr.unobserved(), CExpr::IntLit(0) | CExpr::UIntLit(0))
    }

    fn rewrite_if_short_circuit(stmt: CStmt) -> CStmt {
        let (semantic, observations) = stmt.into_semantic_with_observations();
        let CStmt::If {
            cond,
            then_body,
            else_body,
        } = semantic
        else {
            return observations.reapply(semantic);
        };

        // if (a) { if (b) { T } } -> if (a && b) { T }
        if else_body.is_none()
            && let CStmt::If {
                cond: inner_cond,
                then_body: inner_then,
                else_body: None,
            } = then_body.unobserved()
        {
            let rewritten = CStmt::If {
                cond: CExpr::binary(BinaryOp::And, cond, inner_cond.clone()),
                then_body: inner_then.clone(),
                else_body: None,
            };
            return observations.reapply(rewritten);
        }

        // if (a) { T } else if (b) { T } -> if (a || b) { T }
        if let Some(else_stmt) = else_body.as_deref()
            && let CStmt::If {
            cond: right_cond,
            then_body: right_then,
            else_body: None,
        } = else_stmt.unobserved()
            && Self::stmt_transparently_eq(then_body.as_ref(), right_then)
        {
            let rewritten = CStmt::If {
                cond: CExpr::binary(BinaryOp::Or, cond, right_cond.clone()),
                then_body: then_body.clone(),
                else_body: None,
            };
            return observations.reapply(rewritten);
        }

        // if (a) { if (b) { T } } else { T } -> if (!a || b) { T }
        if let CStmt::If {
            cond: inner_cond,
            then_body: inner_then,
            else_body: None,
        } = then_body.unobserved()
            && let Some(outer_else) = else_body.as_deref()
            && Self::stmt_transparently_eq(outer_else, inner_then)
        {
            let rewritten = CStmt::If {
                cond: CExpr::binary(
                    BinaryOp::Or,
                    Self::negate_condition(cond),
                    inner_cond.clone(),
                ),
                then_body: inner_then.clone(),
                else_body: None,
            };
            return observations.reapply(rewritten);
        }

        // if (a) { if (b) { T } else { E } } else { E } -> if (a && b) { T } else { E }
        if let CStmt::If {
            cond: inner_cond,
            then_body: inner_then,
            else_body: Some(inner_else),
        } = then_body.unobserved()
            && let Some(outer_else) = else_body.as_deref()
            && Self::stmt_transparently_eq(outer_else, inner_else)
        {
            let rewritten = CStmt::If {
                cond: CExpr::binary(BinaryOp::And, cond, inner_cond.clone()),
                then_body: inner_then.clone(),
                else_body: Some(inner_else.clone()),
            };
            return observations.reapply(rewritten);
        }

        observations.reapply(CStmt::If {
            cond,
            then_body,
            else_body,
        })
    }

    fn rewrite_if_condition_inversion(stmt: CStmt) -> CStmt {
        let CStmt::If {
            cond,
            then_body,
            else_body: Some(else_body),
        } = stmt
        else {
            return stmt;
        };

        let then_terminator = Self::single_terminator_stmt(then_body.as_ref());
        let else_terminator = Self::single_terminator_stmt(else_body.as_ref());
        let (guard_cond, guard_terminator, hoisted_body) = match (then_terminator, else_terminator)
        {
            (Some(_), Some(_)) | (None, None) => {
                return CStmt::If {
                    cond,
                    then_body,
                    else_body: Some(else_body),
                };
            }
            (None, Some(terminator)) => (Self::negate_condition(cond), terminator, *then_body),
            (Some(terminator), None) => (cond, terminator, *else_body),
        };

        let mut rewritten = vec![CStmt::If {
            cond: guard_cond,
            then_body: Box::new(guard_terminator),
            else_body: None,
        }];
        Self::append_stmt_body_flat(&mut rewritten, hoisted_body);
        CStmt::Block(rewritten)
    }

    fn append_stmt_body_flat(out: &mut Vec<CStmt>, stmt: CStmt) {
        let (semantic, observations) = stmt.into_semantic_with_observations();
        match semantic {
            CStmt::Block(mut stmts) => {
                observations.reapply_to_unique(&mut stmts);
                out.extend(stmts);
            }
            CStmt::Empty => {}
            other => out.push(observations.reapply(other)),
        }
    }

    fn rewrite_empty_if_bodies(stmt: CStmt) -> CStmt {
        let CStmt::If {
            cond,
            then_body,
            else_body,
        } = stmt
        else {
            return stmt;
        };

        if matches!(then_body.unobserved(), CStmt::Empty) {
            return match else_body {
                Some(else_body) => CStmt::If {
                    cond: Self::negate_condition(cond),
                    then_body: else_body,
                    else_body: None,
                },
                None => CStmt::Empty,
            };
        }

        CStmt::If {
            cond,
            then_body,
            else_body,
        }
    }

    fn rewrite_if_return_ternary(stmt: CStmt) -> CStmt {
        let CStmt::If {
            cond,
            then_body,
            else_body: Some(else_body),
        } = stmt
        else {
            return stmt;
        };

        if let (Some(then_expr), Some(else_expr)) = (
            Self::single_return_expr(then_body.as_ref()),
            Self::single_return_expr(else_body.as_ref()),
        ) && Self::is_zero_guarded_division_return(&cond, &then_expr, &else_expr)
        {
            CStmt::Return(Some(CExpr::Ternary {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            }))
        } else {
            CStmt::If {
                cond,
                then_body,
                else_body: Some(else_body),
            }
        }
    }

    fn single_return_expr(stmt: &CStmt) -> Option<CExpr> {
        match stmt.unobserved() {
            CStmt::Return(Some(expr)) => Some(expr.clone()),
            CStmt::Block(stmts) if stmts.len() == 1 => Self::single_return_expr(&stmts[0]),
            _ => None,
        }
    }

    fn is_zero_guarded_division_return(cond: &CExpr, then_expr: &CExpr, else_expr: &CExpr) -> bool {
        let Some((guarded, zero_when_true)) = Self::zero_compare_operand(cond) else {
            return false;
        };
        if zero_when_true {
            Self::expr_divides_by(else_expr, guarded)
        } else {
            Self::expr_divides_by(then_expr, guarded)
        }
    }

    fn zero_compare_operand(cond: &CExpr) -> Option<(&CExpr, bool)> {
        match cond.unobserved() {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::zero_compare_operand(inner)
            }
            CExpr::Binary { op, left, right } if matches!(op, BinaryOp::Eq | BinaryOp::Ne) => {
                let zero_when_true = matches!(op, BinaryOp::Eq);
                if Self::is_zero_literal(left) {
                    return Some((right, zero_when_true));
                }
                if Self::is_zero_literal(right) {
                    return Some((left, zero_when_true));
                }
                None
            }
            _ => None,
        }
    }

    fn is_zero_literal(expr: &CExpr) -> bool {
        matches!(expr.unobserved(), CExpr::IntLit(0) | CExpr::UIntLit(0))
    }

    fn expr_divides_by(expr: &CExpr, denominator: &CExpr) -> bool {
        match expr.unobserved() {
            CExpr::Binary {
                op: BinaryOp::Div,
                right,
                ..
            } => right.transparently_eq(denominator),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::expr_divides_by(inner, denominator)
            }
            CExpr::Ternary {
                then_expr,
                else_expr,
                ..
            } => {
                Self::expr_divides_by(then_expr, denominator)
                    || Self::expr_divides_by(else_expr, denominator)
            }
            _ => false,
        }
    }

    fn rewrite_guarded_switch_with_trailing_return(stmt: CStmt) -> CStmt {
        let CStmt::If {
            cond,
            then_body,
            else_body: Some(else_body),
        } = stmt
        else {
            return stmt;
        };

        let then_branch = Self::extract_switch_with_trailing_stmt(then_body.as_ref());
        let else_branch = Self::extract_switch_with_trailing_stmt(else_body.as_ref());
        let (switch_stmt, default_stmt, trailing_stmt) = match (then_branch, else_branch) {
            (Some((switch_stmt, trailing_stmt)), None) => {
                (switch_stmt, (*else_body).clone(), trailing_stmt)
            }
            (None, Some((switch_stmt, trailing_stmt))) => {
                (switch_stmt, (*then_body).clone(), trailing_stmt)
            }
            _ => {
                return CStmt::If {
                    cond,
                    then_body,
                    else_body: Some(else_body),
                };
            }
        };

        if !matches!(switch_stmt, CStmt::Switch { default: None, .. })
            || !Self::stmt_guarantees_termination(&default_stmt)
            || trailing_stmt.as_ref().is_some_and(|stmt| {
                !matches!(
                    Self::single_terminator_stmt(stmt),
                    Some(CStmt::Return(Some(CExpr::IntLit(0) | CExpr::UIntLit(0))))
                )
            })
        {
            return CStmt::If {
                cond,
                then_body,
                else_body: Some(else_body),
            };
        }

        let CStmt::Switch { expr, cases, .. } = switch_stmt else {
            unreachable!();
        };
        let mut rewritten = vec![CStmt::Switch {
            expr,
            cases,
            default: Some(vec![default_stmt]),
        }];
        if let Some(trailing_stmt) = trailing_stmt {
            rewritten.push(trailing_stmt);
        }
        CStmt::Block(rewritten)
    }

    fn try_structure_if_else_with_slot_merge_returns(
        &mut self,
        cond_block: u64,
        then_region: &Region,
        else_region: Option<&Region>,
        merge_block: Option<u64>,
    ) -> ControlFlowStructureResult<Option<CStmt>> {
        let Some(merge_block) = merge_block else {
            return Ok(None);
        };
        let Some(else_region) = else_region else {
            return Ok(None);
        };

        let summaries = self
            .fold_ctx
            .frame_slot_merges_map()
            .values()
            .filter(|summary| summary.merge_block_addr == merge_block)
            .collect::<Vec<_>>();
        let [summary] = summaries.as_slice() else {
            return Ok(None);
        };

        let then_pred = self.unique_region_predecessor_to_merge(then_region, merge_block);
        let else_pred = self.unique_region_predecessor_to_merge(else_region, merge_block);
        let then_can_rewrite = then_pred
            .is_some_and(|pred| self.has_merged_slot_return_expr(then_region, pred, summary));
        let else_can_rewrite = else_pred
            .is_some_and(|pred| self.has_merged_slot_return_expr(else_region, pred, summary));
        if !then_can_rewrite && !else_can_rewrite {
            return Ok(None);
        }

        let control_proof_checkpoint = self.control_render_proofs.len();
        let mut then_stmt = self.structure_region(then_region)?;
        let mut else_stmt = self.structure_region(else_region)?;
        let mut rewrote_any = false;

        if then_can_rewrite
            && let Some(pred) = then_pred
            && let Some(rewritten) = self.append_merged_slot_return_if_needed(
                then_stmt.clone(),
                then_region,
                pred,
                summary,
            )?
        {
            then_stmt = rewritten;
            rewrote_any = true;
        }
        if else_can_rewrite
            && let Some(pred) = else_pred
            && let Some(rewritten) = self.append_merged_slot_return_if_needed(
                else_stmt.clone(),
                else_region,
                pred,
                summary,
            )?
        {
            else_stmt = rewritten;
            rewrote_any = true;
        }
        if !rewrote_any
            || !Self::stmt_guarantees_termination(&then_stmt)
            || !Self::stmt_guarantees_termination(&else_stmt)
        {
            self.control_render_proofs
                .truncate(control_proof_checkpoint);
            return Ok(None);
        }

        let (cond, predicate, condition_value) =
            self.get_branch_condition_with_predicate(cond_block);
        let Some(cond) = cond else {
            return Ok(None);
        };
        let if_stmt = self.observe_control_ownership(
            cond_block,
            CStmt::If {
            cond,
            then_body: Box::new(then_stmt),
            else_body: Some(Box::new(else_stmt)),
        },
        );
        self.note_merge_block_rendered_by_duplication(merge_block);
        self.record_branch_render_proof(cond_block, predicate, condition_value);
        let mut prefix = self.structure_block_prefix_stmts(cond_block)?;
        prefix.push(if_stmt);
        Ok(Some(if prefix.len() == 1 {
            prefix.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(prefix)
        }))
    }

    fn try_structure_if_else_with_register_merge_returns(
        &mut self,
        cond_block: u64,
        then_region: &Region,
        else_region: Option<&Region>,
        merge_block: Option<u64>,
    ) -> ControlFlowStructureResult<Option<CStmt>> {
        let Some(merge_block) = merge_block else {
            return Ok(None);
        };
        let Some(else_region) = else_region else {
            return Ok(None);
        };
        let then_pred = self.unique_region_predecessor_to_merge(then_region, merge_block);
        let else_pred = self.unique_region_predecessor_to_merge(else_region, merge_block);
        let mut then_can_rewrite = match then_pred {
            Some(pred) => self.has_merged_register_return_expr(merge_block, pred)?,
            None => false,
        };
        let mut else_can_rewrite = match else_pred {
            Some(pred) => self.has_merged_register_return_expr(merge_block, pred)?,
            None => false,
        };
        let control_proof_checkpoint = self.control_render_proofs.len();

        let mut then_stmt = self.structure_region(then_region)?;
        let mut else_stmt = self.structure_region(else_region)?;
        then_can_rewrite |= then_pred.is_some_and(|pred| {
            self.stmt_has_predecessor_return_register_certificate(&then_stmt, pred)
        });
        else_can_rewrite |= else_pred.is_some_and(|pred| {
            self.stmt_has_predecessor_return_register_certificate(&else_stmt, pred)
        });
        if !then_can_rewrite && !else_can_rewrite {
            self.control_render_proofs
                .truncate(control_proof_checkpoint);
            return Ok(None);
        }
        let mut rewrote_any = false;

        if then_can_rewrite
            && let Some(pred) = then_pred
            && let Some(rewritten) =
                self.append_merged_register_return_if_needed(then_stmt.clone(), merge_block, pred)?
        {
            then_stmt = rewritten;
            rewrote_any = true;
        }
        if else_can_rewrite
            && let Some(pred) = else_pred
            && let Some(rewritten) =
                self.append_merged_register_return_if_needed(else_stmt.clone(), merge_block, pred)?
        {
            else_stmt = rewritten;
            rewrote_any = true;
        }
        if !rewrote_any
            || !Self::stmt_guarantees_termination(&then_stmt)
            || !Self::stmt_guarantees_termination(&else_stmt)
        {
            self.control_render_proofs
                .truncate(control_proof_checkpoint);
            return Ok(None);
        }

        let (cond, predicate, condition_value) =
            self.get_branch_condition_with_predicate(cond_block);
        let Some(cond) = cond else {
            return Ok(None);
        };
        let if_stmt = self.observe_control_ownership(
            cond_block,
            CStmt::If {
            cond,
            then_body: Box::new(then_stmt),
            else_body: Some(Box::new(else_stmt)),
        },
        );
        self.note_merge_block_rendered_by_duplication(merge_block);
        self.record_branch_render_proof(cond_block, predicate, condition_value);

        let mut prefix = self.structure_block_prefix_stmts(cond_block)?;
        prefix.push(if_stmt);
        Ok(Some(if prefix.len() == 1 {
            prefix.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(prefix)
        }))
    }

    fn try_structure_guarded_switch_with_default(
        &mut self,
        cond_block: u64,
        then_region: &Region,
        else_region: Option<&Region>,
        merge_block: Option<u64>,
    ) -> ControlFlowStructureResult<Option<CStmt>> {
        let Some(else_region) = else_region else {
            return Ok(None);
        };
        let (switch_view, default_region) = match (
            Self::switch_region_view(then_region),
            Self::switch_region_view(else_region),
        ) {
            (Some(switch_view), None) => (switch_view, else_region),
            (None, Some(switch_view)) => (switch_view, then_region),
            _ => return Ok(None),
        };

        if self.func.switch_info(switch_view.switch_block).is_some() {
            return Ok(None);
        }
        if switch_view.default.is_some() || switch_view.cases.len() < 4 {
            return Ok(None);
        }
        if !self
            .func
            .successors(cond_block)
            .contains(&switch_view.entry_block)
        {
            return Ok(None);
        }

        let combined_merge = merge_block.or(switch_view.merge_block);
        let mut prefix = self.structure_block_prefix_stmts(cond_block)?;
        for region in switch_view.prefix_regions {
            Self::append_stmt_body_flat(&mut prefix, self.structure_region(region)?);
        }
        let switch_stmt = self.structure_switch_region(
            switch_view.switch_block,
            switch_view.cases,
            Some(default_region),
            None,
        )?;
        Self::append_stmt_body_flat(&mut prefix, switch_stmt);
        if let Some(merge_addr) = combined_merge {
            Self::append_stmt_body_flat(&mut prefix, self.structure_block(merge_addr)?);
        }
        Ok(Some(if prefix.len() == 1 {
            prefix.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(prefix)
        }))
    }

    fn switch_region_view(region: &Region) -> Option<SwitchRegionView<'_>> {
        match region {
            Region::Switch {
                switch_block,
                cases,
                default,
                merge_block,
            } => Some(SwitchRegionView {
                entry_block: *switch_block,
                switch_block: *switch_block,
                cases: cases.as_slice(),
                default: default.as_deref(),
                merge_block: *merge_block,
                prefix_regions: &[],
            }),
            Region::Sequence(regions) if !regions.is_empty() => {
                let (prefix_regions, tail) = regions.split_at(regions.len() - 1);
                let tail_region = tail.first()?;
                let mut view = Self::switch_region_view(tail_region)?;
                view.entry_block = region.entry();
                if view.prefix_regions.is_empty() {
                    view.prefix_regions = prefix_regions;
                }
                Some(view)
            }
            _ => None,
        }
    }

    fn unique_region_predecessor_to_merge(&self, region: &Region, merge_block: u64) -> Option<u64> {
        let mut candidates = region
            .blocks()
            .into_iter()
            .filter(|addr| self.func.successors(*addr).contains(&merge_block))
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            candidates = region
                .blocks()
                .into_iter()
                .filter_map(|addr| self.transparent_branch_successor_to_merge(addr, merge_block))
                .collect::<Vec<_>>();
        }
        if candidates.is_empty() {
            candidates = region
                .blocks()
                .into_iter()
                .filter_map(|addr| self.merge_predecessor_through_forwarders(addr, merge_block))
                .collect::<Vec<_>>();
        }
        candidates.sort_unstable();
        candidates.dedup();
        match candidates.as_slice() {
            [pred] => Some(*pred),
            _ => None,
        }
    }

    /// The block that actually reaches `merge_block`, following the empty
    /// branches a region may leave through.
    ///
    /// A region's own blocks do not always name the merge as a successor. A
    /// compiler will route an arm through a chain of blocks that do nothing
    /// but branch, and those belong to no arm in particular, so the arm looks
    /// as though it contributes nothing to the merge and is given no value.
    /// It contributes whatever the block at the end of that chain stores:
    /// nothing on the way there can change it, because nothing on the way
    /// there does anything.
    ///
    /// Without this the innermost arm of a nested chain of conditions was left
    /// with the other arm's value, so `unlock` returned 1 both when its last
    /// test passed and when it failed.
    fn merge_predecessor_through_forwarders(&self, addr: u64, merge_block: u64) -> Option<u64> {
        const MAX_FORWARDERS: usize = 8;
        let mut current = addr;
        for _ in 0..MAX_FORWARDERS {
            let block = self.func.get_block(current)?;
            if self.func.successors(current).contains(&merge_block) {
                return Some(current);
            }
            let successors = self.transparent_branch_successors(current, block);
            let [successor] = successors.as_slice() else {
                return None;
            };
            if !block.ops.iter().enumerate().all(|(op_idx, op)| {
                self.is_transparent_branch_forwarder_op(op)
                    || self.is_materialized_phi_edge_copy(current, op_idx, *successor)
            }) {
                return None;
            }
            if self
                .region_analyzer
                .as_ref()
                .is_some_and(|analyzer| analyzer.block_has_loop_transfer(current))
            {
                return None;
            }
            current = *successor;
        }
        None
    }

    fn transparent_branch_successor_to_merge(&self, addr: u64, merge_block: u64) -> Option<u64> {
        let block = self.func.get_block(addr)?;
        let successors = self.transparent_branch_successors(addr, block);
        let [successor] = successors.as_slice() else {
            return None;
        };
        if !block.ops.iter().enumerate().all(|(op_idx, op)| {
            self.is_transparent_branch_forwarder_op(op)
                || self.is_materialized_phi_edge_copy(addr, op_idx, *successor)
        }) {
            return None;
        }
        if self
            .region_analyzer
            .as_ref()
            .is_some_and(|analyzer| analyzer.block_has_loop_transfer(addr))
        {
            return None;
        }
        self.block_flows_to_merge(*successor, merge_block)
            .then_some(*successor)
    }

    fn is_materialized_phi_edge_copy(&self, pred_addr: u64, op_idx: usize, successor: u64) -> bool {
        self.fold_ctx
            .is_unconditional_materialized_phi_edge_copy(pred_addr, op_idx, successor)
    }

    fn is_transparent_branch_forwarder_op(&self, op: &SSAOp) -> bool {
        match op {
            SSAOp::Branch { .. } | SSAOp::Nop => true,
            // A copy with no reader is dead and therefore transparent. Any
            // copy feeding a phi or another carrier is transparent only when
            // the sealed normalization origin above identifies that exact
            // occurrence; operation shape is not proof of a transformed edge.
            SSAOp::Copy { dst, .. } => {
                self.func.find_uses(dst).is_empty()
                    && !self.func.blocks().any(|block| {
                        block.phis.iter().any(|phi| {
                            phi.dst == *dst || phi.sources.iter().any(|(_, src)| src == dst)
                        })
                    })
            }
            _ => false,
        }
    }

    fn transparent_branch_successors(
        &self,
        addr: u64,
        block: &r2ssa::FunctionSSABlock,
    ) -> Vec<u64> {
        let successors = self.func.successors(addr);
        if !successors.is_empty() {
            return successors;
        }
        let mut targets = block
            .ops
            .iter()
            .filter_map(|op| match op {
                SSAOp::Branch { target } => parse_address_from_var_name(&target.name),
                _ => None,
            })
            .collect::<Vec<_>>();
        targets.sort_unstable();
        targets.dedup();
        targets
    }

    fn block_flows_to_merge(&self, addr: u64, merge_block: u64) -> bool {
        if self.func.successors(addr).contains(&merge_block) {
            return true;
        }
        let Some(block) = self.func.get_block(addr) else {
            return false;
        };
        if block.ops.iter().any(|op| {
            matches!(
                op,
                SSAOp::Branch { target }
                    if parse_address_from_var_name(&target.name) == Some(merge_block)
            )
        }) {
            return true;
        }
        if block.addr.checked_add(u64::from(block.size)) != Some(merge_block) {
            return false;
        }
        self.func.cfg().get_block(addr).is_none_or(|cfg_block| {
            matches!(
                &cfg_block.terminator,
                BlockTerminator::Fallthrough { next } if *next == merge_block
            ) || matches!(&cfg_block.terminator, BlockTerminator::None)
        })
    }

    fn append_merged_slot_return_if_needed(
        &self,
        stmt: CStmt,
        _region: &Region,
        pred_addr: u64,
        summary: &crate::analysis::FrameSlotMergeSummary,
    ) -> ControlFlowStructureResult<Option<CStmt>> {
        let mut visited = std::collections::HashSet::new();
        let expr = summary
            .incoming
            .get(&pred_addr)
            .and_then(|value| self.fold_ctx.render_semantic_value(value, 0, &mut visited))
            .or_else(|| {
                self.fold_ctx
                    .merged_return_candidate_for_block_slot(pred_addr, summary.slot_offset)
            });
        let Some(expr) = expr else {
            return Ok(None);
        };
        // What reaches the merged slot is recorded as the SSA carrier that
        // wrote it, `x8_8`, which is a version of a machine register and not a
        // name the function declares. Whether that reads as a program name has
        // been decided elsewhere: while the carrier was also emitted as its own
        // statement, `x8_8 = len;`, the later single-use fold replaced the
        // return with the value; once the carrier is inlined instead, the
        // statement is gone and the return is left naming nothing. Resolving
        // here says the value in both cases, which is what the assignment
        // prepended just below has always done with the same expression.
        let expr = self.fold_ctx.resolve_return_candidate(&expr);
        let stmt = self.prepend_named_merged_slot_assignment_if_needed(stmt, summary, &expr)?;
        if let Some(rewritten) = self.rewrite_trailing_return_with_merged_expr(&stmt, &expr) {
            return Ok(Some(rewritten));
        }
        if Self::single_terminator_stmt(&stmt).is_some() {
            return Ok(Some(stmt));
        }
        let mut stmts = Vec::new();
        Self::append_stmt_body_flat(&mut stmts, stmt);
        stmts.push(CStmt::Return(Some(
            expr.clone_without_render_observations(),
        )));
        Ok(Some(if stmts.len() == 1 {
            stmts.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(stmts)
        }))
    }

    fn has_merged_slot_return_expr(
        &self,
        _region: &Region,
        pred_addr: u64,
        summary: &crate::analysis::FrameSlotMergeSummary,
    ) -> bool {
        summary.incoming.contains_key(&pred_addr)
            || self
                .fold_ctx
                .merged_return_candidate_for_block_slot(pred_addr, summary.slot_offset)
                .is_some()
    }

    fn append_merged_register_return_if_needed(
        &self,
        stmt: CStmt,
        merge_addr: u64,
        pred_addr: u64,
    ) -> ControlFlowStructureResult<Option<CStmt>> {
        if !self.block_allows_predecessor_return_register_rewrite(merge_addr) {
            return Ok(None);
        }
        let Some((expr, proof_block, proof_op, proof_value)) =
            self.return_register_candidate_for_merge_predecessor(merge_addr, pred_addr)?
        else {
            if Self::single_return_expr(&stmt).is_some()
                && let Some((proof_block, proof_op, proof_value)) =
                    self.predecessor_return_register_certificate(pred_addr)
            {
                return Ok(Some(self.observe_return_value_ownership(
                    stmt,
                    proof_block, proof_op, proof_value,
                )));
            }
            return Ok(None);
        };
        if let Some(rewritten) = self.rewrite_trailing_return_with_merged_expr(&stmt, &expr) {
            return Ok(Some(self.observe_return_value_ownership(
                rewritten,
                proof_block, proof_op, proof_value,
            )));
        }
        if Self::single_terminator_stmt(&stmt).is_some() {
            return Ok(Some(stmt));
        }
        let mut stmts = Vec::new();
        Self::append_stmt_body_flat(&mut stmts, stmt);
        stmts.push(CStmt::Return(Some(
            expr.clone_without_render_observations(),
        )));
        let rewritten = if stmts.len() == 1 {
            stmts.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(stmts)
        };
        Ok(Some(self.observe_return_value_ownership(
            rewritten,
            proof_block,
            proof_op,
            proof_value,
        )))
    }

    fn predecessor_return_register_certificate(
        &self,
        pred_addr: u64,
    ) -> Option<(u64, usize, ValueId)> {
        self.fold_ctx
            .inputs
            .prepared_ssa?
            .certificates()
            .returns
            .iter()
            .filter(|cert| cert.block_addr == pred_addr)
            .max_by_key(|cert| cert.op_index)
            .map(|cert| (cert.block_addr, cert.op_index, cert.value))
    }

    fn stmt_has_predecessor_return_register_certificate(
        &self,
        stmt: &CStmt,
        pred_addr: u64,
    ) -> bool {
        Self::single_return_expr(stmt).is_some()
            && self
                .predecessor_return_register_certificate(pred_addr)
                .is_some()
    }

    fn has_merged_register_return_expr(
        &self,
        merge_addr: u64,
        pred_addr: u64,
    ) -> ControlFlowStructureResult<bool> {
        Ok(self
            .return_register_candidate_for_merge_predecessor(merge_addr, pred_addr)?
            .is_some())
    }

    /// Record that a merge block reached the output through its predecessors.
    ///
    /// Rewriting an if/else so both arms end in the merge block's return says
    /// what that block says, once per arm, and then never emits the block. The
    /// record of which blocks were folded is what everything downstream reads
    /// to decide whether the output covers the function, and by that record the
    /// block went missing. It did not: it is on the page twice.
    fn note_merge_block_rendered_by_duplication(&self, merge_block: u64) {
        self.fold_ctx
            .folded_blocks
            .borrow_mut()
            .insert(merge_block);
    }

    fn observe_return_value_ownership(&self,
        stmt: CStmt,
        block_addr: u64, op_idx: usize, value: ValueId,
    ) -> CStmt {
        let mut obligations = self.fold_ctx.exact_effect_obligations_for_source_value(
            EffectOccurrenceKind::Return,
            block_addr,
            op_idx,
            Some(value),
        );
        if let Some((read_block, read_op, space, address, read_value)) = self
            .fold_ctx
            .certified_memory_read_for_value_dependency(value)
            .map(|cert| {
                (
                    cert.block_addr,
                    cert.op_index,
                    cert.space,
                    cert.address,
                    cert.value,
                )
            })
        {
            obligations.extend(self.fold_ctx.exact_effect_obligations_for_source_memory(
                EffectOccurrenceKind::MemoryRead,
                read_block,
                read_op,
                space,
                Some(address),
                read_value,
            ));
        }
        self.fold_ctx.observe_effect_stmt(&obligations, stmt)
    }

    fn prepend_named_merged_slot_assignment_if_needed(
        &self,
        stmt: CStmt,
        summary: &crate::analysis::FrameSlotMergeSummary,
        expr: &CExpr,
    ) -> ControlFlowStructureResult<CStmt> {
        let _ = (stmt, summary.slot_offset, expr);
        Err(OpLoweringRefusal::MissingProgramVariableAuthorization.into())
    }

    fn rewrite_trailing_return_with_merged_expr(
        &self,
        stmt: &CStmt,
        merged: &CExpr,
    ) -> Option<CStmt> {
        match stmt {
            // A proven frame-slot merge is authoritative for this region tail.
            // Once structure has matched the if/else -> merge-slot -> return pattern,
            // do not let an earlier synthesized return expression beat the merged value.
            CStmt::Return(Some(_current)) => Some(CStmt::Return(Some(
                merged.clone_without_render_observations(),
            ))),
            CStmt::Comment(reason)
                if reason.starts_with(
                    "r2sleigh residual: unresolved value return for control-only exit",
                ) =>
            {
                Some(CStmt::Return(Some(
                    merged.clone_without_render_observations(),
                )))
            }
            CStmt::Block(stmts) => {
                let (last, prefix) = stmts.split_last()?;
                let rewritten_tail = self.rewrite_trailing_return_with_merged_expr(last, merged)?;
                let mut rebuilt = prefix.to_vec();
                rebuilt.push(rewritten_tail);
                Some(CStmt::Block(rebuilt))
            }
            _ => None,
        }
    }

    fn rewrite_block_tail_guard_clauses(stmts: Vec<CStmt>) -> Vec<CStmt> {
        let mut rewritten = Vec::with_capacity(stmts.len());
        let mut i = 0;
        while i < stmts.len() {
            if i + 1 < stmts.len()
                && let CStmt::If {
                    cond,
                    then_body,
                    else_body: None,
                } = Self::semantic_stmt(&stmts[i])
                && let Some(terminator) = Self::single_terminator_stmt(&stmts[i + 1])
                && Self::single_terminator_stmt(then_body.as_ref()).is_none()
                && !matches!(Self::semantic_stmt(then_body), CStmt::Empty)
            {
                let guard = CStmt::If {
                    cond: Self::negate_condition(cond.clone()),
                    then_body: Box::new(terminator.clone_without_render_observations()),
                    else_body: None,
                };
                rewritten.push(guard);
                Self::append_stmt_body_flat(&mut rewritten, then_body.as_ref().clone());
                rewritten.push(stmts[i + 1].clone());
                i += 2;
                continue;
            }

            rewritten.push(stmts[i].clone());
            i += 1;
        }
        rewritten
    }

    fn rewrite_guarded_switch_if_else(stmts: Vec<CStmt>) -> Vec<CStmt> {
        let mut rewritten = Vec::with_capacity(stmts.len());
        let mut i = 0;
        while i < stmts.len() {
            if i + 1 < stmts.len()
                && let CStmt::If {
                    then_body,
                    else_body: Some(else_body),
                    ..
                } = &stmts[i]
                && let Some(CStmt::Return(Some(CExpr::IntLit(0) | CExpr::UIntLit(0)))) =
                    Self::single_terminator_stmt(&stmts[i + 1])
            {
                let then_switch = Self::single_switch_stmt(then_body.as_ref())
                    .filter(|stmt| matches!(stmt, CStmt::Switch { default: None, .. }));
                let else_switch = Self::single_switch_stmt(else_body.as_ref())
                    .filter(|stmt| matches!(stmt, CStmt::Switch { default: None, .. }));
                let (switch_stmt, default_stmt) = match (then_switch, else_switch) {
                    (Some(switch_stmt), None) => (switch_stmt, else_body.as_ref().clone()),
                    (None, Some(switch_stmt)) => (switch_stmt, then_body.as_ref().clone()),
                    _ => {
                        rewritten.push(stmts[i].clone());
                        i += 1;
                        continue;
                    }
                };
                if !Self::stmt_guarantees_termination(&default_stmt) {
                    rewritten.push(stmts[i].clone());
                    i += 1;
                    continue;
                }

                if let CStmt::Switch { expr, cases, .. } = switch_stmt {
                    rewritten.push(CStmt::Switch {
                        expr,
                        cases,
                        default: Some(vec![default_stmt]),
                    });
                    rewritten.push(stmts[i + 1].clone());
                    i += 2;
                    continue;
                }
            }

            rewritten.push(stmts[i].clone());
            i += 1;
        }
        rewritten
    }

    fn rewrite_continue_tail_merges(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmts: Vec<CStmt>,
    ) -> Vec<CStmt> {
        let mut rewritten = Vec::with_capacity(stmts.len());
        let mut i = 0;
        while i < stmts.len() {
            if i + 1 < stmts.len()
                && let CStmt::If {
                    cond,
                    then_body,
                    else_body: None,
                } = &stmts[i]
                && let Some((then_prefix, tail_stmt)) =
                    Self::split_trailing_update_continue(symbols, (**then_body).clone())
            {
                let else_stmts = stmts[i + 1..].to_vec();
                let else_body = Self::stmt_from_vec(else_stmts.clone());
                if !Self::stmt_guarantees_termination(&else_body) {
                    rewritten.extend(Self::factor_guarded_common_suffix(
                        cond.clone(),
                        then_prefix,
                        else_stmts,
                    ));
                    rewritten.push(tail_stmt);
                    break;
                }
            }

            rewritten.push(stmts[i].clone());
            i += 1;
        }

        rewritten
    }

    fn factor_guarded_common_suffix(
        cond: CExpr,
        mut then_stmts: Vec<CStmt>,
        mut else_stmts: Vec<CStmt>,
    ) -> Vec<CStmt> {
        let mut common_suffix = Vec::new();
        while then_stmts.last().is_some()
            && then_stmts
                .last()
                .zip(else_stmts.last())
                .is_some_and(|(then_stmt, else_stmt)| {
                    Self::stmt_transparently_eq(then_stmt, else_stmt)
                })
            && !Self::stmt_list_contains_control_transfer(&then_stmts[..then_stmts.len() - 1])
            && !Self::stmt_list_contains_control_transfer(&else_stmts[..else_stmts.len() - 1])
        {
            let then_suffix = then_stmts.pop().expect("then suffix");
            let _else_suffix = else_stmts.pop().expect("else suffix");
            let semantic_suffix = then_suffix.clone_without_render_observations();
            common_suffix.push(semantic_suffix);
        }
        common_suffix.reverse();

        let mut out = Vec::new();
        if then_stmts.is_empty() && else_stmts.is_empty() {
            out.extend(common_suffix);
            return out;
        }

        let guarded = if then_stmts.is_empty() {
            CStmt::If {
                cond: Self::negate_condition(cond),
                then_body: Box::new(Self::stmt_from_vec(else_stmts)),
                else_body: None,
            }
        } else {
            CStmt::If {
                cond,
                then_body: Box::new(Self::stmt_from_vec(then_stmts)),
                else_body: (!else_stmts.is_empty())
                    .then(|| Box::new(Self::stmt_from_vec(else_stmts))),
            }
        };
        out.push(Self::rewrite_if_short_circuit(guarded));
        out.extend(common_suffix);
        out
    }

    fn stmt_transparently_eq(left: &CStmt, right: &CStmt) -> bool {
        let left = left.unobserved();
        let right = right.unobserved();
        match (left, right) {
            (CStmt::Empty, CStmt::Empty)
            | (CStmt::Break, CStmt::Break)
            | (CStmt::Continue, CStmt::Continue) => true,
            (CStmt::Expr(left), CStmt::Expr(right)) => left.transparently_eq(right),
            (
                CStmt::Decl {
                    ty: left_ty,
                    name: left_name,
                    init: left_init,
                },
                CStmt::Decl {
                    ty: right_ty,
                    name: right_name,
                    init: right_init,
                },
            ) => {
                left_ty == right_ty
                    && left_name == right_name
                    && match (left_init, right_init) {
                        (Some(left), Some(right)) => left.transparently_eq(right),
                        (None, None) => true,
                        _ => false,
                    }
            }
            (CStmt::Block(left), CStmt::Block(right)) => {
                Self::stmt_slices_transparently_eq(left, right)
            }
            (
                CStmt::If {
                    cond: left_cond,
                    then_body: left_then,
                    else_body: left_else,
                },
                CStmt::If {
                    cond: right_cond,
                    then_body: right_then,
                    else_body: right_else,
                },
            ) => {
                left_cond.transparently_eq(right_cond)
                    && Self::stmt_transparently_eq(left_then, right_then)
                    && match (left_else, right_else) {
                        (Some(left), Some(right)) => Self::stmt_transparently_eq(left, right),
                        (None, None) => true,
                        _ => false,
                    }
            }
            (
                CStmt::While {
                    cond: left_cond,
                    body: left_body,
                },
                CStmt::While {
                    cond: right_cond,
                    body: right_body,
                },
            )
            | (
                CStmt::DoWhile {
                    body: left_body,
                    cond: left_cond,
                },
                CStmt::DoWhile {
                    body: right_body,
                    cond: right_cond,
                },
            ) => {
                left_cond.transparently_eq(right_cond)
                    && Self::stmt_transparently_eq(left_body, right_body)
            }
            (
                CStmt::For {
                    init: left_init,
                    cond: left_cond,
                    update: left_update,
                    body: left_body,
                },
                CStmt::For {
                    init: right_init,
                    cond: right_cond,
                    update: right_update,
                    body: right_body,
                },
            ) => {
                let init_equal = match (left_init, right_init) {
                    (Some(left), Some(right)) => Self::stmt_transparently_eq(left, right),
                    (None, None) => true,
                    _ => false,
                };
                let cond_equal = match (left_cond, right_cond) {
                    (Some(left), Some(right)) => left.transparently_eq(right),
                    (None, None) => true,
                    _ => false,
                };
                let update_equal = match (left_update, right_update) {
                    (Some(left), Some(right)) => left.transparently_eq(right),
                    (None, None) => true,
                    _ => false,
                };
                init_equal
                    && cond_equal
                    && update_equal
                    && Self::stmt_transparently_eq(left_body, right_body)
            }
            (
                CStmt::Switch {
                    expr: left_expr,
                    cases: left_cases,
                    default: left_default,
                },
                CStmt::Switch {
                    expr: right_expr,
                    cases: right_cases,
                    default: right_default,
                },
            ) => {
                left_expr.transparently_eq(right_expr)
                    && left_cases.len() == right_cases.len()
                    && left_cases.iter().zip(right_cases).all(|(left, right)| {
                        left.value.transparently_eq(&right.value)
                            && Self::stmt_slices_transparently_eq(&left.body, &right.body)
                    })
                    && match (left_default, right_default) {
                        (Some(left), Some(right)) => {
                            Self::stmt_slices_transparently_eq(left, right)
                        }
                        (None, None) => true,
                        _ => false,
                    }
            }
            (CStmt::Return(left), CStmt::Return(right)) => match (left, right) {
                (Some(left), Some(right)) => left.transparently_eq(right),
                (None, None) => true,
                _ => false,
            },
            (CStmt::Goto(left), CStmt::Goto(right))
            | (CStmt::Label(left), CStmt::Label(right))
            | (CStmt::Comment(left), CStmt::Comment(right)) => left == right,
            _ => false,
        }
    }

    fn stmt_slices_transparently_eq(left: &[CStmt], right: &[CStmt]) -> bool {
        left.len() == right.len()
            && left
                .iter()
                .zip(right)
                .all(|(left, right)| Self::stmt_transparently_eq(left, right))
    }

    fn stmt_list_contains_control_transfer(stmts: &[CStmt]) -> bool {
        stmts.iter().any(Self::stmt_contains_control_transfer)
    }

    fn stmt_contains_control_transfer(stmt: &CStmt) -> bool {
        if Self::stmt_is_unconditional_terminator(stmt) {
            return true;
        }
        match stmt.unobserved() {
            CStmt::Block(stmts) => Self::stmt_list_contains_control_transfer(stmts),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                Self::stmt_contains_control_transfer(then_body)
                    || else_body
                        .as_ref()
                        .is_some_and(|stmt| Self::stmt_contains_control_transfer(stmt))
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } | CStmt::For { body, .. } => {
                Self::stmt_contains_control_transfer(body)
            }
            CStmt::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|case| Self::stmt_list_contains_control_transfer(&case.body))
                    || default
                        .as_ref()
                        .is_some_and(|body| Self::stmt_list_contains_control_transfer(body))
            }
            _ => false,
        }
    }

    fn split_trailing_update_continue(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: CStmt,
    ) -> Option<(Vec<CStmt>, CStmt)> {
        let mut stmts = Self::stmt_into_vec(stmt);
        while stmts
            .last()
            .is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Empty))
        {
            stmts.pop();
        }
        if !stmts
            .last()
            .is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Continue))
        {
            return None;
        }
        stmts.pop();
        while stmts
            .last()
            .is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Empty))
        {
            stmts.pop();
        }
        while stmts
            .last()
            .is_some_and(|x| Self::is_generated_side_effect_free_assignment(symbols, x))
        {
            stmts.pop();
            while stmts
                .last()
                .is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Empty))
            {
                stmts.pop();
            }
        }
        let tail_stmt = stmts.pop()?;
        Self::stmt_is_self_update(symbols, &tail_stmt).then_some((stmts, tail_stmt))
    }

    fn strip_trailing_for_update(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, body: CStmt, update: &CExpr,
    ) -> CStmt {
        let mut stmts = Self::stmt_into_vec(body);
        while stmts
            .last()
            .is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Empty))
        {
            stmts.pop();
        }
        if stmts.last().is_some_and(|stmt| {
            matches!(stmt.unobserved(), CStmt::Expr(expr) if Self::expr_matches_for_update(symbols, expr, update))
        }) {
            stmts.pop();
        }
        Self::stmt_from_vec(stmts)
    }

    fn remove_dead_generated_artifact_assignments(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        stmt: CStmt,
    ) -> CStmt {
        let (semantic, observations) = stmt.into_semantic_with_observations();
        let (rewritten, exact_outer_statement_survives) = match semantic {
            CStmt::Block(stmts) => {
                let stmts = stmts
                    .into_iter()
                    .map(|x| Self::remove_dead_generated_artifact_assignments(symbols, x))
                    .collect();
                let rewritten = Self::stmt_from_vec(
                    Self::remove_dead_generated_artifact_assignments_from_vec(
                    symbols, stmts),
                );
                let preserves_block = matches!(rewritten, CStmt::Block(_));
                (rewritten, preserves_block)
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => (
                CStmt::If {
                    cond,
                    then_body: Box::new(Self::remove_dead_generated_artifact_assignments(
                        symbols, *then_body,
                    )),
                    else_body: else_body.map(|body| {
                        Box::new(Self::remove_dead_generated_artifact_assignments(
                            symbols, *body,
                        ))
                    }),
                },
                true,
            ),
            CStmt::While { cond, body } => (
                CStmt::While {
                    cond,
                    body: Box::new(Self::remove_dead_generated_artifact_assignments(
                        symbols, *body,
                    )),
                },
                true,
            ),
            CStmt::DoWhile { body, cond } => (
                CStmt::DoWhile {
                    body: Box::new(Self::remove_dead_generated_artifact_assignments(
                        symbols, *body,
                    )),
                    cond,
                },
                true,
            ),
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => (
                CStmt::For {
                    init,
                    cond,
                    update,
                    body: Box::new(Self::remove_dead_generated_artifact_assignments(
                        symbols, *body,
                    )),
                },
                true,
            ),
            CStmt::Switch {
                expr,
                cases,
                default,
            } => (
                CStmt::Switch {
                    expr,
                    cases: cases
                        .into_iter()
                        .map(|case| crate::ast::SwitchCase {
                            value: case.value,
                            body: Self::remove_dead_generated_artifact_assignments_from_vec(
                                symbols, case.body,
                            ),
                        })
                        .collect(),
                    default: default.map(|x| {
                        Self::remove_dead_generated_artifact_assignments_from_vec(symbols, x)
                    }),
                },
                true,
            ),
            other => (other, true),
        };
        if exact_outer_statement_survives {
            observations.reapply(rewritten)
        } else {
            rewritten
        }
    }

    fn remove_dead_generated_artifact_assignments_from_vec(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        stmts: Vec<CStmt>,
    ) -> Vec<CStmt> {
        let mut live = HashSet::new();
        let mut kept = Vec::with_capacity(stmts.len());
        for stmt in stmts.into_iter().rev() {
            if let Some((def, reads, generated, side_effect_free)) =
                Self::stmt_assignment_def_reads(symbols, &stmt)
            {
                if generated && side_effect_free && !Self::set_contains_loop_var(&live, &def) {
                    continue;
                }
                Self::set_remove_loop_var_aliases(&mut live, &def);
                live.extend(reads);
            } else {
                live.extend(Self::collect_stmt_vars(symbols, &stmt));
            }
            kept.push(stmt);
        }
        kept.reverse();
        kept
    }

    fn expr_matches_for_update(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, body_expr: &CExpr, for_update: &CExpr,
    ) -> bool {
        if body_expr.transparently_eq(for_update) {
            return true;
        }

        Self::normalized_self_update_signature(symbols, body_expr)
            .zip(Self::normalized_self_update_signature(symbols, for_update))
            .is_some_and(|(body, update)| body == update)
    }

    fn normalized_self_update_signature(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, expr: &CExpr,
    ) -> Option<(String, BinaryOp, CExpr)> {
        let semantic = expr.clone_without_render_observations();
        let CExpr::Binary { op, left, right } = &semantic else {
            return None;
        };
        let CExpr::Var(name) = left.unobserved() else {
            return None;
        };

        if Self::is_compound_assign_op(*op) {
            return Some((crate::symbol::spelling(symbols, *name).to_string(), *op, right.as_ref().clone(),
            ));
        }

        if *op == BinaryOp::Assign
            && let Some((compound_op, rhs)) = Self::compound_assignment_rhs_of(symbols, &crate::symbol::spelling(symbols, *name), right,
            )
        {
            return Some((crate::symbol::spelling(symbols, *name).to_string(), compound_op, rhs,
            ));
        }

        None
    }

    fn stmt_is_self_update(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: &CStmt,
    ) -> bool {
        let CStmt::Expr(expr) = stmt.unobserved() else {
            return false;
        };
        match expr.unobserved() {
            CExpr::Unary { op, operand } => {
                matches!(
                    op,
                    UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec
                ) && matches!(operand.unobserved(), CExpr::Var(_))
            }
            CExpr::Binary { op, left, right } => {
                let CExpr::Var(name) = left.unobserved() else {
                    return false;
                };
                if Self::is_compound_assign_op(*op) {
                    return true;
                }
                if *op != BinaryOp::Assign {
                    return false;
                }
                let rhs_vars = Self::collect_expr_vars(symbols, right);
                Self::set_contains_loop_var(&rhs_vars, &crate::symbol::spelling(symbols, *name))
            }
            _ => false,
        }
    }

    fn truncate_dead_straight_line_tail(stmts: Vec<CStmt>) -> Vec<CStmt> {
        let mut rewritten = Vec::with_capacity(stmts.len());
        let mut terminated = false;
        for stmt in stmts {
            // Control does not only arrive here by falling in. A label is
            // somewhere a jump goes, so nothing before it can make it dead --
            // and a label carried inside a statement is still a label, which
            // dropping the statement around it would leave jumps pointing at
            // nothing.
            if Self::stmt_carries_label(&stmt) {
                terminated = false;
                rewritten.push(stmt);
                continue;
            }
            if terminated {
                continue;
            }
            terminated = Self::stmt_guarantees_termination(&stmt);
            rewritten.push(stmt);
        }
        rewritten
    }

    /// Whether anything can jump into this statement.
    fn stmt_carries_label(stmt: &CStmt) -> bool {
        match Self::semantic_stmt(stmt) {
            CStmt::Label(_) => true,
            CStmt::Block(stmts) => stmts.iter().any(Self::stmt_carries_label),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                Self::stmt_carries_label(then_body)
                    || else_body
                        .as_ref()
                        .is_some_and(|body| Self::stmt_carries_label(body))
            }
            CStmt::While { body, .. }
            | CStmt::DoWhile { body, .. }
            | CStmt::For { body, .. } => {
                Self::stmt_carries_label(body)
            }
            CStmt::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|case| case.body.iter().any(Self::stmt_carries_label))
                    || default
                        .as_ref()
                        .is_some_and(|body| body.iter().any(Self::stmt_carries_label))
            }
            _ => false,
        }
    }

    fn stmt_guarantees_termination(stmt: &CStmt) -> bool {
        if Self::stmt_is_unconditional_terminator(stmt) {
            return true;
        }

        match Self::semantic_stmt(stmt) {
            CStmt::Block(stmts) => stmts
                .iter()
                .rev()
                .find(|stmt| !matches!(stmt.unobserved(), CStmt::Empty))
                .is_some_and(Self::stmt_guarantees_termination),
            CStmt::If {
                then_body,
                else_body: Some(else_body),
                ..
            } => {
                Self::stmt_guarantees_termination(then_body)
                    && Self::stmt_guarantees_termination(else_body)
            }
            _ => false,
        }
    }

    fn single_terminator_stmt(stmt: &CStmt) -> Option<CStmt> {
        if Self::stmt_is_unconditional_terminator(stmt) {
            return Some(stmt.clone());
        }

        if let CStmt::Block(stmts) = stmt.unobserved()
            && stmts.len() == 1
            && Self::stmt_is_unconditional_terminator(&stmts[0])
        {
            return Some(stmts[0].clone());
        }

        None
    }

    fn single_switch_stmt(stmt: &CStmt) -> Option<CStmt> {
        match stmt.unobserved() {
            CStmt::Switch { .. } => Some(stmt.clone()),
            CStmt::Block(stmts)
                if stmts.len() == 1
                    && matches!(stmts[0].unobserved(), CStmt::Switch { .. }) =>
            {
                Some(stmts[0].clone())
            }
            _ => None,
        }
    }

    fn extract_switch_with_trailing_stmt(stmt: &CStmt) -> Option<(CStmt, Option<CStmt>)> {
        match stmt.unobserved() {
            CStmt::Switch { .. } => Some((stmt.clone(), None)),
            CStmt::Block(stmts) => {
                let stmts = stmts
                    .iter()
                    .filter(|stmt| !matches!(stmt.unobserved(), CStmt::Empty))
                    .cloned()
                    .collect::<Vec<_>>();
                match stmts.as_slice() {
                    [switch @ CStmt::Switch { .. }] => Some((switch.clone(), None)),
                    [switch @ CStmt::Switch { .. }, trailing] => {
                        Some((switch.clone(), Some(trailing.clone())))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn negate_condition(cond: CExpr) -> CExpr {
        match cond {
            CExpr::Observed { id, expr } => CExpr::observed(id, Self::negate_condition(*expr)),
            CExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => *operand,
            CExpr::Binary {
                op: BinaryOp::Or,
                left,
                right,
            } => {
                if let Some(rewritten) =
                    Self::negate_disjunctive_relation_pair(left.as_ref(), right.as_ref())
                {
                    return rewritten;
                }
                CExpr::unary(
                    UnaryOp::Not,
                    CExpr::Binary {
                        op: BinaryOp::Or,
                        left,
                        right,
                    },
                )
            }
            CExpr::Binary { op, left, right } => {
                let negated = match op {
                    BinaryOp::Eq => Some((BinaryOp::Ne, false)),
                    BinaryOp::Ne => Some((BinaryOp::Eq, false)),
                    BinaryOp::Lt => Some((BinaryOp::Ge, false)),
                    BinaryOp::Le => Some((BinaryOp::Lt, true)),
                    BinaryOp::Gt => Some((BinaryOp::Le, false)),
                    BinaryOp::Ge => Some((BinaryOp::Lt, false)),
                    _ => None,
                };

                if let Some((op, swap)) = negated {
                    if swap {
                        CExpr::Binary {
                            op,
                            left: right,
                            right: left,
                        }
                    } else {
                        CExpr::Binary { op, left, right }
                    }
                } else {
                    CExpr::unary(UnaryOp::Not, CExpr::Binary { op, left, right })
                }
            }
            other => CExpr::unary(UnaryOp::Not, other),
        }
    }

    fn negate_disjunctive_relation_pair(left: &CExpr, right: &CExpr) -> Option<CExpr> {
        let (lhs_a, rhs_a, op_a) = Self::relation_signature(left)?;
        let (lhs_b, rhs_b, op_b) = Self::relation_signature(right)?;
        if lhs_a != lhs_b || rhs_a != rhs_b {
            return None;
        }

        let negated_op = match (op_a, op_b) {
            (BinaryOp::Eq, BinaryOp::Lt) | (BinaryOp::Lt, BinaryOp::Eq) => BinaryOp::Gt,
            (BinaryOp::Eq, BinaryOp::Le) | (BinaryOp::Le, BinaryOp::Eq) => BinaryOp::Gt,
            (BinaryOp::Eq, BinaryOp::Gt) | (BinaryOp::Gt, BinaryOp::Eq) => BinaryOp::Lt,
            (BinaryOp::Eq, BinaryOp::Ge) | (BinaryOp::Ge, BinaryOp::Eq) => BinaryOp::Lt,
            _ => return None,
        };

        Some(CExpr::Binary {
            op: negated_op,
            left: Box::new(lhs_a.clone()),
            right: Box::new(rhs_a.clone()),
        })
    }

    fn relation_signature(expr: &CExpr) -> Option<(&CExpr, &CExpr, BinaryOp)> {
        match expr.unobserved() {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::relation_signature(inner)
            }
            CExpr::Binary { op, left, right }
                if matches!(
                    op,
                    BinaryOp::Eq | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
                ) =>
            {
                Some((left.as_ref(), right.as_ref(), *op))
            }
            _ => None,
        }
    }

    /// Rewrite adjacent `init; while (...) { ...; update; }` into `for (...)`.
    fn rewrite_block_loops_to_for(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmts: Vec<CStmt>,
    ) -> Vec<CStmt> {
        let mut rewritten = Vec::with_capacity(stmts.len());
        let mut i = 0;
        while i < stmts.len() {
            if i + 1 < stmts.len()
                && let Some(mut for_stmts) = Self::try_rewrite_while_with_preheader_init(symbols,
                    stmts[i].clone(),
                    stmts[i + 1].clone(),
                )
            {
                rewritten.append(&mut for_stmts);
                i += 2;
                continue;
            }
            rewritten.push(stmts[i].clone());
            i += 1;
        }
        rewritten
    }

    fn try_rewrite_while_with_preheader_init(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, 
        preheader_stmt: CStmt,
        while_stmt: CStmt,
    ) -> Option<Vec<CStmt>> {
        let (prefix_stmts, init_stmt, induction_var) = Self::split_preheader_init(preheader_stmt)?;
        let (while_semantic, _while_observations) =
            while_stmt.into_semantic_with_observations();
        let CStmt::While { cond, body } = while_semantic else {
            return None;
        };

        let (loop_cond, loop_body) = match cond.unobserved() {
            CExpr::IntLit(v) if *v != 0 => {
                let (exit_cond, stripped_body) = Self::extract_guard_break_cond(*body)?;
                (CExpr::unary(UnaryOp::Not, exit_cond), stripped_body)
            }
            _ => (cond, *body),
        };

        let cond_vars = Self::collect_expr_vars(symbols, &loop_cond);
        let cond_reads_induction = Self::set_contains_loop_var(&cond_vars, &crate::symbol::spelling(symbols, induction_var),
        );
        let (update, body_without_update, update_links_cond) =
            Self::extract_loop_update(
                symbols,
                &crate::symbol::spelling(symbols, induction_var),
                &cond_vars,
                loop_body,
            )?;

        if !cond_reads_induction && !update_links_cond {
            return None;
        }

        let mut rewritten = prefix_stmts;
        let body_without_update =
            Self::remove_dead_generated_artifact_assignments(symbols, body_without_update);
        rewritten.push(CStmt::For {
            init: Some(Box::new(init_stmt)),
            cond: Some(loop_cond),
            update: Some(update),
            body: Box::new(body_without_update),
        });
        Some(rewritten)
    }

    fn extract_induction_var_from_init(init_stmt: &CStmt) -> Option<crate::symbol::SymbolId> {
        match init_stmt.unobserved() {
            CStmt::Expr(expr) => {
                let CExpr::Binary {
                    op: BinaryOp::Assign,
                    left,
                    ..
                } = expr.unobserved()
                else {
                    return None;
                };
                match left.unobserved() {
                    CExpr::Var(name) => Some(*name),
                    _ => None,
                }
            }
            CStmt::Decl {
                name,
                init: Some(_),
                ..
            } => Some(*name),
            _ => None,
        }
    }

    fn split_preheader_init(preheader_stmt: CStmt,
    ) -> Option<(Vec<CStmt>, CStmt, crate::symbol::SymbolId)> {
        if let Some(var) = Self::extract_induction_var_from_init(&preheader_stmt) {
            return Some((Vec::new(), preheader_stmt, var));
        }

        let (semantic, _block_observations) =
            preheader_stmt.into_semantic_with_observations();
        let CStmt::Block(mut prefix) = semantic else {
            return None;
        };
        while prefix
            .last()
            .is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Empty))
        {
            prefix.pop();
        }
        let init_stmt = prefix.pop()?;
        let var = Self::extract_induction_var_from_init(&init_stmt)?;
        Some((prefix, init_stmt, var))
    }

    fn extract_loop_update(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, 
        var: &str,
        cond_vars: &HashSet<String>,
        body: CStmt,
    ) -> Option<(CExpr, CStmt, bool)> {
        let stmts = Self::stmt_into_vec(body);
        if stmts.is_empty() {
            return None;
        }

        // Trim unreachable statements after the first unconditional transfer.
        let mut effective = Vec::new();
        for stmt in stmts {
            let is_terminator = Self::stmt_is_unconditional_terminator(&stmt);
            effective.push(stmt);
            if is_terminator {
                break;
            }
        }

        while effective.last().is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Empty | CStmt::Continue)) {
            effective.pop();
        }
        if effective.is_empty() {
            return None;
        }

        for idx in (0..effective.len()).rev() {
            if !effective[idx + 1..]
                .iter()
                .all(|stmt| {
                Self::is_removable_trailing_loop_artifact(symbols, stmt, var, cond_vars)
            })
            {
                break;
            }
            let prev_stmts = &effective[..idx];
            if let Some((update, update_links_cond)) =
                Self::update_expr_from_stmt(symbols, var, cond_vars, prev_stmts, &effective[idx])
            {
                let body = effective[..idx].to_vec();
                return Some((update, Self::stmt_from_vec(body), update_links_cond));
            }
        }

        None
    }

    fn extract_guard_break_cond(body: CStmt) -> Option<(CExpr, CStmt)> {
        let mut stmts = Self::stmt_into_vec(body);
        let first = stmts.first()?;
        let break_cond = Self::is_if_break_without_else(first)?;
        stmts.remove(0);
        Some((break_cond, Self::stmt_from_vec(stmts)))
    }

    fn update_expr_from_stmt(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, 
        var: &str,
        cond_vars: &HashSet<String>,
        prev_stmts: &[CStmt],
        stmt: &CStmt,
    ) -> Option<(CExpr, bool)> {
        let CStmt::Expr(expr) = stmt.unobserved() else {
            return None;
        };
        match expr.unobserved() {
            CExpr::Unary { op, operand }
                if matches!(
                    op,
                    UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec
                ) && matches!(operand.unobserved(), CExpr::Var(name) if Self::loop_var_equiv(&crate::symbol::spelling(symbols, *name), var)) =>
            {
                Some((expr.clone(), false))
            }
            CExpr::Binary { op, left, right } if matches!(left.unobserved(), CExpr::Var(_)) => {
                let CExpr::Var(left_name) = left.unobserved() else {
                    return None;
                };
                let left_is_induction = Self::loop_var_equiv(&crate::symbol::spelling(symbols, *left_name), var);
                let left_feeds_condition = Self::set_contains_loop_var(cond_vars, &crate::symbol::spelling(symbols, *left_name),
                );
                if *op == BinaryOp::Assign {
                    let rhs_vars = Self::collect_expr_vars(symbols, right);
                    let links_cond_direct = Self::sets_overlap_loop_vars(&rhs_vars, cond_vars);
                    let reads_induction = Self::set_contains_loop_var(&rhs_vars, var);
                    let links_cond_via_alias =
                        Self::rhs_links_cond_via_alias(symbols, prev_stmts, &rhs_vars, cond_vars);
                    if (left_is_induction && reads_induction)
                        || (left_feeds_condition && (links_cond_direct || links_cond_via_alias))
                    {
                        return Some((expr.clone(), links_cond_direct || links_cond_via_alias));
                    }
                }
                if Self::is_compound_assign_op(*op)
                    && matches!(left.unobserved(), CExpr::Var(name) if Self::loop_var_equiv(&crate::symbol::spelling(symbols, *name), var))
                {
                    return Some((expr.clone(), false));
                }
                None
            }
            _ => None,
        }
    }

    fn is_removable_trailing_loop_artifact(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, 
        stmt: &CStmt,
        var: &str,
        cond_vars: &HashSet<String>,
    ) -> bool {
        let (name, rhs) = match stmt.unobserved() {
            CStmt::Expr(expr) => {
                let CExpr::Binary {
                    op: BinaryOp::Assign,
                    left,
                    right,
                } = expr.unobserved()
                else {
                    return false;
                };
                let CExpr::Var(name) = left.unobserved() else {
                    return false;
                };
                (&*crate::symbol::spelling(symbols, *name), right.as_ref())
            }
            CStmt::Decl {
                name,
                init: Some(rhs),
                ..
            } => (&*crate::symbol::spelling(symbols, *name), rhs),
            _ => return false,
        };
        if Self::loop_var_equiv(name, var) || Self::set_contains_loop_var(cond_vars, name) {
            return false;
        }
        Self::is_generated_artifact_name(name) && crate::fold::op_lower::expr_is_side_effect_free(rhs)
    }

    fn is_generated_side_effect_free_assignment(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: &CStmt,
    ) -> bool {
        let (name, rhs) = match stmt.unobserved() {
            CStmt::Expr(expr) => {
                let CExpr::Binary {
                    op: BinaryOp::Assign,
                    left,
                    right,
                } = expr.unobserved()
                else {
                    return false;
                };
                let CExpr::Var(name) = left.unobserved() else {
                    return false;
                };
                (&*crate::symbol::spelling(symbols, *name), right.as_ref())
            }
            CStmt::Decl {
                name,
                init: Some(rhs),
                ..
            } => (&*crate::symbol::spelling(symbols, *name), rhs),
            _ => return false,
        };
        Self::is_generated_artifact_name(name) && crate::fold::op_lower::expr_is_side_effect_free(rhs)
    }

    fn is_generated_artifact_name(name: &str) -> bool {

        let lower = name.to_ascii_lowercase();
        let versioned_register = lower.rsplit_once('_').is_some_and(|(base, version)| {
            version.bytes().all(|byte| byte.is_ascii_digit())
                && matches!(
                    base,
                    "al" | "ah"
                        | "ax"
                        | "eax"
                        | "rax"
                        | "bl"
                        | "bh"
                        | "bx"
                        | "ebx"
                        | "rbx"
                        | "cl"
                        | "ch"
                        | "cx"
                        | "ecx"
                        | "rcx"
                        | "dl"
                        | "dh"
                        | "dx"
                        | "edx"
                        | "rdx"
                        | "esi"
                        | "rsi"
                        | "edi"
                        | "rdi"
                )
        });
        lower.starts_with("value_")
            || crate::analysis::utils::is_temporary_name(name)
            || lower.contains(':')
            || (lower.starts_with('t') && lower[1..].chars().all(|ch| ch.is_ascii_digit()))
            || versioned_register
    }

    fn is_if_break_without_else(stmt: &CStmt) -> Option<CExpr> {
        let CStmt::If {
            cond,
            then_body,
            else_body: None,
        } = stmt.unobserved()
        else {
            return None;
        };
        if matches!(then_body.unobserved(), CStmt::Break)
            || matches!(then_body.unobserved(), CStmt::Block(v) if v.len() == 1 && Self::stmt_is_unconditional_break(&v[0]))
        {
            return Some(cond.clone());
        }
        None
    }

    fn is_compound_assign_op(op: BinaryOp) -> bool {
        matches!(
            op,
            BinaryOp::AddAssign
                | BinaryOp::SubAssign
                | BinaryOp::MulAssign
                | BinaryOp::DivAssign
                | BinaryOp::ModAssign
                | BinaryOp::BitAndAssign
                | BinaryOp::BitOrAssign
                | BinaryOp::BitXorAssign
                | BinaryOp::ShlAssign
                | BinaryOp::ShrAssign
        )
    }

    fn stmt_is_unconditional_terminator(stmt: &CStmt) -> bool {
        matches!(
            Self::semantic_stmt(stmt),
            CStmt::Break | CStmt::Continue | CStmt::Return(_) | CStmt::Goto(_)
        )
    }

    fn stmt_is_unconditional_break(stmt: &CStmt) -> bool {
        matches!(Self::semantic_stmt(stmt), CStmt::Break)
    }

    /// Borrow the semantic statement through all run-local metadata wrappers.
    fn semantic_stmt(mut stmt: &CStmt) -> &CStmt {
        loop {
            match stmt {
                CStmt::Observed { stmt: inner, .. }
                | CStmt::StructuredRegion { stmt: inner, .. } => stmt = inner,
                semantic => return semantic,
            }
        }
    }

    fn stmt_into_vec(stmt: CStmt) -> Vec<CStmt> {
        let (semantic, observations) = stmt.into_semantic_with_observations();
        match semantic {
            CStmt::Block(mut stmts) => {
                observations.reapply_to_unique(&mut stmts);
                stmts
            }
            CStmt::Empty => Vec::new(),
            other => vec![observations.reapply(other)],
        }
    }

    fn stmt_from_vec(stmts: Vec<CStmt>) -> CStmt {
        match stmts.len() {
            0 => CStmt::Empty,
            1 => stmts.into_iter().next().unwrap(),
            _ => CStmt::Block(stmts),
        }
    }

    fn rhs_links_cond_via_alias(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, 
        prev_stmts: &[CStmt],
        rhs_vars: &HashSet<String>,
        cond_vars: &HashSet<String>,
    ) -> bool {
        let mut tracked = rhs_vars.clone();
        for stmt in prev_stmts.iter().rev().take(2) {
            let Some((def, prev_reads)) = Self::stmt_def_and_reads(symbols, stmt) else {
                continue;
            };
            if !Self::set_contains_loop_var(&tracked, &def) {
                continue;
            }
            if Self::sets_overlap_loop_vars(&prev_reads, cond_vars) {
                return true;
            }
            Self::set_remove_loop_var_aliases(&mut tracked, &def);
            tracked.extend(prev_reads);
        }
        false
    }

    fn stmt_def_and_reads(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: &CStmt,
    ) -> Option<(String, HashSet<String>)> {
        let CStmt::Expr(expr) = stmt.unobserved()
        else {
            return None;
        };
        let CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        } = expr.unobserved()
        else {
            return None;
        };
        let CExpr::Var(def) = left.unobserved() else {
            return None;
        };
        Some((crate::symbol::spelling(symbols, *def).to_string(), Self::collect_expr_vars(symbols, right),
        ))
    }

    fn stmt_assignment_def_reads(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: &CStmt,
    ) -> Option<(String, HashSet<String>, bool, bool)> {
        match stmt.unobserved() {
            CStmt::Expr(expr) => {
                let CExpr::Binary {
                    op: BinaryOp::Assign,
                    left,
                    right,
                } = expr.unobserved()
                else {
                    return None;
                };
                let CExpr::Var(def) = left.unobserved() else {
                    return None;
                };
                Some((
                    crate::symbol::spelling(symbols, *def).to_string(),
                    Self::collect_expr_vars(symbols, right),
                    Self::is_generated_artifact_name(&crate::symbol::spelling(symbols, *def)),
                    crate::fold::op_lower::expr_is_side_effect_free(right),
                ))
            }
            CStmt::Decl {
                name,
                init: Some(init),
                ..
            } => Some((
                crate::symbol::spelling(symbols, *name).to_string(),
                Self::collect_expr_vars(symbols, init),
                Self::is_generated_artifact_name(&crate::symbol::spelling(symbols, *name)),
                crate::fold::op_lower::expr_is_side_effect_free(init),
            )),
            _ => None,
        }
    }

    fn collect_stmt_vars(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: &CStmt,
    ) -> HashSet<String> {
        let mut vars = HashSet::new();
        Self::collect_stmt_vars_into(symbols, stmt, &mut vars);
        vars
    }

    fn collect_stmt_vars_into(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, stmt: &CStmt, out: &mut HashSet<String>,
    ) {
        match stmt {
            CStmt::StructuredRegion { stmt, .. } => {
                Self::collect_stmt_vars_into(symbols, stmt, out)
            }
            CStmt::Observed { stmt, .. } => Self::collect_stmt_vars_into(symbols, stmt, out),
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
                Self::collect_expr_vars_into(symbols, expr, out)
            }
            CStmt::Decl {
                init: Some(init), ..
            } => Self::collect_expr_vars_into(symbols, init, out),
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                Self::collect_expr_vars_into(symbols, cond, out);
                Self::collect_stmt_vars_into(symbols, then_body, out);
                if let Some(else_body) = else_body.as_ref() {
                    Self::collect_stmt_vars_into(symbols, else_body, out);
                }
            }
            CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
                Self::collect_expr_vars_into(symbols, cond, out);
                Self::collect_stmt_vars_into(symbols, body, out);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init.as_ref() {
                    Self::collect_stmt_vars_into(symbols, init, out);
                }
                if let Some(cond) = cond.as_ref() {
                    Self::collect_expr_vars_into(symbols, cond, out);
                }
                if let Some(update) = update.as_ref() {
                    Self::collect_expr_vars_into(symbols, update, out);
                }
                Self::collect_stmt_vars_into(symbols, body, out);
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    Self::collect_stmt_vars_into(symbols, stmt, out);
                }
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                Self::collect_expr_vars_into(symbols, expr, out);
                for case in cases {
                    Self::collect_expr_vars_into(symbols, &case.value, out);
                    for stmt in &case.body {
                        Self::collect_stmt_vars_into(symbols, stmt, out);
                    }
                }
                if let Some(default) = default.as_ref() {
                    for stmt in default {
                        Self::collect_stmt_vars_into(symbols, stmt, out);
                    }
                }
            }
            CStmt::Return(None)
            | CStmt::Decl { init: None, .. }
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Comment(_)
            | CStmt::Empty => {}
        }
    }

    fn collect_expr_vars(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, expr: &CExpr,
    ) -> HashSet<String> {
        let mut vars = HashSet::new();
        Self::collect_expr_vars_into(symbols, expr, &mut vars);
        vars
    }

    fn normalize_loop_expr_refs(expr: &CExpr) -> &CExpr {
        match expr {
            CExpr::Observed { expr, .. } => Self::normalize_loop_expr_refs(expr),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                Self::normalize_loop_expr_refs(inner)
            }
            CExpr::AddrOf(inner) => match inner.as_ref() {
                CExpr::Deref(inner2) => Self::normalize_loop_expr_refs(inner2),
                _ => expr,
            },
            CExpr::Deref(inner) => match inner.as_ref() {
                CExpr::AddrOf(inner2) => Self::normalize_loop_expr_refs(inner2),
                _ => expr,
            },
            _ => expr,
        }
    }

    fn normalize_condition_addr_artifacts(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, expr: CExpr,
    ) -> CExpr {
        match expr {
            CExpr::Observed { id, expr } => {
                CExpr::observed(
                id,
                Self::normalize_condition_addr_artifacts(symbols, *expr))
            }
            // A SymbolId is already the binding identity. Reinterpreting its
            // spelling as another identifier would mint a second binding.
            CExpr::Var(name) => CExpr::Var(name),
            CExpr::Unary { op, operand } => CExpr::Unary {
                op,
                operand: Box::new(Self::normalize_condition_addr_artifacts(symbols, *operand)),
            },
            CExpr::Binary { op, left, right } => CExpr::Binary {
                op,
                left: Box::new(Self::normalize_condition_addr_artifacts(symbols, *left)),
                right: Box::new(Self::normalize_condition_addr_artifacts(symbols, *right)),
            },
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ternary {
                cond: Box::new(Self::normalize_condition_addr_artifacts(symbols, *cond)),
                then_expr: Box::new(Self::normalize_condition_addr_artifacts(symbols, *then_expr,
                )),
                else_expr: Box::new(Self::normalize_condition_addr_artifacts(symbols, *else_expr,
                )),
            },
            CExpr::Cast { ty, expr } => CExpr::Cast {
                ty,
                expr: Box::new(Self::normalize_condition_addr_artifacts(symbols, *expr)),
            },
            CExpr::Call { func, args, site } => CExpr::Call {
                site,
                func: Box::new(Self::normalize_condition_addr_artifacts(symbols, *func)),
                args: args
                    .into_iter()
                    .map(|x| Self::normalize_condition_addr_artifacts(symbols, x))
                    .collect(),
            },
            CExpr::Subscript { base, index } => CExpr::Subscript {
                base: Box::new(Self::normalize_condition_addr_artifacts(symbols, *base)),
                index: Box::new(Self::normalize_condition_addr_artifacts(symbols, *index)),
            },
            CExpr::Member { base, member } => CExpr::Member {
                base: Box::new(Self::normalize_condition_addr_artifacts(symbols, *base)),
                member,
            },
            CExpr::PtrMember { base, member } => CExpr::PtrMember {
                base: Box::new(Self::normalize_condition_addr_artifacts(symbols, *base)),
                member,
            },
            CExpr::Sizeof(inner) => CExpr::Sizeof(Box::new(Self::normalize_condition_addr_artifacts(symbols, *inner),
            )),
            CExpr::AddrOf(inner) => {
                let normalized = Self::normalize_condition_addr_artifacts(symbols, *inner);
                match normalized {
                    CExpr::Deref(inner2) => *inner2,
                    CExpr::Var(name) => CExpr::Var(name),
                    other => CExpr::AddrOf(Box::new(other)),
                }
            }
            CExpr::Deref(inner) => {
                let normalized = Self::normalize_condition_addr_artifacts(symbols, *inner);
                match normalized {
                    CExpr::AddrOf(inner2) => *inner2,
                    other => CExpr::Deref(Box::new(other)),
                }
            }
            CExpr::Comma(values) => CExpr::Comma(
                values
                    .into_iter()
                    .map(|x| Self::normalize_condition_addr_artifacts(symbols, x))
                    .collect(),
            ),
            CExpr::Paren(inner) => CExpr::Paren(Box::new(Self::normalize_condition_addr_artifacts(symbols, *inner),
            )),
            other => other,
        }
    }

    fn collect_expr_vars_into(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, expr: &CExpr, out: &mut HashSet<String>,
    ) {
        match Self::normalize_loop_expr_refs(expr) {
            CExpr::Observed { expr, .. } => Self::collect_expr_vars_into(symbols, expr, out),
            CExpr::Var(name) => {
                out.insert(crate::symbol::spelling(symbols, *name).trim_start_matches('&').to_string(),
                );
            }
            CExpr::External { .. } => {}
            CExpr::AddrOf(inner) | CExpr::Deref(inner) => {
                if let CExpr::Var(name) = Self::normalize_loop_expr_refs(inner) {
                    out.insert(crate::symbol::spelling(symbols, *name).trim_start_matches('&').to_string(),
                    );
                }
                Self::collect_expr_vars_into(symbols, inner, out);
            }
            CExpr::Unary { operand, .. } => Self::collect_expr_vars_into(symbols, operand, out),
            CExpr::Binary { left, right, .. } => {
                Self::collect_expr_vars_into(symbols, left, out);
                Self::collect_expr_vars_into(symbols, right, out);
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                Self::collect_expr_vars_into(symbols, cond, out);
                Self::collect_expr_vars_into(symbols, then_expr, out);
                Self::collect_expr_vars_into(symbols, else_expr, out);
            }
            CExpr::Cast { expr, .. } | CExpr::Paren(expr) | CExpr::Sizeof(expr) => {
                Self::collect_expr_vars_into(symbols, expr, out)
            }
            CExpr::Call { func, args, .. } => {
                Self::collect_expr_vars_into(symbols, func, out);
                for arg in args {
                    Self::collect_expr_vars_into(symbols, arg, out);
                }
            }
            CExpr::Subscript { base, index } => {
                Self::collect_expr_vars_into(symbols, base, out);
                Self::collect_expr_vars_into(symbols, index, out);
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                Self::collect_expr_vars_into(symbols, base, out);
            }
            CExpr::Comma(values) => {
                for value in values {
                    Self::collect_expr_vars_into(symbols, value, out);
                }
            }
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_) => {}
        }
    }

    fn loop_var_base(name: &str) -> &str {
        let name = name.trim_start_matches('&');
        if let Some((base, suffix)) = name.rsplit_once('_')
            && !base.is_empty()
            && suffix.chars().all(|ch| ch.is_ascii_digit())
        {
            return base;
        }
        name
    }

    fn loop_var_equiv(a: &str, b: &str) -> bool {

        if a.eq_ignore_ascii_case(b) {
            return true;
        }
        Self::loop_var_base(a).eq_ignore_ascii_case(Self::loop_var_base(b))
    }

    fn set_contains_loop_var(vars: &HashSet<String>, target: &str) -> bool {

        vars.iter().any(|name| Self::loop_var_equiv(name, target))
    }

    fn sets_overlap_loop_vars(a: &HashSet<String>, b: &HashSet<String>) -> bool {
        a.iter()
            .any(|name| b.iter().any(|other| Self::loop_var_equiv(name, other)))
    }

    fn set_remove_loop_var_aliases(vars: &mut HashSet<String>, target: &str) {
        let to_remove: Vec<String> = vars
            .iter()
            .filter(|name| Self::loop_var_equiv(name, target))
            .cloned()
            .collect();
        for name in to_remove {
            vars.remove(&name);
        }
    }

    /// Flatten single-element blocks.
    fn flatten(stmt: CStmt) -> CStmt {
        let (semantic, observations) = stmt.into_semantic_with_observations();
        match semantic {
            CStmt::Block(mut stmts) if stmts.len() == 1 => {
                observations.reapply(Self::flatten(stmts.remove(0)))
            }
            CStmt::Block(stmts) if stmts.is_empty() => CStmt::Empty,
            other => observations.reapply(other),
        }
    }

    /// Fix B: Remove trailing `continue` from a loop body (it's implicit).
    /// Also remove trailing `break` inside an if-then at the end of a block
    /// if it's the only exit path.
    fn strip_trailing_continue(stmt: CStmt) -> CStmt {
        match stmt {
            CStmt::Observed { id, stmt } => {
                let stripped = Self::strip_trailing_continue(*stmt);
                if matches!(stripped.unobserved(), CStmt::Empty) {
                    CStmt::Empty
                } else {
                    CStmt::observed(id, stripped)
                }
            }
            CStmt::Continue => CStmt::Empty,
            CStmt::Block(mut stmts) => {
                // Remove trailing Continue
                while stmts
                    .last()
                    .is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Continue))
                {
                    stmts.pop();
                }
                if stmts.is_empty() {
                    CStmt::Empty
                } else if stmts.len() == 1 {
                    stmts.remove(0)
                } else {
                    CStmt::Block(stmts)
                }
            }
            other => other,
        }
    }

    /// Remove the implicit terminal edge marker from a post-tested loop body.
    ///
    /// The latch condition owns both the backedge and the exit edge. Region
    /// analysis may classify that exit edge as a `break`, especially when the
    /// latch is also a singleton loop header. Emitting that marker inside the
    /// resulting do-while would force the loop to execute only once.
    fn strip_trailing_latch_marker(stmt: CStmt) -> CStmt {
        match stmt {
            CStmt::Observed { id, stmt } => {
                let stripped = Self::strip_trailing_latch_marker(*stmt);
                if matches!(stripped.unobserved(), CStmt::Empty) {
                    CStmt::Empty
                } else {
                    CStmt::observed(id, stripped)
                }
            }
            CStmt::Break | CStmt::Continue => CStmt::Empty,
            CStmt::Block(mut stmts) => {
                while stmts.last().is_some_and(|stmt| matches!(stmt.unobserved(), CStmt::Break | CStmt::Continue)) {
                    stmts.pop();
                }
                if stmts.is_empty() {
                    CStmt::Empty
                } else if stmts.len() == 1 {
                    stmts.remove(0)
                } else {
                    CStmt::Block(stmts)
                }
            }
            other => other,
        }
    }

    /// Fix C: Convert `do { if (cond) break; body... } while(1)` into
    /// `while(!cond) { body... }`.
    fn try_convert_do_while_to_while(body: CStmt, cond: CExpr) -> CStmt {
        // Only applies when condition is always true (literal 1 or true)
        let is_infinite = match cond.unobserved() {
            CExpr::IntLit(v) => *v != 0,
            _ => false,
        };
        if !is_infinite {
            return CStmt::DoWhile {
                body: Box::new(body),
                cond,
            };
        }

        // Extract the body statements
        let stmts = match body.unobserved() {
            CStmt::Block(stmts) => stmts.clone(),
            CStmt::If { .. } => vec![body.unobserved().clone()],
            _ => {
                return CStmt::DoWhile {
                    body: Box::new(body),
                    cond,
                };
            }
        };

        if stmts.is_empty() {
            return CStmt::DoWhile {
                body: Box::new(body),
                cond,
            };
        }

        // Check if first statement is `if (c) { break; }` (no else)
        if let CStmt::If {
            cond: break_cond,
            then_body,
            else_body: None,
        } = stmts[0].unobserved()
        {
            let is_break = Self::stmt_is_unconditional_break(then_body)
                || matches!(then_body.unobserved(), CStmt::Block(v) if v.len() == 1 && Self::stmt_is_unconditional_break(&v[0]));
            if is_break {
                // Negate the condition
                let negated = CExpr::unary(crate::ast::UnaryOp::Not, break_cond.clone());
                // Remaining body after the break-guard
                let rest: Vec<CStmt> = stmts[1..].to_vec();
                let new_body = if rest.is_empty() {
                    CStmt::Empty
                } else if rest.len() == 1 {
                    rest.into_iter().next().unwrap()
                } else {
                    CStmt::Block(rest)
                };
                return CStmt::While {
                    cond: negated,
                    body: Box::new(new_body),
                };
            }
        }

        CStmt::DoWhile {
            body: Box::new(body),
            cond,
        }
    }
}

// TODO: detect_for_loop() - Planned feature to detect for-loop patterns.
// A for loop has:
// - An initialization before the loop
// - A condition at the loop header
// - An increment at the end of the loop body
// Implementation requires:
// 1. Identify counter variable initialized before header
// 2. Match counter comparison in header condition
// 3. Find counter increment at end of loop body
// 4. Transform WhileLoop region into ForLoop with init/update expressions

// TODO: detect_switch() - Planned feature to simplify nested if-else chains.
// Would analyze condition expressions to detect:
// - Same variable compared against multiple constants
// - Exclusive conditions (no overlap)
// - Convert to switch statement for cleaner output

#[cfg(test)]
mod tests {
    use super::{BDD_FALSE, BDD_TRUE, ControlBdd, ControlFlowStructurer};
    use crate::ast::{
        BinaryOp, CExpr, CFunction, CStmt, CType, RenderObservationOwner, UnaryOp,
        strip_render_observations,
    };
    use crate::fold::FoldingContext;
    use crate::region::Region;
    use crate::structured_region::StructuredRegionKind;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::{BlockTerminator, PhiNode, PredicateId, SSAFunction, SSAOp, SSAVar, SsaArtifact};
    use std::collections::{BTreeSet, HashMap};
    use std::sync::Arc;

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    #[test]
    fn control_bdd_proves_disjoint_duplicated_path_coverage() {
        let mut bdd = ControlBdd::new(64);
        let predicate = PredicateId(0);
        let positive = bdd.variable(predicate, true).expect("positive literal");
        let negative = bdd.variable(predicate, false).expect("negative literal");
        assert_eq!(
            bdd.and(positive, negative).expect("literal intersection"),
            BDD_FALSE
        );
        assert_eq!(bdd.or(positive, negative).expect("literal union"), BDD_TRUE);
    }

    #[test]
    fn control_bdd_projects_repeated_loop_predicates() {
        let mut bdd = ControlBdd::new(64);
        let repeated = PredicateId(0);
        let stable = PredicateId(1);
        let repeated_false = bdd.variable(repeated, false).expect("repeated literal");
        let stable_true = bdd.variable(stable, true).expect("stable literal");
        let path = bdd
            .and(repeated_false, stable_true)
            .expect("path conjunction");

        assert_eq!(
            bdd.exists(path, &BTreeSet::from([repeated]), &mut HashMap::new())
                .expect("existential projection"),
            stable_true
        );
    }

    /// A reference declared in the table the code under test reads, because an
    /// identifier only means something in the table that issued it.
    fn v(symbols: &std::cell::RefCell<crate::symbol::SymbolTable>, name: &str) -> CExpr {
        crate::symbol::var_ref(symbols, name)
    }

    fn expr_stmt(expr: CExpr) -> CStmt {
        CStmt::Expr(expr)
    }

    fn assign(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        lhs: &str,
        rhs: CExpr,
    ) -> CStmt {
        expr_stmt(CExpr::assign(v(symbols, lhs), rhs))
    }

    fn strip_test_observations(
        owner: &RenderObservationOwner,
        stmt: CStmt,
    ) -> (CStmt, crate::ast::ReachableObservations) {
        let mut function = CFunction::new("observed_structure", CType::Int(32))
            .with_body(vec![stmt]);
        let reachable = strip_render_observations(&mut function, owner.expected_count())
            .expect("structure rewrite must retain each observation at most once");
        let stmt = function.body.pop().unwrap_or(CStmt::Empty);
        (stmt, reachable)
    }

    #[test]
    fn loop_condition_prefix_preserves_sequential_effects() {
        let symbols = test_table();
        let load = CExpr::assign(v(&symbols, "byte"), CExpr::Deref(Box::new(v(&symbols, "cursor"))),
        );
        let condition = CExpr::binary(BinaryOp::Ne, v(&symbols, "byte"), CExpr::IntLit(0));

        assert_eq!(
            ControlFlowStructurer::combine_loop_condition_prefix(
                vec![CStmt::Expr(load.clone())],
                condition.clone(),
            ),
            Ok(CExpr::Comma(vec![load, condition]))
        );
    }

    #[test]
    fn observed_loop_condition_prefix_is_transparent_and_survives_once() {
        let symbols = test_table();
        let mut owner = RenderObservationOwner::new();
        let load = CExpr::assign(
            v(&symbols, "byte"),
            CExpr::Deref(Box::new(v(&symbols, "cursor"))),
        );
        let (expr_id, observed_load) = owner
            .observe_expr(load.clone())
            .expect("prefix expression observation");
        let (inner_stmt_id, observed_stmt) = owner
            .observe_stmt(CStmt::Expr(observed_load))
            .expect("inner prefix statement observation");
        let (outer_stmt_id, observed_stmt) = owner
            .observe_stmt(observed_stmt)
            .expect("outer prefix statement observation");
        let condition = CExpr::binary(
            BinaryOp::Ne,
            v(&symbols, "byte"),
            CExpr::IntLit(0));

        let combined = ControlFlowStructurer::combine_loop_condition_prefix(
            vec![observed_stmt],
            condition.clone(),
        )
        .expect("observation metadata must not reject a valid loop prefix");
        let (plain, reachable) = strip_test_observations(
            &owner,
            CStmt::while_loop(combined, CStmt::Empty));

        assert!(reachable.contains(outer_stmt_id));
        assert!(reachable.contains(inner_stmt_id));
        assert!(reachable.contains(expr_id));
        assert_eq!(
            plain,
            CStmt::while_loop(CExpr::Comma(vec![load, condition]), CStmt::Empty)
        );
    }

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("RDI", 0x10, 8));
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        arch
    }

    #[test]
    fn production_structurer_seals_every_emitted_region_anchor() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0x00, 8),
            src: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let func = SSAFunction::from_blocks_with_arch(&[block], Some(&test_arch()))
            .expect("single-block SSA function");
        let ctx = FoldingContext::new(64);
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);

        let body = structurer
            .structure_with_regions()
            .expect("production structured body");
        let mut visited = Vec::new();
        body.visit_occurrences(|occurrence| {
            visited.push((
                occurrence.id(),
                occurrence.anchor(),
                occurrence.node().entry(),
                occurrence.node().kind(),
            ));
        });

        assert_eq!(visited.len(), body.regions().nodes().len());
        assert_eq!(visited[0].2, 0x1000);
        assert_eq!(visited[0].3, StructuredRegionKind::FunctionBody);
        for (id, anchor, entry, kind) in visited {
            let (resolved_id, node) = body
                .regions()
                .node_for_anchor(body.regions().authority(), anchor)
                .expect("emitted anchor resolves in the exact sealed artifact");
            assert_eq!(resolved_id, id);
            assert_eq!(node.entry(), entry);
            assert_eq!(node.kind(), kind);
        }
    }

    #[test]
    fn region_markers_are_transparent_to_structurer_cleanup() {
        for func in [
            function_with_switch_block_and_unrelated_sub(),
            function_with_terminating_if_and_shared_merge(),
            function_with_guarded_latch_loop_and_shared_exit(),
        ] {
            let plain_ctx = FoldingContext::new(64);
            let mut plain_structurer = ControlFlowStructurer::new(&func, &plain_ctx);
            let plain = plain_structurer
                .structure_preserving_render_proof_identity_impl()
                .expect("plain production structure");
            assert!(plain_structurer.safety_reason().is_none());
            let plain = ControlFlowStructurer::cleanup(&plain_ctx.symbols, plain);

            let mut marked_ctx = FoldingContext::new(64);
            marked_ctx.symbols = std::rc::Rc::clone(&plain_ctx.symbols);
            let mut marked_structurer = ControlFlowStructurer::new(&func, &marked_ctx);
            let marked = marked_structurer
                .structure_with_regions()
                .expect("marked production structure")
                .into_stmt();
            assert!(marked_structurer.safety_reason().is_none());

            assert_eq!(
                marked, plain,
                "region metadata must not alter the cleaned semantic AST at 0x{:x}",
                func.entry
            );
        }
    }

    fn function_with_switch_block_and_unrelated_sub() -> SSAFunction {
        let mut switch_block = R2ILBlock::new(0x1000, 4);
        switch_block.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(1, 8),
        });
        switch_block.push(R2ILOp::BranchInd {
            target: Varnode::register(0x10, 8),
        });
        switch_block.set_switch_info(r2il::SwitchInfo {
            switch_addr: 0x1000,
            min_val: 0,
            max_val: 2,
            default_target: None,
            cases: vec![
                r2il::SwitchCase {
                    value: 0,
                    target: 0x1010,
                },
                r2il::SwitchCase {
                    value: 1,
                    target: 0x1020,
                },
                r2il::SwitchCase {
                    value: 2,
                    target: 0x1030,
                },
            ],
        });

        let mut case_zero = R2ILBlock::new(0x1010, 4);
        case_zero.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut case_one = R2ILBlock::new(0x1020, 4);
        case_one.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });
        let mut case_two = R2ILBlock::new(0x1030, 4);
        case_two.push(R2ILOp::Return {
            target: Varnode::constant(2, 8),
        });

        SSAFunction::from_blocks_with_arch(
            &[switch_block, case_zero, case_one, case_two],
            Some(&test_arch()),
        )
        .expect("ssa function")
        .with_name("switch_unrelated_sub_demo")
    }

    fn function_with_transparent_branch_to_merge() -> SSAFunction {
        let mut branch = R2ILBlock::new(0x1000, 4);
        branch.push(R2ILOp::Copy {
            dst: Varnode::unique(0x2000, 1),
            src: Varnode::unique(0x1000, 1),
        });
        branch.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });

        let mut value_pred = R2ILBlock::new(0x1010, 4);
        value_pred.push(R2ILOp::Copy {
            dst: Varnode::register(0x00, 8),
            src: Varnode::constant(7, 8),
        });
        value_pred.push(R2ILOp::Branch {
            target: Varnode::constant(0x1020, 8),
        });

        let mut merge = R2ILBlock::new(0x1020, 4);
        merge.push(R2ILOp::Return {
            target: Varnode::register(0x00, 8),
        });

        SSAFunction::from_blocks_with_arch(&[branch, value_pred, merge], Some(&test_arch()))
            .expect("ssa function")
            .with_name("transparent_branch_demo")
    }

    fn function_with_materialized_phi_branch_to_merge() -> SSAFunction {
        let mut func = function_with_transparent_branch_to_merge();
        let source = SSAVar::new("x8", 1, 8);
        let destination = SSAVar::new("x8", 2, 8);
        let branch = func.get_block_mut(0x1000).expect("branch block");
        let branch_index = branch.ops.len().saturating_sub(1);
        branch.ops.insert(
            branch_index,
            SSAOp::Copy {
                dst: destination.clone(),
                src: source.clone(),
            },
        );
        func.get_block_mut(0x1010)
            .expect("phi successor")
            .phis
            .push(PhiNode {
                dst: destination,
                sources: vec![(0x1000, source)],
                canonical_storage: None,
            });
        func
    }

    fn function_with_terminating_if_and_shared_merge() -> SSAFunction {
        let mut cond = R2ILBlock::new(0x1000, 4);
        cond.push(R2ILOp::IntEqual {
            dst: Varnode::register(0x80, 1),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(0, 8),
        });
        cond.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1010, 8),
            cond: Varnode::register(0x80, 1),
        });

        let mut false_block = R2ILBlock::new(0x1004, 4);
        false_block.push(R2ILOp::Return {
            target: Varnode::constant(2, 8),
        });

        let mut true_block = R2ILBlock::new(0x1010, 4);
        true_block.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });

        let mut merge = R2ILBlock::new(0x1020, 4);
        merge.push(R2ILOp::Return {
            target: Varnode::constant(99, 8),
        });

        SSAFunction::from_blocks_with_arch(
            &[cond, false_block, true_block, merge],
            Some(&test_arch()),
        )
        .expect("ssa function")
        .with_name("terminating_if_merge_demo")
    }

    fn function_with_guarded_latch_loop_and_shared_exit() -> SSAFunction {
        let mut entry = R2ILBlock::new(0x1000, 0x13);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::register(0x80, 1),
            target: Varnode::constant(0x1044, 8),
        });

        let mut preheader = R2ILBlock::new(0x1013, 0x0d);
        preheader.push(R2ILOp::Branch {
            target: Varnode::constant(0x1020, 8),
        });

        let mut header = R2ILBlock::new(0x1020, 0x11);
        header.push(R2ILOp::Branch {
            target: Varnode::constant(0x1031, 8),
        });

        let mut latch = R2ILBlock::new(0x1031, 0x13);
        latch.push(R2ILOp::CBranch {
            cond: Varnode::register(0x88, 1),
            target: Varnode::constant(0x1020, 8),
        });

        let mut exit = R2ILBlock::new(0x1044, 1);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut func = SSAFunction::from_blocks_with_arch(
            &[entry, preheader, header, latch, exit],
            Some(&test_arch()),
        )
        .expect("ssa function")
        .with_name("guarded_latch_loop_demo");
        func.cfg_mut().set_terminator(
            0x1000,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1044,
                false_target: 0x1013,
            },
        );
        func.cfg_mut()
            .set_terminator(0x1013, BlockTerminator::Branch { target: 0x1020 });
        func.cfg_mut()
            .set_terminator(0x1020, BlockTerminator::Branch { target: 0x1031 });
        func.cfg_mut().set_terminator(
            0x1031,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1020,
                false_target: 0x1044,
            },
        );
        func.refresh_after_cfg_mutation();
        func
    }

    fn stmt_contains_loop(stmt: &CStmt) -> bool {
        match stmt {
            CStmt::While { .. } | CStmt::For { .. } | CStmt::DoWhile { .. } => true,
            CStmt::Block(stmts) => stmts.iter().any(stmt_contains_loop),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                stmt_contains_loop(then_body)
                    || else_body.as_deref().is_some_and(stmt_contains_loop)
            }
            CStmt::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|case| case.body.iter().any(stmt_contains_loop))
                    || default
                        .as_ref()
                        .is_some_and(|body| body.iter().any(stmt_contains_loop))
            }
            _ => false,
        }
    }

    fn first_switch_case_values(stmt: &CStmt) -> Option<Vec<i64>> {
        match stmt {
            CStmt::Switch { cases, .. } => Some(
                cases
                    .iter()
                    .map(|case| match &case.value {
                        CExpr::IntLit(value) => *value,
                        other => panic!("expected literal switch case, got {other:?}"),
                    })
                    .collect(),
            ),
            CStmt::Block(stmts) => stmts.iter().find_map(first_switch_case_values),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => first_switch_case_values(then_body)
                .or_else(|| else_body.as_deref().and_then(first_switch_case_values)),
            CStmt::While { body, .. } | CStmt::For { body, .. } | CStmt::DoWhile { body, .. } => {
                first_switch_case_values(body)
            }
            _ => None,
        }
    }

    #[test]
    fn switch_render_keeps_canonical_case_values_despite_unrelated_sub() {
        let func = function_with_switch_block_and_unrelated_sub();
        let ctx = FoldingContext::new(64);
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let cases = vec![
            (Some(0), Box::new(Region::Block(0x1010))),
            (Some(1), Box::new(Region::Block(0x1020))),
            (Some(2), Box::new(Region::Block(0x1030))),
        ];

        let rendered = structurer
            .structure_switch_region(0x1000, &cases, None, None)
            .expect("supported switch lowering");
        let values = first_switch_case_values(&rendered).expect("rendered switch");

        assert_eq!(
            values,
            vec![0, 1, 2],
            "switch rendering must not bias canonical case values from nearby arithmetic"
        );
    }

    #[test]
    fn cleanup_rewrites_pure_if_else_returns_to_ternary_return() {
        let symbols = test_table();
        let input = CStmt::If {
            cond: CExpr::binary(BinaryOp::Eq, v(&symbols, "b"), CExpr::IntLit(0)),
            then_body: Box::new(CStmt::Return(Some(CExpr::IntLit(-1)))),
            else_body: Some(Box::new(CStmt::Return(Some(CExpr::binary(
                BinaryOp::Div,
                v(&symbols, "a"),
                v(&symbols, "b"),
            ))))),
        };

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::Return(Some(CExpr::Ternary {
                cond: Box::new(CExpr::binary(BinaryOp::Eq, v(&symbols, "b"), CExpr::IntLit(0))),
                then_expr: Box::new(CExpr::IntLit(-1)),
                else_expr: Box::new(CExpr::binary(BinaryOp::Div, v(&symbols, "a"), v(&symbols, "b"))),
            }))
        );
    }

    #[test]
    fn merge_predecessor_follows_transparent_branch_only_region() {
        let func = function_with_transparent_branch_to_merge();
        let ctx = FoldingContext::new(64);
        let structurer = ControlFlowStructurer::new(&func, &ctx);

        assert_eq!(
            structurer.unique_region_predecessor_to_merge(&Region::Block(0x1000), 0x1020),
            Some(0x1010)
        );
    }

    #[test]
    fn merge_predecessor_rejects_phi_shaped_copy_without_normalization_origin() {
        let func = function_with_materialized_phi_branch_to_merge();
        let ctx = FoldingContext::new(64);
        let structurer = ControlFlowStructurer::new(&func, &ctx);

        assert_eq!(
            structurer.unique_region_predecessor_to_merge(&Region::Block(0x1000), 0x1020),
            None
        );
    }

    #[test]
    fn merged_return_synthesis_does_not_clone_source_occurrence_observations() {
        let symbols = test_table();
        let mut owner = RenderObservationOwner::new();
        let (merged_id, merged) = owner
            .observe_expr(CExpr::IntLit(1))
            .expect("merged source occurrence");
        let source_stmt = CStmt::Block(vec![
            assign(&symbols, "acc", merged.clone()),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ]);
        let plain_stmt = CStmt::Block(vec![
            assign(&symbols, "acc", CExpr::IntLit(1)),
            CStmt::Return(Some(CExpr::IntLit(0))),
        ]);

        let func = function_with_switch_block_and_unrelated_sub();
        let ctx = FoldingContext::new(64);
        let structurer = ControlFlowStructurer::new(&func, &ctx);
        let rewritten = structurer
            .rewrite_trailing_return_with_merged_expr(&source_stmt, &merged)
            .expect("trailing return rewrite");
        let plain = structurer
            .rewrite_trailing_return_with_merged_expr(&plain_stmt, &CExpr::IntLit(1))
            .expect("plain trailing return rewrite");
        let (stripped, reachable) = strip_test_observations(&owner, rewritten);

        assert!(
            reachable.contains(merged_id),
            "the source assignment must retain its exact observation"
        );
        assert_eq!(stripped, plain);
    }

    #[test]
    fn structurer_accepts_only_producer_issued_phi_edge_origin() {
        let mut entry = R2ILBlock::new(0x2000, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::Branch {
            target: Varnode::constant(0x2004, 8),
        });
        let mut header = R2ILBlock::new(0x2004, 4);
        header.push(R2ILOp::CBranch {
            cond: Varnode::register(0x10, 8),
            target: Varnode::constant(0x200c, 8),
        });
        let mut latch = R2ILBlock::new(0x2008, 4);
        latch.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(1, 8),
        });
        latch.push(R2ILOp::Branch {
            target: Varnode::constant(0x2004, 8),
        });
        let mut exit = R2ILBlock::new(0x200c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut arch = test_arch();
        arch.addr_size = 8;
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2dec-structure-normalization-owner".to_vec(),
            "sysv64",
            std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .expect("exact test interface");
        let prepared = Arc::new(
            SsaArtifact::for_decompile_with_interface(
                &[entry, header, latch, exit],
                Some(&arch),
                interface,
            )
            .expect("loop SSA artifact"),
        );
        let analysis = r2types::build_source_owned_type_writeback_analysis(
            r2types::TypeWritebackAnalysisRequest::new(
                Arc::clone(&prepared),
                r2types::ParsedExternalContext::default(),
            )
            .expect("matching source assumptions"),
        )
        .expect("source-owned loop analysis");
        let render_facts = analysis.function_facts().render_facts();
        let (normalized, origins) = crate::normalize::materialize_certified_loop_carriers(
            prepared.function(),
            prepared.as_ref(),
            render_facts,
        )
        .expect("producer-issued loop normalization origins");
        origins
            .validate(&normalized, prepared.as_ref(), Some(render_facts))
            .expect("producer-issued origins seal against source authority");
        let (block_addr, op_idx, successor) = prepared
            .graph()
            .block_order
            .iter()
            .find_map(|block_id| {
                let block_addr = prepared.graph().block(*block_id)?.addr;
                normalized
                    .get_block(block_addr)?
                    .ops
                    .iter()
                    .enumerate()
                    .find_map(|(op_idx, _)| {
                        match origins.origin(
                        crate::normalize::NormalizedOpSite {
                            block: *block_id,
                            op_idx,
                        }) {
                        Some(crate::normalize::NormalizedOpOrigin::PhiEdgeCopy(origin))
                            if origin.guarded.is_none() =>
                        {
                            Some((block_addr, op_idx, origin.target))
                        }
                        _ => None,
                    }
                    })
            })
            .expect("loop normalization emits an unconditional phi-edge copy");

        let mut ctx = FoldingContext::new(64);
        ctx.inputs.prepared_ssa = Some(prepared.as_ref());
        ctx.inputs.normalization_origins = Some(&origins);
        let structurer = ControlFlowStructurer::new(&normalized, &ctx);
        assert!(
            structurer.is_materialized_phi_edge_copy(block_addr, op_idx, successor),
            "the structurer must consume the exact producer-issued occurrence"
        );
    }

    #[test]
    fn transparent_transfer_path_rejects_phi_shaped_copy_without_normalization_origin() {
        let mut forwarder = R2ILBlock::new(0x1000, 4);
        forwarder.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut func = SSAFunction::from_blocks_with_arch(
            &[forwarder, R2ILBlock::new(0x1010, 4)],
            Some(&test_arch()),
        )
        .expect("ssa function");
        let source = SSAVar::new("x8", 1, 8);
        let destination = SSAVar::new("x8", 2, 8);
        let branch = func.get_block_mut(0x1000).expect("forwarder block");
        let branch_index = branch.ops.len().saturating_sub(1);
        branch.ops.insert(
            branch_index,
            SSAOp::Copy {
                dst: destination.clone(),
                src: source.clone(),
            },
        );
        func.get_block_mut(0x1010)
            .expect("phi target")
            .phis
            .push(PhiNode {
                dst: destination,
                sources: vec![(0x1000, source)],
                canonical_storage: None,
            });
        let ctx = FoldingContext::new(64);
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        structurer.structured_region_blocks.insert(0x1010);

        assert!(
            structurer.transparent_transfer_path(0x1000).is_err(),
            "an SSA copy shaped like a phi edge is not transformation evidence"
        );
    }

    #[test]
    fn terminating_if_else_does_not_append_unreachable_merge_block() {
        let func = function_with_terminating_if_and_shared_merge();
        let ctx = FoldingContext::new(64);
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let region = Region::IfThenElse {
            cond_block: 0x1000,
            then_region: Box::new(Region::Block(0x1010)),
            else_region: Some(Box::new(Region::Block(0x1004))),
            merge_block: Some(0x1020),
        };

        let stmt = structurer
            .structure_region(&region)
            .expect("supported terminating branch lowering");
        let rendered = format!("{stmt:?}");

        assert!(
            !rendered.contains("IntLit(99)") && !rendered.contains("UIntLit(99)"),
            "terminating branches must not render the shared merge as fallthrough: {rendered}"
        );
        assert!(
            ControlFlowStructurer::stmt_guarantees_termination(&stmt),
            "structured if/else should still be terminating: {stmt:?}"
        );
    }

    #[test]
    fn do_while_render_proof_uses_body_entry_as_loop_anchor() {
        let mut header = R2ILBlock::new(0x1000, 4);
        header.push(R2ILOp::Branch {
            target: Varnode::constant(0x1004, 8),
        });
        let mut latch = R2ILBlock::new(0x1004, 4);
        latch.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1000, 8),
            cond: Varnode::register(0x80, 1),
        });
        let mut exit = R2ILBlock::new(0x1008, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func =
            SSAFunction::from_blocks_with_arch(&[header, latch, exit], Some(&test_arch()))
                .expect("ssa function");
        func.cfg_mut()
            .set_terminator(0x1000, BlockTerminator::Branch { target: 0x1004 });
        func.cfg_mut().set_terminator(
            0x1004,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1000,
                false_target: 0x1008,
            },
        );
        let ctx = FoldingContext::new(64);
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let region = Region::DoWhileLoop {
            body: Box::new(Region::Sequence(vec![
                Region::Block(0x1000),
                Region::Block(0x1004),
            ])),
            cond_block: 0x1004,
        };

        let _ = structurer.structure_region(&region);

        assert_eq!(structurer.control_render_proofs()[0].anchor, 0x1000);
        assert_eq!(
            structurer.control_render_proofs()[0].loop_latches,
            vec![0x1004]
        );
    }

    #[test]
    fn post_test_loop_removes_implicit_latch_break() {
        let symbols = test_table();
        let body = CStmt::Block(vec![assign(&symbols, "hash", v(&symbols, "next_hash")), CStmt::Break,
        ]);

        let stripped = ControlFlowStructurer::strip_trailing_latch_marker(body);

        assert_eq!(stripped, assign(&symbols, "hash", v(&symbols, "next_hash")));
    }

    #[test]
    fn merge_metadata_does_not_own_block_emission() {
        let region = Region::IfThenElse {
            cond_block: 0x1000,
            then_region: Box::new(Region::Block(0x1010)),
            else_region: None,
            merge_block: Some(0x1020),
        };

        assert!(ControlFlowStructurer::region_owns_block_emission(
            &region, 0x1000
        ));
        assert!(ControlFlowStructurer::region_owns_block_emission(
            &region, 0x1010
        ));
        assert!(!ControlFlowStructurer::region_owns_block_emission(
            &region, 0x1020
        ));
    }

    #[test]
    fn guarded_latch_loop_with_shared_exit_keeps_loop_construct() {
        let func = function_with_guarded_latch_loop_and_shared_exit();
        let ctx = FoldingContext::new(64);
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);

        let stmt = structurer.structure().expect("supported loop lowering");

        assert!(
            stmt_contains_loop(&stmt),
            "guarded latch-form loop must remain structured, got {stmt:?}; reason={:?}",
            structurer.safety_reason()
        );
    }

    #[test]
    fn rewrites_canonical_while_to_for() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), CExpr::IntLit(10)),
                CStmt::Block(vec![
                    assign(&symbols, "sum", CExpr::binary(BinaryOp::Add, v(&symbols, "sum"), v(&symbols, "i")),
                    ),
                    assign(&symbols, "i", CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
                    ),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::For {
            init,
            cond,
            update,
            body,
        } = cleaned
        else {
            panic!("Expected canonical loop rewrite to produce CStmt::For");
        };
        assert!(init.is_some(), "for-loop should keep init statement");
        assert!(cond.is_some(), "for-loop should keep loop condition");
        assert!(
            update.is_some(),
            "for-loop should extract update expression"
        );
        assert!(
            !matches!(*body, CStmt::Empty),
            "for-loop body should retain side-effect statements"
        );
    }

    #[test]
    fn rewrites_continue_tail_update_to_shared_for_latch() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            CStmt::Block(vec![
                assign(&symbols, "count", CExpr::IntLit(0)),
                assign(&symbols, "i", CExpr::IntLit(0)),
            ]),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), v(&symbols, "n")),
                CStmt::Block(vec![
                    assign(&symbols, 
                        "c",
                        CExpr::Subscript {
                            base: Box::new(v(&symbols, "buf")),
                            index: Box::new(v(&symbols, "i")),
                        },
                    ),
                    CStmt::if_stmt(
                        CExpr::binary(BinaryOp::Ne, v(&symbols, "c"), v(&symbols, "a")),
                        CStmt::Block(vec![
                            CStmt::if_stmt(
                                CExpr::binary(BinaryOp::Eq, v(&symbols, "c"), v(&symbols, "b")),
                                assign(&symbols, 
                                    "count",
                                    CExpr::binary(BinaryOp::Add, v(&symbols, "count"), CExpr::IntLit(1),
                                    ),
                                ),
                                None,
                            ),
                            assign(&symbols, "i", CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
                            ),
                            CStmt::Continue,
                        ]),
                        None,
                    ),
                    assign(&symbols, 
                        "count",
                        CExpr::binary(BinaryOp::Add, v(&symbols, "count"), CExpr::IntLit(1)),
                    ),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected count init plus for-loop block, got {cleaned:?}");
        };
        let CStmt::For {
            update: Some(update),
            body,
            ..
        } = stmts.get(1).expect("for-loop")
        else {
            panic!("Expected continue-tail loop rewrite to produce CStmt::For, got {stmts:?}");
        };
        assert_eq!(
            update,
            &CExpr::binary(BinaryOp::AddAssign, v(&symbols, "i"), CExpr::IntLit(1))
        );
        let CStmt::Block(body_stmts) = body.as_ref() else {
            panic!("Expected for body block, got {body:?}");
        };
        assert!(
            !body_stmts
                .iter()
                .any(|stmt| matches!(stmt, CStmt::Continue)),
            "shared latch rewrite should remove synthetic continue"
        );
        assert_eq!(
            body_stmts.get(1),
            Some(&CStmt::if_stmt(
                CExpr::binary(
                    BinaryOp::Or,
                    CExpr::binary(BinaryOp::Eq, v(&symbols, "c"), v(&symbols, "a")),
                    CExpr::binary(BinaryOp::Eq, v(&symbols, "c"), v(&symbols, "b"))
                ),
                CStmt::Expr(CExpr::binary(
                    BinaryOp::AddAssign,
                    v(&symbols, "count"),
                    CExpr::IntLit(1),
                )),
                None
            )),
            "fallthrough suffix with duplicate effect should become a single OR guard"
        );
    }

    #[test]
    fn rewrites_nested_else_duplicate_effect_to_or_condition() {
        let symbols = test_table();
        let increment = expr_stmt(CExpr::Unary {
            op: UnaryOp::PostInc,
            operand: Box::new(v(&symbols, "count")),
        });
        let input = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Ne, v(&symbols, "c"), v(&symbols, "a")),
            CStmt::if_stmt(
                CExpr::binary(BinaryOp::Eq, v(&symbols, "c"), v(&symbols, "b")),
                increment.clone(),
                None,
            ),
            Some(increment.clone()),
        );

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(
                CExpr::binary(
                    BinaryOp::Or,
                    CExpr::binary(BinaryOp::Eq, v(&symbols, "c"), v(&symbols, "a")),
                    CExpr::binary(BinaryOp::Eq, v(&symbols, "c"), v(&symbols, "b"))
                ),
                increment,
                None
            )
        );
    }

    #[test]
    fn rewrites_continue_tail_with_common_suffix_before_shared_latch() {
        let symbols = test_table();
        let hash_xor = assign(&symbols, "hash", CExpr::binary(BinaryOp::BitXor, v(&symbols, "c"), v(&symbols, "hash")),
        );
        let hash_mul = assign(&symbols, 
            "hash",
            CExpr::binary(BinaryOp::Mul, v(&symbols, "hash"), CExpr::UIntLit(0x100000001b3),
            ),
        );
        let i_update = assign(&symbols, "i", CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
        );
        let lowercase_update = CStmt::Expr(CExpr::binary(
            BinaryOp::AddAssign,
            v(&symbols, "c"),
            CExpr::IntLit(32),
        ));

        let input = CStmt::Block(vec![
            assign(&symbols, "hash", CExpr::UIntLit(0x14650fb0739d0383)),
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), v(&symbols, "n")),
                CStmt::Block(vec![
                    assign(&symbols, 
                        "c",
                        CExpr::Subscript {
                            base: Box::new(v(&symbols, "buf")),
                            index: Box::new(v(&symbols, "i")),
                        },
                    ),
                    CStmt::if_stmt(
                        CExpr::binary(BinaryOp::Gt, v(&symbols, "c"), CExpr::IntLit(64)),
                        CStmt::Block(vec![
                            CStmt::if_stmt(
                                CExpr::binary(BinaryOp::Le, v(&symbols, "c"), CExpr::IntLit(90)),
                                lowercase_update.clone(),
                                None,
                            ),
                            hash_xor.clone(),
                            hash_mul.clone(),
                            i_update.clone(),
                            assign(&symbols, "value_1", v(&symbols, "c")),
                            CStmt::Continue,
                        ]),
                        None,
                    ),
                    hash_xor.clone(),
                    hash_mul.clone(),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected hash init plus for-loop block, got {cleaned:?}");
        };
        let CStmt::For {
            update: Some(update),
            body,
            ..
        } = stmts.get(1).expect("for-loop")
        else {
            panic!("Expected loop rewrite to produce CStmt::For, got {stmts:?}");
        };
        assert_eq!(
            update,
            &CExpr::binary(BinaryOp::AddAssign, v(&symbols, "i"), CExpr::IntLit(1))
        );

        let CStmt::Block(body_stmts) = body.as_ref() else {
            panic!("Expected for body block, got {body:?}");
        };
        assert!(
            !body_stmts
                .iter()
                .any(ControlFlowStructurer::stmt_contains_control_transfer),
            "factored loop body should not keep synthetic continue"
        );
        assert_eq!(
            body_stmts.get(1),
            Some(&CStmt::if_stmt(
                CExpr::binary(
                    BinaryOp::And,
                    CExpr::binary(BinaryOp::Gt, v(&symbols, "c"), CExpr::IntLit(64)),
                    CExpr::binary(BinaryOp::Le, v(&symbols, "c"), CExpr::IntLit(90)),
                ),
                lowercase_update,
                None
            )),
            "only the lowercase transform should remain guarded"
        );
        assert_eq!(
            body_stmts.get(2),
            Some(&CStmt::Expr(CExpr::binary(
                BinaryOp::BitXorAssign,
                v(&symbols, "hash"),
                v(&symbols, "c")
            )))
        );
        assert_eq!(
            body_stmts.get(3),
            Some(&CStmt::Expr(CExpr::binary(
                BinaryOp::MulAssign,
                v(&symbols, "hash"),
                CExpr::UIntLit(0x100000001b3)
            )))
        );
    }

    #[test]
    fn removes_duplicate_body_update_owned_by_for_latch() {
        let symbols = test_table();
        let i_update_expr = CExpr::binary(
            BinaryOp::Assign,
            v(&symbols, "i"),
            CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
        );
        let hash_update = assign(&symbols, "hash", CExpr::binary(BinaryOp::BitXor, v(&symbols, "c"), v(&symbols, "hash")),
        );
        let input = CStmt::For {
            init: Some(Box::new(assign(&symbols, "i", CExpr::IntLit(0)))),
            cond: Some(CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), v(&symbols, "n"),
            )),
            update: Some(i_update_expr.clone()),
            body: Box::new(CStmt::Block(vec![
                hash_update.clone(),
                CStmt::Expr(i_update_expr.clone()),
            ])),
        };

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::For { body, .. } = cleaned else {
            panic!("Expected for-loop, got {cleaned:?}");
        };
        assert_eq!(
            body.as_ref(),
            &CStmt::Expr(CExpr::binary(BinaryOp::BitXorAssign, v(&symbols, "hash"), v(&symbols, "c"))),
            "for latch update should own the duplicated trailing body update"
        );
    }

    #[test]
    fn observed_rhs_still_rewrites_to_compound_assignment_once() {
        let symbols = test_table();
        let mut owner = RenderObservationOwner::new();
        let (read_id, read) = owner
            .observe_expr(v(&symbols, "value"))
            .expect("self-read observation");
        let (retained_id, retained) = owner
            .observe_expr(CExpr::IntLit(5))
            .expect("retained operand observation");
        let (rhs_id, rhs) = owner
            .observe_expr(CExpr::binary(BinaryOp::Shl, read, retained))
            .expect("rhs observation");
        let rewritten = ControlFlowStructurer::rewrite_compound_assignment_expr(
            &symbols,
            CExpr::assign(v(&symbols, "value"), rhs),
        );

        assert_eq!(
            rewritten,
            CExpr::observed(
                rhs_id,
                CExpr::binary(
                    BinaryOp::ShlAssign,
                    CExpr::observed(read_id, v(&symbols, "value")),
                    CExpr::observed(retained_id, CExpr::IntLit(5)),
                ),
            )
        );
        assert_eq!(
            ControlFlowStructurer::normalized_self_update_signature(&symbols, &rewritten),
            Some((
                "value".to_string(),
                BinaryOp::ShlAssign,
                CExpr::IntLit(5),
            ))
        );

        let (plain, reachable) =
            strip_test_observations(&owner, CStmt::Expr(rewritten));
        assert!(reachable.contains(read_id));
        assert!(reachable.contains(retained_id));
        assert!(reachable.contains(rhs_id));
        assert_eq!(
            plain,
            CStmt::Expr(CExpr::binary(
                BinaryOp::ShlAssign,
                v(&symbols, "value"),
                CExpr::IntLit(5),
            ))
        );
    }

    #[test]
    fn observed_loop_init_condition_and_update_survive_for_recognition_once() {
        let symbols = test_table();
        let mut owner = RenderObservationOwner::new();
        let (init_id, init) = owner
            .observe_stmt(assign(&symbols, "i", CExpr::IntLit(0)))
            .expect("loop init observation");
        let (cond_id, cond) = owner
            .observe_expr(CExpr::binary(
                BinaryOp::Lt,
                v(&symbols, "i"),
                v(&symbols, "n"),
            ))
            .expect("loop condition observation");
        let (update_id, update) = owner
            .observe_expr(CExpr::binary(
                BinaryOp::Assign,
                v(&symbols, "i"),
                CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
            ))
            .expect("loop update observation");
        let input = CStmt::Block(vec![
            init,
            CStmt::while_loop(
                cond,
                CStmt::Block(vec![
                    assign(&symbols, "sum", v(&symbols, "i")),
                    CStmt::Expr(update),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let (plain, reachable) = strip_test_observations(&owner, cleaned);
        assert!(reachable.contains(init_id));
        assert!(reachable.contains(cond_id));
        assert!(reachable.contains(update_id));
        assert!(matches!(plain, CStmt::For { .. }));
    }

    #[test]
    fn for_recognition_preserves_only_positional_observations() {
        let symbols = test_table();
        let prefix = assign(&symbols, "sum", CExpr::IntLit(0));
        let init = assign(&symbols, "i", CExpr::IntLit(0));
        let cond = CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), v(&symbols, "n"));
        let work = assign(&symbols, "sum", v(&symbols, "i"));
        let update = CExpr::assign(
            v(&symbols, "i"),
            CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
        );
        let plain = ControlFlowStructurer::rewrite_block_loops_to_for(
            &symbols,
            vec![
                CStmt::Block(vec![prefix.clone(), init.clone()]),
                CStmt::while_loop(
                    cond.clone(),
                    CStmt::Block(vec![work.clone(), CStmt::Expr(update.clone())]),
                ),
            ],
        );

        let mut owner = RenderObservationOwner::new();
        let (prefix_id, prefix) = owner.observe_stmt(prefix).expect("prefix observation");
        let (init_id, init) = owner.observe_stmt(init).expect("init observation");
        let (preheader_id, preheader) = owner
            .observe_stmt(CStmt::Block(vec![prefix, init]))
            .expect("preheader block observation");
        let (cond_id, cond) = owner.observe_expr(cond).expect("condition observation");
        let (work_id, work) = owner.observe_stmt(work).expect("body observation");
        let (update_id, update) = owner.observe_expr(update).expect("update observation");
        let (body_id, body) = owner
            .observe_stmt(CStmt::Block(vec![work, CStmt::Expr(update)]))
            .expect("body block observation");
        let (while_id, while_stmt) = owner
            .observe_stmt(CStmt::while_loop(cond, body))
            .expect("while observation");
        let marked = ControlFlowStructurer::rewrite_block_loops_to_for(
            &symbols,
            vec![preheader, while_stmt],
        );
        let (stripped, reachable) =
            strip_test_observations(&owner, CStmt::Block(marked));

        for id in [prefix_id, init_id, cond_id, work_id, update_id] {
            assert!(reachable.contains(id), "exact child occurrence was lost");
        }
        for id in [preheader_id, body_id, while_id] {
            assert!(
                !reachable.contains(id),
                "eliminated control wrapper was relocated onto the for-loop"
            );
        }
        assert_eq!(stripped, CStmt::Block(plain));
    }

    #[test]
    fn split_hoisted_block_observations_remain_unaccounted_without_shape_changes() {
        let symbols = test_table();
        let first = assign(&symbols, "x", CExpr::IntLit(1));
        let second = assign(&symbols, "y", CExpr::IntLit(2));
        let plain_input = CStmt::if_stmt(
            v(&symbols, "ready"),
            CStmt::Block(vec![first.clone(), second.clone()]),
            Some(CStmt::ret(Some(CExpr::IntLit(0)))),
        );
        let plain = ControlFlowStructurer::cleanup(&symbols, plain_input);

        let mut owner = RenderObservationOwner::new();
        let (first_id, first) = owner
            .observe_stmt(first)
            .expect("first hoisted statement observation");
        let (second_id, second) = owner
            .observe_stmt(second)
            .expect("second hoisted statement observation");
        let (inner_block_id, body) = owner
            .observe_stmt(CStmt::Block(vec![first, second]))
            .expect("inner body observation");
        let (outer_block_id, body) = owner.observe_stmt(body).expect("outer body observation");
        let marked = ControlFlowStructurer::cleanup(
            &symbols,
            CStmt::if_stmt(
                v(&symbols, "ready"),
                body,
                Some(CStmt::ret(Some(CExpr::IntLit(0)))),
            ),
        );

        let (stripped, reachable) = strip_test_observations(&owner, marked);
        for id in [first_id, second_id] {
            assert!(reachable.contains(id));
        }
        for id in [inner_block_id, outer_block_id] {
            assert!(
                !reachable.contains(id),
                "a split block has no exact child occurrence that can inherit its marker"
            );
        }
        assert_eq!(
            stripped, plain,
            "outer metadata must not turn a flattened hoisted body back into a nested block"
        );
    }

    #[test]
    fn split_for_body_observations_remain_unaccounted_without_shape_changes() {
        let symbols = test_table();
        let update = CExpr::assign(
            v(&symbols, "i"),
            CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
        );
        let first_work = assign(&symbols, "sum", v(&symbols, "i"));
        let second_work = assign(&symbols, "hash", v(&symbols, "byte"));
        let dead_generated = assign(&symbols, "tmp:dead", CExpr::IntLit(9));
        let plain_input = CStmt::Block(vec![
            CStmt::For {
                init: None,
                cond: Some(CExpr::binary(
                    BinaryOp::Lt,
                    v(&symbols, "i"),
                    v(&symbols, "n"),
                )),
                update: Some(update.clone()),
                body: Box::new(CStmt::Block(vec![
                    first_work.clone(),
                    CStmt::Expr(update.clone()),
                ])),
            },
            CStmt::For {
                init: None,
                cond: Some(v(&symbols, "keep_going")),
                update: None,
                body: Box::new(CStmt::Block(vec![
                    second_work.clone(),
                    dead_generated.clone(),
                ])),
            },
        ]);
        let plain = ControlFlowStructurer::cleanup(&symbols, plain_input);

        let mut owner = RenderObservationOwner::new();
        let (first_work_id, first_work) = owner
            .observe_stmt(first_work)
            .expect("first loop work observation");
        let (first_body_inner_id, first_body) = owner
            .observe_stmt(CStmt::Block(vec![first_work, CStmt::Expr(update.clone())]))
            .expect("first loop body observation");
        let (first_body_outer_id, first_body) = owner
            .observe_stmt(first_body)
            .expect("outer first loop body observation");
        let (second_work_id, second_work) = owner
            .observe_stmt(second_work)
            .expect("second loop work observation");
        let (second_body_inner_id, second_body) = owner
            .observe_stmt(CStmt::Block(vec![second_work, dead_generated]))
            .expect("second loop body observation");
        let (second_body_outer_id, second_body) = owner
            .observe_stmt(second_body)
            .expect("outer second loop body observation");
        let marked = ControlFlowStructurer::cleanup(
            &symbols,
            CStmt::Block(vec![
                CStmt::For {
                    init: None,
                    cond: Some(CExpr::binary(
                        BinaryOp::Lt,
                        v(&symbols, "i"),
                        v(&symbols, "n"),
                    )),
                    update: Some(update),
                    body: Box::new(first_body),
                },
                CStmt::For {
                    init: None,
                    cond: Some(v(&symbols, "keep_going")),
                    update: None,
                    body: Box::new(second_body),
                },
            ]),
        );

        let (stripped, reachable) = strip_test_observations(&owner, marked);
        for id in [first_work_id, second_work_id] {
            assert!(reachable.contains(id));
        }
        for id in [
            first_body_inner_id,
            first_body_outer_id,
            second_body_inner_id,
            second_body_outer_id,
        ] {
            assert!(
                !reachable.contains(id),
                "a split loop body has no exact child occurrence that can inherit its marker"
            );
        }
        assert_eq!(
            stripped, plain,
            "statement decomposition must be transparent to for-body cleanup"
        );
    }

    #[test]
    fn observed_terminators_classify_transparently_and_trailing_markers_are_deleted() {
        let symbols = test_table();
        let mut owner = RenderObservationOwner::new();
        let (return_id, observed_return) = owner
            .observe_stmt(CStmt::ret(Some(CExpr::IntLit(3))))
            .expect("return observation");
        assert!(ControlFlowStructurer::stmt_guarantees_termination(
            &observed_return
        ));
        let extracted = ControlFlowStructurer::single_terminator_stmt(&CStmt::Block(vec![
            observed_return]))
        .expect("observed terminator must classify through its wrapper");

        let (body_id, body_stmt) = owner
            .observe_stmt(assign(&symbols, "x", CExpr::IntLit(1)))
            .expect("loop body observation");
        let (continue_id, trailing_continue) = owner
            .observe_stmt(CStmt::Continue)
            .expect("continue observation");
        let stripped_continue = ControlFlowStructurer::strip_trailing_continue(CStmt::Block(vec![
            body_stmt,
            trailing_continue,
        ]));
        let (break_id, trailing_break) = owner
            .observe_stmt(CStmt::Break)
            .expect("latch marker observation");
        let stripped_latch =
            ControlFlowStructurer::strip_trailing_latch_marker(trailing_break);

        let (plain, reachable) = strip_test_observations(
            &owner,
            CStmt::Block(vec![extracted, stripped_continue, stripped_latch]),
        );
        assert!(reachable.contains(return_id));
        assert!(reachable.contains(body_id));
        assert!(!reachable.contains(continue_id));
        assert!(!reachable.contains(break_id));
        assert!(matches!(plain, CStmt::Block(_)));
    }

    #[test]
    fn single_item_block_extraction_keeps_only_the_child_observation() {
        let mut owner = RenderObservationOwner::new();
        let (return_id, return_stmt) = owner
            .observe_stmt(CStmt::ret(Some(CExpr::IntLit(3))))
            .expect("return observation");
        let (return_block_id, return_block) = owner
            .observe_stmt(CStmt::Block(vec![return_stmt]))
            .expect("return block observation");
        let extracted_return =
            ControlFlowStructurer::single_terminator_stmt(&return_block).expect("terminator");

        let switch = CStmt::Switch {
            expr: CExpr::IntLit(0),
            cases: Vec::new(),
            default: None,
        };
        let (switch_id, switch_stmt) = owner
            .observe_stmt(switch.clone())
            .expect("switch observation");
        let (switch_block_id, switch_block) = owner
            .observe_stmt(CStmt::Block(vec![switch_stmt]))
            .expect("switch block observation");
        let extracted_switch =
            ControlFlowStructurer::single_switch_stmt(&switch_block).expect("switch");

        let (plain, reachable) = strip_test_observations(
            &owner,
            CStmt::Block(vec![extracted_return, extracted_switch]),
        );
        assert!(reachable.contains(return_id));
        assert!(reachable.contains(switch_id));
        assert!(!reachable.contains(return_block_id));
        assert!(!reachable.contains(switch_block_id));
        assert_eq!(
            plain,
            CStmt::Block(vec![CStmt::ret(Some(CExpr::IntLit(3))), switch])
        );
    }

    #[test]
    fn flattened_empty_block_observation_remains_unaccounted() {
        let mut owner = RenderObservationOwner::new();
        let (block_id, block) = owner
            .observe_stmt(CStmt::Block(Vec::new()))
            .expect("empty block observation");
        let flattened = ControlFlowStructurer::flatten(block);
        let (plain, reachable) = strip_test_observations(&owner, flattened);

        assert_eq!(plain, CStmt::Empty);
        assert!(!reachable.contains(block_id));
    }

    #[test]
    fn direct_and_block_do_while_guards_preserve_only_the_surviving_condition() {
        let symbols = test_table();
        let infinite = CExpr::IntLit(1);

        let mut direct_owner = RenderObservationOwner::new();
        let (direct_cond_id, direct_cond) = direct_owner
            .observe_expr(v(&symbols, "stop"))
            .expect("direct condition observation");
        let (direct_if_id, direct_if) = direct_owner
            .observe_stmt(CStmt::if_stmt(direct_cond, CStmt::Break, None))
            .expect("direct guard observation");
        let direct = ControlFlowStructurer::try_convert_do_while_to_while(
            direct_if,
            infinite.clone());
        let (direct_plain, direct_reachable) =
            strip_test_observations(&direct_owner, direct);

        let mut block_owner = RenderObservationOwner::new();
        let (block_cond_id, block_cond) = block_owner
            .observe_expr(v(&symbols, "stop"))
            .expect("block condition observation");
        let (block_if_id, block_if) = block_owner
            .observe_stmt(CStmt::if_stmt(block_cond, CStmt::Break, None))
            .expect("block guard observation");
        let (block_body_id, block_body) = block_owner
            .observe_stmt(CStmt::Block(vec![block_if]))
            .expect("block body observation");
        let block = ControlFlowStructurer::try_convert_do_while_to_while(block_body, infinite);
        let (block_plain, block_reachable) = strip_test_observations(&block_owner, block);

        assert_eq!(direct_plain, block_plain);
        assert!(direct_reachable.contains(direct_cond_id));
        assert!(block_reachable.contains(block_cond_id));
        assert!(!direct_reachable.contains(direct_if_id));
        assert!(!block_reachable.contains(block_if_id));
        assert!(!block_reachable.contains(block_body_id));
    }

    #[test]
    fn rewrites_side_effect_free_assignments_to_compound_assignments() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "hash", CExpr::binary(BinaryOp::BitXor, v(&symbols, "c"), v(&symbols, "hash")),
            ),
            assign(&symbols, 
                "hash",
                CExpr::binary(BinaryOp::Mul, v(&symbols, "hash"), CExpr::UIntLit(0x100000001b3),
                ),
            ),
            assign(&symbols, 
                "hash",
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Call {
                        func: Box::new(v(&symbols, "next")),
                        args: Vec::new(),
                        site: None,
                    },
                    v(&symbols, "hash"),
                ),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected block, got {cleaned:?}");
        };
        assert_eq!(
            stmts[0],
            CStmt::Expr(CExpr::binary(BinaryOp::BitXorAssign, v(&symbols, "hash"), v(&symbols, "c")))
        );
        assert_eq!(
            stmts[1],
            CStmt::Expr(CExpr::binary(
                BinaryOp::MulAssign,
                v(&symbols, "hash"),
                CExpr::UIntLit(0x100000001b3)
            ))
        );
        assert!(
            matches!(
                &stmts[2],
                CStmt::Expr(CExpr::Binary {
                    op: BinaryOp::Assign,
                    ..
                })
            ),
            "side-effecting operands should not be reordered into compound assignments"
        );
    }

    #[test]
    fn removes_dead_trailing_returns_inside_switch_cases() {
        let symbols = test_table();
        let input = CStmt::Switch {
            expr: v(&symbols, "op"),
            cases: vec![crate::ast::SwitchCase {
                value: CExpr::IntLit(0),
                body: vec![
                    CStmt::Return(Some(CExpr::IntLit(1))),
                    CStmt::Return(Some(CExpr::IntLit(2))),
                ],
            }],
            default: Some(vec![
                CStmt::Return(Some(CExpr::IntLit(3))),
                CStmt::Return(Some(CExpr::IntLit(4))),
            ]),
        };

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Switch { cases, default, .. } = cleaned else {
            panic!("Expected switch, got {cleaned:?}");
        };
        assert_eq!(cases[0].body, vec![CStmt::Return(Some(CExpr::IntLit(1)))]);
        assert_eq!(default, Some(vec![CStmt::Return(Some(CExpr::IntLit(3)))]));
    }

    #[test]
    fn rewrites_guard_break_while1_to_for() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::IntLit(1),
                CStmt::Block(vec![
                    CStmt::if_stmt(
                        CExpr::binary(BinaryOp::Ge, v(&symbols, "i"), v(&symbols, "n")),
                        CStmt::Break,
                        None,
                    ),
                    assign(&symbols, "sum", CExpr::binary(BinaryOp::Add, v(&symbols, "sum"), v(&symbols, "i")),
                    ),
                    expr_stmt(CExpr::Unary {
                        op: UnaryOp::PostInc,
                        operand: Box::new(v(&symbols, "i")),
                    }),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::For {
            cond: Some(cond),
            update: Some(update),
            ..
        } = cleaned
        else {
            panic!("Expected guarded while(1) rewrite to produce CStmt::For");
        };
        assert!(
            matches!(
                cond,
                CExpr::Unary {
                    op: UnaryOp::Not,
                    ..
                }
            ),
            "guard-break form should negate break condition for for-loop cond"
        );
        assert!(
            matches!(
                update,
                CExpr::Unary {
                    op: UnaryOp::PostInc,
                    ..
                }
            ),
            "guard-break form should preserve update expression"
        );
    }

    #[test]
    fn does_not_rewrite_without_tail_update() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), CExpr::IntLit(10)),
                CStmt::Block(vec![assign(&symbols, 
                    "sum",
                    CExpr::binary(BinaryOp::Add, v(&symbols, "sum"), CExpr::IntLit(1)),
                )]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected unmatched loop to remain a block");
        };
        assert!(
            matches!(stmts.get(1), Some(CStmt::While { .. })),
            "loop without a recognized update should remain while-loop"
        );
    }

    #[test]
    fn does_not_rewrite_when_cond_var_mismatch() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v(&symbols, "j"), CExpr::IntLit(10)),
                CStmt::Block(vec![assign(&symbols, 
                    "i",
                    CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
                )]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected unmatched condition var to remain a block");
        };
        assert!(
            matches!(stmts.get(1), Some(CStmt::While { .. })),
            "condition must reference same induction variable as init/update"
        );
    }

    #[test]
    fn accepts_self_assign_update_forms() {
        let symbols = test_table();
        let updates = vec![
            CExpr::binary(
                BinaryOp::Assign,
                v(&symbols, "i"),
                CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(2)),
            ),
            CExpr::binary(BinaryOp::AddAssign, v(&symbols, "i"), CExpr::IntLit(2)),
            CExpr::binary(
                BinaryOp::Assign,
                v(&symbols, "i"),
                CExpr::call(v(&symbols, "next_i"), vec![v(&symbols, "i"), v(&symbols, "x")],
                ),
            ),
        ];

        for update_expr in updates {
            let input = CStmt::Block(vec![
                assign(&symbols, "i", CExpr::IntLit(0)),
                CStmt::while_loop(
                    CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), v(&symbols, "n")),
                    CStmt::Block(vec![
                        assign(&symbols, "sum", CExpr::binary(BinaryOp::Add, v(&symbols, "sum"), v(&symbols, "i")),
                        ),
                        expr_stmt(update_expr.clone()),
                    ]),
                ),
            ]);

            let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
            let CStmt::For {
                update: Some(update),
                ..
            } = cleaned
            else {
                panic!("Expected loop rewrite for accepted self-assign update form");
            };
            assert!(
                ControlFlowStructurer::expr_matches_for_update(&symbols, &update, &update_expr),
                "Expected canonical loop update {update:?} to match source update {update_expr:?}"
            );
        }
    }

    #[test]
    fn rewrites_for_loop_past_generated_trailing_value_carrier() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            CStmt::Block(vec![
                assign(&symbols, "sum", CExpr::IntLit(0)),
                assign(&symbols, "i", CExpr::IntLit(0)),
            ]),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), v(&symbols, "len")),
                CStmt::Block(vec![
                    CStmt::Expr(CExpr::binary(
                        BinaryOp::AddAssign,
                        v(&symbols, "sum"),
                        CExpr::Subscript {
                            base: Box::new(v(&symbols, "arr")),
                            index: Box::new(v(&symbols, "i")),
                        },
                    )),
                    CStmt::Expr(CExpr::Unary {
                        op: UnaryOp::PostInc,
                        operand: Box::new(v(&symbols, "i")),
                    }),
                    CStmt::Decl {
                        name: crate::symbol::declare(&symbols, "tmp:11f00_4"),
                        ty: CType::i32(),
                        init: Some(CExpr::Deref(Box::new(CExpr::binary(
                            BinaryOp::Add,
                            v(&symbols, "arr"),
                            CExpr::binary(BinaryOp::Mul, v(&symbols, "i"), CExpr::IntLit(4)),
                        )))),
                    },
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected block with sum init and for-loop, got {cleaned:?}");
        };
        assert!(
            matches!(
                stmts.get(1),
                Some(CStmt::For {
                    update: Some(CExpr::Unary {
                        op: UnaryOp::PostInc,
                        ..
                    }),
                    ..
                })
            ),
            "generated trailing value carrier should not own loop update: {stmts:?}"
        );
    }

    #[test]
    fn generated_artifact_name_uses_typed_temporary_kind() {
        assert!(ControlFlowStructurer::is_generated_artifact_name(
            "tmp:11f00_4"
        ));
        assert!(ControlFlowStructurer::is_generated_artifact_name(
            "TMP:11f00_4"
        ));
        assert!(ControlFlowStructurer::is_generated_artifact_name(
            "unique:12_0"
        ));
        assert!(ControlFlowStructurer::is_generated_artifact_name("value_1"));
        assert!(!ControlFlowStructurer::is_generated_artifact_name(
            "sha_state"
        ));
    }

    #[test]
    fn rewrites_nested_if_without_else_to_short_circuit_and() {
        let symbols = test_table();
        let input = CStmt::if_stmt(
            v(&symbols, "a"),
            CStmt::if_stmt(v(&symbols, "b"), CStmt::ret(Some(CExpr::IntLit(1))), None),
            None,
        );

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(
                CExpr::binary(BinaryOp::And, v(&symbols, "a"), v(&symbols, "b")),
                CStmt::ret(Some(CExpr::IntLit(1))),
                None
            )
        );
    }

    #[test]
    fn rewrites_if_else_if_same_body_to_short_circuit_or() {
        let symbols = test_table();
        let body = assign(&symbols, "x", CExpr::IntLit(1));
        let input = CStmt::if_stmt(
            v(&symbols, "a"),
            body.clone(),
            Some(CStmt::if_stmt(v(&symbols, "b"), body.clone(), None)),
        );

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(CExpr::binary(BinaryOp::Or, v(&symbols, "a"), v(&symbols, "b")), body, None)
        );
    }

    #[test]
    fn short_circuit_rewrite_keeps_only_positionally_surviving_observations() {
        let symbols = test_table();
        let body = assign(&symbols, "x", CExpr::IntLit(1));
        let plain_input = CStmt::if_stmt(
            v(&symbols, "a"),
            body.clone(),
            Some(CStmt::if_stmt(v(&symbols, "b"), body.clone(), None)),
        );
        let plain = ControlFlowStructurer::cleanup(&symbols, plain_input);

        let mut owner = RenderObservationOwner::new();
        let (left_cond_id, left_cond) = owner
            .observe_expr(v(&symbols, "a"))
            .expect("left condition observation");
        let (left_body_id, left_body) = owner
            .observe_stmt(body.clone())
            .expect("surviving body observation");
        let (right_cond_id, right_cond) = owner
            .observe_expr(v(&symbols, "b"))
            .expect("right condition observation");
        let (right_body_id, right_body) = owner
            .observe_stmt(body)
            .expect("eliminated duplicate body observation");
        let (inner_if_id, inner_if) = owner
            .observe_stmt(CStmt::if_stmt(right_cond, right_body, None))
            .expect("inner if observation");
        let (outer_if_id, marked_input) = owner
            .observe_stmt(CStmt::if_stmt(left_cond, left_body, Some(inner_if)))
            .expect("outer if observation");
        let marked = ControlFlowStructurer::cleanup(&symbols, marked_input);
        let (stripped, reachable) = strip_test_observations(&owner, marked);

        for id in [left_cond_id, right_cond_id, left_body_id, outer_if_id] {
            assert!(reachable.contains(id), "exact surviving occurrence was lost");
        }
        for id in [right_body_id, inner_if_id] {
            assert!(
                !reachable.contains(id),
                "eliminated nested occurrence was relocated onto the outer if"
            );
        }
        assert_eq!(stripped, plain);
    }

    #[test]
    fn rewrites_shared_else_nested_if_to_short_circuit_and() {
        let symbols = test_table();
        let then_stmt = assign(&symbols, "x", CExpr::IntLit(1));
        let else_stmt = assign(&symbols, "x", CExpr::IntLit(2));
        let input = CStmt::if_stmt(
            v(&symbols, "a"),
            CStmt::if_stmt(v(&symbols, "b"), then_stmt.clone(), Some(else_stmt.clone())),
            Some(else_stmt.clone()),
        );

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(
                CExpr::binary(BinaryOp::And, v(&symbols, "a"), v(&symbols, "b")),
                then_stmt,
                Some(else_stmt)
            )
        );
    }

    #[test]
    fn negates_less_equal_with_canonical_less_than_orientation() {
        let symbols = test_table();
        assert_eq!(
            ControlFlowStructurer::negate_condition(CExpr::binary(
                BinaryOp::Le,
                v(&symbols, "limit"),
                v(&symbols, "index"),
            )),
            CExpr::binary(BinaryOp::Lt, v(&symbols, "index"), v(&symbols, "limit"))
        );
    }

    #[test]
    fn inverts_if_else_terminator_and_flattens_then_block() {
        let symbols = test_table();
        let input = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Lt, v(&symbols, "x"), v(&symbols, "limit")),
            CStmt::Block(vec![
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v(&symbols, "sum"), v(&symbols, "x"),
                )),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v(&symbols, "x"), CExpr::IntLit(1),
                )),
            ]),
            Some(CStmt::ret(Some(CExpr::IntLit(0)))),
        );

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::if_stmt(
                    CExpr::binary(BinaryOp::Ge, v(&symbols, "x"), v(&symbols, "limit")),
                    CStmt::ret(Some(CExpr::IntLit(0))),
                    None
                ),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v(&symbols, "sum"), v(&symbols, "x"))),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v(&symbols, "x"), CExpr::IntLit(1),)),
            ])
        );
    }

    #[test]
    fn inverts_if_then_terminator_and_flattens_else_block() {
        let symbols = test_table();
        let input = CStmt::if_stmt(
            v(&symbols, "is_error"),
            CStmt::ret(Some(CExpr::IntLit(-1))),
            Some(CStmt::Block(vec![
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v(&symbols, "sum"), v(&symbols, "x"),
                )),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v(&symbols, "x"), CExpr::IntLit(1),
                )),
            ])),
        );

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::if_stmt(v(&symbols, "is_error"), CStmt::ret(Some(CExpr::IntLit(-1))), None),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v(&symbols, "sum"), v(&symbols, "x"))),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v(&symbols, "x"), CExpr::IntLit(1),)),
            ])
        );
    }

    #[test]
    fn rewrites_trailing_return_guard_and_flattens_then_block() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            CStmt::if_stmt(
                v(&symbols, "ready"),
                CStmt::Block(vec![
                    assign(&symbols, "x", CExpr::IntLit(1)),
                    assign(&symbols, "y", CExpr::IntLit(2)),
                ]),
                None,
            ),
            CStmt::ret(Some(CExpr::IntLit(0))),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::if_stmt(
                    CExpr::unary(UnaryOp::Not, v(&symbols, "ready")),
                    CStmt::ret(Some(CExpr::IntLit(0))),
                    None
                ),
                assign(&symbols, "x", CExpr::IntLit(1)),
                assign(&symbols, "y", CExpr::IntLit(2)),
                CStmt::ret(Some(CExpr::IntLit(0))),
            ])
        );
    }

    #[test]
    fn guarded_tail_rewrite_preserves_children_without_relocating_the_split_if() {
        let symbols = test_table();
        let mut owner = RenderObservationOwner::new();
        let (cond_id, cond) = owner
            .observe_expr(v(&symbols, "ready"))
            .expect("condition observation");
        let (body_id, body) = owner
            .observe_stmt(assign(&symbols, "x", CExpr::IntLit(1)))
            .expect("body observation");
        let (return_id, terminator) = owner
            .observe_stmt(CStmt::ret(Some(CExpr::IntLit(0))))
            .expect("terminator observation");
        let (if_id, guarded) = owner
            .observe_stmt(CStmt::if_stmt(cond, body, None))
            .expect("split if observation");
        let cleaned = ControlFlowStructurer::cleanup(
            &symbols,
            CStmt::Block(vec![guarded, terminator]));

        let (plain, reachable) = strip_test_observations(&owner, cleaned);
        assert!(reachable.contains(cond_id));
        assert!(reachable.contains(body_id));
        assert!(reachable.contains(return_id));
        assert!(
            !reachable.contains(if_id),
            "a split if has no exact output statement that owns its marker"
        );
        assert_eq!(
            plain,
            CStmt::Block(vec![
                CStmt::if_stmt(
                    CExpr::unary(UnaryOp::Not, v(&symbols, "ready")),
                    CStmt::ret(Some(CExpr::IntLit(0))),
                    None,
                ),
                assign(&symbols, "x", CExpr::IntLit(1)),
                CStmt::ret(Some(CExpr::IntLit(0))),
            ])
        );
    }

    #[test]
    fn common_suffix_factoring_does_not_merge_distinct_occurrence_observations() {
        let symbols = test_table();
        let suffix = assign(&symbols, "hash", v(&symbols, "c"));
        let mut owner = RenderObservationOwner::new();
        let (then_id, then_suffix) = owner
            .observe_stmt(suffix.clone())
            .expect("then suffix observation");
        let (else_id, else_suffix) = owner
            .observe_stmt(suffix.clone())
            .expect("else suffix observation");

        let factored = ControlFlowStructurer::factor_guarded_common_suffix(
            v(&symbols, "guard"),
            vec![then_suffix],
            vec![else_suffix],
        );
        let (plain, reachable) =
            strip_test_observations(&owner, CStmt::Block(factored));
        assert!(!reachable.contains(then_id));
        assert!(!reachable.contains(else_id));
        assert_eq!(plain, CStmt::Block(vec![suffix]));
    }

    #[test]
    fn does_not_rewrite_trailing_guard_when_following_stmt_is_not_terminator() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            CStmt::if_stmt(v(&symbols, "ready"), assign(&symbols, "x", CExpr::IntLit(1)), None,
            ),
            assign(&symbols, "y", CExpr::IntLit(2)),
        ]);
        let cleaned = ControlFlowStructurer::cleanup(&symbols, input.clone());
        assert_eq!(cleaned, input);
    }

    #[test]
    fn does_not_invert_if_when_both_branches_are_terminators() {
        let symbols = test_table();
        let input = CStmt::if_stmt(
            v(&symbols, "a"),
            CStmt::ret(Some(CExpr::IntLit(1))),
            Some(CStmt::ret(Some(CExpr::IntLit(0)))),
        );
        let cleaned = ControlFlowStructurer::cleanup(&symbols, input.clone());
        assert_eq!(cleaned, input);
    }

    #[test]
    fn does_not_invert_if_when_else_is_not_terminator() {
        let symbols = test_table();
        let input = CStmt::if_stmt(
            v(&symbols, "a"),
            assign(&symbols, "x", CExpr::IntLit(1)),
            Some(assign(&symbols, "x", v(&symbols, "b"))),
        );
        let cleaned = ControlFlowStructurer::cleanup(&symbols, input.clone());
        assert_eq!(cleaned, input);
    }

    #[test]
    fn inverts_if_when_else_is_single_terminator() {
        let symbols = test_table();
        let input = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Lt, v(&symbols, "x"), v(&symbols, "limit")),
            assign(&symbols, "sum", CExpr::binary(BinaryOp::Add, v(&symbols, "sum"), v(&symbols, "x")),
            ),
            Some(CStmt::ret(Some(CExpr::IntLit(0)))),
        );

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected condition inversion to emit block sequence");
        };
        assert_eq!(
            stmts[0],
            CStmt::if_stmt(
                CExpr::binary(BinaryOp::Ge, v(&symbols, "x"), v(&symbols, "limit")),
                CStmt::ret(Some(CExpr::IntLit(0))),
                None
            )
        );
    }

    #[test]
    fn removes_empty_else_branch() {
        let symbols = test_table();
        let input = CStmt::if_stmt(v(&symbols, "a"), assign(&symbols, "x", CExpr::IntLit(1)), Some(CStmt::Empty),
        );
        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(v(&symbols, "a"), assign(&symbols, "x", CExpr::IntLit(1)), None)
        );
    }

    #[test]
    fn removes_empty_if_without_else() {
        let symbols = test_table();
        let input = CStmt::if_stmt(v(&symbols, "a"), CStmt::Empty, None);
        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(cleaned, CStmt::Empty);
    }

    #[test]
    fn constant_true_if_collapses_to_then_body() {
        let symbols = test_table();
        let input = CStmt::if_stmt(CExpr::IntLit(1), assign(&symbols, "x", CExpr::IntLit(7)), None,
        );
        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(cleaned, assign(&symbols, "x", CExpr::IntLit(7)));
    }

    #[test]
    fn observed_constant_condition_collapses_and_drops_only_deleted_occurrences() {
        let symbols = test_table();
        let mut owner = RenderObservationOwner::new();
        let (cond_id, cond) = owner
            .observe_expr(CExpr::IntLit(1))
            .expect("constant condition observation");
        let (then_id, then_stmt) = owner
            .observe_stmt(assign(&symbols, "x", CExpr::IntLit(7)))
            .expect("surviving branch observation");
        let (else_id, else_stmt) = owner
            .observe_stmt(assign(&symbols, "x", CExpr::IntLit(9)))
            .expect("deleted branch observation");

        let cleaned = ControlFlowStructurer::cleanup(
            &symbols,
            CStmt::if_stmt(cond, then_stmt, Some(else_stmt)),
        );
        let (plain, reachable) = strip_test_observations(&owner, cleaned);
        assert!(!reachable.contains(cond_id));
        assert!(reachable.contains(then_id));
        assert!(!reachable.contains(else_id));
        assert_eq!(plain, assign(&symbols, "x", CExpr::IntLit(7)));
    }

    #[test]
    fn constant_false_if_collapses_to_else_body() {
        let symbols = test_table();
        let input = CStmt::if_stmt(
            CExpr::IntLit(0),
            assign(&symbols, "x", CExpr::IntLit(7)),
            Some(assign(&symbols, "x", CExpr::IntLit(9))),
        );
        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(cleaned, assign(&symbols, "x", CExpr::IntLit(9)));
    }

    #[test]
    fn guarded_switch_with_trailing_return_becomes_switch_default() {
        let symbols = test_table();
        let input = CStmt::Block(vec![CStmt::if_stmt(
            v(&symbols, "guard"),
            CStmt::Block(vec![
                expr_stmt(CExpr::call(
                    v(&symbols, "sym.imp.printf"),
                    vec![CExpr::StringLit("bad".into())],
                )),
                CStmt::ret(Some(CExpr::IntLit(1))),
            ]),
            Some(CStmt::Block(vec![
                CStmt::Switch {
                    expr: v(&symbols, "selector"),
                    cases: vec![crate::ast::SwitchCase {
                        value: CExpr::IntLit(1),
                        body: vec![assign(&symbols, "x", CExpr::IntLit(1)), CStmt::Break],
                    }],
                    default: None,
                },
                CStmt::ret(Some(CExpr::IntLit(0))),
            ])),
        )]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::Switch {
                    expr: v(&symbols, "selector"),
                    cases: vec![crate::ast::SwitchCase {
                        value: CExpr::IntLit(1),
                        body: vec![assign(&symbols, "x", CExpr::IntLit(1)), CStmt::Break],
                    }],
                    default: Some(vec![CStmt::Block(vec![
                        expr_stmt(CExpr::call(
                            v(&symbols, "sym.imp.printf"),
                            vec![CExpr::StringLit("bad".into())],
                        )),
                        CStmt::ret(Some(CExpr::IntLit(1))),
                    ])]),
                },
                CStmt::ret(Some(CExpr::IntLit(0))),
            ])
        );
    }

    #[test]
    fn selector_expr_from_condition_extracts_non_constant_side() {
        let symbols = test_table();
        let cond = CExpr::binary(
            BinaryOp::Eq,
            CExpr::binary(BinaryOp::BitAnd, v(&symbols, "i"), CExpr::IntLit(7)),
            CExpr::IntLit(0),
        );

        let selector = ControlFlowStructurer::selector_expr_from_condition(&cond)
            .expect("selector expression");
        assert_eq!(
            selector,
            CExpr::binary(BinaryOp::BitAnd, v(&symbols, "i"), CExpr::IntLit(7))
        );
    }

    #[test]
    fn rewrites_while_to_for_when_condition_uses_addrof_induction_var() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, CExpr::AddrOf(Box::new(v(&symbols, "i"))), v(&symbols, "n"),
                ),
                CStmt::Block(vec![
                    assign(&symbols, "sum", CExpr::binary(BinaryOp::Add, v(&symbols, "sum"), v(&symbols, "i")),
                    ),
                    assign(&symbols, "i", CExpr::binary(BinaryOp::Add, v(&symbols, "i"), CExpr::IntLit(1)),
                    ),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert!(
            matches!(cleaned, CStmt::For { .. }),
            "Address-wrapped induction variable should still allow for-loop rewrite"
        );
    }

    #[test]
    fn normalizes_addrof_var_artifact_in_while_condition_without_rewrite() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, CExpr::AddrOf(Box::new(v(&symbols, "local"))), v(&symbols, "n"),
                ),
                CStmt::Block(vec![assign(&symbols, 
                    "sum",
                    CExpr::binary(BinaryOp::Add, v(&symbols, "sum"), CExpr::IntLit(1)),
                )]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected unmatched loop to remain a block");
        };
        let Some(CStmt::While { cond, .. }) = stmts.get(1) else {
            panic!("Expected second statement to remain a while-loop");
        };
        match cond {
            CExpr::Binary { left, .. } => {
                assert!(
                    matches!(left.as_ref(), CExpr::Var(name) if &*crate::symbol::spelling(&symbols, *name) == "local"),
                    "Address-of local artifact should normalize to plain variable in condition"
                );
            }
            other => panic!(
                "Unexpected condition shape after normalization: {:?}",
                other
            ),
        }
    }

    #[test]
    fn rewrites_while_to_for_with_two_step_alias_update_chain() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), v(&symbols, "n")),
                CStmt::Block(vec![
                    assign(&symbols, "tmp1", v(&symbols, "i")),
                    assign(&symbols, "tmp2", v(&symbols, "tmp1")),
                    assign(&symbols, 
                        "i",
                        CExpr::binary(BinaryOp::Add, v(&symbols, "tmp2"), CExpr::IntLit(1)),
                    ),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert!(
            matches!(cleaned, CStmt::For { .. }),
            "Two-step alias chain should be enough to connect update with loop condition"
        );
    }

    #[test]
    fn does_not_rewrite_while_to_for_when_alias_chain_is_too_long() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v(&symbols, "i"), v(&symbols, "n")),
                CStmt::Block(vec![
                    assign(&symbols, "tmp1", v(&symbols, "i")),
                    assign(&symbols, "tmp2", v(&symbols, "tmp1")),
                    assign(&symbols, "tmp3", v(&symbols, "tmp2")),
                    assign(&symbols, 
                        "i",
                        CExpr::binary(BinaryOp::Add, v(&symbols, "tmp3"), CExpr::IntLit(1)),
                    ),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected long alias-chain loop to remain a block");
        };
        assert!(
            matches!(stmts.get(1), Some(CStmt::While { .. })),
            "Alias chain beyond bounded lookback should not rewrite to for-loop"
        );
    }

    #[test]
    fn rewrites_while_to_for_when_condition_uses_suffix_equivalent_var_name() {
        let symbols = test_table();
        let input = CStmt::Block(vec![
            assign(&symbols, "local_4", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, CExpr::AddrOf(Box::new(v(&symbols, "local"))), v(&symbols, "n"),
                ),
                CStmt::Block(vec![assign(&symbols, 
                    "local_4",
                    CExpr::binary(BinaryOp::Add, v(&symbols, "local_4"), CExpr::IntLit(1)),
                )]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(&symbols, input);
        assert!(
            matches!(cleaned, CStmt::For { .. }),
            "Suffix-equivalent loop vars (local/local_4) should be treated as matching"
        );
    }
}
