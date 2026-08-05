//! Control flow structuring.
//!
//! This module converts unstructured control flow (gotos, CFG edges) into
//! structured high-level constructs (if-then-else, while, for, etc.).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use r2ssa::cfg::BlockTerminator;
use r2ssa::{CFGEdge, ControlGuard, LoopId, PredicateId, SSAFunction, SSAOp, ValueId};

use crate::address::parse_address_from_var_name;
use crate::ast::{BinaryOp, CExpr, CStmt, UnaryOp};
use crate::fold::FoldingContext;
use crate::fold::context::{EffectRenderProof, EffectRenderProofKind};
use crate::region::{Region, RegionAnalyzer, RegionTransferKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlRenderProofKind {
    Branch,
    Loop,
    Switch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlRenderProof {
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
    pub fn new(kind: ControlRenderProofKind, anchor: u64) -> Self {
        Self {
            kind,
            anchor,
            branch_condition: None,
            branch_condition_value: None,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlTransferRenderProofKind {
    Break,
    Continue,
    Goto,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ControlTransferRenderProof {
    Break {
        loop_header: u64,
        source: u64,
        target: u64,
    },
    Continue {
        loop_header: u64,
        source: u64,
        target: u64,
    },
    Goto {
        loop_header: u64,
        source: u64,
        target: u64,
        lowered_target: u64,
        path: Vec<u64>,
        label: String,
    },
}

impl ControlTransferRenderProof {
    pub const fn kind(&self) -> ControlTransferRenderProofKind {
        match self {
            Self::Break { .. } => ControlTransferRenderProofKind::Break,
            Self::Continue { .. } => ControlTransferRenderProofKind::Continue,
            Self::Goto { .. } => ControlTransferRenderProofKind::Goto,
        }
    }

    pub const fn loop_header(&self) -> u64 {
        match self {
            Self::Break { loop_header, .. }
            | Self::Continue { loop_header, .. }
            | Self::Goto { loop_header, .. } => *loop_header,
        }
    }

    pub const fn source(&self) -> u64 {
        match self {
            Self::Break { source, .. }
            | Self::Continue { source, .. }
            | Self::Goto { source, .. } => *source,
        }
    }

    pub const fn target(&self) -> u64 {
        match self {
            Self::Break { target, .. }
            | Self::Continue { target, .. }
            | Self::Goto { target, .. } => *target,
        }
    }
}

/// Control flow structurer.
///
/// Converts a region tree into structured C statements.
pub struct ControlFlowStructurer<'a, 'o> {
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
    /// Safety budget for recursive region structuring.
    safety_budget_remaining: usize,
    safety_budget_max: usize,
    safety_reason: Option<String>,
    /// Structured control nodes emitted by this structurer, in render order.
    control_render_proofs: Vec<ControlRenderProof>,
    /// Exact loop-transfer nodes emitted by this structurer, in render order.
    control_transfer_render_proofs: Vec<ControlTransferRenderProof>,
    /// Merge blocks owned by enclosing regions and therefore emitted there.
    deferred_merge_blocks: Vec<u64>,
    /// Exact lexical control-domain alternatives currently being emitted.
    /// A labeled side entry can join another certified alternative without
    /// weakening the domain checks for downstream blocks.
    active_domains: Vec<RenderedBlockDomain>,
    /// Every lexical domain in which a source block was emitted. Shared CFG
    /// blocks may be duplicated by structuring, so coverage is checked only
    /// after all occurrences are known.
    rendered_block_domains: BTreeMap<u64, Vec<RenderedBlockOccurrence>>,
    /// Basic blocks owned by the current structured region tree.
    structured_region_blocks: BTreeSet<u64>,
    /// Exact side-entry domains that reach a labeled block through a certified
    /// noncanonical loop exit.
    transfer_target_domains: BTreeMap<u64, Vec<RenderedBlockDomain>>,
}

#[derive(Debug, Clone)]
struct FoldedBlock {
    stmts: Vec<CStmt>,
    effect_proofs: Vec<EffectRenderProof>,
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

struct ControlBdd {
    nodes: Vec<Option<BddNode>>,
    unique: HashMap<BddNode, usize>,
    apply_cache: HashMap<(BddOp, usize, usize), usize>,
    not_cache: HashMap<usize, usize>,
    node_limit: usize,
}

impl ControlBdd {
    fn new(node_limit: usize) -> Self {
        Self {
            nodes: vec![None, None],
            unique: HashMap::new(),
            apply_cache: HashMap::new(),
            not_cache: HashMap::new(),
            node_limit,
        }
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
    pub fn new(func: &'a SSAFunction, fold_ctx: &'o FoldingContext<'o>) -> Self {
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
            safety_budget_remaining: safety_budget_max,
            safety_budget_max,
            safety_reason: None,
            control_render_proofs: Vec::new(),
            control_transfer_render_proofs: Vec::new(),
            deferred_merge_blocks: Vec::new(),
            active_domains: vec![RenderedBlockDomain::default()],
            rendered_block_domains: BTreeMap::new(),
            structured_region_blocks: BTreeSet::new(),
            transfer_target_domains: BTreeMap::new(),
        }
    }

    /// Create a structurer without expression folding (for comparison).
    pub fn new_unfolded(func: &'a SSAFunction, fold_ctx: &'o FoldingContext<'o>) -> Self {
        let safety_budget_max = Self::compute_safety_budget(func.num_blocks());
        Self {
            func,
            fold_ctx,
            folded_block_cache: HashMap::new(),
            labels: HashMap::new(),
            emitted_labels: BTreeSet::new(),
            label_counter: 0,
            region_analyzer: Some(RegionAnalyzer::new(func)),
            safety_budget_remaining: safety_budget_max,
            safety_budget_max,
            safety_reason: None,
            control_render_proofs: Vec::new(),
            control_transfer_render_proofs: Vec::new(),
            deferred_merge_blocks: Vec::new(),
            active_domains: vec![RenderedBlockDomain::default()],
            rendered_block_domains: BTreeMap::new(),
            structured_region_blocks: BTreeSet::new(),
            transfer_target_domains: BTreeMap::new(),
        }
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
    pub fn safety_reason(&self) -> Option<&str> {
        self.safety_reason.as_deref()
    }

    pub fn control_render_proofs(&self) -> &[ControlRenderProof] {
        &self.control_render_proofs
    }

    pub fn control_transfer_render_proofs(&self) -> &[ControlTransferRenderProof] {
        &self.control_transfer_render_proofs
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

    fn branch_render_proof(
        &self,
        anchor: u64,
        condition: Option<PredicateId>,
        condition_value: Option<ValueId>,
    ) -> ControlRenderProof {
        ControlRenderProof::branch_proof(anchor, condition, condition_value)
    }

    fn certified_branch_render_proof(
        &self,
        anchor: u64,
        condition: Option<PredicateId>,
        condition_value: Option<ValueId>,
    ) -> Option<ControlRenderProof> {
        let proof = self.branch_render_proof(anchor, condition, condition_value);
        let predicate = self.fold_ctx.control_facts()?.branch_for_block(anchor)?;
        (predicate.comparison.is_some()
            && Some(predicate.id) == proof.branch_condition
            && Some(predicate.condition) == proof.branch_condition_value)
            .then_some(proof)
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

    fn certified_loop_render_proof(
        &self,
        anchor: u64,
        condition: Option<PredicateId>,
        condition_value: Option<ValueId>,
        body: &Region,
    ) -> Option<ControlRenderProof> {
        let facts = self.fold_ctx.control_facts()?;
        // Prefer canonical LoopCertificate body/latches/exits when available.
        // Match on header only: loop header uniquely identifies the natural loop.
        // condition/condition_value use different ID spaces (r2il vs SSA) and may differ.
        if let Some(cert) = facts.loops.values().find(|fact| fact.header == anchor) {
            return Some(ControlRenderProof::loop_proof(
                anchor,
                condition,
                condition_value,
                cert.body.clone(),
                cert.latches.clone(),
                cert.exits.clone(),
            ));
        }
        // Fallback: compute from structurer and require exact match
        let proof = self.loop_render_proof(anchor, condition, condition_value, body);
        facts
            .loops
            .values()
            .any(|fact| {
                fact.header == proof.anchor
                    && fact.condition == proof.loop_condition
                    && fact.condition_value == proof.loop_condition_value
                    && fact.body == proof.loop_body_blocks
                    && fact.latches == proof.loop_latches
                    && fact.exits == proof.loop_exits
            })
            .then_some(proof)
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

    fn certified_switch_render_proof(
        &self,
        anchor: u64,
        selector: Option<ValueId>,
        cases: &[(Option<u64>, Box<Region>)],
        default: Option<&Region>,
    ) -> Option<ControlRenderProof> {
        let proof = self.switch_render_proof(anchor, selector, cases, default);
        let facts = self.fold_ctx.control_facts()?;
        facts.switches.get(&anchor).and_then(|fact| {
            let mut fact_cases = fact.cases.clone();
            fact_cases.sort_unstable();
            (fact.selector == proof.switch_selector
                && fact_cases == proof.switch_cases
                && fact.default == proof.switch_default)
                .then_some(proof)
        })
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

    /// Get the set of variable names that survive folding (for filtering declarations).
    pub fn emitted_var_names(&self) -> HashSet<String> {
        let blocks: Vec<_> = self.func.blocks().cloned().collect();
        self.fold_ctx.emitted_var_names(&blocks)
    }

    /// Structure the function's control flow.
    pub fn structure(&mut self) -> CStmt {
        let stmt = self.structure_preserving_render_proof_identity();
        if self.safety_reason.is_some() {
            return CStmt::Empty;
        }
        // Post-process: flatten, simplify loops, remove redundant control flow.
        Self::cleanup(stmt)
    }

    /// Structure control flow without post-proof AST rewrites.
    ///
    /// Certified rendering validates final executable control nodes against the
    /// `FunctionFacts` proof identities recorded while structuring. Cleanup can
    /// invert, merge, synthesize, or delete control nodes, so certified callers
    /// must validate the unrewritten AST or residualize.
    pub(crate) fn structure_preserving_render_proof_identity(&mut self) -> CStmt {
        self.reset_safety_budget();
        self.control_render_proofs.clear();
        self.control_transfer_render_proofs.clear();
        self.active_domains = vec![RenderedBlockDomain::default()];
        self.rendered_block_domains.clear();
        self.emitted_labels.clear();
        self.structured_region_blocks.clear();
        self.transfer_target_domains.clear();
        if self.region_analyzer.is_none() {
            self.region_analyzer = Some(RegionAnalyzer::new(self.func));
        }
        let region = if let Some(analyzer) = self.region_analyzer.as_mut() {
            let region = analyzer.analyze();
            if let Some(reason) = analyzer.analysis_reason() {
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
        let stmt = self.structure_region(&region);
        self.validate_rendered_block_domain_coverage();
        if self.safety_reason.is_some() {
            return CStmt::Empty;
        }
        stmt
    }

    /// Structure a region into C statements.
    fn structure_region(&mut self, region: &Region) -> CStmt {
        if !self.consume_safety_budget(1) {
            return CStmt::Empty;
        }
        let inherited_domains = self.active_domains.clone();
        if let Some(domains) = self.transfer_target_domains.remove(&region.entry()) {
            self.certify_transfer_domain_join(region.entry(), domains);
        }
        let stmt = self.structure_region_in_active_domains(region);
        self.active_domains = inherited_domains;
        stmt
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
                self.safety_reason = Some(format!(
                    "control-domain coverage proof failed for transfer join at 0x{block_addr:x}: {reason}"
                ));
            }
        }
    }

    fn structure_region_in_active_domains(&mut self, region: &Region) -> CStmt {
        match region {
            Region::Block(addr) => self.structure_block(*addr),
            Region::Sequence(regions) => {
                let stmts: Vec<CStmt> = regions
                    .iter()
                    .map(|r| self.structure_region(r))
                    .filter(|s| !matches!(s, CStmt::Empty))
                    .collect();
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
                if !merge_owned_by_ancestor {
                    if !self.fold_ctx.requires_certified_rendering()
                        && let Some(rewritten) = self.try_structure_symbolic_actionable_if(
                            *cond_block,
                            then_region,
                            else_region.as_deref(),
                            *merge_block,
                        )
                    {
                        return rewritten;
                    }
                    if let Some(rewritten) = self.try_structure_if_else_with_slot_merge_returns(
                        *cond_block,
                        then_region,
                        else_region.as_deref(),
                        *merge_block,
                    ) {
                        return rewritten;
                    }
                }
                if !merge_owned_by_ancestor
                    && let Some(rewritten) = self.try_structure_if_else_with_register_merge_returns(
                        *cond_block,
                        then_region,
                        else_region.as_deref(),
                        *merge_block,
                    )
                {
                    return rewritten;
                }
                if !self.fold_ctx.requires_certified_rendering()
                    && let Some(rewritten) = self.try_structure_guarded_switch_with_default(
                        *cond_block,
                        then_region,
                        else_region.as_deref(),
                        *merge_block,
                    )
                {
                    return rewritten;
                }
                let (cond, predicate, condition_value) =
                    self.get_branch_condition_with_predicate(*cond_block);
                let Some(mut cond) = cond else {
                    let mut prefix = self.structure_block_prefix_stmts(*cond_block);
                    prefix.push(CStmt::comment(format!(
                        "r2dec residual: unresolved branch condition at 0x{cond_block:x}"
                    )));
                    return if prefix.len() == 1 {
                        prefix.into_iter().next().unwrap_or(CStmt::Empty)
                    } else {
                        CStmt::Block(prefix)
                    };
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
                if self.fold_ctx.requires_certified_rendering() {
                    let Some(proof) =
                        self.certified_branch_render_proof(*cond_block, predicate, condition_value)
                    else {
                        return CStmt::Block(vec![CStmt::comment(format!(
                            "r2dec residual: uncertified branch structure at 0x{cond_block:x}"
                        ))]);
                    };
                    self.control_render_proofs.push(proof);
                } else {
                    self.record_branch_render_proof(*cond_block, predicate, condition_value);
                }
                if let Some(merge) = merge_block {
                    self.deferred_merge_blocks.push(*merge);
                }
                let then_stmt = self.structure_branch_region(*cond_block, then_region);
                let else_stmt = else_region
                    .as_ref()
                    .map(|r| self.structure_branch_region(*cond_block, r));
                if let Some(merge) = merge_block {
                    debug_assert_eq!(self.deferred_merge_blocks.pop(), Some(*merge));
                }
                let branches_terminate = else_stmt.as_ref().is_some_and(|else_stmt| {
                    Self::stmt_guarantees_termination(&then_stmt)
                        && Self::stmt_guarantees_termination(else_stmt)
                });
                let if_stmt = CStmt::if_stmt(cond, then_stmt, else_stmt);
                let mut prefix = self.structure_block_prefix_stmts(*cond_block);
                prefix.push(if_stmt);
                if let Some(merge_addr) = merge_block
                    && !branches_terminate
                    && !merge_owned_by_ancestor
                {
                    Self::append_stmt_body_flat(&mut prefix, self.structure_block(*merge_addr));
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
                    return CStmt::Block(vec![CStmt::comment(format!(
                        "r2dec residual: unresolved loop condition at 0x{header:x}"
                    ))]);
                };
                if self.loop_needs_condition_inversion(*header, body) {
                    cond = Self::negate_condition(cond);
                }
                if self.fold_ctx.requires_certified_rendering() {
                    let Some(proof) =
                        self.certified_loop_render_proof(*header, predicate, condition_value, body)
                    else {
                        return CStmt::Block(vec![CStmt::comment(format!(
                            "r2dec residual: uncertified loop structure at 0x{header:x}"
                        ))]);
                    };
                    self.control_render_proofs.push(proof);
                } else {
                    self.record_loop_render_proof(*header, predicate, condition_value, body);
                }
                let loop_id = if self.fold_ctx.requires_certified_rendering() {
                    self.fold_ctx
                        .control_facts()
                        .and_then(|facts| facts.loops_for_header(*header).next())
                        .map(|fact| fact.loop_id)
                } else {
                    None
                };
                if self.fold_ctx.requires_certified_rendering() && loop_id.is_none() {
                    self.safety_reason = Some(format!(
                        "missing certified loop domain for header 0x{header:x}"
                    ));
                    return CStmt::Empty;
                }
                let body_guard = if self.fold_ctx.requires_certified_rendering() {
                    self.certified_branch_guard_for_region(*header, body)
                } else {
                    None
                };
                if self.fold_ctx.requires_certified_rendering() && body_guard.is_none() {
                    self.safety_reason = Some(format!(
                        "missing certified loop-body control domain for header 0x{header:x}"
                    ));
                    return CStmt::Empty;
                }
                let outer_domains = self.active_domains.clone();
                if let Some(loop_id) = loop_id {
                    self.push_active_loop(loop_id);
                }
                let prefix = self.structure_block_prefix_stmts(*header);
                let cond = match Self::combine_loop_condition_prefix(prefix, cond) {
                    Ok(cond) => cond,
                    Err(reason) => {
                        self.safety_reason = Some(format!(
                            "loop header 0x{header:x} effects cannot be preserved: {reason}"
                        ));
                        self.active_domains = outer_domains;
                        return CStmt::Empty;
                    }
                };
                if let Some(guard) = &body_guard {
                    self.push_active_guard(guard.clone());
                }
                let body_stmt = Self::strip_trailing_continue(self.structure_loop_body(body));
                self.active_domains = outer_domains;
                CStmt::while_loop(cond, body_stmt)
            }
            Region::DoWhileLoop { body, cond_block } => {
                let (cond, predicate, condition_value) =
                    self.get_branch_condition_with_predicate(*cond_block);
                let Some(mut cond) = cond else {
                    return CStmt::Block(vec![CStmt::comment(format!(
                        "r2dec residual: unresolved loop condition at 0x{cond_block:x}"
                    ))]);
                };
                if self.loop_needs_condition_inversion(*cond_block, body) {
                    cond = Self::negate_condition(cond);
                }
                let anchor = body.entry();
                if self.fold_ctx.requires_certified_rendering() {
                    let Some(proof) =
                        self.certified_loop_render_proof(anchor, predicate, condition_value, body)
                    else {
                        return CStmt::Block(vec![CStmt::comment(format!(
                            "r2dec residual: uncertified loop structure at 0x{anchor:x}"
                        ))]);
                    };
                    self.control_render_proofs.push(proof);
                } else {
                    self.record_loop_render_proof(anchor, predicate, condition_value, body);
                }
                let loop_id = if self.fold_ctx.requires_certified_rendering() {
                    self.fold_ctx
                        .control_facts()
                        .and_then(|facts| facts.loops_for_header(anchor).next())
                        .map(|fact| fact.loop_id)
                } else {
                    None
                };
                if self.fold_ctx.requires_certified_rendering() && loop_id.is_none() {
                    self.safety_reason = Some(format!(
                        "missing certified loop domain for header 0x{anchor:x}"
                    ));
                    return CStmt::Empty;
                }
                let outer_domains = self.active_domains.clone();
                if let Some(loop_id) = loop_id {
                    self.push_active_loop(loop_id);
                }
                let cond_owned_by_body = Self::region_owns_block_emission(body, *cond_block);
                if !cond_owned_by_body {
                    self.deferred_merge_blocks.push(*cond_block);
                }
                let mut body_stmt =
                    Self::strip_trailing_latch_marker(self.structure_loop_body(body));
                if !cond_owned_by_body {
                    debug_assert_eq!(self.deferred_merge_blocks.pop(), Some(*cond_block));
                    let mut stmts = Self::stmt_into_vec(body_stmt);
                    Self::append_stmt_body_flat(&mut stmts, self.structure_block(*cond_block));
                    body_stmt = Self::stmt_from_vec(stmts);
                }
                self.active_domains = outer_domains;
                CStmt::DoWhile {
                    body: Box::new(body_stmt),
                    cond,
                }
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
                source,
                target,
                kind,
            } if *kind == RegionTransferKind::Continue && target == loop_header => {
                self.control_transfer_render_proofs
                    .push(ControlTransferRenderProof::Continue {
                        loop_header: *loop_header,
                        source: *source,
                        target: *target,
                    });
                CStmt::Continue
            }
            Region::Transfer {
                loop_header,
                source,
                target,
                kind,
            } if *kind == RegionTransferKind::Exit
                && self
                    .region_analyzer
                    .as_ref()
                    .and_then(|analyzer| analyzer.get_loop_fallthrough(*loop_header))
                    == Some(*target) =>
            {
                self.control_transfer_render_proofs
                    .push(ControlTransferRenderProof::Break {
                        loop_header: *loop_header,
                        source: *source,
                        target: *target,
                    });
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
                            let label = self.ensure_label(lowered_target);
                            if !self.record_transfer_target_domain(*loop_header, lowered_target) {
                                return CStmt::Empty;
                            }
                            self.control_transfer_render_proofs.push(
                                ControlTransferRenderProof::Goto {
                                    loop_header: *loop_header,
                                    source: *source,
                                    target: *target,
                                    lowered_target,
                                    path,
                                    label: label.clone(),
                                },
                            );
                            return CStmt::Goto(label);
                        }
                        Err(reason) => Some(reason),
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
                self.structure_switch_region(*switch_block, cases, default.as_deref(), *merge_block)
            }
            Region::Irreducible { entry, blocks } => self.structure_irreducible(*entry, blocks),
        }
    }

    fn structure_branch_region(&mut self, pred_block: u64, region: &Region) -> CStmt {
        let direct_successor = self.func.successors(pred_block).contains(&region.entry());
        if !self.fold_ctx.requires_certified_rendering() {
            return if direct_successor {
                self.structure_region_from_predecessor(region, pred_block)
            } else {
                self.structure_region(region)
            };
        }
        let Some(guard) = self.certified_branch_guard_for_region(pred_block, region) else {
            self.safety_reason = Some(format!(
                "missing certified branch-domain edge from 0x{pred_block:x} to region 0x{:x}",
                region.entry()
            ));
            return CStmt::Empty;
        };
        let outer_domains = self.active_domains.clone();
        self.push_active_guard(guard);
        let stmt = if direct_successor {
            self.structure_region_from_predecessor(region, pred_block)
        } else {
            self.structure_region(region)
        };
        self.active_domains = outer_domains;
        stmt
    }

    fn certified_branch_guard_for_region(
        &self,
        pred_block: u64,
        region: &Region,
    ) -> Option<ControlGuard> {
        let predicate = self
            .fold_ctx
            .control_facts()?
            .branch_for_block(pred_block)?;
        let entry = region.entry();
        let reaches_true = self.transparent_target_reaches(predicate.true_target, entry);
        let reaches_false = self.transparent_target_reaches(predicate.false_target, entry);
        if reaches_true == reaches_false {
            return None;
        }
        Some(ControlGuard::Branch {
            predicate: predicate.id,
            truth: reaches_true,
        })
    }

    fn structure_region_from_predecessor(&mut self, region: &Region, pred_block: u64) -> CStmt {
        match region {
            Region::Block(addr) => self.structure_block_from_predecessor(*addr, pred_block),
            _ => self.structure_region(region),
        }
    }

    fn transparent_target_reaches(&self, mut current: u64, target: u64) -> bool {
        let mut visited = HashSet::new();
        while visited.insert(current) {
            if current == target {
                return true;
            }
            let Some(block) = self.func.get_block(current) else {
                return false;
            };
            if !block
                .ops
                .iter()
                .all(|op| self.is_transparent_branch_forwarder_op(op))
            {
                return false;
            }
            let successors = self.transparent_branch_successors(current, block);
            let [successor] = successors.as_slice() else {
                return false;
            };
            current = *successor;
        }
        false
    }

    fn structure_block_from_predecessor(&mut self, addr: u64, pred_block: u64) -> CStmt {
        let stmt = self.structure_block(addr);
        if !self.block_allows_predecessor_return_register_rewrite(addr) {
            return stmt;
        }
        let Some((expr, proof_block, proof_op, proof_value)) =
            self.return_register_candidate_for_merge_predecessor(addr, pred_block)
        else {
            return stmt;
        };
        if let Some(rewritten) = self.rewrite_trailing_return_with_merged_expr(&stmt, &expr) {
            self.record_return_value_render_proof(proof_block, proof_op, proof_value);
            rewritten
        } else {
            stmt
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
    ) -> Option<(CExpr, u64, usize, ValueId)> {
        if !self.block_allows_predecessor_return_register_rewrite(merge_addr) {
            return None;
        }
        self.fold_ctx
            .merged_return_register_candidate_for_block_predecessor_with_proof(
                merge_addr, pred_addr,
            )
            .or_else(|| {
                self.fold_ctx
                    .predecessor_return_register_candidate_with_proof(pred_addr)
            })
    }

    /// Get the switch expression from a block.
    fn get_switch_expression(&mut self, addr: u64) -> Option<(CExpr, Option<ValueId>)> {
        let switch_addr = self.unique_switch_block().unwrap_or(addr);
        let block = self.func.get_block(switch_addr)?;

        if let Some(vm_step) = self
            .fold_ctx
            .inputs
            .semantic_artifact()
            .and_then(|artifact| artifact.vm_step_for_dispatch_header(switch_addr))
            .or_else(|| {
                self.fold_ctx
                    .inputs
                    .semantic_artifact()
                    .and_then(|artifact| artifact.vm_transfer_for_dispatch_header(switch_addr))
            })
            && let Some(selector) = vm_step.selector.as_ref()
        {
            return Some((CExpr::Var(selector.clone()), None));
        }

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
    ) -> CStmt {
        let merge_owned_by_ancestor =
            merge_block.is_some_and(|merge| self.deferred_merge_blocks.contains(&merge));
        let Some((switch_expr, switch_selector)) = self.get_switch_expression(switch_block) else {
            return CStmt::Block(vec![CStmt::comment(format!(
                "r2dec residual: unresolved switch selector at 0x{switch_block:x}"
            ))]);
        };
        if cases.iter().any(|(case_value, _)| case_value.is_none()) {
            return CStmt::Block(vec![CStmt::comment(format!(
                "r2dec residual: unresolved switch case value at 0x{switch_block:x}"
            ))]);
        }
        if self.fold_ctx.requires_certified_rendering() {
            let Some(proof) =
                self.certified_switch_render_proof(switch_block, switch_selector, cases, default)
            else {
                return CStmt::Block(vec![CStmt::comment(format!(
                    "r2dec residual: uncertified switch structure at 0x{switch_block:x}"
                ))]);
            };
            self.control_render_proofs.push(proof);
        } else {
            self.record_switch_render_proof(switch_block, switch_selector, cases, default);
        }

        if let Some(merge) = merge_block {
            self.deferred_merge_blocks.push(merge);
        }
        let mut switch_cases = Vec::new();
        for (case_value, case_region) in cases {
            let outer_domains = self.active_domains.clone();
            let Some(case_value) = case_value else {
                continue;
            };
            let value_expr = CExpr::IntLit(*case_value as i64);
            let guard = if self.fold_ctx.requires_certified_rendering() {
                self.certified_switch_guard_for_region(
                    switch_block,
                    case_region,
                    Some(*case_value),
                    false,
                )
            } else {
                None
            };
            if self.fold_ctx.requires_certified_rendering() && guard.is_none() {
                self.safety_reason = Some(format!(
                    "missing certified switch-domain arm at 0x{switch_block:x} for case {case_value}"
                ));
                return CStmt::Empty;
            }
            if let Some(guard) = &guard {
                self.push_active_guard(guard.clone());
            }
            let case_stmt = self.structure_region(case_region);
            self.active_domains = outer_domains;
            let body = if self.fold_ctx.requires_certified_rendering() {
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
            let guard = if self.fold_ctx.requires_certified_rendering() {
                self.certified_switch_guard_for_region(switch_block, region, None, true)
            } else {
                None
            };
            if self.fold_ctx.requires_certified_rendering() && guard.is_none() {
                self.safety_reason = Some(format!(
                    "missing certified switch-domain default at 0x{switch_block:x}"
                ));
                return CStmt::Empty;
            }
            if let Some(guard) = &guard {
                self.push_active_guard(guard.clone());
            }
            let stmt = self.structure_region(region);
            self.active_domains = outer_domains;
            Some(vec![stmt])
        } else {
            None
        };
        if let Some(merge) = merge_block {
            debug_assert_eq!(self.deferred_merge_blocks.pop(), Some(merge));
        }
        let switch_stmt = CStmt::Switch {
            expr: switch_expr,
            cases: switch_cases,
            default: default_body,
        };

        let mut prefix = self.structure_block_prefix_stmts(switch_block);
        prefix.push(switch_stmt);
        if let Some(merge_addr) = merge_block.filter(|_| !merge_owned_by_ancestor) {
            Self::append_stmt_body_flat(&mut prefix, self.structure_block(merge_addr));
        }
        if prefix.len() == 1 {
            prefix.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(prefix)
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

    fn symbolic_exact_reachable_target(&self, cond_block: u64) -> Option<u64> {
        self.fold_ctx
            .inputs
            .semantic_artifact()?
            .exact_reachable_target_for_block(cond_block)
    }

    #[cfg(test)]
    fn symbolic_actionable_reachable_target(&self, cond_block: u64) -> Option<u64> {
        self.fold_ctx
            .inputs
            .semantic_artifact()?
            .actionable_reachable_target_for_block(cond_block)
    }

    fn structure_region_suffix_from_target(
        &mut self,
        region: &Region,
        target: u64,
    ) -> Option<CStmt> {
        match region {
            Region::Block(addr) => (*addr == target).then(|| self.structure_block(*addr)),
            Region::Sequence(regions) => {
                let start_idx = regions
                    .iter()
                    .position(|child| child.blocks().contains(&target))?;
                let mut stmts = Vec::new();
                Self::append_stmt_body_flat(
                    &mut stmts,
                    self.structure_region_suffix_from_target(&regions[start_idx], target)?,
                );
                for child in &regions[start_idx + 1..] {
                    Self::append_stmt_body_flat(&mut stmts, self.structure_region(child));
                }
                Some(if stmts.len() == 1 {
                    stmts.into_iter().next().unwrap_or(CStmt::Empty)
                } else {
                    CStmt::Block(stmts)
                })
            }
            Region::IfThenElse {
                cond_block,
                then_region,
                else_region,
                merge_block,
            } => {
                if *cond_block == target {
                    return Some(self.structure_region(region));
                }
                let mut stmts = if then_region.blocks().contains(&target) {
                    let mut stmts = Vec::new();
                    Self::append_stmt_body_flat(
                        &mut stmts,
                        self.structure_region_suffix_from_target(then_region, target)?,
                    );
                    stmts
                } else if else_region
                    .as_deref()
                    .is_some_and(|region| region.blocks().contains(&target))
                {
                    let mut stmts = Vec::new();
                    Self::append_stmt_body_flat(
                        &mut stmts,
                        self.structure_region_suffix_from_target(else_region.as_deref()?, target)?,
                    );
                    stmts
                } else if merge_block.is_some_and(|merge| merge == target) {
                    vec![self.structure_block(target)]
                } else {
                    return None;
                };
                if let Some(merge_addr) = merge_block.filter(|merge| *merge != target) {
                    Self::append_stmt_body_flat(&mut stmts, self.structure_block(merge_addr));
                }
                Some(if stmts.len() == 1 {
                    stmts.into_iter().next().unwrap_or(CStmt::Empty)
                } else {
                    CStmt::Block(stmts)
                })
            }
            Region::WhileLoop { header, body } => {
                if *header == target {
                    Some(self.structure_region(region))
                } else if body.blocks().contains(&target) {
                    self.structure_region_suffix_from_target(body, target)
                } else {
                    None
                }
            }
            Region::DoWhileLoop { body, cond_block } => {
                if *cond_block == target {
                    return Some(self.structure_block(*cond_block));
                }
                if !body.blocks().contains(&target) {
                    return None;
                }
                let mut stmts = Vec::new();
                Self::append_stmt_body_flat(
                    &mut stmts,
                    self.structure_region_suffix_from_target(body, target)?,
                );
                Self::append_stmt_body_flat(&mut stmts, self.structure_block(*cond_block));
                Some(if stmts.len() == 1 {
                    stmts.into_iter().next().unwrap_or(CStmt::Empty)
                } else {
                    CStmt::Block(stmts)
                })
            }
            Region::MultiExit { head, .. } => head
                .blocks()
                .contains(&target)
                .then(|| self.structure_region_suffix_from_target(head, target))
                .flatten(),
            Region::Transfer {
                target: transfer_target,
                ..
            } => (*transfer_target == target).then_some(CStmt::Empty),
            Region::Switch {
                switch_block,
                cases,
                default,
                merge_block,
            } => {
                if *switch_block == target {
                    return Some(self.structure_region(region));
                }
                let mut stmts = if let Some((_, case_region)) = cases
                    .iter()
                    .find(|(_, case_region)| case_region.blocks().contains(&target))
                {
                    let mut stmts = Vec::new();
                    Self::append_stmt_body_flat(
                        &mut stmts,
                        self.structure_region_suffix_from_target(case_region, target)?,
                    );
                    stmts
                } else if default
                    .as_deref()
                    .is_some_and(|region| region.blocks().contains(&target))
                {
                    let mut stmts = Vec::new();
                    Self::append_stmt_body_flat(
                        &mut stmts,
                        self.structure_region_suffix_from_target(default.as_deref()?, target)?,
                    );
                    stmts
                } else if merge_block.is_some_and(|merge| merge == target) {
                    vec![self.structure_block(target)]
                } else {
                    return None;
                };
                if let Some(merge_addr) = merge_block.filter(|merge| *merge != target) {
                    Self::append_stmt_body_flat(&mut stmts, self.structure_block(merge_addr));
                }
                Some(if stmts.len() == 1 {
                    stmts.into_iter().next().unwrap_or(CStmt::Empty)
                } else {
                    CStmt::Block(stmts)
                })
            }
            Region::Irreducible { blocks, .. } => blocks
                .contains(&target)
                .then(|| self.structure_block(target)),
        }
    }

    fn try_structure_symbolic_actionable_if(
        &mut self,
        cond_block: u64,
        then_region: &Region,
        else_region: Option<&Region>,
        merge_block: Option<u64>,
    ) -> Option<CStmt> {
        let reachable_target = self.symbolic_exact_reachable_target(cond_block)?;
        let reachable_stmt = if then_region.blocks().contains(&reachable_target) {
            self.structure_region_suffix_from_target(then_region, reachable_target)?
        } else {
            let else_region = else_region?;
            self.structure_region_suffix_from_target(else_region, reachable_target)?
        };

        let mut prefix = self.structure_block_prefix_stmts(cond_block);
        Self::append_stmt_body_flat(&mut prefix, reachable_stmt);
        if let Some(merge_addr) = merge_block {
            Self::append_stmt_body_flat(&mut prefix, self.structure_block(merge_addr));
        }
        Some(if prefix.len() == 1 {
            prefix.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(prefix)
        })
    }

    /// Structure a single basic block.
    fn structure_block(&mut self, addr: u64) -> CStmt {
        if self.is_unresolved_indirect_dispatch_block(addr) {
            return CStmt::Empty;
        }
        let block = match self.func.get_block(addr) {
            Some(b) => b,
            None => return CStmt::Empty,
        };

        let mut stmts = Vec::new();

        // Add label if needed
        if let Some(label) = self.take_block_label(addr) {
            stmts.push(CStmt::Label(label));
        }

        // Convert operations to statements
        stmts.extend(self.folded_block_stmts(block, addr));

        if stmts.is_empty() {
            CStmt::Empty
        } else if stmts.len() == 1 {
            stmts.remove(0)
        } else {
            CStmt::Block(stmts)
        }
    }

    /// Structure a loop body region, flattening block sequences into a single
    /// statement list to avoid nested `{ ...; break; } { ...; continue; }` braces.
    fn structure_loop_body(&mut self, body: &Region) -> CStmt {
        // If the body is a Sequence of Blocks, flatten all block statements
        // into one continuous list instead of wrapping each in CStmt::Block.
        if let Region::Sequence(regions) = body {
            let mut all_stmts = Vec::new();
            for region in regions {
                match region {
                    Region::Block(addr) => {
                        // Inline the block's statements directly
                        self.structure_block_stmts_into(*addr, &mut all_stmts);
                    }
                    _ => {
                        // Non-block region: structure normally and append
                        let stmt = self.structure_region(region);
                        if !matches!(stmt, CStmt::Empty) {
                            all_stmts.push(stmt);
                        }
                    }
                }
            }
            if all_stmts.is_empty() {
                CStmt::Empty
            } else if all_stmts.len() == 1 {
                all_stmts.remove(0)
            } else {
                CStmt::Block(all_stmts)
            }
        } else {
            self.structure_region(body)
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
    fn structure_block_stmts_into(&mut self, addr: u64, stmts: &mut Vec<CStmt>) {
        if self.is_unresolved_indirect_dispatch_block(addr) {
            return;
        }
        let block = match self.func.get_block(addr) {
            Some(b) => b,
            None => return,
        };

        // Add label if needed
        if let Some(label) = self.take_block_label(addr) {
            stmts.push(CStmt::Label(label));
        }

        // Convert operations to statements
        stmts.extend(self.folded_block_stmts(block, addr));
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

    fn transparent_transfer_path(&self, start: u64) -> Result<Vec<u64>, String> {
        let mut path = Vec::new();
        let mut seen = BTreeSet::new();
        let mut current = start;
        loop {
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
            if !block.ops.iter().all(|op| {
                self.is_transparent_branch_forwarder_op(op)
                    || self.is_materialized_phi_edge_copy(current, *next, op)
            }) {
                return Err(format!(
                    "forwarder block 0x{current:x} owns live non-phi SSA effects"
                ));
            }
            current = *next;
        }
    }

    fn record_transfer_target_domain(&mut self, loop_header: u64, target: u64) -> bool {
        if !self.fold_ctx.requires_certified_rendering() {
            return true;
        }
        let Some(loop_id) = self
            .fold_ctx
            .control_facts()
            .and_then(|facts| facts.loops_for_header(loop_header).next())
            .map(|fact| fact.loop_id)
        else {
            self.safety_reason = Some(format!(
                "missing certified loop domain for transfer from 0x{loop_header:x}"
            ));
            return false;
        };
        let mut domains = self.active_domains.clone();
        for domain in &mut domains {
            domain.loops.retain(|active| *active != loop_id);
        }
        Self::normalize_rendered_domains(&mut domains);
        let target_domains = self.transfer_target_domains.entry(target).or_default();
        target_domains.extend(domains);
        Self::normalize_rendered_domains(target_domains);
        true
    }

    fn push_active_guard(&mut self, guard: ControlGuard) {
        for domain in &mut self.active_domains {
            domain.guards.push(guard.clone());
        }
        Self::normalize_rendered_domains(&mut self.active_domains);
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
    fn structure_block_prefix_stmts(&mut self, addr: u64) -> Vec<CStmt> {
        if self.is_unresolved_indirect_dispatch_block(addr) {
            return Vec::new();
        }
        let block = match self.func.get_block(addr) {
            Some(b) => b,
            None => return Vec::new(),
        };

        let mut stmts = Vec::new();
        if let Some(label) = self.take_block_label(addr) {
            stmts.push(CStmt::Label(label));
        }
        stmts.extend(self.folded_block_stmts(block, addr));
        stmts
    }

    fn combine_loop_condition_prefix(
        prefix: Vec<CStmt>,
        condition: CExpr,
    ) -> Result<CExpr, String> {
        let mut expressions = Vec::with_capacity(prefix.len().saturating_add(1));
        for stmt in prefix {
            match stmt {
                CStmt::Expr(expr) => expressions.push(expr),
                CStmt::Empty => {}
                CStmt::Comment(reason) => return Err(reason),
                other => {
                    return Err(format!("unsupported condition-prefix statement {other:?}"));
                }
            }
        }
        if expressions.is_empty() {
            return Ok(condition);
        }
        expressions.push(condition);
        Ok(CExpr::Comma(expressions))
    }

    fn folded_block_stmts(&mut self, block: &r2ssa::FunctionSSABlock, addr: u64) -> Vec<CStmt> {
        let stmts = if let Some(folded) = self.folded_block_cache.get(&addr) {
            self.fold_ctx
                .append_effect_render_proofs(&folded.effect_proofs);
            folded.stmts.clone()
        } else {
            let proof_checkpoint = self.fold_ctx.effect_render_proof_checkpoint();
            let stmts = self.fold_ctx.fold_block(block, addr);
            let effect_proofs = self.fold_ctx.effect_render_proofs_since(proof_checkpoint);
            self.folded_block_cache.insert(
                addr,
                FoldedBlock {
                    stmts: stmts.clone(),
                    effect_proofs,
                },
            );
            stmts
        };
        self.validate_certified_block_domain(addr, &stmts);
        stmts
    }

    fn validate_certified_block_domain(&mut self, block_addr: u64, stmts: &[CStmt]) {
        if !self.fold_ctx.requires_certified_rendering() || stmts.is_empty() {
            return;
        }
        let Some(source) = self
            .fold_ctx
            .control_facts()
            .and_then(|facts| facts.control_domain_for_block(block_addr))
        else {
            self.safety_reason = Some(format!(
                "missing source control domain for emitted block 0x{block_addr:x}"
            ));
            return;
        };
        if !source.complete {
            self.safety_reason = Some(format!(
                "incomplete source control domain for emitted block 0x{block_addr:x}"
            ));
            return;
        }
        let mut alternatives = self.active_domains.clone();
        if let Some(domains) = self.transfer_target_domains.remove(&block_addr) {
            alternatives.extend(domains);
        }
        Self::normalize_rendered_domains(&mut alternatives);
        self.rendered_block_domains
            .entry(block_addr)
            .or_default()
            .push(RenderedBlockOccurrence { alternatives });
    }

    fn validate_rendered_block_domain_coverage(&mut self) {
        if !self.fold_ctx.requires_certified_rendering() || self.safety_reason.is_some() {
            return;
        }
        let rendered = self.rendered_block_domains.clone();
        for (block_addr, occurrences) in rendered {
            let Some(source) = self
                .fold_ctx
                .control_facts()
                .and_then(|facts| facts.control_domain_for_block(block_addr))
                .cloned()
            else {
                self.safety_reason = Some(format!(
                    "missing source control domain for emitted block 0x{block_addr:x}"
                ));
                return;
            };
            if !source.complete {
                self.safety_reason = Some(format!(
                    "incomplete source control domain for emitted block 0x{block_addr:x}"
                ));
                return;
            }
            if occurrences.iter().any(|occurrence| {
                occurrence.alternatives.iter().any(|alternative| {
                    !self.rendered_loop_domain_matches_source(
                        block_addr,
                        &source.loops,
                        &alternative.loops,
                    )
                })
            }) {
                self.safety_reason = Some(format!(
                    "loop-domain mismatch for emitted block 0x{block_addr:x}: source loops {:?}; rendered loops {:?}",
                    source.loops,
                    occurrences
                        .iter()
                        .flat_map(|occurrence| occurrence.alternatives.iter())
                        .map(|alternative| alternative.loops.clone())
                        .collect::<Vec<_>>()
                ));
                return;
            }
            if occurrences.len() == 1
                && occurrences[0].alternatives.len() == 1
                && occurrences[0].alternatives[0].guards == source.guards
            {
                continue;
            }
            match self.rendered_branch_occurrences_cover_source(block_addr, &occurrences) {
                Ok(true) => {}
                Ok(false) => {
                    self.safety_reason = Some(format!(
                        "control-domain coverage mismatch for emitted block 0x{block_addr:x}: source guards {:?}; rendered guard alternatives {:?}",
                        source.guards,
                        occurrences
                            .iter()
                            .map(|occurrence| {
                                occurrence
                                    .alternatives
                                    .iter()
                                    .map(|alternative| alternative.guards.clone())
                                    .collect::<Vec<_>>()
                            })
                            .collect::<Vec<_>>()
                    ));
                    return;
                }
                Err(reason) => {
                    self.safety_reason = Some(format!(
                        "control-domain coverage proof failed for emitted block 0x{block_addr:x}: {reason}"
                    ));
                    return;
                }
            }
        }
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
        let mut bdd = ControlBdd::new(self.safety_budget_remaining);
        let mut rendered_formula = BDD_FALSE;
        for occurrence in occurrences {
            let mut occurrence_formula = BDD_FALSE;
            for alternative in &occurrence.alternatives {
                let mut alternative_formula = BDD_TRUE;
                for guard in &alternative.guards {
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
            queued.remove(&from);
            let from_formula = reach.get(&from).copied().unwrap_or(BDD_FALSE);
            for to in self.func.successors(from) {
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
        if !self.consume_safety_budget(created_nodes) {
            return Err("control coverage exhausted structuring safety budget".to_string());
        }
        Ok(source_formula == rendered_formula)
    }

    fn certified_switch_guard_for_region(
        &self,
        switch_block: u64,
        region: &Region,
        case_value: Option<u64>,
        is_default: bool,
    ) -> Option<ControlGuard> {
        let domain = self
            .fold_ctx
            .control_facts()?
            .control_domain_for_block(region.entry())?;
        domain.guards.iter().find_map(|guard| {
            let ControlGuard::SwitchArm {
                block_addr,
                case_values,
                includes_default,
            } = guard
            else {
                return None;
            };
            let matches = block_addr == &switch_block
                && if is_default {
                    *includes_default && case_values.is_empty()
                } else {
                    !includes_default
                        && case_value.is_some_and(|value| case_values.contains(&value))
                };
            matches.then(|| guard.clone())
        })
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
            return (Some(cond), predicate_id, condition_value);
        }
        if self.fold_ctx.requires_certified_rendering() {
            return (None, predicate_id, condition_value);
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
    fn structure_irreducible(&mut self, entry: u64, blocks: &[u64]) -> CStmt {
        // Assign labels to all blocks
        for &addr in blocks {
            if !self.labels.contains_key(&addr) {
                let label = format!("L{}", self.label_counter);
                self.label_counter += 1;
                self.labels.insert(addr, label);
            }
        }

        // Start with the entry block
        let mut stmts = vec![self.structure_block(entry)];

        // Add remaining blocks with gotos
        for &addr in blocks {
            if addr != entry {
                stmts.push(self.structure_block(addr));
            }
        }

        CStmt::Block(stmts)
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
    pub(crate) fn cleanup(stmt: CStmt) -> CStmt {
        // Recurse first, then simplify
        let stmt = Self::cleanup_recurse(stmt);
        Self::flatten(stmt)
    }

    /// Normalize a certified statement tree without changing its control or
    /// effect inventory.  The only loop rewrite is the canonical equivalence
    /// `init; while (cond) { body; update; }` -> `for (init; cond; update)`;
    /// branch inversion, guard factoring, and tail truncation are deliberately
    /// excluded because they require their own proof transformations.
    pub(crate) fn cleanup_preserving_render_proof_identity(stmt: CStmt) -> CStmt {
        let stmt = match stmt {
            CStmt::Block(stmts) => {
                let cleaned = stmts
                    .into_iter()
                    .map(Self::cleanup_preserving_render_proof_identity)
                    .filter(|stmt| !matches!(stmt, CStmt::Empty))
                    .collect();
                let rewritten = Self::rewrite_block_loops_to_for(cleaned);
                Self::stmt_from_vec(rewritten)
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => CStmt::If {
                cond,
                then_body: Box::new(Self::cleanup_preserving_render_proof_identity(*then_body)),
                else_body: else_body
                    .map(|body| Box::new(Self::cleanup_preserving_render_proof_identity(*body))),
            },
            CStmt::While { cond, body } => CStmt::While {
                cond,
                body: Box::new(Self::strip_trailing_continue(
                    Self::cleanup_preserving_render_proof_identity(*body),
                )),
            },
            CStmt::DoWhile { body, cond } => CStmt::DoWhile {
                body: Box::new(Self::strip_trailing_continue(
                    Self::cleanup_preserving_render_proof_identity(*body),
                )),
                cond,
            },
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => CStmt::For {
                init: init
                    .map(|stmt| Box::new(Self::cleanup_preserving_render_proof_identity(*stmt))),
                cond,
                update,
                body: Box::new(Self::strip_trailing_continue(
                    Self::cleanup_preserving_render_proof_identity(*body),
                )),
            },
            CStmt::Switch {
                expr,
                cases,
                default,
            } => CStmt::Switch {
                expr,
                cases: cases
                    .into_iter()
                    .map(|case| crate::ast::SwitchCase {
                        value: case.value,
                        body: case
                            .body
                            .into_iter()
                            .map(Self::cleanup_preserving_render_proof_identity)
                            .filter(|stmt| !matches!(stmt, CStmt::Empty))
                            .collect(),
                    })
                    .collect(),
                default: default.map(|body| {
                    body.into_iter()
                        .map(Self::cleanup_preserving_render_proof_identity)
                        .filter(|stmt| !matches!(stmt, CStmt::Empty))
                        .collect()
                }),
            },
            other => other,
        };
        Self::flatten(stmt)
    }

    /// Recursively clean up children first, then apply local simplifications.
    fn cleanup_recurse(stmt: CStmt) -> CStmt {
        match stmt {
            CStmt::Block(stmts) => {
                let cleaned = stmts
                    .into_iter()
                    .map(Self::cleanup_recurse)
                    .filter(|s| !matches!(s, CStmt::Empty))
                    .collect();
                let cleaned = Self::rewrite_block_tail_guard_clauses(cleaned);
                let cleaned = Self::rewrite_guarded_switch_if_else(cleaned);
                let cleaned = Self::rewrite_continue_tail_merges(cleaned);
                let cleaned = Self::truncate_dead_straight_line_tail(cleaned);
                let rewritten = Self::rewrite_block_loops_to_for(cleaned);
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
                let cond = Self::normalize_condition_addr_artifacts(cond);
                let then_body = Box::new(Self::cleanup_recurse(*then_body));
                let else_body = else_body
                    .map(|e| Box::new(Self::cleanup_recurse(*e)))
                    .and_then(|e| (!matches!(*e, CStmt::Empty)).then_some(e));
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
                let cond = Self::normalize_condition_addr_artifacts(cond);
                let body = Self::strip_trailing_continue(Self::cleanup_recurse(*body));
                CStmt::While {
                    cond,
                    body: Box::new(body),
                }
            }
            CStmt::DoWhile { body, cond } => {
                let body = Self::strip_trailing_continue(Self::cleanup_recurse(*body));
                let cond = Self::normalize_condition_addr_artifacts(cond);
                // Fix C: do { if (c) break; rest } while(1) -> while(!c) { rest }
                Self::try_convert_do_while_to_while(body, cond)
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                let cond = cond.map(Self::normalize_condition_addr_artifacts);
                let body = Self::strip_trailing_continue(Self::cleanup_recurse(*body));
                let body = update
                    .as_ref()
                    .map(|update| Self::strip_trailing_for_update(body.clone(), update))
                    .unwrap_or(body);
                let body = Self::remove_dead_generated_artifact_assignments(body);
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
                        body: Self::cleanup_switch_body(c.body),
                    })
                    .collect();
                let default = default.map(Self::cleanup_switch_body);
                CStmt::Switch {
                    expr,
                    cases,
                    default,
                }
            }
            CStmt::Expr(expr) => CStmt::Expr(Self::rewrite_compound_assignment_expr(expr)),
            other => other,
        }
    }

    fn cleanup_switch_body(stmts: Vec<CStmt>) -> Vec<CStmt> {
        let cleaned = stmts
            .into_iter()
            .map(Self::cleanup_recurse)
            .filter(|stmt| !matches!(stmt, CStmt::Empty))
            .collect();
        Self::truncate_dead_straight_line_tail(cleaned)
    }

    fn rewrite_compound_assignment_expr(expr: CExpr) -> CExpr {
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

        let Some((op, rhs)) = Self::compound_assignment_rhs(target_name, right.as_ref()) else {
            return CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            };
        };

        CExpr::Binary {
            op,
            left,
            right: Box::new(rhs),
        }
    }

    fn compound_assignment_rhs(target_name: &str, rhs: &CExpr) -> Option<(BinaryOp, CExpr)> {
        let CExpr::Binary { op, left, right } = rhs else {
            return None;
        };
        let compound_op = Self::compound_assignment_op(*op)?;

        if Self::expr_is_var_named(left, target_name) && Self::expr_is_side_effect_free(right) {
            return Some((compound_op, right.as_ref().clone()));
        }

        if Self::binary_op_is_commutative_for_compound(*op)
            && Self::expr_is_var_named(right, target_name)
            && Self::expr_is_side_effect_free(left)
        {
            return Some((compound_op, left.as_ref().clone()));
        }

        None
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

    fn expr_is_var_named(expr: &CExpr, target_name: &str) -> bool {
        matches!(expr, CExpr::Var(name) if name == target_name)
    }

    fn expr_is_side_effect_free(expr: &CExpr) -> bool {
        match expr {
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::Var(_)
            | CExpr::SizeofType(_) => true,
            CExpr::Paren(inner)
            | CExpr::AddrOf(inner)
            | CExpr::Deref(inner)
            | CExpr::Cast { expr: inner, .. }
            | CExpr::Sizeof(inner) => Self::expr_is_side_effect_free(inner),
            CExpr::Unary { op, operand } => {
                !matches!(
                    op,
                    UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec
                ) && Self::expr_is_side_effect_free(operand)
            }
            CExpr::Binary { op, left, right } => {
                !Self::is_assignment_like_op(*op)
                    && Self::expr_is_side_effect_free(left)
                    && Self::expr_is_side_effect_free(right)
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                Self::expr_is_side_effect_free(cond)
                    && Self::expr_is_side_effect_free(then_expr)
                    && Self::expr_is_side_effect_free(else_expr)
            }
            CExpr::Subscript { base, index } => {
                Self::expr_is_side_effect_free(base) && Self::expr_is_side_effect_free(index)
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                Self::expr_is_side_effect_free(base)
            }
            CExpr::Comma(items) => items.iter().all(Self::expr_is_side_effect_free),
            CExpr::Call { .. } => false,
        }
    }

    fn is_assignment_like_op(op: BinaryOp) -> bool {
        op == BinaryOp::Assign || Self::is_compound_assign_op(op)
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
        matches!(expr, CExpr::IntLit(1) | CExpr::UIntLit(1))
    }

    fn is_const_false_expr(expr: &CExpr) -> bool {
        matches!(expr, CExpr::IntLit(0) | CExpr::UIntLit(0))
    }

    fn rewrite_if_short_circuit(stmt: CStmt) -> CStmt {
        let CStmt::If {
            cond,
            then_body,
            else_body,
        } = stmt
        else {
            return stmt;
        };

        let then_stmt = (*then_body).clone();
        let else_stmt = else_body.as_ref().map(|b| (**b).clone());

        // if (a) { if (b) { T } } -> if (a && b) { T }
        if else_body.is_none()
            && let CStmt::If {
                cond: inner_cond,
                then_body: inner_then,
                else_body: None,
            } = &then_stmt
        {
            return CStmt::If {
                cond: CExpr::binary(BinaryOp::And, cond, inner_cond.clone()),
                then_body: inner_then.clone(),
                else_body: None,
            };
        }

        // if (a) { T } else if (b) { T } -> if (a || b) { T }
        if let Some(CStmt::If {
            cond: right_cond,
            then_body: right_then,
            else_body: None,
        }) = else_stmt.as_ref()
            && then_stmt == **right_then
        {
            return CStmt::If {
                cond: CExpr::binary(BinaryOp::Or, cond, right_cond.clone()),
                then_body: Box::new(then_stmt),
                else_body: None,
            };
        }

        // if (a) { if (b) { T } } else { T } -> if (!a || b) { T }
        if let CStmt::If {
            cond: inner_cond,
            then_body: inner_then,
            else_body: None,
        } = &then_stmt
            && let Some(outer_else) = else_stmt.as_ref()
            && *outer_else == **inner_then
        {
            return CStmt::If {
                cond: CExpr::binary(
                    BinaryOp::Or,
                    Self::negate_condition(cond),
                    inner_cond.clone(),
                ),
                then_body: inner_then.clone(),
                else_body: None,
            };
        }

        // if (a) { if (b) { T } else { E } } else { E } -> if (a && b) { T } else { E }
        if let CStmt::If {
            cond: inner_cond,
            then_body: inner_then,
            else_body: Some(inner_else),
        } = &then_stmt
            && let Some(outer_else) = else_stmt.as_ref()
            && *outer_else == **inner_else
        {
            return CStmt::If {
                cond: CExpr::binary(BinaryOp::And, cond, inner_cond.clone()),
                then_body: inner_then.clone(),
                else_body: Some(inner_else.clone()),
            };
        }

        CStmt::If {
            cond,
            then_body,
            else_body,
        }
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
        match stmt {
            CStmt::Block(stmts) => out.extend(stmts),
            CStmt::Empty => {}
            other => out.push(other),
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

        if matches!(then_body.as_ref(), CStmt::Empty) {
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
        match stmt {
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
        match cond {
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
        matches!(expr, CExpr::IntLit(0) | CExpr::UIntLit(0))
    }

    fn expr_divides_by(expr: &CExpr, denominator: &CExpr) -> bool {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Div,
                right,
                ..
            } => right.as_ref() == denominator,
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
    ) -> Option<CStmt> {
        let merge_block = merge_block?;
        let else_region = else_region?;
        let certified = self.fold_ctx.requires_certified_rendering();

        let summaries = self
            .fold_ctx
            .frame_slot_merges_map()
            .values()
            .filter(|summary| summary.merge_block_addr == merge_block)
            .collect::<Vec<_>>();
        let [summary] = summaries.as_slice() else {
            return None;
        };

        let then_pred = self.unique_region_predecessor_to_merge(then_region, merge_block);
        let else_pred = self.unique_region_predecessor_to_merge(else_region, merge_block);
        let then_can_rewrite = then_pred
            .is_some_and(|pred| self.has_merged_slot_return_expr(then_region, pred, summary));
        let else_can_rewrite = else_pred
            .is_some_and(|pred| self.has_merged_slot_return_expr(else_region, pred, summary));
        if !then_can_rewrite && !else_can_rewrite {
            return None;
        }
        if certified
            && (!self.certified_region_terminates_with_slot_merge(then_region, summary)
                || !self.certified_region_terminates_with_slot_merge(else_region, summary))
        {
            return None;
        }

        let certified_branch = if certified {
            let (cond, predicate, condition_value) =
                self.get_branch_condition_with_predicate(cond_block);
            let cond = cond?;
            let proof =
                self.certified_branch_render_proof(cond_block, predicate, condition_value)?;
            Some((cond, proof))
        } else {
            None
        };
        let control_proof_checkpoint = self.control_render_proofs.len();
        let effect_proof_checkpoint = self.fold_ctx.effect_render_proof_checkpoint();
        if let Some((_, proof)) = &certified_branch {
            self.control_render_proofs.push(proof.clone());
        }

        let mut then_stmt = if certified && then_can_rewrite {
            CStmt::Empty
        } else if certified {
            self.structure_branch_region(cond_block, then_region)
        } else {
            self.structure_region(then_region)
        };
        let mut else_stmt = if certified && else_can_rewrite {
            CStmt::Empty
        } else if certified {
            self.structure_branch_region(cond_block, else_region)
        } else {
            self.structure_region(else_region)
        };
        let mut rewrote_any = false;

        if then_can_rewrite
            && let Some(pred) = then_pred
            && let Some(rewritten) = self.append_merged_slot_return_if_needed(
                then_stmt.clone(),
                then_region,
                pred,
                summary,
            )
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
            )
        {
            else_stmt = rewritten;
            rewrote_any = true;
        }
        if !rewrote_any
            || !Self::stmt_guarantees_termination(&then_stmt)
            || !Self::stmt_guarantees_termination(&else_stmt)
        {
            if certified {
                if self.safety_reason.is_none() {
                    self.safety_reason = Some(format!(
                        "certified stack-slot return merge at 0x{merge_block:x} did not preserve terminating paths"
                    ));
                }
                return Some(CStmt::Empty);
            }
            self.control_render_proofs
                .truncate(control_proof_checkpoint);
            self.fold_ctx
                .truncate_effect_render_proofs(effect_proof_checkpoint);
            return None;
        }

        let (cond, predicate, condition_value) = if let Some((cond, _)) = certified_branch {
            (Some(cond), None, None)
        } else {
            self.get_branch_condition_with_predicate(cond_block)
        };
        let cond = cond?;
        let if_stmt = CStmt::If {
            cond,
            then_body: Box::new(then_stmt),
            else_body: Some(Box::new(else_stmt)),
        };
        if !certified {
            self.record_branch_render_proof(cond_block, predicate, condition_value);
        }
        let mut prefix = self.structure_block_prefix_stmts(cond_block);
        prefix.push(if_stmt);
        Some(if prefix.len() == 1 {
            prefix.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(prefix)
        })
    }

    fn try_structure_if_else_with_register_merge_returns(
        &mut self,
        cond_block: u64,
        then_region: &Region,
        else_region: Option<&Region>,
        merge_block: Option<u64>,
    ) -> Option<CStmt> {
        let merge_block = merge_block?;
        let else_region = else_region?;
        let then_pred = self.unique_region_predecessor_to_merge(then_region, merge_block);
        let else_pred = self.unique_region_predecessor_to_merge(else_region, merge_block);
        let mut then_can_rewrite =
            then_pred.is_some_and(|pred| self.has_merged_register_return_expr(merge_block, pred));
        let mut else_can_rewrite =
            else_pred.is_some_and(|pred| self.has_merged_register_return_expr(merge_block, pred));
        let certified_branch = if self.fold_ctx.requires_certified_rendering() {
            if !then_can_rewrite || !else_can_rewrite {
                return None;
            }
            let (cond, predicate, condition_value) =
                self.get_branch_condition_with_predicate(cond_block);
            let cond = cond?;
            let proof =
                self.certified_branch_render_proof(cond_block, predicate, condition_value)?;
            Some((cond, proof))
        } else {
            None
        };
        let control_proof_checkpoint = self.control_render_proofs.len();
        if let Some((_, proof)) = &certified_branch {
            self.control_render_proofs.push(proof.clone());
        }

        let mut then_stmt = self.structure_region(then_region);
        let mut else_stmt = self.structure_region(else_region);
        then_can_rewrite |= then_pred.is_some_and(|pred| {
            self.stmt_has_predecessor_return_register_certificate(&then_stmt, pred)
        });
        else_can_rewrite |= else_pred.is_some_and(|pred| {
            self.stmt_has_predecessor_return_register_certificate(&else_stmt, pred)
        });
        if !then_can_rewrite && !else_can_rewrite {
            self.control_render_proofs
                .truncate(control_proof_checkpoint);
            return None;
        }
        let mut rewrote_any = false;

        if then_can_rewrite
            && let Some(pred) = then_pred
            && let Some(rewritten) =
                self.append_merged_register_return_if_needed(then_stmt.clone(), merge_block, pred)
        {
            then_stmt = rewritten;
            rewrote_any = true;
        }
        if else_can_rewrite
            && let Some(pred) = else_pred
            && let Some(rewritten) =
                self.append_merged_register_return_if_needed(else_stmt.clone(), merge_block, pred)
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
            return None;
        }

        let (cond, predicate, condition_value) = if let Some((cond, _)) = certified_branch {
            (Some(cond), None, None)
        } else {
            self.get_branch_condition_with_predicate(cond_block)
        };
        let cond = cond?;
        let if_stmt = CStmt::If {
            cond,
            then_body: Box::new(then_stmt),
            else_body: Some(Box::new(else_stmt)),
        };
        if !self.fold_ctx.requires_certified_rendering() {
            self.record_branch_render_proof(cond_block, predicate, condition_value);
        }
        let mut prefix = self.structure_block_prefix_stmts(cond_block);
        prefix.push(if_stmt);
        Some(if prefix.len() == 1 {
            prefix.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(prefix)
        })
    }

    fn try_structure_guarded_switch_with_default(
        &mut self,
        cond_block: u64,
        then_region: &Region,
        else_region: Option<&Region>,
        merge_block: Option<u64>,
    ) -> Option<CStmt> {
        let else_region = else_region?;
        let (switch_view, default_region) = match (
            Self::switch_region_view(then_region),
            Self::switch_region_view(else_region),
        ) {
            (Some(switch_view), None) => (switch_view, else_region),
            (None, Some(switch_view)) => (switch_view, then_region),
            _ => return None,
        };

        if self.func.switch_info(switch_view.switch_block).is_some() {
            return None;
        }
        if switch_view.default.is_some() || switch_view.cases.len() < 4 {
            return None;
        }
        if !self
            .func
            .successors(cond_block)
            .contains(&switch_view.entry_block)
        {
            return None;
        }

        let combined_merge = merge_block.or(switch_view.merge_block);
        let mut prefix = self.structure_block_prefix_stmts(cond_block);
        for region in switch_view.prefix_regions {
            Self::append_stmt_body_flat(&mut prefix, self.structure_region(region));
        }
        let switch_stmt = self.structure_switch_region(
            switch_view.switch_block,
            switch_view.cases,
            Some(default_region),
            None,
        );
        Self::append_stmt_body_flat(&mut prefix, switch_stmt);
        if let Some(merge_addr) = combined_merge {
            Self::append_stmt_body_flat(&mut prefix, self.structure_block(merge_addr));
        }
        Some(if prefix.len() == 1 {
            prefix.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(prefix)
        })
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
        candidates.sort_unstable();
        candidates.dedup();
        match candidates.as_slice() {
            [pred] => Some(*pred),
            _ => None,
        }
    }

    fn transparent_branch_successor_to_merge(&self, addr: u64, merge_block: u64) -> Option<u64> {
        let block = self.func.get_block(addr)?;
        let successors = self.transparent_branch_successors(addr, block);
        let [successor] = successors.as_slice() else {
            return None;
        };
        if !block.ops.iter().all(|op| {
            self.is_transparent_branch_forwarder_op(op)
                || self.is_materialized_phi_edge_copy(addr, *successor, op)
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

    fn is_materialized_phi_edge_copy(&self, pred_addr: u64, successor: u64, op: &SSAOp) -> bool {
        let SSAOp::Copy { dst, src } = op else {
            return false;
        };
        self.func.get_block(successor).is_some_and(|block| {
            block.phis.iter().any(|phi| {
                phi.dst == *dst
                    && phi
                        .sources
                        .iter()
                        .any(|(pred, value)| *pred == pred_addr && value == src)
            })
        })
    }

    fn is_transparent_branch_forwarder_op(&self, op: &SSAOp) -> bool {
        match op {
            SSAOp::Branch { .. } | SSAOp::Nop => true,
            SSAOp::Copy { dst, .. } => !self.func.has_noncarrier_use(dst),
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
        region: &Region,
        pred_addr: u64,
        summary: &crate::analysis::FrameSlotMergeSummary,
    ) -> Option<CStmt> {
        if self.fold_ctx.requires_certified_rendering() {
            let (expr, source, proof_block, proof_op, proof_value) = self
                .fold_ctx
                .certified_merged_slot_return_candidate_for_region(
                    summary.merge_block_addr,
                    pred_addr,
                    summary.slot_offset,
                    &region.blocks(),
                )?;
            let return_stmt = CStmt::Return(Some(expr.clone()));
            self.fold_ctx
                .record_certified_call_render_proofs_for_stmt(&return_stmt)?;
            if let Some((read_block, read_op, address, read_value)) = self
                .fold_ctx
                .certified_memory_read_for_value_dependency(source)
                .map(|cert| (cert.block_addr, cert.op_index, cert.address, cert.value))
            {
                self.fold_ctx.record_effect_render_proof_for_memory(
                    EffectRenderProofKind::MemoryRead,
                    read_block,
                    read_op,
                    address,
                    read_value,
                );
            }
            self.record_return_value_render_proof(proof_block, proof_op, proof_value);
            if let Some(rewritten) = self.rewrite_trailing_return_with_merged_expr(&stmt, &expr) {
                return Some(rewritten);
            }
            if Self::single_terminator_stmt(&stmt).is_some() {
                return Some(stmt);
            }
            let mut stmts = Vec::new();
            Self::append_stmt_body_flat(&mut stmts, stmt);
            stmts.push(return_stmt);
            return Some(if stmts.len() == 1 {
                stmts.into_iter().next().unwrap_or(CStmt::Empty)
            } else {
                CStmt::Block(stmts)
            });
        }
        let mut visited = std::collections::HashSet::new();
        let expr = summary
            .incoming
            .get(&pred_addr)
            .and_then(|value| self.fold_ctx.render_semantic_value(value, 0, &mut visited))
            .or_else(|| {
                self.fold_ctx
                    .merged_return_candidate_for_block_slot(pred_addr, summary.slot_offset)
            })?;
        let stmt = self.prepend_named_merged_slot_assignment_if_needed(stmt, summary, &expr);
        if let Some(rewritten) = self.rewrite_trailing_return_with_merged_expr(&stmt, &expr) {
            return Some(rewritten);
        }
        if Self::single_terminator_stmt(&stmt).is_some() {
            return Some(stmt);
        }
        let mut stmts = Vec::new();
        Self::append_stmt_body_flat(&mut stmts, stmt);
        stmts.push(CStmt::Return(Some(expr)));
        Some(if stmts.len() == 1 {
            stmts.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(stmts)
        })
    }

    fn has_merged_slot_return_expr(
        &self,
        region: &Region,
        pred_addr: u64,
        summary: &crate::analysis::FrameSlotMergeSummary,
    ) -> bool {
        if self.fold_ctx.requires_certified_rendering() {
            return self
                .fold_ctx
                .certified_merged_slot_return_candidate_for_region(
                    summary.merge_block_addr,
                    pred_addr,
                    summary.slot_offset,
                    &region.blocks(),
                )
                .is_some();
        }
        summary.incoming.contains_key(&pred_addr)
            || self
                .fold_ctx
                .merged_return_candidate_for_block_slot(pred_addr, summary.slot_offset)
                .is_some()
    }

    fn certified_region_terminates_with_slot_merge(
        &self,
        region: &Region,
        summary: &crate::analysis::FrameSlotMergeSummary,
    ) -> bool {
        let predecessor = self.unique_region_predecessor_to_merge(region, summary.merge_block_addr);
        if let Some(pred) = predecessor
            && self.has_merged_slot_return_expr(region, pred, summary)
        {
            return true;
        }
        match region {
            Region::Sequence(regions) => regions.last().is_some_and(|tail| {
                self.certified_region_terminates_with_slot_merge(tail, summary)
            }),
            Region::IfThenElse {
                then_region,
                else_region: Some(else_region),
                ..
            } => {
                self.certified_region_terminates_with_slot_merge(then_region, summary)
                    && self.certified_region_terminates_with_slot_merge(else_region, summary)
            }
            _ => false,
        }
    }

    fn append_merged_register_return_if_needed(
        &self,
        stmt: CStmt,
        merge_addr: u64,
        pred_addr: u64,
    ) -> Option<CStmt> {
        if !self.block_allows_predecessor_return_register_rewrite(merge_addr) {
            return None;
        }
        let Some((expr, proof_block, proof_op, proof_value)) =
            self.return_register_candidate_for_merge_predecessor(merge_addr, pred_addr)
        else {
            if Self::single_return_expr(&stmt).is_some()
                && let Some((proof_block, proof_op, proof_value)) =
                    self.predecessor_return_register_certificate(pred_addr)
            {
                self.record_return_value_render_proof(proof_block, proof_op, proof_value);
                return Some(stmt);
            }
            return None;
        };
        if let Some(rewritten) = self.rewrite_trailing_return_with_merged_expr(&stmt, &expr) {
            self.record_return_value_render_proof(proof_block, proof_op, proof_value);
            return Some(rewritten);
        }
        if Self::single_terminator_stmt(&stmt).is_some() {
            return Some(stmt);
        }
        let mut stmts = Vec::new();
        Self::append_stmt_body_flat(&mut stmts, stmt);
        stmts.push(CStmt::Return(Some(expr)));
        self.record_return_value_render_proof(proof_block, proof_op, proof_value);
        Some(if stmts.len() == 1 {
            stmts.into_iter().next().unwrap_or(CStmt::Empty)
        } else {
            CStmt::Block(stmts)
        })
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

    fn has_merged_register_return_expr(&self, merge_addr: u64, pred_addr: u64) -> bool {
        self.return_register_candidate_for_merge_predecessor(merge_addr, pred_addr)
            .is_some()
    }

    fn record_return_value_render_proof(&self, block_addr: u64, op_idx: usize, value: ValueId) {
        self.fold_ctx.record_effect_render_proof_for_value(
            EffectRenderProofKind::Return,
            block_addr,
            op_idx,
            Some(value),
        );
        if let Some((read_block, read_op, address, read_value)) = self
            .fold_ctx
            .certified_memory_read_for_value_dependency(value)
            .map(|cert| (cert.block_addr, cert.op_index, cert.address, cert.value))
        {
            self.fold_ctx.record_effect_render_proof_for_memory(
                EffectRenderProofKind::MemoryRead,
                read_block,
                read_op,
                address,
                read_value,
            );
        }
    }

    fn prepend_named_merged_slot_assignment_if_needed(
        &self,
        stmt: CStmt,
        summary: &crate::analysis::FrameSlotMergeSummary,
        expr: &CExpr,
    ) -> CStmt {
        let Some(local_name) = self
            .fold_ctx
            .resolve_stack_var(summary.slot_offset)
            .filter(|name| !crate::fold::op_lower::is_generic_stack_placeholder_alias(name))
        else {
            return stmt;
        };

        let lhs = CExpr::Var(local_name);
        let resolved_expr = self.fold_ctx.resolve_return_candidate(expr);
        if lhs == *expr || lhs == resolved_expr {
            return stmt;
        }

        let assignment = CStmt::Expr(CExpr::assign(lhs, resolved_expr.clone()));
        if Self::stmt_starts_with_assignment(&stmt, &assignment) {
            return stmt;
        }
        match stmt {
            CStmt::Empty => assignment,
            CStmt::Block(mut stmts) => {
                stmts.insert(0, assignment);
                CStmt::Block(stmts)
            }
            other => CStmt::Block(vec![assignment, other]),
        }
    }

    fn stmt_starts_with_assignment(stmt: &CStmt, assignment: &CStmt) -> bool {
        match stmt {
            CStmt::Block(stmts) => stmts.first().is_some_and(|first| first == assignment),
            other => other == assignment,
        }
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
            CStmt::Return(Some(_current)) => Some(CStmt::Return(Some(merged.clone()))),
            CStmt::Comment(reason)
                if !self.fold_ctx.requires_certified_rendering()
                    && reason.starts_with(
                        "r2sleigh residual: unresolved value return for control-only exit",
                    ) =>
            {
                Some(CStmt::Return(Some(merged.clone())))
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
                } = &stmts[i]
                && let Some(terminator) = Self::single_terminator_stmt(&stmts[i + 1])
                && Self::single_terminator_stmt(then_body.as_ref()).is_none()
                && !matches!(then_body.as_ref(), CStmt::Empty)
            {
                rewritten.push(CStmt::If {
                    cond: Self::negate_condition(cond.clone()),
                    then_body: Box::new(terminator),
                    else_body: None,
                });
                Self::append_stmt_body_flat(&mut rewritten, (**then_body).clone());
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

    fn rewrite_continue_tail_merges(stmts: Vec<CStmt>) -> Vec<CStmt> {
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
                    Self::split_trailing_update_continue((**then_body).clone())
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
            && then_stmts.last() == else_stmts.last()
            && !Self::stmt_list_contains_control_transfer(&then_stmts[..then_stmts.len() - 1])
            && !Self::stmt_list_contains_control_transfer(&else_stmts[..else_stmts.len() - 1])
        {
            common_suffix.push(then_stmts.pop().expect("then suffix"));
            else_stmts.pop();
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

    fn stmt_list_contains_control_transfer(stmts: &[CStmt]) -> bool {
        stmts.iter().any(Self::stmt_contains_control_transfer)
    }

    fn stmt_contains_control_transfer(stmt: &CStmt) -> bool {
        if Self::stmt_is_unconditional_terminator(stmt) {
            return true;
        }
        match stmt {
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

    fn split_trailing_update_continue(stmt: CStmt) -> Option<(Vec<CStmt>, CStmt)> {
        let mut stmts = Self::stmt_into_vec(stmt);
        while matches!(stmts.last(), Some(CStmt::Empty)) {
            stmts.pop();
        }
        if !matches!(stmts.last(), Some(CStmt::Continue)) {
            return None;
        }
        stmts.pop();
        while matches!(stmts.last(), Some(CStmt::Empty)) {
            stmts.pop();
        }
        while stmts
            .last()
            .is_some_and(Self::is_generated_side_effect_free_assignment)
        {
            stmts.pop();
            while matches!(stmts.last(), Some(CStmt::Empty)) {
                stmts.pop();
            }
        }
        let tail_stmt = stmts.pop()?;
        Self::stmt_is_self_update(&tail_stmt).then_some((stmts, tail_stmt))
    }

    fn strip_trailing_for_update(body: CStmt, update: &CExpr) -> CStmt {
        let mut stmts = Self::stmt_into_vec(body);
        while matches!(stmts.last(), Some(CStmt::Empty)) {
            stmts.pop();
        }
        if matches!(
            stmts.last(),
            Some(CStmt::Expr(expr)) if Self::expr_matches_for_update(expr, update)
        ) {
            stmts.pop();
        }
        Self::stmt_from_vec(stmts)
    }

    fn remove_dead_generated_artifact_assignments(stmt: CStmt) -> CStmt {
        match stmt {
            CStmt::Block(stmts) => {
                let stmts = stmts
                    .into_iter()
                    .map(Self::remove_dead_generated_artifact_assignments)
                    .collect();
                Self::stmt_from_vec(Self::remove_dead_generated_artifact_assignments_from_vec(
                    stmts,
                ))
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => CStmt::If {
                cond,
                then_body: Box::new(Self::remove_dead_generated_artifact_assignments(*then_body)),
                else_body: else_body
                    .map(|body| Box::new(Self::remove_dead_generated_artifact_assignments(*body))),
            },
            CStmt::While { cond, body } => CStmt::While {
                cond,
                body: Box::new(Self::remove_dead_generated_artifact_assignments(*body)),
            },
            CStmt::DoWhile { body, cond } => CStmt::DoWhile {
                body: Box::new(Self::remove_dead_generated_artifact_assignments(*body)),
                cond,
            },
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => CStmt::For {
                init,
                cond,
                update,
                body: Box::new(Self::remove_dead_generated_artifact_assignments(*body)),
            },
            CStmt::Switch {
                expr,
                cases,
                default,
            } => CStmt::Switch {
                expr,
                cases: cases
                    .into_iter()
                    .map(|case| crate::ast::SwitchCase {
                        value: case.value,
                        body: Self::remove_dead_generated_artifact_assignments_from_vec(case.body),
                    })
                    .collect(),
                default: default.map(Self::remove_dead_generated_artifact_assignments_from_vec),
            },
            other => other,
        }
    }

    fn remove_dead_generated_artifact_assignments_from_vec(stmts: Vec<CStmt>) -> Vec<CStmt> {
        let mut live = HashSet::new();
        let mut kept = Vec::with_capacity(stmts.len());
        for stmt in stmts.into_iter().rev() {
            if let Some((def, reads, generated, side_effect_free)) =
                Self::stmt_assignment_def_reads(&stmt)
            {
                if generated && side_effect_free && !Self::set_contains_loop_var(&live, &def) {
                    continue;
                }
                Self::set_remove_loop_var_aliases(&mut live, &def);
                live.extend(reads);
            } else {
                live.extend(Self::collect_stmt_vars(&stmt));
            }
            kept.push(stmt);
        }
        kept.reverse();
        kept
    }

    fn expr_matches_for_update(body_expr: &CExpr, for_update: &CExpr) -> bool {
        if body_expr == for_update {
            return true;
        }

        Self::normalized_self_update_signature(body_expr)
            .zip(Self::normalized_self_update_signature(for_update))
            .is_some_and(|(body, update)| body == update)
    }

    fn normalized_self_update_signature(expr: &CExpr) -> Option<(String, BinaryOp, CExpr)> {
        let CExpr::Binary { op, left, right } = expr else {
            return None;
        };
        let CExpr::Var(name) = left.as_ref() else {
            return None;
        };

        if Self::is_compound_assign_op(*op) {
            return Some((name.clone(), *op, right.as_ref().clone()));
        }

        if *op == BinaryOp::Assign
            && let Some((compound_op, rhs)) = Self::compound_assignment_rhs(name, right)
        {
            return Some((name.clone(), compound_op, rhs));
        }

        None
    }

    fn stmt_is_self_update(stmt: &CStmt) -> bool {
        let CStmt::Expr(expr) = stmt else {
            return false;
        };
        match expr {
            CExpr::Unary { op, operand } => {
                matches!(
                    op,
                    UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec
                ) && matches!(operand.as_ref(), CExpr::Var(_))
            }
            CExpr::Binary { op, left, right } => {
                let CExpr::Var(name) = left.as_ref() else {
                    return false;
                };
                if Self::is_compound_assign_op(*op) {
                    return true;
                }
                if *op != BinaryOp::Assign {
                    return false;
                }
                let rhs_vars = Self::collect_expr_vars(right);
                Self::set_contains_loop_var(&rhs_vars, name)
            }
            _ => false,
        }
    }

    fn truncate_dead_straight_line_tail(stmts: Vec<CStmt>) -> Vec<CStmt> {
        let mut rewritten = Vec::with_capacity(stmts.len());
        let mut terminated = false;
        for stmt in stmts {
            match stmt {
                CStmt::Label(_) => {
                    terminated = false;
                    rewritten.push(stmt);
                }
                other => {
                    if terminated {
                        continue;
                    }
                    terminated = Self::stmt_guarantees_termination(&other);
                    rewritten.push(other);
                }
            }
        }
        rewritten
    }

    fn stmt_guarantees_termination(stmt: &CStmt) -> bool {
        if Self::stmt_is_unconditional_terminator(stmt) {
            return true;
        }

        match stmt {
            CStmt::Block(stmts) => stmts
                .iter()
                .rev()
                .find(|stmt| !matches!(stmt, CStmt::Empty))
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

        if let CStmt::Block(stmts) = stmt
            && stmts.len() == 1
            && Self::stmt_is_unconditional_terminator(&stmts[0])
        {
            return Some(stmts[0].clone());
        }

        None
    }

    fn single_switch_stmt(stmt: &CStmt) -> Option<CStmt> {
        match stmt {
            CStmt::Switch { .. } => Some(stmt.clone()),
            CStmt::Block(stmts) if stmts.len() == 1 && matches!(stmts[0], CStmt::Switch { .. }) => {
                Some(stmts[0].clone())
            }
            _ => None,
        }
    }

    fn extract_switch_with_trailing_stmt(stmt: &CStmt) -> Option<(CStmt, Option<CStmt>)> {
        match stmt {
            CStmt::Switch { .. } => Some((stmt.clone(), None)),
            CStmt::Block(stmts) => {
                let stmts = stmts
                    .iter()
                    .filter(|stmt| !matches!(stmt, CStmt::Empty))
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
        match expr {
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
    fn rewrite_block_loops_to_for(stmts: Vec<CStmt>) -> Vec<CStmt> {
        let mut rewritten = Vec::with_capacity(stmts.len());
        let mut i = 0;
        while i < stmts.len() {
            if i + 1 < stmts.len()
                && let Some(mut for_stmts) = Self::try_rewrite_while_with_preheader_init(
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

    fn try_rewrite_while_with_preheader_init(
        preheader_stmt: CStmt,
        while_stmt: CStmt,
    ) -> Option<Vec<CStmt>> {
        let (prefix_stmts, init_stmt, induction_var) = Self::split_preheader_init(preheader_stmt)?;
        let CStmt::While { cond, body } = while_stmt else {
            return None;
        };

        let (loop_cond, loop_body) = match cond {
            CExpr::IntLit(v) if v != 0 => {
                let (exit_cond, stripped_body) = Self::extract_guard_break_cond(*body)?;
                (CExpr::unary(UnaryOp::Not, exit_cond), stripped_body)
            }
            _ => (cond, *body),
        };

        let cond_vars = Self::collect_expr_vars(&loop_cond);
        let cond_reads_induction = Self::set_contains_loop_var(&cond_vars, &induction_var);
        let (update, body_without_update, update_links_cond) =
            Self::extract_loop_update(&induction_var, &cond_vars, loop_body)?;

        if !cond_reads_induction && !update_links_cond {
            return None;
        }

        let mut rewritten = prefix_stmts;
        let body_without_update =
            Self::remove_dead_generated_artifact_assignments(body_without_update);
        rewritten.push(CStmt::For {
            init: Some(Box::new(init_stmt)),
            cond: Some(loop_cond),
            update: Some(update),
            body: Box::new(body_without_update),
        });
        Some(rewritten)
    }

    fn extract_induction_var_from_init(init_stmt: &CStmt) -> Option<String> {
        match init_stmt {
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                ..
            }) => match left.as_ref() {
                CExpr::Var(name) => Some(name.clone()),
                _ => None,
            },
            CStmt::Decl {
                name,
                init: Some(_),
                ..
            } => Some(name.clone()),
            _ => None,
        }
    }

    fn split_preheader_init(preheader_stmt: CStmt) -> Option<(Vec<CStmt>, CStmt, String)> {
        if let Some(var) = Self::extract_induction_var_from_init(&preheader_stmt) {
            return Some((Vec::new(), preheader_stmt, var));
        }

        let CStmt::Block(mut prefix) = preheader_stmt else {
            return None;
        };
        while matches!(prefix.last(), Some(CStmt::Empty)) {
            prefix.pop();
        }
        let init_stmt = prefix.pop()?;
        let var = Self::extract_induction_var_from_init(&init_stmt)?;
        Some((prefix, init_stmt, var))
    }

    fn extract_loop_update(
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

        while matches!(effective.last(), Some(CStmt::Empty | CStmt::Continue)) {
            effective.pop();
        }
        if effective.is_empty() {
            return None;
        }

        for idx in (0..effective.len()).rev() {
            if !effective[idx + 1..]
                .iter()
                .all(|stmt| Self::is_removable_trailing_loop_artifact(stmt, var, cond_vars))
            {
                break;
            }
            let prev_stmts = &effective[..idx];
            if let Some((update, update_links_cond)) =
                Self::update_expr_from_stmt(var, cond_vars, prev_stmts, &effective[idx])
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

    fn update_expr_from_stmt(
        var: &str,
        cond_vars: &HashSet<String>,
        prev_stmts: &[CStmt],
        stmt: &CStmt,
    ) -> Option<(CExpr, bool)> {
        let CStmt::Expr(expr) = stmt else {
            return None;
        };
        match expr {
            CExpr::Unary { op, operand }
                if matches!(
                    op,
                    UnaryOp::PreInc | UnaryOp::PostInc | UnaryOp::PreDec | UnaryOp::PostDec
                ) && matches!(operand.as_ref(), CExpr::Var(name) if Self::loop_var_equiv(name, var)) =>
            {
                Some((expr.clone(), false))
            }
            CExpr::Binary { op, left, right } if matches!(left.as_ref(), CExpr::Var(_)) => {
                let CExpr::Var(left_name) = left.as_ref() else {
                    return None;
                };
                let left_is_induction = Self::loop_var_equiv(left_name, var);
                let left_feeds_condition = Self::set_contains_loop_var(cond_vars, left_name);
                if *op == BinaryOp::Assign {
                    let rhs_vars = Self::collect_expr_vars(right);
                    let links_cond_direct = Self::sets_overlap_loop_vars(&rhs_vars, cond_vars);
                    let reads_induction = Self::set_contains_loop_var(&rhs_vars, var);
                    let links_cond_via_alias =
                        Self::rhs_links_cond_via_alias(prev_stmts, &rhs_vars, cond_vars);
                    if (left_is_induction && reads_induction)
                        || (left_feeds_condition && (links_cond_direct || links_cond_via_alias))
                    {
                        return Some((expr.clone(), links_cond_direct || links_cond_via_alias));
                    }
                }
                if Self::is_compound_assign_op(*op)
                    && matches!(left.as_ref(), CExpr::Var(name) if Self::loop_var_equiv(name, var))
                {
                    return Some((expr.clone(), false));
                }
                None
            }
            _ => None,
        }
    }

    fn is_removable_trailing_loop_artifact(
        stmt: &CStmt,
        var: &str,
        cond_vars: &HashSet<String>,
    ) -> bool {
        let (name, rhs) = match stmt {
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            }) => {
                let CExpr::Var(name) = left.as_ref() else {
                    return false;
                };
                (name.as_str(), right.as_ref())
            }
            CStmt::Decl {
                name,
                init: Some(rhs),
                ..
            } => (name.as_str(), rhs),
            _ => return false,
        };
        if Self::loop_var_equiv(name, var) || Self::set_contains_loop_var(cond_vars, name) {
            return false;
        }
        Self::is_generated_artifact_name(name) && Self::expr_is_side_effect_free(rhs)
    }

    fn is_generated_side_effect_free_assignment(stmt: &CStmt) -> bool {
        let (name, rhs) = match stmt {
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            }) => {
                let CExpr::Var(name) = left.as_ref() else {
                    return false;
                };
                (name.as_str(), right.as_ref())
            }
            CStmt::Decl {
                name,
                init: Some(rhs),
                ..
            } => (name.as_str(), rhs),
            _ => return false,
        };
        Self::is_generated_artifact_name(name) && Self::expr_is_side_effect_free(rhs)
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
        } = stmt
        else {
            return None;
        };
        if matches!(then_body.as_ref(), CStmt::Break)
            || matches!(then_body.as_ref(), CStmt::Block(v) if v.len() == 1 && matches!(v[0], CStmt::Break))
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
            stmt,
            CStmt::Break | CStmt::Continue | CStmt::Return(_) | CStmt::Goto(_)
        )
    }

    fn stmt_into_vec(stmt: CStmt) -> Vec<CStmt> {
        match stmt {
            CStmt::Block(stmts) => stmts,
            CStmt::Empty => Vec::new(),
            other => vec![other],
        }
    }

    fn stmt_from_vec(stmts: Vec<CStmt>) -> CStmt {
        match stmts.len() {
            0 => CStmt::Empty,
            1 => stmts.into_iter().next().unwrap(),
            _ => CStmt::Block(stmts),
        }
    }

    fn rhs_links_cond_via_alias(
        prev_stmts: &[CStmt],
        rhs_vars: &HashSet<String>,
        cond_vars: &HashSet<String>,
    ) -> bool {
        let mut tracked = rhs_vars.clone();
        for stmt in prev_stmts.iter().rev().take(2) {
            let Some((def, prev_reads)) = Self::stmt_def_and_reads(stmt) else {
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

    fn stmt_def_and_reads(stmt: &CStmt) -> Option<(String, HashSet<String>)> {
        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) = stmt
        else {
            return None;
        };
        let CExpr::Var(def) = left.as_ref() else {
            return None;
        };
        Some((def.clone(), Self::collect_expr_vars(right)))
    }

    fn stmt_assignment_def_reads(stmt: &CStmt) -> Option<(String, HashSet<String>, bool, bool)> {
        match stmt {
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            }) => {
                let CExpr::Var(def) = left.as_ref() else {
                    return None;
                };
                Some((
                    def.clone(),
                    Self::collect_expr_vars(right),
                    Self::is_generated_artifact_name(def),
                    Self::expr_is_side_effect_free(right),
                ))
            }
            CStmt::Decl {
                name,
                init: Some(init),
                ..
            } => Some((
                name.clone(),
                Self::collect_expr_vars(init),
                Self::is_generated_artifact_name(name),
                Self::expr_is_side_effect_free(init),
            )),
            _ => None,
        }
    }

    fn collect_stmt_vars(stmt: &CStmt) -> HashSet<String> {
        let mut vars = HashSet::new();
        Self::collect_stmt_vars_into(stmt, &mut vars);
        vars
    }

    fn collect_stmt_vars_into(stmt: &CStmt, out: &mut HashSet<String>) {
        match stmt {
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
                Self::collect_expr_vars_into(expr, out)
            }
            CStmt::Decl {
                init: Some(init), ..
            } => Self::collect_expr_vars_into(init, out),
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                Self::collect_expr_vars_into(cond, out);
                Self::collect_stmt_vars_into(then_body, out);
                if let Some(else_body) = else_body.as_ref() {
                    Self::collect_stmt_vars_into(else_body, out);
                }
            }
            CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
                Self::collect_expr_vars_into(cond, out);
                Self::collect_stmt_vars_into(body, out);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init.as_ref() {
                    Self::collect_stmt_vars_into(init, out);
                }
                if let Some(cond) = cond.as_ref() {
                    Self::collect_expr_vars_into(cond, out);
                }
                if let Some(update) = update.as_ref() {
                    Self::collect_expr_vars_into(update, out);
                }
                Self::collect_stmt_vars_into(body, out);
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    Self::collect_stmt_vars_into(stmt, out);
                }
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                Self::collect_expr_vars_into(expr, out);
                for case in cases {
                    Self::collect_expr_vars_into(&case.value, out);
                    for stmt in &case.body {
                        Self::collect_stmt_vars_into(stmt, out);
                    }
                }
                if let Some(default) = default.as_ref() {
                    for stmt in default {
                        Self::collect_stmt_vars_into(stmt, out);
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

    fn collect_expr_vars(expr: &CExpr) -> HashSet<String> {
        let mut vars = HashSet::new();
        Self::collect_expr_vars_into(expr, &mut vars);
        vars
    }

    fn normalize_loop_expr_refs(expr: &CExpr) -> &CExpr {
        match expr {
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

    fn normalize_condition_addr_artifacts(expr: CExpr) -> CExpr {
        match expr {
            CExpr::Var(name) if name.starts_with('&') && name.len() > 1 => {
                CExpr::Var(name.trim_start_matches('&').to_string())
            }
            CExpr::Unary { op, operand } => CExpr::Unary {
                op,
                operand: Box::new(Self::normalize_condition_addr_artifacts(*operand)),
            },
            CExpr::Binary { op, left, right } => CExpr::Binary {
                op,
                left: Box::new(Self::normalize_condition_addr_artifacts(*left)),
                right: Box::new(Self::normalize_condition_addr_artifacts(*right)),
            },
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => CExpr::Ternary {
                cond: Box::new(Self::normalize_condition_addr_artifacts(*cond)),
                then_expr: Box::new(Self::normalize_condition_addr_artifacts(*then_expr)),
                else_expr: Box::new(Self::normalize_condition_addr_artifacts(*else_expr)),
            },
            CExpr::Cast { ty, expr } => CExpr::Cast {
                ty,
                expr: Box::new(Self::normalize_condition_addr_artifacts(*expr)),
            },
            CExpr::Call { func, args } => CExpr::Call {
                func: Box::new(Self::normalize_condition_addr_artifacts(*func)),
                args: args
                    .into_iter()
                    .map(Self::normalize_condition_addr_artifacts)
                    .collect(),
            },
            CExpr::Subscript { base, index } => CExpr::Subscript {
                base: Box::new(Self::normalize_condition_addr_artifacts(*base)),
                index: Box::new(Self::normalize_condition_addr_artifacts(*index)),
            },
            CExpr::Member { base, member } => CExpr::Member {
                base: Box::new(Self::normalize_condition_addr_artifacts(*base)),
                member,
            },
            CExpr::PtrMember { base, member } => CExpr::PtrMember {
                base: Box::new(Self::normalize_condition_addr_artifacts(*base)),
                member,
            },
            CExpr::Sizeof(inner) => {
                CExpr::Sizeof(Box::new(Self::normalize_condition_addr_artifacts(*inner)))
            }
            CExpr::AddrOf(inner) => {
                let normalized = Self::normalize_condition_addr_artifacts(*inner);
                match normalized {
                    CExpr::Deref(inner2) => *inner2,
                    CExpr::Var(name) => CExpr::Var(name),
                    other => CExpr::AddrOf(Box::new(other)),
                }
            }
            CExpr::Deref(inner) => {
                let normalized = Self::normalize_condition_addr_artifacts(*inner);
                match normalized {
                    CExpr::AddrOf(inner2) => *inner2,
                    other => CExpr::Deref(Box::new(other)),
                }
            }
            CExpr::Comma(values) => CExpr::Comma(
                values
                    .into_iter()
                    .map(Self::normalize_condition_addr_artifacts)
                    .collect(),
            ),
            CExpr::Paren(inner) => {
                CExpr::Paren(Box::new(Self::normalize_condition_addr_artifacts(*inner)))
            }
            other => other,
        }
    }

    fn collect_expr_vars_into(expr: &CExpr, out: &mut HashSet<String>) {
        match Self::normalize_loop_expr_refs(expr) {
            CExpr::Var(name) => {
                out.insert(name.trim_start_matches('&').to_string());
            }
            CExpr::AddrOf(inner) | CExpr::Deref(inner) => {
                if let CExpr::Var(name) = Self::normalize_loop_expr_refs(inner) {
                    out.insert(name.trim_start_matches('&').to_string());
                }
                Self::collect_expr_vars_into(inner, out);
            }
            CExpr::Unary { operand, .. } => Self::collect_expr_vars_into(operand, out),
            CExpr::Binary { left, right, .. } => {
                Self::collect_expr_vars_into(left, out);
                Self::collect_expr_vars_into(right, out);
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                Self::collect_expr_vars_into(cond, out);
                Self::collect_expr_vars_into(then_expr, out);
                Self::collect_expr_vars_into(else_expr, out);
            }
            CExpr::Cast { expr, .. } | CExpr::Paren(expr) | CExpr::Sizeof(expr) => {
                Self::collect_expr_vars_into(expr, out)
            }
            CExpr::Call { func, args } => {
                Self::collect_expr_vars_into(func, out);
                for arg in args {
                    Self::collect_expr_vars_into(arg, out);
                }
            }
            CExpr::Subscript { base, index } => {
                Self::collect_expr_vars_into(base, out);
                Self::collect_expr_vars_into(index, out);
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                Self::collect_expr_vars_into(base, out);
            }
            CExpr::Comma(values) => {
                for value in values {
                    Self::collect_expr_vars_into(value, out);
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
        match stmt {
            CStmt::Block(mut stmts) if stmts.len() == 1 => Self::flatten(stmts.remove(0)),
            CStmt::Block(stmts) if stmts.is_empty() => CStmt::Empty,
            other => other,
        }
    }

    /// Fix B: Remove trailing `continue` from a loop body (it's implicit).
    /// Also remove trailing `break` inside an if-then at the end of a block
    /// if it's the only exit path.
    fn strip_trailing_continue(stmt: CStmt) -> CStmt {
        match stmt {
            CStmt::Continue => CStmt::Empty,
            CStmt::Block(mut stmts) => {
                // Remove trailing Continue
                while matches!(stmts.last(), Some(CStmt::Continue)) {
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
            CStmt::Break | CStmt::Continue => CStmt::Empty,
            CStmt::Block(mut stmts) => {
                while matches!(stmts.last(), Some(CStmt::Break | CStmt::Continue)) {
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
        let is_infinite = match &cond {
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
        let stmts = match &body {
            CStmt::Block(stmts) => stmts.clone(),
            CStmt::If { .. } => vec![body.clone()],
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
        } = &stmts[0]
        {
            let is_break = matches!(then_body.as_ref(), CStmt::Break)
                || matches!(then_body.as_ref(), CStmt::Block(v) if v.len() == 1 && matches!(v[0], CStmt::Break));
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
    use crate::ast::{BinaryOp, CExpr, CStmt, CType, UnaryOp};
    use crate::fold::FoldingContext;
    use crate::region::Region;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::{BlockTerminator, PhiNode, PredicateId, SSAFunction, SSAOp, SSAVar, SsaArtifact};
    use std::collections::{BTreeMap, BTreeSet, HashMap};

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

    fn v(name: &str) -> CExpr {
        CExpr::Var(name.to_string())
    }

    fn expr_stmt(expr: CExpr) -> CStmt {
        CStmt::Expr(expr)
    }

    fn assign(lhs: &str, rhs: CExpr) -> CStmt {
        expr_stmt(CExpr::assign(v(lhs), rhs))
    }

    #[test]
    fn loop_condition_prefix_preserves_sequential_effects() {
        let load = CExpr::assign(v("byte"), CExpr::Deref(Box::new(v("cursor"))));
        let condition = CExpr::binary(BinaryOp::Ne, v("byte"), CExpr::IntLit(0));

        assert_eq!(
            ControlFlowStructurer::combine_loop_condition_prefix(
                vec![CStmt::Expr(load.clone())],
                condition.clone(),
            ),
            Ok(CExpr::Comma(vec![load, condition]))
        );
    }

    fn test_structured_worker_route(reason: &str) -> r2types::DecompileRouteFacts {
        r2types::DecompileRouteFacts {
            kind: r2types::DecompileRouteKind::StructuredWorker,
            reason: Some(reason.to_string()),
            fallback_comment: None,
            skip_runtime_type_inference: true,
            use_prepared_semantic_view: false,
            proof_coverage: r2sym::ProofCoverage::default(),
            render_permission: r2sym::RenderPermission::summary(
                r2sym::ProofOwner::R2engine,
                reason,
            ),
        }
    }

    fn certified_standard_route_for_test(reason: &str) -> r2types::DecompileRouteFacts {
        r2types::DecompileRouteFacts {
            kind: r2types::DecompileRouteKind::Standard,
            reason: Some(reason.to_string()),
            fallback_comment: None,
            skip_runtime_type_inference: true,
            use_prepared_semantic_view: true,
            proof_coverage: r2sym::ProofCoverage::default(),
            render_permission: r2sym::RenderPermission::certified(
                r2sym::ProofOwner::R2engine,
                reason,
            ),
        }
    }

    fn install_function_facts(ctx: &mut FoldingContext<'_>, facts: r2types::FunctionFacts) {
        ctx.inputs.function_facts = Box::leak(Box::new(facts));
        ctx.inputs.certified_rendering_required = false;
    }

    fn install_semantic_artifact(ctx: &mut FoldingContext<'_>, artifact: r2sym::SemanticArtifact) {
        let mut function_facts = ctx.inputs.function_facts.clone();
        function_facts.set_semantics(Some(artifact));
        install_function_facts(ctx, function_facts);
    }

    fn certified_function_facts(
        control: r2types::FunctionControlFacts,
        render: r2types::FunctionRenderFacts,
    ) -> r2types::FunctionFacts {
        let mut facts = r2types::FunctionFacts::default()
            .with_control(control)
            .with_render(render)
            .with_decompile_route(certified_standard_route_for_test("test certified Standard"));
        add_test_x86_64_signature(&mut facts);
        facts
    }

    fn add_test_x86_64_signature(facts: &mut r2types::FunctionFacts) {
        let signature = r2types::FunctionSignatureSpec {
            ret_type: Some(r2types::CTypeLike::Int {
                bits: 64,
                signedness: r2types::Signedness::Signed,
            }),
            params: vec![r2types::FunctionParamSpec {
                name: "arg1".to_string(),
                ty: Some(r2types::CTypeLike::Int {
                    bits: 64,
                    signedness: r2types::Signedness::Signed,
                }),
            }],
        };
        let certificate = r2types::SignatureCertificate::from_signature(
            &signature,
            [r2types::SignatureCertificateSource::LocalInference],
        )
        .expect("typed test signature");
        let mut types = facts.type_facts().clone();
        types.merged_signature = Some(signature);
        types.signature_certificate = Some(certificate);
        facts.replace_type_facts(types);
    }

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("RDI", 0x10, 8));
        arch.add_register(RegisterDef::new("RBP", 0x20, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch
    }

    fn function_with_single_block(addr: u64) -> SSAFunction {
        let mut block = R2ILBlock::new(addr, 4);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SSAFunction::from_blocks_with_arch(&[block], Some(&test_arch()))
            .expect("ssa function")
            .with_name("vm_summary_demo")
    }

    fn function_with_return_blocks(addrs: &[u64]) -> SSAFunction {
        let blocks = addrs
            .iter()
            .map(|addr| {
                let mut block = R2ILBlock::new(*addr, 4);
                block.push(R2ILOp::Return {
                    target: Varnode::constant(0, 8),
                });
                block
            })
            .collect::<Vec<_>>();
        SSAFunction::from_blocks_with_arch(&blocks, Some(&test_arch()))
            .expect("ssa function")
            .with_name("worker_region_demo")
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

    fn prepared_with_switch_block_and_cases() -> SsaArtifact {
        let mut switch_block = R2ILBlock::new(0x1000, 4);
        switch_block.push(R2ILOp::BranchInd {
            target: Varnode::register(0x10, 8),
        });
        switch_block.set_switch_info(r2il::SwitchInfo {
            switch_addr: 0x1000,
            min_val: 0,
            max_val: 1,
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

        SsaArtifact::for_decompile(&[switch_block, case_zero, case_one], Some(&test_arch()))
            .expect("prepared switch artifact")
            .with_name("certified_switch_structuring")
    }

    fn function_with_conditional_return_blocks(
        cond_block: u64,
        true_target: u64,
        false_target: u64,
    ) -> SSAFunction {
        let mut cond = R2ILBlock::new(cond_block, 4);
        cond.push(R2ILOp::IntEqual {
            dst: Varnode::register(0x80, 1),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(0, 8),
        });
        cond.push(R2ILOp::CBranch {
            target: Varnode::constant(true_target, 8),
            cond: Varnode::register(0x80, 1),
        });

        let mut false_block = R2ILBlock::new(false_target, 4);
        false_block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut true_block = R2ILBlock::new(true_target, 4);
        true_block.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });

        SSAFunction::from_blocks_with_arch(&[cond, false_block, true_block], Some(&test_arch()))
            .expect("ssa function")
            .with_name("worker_structured_demo")
    }

    fn prepared_with_conditional_return_blocks(
        cond_block: u64,
        true_target: u64,
        false_target: u64,
    ) -> SsaArtifact {
        let mut cond = R2ILBlock::new(cond_block, 4);
        cond.push(R2ILOp::IntEqual {
            dst: Varnode::register(0x80, 1),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(0, 8),
        });
        cond.push(R2ILOp::CBranch {
            target: Varnode::constant(true_target, 8),
            cond: Varnode::register(0x80, 1),
        });

        let mut false_block = R2ILBlock::new(false_target, 4);
        false_block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut true_block = R2ILBlock::new(true_target, 4);
        true_block.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });

        SsaArtifact::for_decompile(&[cond, false_block, true_block], Some(&test_arch()))
            .expect("prepared ssa artifact")
            .with_name("certified_branch_structuring")
    }

    fn prepared_with_guarded_while_loop() -> SsaArtifact {
        let mut header = R2ILBlock::new(0x1000, 4);
        header.push(R2ILOp::IntEqual {
            dst: Varnode::register(0x80, 1),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(0, 8),
        });
        header.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1008, 8),
            cond: Varnode::register(0x80, 1),
        });

        let mut body = R2ILBlock::new(0x1004, 4);
        body.push(R2ILOp::Branch {
            target: Varnode::constant(0x1000, 8),
        });

        let mut exit = R2ILBlock::new(0x1008, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        SsaArtifact::for_decompile(&[header, body, exit], Some(&test_arch()))
            .expect("prepared while artifact")
            .with_name("certified_loop_structuring")
    }

    fn render_facts_for_prepared(prepared: &SsaArtifact) -> r2types::FunctionRenderFacts {
        let mut facts = r2types::FunctionFacts::default()
            .with_render(r2types::FunctionRenderFacts::from_prepared(prepared));
        facts.populate_certified_parameter_exprs(
            prepared,
            &r2types::ParamSlotResolver::from_arch_name(Some("x86-64")),
        );
        facts.render_facts().clone()
    }

    fn control_facts_for_guarded_while_loop(
        prepared: &SsaArtifact,
        include_loop: bool,
    ) -> r2types::FunctionControlFacts {
        let predicate = prepared
            .predicates()
            .predicates
            .values()
            .find(|predicate| predicate.block_addr == 0x1000)
            .expect("loop header predicate");
        let mut facts = r2types::FunctionControlFacts::default();
        facts.branch_predicates.insert(
            0x1000,
            r2types::BranchPredicateFact {
                id: predicate.id,
                block_addr: predicate.block_addr,
                condition: predicate.condition,
                comparison: predicate.comparison.as_ref().map(|comparison| {
                    r2types::PredicateComparisonFact {
                        kind: comparison.kind,
                        lhs: comparison.lhs,
                        rhs: comparison.rhs,
                    }
                }),
                evaluated_comparison: predicate.evaluated_comparison.as_ref().map(|comparison| {
                    r2types::PredicateComparisonFact {
                        kind: comparison.kind,
                        lhs: comparison.lhs,
                        rhs: comparison.rhs,
                    }
                }),
                render_comparison: predicate.comparison.as_ref().map(|comparison| {
                    r2types::PredicateComparisonFact {
                        kind: comparison.kind,
                        lhs: comparison.lhs,
                        rhs: comparison.rhs,
                    }
                }),
                true_target: predicate.true_target,
                false_target: predicate.false_target,
            },
        );
        if include_loop {
            facts.loops.insert(
                r2ssa::LoopId(0),
                r2types::LoopStructureFact {
                    loop_id: r2ssa::LoopId(0),
                    proof_node: "FunctionFacts.loop:LoopId(0)".to_string(),
                    header: 0x1000,
                    condition: Some(predicate.id),
                    condition_value: Some(predicate.condition),
                    body: vec![0x1000, 0x1004],
                    latches: vec![0x1004],
                    exits: vec![0x1008],
                },
            );
        }
        facts.control_domains = prepared.control_domains().clone();
        facts
    }

    fn control_facts_for_switch(
        prepared: &SsaArtifact,
        include_cases: bool,
    ) -> r2types::FunctionControlFacts {
        let selector = prepared
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.eq_ignore_ascii_case("rdi") && value.var.version == 0)
            .map(|value| value.id)
            .expect("rdi selector value");
        r2types::FunctionControlFacts {
            switches: BTreeMap::from([(
                0x1000,
                r2types::SwitchSelectorFact {
                    proof_node: r2ssa::ProofNodeId::switch_certificate(0x1000).to_string(),
                    block_addr: 0x1000,
                    selector: Some(selector),
                    cases: if include_cases {
                        vec![(0, 0x1010), (1, 0x1020)]
                    } else {
                        Vec::new()
                    },
                    default: None,
                },
            )]),
            control_domains: prepared.control_domains().clone(),
            ..r2types::FunctionControlFacts::default()
        }
    }

    fn function_with_multi_block_true_arm(
        cond_block: u64,
        true_entry: u64,
        true_tail: u64,
        false_target: u64,
    ) -> SSAFunction {
        let mut cond = R2ILBlock::new(cond_block, 4);
        cond.push(R2ILOp::IntEqual {
            dst: Varnode::register(0x80, 1),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(0, 8),
        });
        cond.push(R2ILOp::CBranch {
            target: Varnode::constant(true_entry, 8),
            cond: Varnode::register(0x80, 1),
        });

        let mut false_block = R2ILBlock::new(false_target, 4);
        false_block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut true_head = R2ILBlock::new(true_entry, 4);
        true_head.push(R2ILOp::Copy {
            dst: Varnode::register(0x00, 8),
            src: Varnode::constant(1, 8),
        });
        true_head.push(R2ILOp::Branch {
            target: Varnode::constant(true_tail, 8),
        });

        let mut true_tail_block = R2ILBlock::new(true_tail, 4);
        true_tail_block.push(R2ILOp::Return {
            target: Varnode::register(0x00, 8),
        });

        SSAFunction::from_blocks_with_arch(
            &[cond, false_block, true_head, true_tail_block],
            Some(&test_arch()),
        )
        .expect("ssa function")
        .with_name("worker_multiblock_demo")
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

    fn stmt_contains_if(stmt: &CStmt) -> bool {
        match stmt {
            CStmt::If { .. } => true,
            CStmt::Block(stmts) => stmts.iter().any(stmt_contains_if),
            CStmt::While { body, .. } | CStmt::For { body, .. } | CStmt::DoWhile { body, .. } => {
                stmt_contains_if(body)
            }
            CStmt::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|case| case.body.iter().any(stmt_contains_if))
                    || default
                        .as_ref()
                        .is_some_and(|body| body.iter().any(stmt_contains_if))
            }
            _ => false,
        }
    }

    fn stmt_contains_comment(stmt: &CStmt, needle: &str) -> bool {
        match stmt {
            CStmt::Comment(text) => text.contains(needle),
            CStmt::Block(stmts) => stmts.iter().any(|stmt| stmt_contains_comment(stmt, needle)),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                stmt_contains_comment(then_body, needle)
                    || else_body
                        .as_deref()
                        .is_some_and(|stmt| stmt_contains_comment(stmt, needle))
            }
            CStmt::While { body, .. } | CStmt::For { body, .. } | CStmt::DoWhile { body, .. } => {
                stmt_contains_comment(body, needle)
            }
            CStmt::Switch { cases, default, .. } => {
                cases.iter().any(|case| {
                    case.body
                        .iter()
                        .any(|stmt| stmt_contains_comment(stmt, needle))
                }) || default
                    .as_ref()
                    .is_some_and(|body| body.iter().any(|stmt| stmt_contains_comment(stmt, needle)))
            }
            _ => false,
        }
    }

    fn stmt_contains_unproved_control_transfer(stmt: &CStmt) -> bool {
        match stmt {
            CStmt::Break | CStmt::Continue | CStmt::Goto(_) => true,
            CStmt::Block(stmts) => stmts.iter().any(stmt_contains_unproved_control_transfer),
            CStmt::If {
                then_body,
                else_body,
                ..
            } => {
                stmt_contains_unproved_control_transfer(then_body)
                    || else_body
                        .as_deref()
                        .is_some_and(stmt_contains_unproved_control_transfer)
            }
            CStmt::While { body, .. } | CStmt::DoWhile { body, .. } | CStmt::For { body, .. } => {
                stmt_contains_unproved_control_transfer(body)
            }
            CStmt::Switch { cases, default, .. } => {
                cases.iter().any(|case| {
                    case.body
                        .iter()
                        .any(stmt_contains_unproved_control_transfer)
                }) || default
                    .as_ref()
                    .is_some_and(|body| body.iter().any(stmt_contains_unproved_control_transfer))
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

        let rendered = structurer.structure_switch_region(0x1000, &cases, None, None);
        let values = first_switch_case_values(&rendered).expect("rendered switch");

        assert_eq!(
            values,
            vec![0, 1, 2],
            "switch rendering must not bias canonical case values from nearby arithmetic"
        );
    }

    #[test]
    fn certified_branch_structuring_requires_function_facts_predicate() {
        let prepared = prepared_with_conditional_return_blocks(0x1000, 0x1010, 0x1004);
        let mut function_facts = r2types::FunctionFacts::default();
        function_facts.attach_prepared_decompile_evidence(&prepared);

        let mut certified_ctx = FoldingContext::new(64);
        certified_ctx.inputs.prepared_ssa = Some(&prepared);
        function_facts.set_render(render_facts_for_prepared(&prepared));
        add_test_x86_64_signature(&mut function_facts);
        install_function_facts(
            &mut certified_ctx,
            function_facts
                .with_decompile_route(certified_standard_route_for_test("test certified branch")),
        );
        let mut certified_structurer =
            ControlFlowStructurer::new(prepared.function(), &certified_ctx);
        let certified_stmt = certified_structurer.structure();
        assert!(
            stmt_contains_if(&certified_stmt),
            "FunctionFacts branch predicate should authorize structured if output, got {certified_stmt:?}"
        );

        let mut missing_control_ctx = FoldingContext::new(64);
        missing_control_ctx.inputs.prepared_ssa = Some(&prepared);
        install_function_facts(
            &mut missing_control_ctx,
            r2types::FunctionFacts::default()
                .with_render(render_facts_for_prepared(&prepared))
                .with_decompile_route(certified_standard_route_for_test(
                    "test certified missing branch proof",
                )),
        );
        let mut missing_control_structurer =
            ControlFlowStructurer::new(prepared.function(), &missing_control_ctx);
        let missing_control_stmt = missing_control_structurer.structure();

        assert!(
            !stmt_contains_if(&missing_control_stmt),
            "certified branch structuring must not use local CBranch extraction without FunctionFacts control proof: {missing_control_stmt:?}"
        );
        assert!(
            stmt_contains_comment(&missing_control_stmt, "unresolved branch condition"),
            "missing FunctionFacts control proof should residualize the branch, got {missing_control_stmt:?}"
        );
    }

    #[test]
    fn certified_loop_structuring_requires_function_facts_loop_structure() {
        let prepared = prepared_with_guarded_while_loop();
        let region = Region::WhileLoop {
            header: 0x1000,
            body: Box::new(Region::Block(0x1004)),
        };

        let certified_control = control_facts_for_guarded_while_loop(&prepared, true);
        let mut certified_ctx = FoldingContext::new(64);
        certified_ctx.inputs.prepared_ssa = Some(&prepared);
        install_function_facts(
            &mut certified_ctx,
            certified_function_facts(certified_control, render_facts_for_prepared(&prepared)),
        );
        let mut certified_structurer =
            ControlFlowStructurer::new(prepared.function(), &certified_ctx);
        let certified_stmt = certified_structurer.structure_region(&region);
        assert!(
            stmt_contains_loop(&certified_stmt),
            "FunctionFacts loop structure should authorize while output, got {certified_stmt:?}"
        );
        let CStmt::While { cond, .. } = &certified_stmt else {
            panic!("expected direct certified while statement, got {certified_stmt:?}");
        };
        assert!(
            matches!(
                cond,
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    ..
                }
            ),
            "a true edge that exits the loop must invert the branch predicate, got {cond:?}"
        );

        let missing_loop_control = control_facts_for_guarded_while_loop(&prepared, false);
        let mut missing_loop_ctx = FoldingContext::new(64);
        missing_loop_ctx.inputs.prepared_ssa = Some(&prepared);
        install_function_facts(
            &mut missing_loop_ctx,
            certified_function_facts(missing_loop_control, render_facts_for_prepared(&prepared)),
        );
        let mut missing_loop_structurer =
            ControlFlowStructurer::new(prepared.function(), &missing_loop_ctx);
        let missing_loop_stmt = missing_loop_structurer.structure_region(&region);
        assert!(
            !stmt_contains_loop(&missing_loop_stmt),
            "certified loop structuring must not render while from branch proof alone: {missing_loop_stmt:?}"
        );
        assert!(
            stmt_contains_comment(&missing_loop_stmt, "uncertified loop structure"),
            "missing FunctionFacts loop proof should residualize the loop, got {missing_loop_stmt:?}"
        );
    }

    #[test]
    fn certified_switch_structuring_requires_function_facts_case_targets() {
        let prepared = prepared_with_switch_block_and_cases();
        let cases = vec![
            (Some(0), Box::new(Region::Block(0x1010))),
            (Some(1), Box::new(Region::Block(0x1020))),
        ];

        let certified_control = control_facts_for_switch(&prepared, true);
        let mut certified_ctx = FoldingContext::new(64);
        certified_ctx.inputs.prepared_ssa = Some(&prepared);
        install_function_facts(
            &mut certified_ctx,
            certified_function_facts(certified_control, render_facts_for_prepared(&prepared)),
        );
        let mut certified_structurer =
            ControlFlowStructurer::new(prepared.function(), &certified_ctx);
        let certified_stmt =
            certified_structurer.structure_switch_region(0x1000, &cases, None, None);
        assert!(
            first_switch_case_values(&certified_stmt).is_some(),
            "FunctionFacts switch selector/cases should authorize switch output, got {certified_stmt:?}"
        );
        assert!(
            !stmt_contains_unproved_control_transfer(&certified_stmt),
            "certified switch structuring must not synthesize case exits without exact transfer facts: {certified_stmt:?}"
        );

        let selector_only_control = control_facts_for_switch(&prepared, false);
        let mut selector_only_ctx = FoldingContext::new(64);
        selector_only_ctx.inputs.prepared_ssa = Some(&prepared);
        install_function_facts(
            &mut selector_only_ctx,
            certified_function_facts(selector_only_control, render_facts_for_prepared(&prepared)),
        );
        let mut selector_only_structurer =
            ControlFlowStructurer::new(prepared.function(), &selector_only_ctx);
        let selector_only_stmt =
            selector_only_structurer.structure_switch_region(0x1000, &cases, None, None);
        assert!(
            first_switch_case_values(&selector_only_stmt).is_none(),
            "certified switch structuring must not render switch cases from selector proof alone: {selector_only_stmt:?}"
        );
        assert!(
            stmt_contains_comment(&selector_only_stmt, "uncertified switch structure"),
            "missing FunctionFacts switch case proof should residualize the switch, got {selector_only_stmt:?}"
        );
    }

    #[test]
    fn cleanup_rewrites_pure_if_else_returns_to_ternary_return() {
        let input = CStmt::If {
            cond: CExpr::binary(BinaryOp::Eq, v("b"), CExpr::IntLit(0)),
            then_body: Box::new(CStmt::Return(Some(CExpr::IntLit(-1)))),
            else_body: Some(Box::new(CStmt::Return(Some(CExpr::binary(
                BinaryOp::Div,
                v("a"),
                v("b"),
            ))))),
        };

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::Return(Some(CExpr::Ternary {
                cond: Box::new(CExpr::binary(BinaryOp::Eq, v("b"), CExpr::IntLit(0))),
                then_expr: Box::new(CExpr::IntLit(-1)),
                else_expr: Box::new(CExpr::binary(BinaryOp::Div, v("a"), v("b"))),
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
    fn merge_predecessor_accepts_exact_materialized_phi_edge_copies() {
        let func = function_with_materialized_phi_branch_to_merge();
        let ctx = FoldingContext::new(64);
        let structurer = ControlFlowStructurer::new(&func, &ctx);

        assert_eq!(
            structurer.unique_region_predecessor_to_merge(&Region::Block(0x1000), 0x1020),
            Some(0x1010)
        );
    }

    #[test]
    fn transparent_transfer_path_accepts_exact_materialized_phi_edge_copy() {
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
            });
        let ctx = FoldingContext::new(64);
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        structurer.structured_region_blocks.insert(0x1010);

        assert_eq!(
            structurer.transparent_transfer_path(0x1000),
            Ok(vec![0x1000, 0x1010])
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

        let stmt = structurer.structure_region(&region);
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
        let body = CStmt::Block(vec![assign("hash", v("next_hash")), CStmt::Break]);

        let stripped = ControlFlowStructurer::strip_trailing_latch_marker(body);

        assert_eq!(stripped, assign("hash", v("next_hash")));
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

        let stmt = structurer.structure();

        assert!(
            stmt_contains_loop(&stmt),
            "guarded latch-form loop must remain structured, got {stmt:?}; reason={:?}",
            structurer.safety_reason()
        );
    }

    #[test]
    fn rewrites_canonical_while_to_for() {
        let input = CStmt::Block(vec![
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v("i"), CExpr::IntLit(10)),
                CStmt::Block(vec![
                    assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("i"))),
                    assign("i", CExpr::binary(BinaryOp::Add, v("i"), CExpr::IntLit(1))),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
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
        let input = CStmt::Block(vec![
            CStmt::Block(vec![
                assign("count", CExpr::IntLit(0)),
                assign("i", CExpr::IntLit(0)),
            ]),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v("i"), v("n")),
                CStmt::Block(vec![
                    assign(
                        "c",
                        CExpr::Subscript {
                            base: Box::new(v("buf")),
                            index: Box::new(v("i")),
                        },
                    ),
                    CStmt::if_stmt(
                        CExpr::binary(BinaryOp::Ne, v("c"), v("a")),
                        CStmt::Block(vec![
                            CStmt::if_stmt(
                                CExpr::binary(BinaryOp::Eq, v("c"), v("b")),
                                assign(
                                    "count",
                                    CExpr::binary(BinaryOp::Add, v("count"), CExpr::IntLit(1)),
                                ),
                                None,
                            ),
                            assign("i", CExpr::binary(BinaryOp::Add, v("i"), CExpr::IntLit(1))),
                            CStmt::Continue,
                        ]),
                        None,
                    ),
                    assign(
                        "count",
                        CExpr::binary(BinaryOp::Add, v("count"), CExpr::IntLit(1)),
                    ),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
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
            &CExpr::binary(BinaryOp::AddAssign, v("i"), CExpr::IntLit(1))
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
                    CExpr::binary(BinaryOp::Eq, v("c"), v("a")),
                    CExpr::binary(BinaryOp::Eq, v("c"), v("b"))
                ),
                CStmt::Expr(CExpr::binary(
                    BinaryOp::AddAssign,
                    v("count"),
                    CExpr::IntLit(1),
                )),
                None
            )),
            "fallthrough suffix with duplicate effect should become a single OR guard"
        );
    }

    #[test]
    fn rewrites_nested_else_duplicate_effect_to_or_condition() {
        let increment = expr_stmt(CExpr::Unary {
            op: UnaryOp::PostInc,
            operand: Box::new(v("count")),
        });
        let input = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Ne, v("c"), v("a")),
            CStmt::if_stmt(
                CExpr::binary(BinaryOp::Eq, v("c"), v("b")),
                increment.clone(),
                None,
            ),
            Some(increment.clone()),
        );

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(
                CExpr::binary(
                    BinaryOp::Or,
                    CExpr::binary(BinaryOp::Eq, v("c"), v("a")),
                    CExpr::binary(BinaryOp::Eq, v("c"), v("b"))
                ),
                increment,
                None
            )
        );
    }

    #[test]
    fn rewrites_continue_tail_with_common_suffix_before_shared_latch() {
        let hash_xor = assign("hash", CExpr::binary(BinaryOp::BitXor, v("c"), v("hash")));
        let hash_mul = assign(
            "hash",
            CExpr::binary(BinaryOp::Mul, v("hash"), CExpr::UIntLit(0x100000001b3)),
        );
        let i_update = assign("i", CExpr::binary(BinaryOp::Add, v("i"), CExpr::IntLit(1)));
        let lowercase_update = CStmt::Expr(CExpr::binary(
            BinaryOp::AddAssign,
            v("c"),
            CExpr::IntLit(32),
        ));

        let input = CStmt::Block(vec![
            assign("hash", CExpr::UIntLit(0x14650fb0739d0383)),
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v("i"), v("n")),
                CStmt::Block(vec![
                    assign(
                        "c",
                        CExpr::Subscript {
                            base: Box::new(v("buf")),
                            index: Box::new(v("i")),
                        },
                    ),
                    CStmt::if_stmt(
                        CExpr::binary(BinaryOp::Gt, v("c"), CExpr::IntLit(64)),
                        CStmt::Block(vec![
                            CStmt::if_stmt(
                                CExpr::binary(BinaryOp::Le, v("c"), CExpr::IntLit(90)),
                                lowercase_update.clone(),
                                None,
                            ),
                            hash_xor.clone(),
                            hash_mul.clone(),
                            i_update.clone(),
                            assign("value_1", v("c")),
                            CStmt::Continue,
                        ]),
                        None,
                    ),
                    hash_xor.clone(),
                    hash_mul.clone(),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
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
            &CExpr::binary(BinaryOp::AddAssign, v("i"), CExpr::IntLit(1))
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
                    CExpr::binary(BinaryOp::Gt, v("c"), CExpr::IntLit(64)),
                    CExpr::binary(BinaryOp::Le, v("c"), CExpr::IntLit(90)),
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
                v("hash"),
                v("c")
            )))
        );
        assert_eq!(
            body_stmts.get(3),
            Some(&CStmt::Expr(CExpr::binary(
                BinaryOp::MulAssign,
                v("hash"),
                CExpr::UIntLit(0x100000001b3)
            )))
        );
    }

    #[test]
    fn removes_duplicate_body_update_owned_by_for_latch() {
        let i_update_expr = CExpr::binary(
            BinaryOp::Assign,
            v("i"),
            CExpr::binary(BinaryOp::Add, v("i"), CExpr::IntLit(1)),
        );
        let hash_update = assign("hash", CExpr::binary(BinaryOp::BitXor, v("c"), v("hash")));
        let input = CStmt::For {
            init: Some(Box::new(assign("i", CExpr::IntLit(0)))),
            cond: Some(CExpr::binary(BinaryOp::Lt, v("i"), v("n"))),
            update: Some(i_update_expr.clone()),
            body: Box::new(CStmt::Block(vec![
                hash_update.clone(),
                CStmt::Expr(i_update_expr.clone()),
            ])),
        };

        let cleaned = ControlFlowStructurer::cleanup(input);
        let CStmt::For { body, .. } = cleaned else {
            panic!("Expected for-loop, got {cleaned:?}");
        };
        assert_eq!(
            body.as_ref(),
            &CStmt::Expr(CExpr::binary(BinaryOp::BitXorAssign, v("hash"), v("c"))),
            "for latch update should own the duplicated trailing body update"
        );
    }

    #[test]
    fn rewrites_side_effect_free_assignments_to_compound_assignments() {
        let input = CStmt::Block(vec![
            assign("hash", CExpr::binary(BinaryOp::BitXor, v("c"), v("hash"))),
            assign(
                "hash",
                CExpr::binary(BinaryOp::Mul, v("hash"), CExpr::UIntLit(0x100000001b3)),
            ),
            assign(
                "hash",
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Call {
                        func: Box::new(v("next")),
                        args: Vec::new(),
                    },
                    v("hash"),
                ),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected block, got {cleaned:?}");
        };
        assert_eq!(
            stmts[0],
            CStmt::Expr(CExpr::binary(BinaryOp::BitXorAssign, v("hash"), v("c")))
        );
        assert_eq!(
            stmts[1],
            CStmt::Expr(CExpr::binary(
                BinaryOp::MulAssign,
                v("hash"),
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
        let input = CStmt::Switch {
            expr: v("op"),
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

        let cleaned = ControlFlowStructurer::cleanup(input);
        let CStmt::Switch { cases, default, .. } = cleaned else {
            panic!("Expected switch, got {cleaned:?}");
        };
        assert_eq!(cases[0].body, vec![CStmt::Return(Some(CExpr::IntLit(1)))]);
        assert_eq!(default, Some(vec![CStmt::Return(Some(CExpr::IntLit(3)))]));
    }

    #[test]
    fn rewrites_guard_break_while1_to_for() {
        let input = CStmt::Block(vec![
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::IntLit(1),
                CStmt::Block(vec![
                    CStmt::if_stmt(
                        CExpr::binary(BinaryOp::Ge, v("i"), v("n")),
                        CStmt::Break,
                        None,
                    ),
                    assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("i"))),
                    expr_stmt(CExpr::Unary {
                        op: UnaryOp::PostInc,
                        operand: Box::new(v("i")),
                    }),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
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
        let input = CStmt::Block(vec![
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v("i"), CExpr::IntLit(10)),
                CStmt::Block(vec![assign(
                    "sum",
                    CExpr::binary(BinaryOp::Add, v("sum"), CExpr::IntLit(1)),
                )]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
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
        let input = CStmt::Block(vec![
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v("j"), CExpr::IntLit(10)),
                CStmt::Block(vec![assign(
                    "i",
                    CExpr::binary(BinaryOp::Add, v("i"), CExpr::IntLit(1)),
                )]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
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
        let updates = vec![
            CExpr::binary(
                BinaryOp::Assign,
                v("i"),
                CExpr::binary(BinaryOp::Add, v("i"), CExpr::IntLit(2)),
            ),
            CExpr::binary(BinaryOp::AddAssign, v("i"), CExpr::IntLit(2)),
            CExpr::binary(
                BinaryOp::Assign,
                v("i"),
                CExpr::call(v("next_i"), vec![v("i"), v("x")]),
            ),
        ];

        for update_expr in updates {
            let input = CStmt::Block(vec![
                assign("i", CExpr::IntLit(0)),
                CStmt::while_loop(
                    CExpr::binary(BinaryOp::Lt, v("i"), v("n")),
                    CStmt::Block(vec![
                        assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("i"))),
                        expr_stmt(update_expr.clone()),
                    ]),
                ),
            ]);

            let cleaned = ControlFlowStructurer::cleanup(input);
            let CStmt::For {
                update: Some(update),
                ..
            } = cleaned
            else {
                panic!("Expected loop rewrite for accepted self-assign update form");
            };
            assert!(
                ControlFlowStructurer::expr_matches_for_update(&update, &update_expr),
                "Expected canonical loop update {update:?} to match source update {update_expr:?}"
            );
        }
    }

    #[test]
    fn rewrites_for_loop_past_generated_trailing_value_carrier() {
        let input = CStmt::Block(vec![
            CStmt::Block(vec![
                assign("sum", CExpr::IntLit(0)),
                assign("i", CExpr::IntLit(0)),
            ]),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v("i"), v("len")),
                CStmt::Block(vec![
                    CStmt::Expr(CExpr::binary(
                        BinaryOp::AddAssign,
                        v("sum"),
                        CExpr::Subscript {
                            base: Box::new(v("arr")),
                            index: Box::new(v("i")),
                        },
                    )),
                    CStmt::Expr(CExpr::Unary {
                        op: UnaryOp::PostInc,
                        operand: Box::new(v("i")),
                    }),
                    CStmt::Decl {
                        name: "tmp:11f00_4".to_string(),
                        ty: CType::i32(),
                        init: Some(CExpr::Deref(Box::new(CExpr::binary(
                            BinaryOp::Add,
                            v("arr"),
                            CExpr::binary(BinaryOp::Mul, v("i"), CExpr::IntLit(4)),
                        )))),
                    },
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
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
        let input = CStmt::if_stmt(
            v("a"),
            CStmt::if_stmt(v("b"), CStmt::ret(Some(CExpr::IntLit(1))), None),
            None,
        );

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(
                CExpr::binary(BinaryOp::And, v("a"), v("b")),
                CStmt::ret(Some(CExpr::IntLit(1))),
                None
            )
        );
    }

    #[test]
    fn rewrites_if_else_if_same_body_to_short_circuit_or() {
        let body = assign("x", CExpr::IntLit(1));
        let input = CStmt::if_stmt(
            v("a"),
            body.clone(),
            Some(CStmt::if_stmt(v("b"), body.clone(), None)),
        );

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(CExpr::binary(BinaryOp::Or, v("a"), v("b")), body, None)
        );
    }

    #[test]
    fn rewrites_shared_else_nested_if_to_short_circuit_and() {
        let then_stmt = assign("x", CExpr::IntLit(1));
        let else_stmt = assign("x", CExpr::IntLit(2));
        let input = CStmt::if_stmt(
            v("a"),
            CStmt::if_stmt(v("b"), then_stmt.clone(), Some(else_stmt.clone())),
            Some(else_stmt.clone()),
        );

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(
                CExpr::binary(BinaryOp::And, v("a"), v("b")),
                then_stmt,
                Some(else_stmt)
            )
        );
    }

    #[test]
    fn negates_less_equal_with_canonical_less_than_orientation() {
        assert_eq!(
            ControlFlowStructurer::negate_condition(CExpr::binary(
                BinaryOp::Le,
                v("limit"),
                v("index"),
            )),
            CExpr::binary(BinaryOp::Lt, v("index"), v("limit"))
        );
    }

    #[test]
    fn inverts_if_else_terminator_and_flattens_then_block() {
        let input = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Lt, v("x"), v("limit")),
            CStmt::Block(vec![
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v("sum"), v("x"))),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v("x"), CExpr::IntLit(1))),
            ]),
            Some(CStmt::ret(Some(CExpr::IntLit(0)))),
        );

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::if_stmt(
                    CExpr::binary(BinaryOp::Ge, v("x"), v("limit")),
                    CStmt::ret(Some(CExpr::IntLit(0))),
                    None
                ),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v("sum"), v("x"))),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v("x"), CExpr::IntLit(1),)),
            ])
        );
    }

    #[test]
    fn inverts_if_then_terminator_and_flattens_else_block() {
        let input = CStmt::if_stmt(
            v("is_error"),
            CStmt::ret(Some(CExpr::IntLit(-1))),
            Some(CStmt::Block(vec![
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v("sum"), v("x"))),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v("x"), CExpr::IntLit(1))),
            ])),
        );

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::if_stmt(v("is_error"), CStmt::ret(Some(CExpr::IntLit(-1))), None),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v("sum"), v("x"))),
                CStmt::Expr(CExpr::binary(BinaryOp::AddAssign, v("x"), CExpr::IntLit(1),)),
            ])
        );
    }

    #[test]
    fn rewrites_trailing_return_guard_and_flattens_then_block() {
        let input = CStmt::Block(vec![
            CStmt::if_stmt(
                v("ready"),
                CStmt::Block(vec![
                    assign("x", CExpr::IntLit(1)),
                    assign("y", CExpr::IntLit(2)),
                ]),
                None,
            ),
            CStmt::ret(Some(CExpr::IntLit(0))),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::if_stmt(
                    CExpr::unary(UnaryOp::Not, v("ready")),
                    CStmt::ret(Some(CExpr::IntLit(0))),
                    None
                ),
                assign("x", CExpr::IntLit(1)),
                assign("y", CExpr::IntLit(2)),
                CStmt::ret(Some(CExpr::IntLit(0))),
            ])
        );
    }

    #[test]
    fn does_not_rewrite_trailing_guard_when_following_stmt_is_not_terminator() {
        let input = CStmt::Block(vec![
            CStmt::if_stmt(v("ready"), assign("x", CExpr::IntLit(1)), None),
            assign("y", CExpr::IntLit(2)),
        ]);
        let cleaned = ControlFlowStructurer::cleanup(input.clone());
        assert_eq!(cleaned, input);
    }

    #[test]
    fn does_not_invert_if_when_both_branches_are_terminators() {
        let input = CStmt::if_stmt(
            v("a"),
            CStmt::ret(Some(CExpr::IntLit(1))),
            Some(CStmt::ret(Some(CExpr::IntLit(0)))),
        );
        let cleaned = ControlFlowStructurer::cleanup(input.clone());
        assert_eq!(cleaned, input);
    }

    #[test]
    fn does_not_invert_if_when_else_is_not_terminator() {
        let input = CStmt::if_stmt(
            v("a"),
            assign("x", CExpr::IntLit(1)),
            Some(assign("x", v("b"))),
        );
        let cleaned = ControlFlowStructurer::cleanup(input.clone());
        assert_eq!(cleaned, input);
    }

    #[test]
    fn inverts_if_when_else_is_single_terminator() {
        let input = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Lt, v("x"), v("limit")),
            assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("x"))),
            Some(CStmt::ret(Some(CExpr::IntLit(0)))),
        );

        let cleaned = ControlFlowStructurer::cleanup(input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected condition inversion to emit block sequence");
        };
        assert_eq!(
            stmts[0],
            CStmt::if_stmt(
                CExpr::binary(BinaryOp::Ge, v("x"), v("limit")),
                CStmt::ret(Some(CExpr::IntLit(0))),
                None
            )
        );
    }

    #[test]
    fn removes_empty_else_branch() {
        let input = CStmt::if_stmt(v("a"), assign("x", CExpr::IntLit(1)), Some(CStmt::Empty));
        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::if_stmt(v("a"), assign("x", CExpr::IntLit(1)), None)
        );
    }

    #[test]
    fn removes_empty_if_without_else() {
        let input = CStmt::if_stmt(v("a"), CStmt::Empty, None);
        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(cleaned, CStmt::Empty);
    }

    #[test]
    fn constant_true_if_collapses_to_then_body() {
        let input = CStmt::if_stmt(CExpr::IntLit(1), assign("x", CExpr::IntLit(7)), None);
        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(cleaned, assign("x", CExpr::IntLit(7)));
    }

    #[test]
    fn constant_false_if_collapses_to_else_body() {
        let input = CStmt::if_stmt(
            CExpr::IntLit(0),
            assign("x", CExpr::IntLit(7)),
            Some(assign("x", CExpr::IntLit(9))),
        );
        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(cleaned, assign("x", CExpr::IntLit(9)));
    }

    #[test]
    fn guarded_switch_with_trailing_return_becomes_switch_default() {
        let input = CStmt::Block(vec![CStmt::if_stmt(
            v("guard"),
            CStmt::Block(vec![
                expr_stmt(CExpr::call(
                    v("sym.imp.printf"),
                    vec![CExpr::StringLit("bad".into())],
                )),
                CStmt::ret(Some(CExpr::IntLit(1))),
            ]),
            Some(CStmt::Block(vec![
                CStmt::Switch {
                    expr: v("selector"),
                    cases: vec![crate::ast::SwitchCase {
                        value: CExpr::IntLit(1),
                        body: vec![assign("x", CExpr::IntLit(1)), CStmt::Break],
                    }],
                    default: None,
                },
                CStmt::ret(Some(CExpr::IntLit(0))),
            ])),
        )]);

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::Switch {
                    expr: v("selector"),
                    cases: vec![crate::ast::SwitchCase {
                        value: CExpr::IntLit(1),
                        body: vec![assign("x", CExpr::IntLit(1)), CStmt::Break],
                    }],
                    default: Some(vec![CStmt::Block(vec![
                        expr_stmt(CExpr::call(
                            v("sym.imp.printf"),
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
        let cond = CExpr::binary(
            BinaryOp::Eq,
            CExpr::binary(BinaryOp::BitAnd, v("i"), CExpr::IntLit(7)),
            CExpr::IntLit(0),
        );

        let selector = ControlFlowStructurer::selector_expr_from_condition(&cond)
            .expect("selector expression");
        assert_eq!(
            selector,
            CExpr::binary(BinaryOp::BitAnd, v("i"), CExpr::IntLit(7))
        );
    }

    #[test]
    fn rewrites_while_to_for_when_condition_uses_addrof_induction_var() {
        let input = CStmt::Block(vec![
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, CExpr::AddrOf(Box::new(v("i"))), v("n")),
                CStmt::Block(vec![
                    assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("i"))),
                    assign("i", CExpr::binary(BinaryOp::Add, v("i"), CExpr::IntLit(1))),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert!(
            matches!(cleaned, CStmt::For { .. }),
            "Address-wrapped induction variable should still allow for-loop rewrite"
        );
    }

    #[test]
    fn normalizes_addrof_var_artifact_in_while_condition_without_rewrite() {
        let input = CStmt::Block(vec![
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, CExpr::AddrOf(Box::new(v("local"))), v("n")),
                CStmt::Block(vec![assign(
                    "sum",
                    CExpr::binary(BinaryOp::Add, v("sum"), CExpr::IntLit(1)),
                )]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
        let CStmt::Block(stmts) = cleaned else {
            panic!("Expected unmatched loop to remain a block");
        };
        let Some(CStmt::While { cond, .. }) = stmts.get(1) else {
            panic!("Expected second statement to remain a while-loop");
        };
        match cond {
            CExpr::Binary { left, .. } => {
                assert!(
                    matches!(left.as_ref(), CExpr::Var(name) if name == "local"),
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
        let input = CStmt::Block(vec![
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v("i"), v("n")),
                CStmt::Block(vec![
                    assign("tmp1", v("i")),
                    assign("tmp2", v("tmp1")),
                    assign(
                        "i",
                        CExpr::binary(BinaryOp::Add, v("tmp2"), CExpr::IntLit(1)),
                    ),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert!(
            matches!(cleaned, CStmt::For { .. }),
            "Two-step alias chain should be enough to connect update with loop condition"
        );
    }

    #[test]
    fn does_not_rewrite_while_to_for_when_alias_chain_is_too_long() {
        let input = CStmt::Block(vec![
            assign("i", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, v("i"), v("n")),
                CStmt::Block(vec![
                    assign("tmp1", v("i")),
                    assign("tmp2", v("tmp1")),
                    assign("tmp3", v("tmp2")),
                    assign(
                        "i",
                        CExpr::binary(BinaryOp::Add, v("tmp3"), CExpr::IntLit(1)),
                    ),
                ]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
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
        let input = CStmt::Block(vec![
            assign("local_4", CExpr::IntLit(0)),
            CStmt::while_loop(
                CExpr::binary(BinaryOp::Lt, CExpr::AddrOf(Box::new(v("local"))), v("n")),
                CStmt::Block(vec![assign(
                    "local_4",
                    CExpr::binary(BinaryOp::Add, v("local_4"), CExpr::IntLit(1)),
                )]),
            ),
        ]);

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert!(
            matches!(cleaned, CStmt::For { .. }),
            "Suffix-equivalent loop vars (local/local_4) should be treated as matching"
        );
    }

    #[test]
    fn uses_vm_transfer_selector_when_vm_step_is_absent() {
        let func = function_with_single_block(0x1000);
        let mut ctx = FoldingContext::new(64);
        let artifact = r2sym::SemanticArtifact {
            stage: r2sym::RefinementStage::Residual,
            granularity: r2sym::ArtifactGranularity::SummaryOnly,
            execution: r2sym::ExecutionModel::Vm,
            body: r2sym::SemanticArtifactBody::Vm(Box::new(r2sym::VmArtifactBody {
                interpreter: None,
                step_summary: None,
                transfer_summary: Some(r2sym::VmStepSummary {
                    kind: r2sym::InterpreterKind::SwitchDispatch,
                    loop_header: 0x1000,
                    dispatch_header: 0x1000,
                    selector: Some("vm.sel".to_string()),
                    dispatch_targets: vec![0x1004],
                    default_target: None,
                    case_values_by_target: BTreeMap::from([(0x1004, vec![1, 2])]),
                    loop_latches: vec![0x1000],
                    state_inputs: vec!["state".to_string()],
                    state_outputs: vec!["state".to_string()],
                    step_blocks: vec![0x1000],
                    handler_regions: BTreeMap::from([(0x1004, vec![0x1004, 0x1008])]),
                    handler_state_inputs: BTreeMap::from([(0x1004, vec!["state".to_string()])]),
                    handler_state_outputs: BTreeMap::from([(0x1004, vec!["state".to_string()])]),
                    handler_state_updates: BTreeMap::from([(
                        0x1004,
                        vec![r2sym::VmStateUpdate {
                            output: "state".to_string(),
                            expr: "state + 1".to_string(),
                            value: r2sym::VmValueExpr::Expr("state + 1".to_string()),
                            exact: false,
                        }],
                    )]),
                    handler_exit_guards: BTreeMap::new(),
                    handler_memory_read_effects: BTreeMap::new(),
                    handler_memory_write_effects: BTreeMap::new(),
                    handler_memory_reads: BTreeMap::from([(0x1004, 1)]),
                    handler_memory_writes: BTreeMap::from([(0x1004, 1)]),
                    handler_calls: BTreeMap::from([(0x1004, 0)]),
                    handler_conditional_branches: BTreeMap::from([(0x1004, 0)]),
                    handler_exit_targets: BTreeMap::from([(0x1004, vec![0x1008])]),
                    redispatch_handlers: vec![0x1000],
                    returning_handlers: vec![],
                    truncated_handlers: vec![],
                    transfers: vec![r2sym::VmTransferArm {
                        handler_target: 0x1004,
                        case_values: vec![1, 2],
                        region_blocks: vec![0x1004, 0x1008],
                        exit_targets: vec![0x1008],
                        exit_guards: Vec::new(),
                        state_updates: vec![r2sym::VmStateUpdate {
                            output: "state".to_string(),
                            expr: "state + 1".to_string(),
                            value: r2sym::VmValueExpr::Expr("state + 1".to_string()),
                            exact: false,
                        }],
                        selector_update: None,
                        memory_reads: Vec::new(),
                        memory_writes: Vec::new(),
                        residual_guards: false,
                        residual_memory_effects: false,
                        exact: false,
                        redispatch: false,
                        may_return: false,
                        truncated: false,
                    }],
                }),
            })),
            diagnostics: r2sym::SemanticArtifactDiagnostics {
                branches_evaluated: 0,
                branches_pruned: 0,
                branches_unknown: 0,
                skipped_missing_arch: false,
                skipped_large_cfg: false,
                residual_reasons: Vec::new(),
                interpreter: None,
                ambiguous_targets: Vec::new(),
                cache_hit: false,
            },
        };
        install_semantic_artifact(&mut ctx, artifact);

        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        assert_eq!(
            structurer.get_switch_expression(0x1000),
            Some((CExpr::Var("vm.sel".to_string()), None))
        );
    }

    #[test]
    fn symbolic_exact_reachable_target_uses_control_island_fallback() {
        let func = function_with_single_block(0x2000);
        let mut ctx = FoldingContext::new(64);
        let region = crate::test_semantic_region(
            0x2000,
            BTreeSet::from([0x2004, 0x2008]),
            vec![
                crate::test_control_fact(
                    0x2004,
                    r2sym::SymbolicReachabilityStatus::Reachable,
                    None,
                    Some("x == 0"),
                    None,
                    r2sym::SemanticEvidence::exact(),
                ),
                crate::test_control_fact(
                    0x2008,
                    r2sym::SymbolicReachabilityStatus::Unreachable,
                    None,
                    Some("!(x == 0)"),
                    None,
                    r2sym::SemanticEvidence::exact(),
                ),
            ],
            Vec::new(),
        );
        install_semantic_artifact(
            &mut ctx,
            crate::test_native_semantic_artifact(
                r2sym::RefinementStage::Compiled,
                r2sym::ArtifactGranularity::Regioned,
                r2sym::SliceClass::Worker,
                false,
                Vec::new(),
                vec![region],
            ),
        );

        let structurer = ControlFlowStructurer::new(&func, &ctx);
        assert_eq!(
            structurer.symbolic_exact_reachable_target(0x2000),
            Some(0x2004)
        );
    }

    #[test]
    fn certified_structuring_refuses_symbolic_exact_target_branch_elision() {
        let func = function_with_conditional_return_blocks(0x2000, 0x2004, 0x2008);
        let mut ctx = FoldingContext::new(64);
        install_function_facts(
            &mut ctx,
            r2types::FunctionFacts::default().with_decompile_route(
                certified_standard_route_for_test("test certified exact target refusal"),
            ),
        );
        let region = crate::test_semantic_region(
            0x2000,
            BTreeSet::from([0x2004, 0x2008]),
            vec![
                crate::test_control_fact(
                    0x2004,
                    r2sym::SymbolicReachabilityStatus::Reachable,
                    Some(true),
                    Some("x == 0"),
                    None,
                    r2sym::SemanticEvidence::exact(),
                ),
                crate::test_control_fact(
                    0x2008,
                    r2sym::SymbolicReachabilityStatus::Unreachable,
                    Some(false),
                    Some("!(x == 0)"),
                    None,
                    r2sym::SemanticEvidence::exact(),
                ),
            ],
            Vec::new(),
        );
        install_semantic_artifact(
            &mut ctx,
            crate::test_native_semantic_artifact(
                r2sym::RefinementStage::Compiled,
                r2sym::ArtifactGranularity::Regioned,
                r2sym::SliceClass::Worker,
                false,
                Vec::new(),
                vec![region],
            ),
        );

        let region = Region::IfThenElse {
            cond_block: 0x2000,
            then_region: Box::new(Region::Block(0x2004)),
            else_region: Some(Box::new(Region::Block(0x2008))),
            merge_block: None,
        };
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let stmt = structurer.structure_region(&region);

        assert!(
            !stmt_contains_if(&stmt),
            "certified mode must not elide or render a branch from r2sym exact target side-channel proof: {stmt:?}"
        );
        assert!(
            stmt_contains_comment(&stmt, "unresolved branch condition")
                || stmt_contains_comment(&stmt, "uncertified branch structure"),
            "missing FunctionFacts control proof should residualize exact-target branch elision, got {stmt:?}"
        );
    }

    #[test]
    fn symbolic_actionable_reachable_target_uses_likely_control_island_fallback() {
        let func = function_with_single_block(0x2000);
        let mut ctx = FoldingContext::new(64);
        let likely =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::PartialPathCoverage);
        let region = crate::test_semantic_region(
            0x2000,
            BTreeSet::from([0x2004, 0x2008]),
            vec![
                crate::test_control_fact(
                    0x2004,
                    r2sym::SymbolicReachabilityStatus::Reachable,
                    None,
                    Some("x == 0"),
                    Some(r2sym::BackwardConditionSummary {
                        simplified: "x == 0".to_string(),
                        terms: vec!["x == 0".to_string()],
                        memory_terms: Vec::new(),
                        backward_memory_substitutions: 0,
                        backward_memory_candidate_enumerations: 0,
                        backward_memory_residual_fallbacks: 0,
                        precision: r2sym::BackwardConditionPrecision::OverApprox,
                        supported_paths: 1,
                        total_paths: 2,
                    }),
                    likely.clone(),
                ),
                crate::test_control_fact(
                    0x2008,
                    r2sym::SymbolicReachabilityStatus::Unreachable,
                    None,
                    Some("!(x == 0)"),
                    None,
                    likely.clone(),
                ),
            ],
            Vec::new(),
        );
        install_semantic_artifact(
            &mut ctx,
            crate::test_native_semantic_artifact(
                r2sym::RefinementStage::Compiled,
                r2sym::ArtifactGranularity::Regioned,
                r2sym::SliceClass::Worker,
                false,
                Vec::new(),
                vec![region],
            ),
        );

        let structurer = ControlFlowStructurer::new(&func, &ctx);
        assert_eq!(
            structurer.symbolic_actionable_reachable_target(0x2000),
            Some(0x2004)
        );
    }

    #[test]
    fn symbolic_actionable_if_refuses_likely_target_without_exact_reachability() {
        let func = function_with_return_blocks(&[0x2000, 0x2004, 0x2008]);
        let mut ctx = FoldingContext::new(64);
        let likely =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::PartialPathCoverage);
        let region = crate::test_semantic_region(
            0x2000,
            BTreeSet::from([0x2004, 0x2008]),
            vec![
                crate::test_control_fact(
                    0x2008,
                    r2sym::SymbolicReachabilityStatus::Reachable,
                    None,
                    Some("x == 0"),
                    Some(r2sym::BackwardConditionSummary {
                        simplified: "x == 0".to_string(),
                        terms: vec!["x == 0".to_string()],
                        memory_terms: Vec::new(),
                        backward_memory_substitutions: 0,
                        backward_memory_candidate_enumerations: 0,
                        backward_memory_residual_fallbacks: 0,
                        precision: r2sym::BackwardConditionPrecision::OverApprox,
                        supported_paths: 1,
                        total_paths: 2,
                    }),
                    likely.clone(),
                ),
                crate::test_control_fact(
                    0x2004,
                    r2sym::SymbolicReachabilityStatus::Unreachable,
                    None,
                    Some("!(x == 0)"),
                    Some(r2sym::BackwardConditionSummary {
                        simplified: "!(x == 0)".to_string(),
                        terms: vec!["!(x == 0)".to_string()],
                        memory_terms: Vec::new(),
                        backward_memory_substitutions: 0,
                        backward_memory_candidate_enumerations: 0,
                        backward_memory_residual_fallbacks: 0,
                        precision: r2sym::BackwardConditionPrecision::OverApprox,
                        supported_paths: 1,
                        total_paths: 2,
                    }),
                    likely.clone(),
                ),
            ],
            Vec::new(),
        );
        install_semantic_artifact(
            &mut ctx,
            crate::test_native_semantic_artifact(
                r2sym::RefinementStage::Compiled,
                r2sym::ArtifactGranularity::Regioned,
                r2sym::SliceClass::Worker,
                false,
                Vec::new(),
                vec![region],
            ),
        );

        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let then_region = crate::region::Region::Sequence(vec![
            crate::region::Region::Block(0x2004),
            crate::region::Region::Block(0x2008),
        ]);

        let rewritten =
            structurer.try_structure_symbolic_actionable_if(0x2000, &then_region, None, None);
        assert!(
            rewritten.is_none(),
            "likely/actionable reachability is not enough to erase a native branch"
        );
    }

    #[test]
    fn structured_worker_route_refuses_executable_if_from_summary_region() {
        let func = function_with_conditional_return_blocks(0x2000, 0x2004, 0x2008);
        let mut ctx = FoldingContext::new(64);
        let region = r2sym::SemanticRegion {
            anchor: 0x2000,
            frontier: std::collections::BTreeSet::from([0x2004, 0x2008]),
            control: vec![
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x2004,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                        condition: Some("x == 0".to_string()),
                        compiled: Some(r2sym::BackwardConditionSummary {
                            simplified: "x == 0".to_string(),
                            terms: vec!["x == 0".to_string()],
                            memory_terms: vec![r2sym::BackwardMemoryCondition {
                                region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
                                offset_lo: 0,
                                offset_hi: 0,
                                size: 1,
                                exact_offset: true,
                                address_terms: Vec::new(),
                                evidence: r2sym::SemanticEvidence::exact(),
                                binding: None,
                                expr: "*arg0".to_string(),
                                value_expr: Some("0x0:8".to_string()),
                                exact_value: true,
                            }],
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: r2sym::BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x2008,
                        status: r2sym::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                        condition: Some("!(x == 0)".to_string()),
                        compiled: None,
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
            ],
            memory: vec![r2sym::Judged::new(
                r2sym::MemoryFact {
                    term: r2sym::BackwardMemoryCondition {
                        region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
                        offset_lo: 0,
                        offset_hi: 0,
                        size: 1,
                        exact_offset: true,
                        address_terms: Vec::new(),
                        evidence: r2sym::SemanticEvidence::exact(),
                        binding: None,
                        expr: "*arg0".to_string(),
                        value_expr: Some("0x0:8".to_string()),
                        exact_value: true,
                    },
                },
                r2sym::SemanticEvidence::exact(),
            )],
            pre: Vec::new(),
            post: Vec::new(),
            targets: vec![
                r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x2004,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
                r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x2008,
                        status: r2sym::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
            ],
        };
        let artifact = r2sym::SemanticArtifact {
            stage: r2sym::RefinementStage::Compiled,
            granularity: r2sym::ArtifactGranularity::Regioned,
            execution: r2sym::ExecutionModel::Native,
            body: r2sym::SemanticArtifactBody::Native(r2sym::NativeArtifactBody {
                summary: r2sym::NativeFunctionSummary {
                    slice_class: r2sym::SliceClass::Worker,
                    role_identity: None,
                    closure_functions: 1,
                    helper_functions: 0,
                    derived_summaries: 0,
                    derived_diagnostics: Default::default(),
                    region_summaries: Vec::new(),
                    worker_summaries: Vec::new(),
                },
                regions: BTreeMap::from([(region.key(), region)]),
            }),
            diagnostics: r2sym::SemanticArtifactDiagnostics {
                branches_evaluated: 1,
                branches_pruned: 1,
                branches_unknown: 0,
                skipped_missing_arch: false,
                skipped_large_cfg: true,
                residual_reasons: vec![r2sym::ResidualReason::LargeCfg],
                interpreter: None,
                ambiguous_targets: Vec::new(),
                cache_hit: false,
            },
        };
        install_semantic_artifact(&mut ctx, artifact);

        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let routed = crate::consumer_structured::primary_body_for_semantic_route(
            &test_structured_worker_route("large native worker summarized as typed islands"),
            &mut structurer,
            Vec::new,
        );
        assert!(
            !stmt_contains_if(&routed.body_stmt),
            "summary-permission route must not emit executable if statements, got {:?}",
            routed.body_stmt
        );
        assert!(
            stmt_contains_comment(
                &routed.body_stmt,
                "render contract: summary facts only; no executable native C reconstructed"
            ),
            "summary-permission route must state the render contract, got {:?}",
            routed.body_stmt
        );
    }

    #[test]
    fn structured_worker_route_refuses_likely_false_branch_projection() {
        let func = function_with_conditional_return_blocks(0x2000, 0x2008, 0x2004);
        let mut ctx = FoldingContext::new(64);
        let likely =
            r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::DerivedFromRanking);
        let region = r2sym::SemanticRegion {
            anchor: 0x2000,
            frontier: std::collections::BTreeSet::from([0x2004, 0x2008]),
            control: vec![
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x2008,
                        status: r2sym::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(true),
                        condition: Some("x == 0".to_string()),
                        compiled: None,
                    },
                    likely.clone(),
                ),
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x2004,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(false),
                        condition: Some("!(x == 0)".to_string()),
                        compiled: Some(r2sym::BackwardConditionSummary {
                            simplified: "!(x == 0)".to_string(),
                            terms: vec!["!(x == 0)".to_string()],
                            memory_terms: vec![r2sym::BackwardMemoryCondition {
                                region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
                                offset_lo: 0,
                                offset_hi: 0,
                                size: 1,
                                exact_offset: true,
                                address_terms: Vec::new(),
                                evidence: likely.clone(),
                                binding: None,
                                expr: "*arg0".to_string(),
                                value_expr: Some("0x1:8".to_string()),
                                exact_value: true,
                            }],
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: r2sym::BackwardConditionPrecision::OverApprox,
                            supported_paths: 1,
                            total_paths: 2,
                        }),
                    },
                    likely.clone(),
                ),
            ],
            memory: vec![r2sym::Judged::new(
                r2sym::MemoryFact {
                    term: r2sym::BackwardMemoryCondition {
                        region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
                        offset_lo: 0,
                        offset_hi: 0,
                        size: 1,
                        exact_offset: true,
                        address_terms: Vec::new(),
                        evidence: likely.clone(),
                        binding: None,
                        expr: "*arg0".to_string(),
                        value_expr: Some("0x1:8".to_string()),
                        exact_value: true,
                    },
                },
                likely.clone(),
            )],
            pre: Vec::new(),
            post: Vec::new(),
            targets: vec![
                r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x2008,
                        status: r2sym::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(true),
                    },
                    likely.clone(),
                ),
                r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x2004,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(false),
                    },
                    likely.clone(),
                ),
            ],
        };
        let artifact = r2sym::SemanticArtifact {
            stage: r2sym::RefinementStage::Compiled,
            granularity: r2sym::ArtifactGranularity::Regioned,
            execution: r2sym::ExecutionModel::Native,
            body: r2sym::SemanticArtifactBody::Native(r2sym::NativeArtifactBody {
                summary: r2sym::NativeFunctionSummary {
                    slice_class: r2sym::SliceClass::Worker,
                    role_identity: None,
                    closure_functions: 0,
                    helper_functions: 0,
                    derived_summaries: 0,
                    derived_diagnostics: Default::default(),
                    region_summaries: Vec::new(),
                    worker_summaries: Vec::new(),
                },
                regions: BTreeMap::from([(region.key(), region)]),
            }),
            diagnostics: r2sym::SemanticArtifactDiagnostics {
                branches_evaluated: 1,
                branches_pruned: 0,
                branches_unknown: 0,
                skipped_missing_arch: false,
                skipped_large_cfg: true,
                residual_reasons: vec![r2sym::ResidualReason::LargeCfg],
                interpreter: None,
                ambiguous_targets: Vec::new(),
                cache_hit: false,
            },
        };
        install_semantic_artifact(&mut ctx, artifact);

        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let routed = crate::consumer_structured::primary_body_for_semantic_route(
            &test_structured_worker_route("likely semantic worker reachability"),
            &mut structurer,
            Vec::new,
        );
        assert!(
            !stmt_contains_if(&routed.body_stmt),
            "likely/actionable reachability must stay comment-only under summary permission, got {:?}",
            routed.body_stmt
        );
        assert!(
            stmt_contains_comment(
                &routed.body_stmt,
                "render contract: summary facts only; no executable native C reconstructed"
            ),
            "summary-permission route must state the render contract, got {:?}",
            routed.body_stmt
        );
    }

    #[test]
    fn structured_worker_route_refuses_multi_block_suffix_projection() {
        let func = function_with_multi_block_true_arm(0x2000, 0x2008, 0x200c, 0x2004);
        let mut ctx = FoldingContext::new(64);
        let region = r2sym::SemanticRegion {
            anchor: 0x2000,
            frontier: BTreeSet::from([0x2008, 0x2004]),
            control: vec![
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x2008,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                        condition: Some("x == 0".to_string()),
                        compiled: Some(r2sym::BackwardConditionSummary {
                            simplified: "x == 0".to_string(),
                            terms: vec!["x == 0".to_string()],
                            memory_terms: vec![r2sym::BackwardMemoryCondition {
                                region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
                                offset_lo: 0,
                                offset_hi: 0,
                                size: 1,
                                exact_offset: true,
                                address_terms: Vec::new(),
                                evidence: r2sym::SemanticEvidence::exact(),
                                binding: None,
                                expr: "*arg0".to_string(),
                                value_expr: Some("0x0:8".to_string()),
                                exact_value: true,
                            }],
                            backward_memory_substitutions: 0,
                            backward_memory_candidate_enumerations: 0,
                            backward_memory_residual_fallbacks: 0,
                            precision: r2sym::BackwardConditionPrecision::Exact,
                            supported_paths: 1,
                            total_paths: 1,
                        }),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
                r2sym::Judged::new(
                    r2sym::ControlFact {
                        target: 0x2004,
                        status: r2sym::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                        condition: Some("!(x == 0)".to_string()),
                        compiled: None,
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
            ],
            memory: vec![r2sym::Judged::new(
                r2sym::MemoryFact {
                    term: r2sym::BackwardMemoryCondition {
                        region: r2sym::BackwardMemoryRegion::Argument { index: 0 },
                        offset_lo: 0,
                        offset_hi: 0,
                        size: 1,
                        exact_offset: true,
                        address_terms: Vec::new(),
                        evidence: r2sym::SemanticEvidence::exact(),
                        binding: None,
                        expr: "*arg0".to_string(),
                        value_expr: Some("0x0:8".to_string()),
                        exact_value: true,
                    },
                },
                r2sym::SemanticEvidence::exact(),
            )],
            pre: Vec::new(),
            post: Vec::new(),
            targets: vec![
                r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x2008,
                        status: r2sym::SymbolicReachabilityStatus::Reachable,
                        branch_truth: Some(true),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
                r2sym::Judged::new(
                    r2sym::TargetFact {
                        target: 0x2004,
                        status: r2sym::SymbolicReachabilityStatus::Unreachable,
                        branch_truth: Some(false),
                    },
                    r2sym::SemanticEvidence::exact(),
                ),
            ],
        };
        let artifact = r2sym::SemanticArtifact {
            stage: r2sym::RefinementStage::Compiled,
            granularity: r2sym::ArtifactGranularity::Regioned,
            execution: r2sym::ExecutionModel::Native,
            body: r2sym::SemanticArtifactBody::Native(r2sym::NativeArtifactBody {
                summary: r2sym::NativeFunctionSummary {
                    slice_class: r2sym::SliceClass::Worker,
                    role_identity: None,
                    closure_functions: 0,
                    helper_functions: 0,
                    derived_summaries: 0,
                    derived_diagnostics: Default::default(),
                    region_summaries: Vec::new(),
                    worker_summaries: Vec::new(),
                },
                regions: BTreeMap::from([(region.key(), region)]),
            }),
            diagnostics: r2sym::SemanticArtifactDiagnostics {
                branches_evaluated: 1,
                branches_pruned: 0,
                branches_unknown: 0,
                skipped_missing_arch: false,
                skipped_large_cfg: true,
                residual_reasons: vec![r2sym::ResidualReason::LargeCfg],
                interpreter: None,
                ambiguous_targets: Vec::new(),
                cache_hit: false,
            },
        };
        install_semantic_artifact(&mut ctx, artifact);

        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let routed = crate::consumer_structured::primary_body_for_semantic_route(
            &test_structured_worker_route("semantic worker target suffix"),
            &mut structurer,
            Vec::new,
        );
        assert!(
            !stmt_contains_if(&routed.body_stmt),
            "summary-permission route must not emit target suffix C, got {:?}",
            routed.body_stmt
        );
        assert!(
            stmt_contains_comment(
                &routed.body_stmt,
                "render contract: summary facts only; no executable native C reconstructed"
            ),
            "summary-permission route must state the render contract, got {:?}",
            routed.body_stmt
        );
    }
}
