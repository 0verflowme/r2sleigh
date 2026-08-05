//! Control flow region identification.
//!
//! This module identifies structured regions in the CFG:
//! - Sequences (linear blocks)
//! - If-then-else (diamond patterns)
//! - Loops (natural loops with back edges)

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use r2ssa::{BlockTerminator, CFGEdge, SSAFunction, SSAOp, SSAVar, domtree::DomTree};

/// A control flow region.
#[derive(Debug, Clone)]
pub enum Region {
    /// A single basic block.
    Block(u64),
    /// A sequence of regions.
    Sequence(Vec<Region>),
    /// An if-then-else region.
    IfThenElse {
        /// The condition block.
        cond_block: u64,
        /// The then region.
        then_region: Box<Region>,
        /// The else region (optional).
        else_region: Option<Box<Region>>,
        /// The merge block (if any).
        merge_block: Option<u64>,
    },
    /// A while loop.
    WhileLoop {
        /// The header block (condition).
        header: u64,
        /// The loop body.
        body: Box<Region>,
    },
    /// A do-while loop.
    DoWhileLoop {
        /// The loop body.
        body: Box<Region>,
        /// The condition block.
        cond_block: u64,
    },
    /// A structured region whose control can leave through more than one
    /// distinct target. The head remains structurally valid; `exits` records
    /// the exact continuation entries that still require transfer lowering.
    MultiExit {
        /// Structured control region before the transfers.
        head: Box<Region>,
        /// Distinct external continuation entries.
        exits: Vec<u64>,
    },
    /// A switch statement.
    Switch {
        /// The block containing the switch expression.
        switch_block: u64,
        /// Case targets: (case_value, case_region).
        cases: Vec<(Option<u64>, Box<Region>)>,
        /// Default case region (if any).
        default: Option<Box<Region>>,
        /// The merge block after the switch (if any).
        merge_block: Option<u64>,
    },
    /// An irreducible region (contains gotos).
    Irreducible {
        /// Entry block.
        entry: u64,
        /// All blocks in this region.
        blocks: Vec<u64>,
    },
}

impl Region {
    /// Get the entry block of this region.
    pub fn entry(&self) -> u64 {
        match self {
            Self::Block(addr) => *addr,
            Self::Sequence(regions) => regions.first().map(|r| r.entry()).unwrap_or(0),
            Self::IfThenElse { cond_block, .. } => *cond_block,
            Self::WhileLoop { header, .. } => *header,
            Self::DoWhileLoop { body, .. } => body.entry(),
            Self::MultiExit { head, .. } => head.entry(),
            Self::Switch { switch_block, .. } => *switch_block,
            Self::Irreducible { entry, .. } => *entry,
        }
    }

    /// Get all blocks in this region.
    pub fn blocks(&self) -> Vec<u64> {
        match self {
            Self::Block(addr) => vec![*addr],
            Self::Sequence(regions) => regions.iter().flat_map(|r| r.blocks()).collect(),
            Self::IfThenElse {
                cond_block,
                then_region,
                else_region,
                merge_block,
            } => {
                let mut blocks = vec![*cond_block];
                blocks.extend(then_region.blocks());
                if let Some(else_r) = else_region {
                    blocks.extend(else_r.blocks());
                }
                if let Some(merge) = merge_block {
                    blocks.push(*merge);
                }
                blocks
            }
            Self::WhileLoop { header, body } => {
                let mut blocks = vec![*header];
                blocks.extend(body.blocks());
                blocks
            }
            Self::DoWhileLoop { body, cond_block } => {
                let mut blocks = body.blocks();
                blocks.push(*cond_block);
                blocks
            }
            Self::MultiExit { head, .. } => head.blocks(),
            Self::Switch {
                switch_block,
                cases,
                default,
                merge_block,
            } => {
                let mut blocks = vec![*switch_block];
                for (_, case_region) in cases {
                    blocks.extend(case_region.blocks());
                }
                if let Some(def) = default {
                    blocks.extend(def.blocks());
                }
                if let Some(merge) = merge_block {
                    blocks.push(*merge);
                }
                blocks
            }
            Self::Irreducible { blocks, .. } => blocks.clone(),
        }
    }
}

/// Region analyzer for identifying structured control flow.
pub struct RegionAnalyzer<'a> {
    func: &'a SSAFunction,
    /// Dominator tree computed from the current CFG snapshot.
    dominators: DomTree,
    /// Back edges in the CFG (target -> sources).
    back_edges: HashMap<u64, Vec<u64>>,
    /// Natural loops (header -> body blocks).
    loops: HashMap<u64, HashSet<u64>>,
    /// Post-dominator sets used to pick stable merge blocks for conditionals.
    post_dominators: HashMap<u64, BTreeSet<u64>>,
    /// Processed blocks.
    processed: HashSet<u64>,
    /// Blocks that exit a loop (break targets): block_addr -> exit_target.
    loop_exits: HashMap<u64, u64>,
    /// Blocks that continue to loop header: block_addr -> header.
    loop_continues: HashMap<u64, u64>,
    /// Blocks that need an explicit goto target for cross-loop control flow.
    loop_gotos: HashMap<u64, u64>,
    /// Optional reason when analysis had to abort/degrade.
    analysis_reason: Option<String>,
    /// Recursion guard for legacy recursive analysis.
    recursion_depth: usize,
    recursion_depth_limit: usize,
    /// Iterative collapse guard.
    max_collapse_iterations: usize,
}

#[derive(Debug, Clone)]
struct NormalizedSwitchInfo {
    cases: Vec<(u64, u64)>,
    default: Option<u64>,
}

#[derive(Debug, Clone)]
struct SwitchInfoCandidate {
    cases: Vec<(u64, u64)>,
    default: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SwitchChainCase {
    selector_key: String,
    case_value: u64,
    match_when_true: bool,
}

type LocalSwitchTargets = (Vec<(u64, u64)>, Option<u64>);

impl<'a> RegionAnalyzer<'a> {
    fn filter_local_switch_targets(
        &self,
        cases: Vec<(u64, u64)>,
        default: Option<u64>,
    ) -> Option<LocalSwitchTargets> {
        let cases = cases
            .into_iter()
            .filter(|(_, target)| self.func.cfg().get_block(*target).is_some())
            .collect::<Vec<_>>();
        let default = default.filter(|target| self.func.cfg().get_block(*target).is_some());
        (!cases.is_empty()).then_some((cases, default))
    }

    /// Create a new region analyzer.
    pub fn new(func: &'a SSAFunction) -> Self {
        let num_blocks = func.num_blocks();
        let dominators = DomTree::compute(func.cfg());
        let mut analyzer = Self {
            func,
            dominators,
            back_edges: HashMap::new(),
            loops: HashMap::new(),
            post_dominators: HashMap::new(),
            processed: HashSet::new(),
            loop_exits: HashMap::new(),
            loop_continues: HashMap::new(),
            loop_gotos: HashMap::new(),
            analysis_reason: None,
            recursion_depth: 0,
            recursion_depth_limit: (num_blocks.saturating_mul(8)).max(256),
            max_collapse_iterations: num_blocks.saturating_mul(10).max(256),
        };
        analyzer.find_back_edges();
        analyzer.find_loops();
        analyzer.compute_post_dominators();
        analyzer.find_loop_exits();
        analyzer
    }

    fn compute_post_dominators(&mut self) {
        let block_addrs = self.func.block_addrs();
        let all_blocks: BTreeSet<u64> = block_addrs.iter().copied().collect();
        let exit_blocks: BTreeSet<u64> = block_addrs
            .iter()
            .copied()
            .filter(|addr| self.func.successors(*addr).is_empty())
            .collect();

        let mut postdoms: HashMap<u64, BTreeSet<u64>> = HashMap::new();
        for &addr in block_addrs {
            let initial = if exit_blocks.contains(&addr) {
                BTreeSet::from([addr])
            } else {
                all_blocks.clone()
            };
            postdoms.insert(addr, initial);
        }

        let mut changed = true;
        while changed {
            changed = false;
            for &addr in block_addrs.iter().rev() {
                if exit_blocks.contains(&addr) {
                    continue;
                }

                let succs = self.func.successors(addr);
                if succs.is_empty() {
                    continue;
                }

                let mut new_set: Option<BTreeSet<u64>> = None;
                for succ in succs {
                    let succ_set = postdoms
                        .get(&succ)
                        .cloned()
                        .unwrap_or_else(|| BTreeSet::from([succ]));
                    new_set = Some(match new_set {
                        Some(current) => current.intersection(&succ_set).copied().collect(),
                        None => succ_set,
                    });
                }

                let mut new_set = new_set.unwrap_or_default();
                new_set.insert(addr);

                if postdoms.get(&addr) != Some(&new_set) {
                    postdoms.insert(addr, new_set);
                    changed = true;
                }
            }
        }

        self.post_dominators = postdoms;
    }

    /// Find back edges by the canonical dominance invariant.
    fn find_back_edges(&mut self) {
        self.back_edges.clear();
        for &block in self.func.block_addrs() {
            for succ in self.func.successors(block) {
                if self.dominators.dominates(succ, block) {
                    self.back_edges.entry(succ).or_default().push(block);
                }
            }
        }
        for sources in self.back_edges.values_mut() {
            sources.sort_unstable();
            sources.dedup();
        }
    }

    /// Find natural loops from back edges.
    fn find_loops(&mut self) {
        for (&header, sources) in &self.back_edges {
            let mut body = HashSet::new();
            body.insert(header);

            for &source in sources {
                self.collect_loop_body(source, header, &mut body);
            }

            self.loops.insert(header, body);
        }
    }

    /// Find loop exit and continue edges.
    fn find_loop_exits(&mut self) {
        for (&header, body) in &self.loops {
            for &block in body {
                // Check successors of each block in the loop
                for succ in self.func.successors(block) {
                    if succ == header && block != header {
                        // This is a continue (jump back to header, not from header itself)
                        self.loop_continues.insert(block, header);
                    } else if !body.contains(&succ) {
                        // This is a break (exit from loop)
                        self.loop_exits.insert(block, succ);
                    }
                }
            }
        }
    }

    /// Check if a block contains a break (loop exit).
    pub fn is_loop_break(&self, block: u64) -> bool {
        self.loop_exits.contains_key(&block)
    }

    /// Check if a block contains a continue (jump to loop header).
    pub fn is_loop_continue(&self, block: u64) -> bool {
        self.loop_continues.contains_key(&block)
    }

    /// Check if a block needs an explicit goto.
    pub fn is_loop_goto(&self, block: u64) -> bool {
        self.loop_gotos.contains_key(&block)
    }

    /// Get the goto target for a block, when present.
    pub fn get_loop_goto_target(&self, block: u64) -> Option<u64> {
        self.loop_gotos.get(&block).copied()
    }

    /// Get the loop exit target for a block.
    pub fn get_loop_exit_target(&self, block: u64) -> Option<u64> {
        self.loop_exits.get(&block).copied()
    }

    /// Reason for analysis degradation/short-circuit, if any.
    pub fn analysis_reason(&self) -> Option<&str> {
        self.analysis_reason.as_deref()
    }

    fn collect_loop_body(&self, source: u64, header: u64, body: &mut HashSet<u64>) {
        let mut worklist = vec![source];
        while let Some(block) = worklist.pop() {
            if block != header && !self.dominators.dominates(header, block) {
                continue;
            }
            if !body.insert(block) {
                continue;
            }
            for pred in self.func.predecessors(block) {
                if pred != header
                    && !body.contains(&pred)
                    && self.dominators.dominates(header, pred)
                {
                    worklist.push(pred);
                }
            }
        }
    }

    /// Analyze the function and build a region tree.
    ///
    /// Default path: iterative bottom-up loop collapsing (handles complex O2 CFGs).
    /// Fallback: recursive analysis with depth guard.
    /// `SLEIGH_DEC_LEGACY_ANALYZER=1`: force legacy recursive-only (A/B testing).
    pub fn analyze(&mut self) -> Region {
        self.processed.clear();
        self.loop_gotos.clear();
        self.analysis_reason = None;
        self.recursion_depth = 0;

        let force_legacy = std::env::var("SLEIGH_DEC_LEGACY_ANALYZER")
            .ok()
            .map(|v| {
                let v = v.trim().to_ascii_lowercase();
                v == "1" || v == "true" || v == "yes" || v == "on"
            })
            .unwrap_or(false);

        let back_edge_count: usize = self.back_edges.values().map(Vec::len).sum();
        let loop_count = self.loops.len();

        // Legacy-only path: opt-in via env var.  Guard complex graphs since the
        // recursive analyzer cannot handle deeply nested loop structures.
        if force_legacy {
            if loop_count > 8 || back_edge_count > 16 {
                self.analysis_reason = Some(format!(
                    "legacy region analyzer skipped for complex loop graph (loops={}, back_edges={})",
                    loop_count, back_edge_count
                ));
                return Region::Irreducible {
                    entry: self.func.entry,
                    blocks: self.func.block_addrs().to_vec(),
                };
            }
            return self.analyze_region_recursive(self.func.entry);
        }

        // Primary path: iterative analysis.  No complexity guard — the iterative
        // algorithm has its own safety via max_collapse_iterations.
        if let Some(region) = self.analyze_iterative() {
            return region;
        }

        // Iterative path failed to converge; fall back to recursive with depth guard.
        self.analysis_reason = None;
        self.processed.clear();
        self.loop_gotos.clear();
        self.recursion_depth = 0;

        // Guard the recursive fallback against complex graphs.
        if loop_count > 8 || back_edge_count > 16 {
            self.analysis_reason = Some(format!(
                "recursive fallback skipped for complex loop graph (loops={}, back_edges={})",
                loop_count, back_edge_count
            ));
            return Region::Irreducible {
                entry: self.func.entry,
                blocks: self.func.block_addrs().to_vec(),
            };
        }

        let region = self.analyze_region_recursive(self.func.entry);
        if self.analysis_reason.is_some() {
            return Region::Irreducible {
                entry: self.func.entry,
                blocks: self.func.block_addrs().to_vec(),
            };
        }
        region
    }

    fn analyze_region_recursive(&mut self, entry: u64) -> Region {
        if self.recursion_depth >= self.recursion_depth_limit {
            if self.analysis_reason.is_none() {
                self.analysis_reason = Some(format!(
                    "region analysis recursion limit exceeded (limit: {})",
                    self.recursion_depth_limit
                ));
            }
            let mut blocks = self.func.successors(entry);
            blocks.insert(0, entry);
            blocks.sort_unstable();
            blocks.dedup();
            return Region::Irreducible { entry, blocks };
        }

        self.recursion_depth += 1;
        let result = self.analyze_region_recursive_inner(entry);
        self.recursion_depth = self.recursion_depth.saturating_sub(1);
        result
    }

    fn analyze_region_recursive_inner(&mut self, entry: u64) -> Region {
        if self.processed.contains(&entry) {
            return Region::Block(entry);
        }

        // Check if this is a loop header
        if let Some(body) = self.loops.get(&entry).cloned() {
            return self.analyze_loop(entry, &body);
        }

        // Prefer explicit switch metadata from CFG terminators.
        if self.should_promote_nested_switch_metadata(entry)
            && let Some(switch_info) = self.normalized_switch_info(entry)
        {
            return self.analyze_switch_with_cases(entry, &switch_info.cases, switch_info.default);
        }

        // Get successors
        let succs = self.func.successors(entry);

        match succs.len() {
            0 => {
                // Terminal block
                self.processed.insert(entry);
                Region::Block(entry)
            }
            1 => {
                // Linear flow - try to build a sequence
                self.processed.insert(entry);
                let next = succs[0];
                let preds = self.func.predecessors(next);
                let next_loop_body = self.loops.get(&next);
                let is_loop_preheader = next_loop_body
                    .map(|loop_body| !loop_body.contains(&entry))
                    .unwrap_or(false);

                if (preds.len() == 1 && !self.loops.contains_key(&next)) || is_loop_preheader {
                    // Can extend sequence
                    let next_region = self.analyze_region_recursive(next);
                    match next_region {
                        Region::Sequence(mut regions) => {
                            regions.insert(0, Region::Block(entry));
                            Region::Sequence(regions)
                        }
                        _ => Region::Sequence(vec![Region::Block(entry), next_region]),
                    }
                } else {
                    Region::Block(entry)
                }
            }
            2 => {
                // Conditional - prefer CFG edge polarity over successor order.
                if let Some((true_target, false_target)) = self.resolve_conditional_targets(entry) {
                    if let Some(switch_region) =
                        self.detect_conditional_switch_chain(entry, true_target, false_target)
                    {
                        return switch_region;
                    }
                    self.analyze_conditional(entry, true_target, false_target)
                } else {
                    // Fallback: preserve existing successor order when labels are unavailable.
                    self.analyze_conditional(entry, succs[0], succs[1])
                }
            }
            _ => {
                // Multiple successors - likely a switch statement
                // Try to detect switch pattern
                if let Some(switch_region) = self.detect_switch(entry, &succs) {
                    return switch_region;
                }
                // Fallback to irreducible
                self.processed.insert(entry);
                Region::Irreducible {
                    entry,
                    blocks: succs,
                }
            }
        }
    }

    fn should_promote_nested_switch_metadata(&self, entry: u64) -> bool {
        if self.func.switch_info(entry).is_some() {
            return true;
        }

        self.func.successors(entry).len() <= 1
    }

    fn analyze_conditional(&mut self, cond: u64, true_target: u64, false_target: u64) -> Region {
        self.processed.insert(cond);

        // Find the merge point (immediate post-dominator)
        let merge = self.find_merge_point(cond, true_target, false_target);

        // Analyze then and else branches
        let then_region = if true_target != merge.unwrap_or(u64::MAX) {
            Some(Box::new(self.analyze_region_recursive(true_target)))
        } else {
            None
        };

        let else_region = if false_target != merge.unwrap_or(u64::MAX) {
            Some(Box::new(self.analyze_region_recursive(false_target)))
        } else {
            None
        };

        match (then_region, else_region) {
            (Some(then_r), Some(else_r)) => Region::IfThenElse {
                cond_block: cond,
                then_region: then_r,
                else_region: Some(else_r),
                merge_block: merge,
            },
            (Some(then_r), None) => Region::IfThenElse {
                cond_block: cond,
                then_region: then_r,
                else_region: None,
                merge_block: merge,
            },
            (None, Some(else_r)) => {
                // Swap branches (invert condition in codegen)
                Region::IfThenElse {
                    cond_block: cond,
                    then_region: else_r,
                    else_region: None,
                    merge_block: merge,
                }
            }
            (None, None) => Region::Block(cond),
        }
    }

    fn find_merge_point(&self, _cond: u64, true_target: u64, false_target: u64) -> Option<u64> {
        let mut true_reachable = HashSet::new();
        self.collect_reachable(true_target, &mut true_reachable, 10);

        let mut false_reachable = HashSet::new();
        self.collect_reachable(false_target, &mut false_reachable, 10);

        let mut common: Vec<u64> = true_reachable
            .into_iter()
            .filter(|block| false_reachable.contains(block))
            .filter(|block| {
                self.post_dominates(true_target, *block)
                    && self.post_dominates(false_target, *block)
            })
            .collect();
        common.sort_unstable_by_key(|block| {
            (
                self.shortest_distance(true_target, *block)
                    .unwrap_or(usize::MAX),
                self.shortest_distance(false_target, *block)
                    .unwrap_or(usize::MAX),
                *block,
            )
        });
        common.into_iter().next()
    }

    fn post_dominates(&self, start: u64, candidate: u64) -> bool {
        self.post_dominators
            .get(&start)
            .map(|set| set.contains(&candidate))
            .unwrap_or(false)
    }

    fn shortest_distance(&self, start: u64, target: u64) -> Option<usize> {
        if start == target {
            return Some(0);
        }

        let mut queue = VecDeque::from([(start, 0usize)]);
        let mut visited = HashSet::from([start]);

        while let Some((block, dist)) = queue.pop_front() {
            for succ in self.func.successors(block) {
                if !visited.insert(succ) {
                    continue;
                }
                if succ == target {
                    return Some(dist + 1);
                }
                queue.push_back((succ, dist + 1));
            }
        }

        None
    }

    fn resolve_conditional_targets(&self, cond: u64) -> Option<(u64, u64)> {
        let succs = self.func.successors(cond);
        if succs.len() != 2 {
            return None;
        }

        let mut true_target = None;
        let mut false_target = None;

        for succ in succs {
            match self.func.edge_type(cond, succ) {
                Some(CFGEdge::True) => true_target = Some(succ),
                Some(CFGEdge::False) => false_target = Some(succ),
                _ => {}
            }
        }

        Some((true_target?, false_target?))
    }

    fn collect_reachable(&self, start: u64, reachable: &mut HashSet<u64>, depth: usize) {
        if depth == 0 || reachable.contains(&start) {
            return;
        }
        reachable.insert(start);
        for succ in self.func.successors(start) {
            self.collect_reachable(succ, reachable, depth - 1);
        }
    }

    fn analyze_loop(&mut self, header: u64, body: &HashSet<u64>) -> Region {
        self.processed.insert(header);

        // A pre-tested loop must enter a distinct body block. A conditional
        // self-edge executes the header's value/effect operations before its
        // latch test and is therefore a do-while loop, not an empty while.
        if let Some(body_entry) = self.pretest_loop_body_entry(header, body) {
            // While loop: header is the condition
            let mut body_blocks = body.clone();
            body_blocks.remove(&header);
            let body_region = self.analyze_loop_body(body_entry, &body_blocks, false);

            Region::WhileLoop {
                header,
                body: Box::new(body_region),
            }
        } else {
            // Guarded infinite-loop pattern:
            //   loop_head -> guard
            //   guard: if (break_cond) break; ...
            // Recover this as while(cond) from region analysis instead of cleanup.
            if let Some((guard_block, body_entry)) = self.find_precheck_guard(header, body) {
                let mut body_blocks = body.clone();
                body_blocks.remove(&guard_block);
                if header != guard_block && self.func.successors(header).len() == 1 {
                    body_blocks.remove(&header);
                }
                let body_region = self.analyze_loop_body(body_entry, &body_blocks, false);
                return Region::WhileLoop {
                    header: guard_block,
                    body: Box::new(body_region),
                };
            }

            // Do-while or infinite loop.  When the loop continuation test lives
            // in a unique latch, anchor the condition there; the header may be
            // a one-way body block in optimized CFGs.
            let cond_block = self
                .unique_loop_latch_condition_block(header, body)
                .unwrap_or(header);
            let body_region = self.analyze_loop_body(header, body, true);
            Region::DoWhileLoop {
                body: Box::new(body_region),
                cond_block,
            }
        }
    }

    fn pretest_loop_body_entry(&self, header: u64, body: &HashSet<u64>) -> Option<u64> {
        let successors = self.func.successors(header);
        if successors.len() != 2 || !successors.iter().any(|addr| !body.contains(addr)) {
            return None;
        }
        let mut entries = successors
            .into_iter()
            .filter(|addr| *addr != header && body.contains(addr));
        let entry = entries.next()?;
        entries.next().is_none().then_some(entry)
    }

    fn unique_loop_latch_condition_block(&self, header: u64, body: &HashSet<u64>) -> Option<u64> {
        let mut candidates = body
            .iter()
            .copied()
            .filter(|block| {
                let succs = self.func.successors(*block);
                succs.contains(&header) && succs.iter().any(|succ| !body.contains(succ))
            })
            .collect::<Vec<_>>();
        candidates.sort_unstable();
        candidates.dedup();
        if candidates.len() == 1 {
            Some(candidates[0])
        } else {
            None
        }
    }

    fn analyze_loop_body(
        &mut self,
        entry: u64,
        body: &HashSet<u64>,
        include_processed_entry: bool,
    ) -> Region {
        if body.is_empty() {
            return Region::Sequence(Vec::new());
        }

        let mut blocks = Vec::new();
        let mut seen = HashSet::new();
        self.collect_loop_body_order(entry, body, &mut seen, &mut blocks);

        for &b in body {
            if !seen.contains(&b) {
                blocks.push(b);
            }
        }

        let mut regions = Vec::new();
        for b in blocks {
            if self.processed.contains(&b) && !(include_processed_entry && b == entry) {
                continue;
            }
            regions.push(if include_processed_entry && b == entry {
                Region::Block(b)
            } else {
                self.analyze_region_recursive(b)
            });
        }

        if regions.is_empty() {
            Region::Sequence(Vec::new())
        } else if regions.len() == 1 {
            regions.remove(0)
        } else {
            Region::Sequence(regions)
        }
    }

    fn collect_loop_body_order(
        &self,
        start: u64,
        body: &HashSet<u64>,
        seen: &mut HashSet<u64>,
        out: &mut Vec<u64>,
    ) {
        // Iterative DFS that produces the same pre-order as the recursive version.
        let mut stack = vec![start];
        while let Some(block) = stack.pop() {
            if !body.contains(&block) || !seen.insert(block) {
                continue;
            }
            out.push(block);
            // Push successors in reverse order so the first successor is processed first.
            let succs: Vec<u64> = self
                .func
                .successors(block)
                .into_iter()
                .filter(|s| body.contains(s))
                .collect();
            for s in succs.into_iter().rev() {
                stack.push(s);
            }
        }
    }

    fn find_precheck_guard(&self, header: u64, body: &HashSet<u64>) -> Option<(u64, u64)> {
        if self.func.successors(header).len() != 1 {
            return None;
        }

        for &block in body {
            if block == header {
                continue;
            }
            let preds = self.func.predecessors(block);
            if !preds.contains(&header) {
                continue;
            }

            let succs = self.func.successors(block);
            if succs.len() != 2 {
                continue;
            }

            let mut inside = None;
            let mut outside = false;
            for succ in succs {
                if body.contains(&succ) {
                    inside = Some(succ);
                } else {
                    outside = true;
                }
            }

            if outside
                && let Some(next_body) = inside
                && next_body != header
            {
                return Some((block, next_body));
            }
        }

        None
    }

    /// Check if a block is a loop header.
    pub fn is_loop_header(&self, block: u64) -> bool {
        self.loops.contains_key(&block)
    }

    /// Get the loop body for a header.
    pub fn get_loop_body(&self, header: u64) -> Option<&HashSet<u64>> {
        self.loops.get(&header)
    }

    /// Detect a switch statement pattern.
    /// Returns a Switch region if the entry block dispatches to multiple targets.
    fn detect_switch(&mut self, entry: u64, targets: &[u64]) -> Option<Region> {
        // A switch is detected when:
        // 1. Multiple successors (already checked by caller)
        // 2. Targets don't all merge back to the same point (that would be if-else chain)

        if targets.len() < 3 {
            // Too few targets for a meaningful switch
            return None;
        }

        // Find the common merge point for all targets
        let merge = self.find_switch_merge(targets);

        let Some(NormalizedSwitchInfo {
            cases: switch_cases,
            default: def,
        }) = self.normalized_switch_info(entry)
        else {
            if self.analysis_reason.is_none() {
                self.analysis_reason = Some(format!(
                    "switch-like block 0x{entry:x} has multiple successors but no canonical case values"
                ));
            }
            return None;
        };

        self.processed.insert(entry);

        // Build case regions for each target
        let mut cases = Vec::new();
        let default_target = def;

        // Group cases by target and deduplicate
        let mut target_to_values: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
        for (value, target) in &switch_cases {
            target_to_values.entry(*target).or_default().push(*value);
        }

        for (&target, values) in &target_to_values {
            if Some(target) == merge || Some(target) == default_target {
                continue;
            }
            // Use the first value for this target
            let case_value = values.first().copied();
            let case_region = Box::new(self.analyze_region_recursive(target));
            cases.push((case_value, case_region));
        }
        cases.sort_by_key(|(value, _)| value.unwrap_or(u64::MAX));

        // Build default region if we have one
        let default = default_target.map(|addr| Box::new(self.analyze_region_recursive(addr)));

        Some(Region::Switch {
            switch_block: entry,
            cases,
            default,
            merge_block: merge,
        })
    }

    fn analyze_switch_with_cases(
        &mut self,
        entry: u64,
        switch_cases: &[(u64, u64)],
        default: Option<u64>,
    ) -> Region {
        self.processed.insert(entry);

        let mut targets: Vec<u64> = switch_cases.iter().map(|(_, t)| *t).collect();
        if let Some(def) = default {
            targets.push(def);
        }
        targets.sort();
        targets.dedup();

        let merge = self.find_switch_merge(&targets);

        let mut target_to_values: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
        for (value, target) in switch_cases {
            target_to_values.entry(*target).or_default().push(*value);
        }

        let mut cases = Vec::new();
        for (&target, values) in &target_to_values {
            if Some(target) == merge || Some(target) == default {
                continue;
            }
            let case_region = Box::new(self.analyze_region_recursive(target));
            cases.push((values.first().copied(), case_region));
        }
        cases.sort_by_key(|(v, _)| v.unwrap_or(u64::MAX));

        let default_region = default
            .filter(|t| Some(*t) != merge)
            .map(|addr| Box::new(self.analyze_region_recursive(addr)));

        Region::Switch {
            switch_block: entry,
            cases,
            default: default_region,
            merge_block: merge,
        }
    }

    fn detect_conditional_switch_chain(
        &mut self,
        entry: u64,
        true_target: u64,
        false_target: u64,
    ) -> Option<Region> {
        let mut processed_blocks = vec![entry];
        let mut switch_cases = Vec::new();
        let mut compare_block = entry;
        let mut current_true = true_target;
        let mut current_false = false_target;
        let mut selector_key = None;

        for _ in 0..16 {
            let compare = self.extract_switch_chain_case(compare_block)?;
            if let Some(expected) = selector_key.as_ref() {
                if expected != &compare.selector_key {
                    return None;
                }
            } else {
                selector_key = Some(compare.selector_key.clone());
            }

            let true_path = self.follow_branch_only_chain(current_true);
            let false_path = self.follow_branch_only_chain(current_false);
            let next_selector = selector_key.as_ref()?;
            let true_compare = self
                .extract_switch_chain_case(true_path)
                .filter(|next| next.selector_key == *next_selector);
            let false_compare = self
                .extract_switch_chain_case(false_path)
                .filter(|next| next.selector_key == *next_selector);

            match (true_compare, false_compare) {
                (Some(_), Some(_)) => return None,
                (Some(_), None) => {
                    switch_cases.push((compare.case_value, false_path));
                    let (next_true, next_false) = self.resolve_conditional_targets(true_path)?;
                    processed_blocks.push(true_path);
                    compare_block = true_path;
                    current_true = next_true;
                    current_false = next_false;
                }
                (None, Some(_)) => {
                    switch_cases.push((compare.case_value, true_path));
                    let (next_true, next_false) = self.resolve_conditional_targets(false_path)?;
                    processed_blocks.push(false_path);
                    compare_block = false_path;
                    current_true = next_true;
                    current_false = next_false;
                }
                (None, None) => {
                    let (case_target, default_target) = if compare.match_when_true {
                        (true_path, false_path)
                    } else {
                        (false_path, true_path)
                    };
                    switch_cases.push((compare.case_value, case_target));
                    if switch_cases.len() < 4 {
                        return None;
                    }
                    switch_cases.sort_unstable_by_key(|(value, _)| *value);
                    switch_cases.dedup_by_key(|(value, _)| *value);
                    for block in processed_blocks {
                        self.processed.insert(block);
                    }
                    return Some(self.analyze_switch_with_cases(
                        entry,
                        &switch_cases,
                        Some(default_target),
                    ));
                }
            }
        }

        None
    }

    fn normalized_switch_info(&self, entry: u64) -> Option<NormalizedSwitchInfo> {
        if let Some((cases, default)) = self.func.switch_info(entry) {
            let (cases, default) = self.filter_local_switch_targets(cases, default)?;
            let cases = self.canonical_switch_cases(&cases);
            return Some(NormalizedSwitchInfo { cases, default });
        }

        let mut best = None;

        let mut visited = HashSet::from([entry]);
        let mut queue = VecDeque::from([(entry, 0usize)]);
        while let Some((block, depth)) = queue.pop_front() {
            if depth >= 6 {
                continue;
            }
            for succ in self.func.successors(block) {
                if !visited.insert(succ) {
                    continue;
                }
                if let Some((cases, default)) = self.func.switch_info(succ) {
                    let candidate = SwitchInfoCandidate { cases, default };
                    match best.as_ref() {
                        Some(current) if !self.is_better_switch_candidate(&candidate, current) => {}
                        _ => best = Some(candidate),
                    }
                }
                queue.push_back((succ, depth + 1));
            }
        }

        let best = best?;
        let (cases, default) = self.filter_local_switch_targets(best.cases, best.default)?;
        let cases = self.canonical_switch_cases(&cases);

        Some(NormalizedSwitchInfo { cases, default })
    }

    fn follow_branch_only_chain(&self, start: u64) -> u64 {
        let mut current = start;
        let mut seen = HashSet::new();
        while seen.insert(current) {
            let Some(block) = self.func.get_block(current) else {
                break;
            };
            let succs = self.func.successors(current);
            if succs.len() != 1
                || !block.phis.is_empty()
                || !block
                    .ops
                    .iter()
                    .all(|op| matches!(op, SSAOp::Branch { .. }))
            {
                break;
            }
            current = succs[0];
        }
        current
    }

    fn extract_switch_chain_case(&self, block_addr: u64) -> Option<SwitchChainCase> {
        let block = self.func.get_block(block_addr)?;
        let cond = block.ops.iter().rev().find_map(|op| match op {
            SSAOp::CBranch { cond, .. } => Some(cond),
            _ => None,
        })?;
        self.extract_switch_chain_case_from_var(block, cond, 0)
    }

    fn extract_switch_chain_case_from_var(
        &self,
        block: &r2ssa::FunctionSSABlock,
        var: &SSAVar,
        depth: usize,
    ) -> Option<SwitchChainCase> {
        if depth > 8 {
            return None;
        }
        let defining_op = block.ops.iter().rev().find(|op| op.dst() == Some(var))?;
        match defining_op {
            SSAOp::Copy { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::New { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Subpiece { src, .. } => {
                self.extract_switch_chain_case_from_var(block, src, depth + 1)
            }
            SSAOp::BoolNot { src, .. } => {
                let mut compare = self.extract_switch_chain_case_from_var(block, src, depth + 1)?;
                compare.match_when_true = !compare.match_when_true;
                Some(compare)
            }
            SSAOp::IntEqual { a, b, .. } => {
                self.extract_switch_chain_case_from_compare(block, a, b, true)
            }
            SSAOp::IntNotEqual { a, b, .. } => {
                self.extract_switch_chain_case_from_compare(block, a, b, false)
            }
            _ => None,
        }
    }

    fn extract_switch_chain_case_from_compare(
        &self,
        block: &r2ssa::FunctionSSABlock,
        a: &SSAVar,
        b: &SSAVar,
        match_when_true: bool,
    ) -> Option<SwitchChainCase> {
        if let Some(raw) = crate::analysis::utils::parse_const_value(&a.name) {
            return self
                .extract_selector_root(block, b, 0)
                .map(|selector_key| SwitchChainCase {
                    selector_key,
                    case_value: raw,
                    match_when_true,
                });
        }
        if let Some(raw) = crate::analysis::utils::parse_const_value(&b.name) {
            if raw == 0
                && let Some((selector_key, case_value)) =
                    self.extract_selector_minus_const(block, a, 0)
            {
                return Some(SwitchChainCase {
                    selector_key,
                    case_value,
                    match_when_true,
                });
            }
            return self
                .extract_selector_root(block, a, 0)
                .map(|selector_key| SwitchChainCase {
                    selector_key,
                    case_value: raw,
                    match_when_true,
                });
        }
        None
    }

    fn extract_selector_minus_const(
        &self,
        block: &r2ssa::FunctionSSABlock,
        var: &SSAVar,
        depth: usize,
    ) -> Option<(String, u64)> {
        if depth > 8 {
            return None;
        }
        let defining_op = block.ops.iter().rev().find(|op| op.dst() == Some(var))?;
        match defining_op {
            SSAOp::Copy { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::New { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Subpiece { src, .. } => {
                self.extract_selector_minus_const(block, src, depth + 1)
            }
            SSAOp::IntSub { a, b, .. } => {
                let raw = crate::analysis::utils::parse_const_value(&b.name)?;
                let selector_key = self.extract_selector_root(block, a, depth + 1)?;
                Some((selector_key, raw))
            }
            _ => None,
        }
    }

    fn extract_selector_root(
        &self,
        block: &r2ssa::FunctionSSABlock,
        var: &SSAVar,
        depth: usize,
    ) -> Option<String> {
        if depth > 8 || crate::analysis::utils::parse_const_value(&var.name).is_some() {
            return None;
        }
        let Some(defining_op) = block.ops.iter().rev().find(|op| op.dst() == Some(var)) else {
            return Some(var.display_name());
        };
        match defining_op {
            SSAOp::Copy { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::New { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Subpiece { src, .. } => self.extract_selector_root(block, src, depth + 1),
            _ => Some(var.display_name()),
        }
    }

    fn is_better_switch_candidate(
        &self,
        candidate: &SwitchInfoCandidate,
        current: &SwitchInfoCandidate,
    ) -> bool {
        self.switch_candidate_score(candidate) > self.switch_candidate_score(current)
    }

    fn switch_candidate_score(
        &self,
        candidate: &SwitchInfoCandidate,
    ) -> (usize, usize, usize, usize, usize) {
        let values = self.normalized_switch_values(&candidate.cases);
        let contiguous_run = Self::leading_contiguous_run_len(&values);
        let small_values = values.iter().filter(|value| **value <= 0xff).count();
        let unique_targets = candidate
            .cases
            .iter()
            .map(|(_, target)| *target)
            .collect::<BTreeSet<_>>()
            .len();
        let outliers = values.len().saturating_sub(contiguous_run);
        (
            contiguous_run,
            small_values,
            candidate.cases.len(),
            unique_targets,
            usize::MAX.saturating_sub(outliers),
        )
    }

    fn normalized_switch_values(&self, cases: &[(u64, u64)]) -> Vec<u64> {
        let mut values = cases.iter().map(|(value, _)| *value).collect::<Vec<_>>();
        values.sort_unstable();
        values.dedup();
        values
    }

    fn leading_contiguous_run_len(values: &[u64]) -> usize {
        let Some((&first, rest)) = values.split_first() else {
            return 0;
        };

        let mut expected = first;
        let mut len = 1usize;
        for value in rest {
            let next = expected.saturating_add(1);
            if *value != next {
                break;
            }
            expected = *value;
            len += 1;
        }
        len
    }

    fn canonical_switch_cases(&self, cases: &[(u64, u64)]) -> Vec<(u64, u64)> {
        let mut sorted = cases.to_vec();
        sorted.sort_unstable_by_key(|(value, target)| (*value, *target));
        sorted.dedup();
        sorted
    }

    /// Find the merge point for switch targets.
    fn find_switch_merge(&self, targets: &[u64]) -> Option<u64> {
        if targets.is_empty() {
            return None;
        }

        // Collect reachable blocks from each target
        let mut reachable_sets: Vec<HashSet<u64>> = Vec::new();
        for &target in targets {
            let mut reachable = HashSet::new();
            self.collect_reachable(target, &mut reachable, 10);
            reachable_sets.push(reachable);
        }

        // Find intersection of all reachable sets
        if let Some(first) = reachable_sets.first() {
            let common: HashSet<u64> = first
                .iter()
                .copied()
                .filter(|b| reachable_sets.iter().all(|s| s.contains(b)))
                .collect();

            // Return the first common block (closest to targets)
            // In a proper implementation, we'd want the immediate post-dominator
            return common.into_iter().min();
        }

        None
    }

    fn analyze_iterative(&mut self) -> Option<Region> {
        let mut graph = WorkingGraph::from_function(self.func);
        let all_loops = self.collect_ordered_loops();
        if all_loops.is_empty() {
            return Some(self.analyze_region_recursive(self.func.entry));
        }

        let mut iterations = 0usize;
        for loop_info in &all_loops {
            iterations = iterations.saturating_add(1);
            if iterations > self.max_collapse_iterations {
                self.analysis_reason = Some(format!(
                    "iterative region collapse iteration limit exceeded (limit: {})",
                    self.max_collapse_iterations
                ));
                return None;
            }

            if graph.collapse_loop(self, loop_info, &all_loops).is_err() {
                return None;
            }
        }

        let topo = match graph.topological_order() {
            Some(order) => order,
            None => {
                self.analysis_reason =
                    Some("iterative region graph still cyclic after loop collapse".to_string());
                return None;
            }
        };

        let entry_node = graph.node_for_block(self.func.entry)?;
        let region = self.analyze_post_collapse_iterative(entry_node, &graph, &topo);
        Some(region)
    }

    /// Build the final region tree from a post-collapse acyclic WorkingGraph
    /// using an iterative reverse-topological-order pass (no recursion).
    fn analyze_post_collapse_iterative(
        &mut self,
        entry: usize,
        graph: &WorkingGraph,
        topo: &[usize],
    ) -> Region {
        // Build a set of nodes reachable from entry so we skip disconnected parts.
        let reachable: HashSet<usize> = {
            let mut set = HashSet::new();
            let mut stack = vec![entry];
            while let Some(n) = stack.pop() {
                if set.insert(n) {
                    for s in graph.sorted_succs(n) {
                        stack.push(s);
                    }
                }
            }
            set
        };

        // Reverse topological order: leaves are processed first.
        let rev_topo: Vec<usize> = topo
            .iter()
            .rev()
            .copied()
            .filter(|id| reachable.contains(id))
            .collect();

        // Map from node → composed region.
        let mut region_map: HashMap<usize, Region> = HashMap::new();

        for node in &rev_topo {
            let node = *node;
            let base = match graph.node_region(node) {
                Some(r) => r,
                None => continue,
            };

            let succs = graph.sorted_succs(node);
            let composed = match succs.len() {
                0 => base,
                1 => {
                    let next = succs[0];
                    if graph.preds_len(next) == 1 {
                        if let Some(next_region) = region_map.remove(&next) {
                            Self::sequence_merge(base, next_region)
                        } else {
                            base
                        }
                    } else {
                        // Multi-predecessor: don't absorb; leave next for its own composition.
                        base
                    }
                }
                2 => {
                    let cond_block = match &base {
                        Region::Block(addr) => *addr,
                        _ => {
                            region_map.insert(node, Self::multi_exit_region(base, &succs, graph));
                            continue;
                        }
                    };
                    let (true_succ, false_succ) = graph
                        .conditional_succs(node)
                        .unwrap_or((succs[0], succs[1]));
                    let merge = self.find_working_merge_point(true_succ, false_succ, graph);
                    let then_region = if Some(true_succ) != merge {
                        region_map.remove(&true_succ).map(Box::new)
                    } else {
                        None
                    };
                    let else_region = if Some(false_succ) != merge {
                        region_map.remove(&false_succ).map(Box::new)
                    } else {
                        None
                    };
                    match (then_region, else_region) {
                        (Some(then_r), Some(else_r)) => Region::IfThenElse {
                            cond_block,
                            then_region: then_r,
                            else_region: Some(else_r),
                            merge_block: merge.and_then(|id| graph.node_entry(id)),
                        },
                        (Some(then_r), None) => Region::IfThenElse {
                            cond_block,
                            then_region: then_r,
                            else_region: None,
                            merge_block: merge.and_then(|id| graph.node_entry(id)),
                        },
                        (None, Some(else_r)) => Region::IfThenElse {
                            cond_block,
                            then_region: else_r,
                            else_region: None,
                            merge_block: merge.and_then(|id| graph.node_entry(id)),
                        },
                        _ => base,
                    }
                }
                _ => {
                    // 3+ successors: switch
                    let switch_block = match &base {
                        Region::Block(addr) => *addr,
                        _ => {
                            region_map.insert(node, Self::multi_exit_region(base, &succs, graph));
                            continue;
                        }
                    };
                    let merge = self.find_working_switch_merge(&succs, graph);
                    let mut cases = Vec::new();
                    if let Some(NormalizedSwitchInfo {
                        cases: switch_cases,
                        default,
                    }) = self.normalized_switch_info(switch_block)
                    {
                        let mut grouped: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
                        for (value, target) in &switch_cases {
                            grouped.entry(*target).or_default().push(*value);
                        }
                        for (target_block, values) in grouped {
                            let Some(target_node) = graph.node_for_block(target_block) else {
                                continue;
                            };
                            if Some(target_node) == merge {
                                continue;
                            }
                            if default
                                .and_then(|addr| graph.node_for_block(addr))
                                .is_some_and(|def_node| def_node == target_node)
                            {
                                continue;
                            }
                            let case_region =
                                region_map.remove(&target_node).unwrap_or_else(|| {
                                    graph
                                        .node_region(target_node)
                                        .unwrap_or(Region::Block(target_block))
                                });
                            cases.push((values.first().copied(), Box::new(case_region)));
                        }
                        let default_region = default
                            .and_then(|addr| graph.node_for_block(addr))
                            .filter(|node_id| Some(*node_id) != merge)
                            .map(|node_id| {
                                let r = region_map.remove(&node_id).unwrap_or_else(|| {
                                    graph.node_region(node_id).unwrap_or(Region::Block(
                                        default.unwrap_or(self.func.entry),
                                    ))
                                });
                                Box::new(r)
                            });
                        region_map.insert(
                            node,
                            Region::Switch {
                                switch_block,
                                cases,
                                default: default_region,
                                merge_block: merge.and_then(|id| graph.node_entry(id)),
                            },
                        );
                        continue;
                    }

                    if self.analysis_reason.is_none() {
                        self.analysis_reason = Some(format!(
                            "switch-like block 0x{switch_block:x} has multiple successors but no canonical case values"
                        ));
                    }
                    let mut blocks = graph.node_blocks(node);
                    blocks.extend(succs.iter().flat_map(|id| graph.node_blocks(*id)));
                    blocks.sort_unstable();
                    blocks.dedup();
                    Region::Irreducible {
                        entry: graph.node_entry(node).unwrap_or(self.func.entry),
                        blocks,
                    }
                }
            };
            region_map.insert(node, composed);
        }

        // The entry node's composed region is the final result.
        region_map
            .remove(&entry)
            .unwrap_or_else(|| Region::Irreducible {
                entry: self.func.entry,
                blocks: self.func.block_addrs().to_vec(),
            })
    }

    /// Merge two regions into a sequence, flattening nested Sequences.
    fn sequence_merge(a: Region, b: Region) -> Region {
        match (a, b) {
            (Region::Sequence(mut va), Region::Sequence(mut vb)) => {
                va.append(&mut vb);
                Region::Sequence(va)
            }
            (Region::Sequence(mut va), b) => {
                va.push(b);
                Region::Sequence(va)
            }
            (a, Region::Sequence(mut vb)) => {
                let mut out = vec![a];
                out.append(&mut vb);
                Region::Sequence(out)
            }
            (a, b) => Region::Sequence(vec![a, b]),
        }
    }

    fn multi_exit_region(head: Region, succs: &[usize], graph: &WorkingGraph) -> Region {
        let mut exits = succs
            .iter()
            .filter_map(|succ| graph.node_entry(*succ))
            .collect::<Vec<_>>();
        exits.sort_unstable();
        exits.dedup();
        Region::MultiExit {
            head: Box::new(head),
            exits,
        }
    }

    fn collect_ordered_loops(&self) -> Vec<LoopInfo> {
        let mut loop_infos: Vec<LoopInfo> = self
            .loops
            .iter()
            .map(|(header, body)| LoopInfo {
                header: *header,
                body: body.clone(),
                depth: 0,
            })
            .collect();

        for i in 0..loop_infos.len() {
            let mut depth = 0usize;
            for j in 0..loop_infos.len() {
                if i == j {
                    continue;
                }
                if loop_infos[j].body.len() > loop_infos[i].body.len()
                    && loop_infos[j].body.contains(&loop_infos[i].header)
                    && loop_infos[i].body.is_subset(&loop_infos[j].body)
                {
                    depth = depth.saturating_add(1);
                }
            }
            loop_infos[i].depth = depth;
        }

        loop_infos.sort_by(|a, b| {
            b.depth
                .cmp(&a.depth)
                .then(a.body.len().cmp(&b.body.len()))
                .then(a.header.cmp(&b.header))
        });
        loop_infos
    }

    fn find_working_merge_point(
        &self,
        true_target: usize,
        false_target: usize,
        graph: &WorkingGraph,
    ) -> Option<usize> {
        let mut true_reachable = HashSet::new();
        graph.collect_reachable_limited(true_target, &mut true_reachable, 10);
        let mut false_reachable = HashSet::new();
        graph.collect_reachable_limited(false_target, &mut false_reachable, 10);
        let mut common: Vec<usize> = true_reachable
            .into_iter()
            .filter(|id| false_reachable.contains(id))
            .collect();
        common.sort_by_key(|id| {
            let true_distance = self
                .working_shortest_distance(true_target, *id, graph)
                .unwrap_or(usize::MAX);
            let false_distance = self
                .working_shortest_distance(false_target, *id, graph)
                .unwrap_or(usize::MAX);
            (
                true_distance.max(false_distance),
                true_distance.saturating_add(false_distance),
                graph.node_entry(*id).unwrap_or(u64::MAX),
            )
        });
        common.into_iter().next()
    }

    fn find_working_switch_merge(&self, targets: &[usize], graph: &WorkingGraph) -> Option<usize> {
        if targets.is_empty() {
            return None;
        }
        let mut reachable_sets: Vec<HashSet<usize>> = Vec::new();
        for target in targets {
            let mut reachable = HashSet::new();
            graph.collect_reachable_limited(*target, &mut reachable, 10);
            reachable_sets.push(reachable);
        }
        let first = reachable_sets.first()?;
        let common: HashSet<usize> = first
            .iter()
            .copied()
            .filter(|id| reachable_sets.iter().all(|s| s.contains(id)))
            .collect();
        common
            .into_iter()
            .min_by_key(|id| graph.node_entry(*id).unwrap_or(u64::MAX))
    }

    fn working_shortest_distance(
        &self,
        start: usize,
        target: usize,
        graph: &WorkingGraph,
    ) -> Option<usize> {
        if start == target {
            return Some(0);
        }

        let mut queue = VecDeque::from([(start, 0usize)]);
        let mut visited = HashSet::from([start]);

        while let Some((node, dist)) = queue.pop_front() {
            for succ in graph.sorted_succs(node) {
                if !visited.insert(succ) {
                    continue;
                }
                if succ == target {
                    return Some(dist + 1);
                }
                queue.push_back((succ, dist + 1));
            }
        }

        None
    }
}

#[derive(Debug, Clone)]
struct LoopInfo {
    header: u64,
    body: HashSet<u64>,
    depth: usize,
}

#[derive(Debug, Clone)]
struct WorkingNode {
    entry: u64,
    blocks: BTreeSet<u64>,
    region: Region,
}

#[derive(Debug, Clone)]
struct WorkingGraph {
    nodes: HashMap<usize, WorkingNode>,
    preds: HashMap<usize, HashSet<usize>>,
    succs: HashMap<usize, HashSet<usize>>,
    edge_labels: HashMap<(usize, usize), CFGEdge>,
    block_to_node: HashMap<u64, usize>,
    next_id: usize,
}

impl WorkingGraph {
    fn from_function(func: &SSAFunction) -> Self {
        let mut nodes = HashMap::new();
        let mut preds: HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut succs: HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut edge_labels: HashMap<(usize, usize), CFGEdge> = HashMap::new();
        let mut block_to_node = HashMap::new();

        let mut blocks = func.block_addrs().to_vec();
        blocks.sort_unstable();
        for (idx, block) in blocks.iter().enumerate() {
            nodes.insert(
                idx,
                WorkingNode {
                    entry: *block,
                    blocks: BTreeSet::from([*block]),
                    region: Region::Block(*block),
                },
            );
            preds.insert(idx, HashSet::new());
            succs.insert(idx, HashSet::new());
            block_to_node.insert(*block, idx);
        }

        for block in blocks {
            let Some(from) = block_to_node.get(&block).copied() else {
                continue;
            };
            for succ_block in func.successors(block) {
                let Some(to) = block_to_node.get(&succ_block).copied() else {
                    continue;
                };
                succs.entry(from).or_default().insert(to);
                preds.entry(to).or_default().insert(from);
                if let Some(edge_type) = func.edge_type(block, succ_block) {
                    edge_labels.insert((from, to), edge_type);
                }
            }
        }

        Self {
            next_id: nodes.len(),
            nodes,
            preds,
            succs,
            edge_labels,
            block_to_node,
        }
    }

    fn node_for_block(&self, block: u64) -> Option<usize> {
        self.block_to_node.get(&block).copied()
    }

    fn node_region(&self, node: usize) -> Option<Region> {
        self.nodes.get(&node).map(|n| n.region.clone())
    }

    fn node_entry(&self, node: usize) -> Option<u64> {
        self.nodes.get(&node).map(|n| n.entry)
    }

    fn node_blocks(&self, node: usize) -> Vec<u64> {
        self.nodes
            .get(&node)
            .map(|n| n.blocks.iter().copied().collect())
            .unwrap_or_default()
    }

    fn sorted_succs(&self, node: usize) -> Vec<usize> {
        let mut out: Vec<usize> = self
            .succs
            .get(&node)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .collect();
        out.sort_by_key(|id| self.node_entry(*id).unwrap_or(u64::MAX));
        out
    }

    fn conditional_succs(&self, node: usize) -> Option<(usize, usize)> {
        let succs = self.sorted_succs(node);
        if succs.len() != 2 {
            return None;
        }

        let mut true_succ = None;
        let mut false_succ = None;
        for succ in succs {
            match self.edge_labels.get(&(node, succ)) {
                Some(CFGEdge::True) => true_succ = Some(succ),
                Some(CFGEdge::False) => false_succ = Some(succ),
                _ => {}
            }
        }

        Some((true_succ?, false_succ?))
    }

    fn preds_len(&self, node: usize) -> usize {
        self.preds.get(&node).map_or(0, HashSet::len)
    }

    fn remove_edge(&mut self, from: usize, to: usize) {
        if let Some(succs) = self.succs.get_mut(&from) {
            succs.remove(&to);
        }
        if let Some(preds) = self.preds.get_mut(&to) {
            preds.remove(&from);
        }
        self.edge_labels.remove(&(from, to));
    }

    fn collect_reachable_limited(
        &self,
        start: usize,
        reachable: &mut HashSet<usize>,
        depth: usize,
    ) {
        let mut queue = VecDeque::new();
        queue.push_back((start, depth));
        while let Some((node, d)) = queue.pop_front() {
            if d == 0 || !reachable.insert(node) {
                continue;
            }
            for succ in self.sorted_succs(node) {
                queue.push_back((succ, d.saturating_sub(1)));
            }
        }
    }

    /// Kahn's algorithm: returns nodes in topological order, or None if cyclic.
    fn topological_order(&self) -> Option<Vec<usize>> {
        let mut indegree: HashMap<usize, usize> = self
            .nodes
            .keys()
            .map(|id| (*id, self.preds.get(id).map_or(0, HashSet::len)))
            .collect();
        let mut queue: VecDeque<usize> = indegree
            .iter()
            .filter_map(|(id, deg)| (*deg == 0).then_some(*id))
            .collect();
        let mut order = Vec::with_capacity(self.nodes.len());
        while let Some(node) = queue.pop_front() {
            order.push(node);
            for succ in self.sorted_succs(node) {
                if let Some(deg) = indegree.get_mut(&succ) {
                    *deg = deg.saturating_sub(1);
                    if *deg == 0 {
                        queue.push_back(succ);
                    }
                }
            }
        }
        if order.len() == self.nodes.len() {
            Some(order)
        } else {
            None
        }
    }

    fn collapse_loop(
        &mut self,
        analyzer: &mut RegionAnalyzer<'_>,
        loop_info: &LoopInfo,
        all_loops: &[LoopInfo],
    ) -> Result<(), ()> {
        let header = loop_info.header;
        let body = &loop_info.body;
        let Some(header_node) = self.node_for_block(header) else {
            return Ok(());
        };

        let mut internal_nodes = HashSet::new();
        let mut partial_overlap = false;
        for (node_id, node) in &self.nodes {
            let in_count = node.blocks.iter().filter(|b| body.contains(b)).count();
            if in_count == 0 {
                continue;
            }
            if in_count != node.blocks.len() {
                partial_overlap = true;
                break;
            }
            internal_nodes.insert(*node_id);
        }
        if partial_overlap || !internal_nodes.contains(&header_node) {
            analyzer.analysis_reason =
                Some("iterative loop collapse encountered partial overlap".to_string());
            return Err(());
        }

        let absorbed_terminal_exit_nodes =
            self.terminal_return_exit_nodes(analyzer, &internal_nodes);
        let absorbed_terminal_exit_blocks = absorbed_terminal_exit_nodes
            .iter()
            .flat_map(|node_id| self.node_blocks(*node_id))
            .collect::<HashSet<_>>();
        internal_nodes.extend(absorbed_terminal_exit_nodes);

        let mut external_preds = HashSet::new();
        let mut external_succs = HashSet::new();

        for node in &internal_nodes {
            if let Some(preds) = self.preds.get(node) {
                for pred in preds {
                    if !internal_nodes.contains(pred) {
                        external_preds.insert(*pred);
                    }
                }
            }
            if let Some(succs) = self.succs.get(node) {
                for succ in succs {
                    if !internal_nodes.contains(succ) {
                        external_succs.insert(*succ);
                    }
                }
            }
        }

        let mut incoming_edge_labels = Vec::new();
        for pred in &external_preds {
            let labels = internal_nodes
                .iter()
                .filter_map(|internal| self.edge_labels.get(&(*pred, *internal)).copied())
                .collect::<Vec<_>>();
            if let Some(first) = labels.first().copied()
                && labels.iter().all(|label| *label == first)
            {
                incoming_edge_labels.push((*pred, first));
            }
        }
        let mut outgoing_edge_labels = Vec::new();
        for succ in &external_succs {
            let labels = internal_nodes
                .iter()
                .filter_map(|internal| self.edge_labels.get(&(*internal, *succ)).copied())
                .collect::<Vec<_>>();
            if let Some(first) = labels.first().copied()
                && labels.iter().all(|label| *label == first)
            {
                outgoing_edge_labels.push((*succ, first));
            }
        }

        // Classify edges leaving the loop body.
        //
        // - Continue: back-edge to this loop's header (from non-header block)
        // - Break (loop_exit): edge leaving this loop body, normal exit
        // - Goto: edge that targets a block inside a *different* loop's body
        //   (cross-nesting jump), excluding our own enclosing loops' headers
        //   which would be outer-loop continues.
        for block in body {
            for succ in analyzer.func.successors(*block) {
                // Continue: back to this loop header
                if succ == header && *block != header {
                    analyzer.loop_continues.insert(*block, header);
                    continue;
                }
                // Internal edge
                if body.contains(&succ) {
                    continue;
                }
                if absorbed_terminal_exit_blocks.contains(&succ) {
                    if analyzer
                        .loop_exits
                        .get(block)
                        .is_some_and(|existing| *existing == succ)
                    {
                        analyzer.loop_exits.remove(block);
                    }
                    continue;
                }
                // Already recorded as exit with same target — skip
                if analyzer
                    .loop_exits
                    .get(block)
                    .is_some_and(|existing| *existing == succ)
                {
                    continue;
                }

                // Determine whether this is a cross-nesting goto or a normal break.
                // A goto targets a block that is inside a *sibling* or *unrelated*
                // loop body (not our body, not an enclosing loop's body).
                let is_cross_nesting = Self::is_cross_nesting_target(succ, header, body, all_loops);

                if is_cross_nesting {
                    analyzer.loop_gotos.insert(*block, succ);
                } else {
                    // Normal break.  If this block already has a loop_exit recorded
                    // (multi-exit conditional), keep the first and ignore the rest —
                    // both are normal breaks, not gotos.
                    if !analyzer.loop_exits.contains_key(block) {
                        analyzer.loop_exits.insert(*block, succ);
                    }
                }
            }
        }

        let loop_region = self.make_loop_region(
            analyzer,
            loop_info,
            &internal_nodes,
            &absorbed_terminal_exit_blocks,
        );
        let mut collapsed_blocks = BTreeSet::new();
        for node_id in &internal_nodes {
            if let Some(node) = self.nodes.get(node_id) {
                collapsed_blocks.extend(node.blocks.iter().copied());
            }
        }

        let next_available = self
            .nodes
            .keys()
            .copied()
            .max()
            .map(|id| id.saturating_add(1))
            .unwrap_or(0);
        let new_id = self.next_id.max(next_available);
        self.next_id = new_id.saturating_add(1);
        self.nodes.insert(
            new_id,
            WorkingNode {
                entry: header,
                blocks: collapsed_blocks.clone(),
                region: loop_region,
            },
        );
        self.preds.insert(new_id, external_preds.clone());
        self.succs.insert(new_id, external_succs.clone());

        for pred in &external_preds {
            if let Some(succs) = self.succs.get_mut(pred) {
                succs.retain(|id| !internal_nodes.contains(id));
                succs.insert(new_id);
            }
        }
        for succ in &external_succs {
            if let Some(preds) = self.preds.get_mut(succ) {
                preds.retain(|id| !internal_nodes.contains(id));
                preds.insert(new_id);
            }
        }

        self.edge_labels
            .retain(|(from, to), _| !internal_nodes.contains(from) && !internal_nodes.contains(to));
        for (pred, label) in incoming_edge_labels {
            self.edge_labels.insert((pred, new_id), label);
        }
        for (succ, label) in outgoing_edge_labels {
            self.edge_labels.insert((new_id, succ), label);
        }

        for node_id in &internal_nodes {
            self.nodes.remove(node_id);
            self.preds.remove(node_id);
            self.succs.remove(node_id);
        }
        for block in collapsed_blocks {
            self.block_to_node.insert(block, new_id);
        }

        Ok(())
    }

    /// Determine whether `target` is a cross-nesting jump target.
    ///
    /// A target is cross-nesting if it is inside some other loop's body that
    /// does NOT enclose our current loop (i.e. it's a sibling or unrelated loop).
    /// Targets that are simply outside the current loop body (normal breaks)
    /// or inside an enclosing loop's body are NOT cross-nesting.
    fn is_cross_nesting_target(
        target: u64,
        current_header: u64,
        current_body: &HashSet<u64>,
        all_loops: &[LoopInfo],
    ) -> bool {
        for other in all_loops {
            // Skip our own loop
            if other.header == current_header && other.body == *current_body {
                continue;
            }
            // Skip enclosing loops (they contain our header)
            if other.body.contains(&current_header) && current_body.is_subset(&other.body) {
                continue;
            }
            // If the target is inside a sibling/unrelated loop's body, it's cross-nesting
            if other.body.contains(&target) {
                return true;
            }
        }
        false
    }

    fn terminal_return_exit_nodes(
        &self,
        analyzer: &RegionAnalyzer<'_>,
        internal_nodes: &HashSet<usize>,
    ) -> HashSet<usize> {
        let mut out = HashSet::new();
        for node in internal_nodes {
            for succ in self.sorted_succs(*node) {
                if internal_nodes.contains(&succ) || out.contains(&succ) {
                    continue;
                }
                if let Some(chain) = self.terminal_return_exit_chain(analyzer, succ, internal_nodes)
                {
                    out.extend(chain);
                }
            }
        }
        out
    }

    fn terminal_return_exit_chain(
        &self,
        analyzer: &RegionAnalyzer<'_>,
        start: usize,
        internal_nodes: &HashSet<usize>,
    ) -> Option<HashSet<usize>> {
        let mut chain = HashSet::new();
        let mut current = start;

        loop {
            if internal_nodes.contains(&current) || !self.nodes.contains_key(&current) {
                return None;
            }
            if !self.preds.get(&current).is_some_and(|preds| {
                preds
                    .iter()
                    .all(|pred| internal_nodes.contains(pred) || chain.contains(pred))
            }) {
                return None;
            }
            if !chain.insert(current) {
                return None;
            }
            if self.node_is_terminal_return(analyzer, current) {
                return Some(chain);
            }

            let succs = self.sorted_succs(current);
            if succs.len() != 1 {
                return None;
            }
            current = succs[0];
        }
    }

    fn node_is_terminal_return(&self, analyzer: &RegionAnalyzer<'_>, node: usize) -> bool {
        let Some(node_data) = self.nodes.get(&node) else {
            return false;
        };
        if !self.sorted_succs(node).is_empty() || node_data.blocks.len() != 1 {
            return false;
        }
        let Some(block) = node_data.blocks.iter().next().copied() else {
            return false;
        };
        analyzer
            .func
            .cfg()
            .get_block(block)
            .is_some_and(|cfg_block| matches!(cfg_block.terminator, BlockTerminator::Return))
    }

    fn make_loop_region(
        &self,
        analyzer: &mut RegionAnalyzer<'_>,
        loop_info: &LoopInfo,
        internal_nodes: &HashSet<usize>,
        absorbed_terminal_exit_blocks: &HashSet<u64>,
    ) -> Region {
        let header = loop_info.header;
        let body = &loop_info.body;
        let mut region_body = body.clone();
        region_body.extend(absorbed_terminal_exit_blocks.iter().copied());
        if let Some(body_entry) = analyzer.pretest_loop_body_entry(header, body) {
            let mut body_blocks = region_body.clone();
            body_blocks.remove(&header);
            let loop_body = self.make_loop_body_region(
                analyzer,
                internal_nodes,
                &body_blocks,
                Some(body_entry),
                header,
            );
            return Region::WhileLoop {
                header,
                body: Box::new(loop_body),
            };
        }

        if let Some((guard_block, body_entry)) = analyzer.find_precheck_guard(header, body) {
            let mut body_blocks = region_body.clone();
            body_blocks.remove(&guard_block);
            if header != guard_block && analyzer.func.successors(header).len() == 1 {
                body_blocks.remove(&header);
            }
            let loop_body = self.make_loop_body_region(
                analyzer,
                internal_nodes,
                &body_blocks,
                Some(body_entry),
                header,
            );
            return Region::WhileLoop {
                header: guard_block,
                body: Box::new(loop_body),
            };
        }

        let cond_block = analyzer
            .unique_loop_latch_condition_block(header, body)
            .unwrap_or(header);
        let loop_body = self.make_loop_body_region(
            analyzer,
            internal_nodes,
            &region_body,
            Some(header),
            header,
        );
        Region::DoWhileLoop {
            body: Box::new(loop_body),
            cond_block,
        }
    }

    fn make_loop_body_region(
        &self,
        analyzer: &mut RegionAnalyzer<'_>,
        internal_nodes: &HashSet<usize>,
        body_blocks: &HashSet<u64>,
        start_block: Option<u64>,
        loop_header: u64,
    ) -> Region {
        if body_blocks.is_empty() {
            return Region::Sequence(Vec::new());
        }

        let relevant_nodes: HashSet<usize> = internal_nodes
            .iter()
            .copied()
            .filter(|node_id| {
                self.nodes
                    .get(node_id)
                    .map(|node| node.blocks.iter().all(|b| body_blocks.contains(b)))
                    .unwrap_or(false)
            })
            .collect();

        if relevant_nodes.is_empty() {
            return Region::Sequence(Vec::new());
        }

        // Build a subgraph of just the relevant body nodes. A loop region owns
        // its natural backedges, so its body represents one iteration and must
        // be analyzed without those edges. Keeping them here makes the body
        // cyclic and forces the flat DFS fallback, which erases conditional
        // continue regions.
        let mut sub = self.subgraph(&relevant_nodes);
        if let Some(header_node) = sub.node_for_block(loop_header) {
            for source in analyzer.back_edges.get(&loop_header).into_iter().flatten() {
                if let Some(source_node) = sub.node_for_block(*source) {
                    sub.remove_edge(source_node, header_node);
                }
            }
        }

        // Try structured composition via topological ordering.
        let entry = start_block.and_then(|b| sub.node_for_block(b));
        if let Some(entry_id) = entry
            && let Some(topo) = sub.topological_order()
        {
            return analyzer.analyze_post_collapse_iterative(entry_id, &sub, &topo);
        }

        // Fallback: flat sequence ordered by DFS.
        let mut ordered = Vec::new();
        let mut seen = HashSet::new();
        if let Some(start_block) = start_block
            && let Some(start_node) = self.node_for_block(start_block)
            && relevant_nodes.contains(&start_node)
        {
            let mut stack = vec![start_node];
            while let Some(node) = stack.pop() {
                if !seen.insert(node) {
                    continue;
                }
                ordered.push(node);
                let mut succs = self.sorted_succs(node);
                succs.retain(|id| relevant_nodes.contains(id));
                succs.reverse();
                stack.extend(succs);
            }
        }

        let mut leftovers: Vec<usize> = relevant_nodes
            .iter()
            .copied()
            .filter(|id| !seen.contains(id))
            .collect();
        leftovers.sort_by_key(|id| self.node_entry(*id).unwrap_or(u64::MAX));
        ordered.extend(leftovers);

        let mut regions = Vec::new();
        for node_id in ordered {
            if let Some(node) = self.nodes.get(&node_id) {
                regions.push(node.region.clone());
            }
        }

        match regions.len() {
            0 => Region::Sequence(Vec::new()),
            1 => regions.remove(0),
            _ => Region::Sequence(regions),
        }
    }

    /// Create a subgraph containing only the specified node IDs.
    /// Edges between included nodes are preserved; external edges are dropped.
    fn subgraph(&self, node_ids: &HashSet<usize>) -> WorkingGraph {
        let mut nodes = HashMap::new();
        let mut preds: HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut succs: HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut edge_labels: HashMap<(usize, usize), CFGEdge> = HashMap::new();
        let mut block_to_node = HashMap::new();

        for &id in node_ids {
            if let Some(node) = self.nodes.get(&id) {
                nodes.insert(id, node.clone());
                for b in &node.blocks {
                    block_to_node.insert(*b, id);
                }
            }
            // Filter edges to only include nodes within the subgraph.
            let pred_set: HashSet<usize> = self
                .preds
                .get(&id)
                .map(|p| {
                    p.iter()
                        .copied()
                        .filter(|pid| node_ids.contains(pid))
                        .collect()
                })
                .unwrap_or_default();
            preds.insert(id, pred_set);
            let succ_set: HashSet<usize> = self
                .succs
                .get(&id)
                .map(|s| {
                    s.iter()
                        .copied()
                        .filter(|sid| node_ids.contains(sid))
                        .collect()
                })
                .unwrap_or_default();
            succs.insert(id, succ_set);
        }
        for (&(from, to), edge) in &self.edge_labels {
            if node_ids.contains(&from) && node_ids.contains(&to) {
                edge_labels.insert((from, to), *edge);
            }
        }

        WorkingGraph {
            next_id: self.next_id,
            nodes,
            preds,
            succs,
            edge_labels,
            block_to_node,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::CStmt;
    use crate::fold::FoldingContext;
    use crate::structure::ControlFlowStructurer;
    use r2il::{R2ILBlock, R2ILOp, Varnode};
    use r2ssa::{BlockTerminator, SSAFunction};

    // Note: Full tests would require constructing SSAFunctions
    // which requires r2il blocks. These are placeholder tests.

    #[test]
    fn test_region_entry() {
        let region = Region::Block(0x1000);
        assert_eq!(region.entry(), 0x1000);
    }

    #[test]
    fn test_region_blocks() {
        let region = Region::Sequence(vec![
            Region::Block(0x1000),
            Region::Block(0x1004),
            Region::Block(0x1008),
        ]);
        let blocks = region.blocks();
        assert_eq!(blocks, vec![0x1000, 0x1004, 0x1008]);
    }

    #[test]
    fn test_if_then_else_blocks() {
        let region = Region::IfThenElse {
            cond_block: 0x1000,
            then_region: Box::new(Region::Block(0x1004)),
            else_region: Some(Box::new(Region::Block(0x1008))),
            merge_block: Some(0x100c),
        };
        let blocks = region.blocks();
        assert!(blocks.contains(&0x1000));
        assert!(blocks.contains(&0x1004));
        assert!(blocks.contains(&0x1008));
        assert!(blocks.contains(&0x100c));
    }

    #[test]
    fn recursive_guard_returns_irreducible_on_limit() {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Branch {
            target: Varnode::constant(0x1000, 8),
        });
        let func = SSAFunction::from_blocks(&[block]).expect("ssa function");
        let mut analyzer = RegionAnalyzer::new(&func);
        analyzer.recursion_depth_limit = 0;

        let region = analyzer.analyze_region_recursive(func.entry);
        assert!(
            matches!(region, Region::Irreducible { .. }),
            "recursive guard should degrade to irreducible region"
        );
        assert!(
            analyzer.analysis_reason().is_some(),
            "recursive guard should set analysis reason"
        );
    }

    fn build_diamond_cfg_with_reversed_address_order() -> SSAFunction {
        // Conditional at 0x1000:
        //   true  -> 0x2000
        //   false -> 0x1004 (fallthrough, lower address than true target)
        let mut b0 = R2ILBlock::new(0x1000, 4);
        b0.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x2000, 8),
        });

        let mut b_false = R2ILBlock::new(0x1004, 4);
        b_false.push(R2ILOp::Branch {
            target: Varnode::constant(0x3000, 8),
        });

        let mut b_true = R2ILBlock::new(0x2000, 4);
        b_true.push(R2ILOp::Branch {
            target: Varnode::constant(0x3000, 8),
        });

        let mut b_merge = R2ILBlock::new(0x3000, 4);
        b_merge.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        SSAFunction::from_blocks_raw_no_arch(&[b0, b_false, b_true, b_merge]).expect("ssa function")
    }

    #[test]
    fn recursive_conditional_targets_use_cfg_edge_polarity() {
        let func = build_diamond_cfg_with_reversed_address_order();
        let mut analyzer = RegionAnalyzer::new(&func);

        assert_eq!(
            analyzer.resolve_conditional_targets(0x1000),
            Some((0x2000, 0x1004)),
            "true/false targets should follow CFG edge labels, not successor ordering"
        );

        let region = analyzer.analyze_region_recursive(func.entry);
        let Region::IfThenElse {
            then_region,
            else_region,
            ..
        } = region
        else {
            panic!("expected top-level IfThenElse region");
        };

        assert_eq!(
            then_region.entry(),
            0x2000,
            "then branch should be true-target"
        );
        assert_eq!(
            else_region.as_ref().map(|r| r.entry()),
            Some(0x1004),
            "else branch should be false-target"
        );
    }

    #[test]
    fn iterative_composition_uses_working_graph_edge_polarity() {
        let func = build_diamond_cfg_with_reversed_address_order();
        let mut analyzer = RegionAnalyzer::new(&func);
        let graph = WorkingGraph::from_function(&func);

        let entry_node = graph
            .node_for_block(func.entry)
            .expect("entry node should exist");
        let sorted_succs = graph.sorted_succs(entry_node);
        let sorted_entries: Vec<u64> = sorted_succs
            .iter()
            .map(|id| graph.node_entry(*id).expect("node entry"))
            .collect();
        assert_eq!(
            sorted_entries,
            vec![0x1004, 0x2000],
            "sorted successor order should be address-based and opposite of true/false"
        );

        let (true_node, false_node) = graph
            .conditional_succs(entry_node)
            .expect("conditional edge labels should be available");
        assert_eq!(
            graph.node_entry(true_node),
            Some(0x2000),
            "true successor should be decoded from CFGEdge::True"
        );
        assert_eq!(
            graph.node_entry(false_node),
            Some(0x1004),
            "false successor should be decoded from CFGEdge::False"
        );

        let topo = graph.topological_order().expect("graph should be acyclic");
        let region = analyzer.analyze_post_collapse_iterative(entry_node, &graph, &topo);
        let Region::IfThenElse {
            then_region,
            else_region,
            ..
        } = region
        else {
            panic!("expected top-level IfThenElse region");
        };

        assert_eq!(
            then_region.entry(),
            0x2000,
            "then branch should be true-target"
        );
        assert_eq!(
            else_region.as_ref().map(|r| r.entry()),
            Some(0x1004),
            "else branch should be false-target"
        );
    }

    fn build_latch_condition_loop_cfg() -> SSAFunction {
        let mut header = R2ILBlock::new(0x1010, 4);
        header.push(R2ILOp::Branch {
            target: Varnode::constant(0x1020, 8),
        });

        let mut latch = R2ILBlock::new(0x1020, 4);
        latch.push(R2ILOp::CBranch {
            cond: Varnode::register(0x200, 1),
            target: Varnode::constant(0x1010, 8),
        });

        let mut exit = R2ILBlock::new(0x1030, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func =
            SSAFunction::from_blocks_raw_no_arch(&[header, latch, exit]).expect("ssa function");
        func.cfg_mut()
            .set_terminator(0x1010, BlockTerminator::Branch { target: 0x1020 });
        func.cfg_mut().set_terminator(
            0x1020,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1010,
                false_target: 0x1030,
            },
        );
        func.refresh_after_cfg_mutation();
        func
    }

    fn build_conditional_self_loop_cfg() -> SSAFunction {
        let mut preheader = R2ILBlock::new(0x1000, 4);
        preheader.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });

        let mut loop_block = R2ILBlock::new(0x1010, 4);
        loop_block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0x208, 8),
            a: Varnode::register(0x208, 8),
            b: Varnode::constant(1, 8),
        });
        loop_block.push(R2ILOp::CBranch {
            cond: Varnode::register(0x200, 1),
            target: Varnode::constant(0x1010, 8),
        });

        let mut exit = R2ILBlock::new(0x1020, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[preheader, loop_block, exit])
            .expect("ssa function");
        func.cfg_mut()
            .set_terminator(0x1000, BlockTerminator::Branch { target: 0x1010 });
        func.cfg_mut().set_terminator(
            0x1010,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1010,
                false_target: 0x1020,
            },
        );
        func.refresh_after_cfg_mutation();
        func
    }

    fn build_guarded_latch_condition_loop_cfg() -> SSAFunction {
        let mut entry = R2ILBlock::new(0x1000, 0x10);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::register(0x200, 1),
            target: Varnode::constant(0x1040, 8),
        });

        let mut preheader = R2ILBlock::new(0x1010, 0x10);
        preheader.push(R2ILOp::Branch {
            target: Varnode::constant(0x1020, 8),
        });

        let mut header = R2ILBlock::new(0x1020, 0x10);
        header.push(R2ILOp::Branch {
            target: Varnode::constant(0x1030, 8),
        });

        let mut latch = R2ILBlock::new(0x1030, 0x10);
        latch.push(R2ILOp::CBranch {
            cond: Varnode::register(0x206, 1),
            target: Varnode::constant(0x1020, 8),
        });

        let mut exit = R2ILBlock::new(0x1040, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func =
            SSAFunction::from_blocks_raw_no_arch(&[entry, preheader, header, latch, exit])
                .expect("ssa function");
        func.cfg_mut().set_terminator(
            0x1000,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1040,
                false_target: 0x1010,
            },
        );
        func.cfg_mut()
            .set_terminator(0x1010, BlockTerminator::Branch { target: 0x1020 });
        func.cfg_mut()
            .set_terminator(0x1020, BlockTerminator::Branch { target: 0x1030 });
        func.cfg_mut().set_terminator(
            0x1030,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1020,
                false_target: 0x1040,
            },
        );
        func.refresh_after_cfg_mutation();
        func
    }

    fn build_table_walk_like_cfg() -> SSAFunction {
        let addrs = [
            0x401490, 0x401499, 0x40149e, 0x4014a0, 0x4014a9, 0x4014b9, 0x4014c6, 0x4014cf,
            0x4014d2, 0x4014d8, 0x4014de, 0x4014e7, 0x4014ef, 0x4014f4, 0x4014fa, 0x401500,
            0x401505, 0x401508, 0x40150e, 0x401510,
        ];
        let blocks = addrs
            .into_iter()
            .map(|addr| {
                let mut block = R2ILBlock::new(addr, 4);
                block.push(R2ILOp::Nop);
                block
            })
            .collect::<Vec<_>>();
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");

        func.cfg_mut().set_terminator(
            0x401490,
            BlockTerminator::ConditionalBranch {
                true_target: 0x401510,
                false_target: 0x401499,
            },
        );
        func.cfg_mut()
            .set_terminator(0x401499, BlockTerminator::Branch { target: 0x4014a9 });
        func.cfg_mut()
            .set_terminator(0x40149e, BlockTerminator::Branch { target: 0x4014a0 });
        func.cfg_mut().set_terminator(
            0x4014a0,
            BlockTerminator::ConditionalBranch {
                true_target: 0x4014cf,
                false_target: 0x4014a9,
            },
        );
        func.cfg_mut().set_terminator(
            0x4014a9,
            BlockTerminator::ConditionalBranch {
                true_target: 0x4014a0,
                false_target: 0x4014b9,
            },
        );
        func.cfg_mut().set_terminator(
            0x4014b9,
            BlockTerminator::ConditionalBranch {
                true_target: 0x4014e7,
                false_target: 0x4014c6,
            },
        );
        func.cfg_mut().set_terminator(
            0x4014c6,
            BlockTerminator::ConditionalBranch {
                true_target: 0x4014a9,
                false_target: 0x4014cf,
            },
        );
        func.cfg_mut()
            .set_terminator(0x4014cf, BlockTerminator::Return);
        func.cfg_mut()
            .set_terminator(0x4014d2, BlockTerminator::Branch { target: 0x4014d8 });
        func.cfg_mut().set_terminator(
            0x4014d8,
            BlockTerminator::ConditionalBranch {
                true_target: 0x401500,
                false_target: 0x4014de,
            },
        );
        func.cfg_mut().set_terminator(
            0x4014de,
            BlockTerminator::ConditionalBranch {
                true_target: 0x401508,
                false_target: 0x4014e7,
            },
        );
        func.cfg_mut().set_terminator(
            0x4014e7,
            BlockTerminator::ConditionalBranch {
                true_target: 0x4014d8,
                false_target: 0x4014ef,
            },
        );
        func.cfg_mut().set_terminator(
            0x4014ef,
            BlockTerminator::ConditionalBranch {
                true_target: 0x4014a0,
                false_target: 0x4014f4,
            },
        );
        func.cfg_mut()
            .set_terminator(0x4014f4, BlockTerminator::Return);
        func.cfg_mut()
            .set_terminator(0x4014fa, BlockTerminator::Branch { target: 0x401500 });
        func.cfg_mut().set_terminator(
            0x401500,
            BlockTerminator::ConditionalBranch {
                true_target: 0x4014a0,
                false_target: 0x401505,
            },
        );
        func.cfg_mut()
            .set_terminator(0x401505, BlockTerminator::Branch { target: 0x401508 });
        func.cfg_mut().set_terminator(
            0x401508,
            BlockTerminator::ConditionalBranch {
                true_target: 0x4014a0,
                false_target: 0x40150e,
            },
        );
        func.cfg_mut()
            .set_terminator(0x40150e, BlockTerminator::Branch { target: 0x4014f4 });
        func.cfg_mut()
            .set_terminator(0x401510, BlockTerminator::Return);
        func.refresh_after_cfg_mutation();
        func
    }

    fn region_contains_dowhile_cond(region: &Region, expected: u64) -> bool {
        match region {
            Region::DoWhileLoop { body, cond_block } => {
                *cond_block == expected || region_contains_dowhile_cond(body, expected)
            }
            Region::WhileLoop { body, .. } => region_contains_dowhile_cond(body, expected),
            Region::MultiExit { head, .. } => region_contains_dowhile_cond(head, expected),
            Region::Sequence(regions) => regions
                .iter()
                .any(|region| region_contains_dowhile_cond(region, expected)),
            Region::IfThenElse {
                then_region,
                else_region,
                ..
            } => {
                region_contains_dowhile_cond(then_region, expected)
                    || else_region
                        .as_deref()
                        .is_some_and(|region| region_contains_dowhile_cond(region, expected))
            }
            Region::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|(_, region)| region_contains_dowhile_cond(region, expected))
                    || default
                        .as_deref()
                        .is_some_and(|region| region_contains_dowhile_cond(region, expected))
            }
            Region::Block(_) | Region::Irreducible { .. } => false,
        }
    }

    fn region_contains_loop_entry(region: &Region, expected: u64) -> bool {
        match region {
            Region::DoWhileLoop { body, .. } => {
                body.entry() == expected || region_contains_loop_entry(body, expected)
            }
            Region::WhileLoop { header, body } => {
                *header == expected || region_contains_loop_entry(body, expected)
            }
            Region::MultiExit { head, .. } => region_contains_loop_entry(head, expected),
            Region::Sequence(regions) => regions
                .iter()
                .any(|region| region_contains_loop_entry(region, expected)),
            Region::IfThenElse {
                then_region,
                else_region,
                ..
            } => {
                region_contains_loop_entry(then_region, expected)
                    || else_region
                        .as_deref()
                        .is_some_and(|region| region_contains_loop_entry(region, expected))
            }
            Region::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|(_, region)| region_contains_loop_entry(region, expected))
                    || default
                        .as_deref()
                        .is_some_and(|region| region_contains_loop_entry(region, expected))
            }
            Region::Block(_) | Region::Irreducible { .. } => false,
        }
    }

    fn region_contains_cond_block(region: &Region, expected: u64) -> bool {
        match region {
            Region::IfThenElse {
                cond_block,
                then_region,
                else_region,
                ..
            } => {
                *cond_block == expected
                    || region_contains_cond_block(then_region, expected)
                    || else_region
                        .as_deref()
                        .is_some_and(|region| region_contains_cond_block(region, expected))
            }
            Region::WhileLoop { body, .. } | Region::DoWhileLoop { body, .. } => {
                region_contains_cond_block(body, expected)
            }
            Region::MultiExit { head, .. } => region_contains_cond_block(head, expected),
            Region::Sequence(regions) => regions
                .iter()
                .any(|region| region_contains_cond_block(region, expected)),
            Region::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|(_, region)| region_contains_cond_block(region, expected))
                    || default
                        .as_deref()
                        .is_some_and(|region| region_contains_cond_block(region, expected))
            }
            Region::Block(_) | Region::Irreducible { .. } => false,
        }
    }

    fn region_contains_multi_exit(
        region: &Region,
        expected_entry: u64,
        expected_exits: &[u64],
    ) -> bool {
        match region {
            Region::MultiExit { head, exits } => {
                (head.entry() == expected_entry && exits == expected_exits)
                    || region_contains_multi_exit(head, expected_entry, expected_exits)
            }
            Region::WhileLoop { body, .. } | Region::DoWhileLoop { body, .. } => {
                region_contains_multi_exit(body, expected_entry, expected_exits)
            }
            Region::Sequence(regions) => regions
                .iter()
                .any(|region| region_contains_multi_exit(region, expected_entry, expected_exits)),
            Region::IfThenElse {
                then_region,
                else_region,
                ..
            } => {
                region_contains_multi_exit(then_region, expected_entry, expected_exits)
                    || else_region.as_deref().is_some_and(|region| {
                        region_contains_multi_exit(region, expected_entry, expected_exits)
                    })
            }
            Region::Switch { cases, default, .. } => {
                cases.iter().any(|(_, region)| {
                    region_contains_multi_exit(region, expected_entry, expected_exits)
                }) || default.as_deref().is_some_and(|region| {
                    region_contains_multi_exit(region, expected_entry, expected_exits)
                })
            }
            Region::Block(_) | Region::Irreducible { .. } => false,
        }
    }

    fn region_contains_irreducible_entry(region: &Region, expected: u64) -> bool {
        match region {
            Region::Irreducible { entry, .. } => *entry == expected,
            Region::WhileLoop { body, .. } | Region::DoWhileLoop { body, .. } => {
                region_contains_irreducible_entry(body, expected)
            }
            Region::MultiExit { head, .. } => region_contains_irreducible_entry(head, expected),
            Region::Sequence(regions) => regions
                .iter()
                .any(|region| region_contains_irreducible_entry(region, expected)),
            Region::IfThenElse {
                then_region,
                else_region,
                ..
            } => {
                region_contains_irreducible_entry(then_region, expected)
                    || else_region
                        .as_deref()
                        .is_some_and(|region| region_contains_irreducible_entry(region, expected))
            }
            Region::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|(_, region)| region_contains_irreducible_entry(region, expected))
                    || default
                        .as_deref()
                        .is_some_and(|region| region_contains_irreducible_entry(region, expected))
            }
            Region::Block(_) => false,
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

    #[test]
    fn iterative_loop_region_uses_unique_latch_condition_block() {
        let func = build_latch_condition_loop_cfg();
        let mut analyzer = RegionAnalyzer::new(&func);

        let region = analyzer.analyze();
        let Region::DoWhileLoop { cond_block, .. } = region else {
            panic!("expected latch-conditioned loop, got {region:?}");
        };

        assert_eq!(cond_block, 0x1020);
    }

    #[test]
    fn conditional_self_loop_keeps_header_effects_in_do_while_body() {
        let func = build_conditional_self_loop_cfg();
        let mut analyzer = RegionAnalyzer::new(&func);

        let region = analyzer.analyze();

        assert!(
            region_contains_dowhile_cond(&region, 0x1010),
            "self-edge latch must be a do-while condition: {region:?}"
        );
        assert!(
            region.blocks().contains(&0x1010),
            "self-loop header effects must remain in the loop body: {region:?}"
        );
        let direct = analyzer.analyze_loop(0x1010, &HashSet::from([0x1010]));
        assert!(
            matches!(
                direct,
                Region::DoWhileLoop {
                    ref body,
                    cond_block: 0x1010
                } if body.blocks() == vec![0x1010]
            ),
            "recursive fallback must preserve the self-loop header body: {direct:?}"
        );
    }

    #[test]
    fn iterative_guarded_loop_preserves_latch_condition_region() {
        let func = build_guarded_latch_condition_loop_cfg();
        assert_eq!(func.successors(0x1000), vec![0x1040, 0x1010]);
        assert_eq!(func.successors(0x1010), vec![0x1020]);
        assert_eq!(func.successors(0x1020), vec![0x1030]);
        assert_eq!(func.successors(0x1030), vec![0x1020, 0x1040]);
        let mut analyzer = RegionAnalyzer::new(&func);

        let region = analyzer.analyze();
        assert!(
            matches!(
                region,
                Region::IfThenElse { .. } | Region::Sequence(_) | Region::DoWhileLoop { .. }
            ),
            "region should stay structured enough to inspect, got {region:?}"
        );
        assert!(
            region.blocks().contains(&0x1030),
            "latch block must stay in the structured region, got {region:?}; loops={:?}",
            analyzer.loops
        );
        assert!(
            region_contains_dowhile_cond(&region, 0x1030),
            "loop condition should be anchored at latch 0x1030, got {region:?}"
        );
    }

    #[test]
    fn table_walk_like_cfg_recovers_dominator_backed_loop_regions() {
        let func = build_table_walk_like_cfg();
        let mut analyzer = RegionAnalyzer::new(&func);

        let outer = analyzer
            .get_loop_body(0x4014a9)
            .expect("outer table loop should be recognized from dominance");
        assert!(outer.contains(&0x4014a0));
        assert!(outer.contains(&0x4014c6));

        let inner = analyzer
            .get_loop_body(0x4014e7)
            .expect("inner string loop should be recognized from dominance");
        assert!(inner.contains(&0x4014d8));
        assert!(inner.contains(&0x4014de));

        let mut recursive_analyzer = RegionAnalyzer::new(&func);
        let direct = recursive_analyzer.analyze_region_recursive(0x4014a9);
        assert!(
            matches!(
                direct,
                Region::WhileLoop { .. } | Region::DoWhileLoop { .. }
            ),
            "direct loop analysis should recover the table loop, got {direct:?}"
        );

        let region = analyzer.analyze();
        assert!(
            !region_contains_irreducible_entry(&region, 0x4014a9),
            "table-walk loop header must not degrade to an irreducible island: {region:?}; loops={:?}; reason={:?}",
            analyzer.loops,
            analyzer.analysis_reason()
        );
        assert!(
            region_contains_loop_entry(&region, 0x4014a9),
            "outer table-walk natural loop must survive in the region tree: {region:?}"
        );
        assert!(
            region_contains_loop_entry(&region, 0x4014e7),
            "inner string-match natural loop must survive in the region tree: {region:?}"
        );
        assert!(
            region_contains_cond_block(&region, 0x4014a9)
                && region_contains_cond_block(&region, 0x4014b9),
            "outer-loop continue guards must survive body analysis: {region:?}"
        );
        assert!(
            region_contains_multi_exit(&region, 0x4014e7, &[0x4014ef, 0x401500, 0x401508]),
            "inner loop must retain every exact external continuation: {region:?}"
        );

        let ctx = FoldingContext::new(64);
        let mut structurer = ControlFlowStructurer::new(&func, &ctx);
        let rendered = structurer.structure();
        let proof_anchors = structurer
            .control_render_proofs()
            .iter()
            .map(|proof| proof.anchor)
            .collect::<BTreeSet<_>>();
        assert!(
            proof_anchors.is_empty(),
            "predicate-less fixture must not mint loop render proofs, got {proof_anchors:x?}"
        );
        assert!(
            stmt_contains_comment(&rendered, "r2dec residual: unresolved"),
            "predicate-less fixture should residualize unresolved control, got {rendered:?}"
        );
    }

    #[test]
    fn iterative_composition_refuses_unknown_multiway_cases_instead_of_numbering_them() {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Nop);
        entry.set_switch_info(r2il::SwitchInfo {
            switch_addr: 0x1000,
            min_val: 10,
            max_val: 30,
            default_target: None,
            cases: vec![
                r2il::SwitchCase {
                    value: 10,
                    target: 0x1010,
                },
                r2il::SwitchCase {
                    value: 20,
                    target: 0x1020,
                },
                r2il::SwitchCase {
                    value: 30,
                    target: 0x1030,
                },
            ],
        });
        let mut case0 = R2ILBlock::new(0x1010, 4);
        case0.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case1 = R2ILBlock::new(0x1020, 4);
        case1.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case2 = R2ILBlock::new(0x1030, 4);
        case2.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[entry, case0, case1, case2])
            .expect("ssa function");
        let graph = WorkingGraph::from_function(&func);
        func.cfg_mut().set_terminator(0x1000, BlockTerminator::None);

        let mut analyzer = RegionAnalyzer::new(&func);
        let entry_node = graph.node_for_block(0x1000).expect("entry node");
        assert_eq!(graph.sorted_succs(entry_node).len(), 3);
        let topo = graph.topological_order().expect("manual graph is acyclic");

        let region = analyzer.analyze_post_collapse_iterative(entry_node, &graph, &topo);

        let Region::Irreducible { entry, blocks } = region else {
            panic!("unknown multiway control must residualize instead of rendering a fake switch");
        };
        assert_eq!(entry, 0x1000);
        assert_eq!(blocks, vec![0x1000, 0x1010, 0x1020, 0x1030]);
        assert!(
            analyzer
                .analysis_reason()
                .is_some_and(|reason| reason.contains("no canonical case values")),
            "unknown multiway residual should keep an explicit analysis reason"
        );
    }

    fn build_single_arm_guard_cfg() -> SSAFunction {
        // Conditional at 0x1000:
        //   true  -> 0x2000 (immediate merge)
        //   false -> 0x1004 (body), which also flows to 0x2000
        let mut cond = R2ILBlock::new(0x1000, 4);
        cond.push(R2ILOp::Nop);

        let mut body = R2ILBlock::new(0x1004, 4);
        body.push(R2ILOp::Branch {
            target: Varnode::constant(0x2000, 8),
        });

        let mut merge = R2ILBlock::new(0x2000, 4);
        merge.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func =
            SSAFunction::from_blocks_raw_no_arch(&[cond, body, merge]).expect("ssa function");
        func.cfg_mut().set_terminator(
            0x1000,
            BlockTerminator::ConditionalBranch {
                true_target: 0x2000,
                false_target: 0x1004,
            },
        );
        func
    }

    #[test]
    fn iterative_composition_prefers_near_single_arm_merge() {
        let func = build_single_arm_guard_cfg();
        let analyzer = RegionAnalyzer::new(&func);
        let graph = WorkingGraph::from_function(&func);
        let false_node = graph
            .node_for_block(0x1004)
            .expect("body node should exist");
        let true_node = graph
            .node_for_block(0x2000)
            .expect("merge node should exist");
        let merge_node = analyzer
            .find_working_merge_point(true_node, false_node, &graph)
            .expect("merge node should be found");
        assert_eq!(
            graph.node_entry(merge_node),
            Some(0x2000),
            "iterative merge selection should pick the immediate join block"
        );
    }

    #[test]
    fn iterative_path_handles_nested_cross_loop_cfg() {
        // Outer header: 0x1000 (back edge from 0x1020)
        let mut b0 = R2ILBlock::new(0x1000, 4);
        b0.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1010, 8),
        });

        // Outer exit
        let mut b1 = R2ILBlock::new(0x1004, 4);
        b1.push(R2ILOp::Branch {
            target: Varnode::constant(0x1030, 8),
        });

        // Inner header: true -> 0x1014, false(fallthrough) -> 0x1020
        let mut b2 = R2ILBlock::new(0x1010, 0x10);
        b2.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1014, 8),
        });

        // Inner back edge
        let mut b3 = R2ILBlock::new(0x1014, 4);
        b3.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });

        // Cross level edge: back to outer header
        let mut b4 = R2ILBlock::new(0x1020, 4);
        b4.push(R2ILOp::Branch {
            target: Varnode::constant(0x1000, 8),
        });

        let mut b5 = R2ILBlock::new(0x1030, 4);
        b5.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let func = SSAFunction::from_blocks(&[b0, b1, b2, b3, b4, b5]).expect("ssa function");
        let mut analyzer = RegionAnalyzer::new(&func);
        let region = analyzer.analyze();
        assert!(
            !matches!(region, Region::Irreducible { entry, .. } if entry == func.entry),
            "iterative analyzer should produce a structured region for nested cross-loop cfg"
        );
        assert!(
            analyzer.analysis_reason().is_none(),
            "iterative analyzer should not trip safety limits on this fixture"
        );
    }

    fn build_switch_trampoline_cfg() -> SSAFunction {
        let mut pred = R2ILBlock::new(0x0ff0, 4);
        pred.push(R2ILOp::Nop);

        let mut outer = R2ILBlock::new(0x1000, 4);
        outer.push(R2ILOp::Nop);

        let mut hop = R2ILBlock::new(0x1004, 4);
        hop.push(R2ILOp::Nop);

        let mut inner = R2ILBlock::new(0x1008, 4);
        inner.push(R2ILOp::Nop);

        let mut case1 = R2ILBlock::new(0x1010, 4);
        case1.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case2 = R2ILBlock::new(0x1020, 4);
        case2.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case3 = R2ILBlock::new(0x1030, 4);
        case3.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut default = R2ILBlock::new(0x1040, 4);
        default.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[
            pred, outer, hop, inner, case1, case2, case3, default,
        ])
        .expect("ssa function");

        func.cfg_mut()
            .set_terminator(0x0ff0, BlockTerminator::Branch { target: 0x1000 });
        func.cfg_mut().set_terminator(
            0x1000,
            BlockTerminator::Switch {
                cases: vec![(433, 0x1004), (437, 0x1040)],
                default: Some(0x1040),
            },
        );
        func.cfg_mut()
            .set_terminator(0x1004, BlockTerminator::Branch { target: 0x1008 });
        func.cfg_mut().set_terminator(
            0x1008,
            BlockTerminator::Switch {
                cases: vec![(0, 0x1010), (1, 0x1020), (2, 0x1030), (408, 0x1040)],
                default: Some(0x1040),
            },
        );

        func
    }

    #[test]
    fn normalized_switch_info_keeps_entry_switch_metadata_authoritative() {
        let func = build_switch_trampoline_cfg();
        let analyzer = RegionAnalyzer::new(&func);
        let info = analyzer
            .normalized_switch_info(0x1000)
            .expect("normalized switch info");
        let pairs = info.cases;

        assert_eq!(pairs, vec![(433, 0x1004), (437, 0x1040)]);
        assert_eq!(info.default, Some(0x1040));
    }

    fn build_nested_switch_cfg_without_entry_switch() -> SSAFunction {
        let mut outer = R2ILBlock::new(0x1000, 4);
        outer.push(R2ILOp::Nop);
        let mut hop = R2ILBlock::new(0x1004, 4);
        hop.push(R2ILOp::Nop);
        let mut inner = R2ILBlock::new(0x1008, 4);
        inner.push(R2ILOp::Nop);
        let mut case1 = R2ILBlock::new(0x1010, 4);
        case1.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case2 = R2ILBlock::new(0x1020, 4);
        case2.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case3 = R2ILBlock::new(0x1030, 4);
        case3.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut default = R2ILBlock::new(0x1040, 4);
        default.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[
            outer, hop, inner, case1, case2, case3, default,
        ])
        .expect("ssa function");
        func.cfg_mut()
            .set_terminator(0x1000, BlockTerminator::Branch { target: 0x1004 });
        func.cfg_mut()
            .set_terminator(0x1004, BlockTerminator::Branch { target: 0x1008 });
        func.cfg_mut().set_terminator(
            0x1008,
            BlockTerminator::Switch {
                cases: vec![(0, 0x1010), (1, 0x1020), (2, 0x1030), (408, 0x1040)],
                default: Some(0x1040),
            },
        );
        func
    }

    #[test]
    fn normalized_switch_info_keeps_dense_nested_cases_with_default_outlier_authoritative() {
        let func = build_nested_switch_cfg_without_entry_switch();
        let analyzer = RegionAnalyzer::new(&func);

        let info = analyzer
            .normalized_switch_info(0x1000)
            .expect("normalized switch info");
        let values: Vec<u64> = info.cases.iter().map(|(value, _)| *value).collect();
        let targets: Vec<u64> = info.cases.iter().map(|(_, target)| *target).collect();

        assert_eq!(values, vec![0, 1, 2, 408]);
        assert_eq!(targets, vec![0x1010, 0x1020, 0x1030, 0x1040]);
        assert_eq!(info.default, Some(0x1040));
    }

    fn build_entry_switch_with_unrelated_sub_cfg() -> SSAFunction {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::register(0x10, 8),
            b: Varnode::constant(1, 8),
        });

        let mut case1 = R2ILBlock::new(0x1010, 4);
        case1.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case2 = R2ILBlock::new(0x1020, 4);
        case2.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case3 = R2ILBlock::new(0x1030, 4);
        case3.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut default = R2ILBlock::new(0x1040, 4);
        default.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[entry, case1, case2, case3, default])
            .expect("ssa function");
        func.cfg_mut().set_terminator(
            0x1000,
            BlockTerminator::Switch {
                cases: vec![(0, 0x1010), (1, 0x1020), (2, 0x1030)],
                default: Some(0x1040),
            },
        );
        func
    }

    #[test]
    fn normalized_switch_info_keeps_authoritative_cases_despite_unrelated_sub() {
        let func = build_entry_switch_with_unrelated_sub_cfg();
        let analyzer = RegionAnalyzer::new(&func);
        let info = analyzer
            .normalized_switch_info(0x1000)
            .expect("normalized switch info");
        let values: Vec<u64> = info.cases.iter().map(|(value, _)| *value).collect();

        assert_eq!(values, vec![0, 1, 2]);
        assert_eq!(info.default, Some(0x1040));
    }

    #[test]
    fn normalized_switch_info_ignores_external_only_targets() {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Nop);

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[entry]).expect("ssa function");
        func.cfg_mut().set_terminator(
            0x1000,
            BlockTerminator::Switch {
                cases: vec![(0, 0x401000), (1, 0x401100)],
                default: Some(0x401200),
            },
        );

        let analyzer = RegionAnalyzer::new(&func);
        assert!(
            analyzer.normalized_switch_info(0x1000).is_none(),
            "switch metadata with only out-of-function targets should not structure as a local switch"
        );

        let mut analyzer = RegionAnalyzer::new(&func);
        let region = analyzer.detect_switch(0x1000, &[0x401000, 0x401100, 0x401200]);
        assert!(
            region.is_none(),
            "external-only switch targets must not synthesize placeholder case values"
        );
        assert!(
            analyzer
                .analysis_reason()
                .is_some_and(|reason| reason.contains("no canonical case values")),
            "refused switch structuring should leave an explicit analysis reason"
        );
    }

    fn build_equality_switch_chain_cfg() -> SSAFunction {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1100, 8),
        });
        let mut hop0 = R2ILBlock::new(0x1004, 4);
        hop0.push(R2ILOp::Branch {
            target: Varnode::constant(0x1008, 8),
        });
        let mut cmp1 = R2ILBlock::new(0x1008, 4);
        cmp1.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1110, 8),
        });
        let mut hop1 = R2ILBlock::new(0x100c, 4);
        hop1.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut cmp2 = R2ILBlock::new(0x1010, 4);
        cmp2.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1120, 8),
        });
        let mut hop2 = R2ILBlock::new(0x1014, 4);
        hop2.push(R2ILOp::Branch {
            target: Varnode::constant(0x1018, 8),
        });
        let mut cmp3 = R2ILBlock::new(0x1018, 4);
        cmp3.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1130, 8),
        });
        let mut hop3 = R2ILBlock::new(0x101c, 4);
        hop3.push(R2ILOp::Branch {
            target: Varnode::constant(0x1140, 8),
        });
        let mut case0 = R2ILBlock::new(0x1100, 4);
        case0.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut case1 = R2ILBlock::new(0x1110, 4);
        case1.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut case2 = R2ILBlock::new(0x1120, 4);
        case2.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut case3 = R2ILBlock::new(0x1130, 4);
        case3.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut default = R2ILBlock::new(0x1140, 4);
        default.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut merge = R2ILBlock::new(0x1200, 4);
        merge.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[
            entry, hop0, cmp1, hop1, cmp2, hop2, cmp3, hop3, case0, case1, case2, case3, default,
            merge,
        ])
        .expect("ssa function");

        let selector = SSAVar::new("W8", 0, 4);

        func.get_block_mut(0x1000).expect("entry block").ops = vec![
            SSAOp::IntEqual {
                dst: SSAVar::new("tmp:eq0", 1, 1),
                a: selector.clone(),
                b: SSAVar::new("const:0", 0, 4),
            },
            SSAOp::CBranch {
                cond: SSAVar::new("tmp:eq0", 1, 1),
                target: SSAVar::new("ram:1100", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("hop0").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("cmp1").ops = vec![
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:sub1", 1, 4),
                a: selector.clone(),
                b: SSAVar::new("const:1", 0, 4),
            },
            SSAOp::IntEqual {
                dst: SSAVar::new("tmp:eq1", 1, 1),
                a: SSAVar::new("tmp:sub1", 1, 4),
                b: SSAVar::new("const:0", 0, 4),
            },
            SSAOp::CBranch {
                cond: SSAVar::new("tmp:eq1", 1, 1),
                target: SSAVar::new("ram:1110", 0, 8),
            },
        ];
        func.get_block_mut(0x100c).expect("hop1").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1010", 0, 8),
        }];
        func.get_block_mut(0x1010).expect("cmp2").ops = vec![
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:sub2", 1, 4),
                a: selector.clone(),
                b: SSAVar::new("const:2", 0, 4),
            },
            SSAOp::IntEqual {
                dst: SSAVar::new("tmp:eq2", 1, 1),
                a: SSAVar::new("tmp:sub2", 1, 4),
                b: SSAVar::new("const:0", 0, 4),
            },
            SSAOp::CBranch {
                cond: SSAVar::new("tmp:eq2", 1, 1),
                target: SSAVar::new("ram:1120", 0, 8),
            },
        ];
        func.get_block_mut(0x1014).expect("hop2").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1018", 0, 8),
        }];
        func.get_block_mut(0x1018).expect("cmp3").ops = vec![
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:sub3", 1, 4),
                a: selector.clone(),
                b: SSAVar::new("const:3", 0, 4),
            },
            SSAOp::IntEqual {
                dst: SSAVar::new("tmp:eq3", 1, 1),
                a: SSAVar::new("tmp:sub3", 1, 4),
                b: SSAVar::new("const:0", 0, 4),
            },
            SSAOp::CBranch {
                cond: SSAVar::new("tmp:eq3", 1, 1),
                target: SSAVar::new("ram:1130", 0, 8),
            },
        ];
        func.get_block_mut(0x101c).expect("hop3").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1140", 0, 8),
        }];
        for (addr, dst_name) in [
            (0x1100, "tmp:case0"),
            (0x1110, "tmp:case1"),
            (0x1120, "tmp:case2"),
            (0x1130, "tmp:case3"),
            (0x1140, "tmp:default"),
        ] {
            func.get_block_mut(addr).expect("case block").ops = vec![
                SSAOp::Copy {
                    dst: SSAVar::new(dst_name, 1, 4),
                    src: selector.clone(),
                },
                SSAOp::Branch {
                    target: SSAVar::new("ram:1200", 0, 8),
                },
            ];
        }

        func.cfg_mut().set_terminator(
            0x1000,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1100,
                false_target: 0x1004,
            },
        );
        func.cfg_mut()
            .set_terminator(0x1004, BlockTerminator::Branch { target: 0x1008 });
        func.cfg_mut().set_terminator(
            0x1008,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1110,
                false_target: 0x100c,
            },
        );
        func.cfg_mut()
            .set_terminator(0x100c, BlockTerminator::Branch { target: 0x1010 });
        func.cfg_mut().set_terminator(
            0x1010,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1120,
                false_target: 0x1014,
            },
        );
        func.cfg_mut()
            .set_terminator(0x1014, BlockTerminator::Branch { target: 0x1018 });
        func.cfg_mut().set_terminator(
            0x1018,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1130,
                false_target: 0x101c,
            },
        );
        func.cfg_mut()
            .set_terminator(0x101c, BlockTerminator::Branch { target: 0x1140 });
        for addr in [0x1100, 0x1110, 0x1120, 0x1130, 0x1140] {
            func.cfg_mut()
                .set_terminator(addr, BlockTerminator::Branch { target: 0x1200 });
        }

        func
    }

    fn build_flag_switch_chain_cfg() -> SSAFunction {
        let mut func = build_equality_switch_chain_cfg();
        let selector = SSAVar::new("W8", 0, 4);

        func.get_block_mut(0x1000).expect("entry block").ops = vec![
            SSAOp::IntEqual {
                dst: SSAVar::new("TMPZR_0", 1, 1),
                a: selector.clone(),
                b: SSAVar::new("const:0", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("ZR_0", 1, 1),
                src: SSAVar::new("TMPZR_0", 1, 1),
            },
            SSAOp::CBranch {
                cond: SSAVar::new("ZR_0", 1, 1),
                target: SSAVar::new("ram:1100", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("cmp1").ops = vec![
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:sub1", 1, 4),
                a: selector.clone(),
                b: SSAVar::new("const:1", 0, 4),
            },
            SSAOp::IntEqual {
                dst: SSAVar::new("TMPZR_1", 1, 1),
                a: SSAVar::new("tmp:sub1", 1, 4),
                b: SSAVar::new("const:0", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("ZR_1", 1, 1),
                src: SSAVar::new("TMPZR_1", 1, 1),
            },
            SSAOp::CBranch {
                cond: SSAVar::new("ZR_1", 1, 1),
                target: SSAVar::new("ram:1110", 0, 8),
            },
        ];
        func.get_block_mut(0x1010).expect("cmp2").ops = vec![
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:sub2", 1, 4),
                a: selector.clone(),
                b: SSAVar::new("const:2", 0, 4),
            },
            SSAOp::IntEqual {
                dst: SSAVar::new("TMPZR_2", 1, 1),
                a: SSAVar::new("tmp:sub2", 1, 4),
                b: SSAVar::new("const:0", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("ZR_2", 1, 1),
                src: SSAVar::new("TMPZR_2", 1, 1),
            },
            SSAOp::CBranch {
                cond: SSAVar::new("ZR_2", 1, 1),
                target: SSAVar::new("ram:1120", 0, 8),
            },
        ];
        func.get_block_mut(0x1018).expect("cmp3").ops = vec![
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:sub3", 1, 4),
                a: selector,
                b: SSAVar::new("const:3", 0, 4),
            },
            SSAOp::IntEqual {
                dst: SSAVar::new("TMPZR_3", 1, 1),
                a: SSAVar::new("tmp:sub3", 1, 4),
                b: SSAVar::new("const:0", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("ZR_3", 1, 1),
                src: SSAVar::new("TMPZR_3", 1, 1),
            },
            SSAOp::CBranch {
                cond: SSAVar::new("ZR_3", 1, 1),
                target: SSAVar::new("ram:1130", 0, 8),
            },
        ];

        func
    }

    fn build_guarded_nested_switch_cfg() -> SSAFunction {
        let mut guard0 = R2ILBlock::new(0x1000, 4);
        guard0.push(R2ILOp::CBranch {
            cond: Varnode::unique(0x10, 1),
            target: Varnode::constant(0x1010, 8),
        });
        let mut guard1 = R2ILBlock::new(0x1004, 4);
        guard1.push(R2ILOp::CBranch {
            cond: Varnode::unique(0x11, 1),
            target: Varnode::constant(0x1014, 8),
        });
        let mut switch_block = R2ILBlock::new(0x1008, 4);
        switch_block.push(R2ILOp::Nop);
        let mut early_ret = R2ILBlock::new(0x1010, 4);
        early_ret.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut range_ret = R2ILBlock::new(0x1014, 4);
        range_ret.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut case0 = R2ILBlock::new(0x1100, 4);
        case0.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut case1 = R2ILBlock::new(0x1110, 4);
        case1.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut case2 = R2ILBlock::new(0x1120, 4);
        case2.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut case3 = R2ILBlock::new(0x1130, 4);
        case3.push(R2ILOp::Branch {
            target: Varnode::constant(0x1200, 8),
        });
        let mut merge = R2ILBlock::new(0x1200, 4);
        merge.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[
            guard0,
            guard1,
            switch_block,
            early_ret,
            range_ret,
            case0,
            case1,
            case2,
            case3,
            merge,
        ])
        .expect("ssa function");

        func.cfg_mut().set_terminator(
            0x1008,
            BlockTerminator::Switch {
                cases: vec![(0, 0x1100), (1, 0x1110), (2, 0x1120), (3, 0x1130)],
                default: Some(0x1014),
            },
        );

        func
    }

    #[test]
    fn detects_conditional_switch_chain_from_equality_ladder() {
        let func = build_equality_switch_chain_cfg();
        let mut analyzer = RegionAnalyzer::new(&func);

        let region = analyzer
            .detect_conditional_switch_chain(0x1000, 0x1100, 0x1004)
            .expect("switch chain region");
        let Region::Switch {
            switch_block,
            cases,
            default,
            merge_block,
        } = region
        else {
            panic!("expected switch region from equality ladder");
        };

        assert_eq!(switch_block, 0x1000);
        let values: Vec<u64> = cases
            .iter()
            .map(|(value, _)| value.expect("case value"))
            .collect();
        assert_eq!(values, vec![0, 1, 2, 3]);
        assert_eq!(default.map(|region| region.entry()), Some(0x1140));
        assert_eq!(merge_block, Some(0x1200));
    }

    #[test]
    fn detects_conditional_switch_chain_from_flag_zero_ladder() {
        let func = build_flag_switch_chain_cfg();
        let mut analyzer = RegionAnalyzer::new(&func);

        let region = analyzer
            .detect_conditional_switch_chain(0x1000, 0x1100, 0x1004)
            .expect("switch chain region");
        let Region::Switch {
            switch_block,
            cases,
            default,
            merge_block,
        } = region
        else {
            panic!("expected switch region from flag ladder");
        };

        assert_eq!(switch_block, 0x1000);
        let values: Vec<u64> = cases
            .iter()
            .map(|(value, _)| value.expect("case value"))
            .collect();
        assert_eq!(values, vec![0, 1, 2, 3]);
        assert_eq!(default.map(|region| region.entry()), Some(0x1140));
        assert_eq!(merge_block, Some(0x1200));
    }

    #[test]
    fn guarded_nested_switch_does_not_promote_entry_guard_to_switch() {
        let func = build_guarded_nested_switch_cfg();
        assert_eq!(func.successors(0x1000), vec![0x1010, 0x1004]);
        assert_eq!(func.successors(0x1004), vec![0x1014, 0x1008]);
        let mut analyzer = RegionAnalyzer::new(&func);

        let region = analyzer.analyze_region_recursive(0x1000);
        let Region::IfThenElse {
            cond_block,
            then_region,
            else_region,
            ..
        } = region
        else {
            panic!("expected entry guard to stay conditional");
        };
        assert_eq!(cond_block, 0x1000);

        let Some(other_region) = else_region else {
            panic!("expected both entry-guard arms");
        };
        let (nested_guard, early_return) = if then_region.entry() == 0x1004 {
            (then_region, other_region)
        } else if other_region.entry() == 0x1004 {
            (other_region, then_region)
        } else {
            panic!("expected one entry arm to continue into nested guard");
        };
        assert_eq!(early_return.entry(), 0x1010);

        let Region::IfThenElse {
            cond_block,
            then_region,
            else_region,
            ..
        } = *nested_guard
        else {
            panic!("expected nested range guard before switch");
        };
        assert_eq!(cond_block, 0x1004);
        let Some(other_region) = else_region else {
            panic!("expected both nested-guard arms");
        };
        let (switch_region, range_return) = if then_region.entry() == 0x1008 {
            (then_region, other_region)
        } else if other_region.entry() == 0x1008 {
            (other_region, then_region)
        } else {
            panic!("expected one nested guard arm to continue into switch");
        };
        assert_eq!(range_return.entry(), 0x1014);

        let Region::Switch { switch_block, .. } = *switch_region else {
            panic!("expected real switch to stay anchored at the jump-table block");
        };
        assert_eq!(switch_block, 0x1008);
    }
}
