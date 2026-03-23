//! Control flow structuring.
//!
//! This module converts unstructured control flow (gotos, CFG edges) into
//! structured high-level constructs (if-then-else, while, for, etc.).

use std::collections::{HashMap, HashSet};

use r2ssa::cfg::BlockTerminator;
use r2ssa::{CFGEdge, SSAFunction};

use crate::ast::{BinaryOp, CExpr, CStmt, UnaryOp};
use crate::fold::FoldingContext;
use crate::region::{Region, RegionAnalyzer};

/// Control flow structurer.
///
/// Converts a region tree into structured C statements.
pub struct ControlFlowStructurer<'a, 'o> {
    func: &'a SSAFunction,
    /// Folding context for expression optimization.
    fold_ctx: &'o FoldingContext<'o>,
    /// Cached folded statements per basic block.
    folded_block_cache: HashMap<u64, Vec<CStmt>>,
    /// Labels for blocks that need gotos.
    labels: HashMap<u64, String>,
    /// Counter for generating unique labels.
    label_counter: usize,
    /// Region analyzer for detecting breaks/continues.
    region_analyzer: Option<RegionAnalyzer<'a>>,
    /// Safety budget for recursive region structuring.
    safety_budget_remaining: usize,
    safety_budget_max: usize,
    safety_reason: Option<String>,
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
            label_counter: 0,
            region_analyzer: Some(region_analyzer),
            safety_budget_remaining: safety_budget_max,
            safety_budget_max,
            safety_reason: None,
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
            label_counter: 0,
            region_analyzer: Some(RegionAnalyzer::new(func)),
            safety_budget_remaining: safety_budget_max,
            safety_budget_max,
            safety_reason: None,
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

    /// Get the set of variable names that survive folding (for filtering declarations).
    pub fn emitted_var_names(&self) -> HashSet<String> {
        let blocks: Vec<_> = self.func.blocks().cloned().collect();
        self.fold_ctx.emitted_var_names(&blocks)
    }

    /// Structure the function's control flow.
    pub fn structure(&mut self) -> CStmt {
        self.reset_safety_budget();
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
        let stmt = self.structure_region(&region);
        if self.safety_reason.is_some() {
            return CStmt::Empty;
        }
        // Post-process: flatten, simplify loops, remove redundant control flow
        Self::cleanup(stmt)
    }

    /// Structure a region into C statements.
    fn structure_region(&mut self, region: &Region) -> CStmt {
        if !self.consume_safety_budget(1) {
            return CStmt::Empty;
        }
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
                if let Some(rewritten) = self.try_structure_if_else_with_slot_merge_returns(
                    *cond_block,
                    then_region,
                    else_region.as_deref(),
                    *merge_block,
                ) {
                    return rewritten;
                }
                if let Some(rewritten) = self.try_structure_guarded_switch_with_default(
                    *cond_block,
                    then_region,
                    else_region.as_deref(),
                    *merge_block,
                ) {
                    return rewritten;
                }
                let mut cond = self.get_branch_condition(*cond_block);
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
                let then_stmt = self.structure_region(then_region);
                let else_stmt = else_region.as_ref().map(|r| self.structure_region(r));
                let if_stmt = CStmt::if_stmt(cond, then_stmt, else_stmt);
                let mut prefix = self.structure_block_prefix_stmts(*cond_block);
                prefix.push(if_stmt);
                if let Some(merge_addr) = merge_block {
                    Self::append_stmt_body_flat(&mut prefix, self.structure_block(*merge_addr));
                }
                if prefix.len() == 1 {
                    prefix.into_iter().next().unwrap_or(CStmt::Empty)
                } else {
                    CStmt::Block(prefix)
                }
            }
            Region::WhileLoop { header, body } => {
                let cond = self.get_branch_condition(*header);
                let body_stmt = self.structure_loop_body(body);
                CStmt::while_loop(cond, body_stmt)
            }
            Region::DoWhileLoop { body, cond_block } => {
                let body_stmt = self.structure_loop_body(body);
                let cond = self.get_branch_condition(*cond_block);
                CStmt::DoWhile {
                    body: Box::new(body_stmt),
                    cond,
                }
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

    /// Get the switch expression from a block.
    fn get_switch_expression(&mut self, addr: u64) -> CExpr {
        let switch_addr = self.unique_switch_block().unwrap_or(addr);
        let block = match self.func.get_block(switch_addr) {
            Some(b) => b,
            None => return CExpr::Var("switch_expr".to_string()),
        };

        if let Some(expr) = self.fold_ctx.resolve_switch_expr_for_block(switch_addr) {
            return expr;
        }

        if let Some(expr) =
            Self::selector_expr_from_condition(&self.get_branch_condition(switch_addr))
        {
            return expr;
        }
        if let Some(expr) = self.selector_expr_from_switch_predecessors(switch_addr) {
            return expr;
        }

        // Look for an indirect branch which typically has the switch variable
        for op in &block.ops {
            if let Some(expr) = self.fold_ctx.extract_switch_expr(op) {
                return expr;
            }
        }

        CExpr::Var("test".to_string())
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
            .filter_map(|pred| Self::selector_expr_from_condition(&self.get_branch_condition(pred)))
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
        let switch_expr = self.get_switch_expression(switch_block);
        let case_display_bias = self.switch_case_display_bias(switch_block, cases);

        let mut switch_cases = Vec::new();
        for (case_value, case_region) in cases {
            let value_expr = case_value
                .map(|v| CExpr::IntLit(v.saturating_add_signed(case_display_bias) as i64))
                .unwrap_or(CExpr::IntLit(0));
            let case_stmt = self.structure_region(case_region);
            switch_cases.push(crate::ast::SwitchCase {
                value: value_expr,
                body: vec![case_stmt, CStmt::Break],
            });
        }

        let default_body = default.map(|region| vec![self.structure_region(region)]);
        let switch_stmt = CStmt::Switch {
            expr: switch_expr,
            cases: switch_cases,
            default: default_body,
        };

        let mut prefix = self.structure_block_prefix_stmts(switch_block);
        prefix.push(switch_stmt);
        if let Some(merge_addr) = merge_block {
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

    fn switch_case_display_bias(
        &self,
        switch_block: u64,
        cases: &[(Option<u64>, Box<Region>)],
    ) -> i64 {
        let values = cases
            .iter()
            .filter_map(|(value, _)| *value)
            .collect::<Vec<_>>();
        if values.is_empty() || !values.contains(&0) {
            return 0;
        }
        if let Some(bias) = values.iter().copied().max().and_then(|upper_bound| {
            self.guarded_dense_zero_based_switch_bias(switch_block, values.len(), upper_bound)
        }) {
            return bias;
        }

        let mut search_blocks = vec![switch_block];
        let mut seen = HashSet::from([switch_block]);
        let mut queue = std::collections::VecDeque::from([(switch_block, 0usize)]);
        for succ in self.func.successors(switch_block) {
            if seen.insert(succ) {
                search_blocks.push(succ);
                queue.push_back((succ, 0usize));
            }
        }
        while let Some((block, depth)) = queue.pop_front() {
            if depth >= 8 {
                continue;
            }
            for pred in self.func.predecessors(block) {
                if seen.insert(pred) {
                    search_blocks.push(pred);
                    queue.push_back((pred, depth + 1));
                }
            }
        }

        let mut best_bias = 0i64;
        for block_addr in search_blocks {
            let Some(block) = self.func.get_block(block_addr) else {
                continue;
            };
            for op in &block.ops {
                if let r2ssa::SSAOp::IntSub { b, .. } = op
                    && let Some(raw) = crate::analysis::utils::parse_const_value(&b.name)
                    && let Ok(bias) = i64::try_from(raw)
                    && (1..=8).contains(&bias)
                    && (best_bias == 0 || bias < best_bias)
                {
                    best_bias = bias;
                }
            }
        }

        if best_bias == 0 && values.len() >= 16 {
            for block_addr in self.func.block_addrs() {
                let Some(block) = self.func.get_block(*block_addr) else {
                    continue;
                };
                for op in &block.ops {
                    if let r2ssa::SSAOp::IntSub { b, .. } = op
                        && let Some(raw) = crate::analysis::utils::parse_const_value(&b.name)
                        && let Ok(bias) = i64::try_from(raw)
                        && (1..=8).contains(&bias)
                        && (best_bias == 0 || bias < best_bias)
                    {
                        best_bias = bias;
                    }
                }
            }
        }

        if best_bias == 0
            && values.len() >= 32
            && values
                .iter()
                .enumerate()
                .all(|(idx, value)| *value == idx as u64)
        {
            return 1;
        }

        best_bias
    }

    fn guarded_dense_zero_based_switch_bias(
        &self,
        switch_block: u64,
        case_count: usize,
        upper_bound: u64,
    ) -> Option<i64> {
        if case_count < 4 {
            return None;
        }

        for block_addr in std::iter::once(switch_block).chain(self.func.predecessors(switch_block))
        {
            let Some(block) = self.func.get_block(block_addr) else {
                continue;
            };
            let mut best_bias = None;
            let mut saw_upper_bound_guard = false;
            for op in &block.ops {
                if let r2ssa::SSAOp::IntSub { b, .. } = op
                    && let Some(raw) = crate::analysis::utils::parse_const_value(&b.name)
                {
                    if raw == upper_bound {
                        saw_upper_bound_guard = true;
                    }
                    if let Ok(bias) = i64::try_from(raw)
                        && (1..=8).contains(&bias)
                    {
                        best_bias = Some(best_bias.map_or(bias, |current: i64| current.min(bias)));
                    }
                }
            }
            if saw_upper_bound_guard && best_bias.is_some() {
                return best_bias;
            }
        }

        None
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
        if let Some(label) = self.labels.get(&addr) {
            stmts.push(CStmt::Label(label.clone()));
        }

        // Convert operations to statements
        stmts.extend(self.folded_block_stmts(block, addr));

        // Check for break/continue at block end
        if let Some(ref analyzer) = self.region_analyzer {
            if analyzer.is_loop_continue(addr) {
                stmts.push(CStmt::Continue);
            } else if analyzer.is_loop_break(addr) {
                stmts.push(CStmt::Break);
            } else if analyzer.is_loop_goto(addr)
                && let Some(target) = analyzer.get_loop_goto_target(addr)
            {
                let label = self.ensure_label(target);
                stmts.push(CStmt::Goto(label));
            }
        }

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
        if let Some(label) = self.labels.get(&addr) {
            stmts.push(CStmt::Label(label.clone()));
        }

        // Convert operations to statements
        stmts.extend(self.folded_block_stmts(block, addr));

        // Check for break/continue at block end
        if let Some(ref analyzer) = self.region_analyzer {
            if analyzer.is_loop_continue(addr) {
                stmts.push(CStmt::Continue);
            } else if analyzer.is_loop_break(addr) {
                stmts.push(CStmt::Break);
            } else if analyzer.is_loop_goto(addr)
                && let Some(target) = analyzer.get_loop_goto_target(addr)
            {
                let label = self.ensure_label(target);
                stmts.push(CStmt::Goto(label));
            }
        }
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

        self.folded_block_stmts(block, addr)
    }

    fn folded_block_stmts(&mut self, block: &r2ssa::FunctionSSABlock, addr: u64) -> Vec<CStmt> {
        if let Some(stmts) = self.folded_block_cache.get(&addr) {
            return stmts.clone();
        }

        let stmts = self.fold_ctx.fold_block(block, addr);
        self.folded_block_cache.insert(addr, stmts.clone());
        stmts
    }

    /// Get the branch condition from a block.
    fn get_branch_condition(&mut self, addr: u64) -> CExpr {
        let block = match self.func.get_block(addr) {
            Some(b) => b,
            None => return CExpr::IntLit(1),
        };

        if let Some(cond) = self.fold_ctx.extract_condition_from_block(block) {
            return cond;
        }

        // Look for a conditional branch in the block
        for op in &block.ops {
            if let Some(cond) = self.fold_ctx.extract_condition(op) {
                return cond;
            }
        }

        // Default to true
        CExpr::IntLit(1)
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
    fn cleanup(stmt: CStmt) -> CStmt {
        // Recurse first, then simplify
        let stmt = Self::cleanup_recurse(stmt);
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
                let stmt = Self::rewrite_if_short_circuit(stmt);
                let stmt = Self::rewrite_if_condition_inversion(stmt);
                let stmt = Self::rewrite_empty_if_bodies(stmt);
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
                        body: c.body.into_iter().map(Self::cleanup_recurse).collect(),
                    })
                    .collect();
                let default = default.map(|d| d.into_iter().map(Self::cleanup_recurse).collect());
                CStmt::Switch {
                    expr,
                    cases,
                    default,
                }
            }
            other => other,
        }
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
        let then_can_rewrite =
            then_pred.is_some_and(|pred| self.has_merged_slot_return_expr(pred, summary));
        let else_can_rewrite =
            else_pred.is_some_and(|pred| self.has_merged_slot_return_expr(pred, summary));
        if !then_can_rewrite && !else_can_rewrite {
            return None;
        }

        let mut then_stmt = self.structure_region(then_region);
        let mut else_stmt = self.structure_region(else_region);
        let mut rewrote_any = false;

        if then_can_rewrite
            && let Some(pred) = then_pred
            && let Some(rewritten) =
                self.append_merged_slot_return_if_needed(then_stmt.clone(), pred, summary)
        {
            then_stmt = rewritten;
            rewrote_any = true;
        }
        if else_can_rewrite
            && let Some(pred) = else_pred
            && let Some(rewritten) =
                self.append_merged_slot_return_if_needed(else_stmt.clone(), pred, summary)
        {
            else_stmt = rewritten;
            rewrote_any = true;
        }
        if !rewrote_any
            || !Self::stmt_guarantees_termination(&then_stmt)
            || !Self::stmt_guarantees_termination(&else_stmt)
        {
            return None;
        }

        let if_stmt = CStmt::If {
            cond: self.get_branch_condition(cond_block),
            then_body: Box::new(then_stmt),
            else_body: Some(Box::new(else_stmt)),
        };
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
        candidates.sort_unstable();
        candidates.dedup();
        match candidates.as_slice() {
            [pred] => Some(*pred),
            _ => None,
        }
    }

    fn append_merged_slot_return_if_needed(
        &self,
        stmt: CStmt,
        pred_addr: u64,
        summary: &crate::analysis::FrameSlotMergeSummary,
    ) -> Option<CStmt> {
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
        pred_addr: u64,
        summary: &crate::analysis::FrameSlotMergeSummary,
    ) -> bool {
        summary.incoming.contains_key(&pred_addr)
            || self
                .fold_ctx
                .merged_return_candidate_for_block_slot(pred_addr, summary.slot_offset)
                .is_some()
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
                    BinaryOp::Eq => Some(BinaryOp::Ne),
                    BinaryOp::Ne => Some(BinaryOp::Eq),
                    BinaryOp::Lt => Some(BinaryOp::Ge),
                    BinaryOp::Le => Some(BinaryOp::Gt),
                    BinaryOp::Gt => Some(BinaryOp::Le),
                    BinaryOp::Ge => Some(BinaryOp::Lt),
                    _ => None,
                };

                if let Some(op) = negated {
                    CExpr::Binary { op, left, right }
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

        let prev_stmts = if effective.len() >= 2 {
            &effective[..effective.len() - 1]
        } else {
            &[]
        };
        let (update, update_links_cond) =
            Self::update_expr_from_stmt(var, cond_vars, prev_stmts, effective.last().unwrap())?;
        effective.pop();
        Some((update, Self::stmt_from_vec(effective), update_links_cond))
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
                ) && matches!(operand.as_ref(), CExpr::Var(_)) =>
            {
                Some((expr.clone(), false))
            }
            CExpr::Binary { op, left, right } if matches!(left.as_ref(), CExpr::Var(_)) => {
                if *op == BinaryOp::Assign {
                    let rhs_vars = Self::collect_expr_vars(right);
                    let links_cond_direct = Self::sets_overlap_loop_vars(&rhs_vars, cond_vars);
                    let reads_induction = Self::set_contains_loop_var(&rhs_vars, var);
                    let links_cond_via_alias =
                        Self::rhs_links_cond_via_alias(prev_stmts, &rhs_vars, cond_vars);
                    if reads_induction || links_cond_direct || links_cond_via_alias {
                        return Some((expr.clone(), links_cond_direct || links_cond_via_alias));
                    }
                }
                if Self::is_compound_assign_op(*op) {
                    return Some((expr.clone(), false));
                }
                None
            }
            _ => None,
        }
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
    use super::ControlFlowStructurer;
    use crate::ast::{BinaryOp, CExpr, CStmt, UnaryOp};

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
            assert_eq!(update, update_expr);
        }
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
    fn inverts_if_else_terminator_and_flattens_then_block() {
        let input = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Lt, v("x"), v("limit")),
            CStmt::Block(vec![
                assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("x"))),
                assign("x", CExpr::binary(BinaryOp::Add, v("x"), CExpr::IntLit(1))),
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
                assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("x"))),
                assign("x", CExpr::binary(BinaryOp::Add, v("x"), CExpr::IntLit(1))),
            ])
        );
    }

    #[test]
    fn inverts_if_then_terminator_and_flattens_else_block() {
        let input = CStmt::if_stmt(
            v("is_error"),
            CStmt::ret(Some(CExpr::IntLit(-1))),
            Some(CStmt::Block(vec![
                assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("x"))),
                assign("x", CExpr::binary(BinaryOp::Add, v("x"), CExpr::IntLit(1))),
            ])),
        );

        let cleaned = ControlFlowStructurer::cleanup(input);
        assert_eq!(
            cleaned,
            CStmt::Block(vec![
                CStmt::if_stmt(v("is_error"), CStmt::ret(Some(CExpr::IntLit(-1))), None),
                assign("sum", CExpr::binary(BinaryOp::Add, v("sum"), v("x"))),
                assign("x", CExpr::binary(BinaryOp::Add, v("x"), CExpr::IntLit(1))),
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
}
