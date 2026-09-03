//! Control Flow Graph (CFG) representation for r2il.
//!
//! This module provides a CFG data structure built from r2il blocks,
//! which is the foundation for inter-procedural SSA analysis.

use std::collections::{BTreeSet, HashMap, HashSet};

use petgraph::Direction;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::EdgeRef;
use r2il::{R2ILBlock, R2ILOp, SwitchInfo};
use serde::{Deserialize, Serialize};

/// A basic block in the control flow graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BasicBlock {
    /// The address of the first instruction in this block.
    pub addr: u64,
    /// The size of this block in bytes.
    pub size: u32,
    /// The r2il operations in this block.
    pub ops: Vec<R2ILOp>,
    /// The type of terminator for this block.
    pub terminator: BlockTerminator,
    /// Original switch metadata, retained so certification can validate every
    /// source field instead of relying on the lossy CFG terminator projection.
    pub switch_info: Option<SwitchInfo>,
    /// Address attributed to the final operation by the source lifter. When
    /// metadata is absent this falls back to the block address.
    terminal_instruction_addr: Option<u64>,
    /// Source instruction each operation was lifted from, parallel to `ops`.
    ///
    /// One machine instruction lifts to several operations, and the boundary
    /// between two of them is not recoverable from the operations themselves.
    /// Anything reasoning about what a whole instruction did -- as opposed to
    /// what one operation did -- needs that boundary, and the lifter is the
    /// only thing that ever saw it.
    ///
    /// Empty, or `None` at an index, where the lifter attached no metadata.
    /// Nothing may then claim to know where an instruction begins, which is
    /// the honest answer rather than assuming the block is one.
    #[serde(default)]
    op_instruction_addrs: Vec<Option<u64>>,
}

/// How a basic block terminates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum BlockTerminator {
    /// Falls through to the next sequential block.
    Fallthrough { next: u64 },
    /// Unconditional branch to a target.
    Branch { target: u64 },
    /// Conditional branch with true and false targets.
    ConditionalBranch { true_target: u64, false_target: u64 },
    /// Indirect branch (target unknown at compile time).
    IndirectBranch,
    /// Switch statement with multiple targets.
    Switch {
        /// Case targets: (case_value, target_address).
        cases: Vec<(u64, u64)>,
        /// Default case target (if any).
        default: Option<u64>,
    },
    /// Call to a function (may have fallthrough).
    Call {
        target: u64,
        fallthrough: Option<u64>,
    },
    /// Indirect call.
    IndirectCall { fallthrough: Option<u64> },
    /// Return from function.
    Return,
    /// No terminator (incomplete block).
    None,
}

impl BasicBlock {
    /// Create a new basic block.
    pub fn new(addr: u64) -> Self {
        Self {
            addr,
            size: 0,
            ops: Vec::new(),
            terminator: BlockTerminator::None,
            switch_info: None,
            terminal_instruction_addr: None,
            op_instruction_addrs: Vec::new(),
        }
    }

    /// Create a basic block from an r2il block.
    pub fn from_r2il(block: &R2ILBlock) -> Self {
        // Check if this block has switch info
        let terminator = if let Some(ref switch_info) = block.switch_info {
            // Use switch terminator with cases from switch_info
            let cases: Vec<(u64, u64)> = switch_info
                .cases
                .iter()
                .map(|c| (c.value, c.target))
                .collect();
            BlockTerminator::Switch {
                cases,
                default: switch_info.default_target,
            }
        } else {
            Self::analyze_terminator(&block.ops, block.addr + block.size as u64)
        };

        Self {
            addr: block.addr,
            size: block.size,
            ops: block.ops.clone(),
            terminator,
            switch_info: block.switch_info.clone(),
            terminal_instruction_addr: (!block.ops.is_empty()).then(|| {
                block
                    .op_metadata
                    .get(&(block.ops.len() - 1))
                    .and_then(|metadata| metadata.instruction_addr)
                    .unwrap_or(block.addr)
            }),
            op_instruction_addrs: (0..block.ops.len())
                .map(|index| {
                    block
                        .op_metadata
                        .get(&index)
                        .and_then(|metadata| metadata.instruction_addr)
                })
                .collect(),
        }
    }

    /// Source address of the final operation, with the block address used when
    /// the lifter did not attach per-operation instruction metadata.
    pub const fn terminal_instruction_addr(&self) -> Option<u64> {
        self.terminal_instruction_addr
    }

    /// Source instruction the operation at this index was lifted from.
    ///
    /// `None` where the lifter attached no metadata for it, and then no caller
    /// may treat the operation as beginning or continuing an instruction.
    pub fn op_instruction_addr(&self, index: usize) -> Option<u64> {
        self.op_instruction_addrs.get(index).copied().flatten()
    }

    /// Analyze the operations to determine the block terminator.
    fn analyze_terminator(ops: &[R2ILOp], fallthrough_addr: u64) -> BlockTerminator {
        // Look for control flow operations at the end
        for op in ops.iter().rev() {
            match op {
                R2ILOp::Branch { target } => {
                    if let Some(addr) = Self::extract_const_addr(target) {
                        return BlockTerminator::Branch { target: addr };
                    }
                    return BlockTerminator::IndirectBranch;
                }
                R2ILOp::CBranch { target, .. } => {
                    if let Some(true_target) = Self::extract_const_addr(target) {
                        return BlockTerminator::ConditionalBranch {
                            true_target,
                            false_target: fallthrough_addr,
                        };
                    }
                    // Indirect conditional branch - treat as indirect
                    return BlockTerminator::IndirectBranch;
                }
                R2ILOp::BranchInd { .. } => {
                    return BlockTerminator::IndirectBranch;
                }
                R2ILOp::Call { target } => {
                    if let Some(addr) = Self::extract_const_addr(target) {
                        return BlockTerminator::Call {
                            target: addr,
                            fallthrough: Some(fallthrough_addr),
                        };
                    }
                    return BlockTerminator::IndirectCall {
                        fallthrough: Some(fallthrough_addr),
                    };
                }
                R2ILOp::CallInd { .. } => {
                    return BlockTerminator::IndirectCall {
                        fallthrough: Some(fallthrough_addr),
                    };
                }
                R2ILOp::Return { .. } => {
                    return BlockTerminator::Return;
                }
                // Skip non-control-flow ops
                _ => continue,
            }
        }

        // No control flow op found - falls through
        BlockTerminator::Fallthrough {
            next: fallthrough_addr,
        }
    }

    /// Extract a constant address from a varnode.
    fn extract_const_addr(vn: &r2il::Varnode) -> Option<u64> {
        use r2il::SpaceId;
        if vn.space == SpaceId::Const {
            Some(vn.offset)
        } else if vn.space == SpaceId::Ram {
            // Direct address in RAM space
            Some(vn.offset)
        } else {
            None
        }
    }

    /// Get the successor addresses of this block.
    pub fn successors(&self) -> Vec<u64> {
        match &self.terminator {
            BlockTerminator::Fallthrough { next } => vec![*next],
            BlockTerminator::Branch { target } => vec![*target],
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => vec![*true_target, *false_target],
            BlockTerminator::Switch { cases, default } => {
                let mut targets: Vec<u64> = cases.iter().map(|(_, target)| *target).collect();
                if let Some(def) = default {
                    targets.push(*def);
                }
                // Deduplicate targets
                targets.sort();
                targets.dedup();
                targets
            }
            BlockTerminator::Call { fallthrough, .. } => fallthrough.iter().copied().collect(),
            BlockTerminator::IndirectCall { fallthrough } => fallthrough.iter().copied().collect(),
            BlockTerminator::IndirectBranch | BlockTerminator::Return | BlockTerminator::None => {
                vec![]
            }
        }
    }

    /// Check if this block is a branch (conditional or unconditional).
    pub fn is_branch(&self) -> bool {
        matches!(
            self.terminator,
            BlockTerminator::Branch { .. }
                | BlockTerminator::ConditionalBranch { .. }
                | BlockTerminator::IndirectBranch
                | BlockTerminator::Switch { .. }
        )
    }

    /// Check if this block ends with a return.
    pub fn is_return(&self) -> bool {
        matches!(self.terminator, BlockTerminator::Return)
    }
}

fn op_direct_control_target(op: &R2ILOp) -> Option<u64> {
    match op {
        R2ILOp::Branch { target } | R2ILOp::CBranch { target, .. } => {
            BasicBlock::extract_const_addr(target)
        }
        _ => None,
    }
}

fn op_terminates_basic_block(op: &R2ILOp) -> bool {
    matches!(
        op,
        R2ILOp::Branch { .. }
            | R2ILOp::CBranch { .. }
            | R2ILOp::BranchInd { .. }
            | R2ILOp::Return { .. }
    )
}

fn op_instruction_addr(block: &R2ILBlock, op_idx: usize) -> Option<u64> {
    block
        .op_metadata
        .get(&op_idx)
        .and_then(|metadata| metadata.instruction_addr)
}

fn split_internal_control_flow_targets(block: &R2ILBlock) -> Vec<R2ILBlock> {
    if block.switch_info.is_some() || block.ops.is_empty() {
        return vec![block.clone()];
    }

    let block_end = block.addr.saturating_add(block.size as u64);
    if block_end <= block.addr {
        return vec![block.clone()];
    }

    let instruction_addrs = block
        .op_metadata
        .values()
        .filter_map(|metadata| metadata.instruction_addr)
        .collect::<BTreeSet<_>>();
    if instruction_addrs.is_empty() {
        return vec![block.clone()];
    }

    let mut op_instruction_addrs = Vec::with_capacity(block.ops.len());
    let mut last_instruction_addr = block.addr;
    for op_idx in 0..block.ops.len() {
        if let Some(instruction_addr) = op_instruction_addr(block, op_idx) {
            last_instruction_addr = instruction_addr;
        }
        op_instruction_addrs.push(last_instruction_addr);
    }

    let mut split_points = BTreeSet::new();
    for (op_idx, op) in block.ops.iter().enumerate() {
        if let Some(target) = op_direct_control_target(op)
            && target > block.addr
            && target < block_end
            && instruction_addrs.contains(&target)
        {
            split_points.insert(target);
        }

        if op_terminates_basic_block(op) {
            let current_addr = op_instruction_addrs
                .get(op_idx)
                .copied()
                .unwrap_or(block.addr);
            let fallthrough = op_instruction_addrs
                .iter()
                .skip(op_idx + 1)
                .copied()
                .find(|addr| *addr > current_addr);
            if let Some(fallthrough) = fallthrough
                && fallthrough > block.addr
                && fallthrough < block_end
                && instruction_addrs.contains(&fallthrough)
            {
                split_points.insert(fallthrough);
            }
        }
    }
    if split_points.is_empty() {
        return vec![block.clone()];
    }

    let mut starts = Vec::with_capacity(split_points.len() + 1);
    starts.push(block.addr);
    starts.extend(split_points);

    let mut chunks = starts
        .iter()
        .enumerate()
        .map(|(idx, &start)| {
            let end = starts.get(idx + 1).copied().unwrap_or(block_end);
            R2ILBlock {
                addr: start,
                size: end.saturating_sub(start).min(u32::MAX as u64) as u32,
                ops: Vec::new(),
                switch_info: None,
                op_metadata: Default::default(),
            }
        })
        .collect::<Vec<_>>();

    for (op_idx, op) in block.ops.iter().cloned().enumerate() {
        let instruction_addr = op_instruction_addrs
            .get(op_idx)
            .copied()
            .unwrap_or(block.addr);
        let chunk_idx = starts
            .partition_point(|start| *start <= instruction_addr)
            .saturating_sub(1)
            .min(chunks.len().saturating_sub(1));
        let next_op_idx = chunks[chunk_idx].ops.len();
        chunks[chunk_idx].ops.push(op);
        if let Some(metadata) = block.op_metadata.get(&op_idx) {
            chunks[chunk_idx]
                .op_metadata
                .insert(next_op_idx, metadata.clone());
        }
    }

    chunks
        .into_iter()
        .filter(|chunk| !chunk.ops.is_empty())
        .collect()
}

/// A Control Flow Graph for a function.
#[derive(Debug, Clone)]
pub struct CFG {
    /// The underlying directed graph.
    graph: DiGraph<BasicBlock, CFGEdge>,
    /// Map from block address to node index.
    addr_to_node: HashMap<u64, NodeIndex>,
    /// The entry block address.
    pub entry: u64,
}

/// Edge type in the CFG.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CFGEdge {
    /// Normal control flow (fallthrough or unconditional branch).
    Normal,
    /// True branch of a conditional.
    True,
    /// False branch of a conditional.
    False,
    /// Back edge (loop).
    Back,
}

impl CFG {
    fn edge_sort_rank(edge: CFGEdge) -> u8 {
        match edge {
            CFGEdge::True => 0,
            CFGEdge::False => 1,
            CFGEdge::Normal => 2,
            CFGEdge::Back => 3,
        }
    }

    /// Create a new empty CFG with the given entry address.
    pub fn new(entry: u64) -> Self {
        Self {
            graph: DiGraph::new(),
            addr_to_node: HashMap::new(),
            entry,
        }
    }

    /// Build a CFG from a sequence of r2il blocks.
    ///
    /// The blocks should be in address order and represent a complete function.
    pub fn from_blocks(blocks: &[R2ILBlock]) -> Option<Self> {
        if blocks.is_empty() {
            return None;
        }

        let entry = blocks[0].addr;
        let mut cfg = Self::new(entry);

        let normalized_blocks = blocks
            .iter()
            .flat_map(split_internal_control_flow_targets)
            .collect::<Vec<_>>();

        // First pass: add all blocks as nodes
        for block in &normalized_blocks {
            let bb = BasicBlock::from_r2il(block);
            cfg.add_block(bb);
        }

        cfg.rebuild_edges();
        Some(cfg)
    }

    /// Add a basic block to the CFG.
    pub fn add_block(&mut self, block: BasicBlock) -> NodeIndex {
        let addr = block.addr;
        let idx = self.graph.add_node(block);
        self.addr_to_node.insert(addr, idx);
        idx
    }

    /// Recompute every edge from the terminators the blocks currently carry.
    ///
    /// Edges are a function of the terminators, so a caller that assembles
    /// blocks itself gets the same graph the block reader builds rather than a
    /// second way of connecting them.
    pub fn rebuild_edges(&mut self) {
        let mut addrs: Vec<u64> = self.addr_to_node.keys().copied().collect();
        addrs.sort_unstable();
        for addr in addrs {
            self.add_edges_for_block(addr);
        }
    }

    /// Add edges for a block based on its terminator.
    fn add_edges_for_block(&mut self, addr: u64) {
        let node_idx = match self.addr_to_node.get(&addr) {
            Some(&idx) => idx,
            None => return,
        };

        let block = &self.graph[node_idx];
        let terminator = block.terminator.clone();

        match terminator {
            BlockTerminator::Fallthrough { next } | BlockTerminator::Branch { target: next } => {
                if let Some(&target_idx) = self.addr_to_node.get(&next) {
                    self.graph.add_edge(node_idx, target_idx, CFGEdge::Normal);
                }
            }
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => {
                if true_target == false_target {
                    if let Some(&target_idx) = self.addr_to_node.get(&true_target) {
                        self.graph.add_edge(node_idx, target_idx, CFGEdge::Normal);
                    }
                } else {
                    if let Some(&true_idx) = self.addr_to_node.get(&true_target) {
                        self.graph.add_edge(node_idx, true_idx, CFGEdge::True);
                    }
                    if let Some(&false_idx) = self.addr_to_node.get(&false_target) {
                        self.graph.add_edge(node_idx, false_idx, CFGEdge::False);
                    }
                }
            }
            BlockTerminator::Call { fallthrough, .. }
            | BlockTerminator::IndirectCall { fallthrough } => {
                if let Some(ft) = fallthrough
                    && let Some(&ft_idx) = self.addr_to_node.get(&ft)
                {
                    self.graph.add_edge(node_idx, ft_idx, CFGEdge::Normal);
                }
            }
            BlockTerminator::Switch { ref cases, default } => {
                // Add edges for each switch case
                for (_, target) in cases {
                    if let Some(&target_idx) = self.addr_to_node.get(target) {
                        self.graph.add_edge(node_idx, target_idx, CFGEdge::Normal);
                    }
                }
                // Add edge for default case
                if let Some(def) = default
                    && let Some(&def_idx) = self.addr_to_node.get(&def)
                {
                    self.graph.add_edge(node_idx, def_idx, CFGEdge::Normal);
                }
            }
            BlockTerminator::IndirectBranch | BlockTerminator::Return | BlockTerminator::None => {
                // No edges to add
            }
        }
    }

    /// Get a block by its address.
    pub fn get_block(&self, addr: u64) -> Option<&BasicBlock> {
        self.addr_to_node.get(&addr).map(|&idx| &self.graph[idx])
    }

    /// Get a mutable reference to a block by its address.
    pub fn get_block_mut(&mut self, addr: u64) -> Option<&mut BasicBlock> {
        self.addr_to_node
            .get(&addr)
            .copied()
            .map(|idx| &mut self.graph[idx])
    }

    /// Get the node index for a block address.
    pub fn get_node(&self, addr: u64) -> Option<NodeIndex> {
        self.addr_to_node.get(&addr).copied()
    }

    /// Get the entry block.
    pub fn entry_block(&self) -> Option<&BasicBlock> {
        self.get_block(self.entry)
    }

    /// Get all block addresses in the CFG.
    pub fn block_addrs(&self) -> impl Iterator<Item = u64> + '_ {
        let mut addrs: Vec<u64> = self.addr_to_node.keys().copied().collect();
        addrs.sort_unstable();
        addrs.into_iter()
    }

    /// Get all blocks in the CFG.
    pub fn blocks(&self) -> impl Iterator<Item = &BasicBlock> {
        self.graph.node_weights()
    }

    /// Get the number of blocks.
    pub fn num_blocks(&self) -> usize {
        self.graph.node_count()
    }

    /// Get the number of edges.
    pub fn num_edges(&self) -> usize {
        self.graph.edge_count()
    }

    /// Get the predecessors of a block.
    pub fn predecessors(&self, addr: u64) -> Vec<u64> {
        let Some(&node_idx) = self.addr_to_node.get(&addr) else {
            return vec![];
        };

        let mut preds: Vec<_> = self
            .graph
            .edges_directed(node_idx, Direction::Incoming)
            .map(|edge| self.graph[edge.source()].addr)
            .collect();
        preds.sort_unstable();
        preds
    }

    /// Get the successors of a block.
    pub fn successors(&self, addr: u64) -> Vec<u64> {
        let Some(&node_idx) = self.addr_to_node.get(&addr) else {
            return vec![];
        };

        let mut succs: Vec<_> = self
            .graph
            .edges_directed(node_idx, Direction::Outgoing)
            .map(|edge| {
                (
                    Self::edge_sort_rank(*edge.weight()),
                    self.graph[edge.target()].addr,
                )
            })
            .collect();
        succs.sort_unstable();
        succs.into_iter().map(|(_, addr)| addr).collect()
    }

    /// Get the edge type between two blocks.
    pub fn edge_type(&self, from: u64, to: u64) -> Option<CFGEdge> {
        let from_idx = self.addr_to_node.get(&from)?;
        let to_idx = self.addr_to_node.get(&to)?;
        self.graph
            .find_edge(*from_idx, *to_idx)
            .map(|e| self.graph[e])
    }

    /// Iterate over blocks in reverse post-order (topological order for acyclic parts).
    pub fn reverse_postorder(&self) -> Vec<u64> {
        let Some(&entry_idx) = self.addr_to_node.get(&self.entry) else {
            return vec![];
        };

        let mut visited = HashSet::new();
        let mut postorder = Vec::new();

        self.dfs_postorder(entry_idx, &mut visited, &mut postorder);

        postorder.reverse();
        postorder
    }

    /// DFS helper for postorder traversal.
    fn dfs_postorder(
        &self,
        node: NodeIndex,
        visited: &mut HashSet<NodeIndex>,
        postorder: &mut Vec<u64>,
    ) {
        let mut stack = vec![(node, false)];
        while let Some((node, expanded)) = stack.pop() {
            if expanded {
                postorder.push(self.graph[node].addr);
                continue;
            }
            if !visited.insert(node) {
                continue;
            }

            stack.push((node, true));
            for succ_addr in self.successors(self.graph[node].addr).into_iter().rev() {
                if let Some(succ) = self.get_node(succ_addr) {
                    stack.push((succ, false));
                }
            }
        }
    }

    /// Get the underlying petgraph for advanced algorithms.
    pub fn graph(&self) -> &DiGraph<BasicBlock, CFGEdge> {
        &self.graph
    }

    /// Check if there's an edge from one block to another.
    pub fn has_edge(&self, from: u64, to: u64) -> bool {
        self.edge_type(from, to).is_some()
    }

    /// Remove all edges from `from` to `to`.
    pub fn remove_edge(&mut self, from: u64, to: u64) {
        let Some(&from_idx) = self.addr_to_node.get(&from) else {
            return;
        };
        let Some(&to_idx) = self.addr_to_node.get(&to) else {
            return;
        };

        while let Some(edge) = self.graph.find_edge(from_idx, to_idx) {
            self.graph.remove_edge(edge);
        }
    }

    /// Remove a block node and all incident edges.
    pub fn remove_block(&mut self, addr: u64) {
        let Some(idx) = self.addr_to_node.remove(&addr) else {
            return;
        };
        self.graph.remove_node(idx);
        // petgraph may swap node indices during removal.
        self.rebuild_addr_map();
    }

    /// Replace the terminator for a block.
    pub fn set_terminator(&mut self, addr: u64, terminator: BlockTerminator) {
        let Some(&node_idx) = self.addr_to_node.get(&addr) else {
            return;
        };

        let outgoing: Vec<_> = self
            .graph
            .edges_directed(node_idx, Direction::Outgoing)
            .map(|edge| edge.id())
            .collect();
        for edge in outgoing {
            self.graph.remove_edge(edge);
        }

        if let Some(block) = self.get_block_mut(addr) {
            block.terminator = terminator;
        }
        self.add_edges_for_block(addr);
    }

    fn rebuild_addr_map(&mut self) {
        self.addr_to_node.clear();
        for idx in self.graph.node_indices() {
            self.addr_to_node.insert(self.graph[idx].addr, idx);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{OpMetadata, R2ILBlock, R2ILOp, SpaceId, Varnode};

    fn make_const(val: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: val,
            size,
            meta: None,
        }
    }

    fn make_ram(addr: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Ram,
            offset: addr,
            size,
            meta: None,
        }
    }

    #[test]
    fn test_basic_block_fallthrough() {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Nop],
            switch_info: None,
            op_metadata: Default::default(),
        };

        let bb = BasicBlock::from_r2il(&block);
        assert_eq!(bb.addr, 0x1000);
        assert_eq!(bb.terminator, BlockTerminator::Fallthrough { next: 0x1004 });
        assert_eq!(bb.successors(), vec![0x1004]);
    }

    #[test]
    fn test_basic_block_branch() {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Branch {
                target: make_const(0x2000, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };

        let bb = BasicBlock::from_r2il(&block);
        assert_eq!(bb.terminator, BlockTerminator::Branch { target: 0x2000 });
        assert_eq!(bb.successors(), vec![0x2000]);
    }

    #[test]
    fn test_basic_block_cbranch() {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::CBranch {
                target: make_const(0x2000, 8),
                cond: make_const(1, 1),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };

        let bb = BasicBlock::from_r2il(&block);
        assert_eq!(
            bb.terminator,
            BlockTerminator::ConditionalBranch {
                true_target: 0x2000,
                false_target: 0x1004,
            }
        );
        assert_eq!(bb.successors(), vec![0x2000, 0x1004]);
    }

    #[test]
    fn test_basic_block_return() {
        let block = R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };

        let bb = BasicBlock::from_r2il(&block);
        assert_eq!(bb.terminator, BlockTerminator::Return);
        assert!(bb.successors().is_empty());
    }

    #[test]
    fn test_cfg_simple() {
        // Create a simple CFG: entry -> block1 -> exit
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Nop],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let cfg = CFG::from_blocks(&blocks).unwrap();
        assert_eq!(cfg.entry, 0x1000);
        assert_eq!(cfg.num_blocks(), 2);
        assert_eq!(cfg.successors(0x1000), vec![0x1004]);
        assert!(cfg.successors(0x1004).is_empty());
        assert_eq!(cfg.predecessors(0x1004), vec![0x1000]);
    }

    #[test]
    fn test_cfg_diamond() {
        // Create a diamond CFG:
        //     entry (0x1000)
        //     /    \
        //  left   right
        // (0x1004) (0x1008)
        //     \    /
        //      exit (0x100c)
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1008, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x100c, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Nop],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let cfg = CFG::from_blocks(&blocks).unwrap();
        assert_eq!(cfg.num_blocks(), 4);

        // Entry has two successors
        let entry_succs = cfg.successors(0x1000);
        assert_eq!(entry_succs.len(), 2);
        assert!(entry_succs.contains(&0x1004)); // false branch
        assert!(entry_succs.contains(&0x1008)); // true branch

        // Exit has two predecessors
        let exit_preds = cfg.predecessors(0x100c);
        assert_eq!(exit_preds.len(), 2);

        // Preserve DFS successor visitation (true before false) and the
        // resulting deterministic reverse postorder.
        assert_eq!(
            cfg.reverse_postorder(),
            vec![0x1000, 0x1004, 0x1008, 0x100c]
        );
    }

    #[test]
    fn test_reverse_postorder() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Nop],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let cfg = CFG::from_blocks(&blocks).unwrap();
        let rpo = cfg.reverse_postorder();
        assert_eq!(rpo, vec![0x1000, 0x1004]);
    }

    #[test]
    fn reverse_postorder_handles_a_deep_linear_cfg() {
        const BLOCK_COUNT: usize = 8_192;
        const BASE: u64 = 0x1000;

        let blocks = (0..BLOCK_COUNT)
            .map(|index| R2ILBlock {
                addr: BASE + index as u64 * 4,
                size: 4,
                ops: if index + 1 == BLOCK_COUNT {
                    vec![R2ILOp::Return {
                        target: make_ram(0, 8),
                    }]
                } else {
                    vec![R2ILOp::Nop]
                },
                switch_info: None,
                op_metadata: Default::default(),
            })
            .collect::<Vec<_>>();
        let expected = blocks.iter().map(|block| block.addr).collect::<Vec<_>>();

        let cfg = CFG::from_blocks(&blocks).expect("deep linear CFG");

        assert_eq!(cfg.reverse_postorder(), expected);
    }

    #[test]
    fn test_remove_edge() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1008, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut cfg = CFG::from_blocks(&blocks).unwrap();
        assert!(cfg.has_edge(0x1000, 0x1004));
        cfg.remove_edge(0x1000, 0x1004);
        assert!(!cfg.has_edge(0x1000, 0x1004));
        assert!(cfg.has_edge(0x1000, 0x1008));
    }

    #[test]
    fn test_remove_block_rebuilds_addr_map() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1008, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut cfg = CFG::from_blocks(&blocks).unwrap();
        cfg.remove_block(0x1004);
        assert!(cfg.get_block(0x1004).is_none());
        assert!(cfg.get_block(0x1000).is_some());
        assert!(cfg.get_block(0x1008).is_some());
    }

    #[test]
    fn test_set_terminator() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Nop],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut cfg = CFG::from_blocks(&blocks).unwrap();
        cfg.set_terminator(0x1000, BlockTerminator::Branch { target: 0x1004 });
        assert_eq!(
            cfg.get_block(0x1000).map(|b| b.terminator.clone()),
            Some(BlockTerminator::Branch { target: 0x1004 })
        );
        assert_eq!(cfg.successors(0x1000), vec![0x1004]);
        assert_eq!(cfg.predecessors(0x1004), vec![0x1000]);
    }

    #[test]
    fn test_successors_are_deterministic_true_then_false() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1008, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let cfg = CFG::from_blocks(&blocks).unwrap();
        assert_eq!(cfg.successors(0x1000), vec![0x1008, 0x1004]);
        assert_eq!(
            cfg.block_addrs().collect::<Vec<_>>(),
            vec![0x1000, 0x1004, 0x1008]
        );
    }

    #[test]
    fn test_internal_pcode_branch_target_splits_block() {
        let mut op_metadata = std::collections::BTreeMap::new();
        for op_idx in 0..3 {
            op_metadata.insert(
                op_idx,
                OpMetadata {
                    instruction_addr: Some(0x1000),
                    ..Default::default()
                },
            );
        }
        op_metadata.insert(
            3,
            OpMetadata {
                instruction_addr: Some(0x1004),
                ..Default::default()
            },
        );

        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 8,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_ram(0x3000, 8),
                    src: make_const(1, 8),
                },
                R2ILOp::CBranch {
                    target: make_ram(0x1004, 8),
                    cond: make_const(1, 1),
                },
                R2ILOp::Copy {
                    dst: make_ram(0x3008, 8),
                    src: make_const(2, 8),
                },
                R2ILOp::Return {
                    target: make_ram(0, 8),
                },
            ],
            switch_info: None,
            op_metadata,
        }];

        let cfg = CFG::from_blocks(&blocks).expect("cfg");
        assert_eq!(cfg.block_addrs().collect::<Vec<_>>(), vec![0x1000, 0x1004]);
        assert_eq!(cfg.get_block(0x1000).expect("entry").ops.len(), 3);
        assert_eq!(cfg.get_block(0x1004).expect("target").ops.len(), 1);
        assert_eq!(cfg.successors(0x1000), vec![0x1004]);
        assert_eq!(cfg.predecessors(0x1004), vec![0x1000]);
    }

    #[test]
    fn test_internal_conditional_fallthrough_splits_block() {
        let mut op_metadata = std::collections::BTreeMap::new();
        for (op_idx, instruction_addr) in [
            (0, 0x1000),
            (1, 0x1004),
            (2, 0x1008),
            (3, 0x100c),
            (4, 0x1010),
            (5, 0x1014),
        ] {
            op_metadata.insert(
                op_idx,
                OpMetadata {
                    instruction_addr: Some(instruction_addr),
                    ..Default::default()
                },
            );
        }

        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 0x18,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_ram(0x3000, 8),
                    src: make_const(1, 8),
                },
                R2ILOp::CBranch {
                    target: make_ram(0x1010, 8),
                    cond: make_const(1, 1),
                },
                R2ILOp::Copy {
                    dst: make_ram(0x3000, 8),
                    src: make_const(0, 8),
                },
                R2ILOp::Branch {
                    target: make_ram(0x1014, 8),
                },
                R2ILOp::Copy {
                    dst: make_ram(0x3000, 8),
                    src: make_const(2, 8),
                },
                R2ILOp::Return {
                    target: make_ram(0, 8),
                },
            ],
            switch_info: None,
            op_metadata,
        }];

        let cfg = CFG::from_blocks(&blocks).expect("cfg");
        assert_eq!(
            cfg.block_addrs().collect::<Vec<_>>(),
            vec![0x1000, 0x1008, 0x1010, 0x1014]
        );
        assert_eq!(
            cfg.get_block(0x1000).expect("entry").terminator,
            BlockTerminator::ConditionalBranch {
                true_target: 0x1010,
                false_target: 0x1008
            }
        );
        assert_eq!(cfg.successors(0x1000), vec![0x1010, 0x1008]);
        assert_eq!(cfg.successors(0x1008), vec![0x1014]);
        assert_eq!(cfg.successors(0x1010), vec![0x1014]);
    }
}
