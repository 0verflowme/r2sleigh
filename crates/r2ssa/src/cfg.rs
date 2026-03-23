//! Control Flow Graph (CFG) representation for r2il.
//!
//! This module provides a CFG data structure built from r2il blocks,
//! which is the foundation for inter-procedural SSA analysis.

use std::collections::{HashMap, HashSet};

use petgraph::Direction;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::EdgeRef;
use r2il::{R2ILBlock, R2ILOp};
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
        }
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

        // First pass: add all blocks as nodes
        for block in blocks {
            let bb = BasicBlock::from_r2il(block);
            cfg.add_block(bb);
        }

        // Second pass: add edges based on terminators
        let mut addrs: Vec<u64> = cfg.addr_to_node.keys().copied().collect();
        addrs.sort_unstable();
        for addr in addrs {
            cfg.add_edges_for_block(addr);
        }

        Some(cfg)
    }

    /// Add a basic block to the CFG.
    pub fn add_block(&mut self, block: BasicBlock) -> NodeIndex {
        let addr = block.addr;
        let idx = self.graph.add_node(block);
        self.addr_to_node.insert(addr, idx);
        idx
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
                if let Some(&true_idx) = self.addr_to_node.get(&true_target) {
                    self.graph.add_edge(node_idx, true_idx, CFGEdge::True);
                }
                if let Some(&false_idx) = self.addr_to_node.get(&false_target) {
                    self.graph.add_edge(node_idx, false_idx, CFGEdge::False);
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
        if !visited.insert(node) {
            return;
        }

        for succ_addr in self.successors(self.graph[node].addr) {
            if let Some(succ) = self.get_node(succ_addr) {
                self.dfs_postorder(succ, visited, postorder);
            }
        }

        postorder.push(self.graph[node].addr);
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
    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};

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
}
