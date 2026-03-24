//! Dominator tree computation for control flow graphs.
//!
//! This module implements the Lengauer-Tarjan algorithm for computing
//! dominators and the dominance frontier, which are essential for
//! SSA phi-node placement.

use std::collections::{HashMap, HashSet};

use crate::cfg::CFG;

/// Dominator tree for a CFG.
///
/// The dominator tree captures the dominance relationship between blocks:
/// block A dominates block B if every path from the entry to B goes through A.
#[derive(Debug, Clone)]
pub struct DomTree {
    /// The entry block address.
    pub entry: u64,
    /// Immediate dominator for each block (block addr -> idom addr).
    idom: HashMap<u64, u64>,
    /// Children in the dominator tree (block addr -> children addrs).
    children: HashMap<u64, Vec<u64>>,
    /// Dominance frontier for each block.
    frontier: HashMap<u64, HashSet<u64>>,
    /// Depth of each block in the dominator tree.
    depth: HashMap<u64, usize>,
}

impl DomTree {
    /// Compute the dominator tree for a CFG using the Lengauer-Tarjan algorithm.
    pub fn compute(cfg: &CFG) -> Self {
        let mut domtree = Self {
            entry: cfg.entry,
            idom: HashMap::new(),
            children: HashMap::new(),
            frontier: HashMap::new(),
            depth: HashMap::new(),
        };

        // Get blocks in reverse postorder
        let rpo = cfg.reverse_postorder();
        if rpo.is_empty() {
            return domtree;
        }

        // Map block addresses to RPO indices
        let mut rpo_idx: HashMap<u64, usize> = HashMap::new();
        for (i, &addr) in rpo.iter().enumerate() {
            rpo_idx.insert(addr, i);
        }

        // Initialize: entry dominates itself
        domtree.idom.insert(cfg.entry, cfg.entry);

        // Iterative dominator computation (Cooper, Harvey, Kennedy algorithm)
        // This is simpler than Lengauer-Tarjan and works well for most CFGs
        let mut changed = true;
        while changed {
            changed = false;

            for &block in rpo.iter().skip(1) {
                // Skip entry block
                let preds = cfg.predecessors(block);

                // Find first processed predecessor
                let mut new_idom = None;
                for &pred in &preds {
                    if domtree.idom.contains_key(&pred) {
                        new_idom = Some(pred);
                        break;
                    }
                }

                let Some(mut new_idom) = new_idom else {
                    continue;
                };

                // Intersect with other predecessors
                for &pred in &preds {
                    if pred == new_idom {
                        continue;
                    }
                    if domtree.idom.contains_key(&pred) {
                        new_idom = domtree.intersect(pred, new_idom, &rpo_idx);
                    }
                }

                // Update if changed
                if domtree.idom.get(&block) != Some(&new_idom) {
                    domtree.idom.insert(block, new_idom);
                    changed = true;
                }
            }
        }

        // Build children map
        for (&block, &idom) in &domtree.idom {
            if block != idom {
                domtree.children.entry(idom).or_default().push(block);
            }
        }
        for children in domtree.children.values_mut() {
            children.sort_unstable();
        }

        // Compute depths
        domtree.compute_depths(cfg.entry, 0);

        // Compute dominance frontiers
        domtree.compute_frontiers(cfg);

        domtree
    }

    /// Intersect two dominators (find common dominator).
    fn intersect(&self, mut b1: u64, mut b2: u64, rpo_idx: &HashMap<u64, usize>) -> u64 {
        while b1 != b2 {
            let mut idx1 = rpo_idx.get(&b1).copied().unwrap_or(usize::MAX);
            let mut idx2 = rpo_idx.get(&b2).copied().unwrap_or(usize::MAX);

            while idx1 > idx2 {
                b1 = match self.idom.get(&b1) {
                    Some(&idom) if idom != b1 => idom,
                    _ => break,
                };
                let new_idx1 = rpo_idx.get(&b1).copied().unwrap_or(usize::MAX);
                if new_idx1 >= idx1 {
                    break;
                }
                idx1 = new_idx1;
            }

            idx1 = rpo_idx.get(&b1).copied().unwrap_or(usize::MAX);
            while idx2 > idx1 {
                b2 = match self.idom.get(&b2) {
                    Some(&idom) if idom != b2 => idom,
                    _ => break,
                };
                let new_idx2 = rpo_idx.get(&b2).copied().unwrap_or(usize::MAX);
                if new_idx2 >= idx2 {
                    break;
                }
                idx2 = new_idx2;
            }

            if b1 == b2 {
                break;
            }

            // Safety check to prevent infinite loops
            let idx1 = rpo_idx.get(&b1).copied().unwrap_or(usize::MAX);
            let idx2 = rpo_idx.get(&b2).copied().unwrap_or(usize::MAX);
            if idx1 == idx2 {
                break;
            }
        }
        b1
    }

    /// Compute depths in the dominator tree.
    fn compute_depths(&mut self, block: u64, depth: usize) {
        self.depth.insert(block, depth);
        if let Some(children) = self.children.get(&block).cloned() {
            for child in children {
                self.compute_depths(child, depth + 1);
            }
        }
    }

    /// Compute dominance frontiers using the algorithm from Cytron et al.
    fn compute_frontiers(&mut self, cfg: &CFG) {
        // Initialize empty frontiers
        for addr in cfg.block_addrs() {
            self.frontier.insert(addr, HashSet::new());
        }

        // For each block with multiple predecessors
        for addr in cfg.block_addrs() {
            let preds = cfg.predecessors(addr);
            if preds.len() >= 2 {
                // For each predecessor
                for &pred in &preds {
                    let mut runner = pred;
                    // Walk up the dominator tree
                    while runner != self.idom.get(&addr).copied().unwrap_or(addr) {
                        self.frontier.entry(runner).or_default().insert(addr);
                        runner = match self.idom.get(&runner) {
                            Some(&idom) if idom != runner => idom,
                            _ => break,
                        };
                    }
                }
            }
        }
    }

    /// Get the immediate dominator of a block.
    pub fn idom(&self, block: u64) -> Option<u64> {
        self.idom.get(&block).copied().filter(|&idom| idom != block)
    }

    /// Get the children of a block in the dominator tree.
    pub fn children(&self, block: u64) -> &[u64] {
        self.children
            .get(&block)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Get the dominance frontier of a block.
    pub fn frontier(&self, block: u64) -> impl Iterator<Item = u64> + '_ {
        let mut frontier: Vec<u64> = self
            .frontier
            .get(&block)
            .into_iter()
            .flat_map(|s| s.iter().copied())
            .collect();
        frontier.sort_unstable();
        frontier.into_iter()
    }

    /// Get the depth of a block in the dominator tree.
    pub fn depth(&self, block: u64) -> usize {
        self.depth.get(&block).copied().unwrap_or(0)
    }

    /// Check if block A dominates block B.
    pub fn dominates(&self, a: u64, b: u64) -> bool {
        if a == b {
            return true;
        }

        let mut current = b;
        while let Some(idom) = self.idom(current) {
            if idom == a {
                return true;
            }
            current = idom;
        }
        false
    }

    /// Check if block A strictly dominates block B (A dominates B and A != B).
    pub fn strictly_dominates(&self, a: u64, b: u64) -> bool {
        a != b && self.dominates(a, b)
    }

    /// Get all blocks dominated by a given block.
    pub fn dominated_by(&self, block: u64) -> Vec<u64> {
        let mut result = vec![block];
        let mut stack = vec![block];

        while let Some(current) = stack.pop() {
            for &child in self.children(current) {
                result.push(child);
                stack.push(child);
            }
        }

        result
    }

    /// Iterate over the dominator tree in preorder.
    pub fn preorder(&self) -> Vec<u64> {
        let mut result = Vec::new();
        let mut stack = vec![self.entry];

        while let Some(current) = stack.pop() {
            result.push(current);
            // Push children in reverse order for correct preorder
            let children = self.children(current);
            for &child in children.iter().rev() {
                stack.push(child);
            }
        }

        result
    }

    /// Compute the iterated dominance frontier for a set of blocks.
    ///
    /// This is used for phi-node placement: we need to place phi nodes
    /// at all blocks in the iterated dominance frontier of the definition sites.
    pub fn iterated_frontier(&self, blocks: &[u64]) -> HashSet<u64> {
        let mut result = HashSet::new();
        let mut worklist: Vec<u64> = blocks.to_vec();
        worklist.sort_unstable_by(|a, b| b.cmp(a));
        let mut processed = HashSet::new();

        while let Some(block) = worklist.pop() {
            if !processed.insert(block) {
                continue;
            }

            let mut frontier_blocks: Vec<u64> = self.frontier(block).collect();
            frontier_blocks.sort_unstable_by(|a, b| b.cmp(a));
            for frontier_block in frontier_blocks {
                if result.insert(frontier_block) {
                    worklist.push(frontier_block);
                }
            }
        }

        result
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
    fn test_domtree_linear() {
        // Linear CFG: A -> B -> C
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
                ops: vec![R2ILOp::Nop],
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
        let domtree = DomTree::compute(&cfg);

        // Entry dominates all
        assert!(domtree.dominates(0x1000, 0x1000));
        assert!(domtree.dominates(0x1000, 0x1004));
        assert!(domtree.dominates(0x1000, 0x1008));

        // B dominates C
        assert!(domtree.dominates(0x1004, 0x1008));

        // C doesn't dominate A or B
        assert!(!domtree.dominates(0x1008, 0x1000));
        assert!(!domtree.dominates(0x1008, 0x1004));

        // Immediate dominators
        assert_eq!(domtree.idom(0x1004), Some(0x1000));
        assert_eq!(domtree.idom(0x1008), Some(0x1004));
    }

    #[test]
    fn test_domtree_diamond() {
        // Diamond CFG:
        //     A (0x1000)
        //    / \
        //   B   C
        //    \ /
        //     D (0x100c)
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
        let domtree = DomTree::compute(&cfg);

        // A dominates all
        assert!(domtree.dominates(0x1000, 0x1004));
        assert!(domtree.dominates(0x1000, 0x1008));
        assert!(domtree.dominates(0x1000, 0x100c));

        // B and C don't dominate D (both paths lead to D)
        assert!(!domtree.strictly_dominates(0x1004, 0x100c));
        assert!(!domtree.strictly_dominates(0x1008, 0x100c));

        // D's immediate dominator is A
        assert_eq!(domtree.idom(0x100c), Some(0x1000));

        // Dominance frontier of B and C should include D
        assert!(domtree.frontier(0x1004).any(|x| x == 0x100c));
        assert!(domtree.frontier(0x1008).any(|x| x == 0x100c));
    }

    #[test]
    fn test_iterated_frontier() {
        // Diamond CFG
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
        let domtree = DomTree::compute(&cfg);

        // If we define a variable in B and C, we need a phi at D
        let def_sites = vec![0x1004, 0x1008];
        let idf = domtree.iterated_frontier(&def_sites);
        assert!(idf.contains(&0x100c));
    }

    #[test]
    fn test_preorder() {
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
                ops: vec![R2ILOp::Nop],
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
        let domtree = DomTree::compute(&cfg);

        let preorder = domtree.preorder();
        // Entry should be first
        assert_eq!(preorder[0], 0x1000);
        // All blocks should be present
        assert_eq!(preorder.len(), 3);
    }
}
