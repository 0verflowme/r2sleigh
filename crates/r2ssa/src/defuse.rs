//! Def-use chain analysis for SSA blocks.

use std::collections::{HashMap, HashSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::SSABlock;
use crate::function::{DefLocation, SSAFunction};
use crate::op::SSAOp;
use crate::var::SSAVar;

/// Information about where a variable is defined and used.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DefUseInfo {
    /// Presentation-only map from displayed variable names to definition sites.
    ///
    /// A displayed name that identifies multiple exact variables is retained
    /// with no definition instead of selecting one of them as authoritative.
    pub definitions: HashMap<String, Option<usize>>,

    /// Presentation-only map from displayed variable names to use sites.
    pub uses: HashMap<String, Vec<usize>>,

    /// Presentation names of variables that are inputs.
    pub inputs: HashSet<String>,

    /// Presentation names of variables that are outputs.
    pub outputs: HashSet<String>,

    /// Presentation names of variables that are live.
    pub live: HashSet<String>,

    /// Exact semantic def-use state. These fields are rebuilt by [`def_use`]
    /// and intentionally excluded from the legacy presentation serialization.
    #[serde(skip)]
    exact_definitions: HashMap<SSAVar, Option<usize>>,
    #[serde(skip)]
    exact_uses: HashMap<SSAVar, Vec<usize>>,
    #[serde(skip)]
    exact_inputs: HashSet<SSAVar>,
    #[serde(skip)]
    exact_outputs: HashSet<SSAVar>,
    #[serde(skip)]
    exact_live: HashSet<SSAVar>,
}

impl DefUseInfo {
    /// Create a new empty def-use info.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the definition site of a variable.
    pub fn get_def(&self, var: &SSAVar) -> Option<usize> {
        self.exact_definitions.get(var).copied().flatten()
    }

    /// Get all use sites of a variable.
    pub fn get_uses(&self, var: &SSAVar) -> &[usize] {
        self.exact_uses
            .get(var)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Check if a variable is an input to this block.
    pub fn is_input(&self, var: &SSAVar) -> bool {
        self.exact_inputs.contains(var)
    }

    /// Check if a variable is an output from this block.
    pub fn is_output(&self, var: &SSAVar) -> bool {
        self.exact_outputs.contains(var)
    }

    /// Check if a variable is live (both defined and used).
    pub fn is_live(&self, var: &SSAVar) -> bool {
        self.exact_live.contains(var)
    }

    /// Get all input variable names.
    pub fn input_vars(&self) -> impl Iterator<Item = &str> {
        self.inputs.iter().map(|s| s.as_str())
    }

    /// Get all output variable names.
    pub fn output_vars(&self) -> impl Iterator<Item = &str> {
        self.outputs.iter().map(|s| s.as_str())
    }

    fn rebuild_presentation(&mut self) {
        self.definitions.clear();
        self.uses.clear();
        self.inputs.clear();
        self.outputs.clear();
        self.live.clear();

        for (var, definition) in &self.exact_definitions {
            self.definitions
                .entry(var.display_name())
                .and_modify(|existing| {
                    if *existing != *definition {
                        *existing = None;
                    }
                })
                .or_insert(*definition);
        }
        for (var, uses) in &self.exact_uses {
            let displayed_uses = self.uses.entry(var.display_name()).or_default();
            displayed_uses.extend(uses);
            displayed_uses.sort_unstable();
            displayed_uses.dedup();
        }
        self.inputs
            .extend(self.exact_inputs.iter().map(SSAVar::display_name));
        self.outputs
            .extend(self.exact_outputs.iter().map(SSAVar::display_name));
        self.live
            .extend(self.exact_live.iter().map(SSAVar::display_name));
    }
}

/// Reference to an SSA operation or phi node in a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SliceOpRef {
    /// Phi node at the given index in the block.
    Phi { block_addr: u64, phi_idx: usize },
    /// Operation at the given index in the block.
    Op { block_addr: u64, op_idx: usize },
}

impl SliceOpRef {
    /// Get the block address for this reference.
    pub fn block_addr(&self) -> u64 {
        match self {
            SliceOpRef::Phi { block_addr, .. } | SliceOpRef::Op { block_addr, .. } => *block_addr,
        }
    }
}

/// Result of a backward slice: SSA operations and blocks that affect a sink.
#[derive(Debug, Clone, Default)]
pub struct BackwardSlice {
    /// Operations (including phi nodes) in the slice.
    pub ops: HashSet<SliceOpRef>,
    /// Blocks that contain slice operations.
    pub blocks: HashSet<u64>,
}

impl BackwardSlice {
    /// Insert an operation into the slice and track its block.
    pub fn add_op(&mut self, op: SliceOpRef) -> bool {
        let inserted = self.ops.insert(op);
        if inserted {
            self.blocks.insert(op.block_addr());
        }
        inserted
    }

    /// Check if the slice is empty.
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }
}

/// Compute def-use chains for an SSA block.
///
/// This analyzes which operations define and use each variable,
/// and identifies inputs (used but not defined) and outputs
/// (defined but not used).
pub fn def_use(block: &SSABlock) -> DefUseInfo {
    let mut info = DefUseInfo::new();

    // First pass: record all definitions
    for (idx, op) in block.ops.iter().enumerate() {
        if let Some(dst) = op.dst() {
            info.exact_definitions.insert(dst.clone(), Some(idx));
        }
    }

    // Second pass: record all uses
    for (idx, op) in block.ops.iter().enumerate() {
        for src in op.sources() {
            info.exact_uses.entry(src.clone()).or_default().push(idx);
        }
    }

    // Identify inputs: variables that are used but not defined
    for var in info.exact_uses.keys() {
        if !info.exact_definitions.contains_key(var) {
            info.exact_inputs.insert(var.clone());
            // Also record that this variable has no definition
            info.exact_definitions.insert(var.clone(), None);
        }
    }

    // Identify outputs: variables that are defined but not used
    for (var, def) in &info.exact_definitions {
        if def.is_some() && !info.exact_uses.contains_key(var) {
            info.exact_outputs.insert(var.clone());
        }
    }

    // Identify live variables: defined and used
    for (var, def) in &info.exact_definitions {
        if def.is_some() && info.exact_uses.contains_key(var) {
            info.exact_live.insert(var.clone());
        }
    }

    info.rebuild_presentation();

    info
}

#[derive(Debug, Clone)]
struct StoreInfo {
    block_addr: u64,
    op_idx: usize,
    space: r2il::SpaceId,
    addr: SSAVar,
    val: SSAVar,
    access_size: u32,
}

fn collect_store_infos(func: &SSAFunction) -> Vec<StoreInfo> {
    let mut stores = Vec::new();

    for block in func.blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            if let SSAOp::Store { space, addr, val } = op {
                stores.push(StoreInfo {
                    block_addr: block.addr,
                    op_idx,
                    space: *space,
                    addr: addr.clone(),
                    val: val.clone(),
                    access_size: val.size,
                });
            }
        }
    }

    stores
}

fn const_value(var: &SSAVar) -> Option<u64> {
    var.constant_bits()
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AddressProvenance {
    absolute: Option<u64>,
}

fn detect_address_provenance(var: &SSAVar) -> AddressProvenance {
    AddressProvenance {
        absolute: const_value(var),
    }
}

fn ranges_overlap(a_base: i128, a_size: u32, b_base: i128, b_size: u32) -> bool {
    let a_end = a_base + i128::from(a_size.max(1));
    let b_end = b_base + i128::from(b_size.max(1));
    a_base < b_end && b_base < a_end
}

fn addresses_may_alias(a: &SSAVar, a_size: u32, b: &SSAVar, b_size: u32) -> bool {
    let pa = detect_address_provenance(a);
    let pb = detect_address_provenance(b);

    if let (Some(a_abs), Some(b_abs)) = (pa.absolute, pb.absolute) {
        return ranges_overlap(i128::from(a_abs), a_size, i128::from(b_abs), b_size);
    }

    true
}

fn add_aliasing_stores(
    slice: &mut BackwardSlice,
    worklist: &mut VecDeque<SSAVar>,
    stores: &[StoreInfo],
    sink_space: r2il::SpaceId,
    sink_addr: &SSAVar,
    sink_access_size: u32,
) {
    for store in stores {
        if store.space != sink_space {
            continue;
        }
        if !addresses_may_alias(&store.addr, store.access_size, sink_addr, sink_access_size) {
            continue;
        }
        if slice.add_op(SliceOpRef::Op {
            block_addr: store.block_addr,
            op_idx: store.op_idx,
        }) {
            worklist.push_back(store.addr.clone());
            worklist.push_back(store.val.clone());
        }
    }
}

fn walk_backward(
    func: &SSAFunction,
    stores: &[StoreInfo],
    slice: &mut BackwardSlice,
    worklist: &mut VecDeque<SSAVar>,
    visited_vars: &mut HashSet<SSAVar>,
) {
    while let Some(var) = worklist.pop_front() {
        if !visited_vars.insert(var.clone()) {
            continue;
        }

        let Some((block_addr, def_loc)) = func.find_def(&var) else {
            continue;
        };

        match def_loc {
            DefLocation::Phi(phi_idx) => {
                if slice.add_op(SliceOpRef::Phi {
                    block_addr,
                    phi_idx,
                }) && let Some(block) = func.get_block(block_addr)
                    && let Some(phi) = block.phis.get(phi_idx)
                {
                    for (_, src) in &phi.sources {
                        worklist.push_back(src.clone());
                    }
                }
            }
            DefLocation::Op(op_idx) => {
                if slice.add_op(SliceOpRef::Op { block_addr, op_idx })
                    && let Some(block) = func.get_block(block_addr)
                    && let Some(op) = block.ops.get(op_idx)
                {
                    for src in op.sources() {
                        worklist.push_back(src.clone());
                    }
                    if let SSAOp::Load { space, addr, dst } = op {
                        add_aliasing_stores(slice, worklist, stores, *space, addr, dst.size);
                    }
                }
            }
        }
    }
}

/// Compute a backward slice starting from a sink variable.
pub fn backward_slice_from_var(func: &SSAFunction, sink: &SSAVar) -> BackwardSlice {
    let stores = collect_store_infos(func);
    let mut slice = BackwardSlice::default();
    let mut worklist = VecDeque::new();
    let mut visited_vars = HashSet::new();

    worklist.push_back(sink.clone());
    walk_backward(func, &stores, &mut slice, &mut worklist, &mut visited_vars);

    slice
}

/// Compute a backward slice starting from a specific SSA operation.
pub fn backward_slice_from_op(func: &SSAFunction, sink: SliceOpRef) -> BackwardSlice {
    let stores = collect_store_infos(func);
    let mut slice = BackwardSlice::default();
    let mut worklist = VecDeque::new();
    let mut visited_vars = HashSet::new();

    match sink {
        SliceOpRef::Phi {
            block_addr,
            phi_idx,
        } => {
            if let Some(block) = func.get_block(block_addr)
                && let Some(phi) = block.phis.get(phi_idx)
            {
                slice.add_op(SliceOpRef::Phi {
                    block_addr,
                    phi_idx,
                });
                for (_, src) in &phi.sources {
                    worklist.push_back(src.clone());
                }
            }
        }
        SliceOpRef::Op { block_addr, op_idx } => {
            if let Some(block) = func.get_block(block_addr)
                && let Some(op) = block.ops.get(op_idx)
            {
                slice.add_op(SliceOpRef::Op { block_addr, op_idx });
                for src in op.sources() {
                    worklist.push_back(src.clone());
                }
                if let SSAOp::Load { space, addr, dst } = op {
                    add_aliasing_stores(&mut slice, &mut worklist, &stores, *space, addr, dst.size);
                }
                if let SSAOp::Store { space, addr, val } = op {
                    add_aliasing_stores(&mut slice, &mut worklist, &stores, *space, addr, val.size);
                }
            }
        }
    }

    walk_backward(func, &stores, &mut slice, &mut worklist, &mut visited_vars);

    slice
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SSAFunction;
    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};

    fn make_var(name: &str, version: u32, size: u32) -> SSAVar {
        SSAVar::new(name, version, size)
    }

    fn make_const_vn(val: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: val,
            size,
            meta: None,
        }
    }

    fn make_reg_vn(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    #[test]
    fn test_def_use_simple() {
        let mut block = SSABlock::new(0x1000, 4);

        // RAX_0 is input, RAX_1 = RAX_0 + RBX_0
        let rax_0 = make_var("RAX", 0, 8);
        let rbx_0 = make_var("RBX", 0, 8);
        let rax_1 = make_var("RAX", 1, 8);

        block.push(SSAOp::IntAdd {
            dst: rax_1.clone(),
            a: rax_0.clone(),
            b: rbx_0.clone(),
        });

        let info = def_use(&block);

        // RAX_0 and RBX_0 are inputs (used but not defined)
        assert!(info.is_input(&rax_0));
        assert!(info.is_input(&rbx_0));

        // RAX_1 is output (defined but not used)
        assert!(info.is_output(&rax_1));

        // RAX_1 is defined at op 0
        assert_eq!(info.get_def(&rax_1), Some(0));

        // RAX_0 is used at op 0
        assert_eq!(info.get_uses(&rax_0), &[0]);
    }

    #[test]
    fn test_def_use_chain() {
        let mut block = SSABlock::new(0x1000, 8);

        let rax_0 = make_var("RAX", 0, 8);
        let rax_1 = make_var("RAX", 1, 8);
        let rax_2 = make_var("RAX", 2, 8);
        let rbx_0 = make_var("RBX", 0, 8);

        // RAX_1 = RAX_0 + 1
        block.push(SSAOp::IntAdd {
            dst: rax_1.clone(),
            a: rax_0.clone(),
            b: SSAVar::constant(1, 8),
        });

        // RAX_2 = RAX_1 + RBX_0
        block.push(SSAOp::IntAdd {
            dst: rax_2.clone(),
            a: rax_1.clone(),
            b: rbx_0.clone(),
        });

        let info = def_use(&block);

        // RAX_1 is live (defined at 0, used at 1)
        assert!(info.is_live(&rax_1));
        assert_eq!(info.get_def(&rax_1), Some(0));
        assert_eq!(info.get_uses(&rax_1), &[1]);

        // RAX_2 is output (defined but not used)
        assert!(info.is_output(&rax_2));
    }

    #[test]
    fn test_backward_slice_var_chain() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg_vn(0, 8),
                    src: make_const_vn(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::IntAdd {
                    dst: make_reg_vn(8, 8),
                    a: make_reg_vn(0, 8),
                    b: make_const_vn(2, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).unwrap();
        let block = func.get_block(0x1004).unwrap();
        let dst = block.ops[0].dst().unwrap().clone();

        let slice = backward_slice_from_var(&func, &dst);
        assert!(slice.ops.contains(&SliceOpRef::Op {
            block_addr: 0x1004,
            op_idx: 0
        }));
        assert!(slice.ops.contains(&SliceOpRef::Op {
            block_addr: 0x1000,
            op_idx: 0
        }));
    }

    #[test]
    fn backward_slice_visits_distinct_vars_with_colliding_display_names() {
        let raw = R2ILBlock {
            addr: 0x1800,
            size: 4,
            ops: vec![R2ILOp::Copy {
                dst: make_reg_vn(0, 8),
                src: make_const_vn(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        };
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[raw]).unwrap();
        let left = make_var("spoof", 1, 8);
        let right = make_var("SPOOF", 1, 8);
        let sink = make_var("sink", 1, 8);
        assert_eq!(left.display_name(), right.display_name());
        assert_ne!(left, right);
        func.get_block_mut(0x1800).unwrap().ops = vec![
            SSAOp::Copy {
                dst: left.clone(),
                src: SSAVar::constant(1, 8),
            },
            SSAOp::Copy {
                dst: right.clone(),
                src: SSAVar::constant(2, 8),
            },
            SSAOp::IntAdd {
                dst: sink.clone(),
                a: left,
                b: right,
            },
        ];

        let from_var = backward_slice_from_var(&func, &sink);
        let from_op = backward_slice_from_op(
            &func,
            SliceOpRef::Op {
                block_addr: 0x1800,
                op_idx: 2,
            },
        );
        for slice in [&from_var, &from_op] {
            for op_idx in 0..=2 {
                assert!(slice.ops.contains(&SliceOpRef::Op {
                    block_addr: 0x1800,
                    op_idx,
                }));
            }
        }
    }

    #[test]
    fn test_backward_slice_memory_alias() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x2000,
                size: 4,
                ops: vec![R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: make_const_vn(0x1000, 8),
                    val: make_reg_vn(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x2004,
                size: 4,
                ops: vec![R2ILOp::Load {
                    dst: make_reg_vn(8, 8),
                    space: SpaceId::Ram,
                    addr: make_const_vn(0x1000, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).unwrap();
        let block = func.get_block(0x2004).unwrap();
        let dst = block.ops[0].dst().unwrap().clone();

        let slice = backward_slice_from_var(&func, &dst);
        assert!(slice.ops.contains(&SliceOpRef::Op {
            block_addr: 0x2004,
            op_idx: 0
        }));
        assert!(slice.ops.contains(&SliceOpRef::Op {
            block_addr: 0x2000,
            op_idx: 0
        }));
    }

    #[test]
    fn test_alias_provenance_refuses_textual_stack_and_global_names() {
        let stack_addr = make_var("stack:rbp:-0x10", 0, 8);
        let global_addr = make_var("ram:0x401000", 0, 8);
        assert!(
            addresses_may_alias(&stack_addr, 8, &global_addr, 8),
            "display names alone cannot establish disjoint address regions"
        );
    }

    #[test]
    fn test_alias_provenance_refuses_spoofed_constant_names() {
        let base = make_var("const:1000", 0, 8);
        let far = make_var("const:1100", 0, 8);
        assert!(
            addresses_may_alias(&base, 8, &far, 8),
            "display-only constants cannot prove disjoint address ranges"
        );
    }

    #[test]
    fn test_alias_range_overlap_for_adjacent_constants() {
        let base = SSAVar::constant(0x1000, 8);
        let near = SSAVar::constant(0x1004, 8);
        let far = SSAVar::constant(0x1100, 8);
        assert!(
            addresses_may_alias(&base, 8, &near, 8),
            "constant ranges that overlap should alias"
        );
        assert!(
            !addresses_may_alias(&base, 8, &far, 8),
            "distant constant ranges should not alias"
        );
    }
}
