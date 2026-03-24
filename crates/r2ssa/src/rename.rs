//! SSA renaming algorithm.
//!
//! This module implements the SSA renaming pass that assigns version numbers
//! to variables, following the algorithm from Cytron et al.

use std::collections::{BTreeSet, HashMap};

use crate::cfg::CFG;
use crate::domtree::DomTree;
use crate::naming::{RegisterNameMap, varnode_to_name};
use crate::op::SSAOp;
use crate::phi::PhiPlacement;
use crate::var::SSAVar;

/// Context for SSA renaming.
#[derive(Debug)]
pub struct RenameContext {
    /// Stack of versions for each variable name.
    /// The top of the stack is the current version.
    stacks: HashMap<String, Vec<u32>>,
    /// Counter for generating new versions.
    counters: HashMap<String, u32>,
    /// Variable sizes.
    sizes: HashMap<String, u32>,
}

/// Decompiler-safe call boundary policy.
#[derive(Debug, Clone, Default)]
pub struct CallBoundaryConfig {
    /// Registers that must receive a fresh SSA definition after a call.
    pub defined_regs: Vec<CallBoundaryDef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallBoundaryDef {
    pub name: String,
    pub size: u32,
}

impl RenameContext {
    /// Create a new rename context.
    pub fn new() -> Self {
        Self {
            stacks: HashMap::new(),
            counters: HashMap::new(),
            sizes: HashMap::new(),
        }
    }

    /// Initialize a variable with a given size.
    pub fn init_var(&mut self, name: &str, size: u32) {
        self.sizes.insert(name.to_string(), size);
        // Start with version 0 on the stack (representing "undefined" or function entry)
        self.stacks
            .entry(name.to_string())
            .or_insert_with(|| vec![0]);
        self.counters.entry(name.to_string()).or_insert(0);
    }

    /// Get the current version of a variable (for reading).
    pub fn current_version(&self, name: &str) -> u32 {
        self.stacks
            .get(name)
            .and_then(|stack| stack.last().copied())
            .unwrap_or(0)
    }

    /// Generate a new version of a variable (for writing).
    pub fn new_version(&mut self, name: &str) -> u32 {
        let counter = self.counters.entry(name.to_string()).or_insert(0);
        *counter += 1;
        let version = *counter;
        self.stacks
            .entry(name.to_string())
            .or_default()
            .push(version);
        version
    }

    /// Pop a version from a variable's stack (when leaving a block's scope).
    pub fn pop_version(&mut self, name: &str) {
        if let Some(stack) = self.stacks.get_mut(name) {
            stack.pop();
        }
    }

    /// Get the size of a variable.
    pub fn get_size(&self, name: &str) -> u32 {
        self.sizes.get(name).copied().unwrap_or(8)
    }

    /// Create an SSAVar for reading a variable.
    pub fn read_var(&self, name: &str) -> SSAVar {
        let version = self.current_version(name);
        let size = self.get_size(name);
        SSAVar::new(name, version, size)
    }

    /// Create an SSAVar for writing a variable (generates new version).
    pub fn write_var(&mut self, name: &str) -> SSAVar {
        let version = self.new_version(name);
        let size = self.get_size(name);
        SSAVar::new(name, version, size)
    }

    /// Find initialized variable names that match a register name ignoring case.
    pub fn matching_var_names_ci(&self, name: &str) -> Vec<String> {
        let needle = name.to_ascii_lowercase();
        let mut matches: Vec<String> = self
            .sizes
            .keys()
            .filter(|candidate| candidate.to_ascii_lowercase() == needle)
            .cloned()
            .collect();
        matches.sort_unstable();
        matches
    }
}

impl Default for RenameContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of renaming a function.
#[derive(Debug, Clone)]
pub struct RenamedFunction {
    /// SSA operations for each block (block addr -> ops).
    pub blocks: HashMap<u64, Vec<SSAOp>>,
    /// Block addresses in order.
    pub block_order: Vec<u64>,
    /// Entry block address.
    pub entry: u64,
}

impl RenamedFunction {
    /// Create a new empty renamed function.
    pub fn new(entry: u64) -> Self {
        Self {
            blocks: HashMap::new(),
            block_order: Vec::new(),
            entry,
        }
    }

    /// Get the SSA operations for a block.
    pub fn get_block(&self, addr: u64) -> &[SSAOp] {
        self.blocks.get(&addr).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

/// Perform SSA renaming on a CFG.
///
/// This is the main entry point for the renaming algorithm.
pub fn rename_function(
    cfg: &CFG,
    domtree: &DomTree,
    phi_placement: &PhiPlacement,
    var_sizes: &HashMap<String, u32>,
) -> RenamedFunction {
    rename_function_with_names(cfg, domtree, phi_placement, var_sizes, None)
}

/// Perform SSA renaming on a CFG with optional register names.
pub fn rename_function_with_names(
    cfg: &CFG,
    domtree: &DomTree,
    phi_placement: &PhiPlacement,
    var_sizes: &HashMap<String, u32>,
    reg_names: Option<&RegisterNameMap>,
) -> RenamedFunction {
    rename_function_with_names_and_call_boundaries(
        cfg,
        domtree,
        phi_placement,
        var_sizes,
        reg_names,
        None,
    )
}

/// Perform SSA renaming on a CFG with optional register names and decompiler-safe call
/// boundaries.
pub fn rename_function_with_names_and_call_boundaries(
    cfg: &CFG,
    domtree: &DomTree,
    phi_placement: &PhiPlacement,
    var_sizes: &HashMap<String, u32>,
    reg_names: Option<&RegisterNameMap>,
    call_boundaries: Option<&CallBoundaryConfig>,
) -> RenamedFunction {
    let mut ctx = RenameContext::new();
    let mut result = RenamedFunction::new(cfg.entry);

    // Initialize all variables
    let mut initialized_vars: Vec<(&String, &u32)> = var_sizes.iter().collect();
    initialized_vars.sort_unstable_by(|(lhs_name, lhs_size), (rhs_name, rhs_size)| {
        lhs_name.cmp(rhs_name).then(lhs_size.cmp(rhs_size))
    });
    for (name, &size) in initialized_vars {
        ctx.init_var(name, size);
    }

    // Also initialize variables from phi nodes
    let mut phi_blocks: Vec<u64> = phi_placement.phis.keys().copied().collect();
    phi_blocks.sort_unstable();
    for block_addr in phi_blocks {
        for phi in phi_placement.get_phis(block_addr) {
            ctx.init_var(&phi.var_name, phi.var_size);
        }
    }

    // Get block order (reverse postorder for dominator tree traversal)
    result.block_order = cfg.reverse_postorder();

    // Initialize empty blocks
    for &addr in &result.block_order {
        result.blocks.insert(addr, Vec::new());
    }

    // Prepopulate phi placeholders so predecessor-edge source propagation can update them
    // even if the merge block is renamed later in dominator traversal.
    for &addr in &result.block_order {
        let block_ops = result.blocks.get_mut(&addr).expect("preinitialized block");
        for phi in phi_placement.get_phis(addr) {
            let sources: Vec<SSAVar> = phi
                .predecessors
                .iter()
                .map(|_| SSAVar::new(&phi.var_name, 0, phi.var_size))
                .collect();
            block_ops.push(SSAOp::Phi {
                dst: SSAVar::new(&phi.var_name, 0, phi.var_size),
                sources,
            });
        }
    }

    // Rename starting from entry block using dominator tree traversal
    rename_block(
        cfg.entry,
        cfg,
        domtree,
        phi_placement,
        &mut ctx,
        &mut result,
        reg_names,
        call_boundaries,
    );

    result
}

/// Rename a single block and recursively rename dominated blocks.
#[allow(clippy::too_many_arguments)]
fn rename_block(
    block_addr: u64,
    cfg: &CFG,
    domtree: &DomTree,
    phi_placement: &PhiPlacement,
    ctx: &mut RenameContext,
    result: &mut RenamedFunction,
    reg_names: Option<&RegisterNameMap>,
    call_boundaries: Option<&CallBoundaryConfig>,
) {
    // Track variables defined in this block for cleanup
    let mut defined_vars: Vec<String> = Vec::new();

    // 1. Rename phi node destinations
    let phis = phi_placement.get_phis(block_addr);
    let block_ops = result
        .blocks
        .get_mut(&block_addr)
        .expect("preinitialized block");
    for (phi_idx, phi) in phis.iter().enumerate() {
        let dst = ctx.write_var(&phi.var_name);
        defined_vars.push(phi.var_name.clone());

        // Update the precreated placeholder so predecessor-edge propagation can land
        // before or after the merge block is renamed.
        match block_ops.get_mut(phi_idx) {
            Some(SSAOp::Phi {
                dst: existing_dst,
                sources,
            }) => {
                *existing_dst = dst;
                if sources.len() != phi.predecessors.len() {
                    *sources = phi
                        .predecessors
                        .iter()
                        .map(|_| SSAVar::new(&phi.var_name, 0, phi.var_size))
                        .collect();
                }
            }
            _ => {
                let sources: Vec<SSAVar> = phi
                    .predecessors
                    .iter()
                    .map(|_| SSAVar::new(&phi.var_name, 0, phi.var_size))
                    .collect();
                block_ops.insert(phi_idx, SSAOp::Phi { dst, sources });
            }
        }
    }

    // 2. Rename operations in the block
    if let Some(block) = cfg.get_block(block_addr) {
        for op in &block.ops {
            let renamed_op = rename_op(op, ctx, &mut defined_vars, reg_names);
            result.blocks.get_mut(&block_addr).unwrap().push(renamed_op);

            if matches!(op, r2il::R2ILOp::Call { .. } | r2il::R2ILOp::CallInd { .. })
                && let Some(boundary) = call_boundaries
            {
                append_call_boundary_defs(
                    &mut result.blocks,
                    block_addr,
                    ctx,
                    &mut defined_vars,
                    boundary,
                    reg_names,
                );
            }
        }
    }

    // 3. Fill in phi sources in successor blocks
    for succ_addr in cfg.successors(block_addr) {
        fill_phi_sources(block_addr, succ_addr, phi_placement, ctx, result);
    }

    // 4. Recursively rename dominated blocks
    for &child in domtree.children(block_addr) {
        rename_block(
            child,
            cfg,
            domtree,
            phi_placement,
            ctx,
            result,
            reg_names,
            call_boundaries,
        );
    }

    // 5. Pop versions defined in this block
    for var in defined_vars {
        ctx.pop_version(&var);
    }
}

fn append_call_boundary_defs(
    blocks: &mut HashMap<u64, Vec<SSAOp>>,
    block_addr: u64,
    ctx: &mut RenameContext,
    defined_vars: &mut Vec<String>,
    call_boundaries: &CallBoundaryConfig,
    reg_names: Option<&RegisterNameMap>,
) {
    let Some(block_ops) = blocks.get_mut(&block_addr) else {
        return;
    };

    for reg in &call_boundaries.defined_regs {
        let mut actual_names: BTreeSet<String> =
            ctx.matching_var_names_ci(&reg.name).into_iter().collect();
        if actual_names.is_empty()
            && let Some(reg_names) = reg_names
        {
            for ((_, size), candidate) in reg_names {
                if *size == reg.size && candidate.eq_ignore_ascii_case(&reg.name) {
                    actual_names.insert(candidate.clone());
                }
            }
        }
        if actual_names.is_empty() {
            ctx.init_var(&reg.name, reg.size);
            actual_names.insert(reg.name.clone());
        }
        for actual_name in actual_names {
            let dst = ctx.write_var(&actual_name);
            defined_vars.push(actual_name);
            block_ops.push(SSAOp::CallDefine { dst });
        }
    }
}

/// Fill in phi sources for a successor block.
fn fill_phi_sources(
    pred_addr: u64,
    succ_addr: u64,
    phi_placement: &PhiPlacement,
    ctx: &RenameContext,
    result: &mut RenamedFunction,
) {
    let phis = phi_placement.get_phis(succ_addr);
    if phis.is_empty() {
        return;
    }

    // Find the index of this predecessor
    let pred_idx = phis
        .first()
        .and_then(|phi| phi.predecessors.iter().position(|&p| p == pred_addr));

    let Some(pred_idx) = pred_idx else {
        return;
    };

    // Update phi sources in the result
    let block_ops = result.blocks.get_mut(&succ_addr).unwrap();
    let mut phi_idx = 0;

    for op in block_ops.iter_mut() {
        if let SSAOp::Phi { sources, .. } = op
            && phi_idx < phis.len()
        {
            let phi = &phis[phi_idx];
            if pred_idx < sources.len() {
                sources[pred_idx] = ctx.read_var(&phi.var_name);
            }
            phi_idx += 1;
        }
    }
}

/// Rename a single r2il operation to an SSA operation.
fn rename_op(
    op: &r2il::R2ILOp,
    ctx: &mut RenameContext,
    defined_vars: &mut Vec<String>,
    reg_names: Option<&RegisterNameMap>,
) -> SSAOp {
    use r2il::R2ILOp::*;

    match op {
        Copy { dst, src } => {
            let src_ssa = read_varnode(src, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::Copy {
                dst: dst_ssa,
                src: src_ssa,
            }
        }

        Load { dst, addr, space } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::Load {
                dst: dst_ssa,
                addr: addr_ssa,
                space: format!("{:?}", space),
            }
        }

        Store { addr, val, space } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let val_ssa = read_varnode(val, ctx, reg_names);
            SSAOp::Store {
                addr: addr_ssa,
                val: val_ssa,
                space: format!("{:?}", space),
            }
        }
        Fence { ordering } => SSAOp::Fence {
            ordering: *ordering,
        },
        LoadLinked {
            dst,
            addr,
            space,
            ordering,
        } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::LoadLinked {
                dst: dst_ssa,
                addr: addr_ssa,
                space: format!("{:?}", space),
                ordering: *ordering,
            }
        }
        StoreConditional {
            result,
            addr,
            val,
            space,
            ordering,
        } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let val_ssa = read_varnode(val, ctx, reg_names);
            let result_ssa = result.as_ref().map(|r| {
                let name = varnode_to_name(r, reg_names);
                let ssa = ctx.write_var(&name);
                defined_vars.push(name);
                ssa
            });
            SSAOp::StoreConditional {
                result: result_ssa,
                addr: addr_ssa,
                val: val_ssa,
                space: format!("{:?}", space),
                ordering: *ordering,
            }
        }
        AtomicCAS {
            dst,
            addr,
            expected,
            replacement,
            space,
            ordering,
        } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let expected_ssa = read_varnode(expected, ctx, reg_names);
            let replacement_ssa = read_varnode(replacement, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::AtomicCAS {
                dst: dst_ssa,
                space: format!("{:?}", space),
                addr: addr_ssa,
                expected: expected_ssa,
                replacement: replacement_ssa,
                ordering: *ordering,
            }
        }
        LoadGuarded {
            dst,
            addr,
            guard,
            space,
            ordering,
        } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let guard_ssa = read_varnode(guard, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::LoadGuarded {
                dst: dst_ssa,
                addr: addr_ssa,
                guard: guard_ssa,
                space: format!("{:?}", space),
                ordering: *ordering,
            }
        }
        StoreGuarded {
            addr,
            val,
            guard,
            space,
            ordering,
        } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let val_ssa = read_varnode(val, ctx, reg_names);
            let guard_ssa = read_varnode(guard, ctx, reg_names);
            SSAOp::StoreGuarded {
                space: format!("{:?}", space),
                addr: addr_ssa,
                val: val_ssa,
                guard: guard_ssa,
                ordering: *ordering,
            }
        }

        Branch { target } => {
            let target_ssa = read_varnode(target, ctx, reg_names);
            SSAOp::Branch { target: target_ssa }
        }

        CBranch { target, cond } => {
            let target_ssa = read_varnode(target, ctx, reg_names);
            let cond_ssa = read_varnode(cond, ctx, reg_names);
            SSAOp::CBranch {
                target: target_ssa,
                cond: cond_ssa,
            }
        }

        BranchInd { target } => {
            let target_ssa = read_varnode(target, ctx, reg_names);
            SSAOp::BranchInd { target: target_ssa }
        }

        Call { target } => {
            let target_ssa = read_varnode(target, ctx, reg_names);
            SSAOp::Call { target: target_ssa }
        }

        CallInd { target } => {
            let target_ssa = read_varnode(target, ctx, reg_names);
            SSAOp::CallInd { target: target_ssa }
        }

        Return { target } => {
            let target_ssa = read_varnode(target, ctx, reg_names);
            SSAOp::Return { target: target_ssa }
        }

        IntAdd { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntAdd {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntSub { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntSub {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntMult { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntMult {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntDiv { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntDiv {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntSDiv { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntSDiv {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntRem { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntRem {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntSRem { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntSRem {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntAnd { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntAnd {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntOr { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntOr {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntXor { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntXor {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntLeft { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntLeft {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntRight { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntRight {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntSRight { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntSRight {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntEqual { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntEqual {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntNotEqual { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntNotEqual {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntLess { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntLess {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntSLess { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntSLess {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntLessEqual { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntLessEqual {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntSLessEqual { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntSLessEqual {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntCarry { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntCarry {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntSCarry { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntSCarry {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntSBorrow { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::IntSBorrow {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        IntNegate { dst, src } => {
            rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
                SSAOp::IntNegate { dst: d, src: s }
            })
        }

        IntNot { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::IntNot { dst: d, src: s }
        }),

        IntZExt { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::IntZExt { dst: d, src: s }
        }),

        IntSExt { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::IntSExt { dst: d, src: s }
        }),

        BoolNot { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::BoolNot { dst: d, src: s }
        }),

        BoolAnd { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::BoolAnd {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        BoolOr { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::BoolOr {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        BoolXor { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::BoolXor {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        Piece { dst, hi, lo } => {
            let hi_ssa = read_varnode(hi, ctx, reg_names);
            let lo_ssa = read_varnode(lo, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::Piece {
                dst: dst_ssa,
                hi: hi_ssa,
                lo: lo_ssa,
            }
        }

        Subpiece { dst, src, offset } => {
            let src_ssa = read_varnode(src, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::Subpiece {
                dst: dst_ssa,
                src: src_ssa,
                offset: *offset,
            }
        }

        PopCount { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::PopCount { dst: d, src: s }
        }),

        Lzcount { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::Lzcount { dst: d, src: s }
        }),

        // Floating point operations
        FloatAdd { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::FloatAdd {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        FloatSub { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::FloatSub {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        FloatMult { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::FloatMult {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        FloatDiv { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::FloatDiv {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        FloatNeg { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::FloatNeg { dst: d, src: s }
        }),

        FloatAbs { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::FloatAbs { dst: d, src: s }
        }),

        FloatSqrt { dst, src } => {
            rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
                SSAOp::FloatSqrt { dst: d, src: s }
            })
        }

        FloatCeil { dst, src } => {
            rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
                SSAOp::FloatCeil { dst: d, src: s }
            })
        }

        FloatFloor { dst, src } => {
            rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
                SSAOp::FloatFloor { dst: d, src: s }
            })
        }

        FloatRound { dst, src } => {
            rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
                SSAOp::FloatRound { dst: d, src: s }
            })
        }

        FloatNaN { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::FloatNaN { dst: d, src: s }
        }),

        FloatEqual { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::FloatEqual {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        FloatNotEqual { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::FloatNotEqual {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        FloatLess { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::FloatLess {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        FloatLessEqual { dst, a, b } => {
            rename_binary_op(dst, a, b, ctx, defined_vars, reg_names, |d, s1, s2| {
                SSAOp::FloatLessEqual {
                    dst: d,
                    a: s1,
                    b: s2,
                }
            })
        }

        Int2Float { dst, src } => {
            rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
                SSAOp::Int2Float { dst: d, src: s }
            })
        }

        Float2Int { dst, src } => {
            rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
                SSAOp::Float2Int { dst: d, src: s }
            })
        }

        FloatFloat { dst, src } => {
            rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
                SSAOp::FloatFloat { dst: d, src: s }
            })
        }

        Trunc { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::Trunc { dst: d, src: s }
        }),

        Nop => SSAOp::Nop,

        Unimplemented => SSAOp::Unimplemented,

        Breakpoint => SSAOp::Breakpoint,

        CpuId { dst } => {
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::CpuId { dst: dst_ssa }
        }

        CallOther {
            output,
            userop,
            inputs,
        } => {
            let inputs_ssa: Vec<SSAVar> = inputs
                .iter()
                .map(|v| read_varnode(v, ctx, reg_names))
                .collect();
            let output_ssa = output.as_ref().map(|v| {
                let name = varnode_to_name(v, reg_names);
                let ssa = ctx.write_var(&name);
                defined_vars.push(name);
                ssa
            });
            SSAOp::CallOther {
                output: output_ssa,
                userop: *userop,
                inputs: inputs_ssa,
            }
        }

        Multiequal { dst, inputs } => {
            let inputs_ssa: Vec<SSAVar> = inputs
                .iter()
                .map(|v| read_varnode(v, ctx, reg_names))
                .collect();
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::Phi {
                dst: dst_ssa,
                sources: inputs_ssa,
            }
        }

        Indirect {
            dst,
            src,
            indirect: _,
        } => {
            // Indirect is used for aliasing - treat as a copy for SSA purposes
            let src_ssa = read_varnode(src, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::Copy {
                dst: dst_ssa,
                src: src_ssa,
            }
        }

        PtrAdd {
            dst,
            base,
            index,
            element_size,
        } => {
            let base_ssa = read_varnode(base, ctx, reg_names);
            let index_ssa = read_varnode(index, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::PtrAdd {
                dst: dst_ssa,
                base: base_ssa,
                index: index_ssa,
                element_size: *element_size,
            }
        }

        PtrSub {
            dst,
            base,
            index,
            element_size,
        } => {
            let base_ssa = read_varnode(base, ctx, reg_names);
            let index_ssa = read_varnode(index, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::PtrSub {
                dst: dst_ssa,
                base: base_ssa,
                index: index_ssa,
                element_size: *element_size,
            }
        }

        SegmentOp {
            dst,
            segment,
            offset,
        } => {
            let seg_ssa = read_varnode(segment, ctx, reg_names);
            let off_ssa = read_varnode(offset, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::SegmentOp {
                dst: dst_ssa,
                segment: seg_ssa,
                offset: off_ssa,
            }
        }

        New { dst, src } => {
            let src_ssa = read_varnode(src, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::New {
                dst: dst_ssa,
                src: src_ssa,
            }
        }

        Cast { dst, src } => rename_unary_op(dst, src, ctx, defined_vars, reg_names, |d, s| {
            SSAOp::Cast { dst: d, src: s }
        }),

        Extract { dst, src, position } => {
            let src_ssa = read_varnode(src, ctx, reg_names);
            let pos_ssa = read_varnode(position, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::Extract {
                dst: dst_ssa,
                src: src_ssa,
                position: pos_ssa,
            }
        }

        Insert {
            dst,
            src,
            value,
            position,
        } => {
            let src_ssa = read_varnode(src, ctx, reg_names);
            let val_ssa = read_varnode(value, ctx, reg_names);
            let pos_ssa = read_varnode(position, ctx, reg_names);
            let dst_name = varnode_to_name(dst, reg_names);
            let dst_ssa = ctx.write_var(&dst_name);
            defined_vars.push(dst_name);
            SSAOp::Insert {
                dst: dst_ssa,
                src: src_ssa,
                value: val_ssa,
                position: pos_ssa,
            }
        }
    }
}

/// Helper for renaming binary operations.
fn rename_binary_op<F>(
    dst: &r2il::Varnode,
    src1: &r2il::Varnode,
    src2: &r2il::Varnode,
    ctx: &mut RenameContext,
    defined_vars: &mut Vec<String>,
    reg_names: Option<&RegisterNameMap>,
    f: F,
) -> SSAOp
where
    F: FnOnce(SSAVar, SSAVar, SSAVar) -> SSAOp,
{
    let src1_ssa = read_varnode(src1, ctx, reg_names);
    let src2_ssa = read_varnode(src2, ctx, reg_names);
    let dst_name = varnode_to_name(dst, reg_names);
    let dst_ssa = ctx.write_var(&dst_name);
    defined_vars.push(dst_name);
    f(dst_ssa, src1_ssa, src2_ssa)
}

/// Helper for renaming unary operations.
fn rename_unary_op<F>(
    dst: &r2il::Varnode,
    src: &r2il::Varnode,
    ctx: &mut RenameContext,
    defined_vars: &mut Vec<String>,
    reg_names: Option<&RegisterNameMap>,
    f: F,
) -> SSAOp
where
    F: FnOnce(SSAVar, SSAVar) -> SSAOp,
{
    let src_ssa = read_varnode(src, ctx, reg_names);
    let dst_name = varnode_to_name(dst, reg_names);
    let dst_ssa = ctx.write_var(&dst_name);
    defined_vars.push(dst_name);
    f(dst_ssa, src_ssa)
}

/// Read a varnode and return an SSAVar.
fn read_varnode(
    vn: &r2il::Varnode,
    ctx: &RenameContext,
    reg_names: Option<&RegisterNameMap>,
) -> SSAVar {
    use r2il::SpaceId;

    match vn.space {
        SpaceId::Const => {
            // Constants don't need versioning
            SSAVar::constant(vn.offset, vn.size)
        }
        _ => {
            let name = varnode_to_name(vn, reg_names);
            ctx.read_var(&name)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::CFG;
    use crate::phi::collect_defs_from_cfg;
    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};

    fn make_const(val: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: val,
            size,
            meta: None,
        }
    }

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
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
    fn test_rename_linear() {
        // Linear CFG with two writes to same register
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(2, 8),
                    },
                ],
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
        let domtree = DomTree::compute(&cfg);
        let (defs, var_sizes) = collect_defs_from_cfg(&cfg);
        let phi_placement = PhiPlacement::compute(&cfg, &domtree, &defs, &var_sizes);
        let result = rename_function(&cfg, &domtree, &phi_placement, &var_sizes);

        // Check that versions are assigned correctly
        let block_ops = result.get_block(0x1000);
        assert_eq!(block_ops.len(), 2);

        // First copy should produce reg:0 v1
        if let SSAOp::Copy { dst, .. } = &block_ops[0] {
            assert_eq!(dst.version, 1);
        } else {
            panic!("Expected Copy op");
        }

        // Second copy should produce reg:0 v2
        if let SSAOp::Copy { dst, .. } = &block_ops[1] {
            assert_eq!(dst.version, 2);
        } else {
            panic!("Expected Copy op");
        }
    }

    #[test]
    fn test_rename_with_phi() {
        // Diamond CFG with phi
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
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x100c, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(2, 8),
                }],
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
        let (defs, var_sizes) = collect_defs_from_cfg(&cfg);
        let phi_placement = PhiPlacement::compute(&cfg, &domtree, &defs, &var_sizes);
        let result = rename_function(&cfg, &domtree, &phi_placement, &var_sizes);

        // Check that merge block has a phi
        let merge_ops = result.get_block(0x100c);
        assert!(!merge_ops.is_empty());

        // First op should be a phi
        if let SSAOp::Phi { dst, sources } = &merge_ops[0] {
            assert_eq!(dst.name, "reg:0");
            assert_eq!(sources.len(), 2);
            assert_eq!(sources[0].name, "reg:0");
            assert_eq!(sources[1].name, "reg:0");
            assert_eq!(sources[0].version, 1);
            assert_eq!(sources[1].version, 2);
        } else {
            panic!("Expected Phi op, got {:?}", merge_ops[0]);
        }
    }
}
