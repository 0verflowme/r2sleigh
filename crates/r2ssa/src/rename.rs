//! SSA renaming algorithm.
//!
//! This module implements the SSA renaming pass that assigns version numbers
//! to variables, following the algorithm from Cytron et al.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::cfg::CFG;
use crate::control::{SsaExecutionStopReason, SsaWorkControl, UncheckedSsaWorkControl};
use crate::domtree::DomTree;
use crate::naming::RegisterNameMap;
use crate::op::SSAOp;
use crate::phi::{DefinitionSitesByIdentity, PhiPlacement, RenameIdentity};
use crate::var::{CanonicalStorageId, SSAVar};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RenameProjection {
    name: String,
    size: u32,
}

impl From<&RenameIdentity> for RenameProjection {
    fn from(identity: &RenameIdentity) -> Self {
        Self {
            name: identity.name.clone(),
            size: identity.size,
        }
    }
}

/// Context for SSA renaming.
#[derive(Debug)]
pub struct RenameContext {
    /// Stack of versions for each exact semantic-name/width/storage identity.
    /// The top of the stack is the current version.
    stacks: HashMap<RenameIdentity, Vec<u32>>,
    /// Collision-free version namespace for the user-facing SSAVar projection.
    counters: HashMap<RenameProjection, u32>,
    /// Dense deterministic discriminator for exact identities whose public
    /// name/width projection is otherwise identical.
    disambiguators: HashMap<RenameIdentity, u32>,
    next_disambiguator: HashMap<RenameProjection, u32>,
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
            disambiguators: HashMap::new(),
            next_disambiguator: HashMap::new(),
        }
    }

    /// Initialize one exact rename identity.
    pub fn init_identity(&mut self, identity: RenameIdentity) {
        let projection = RenameProjection::from(&identity);
        if !self.disambiguators.contains_key(&identity) {
            let next = self
                .next_disambiguator
                .entry(projection.clone())
                .or_insert(0);
            self.disambiguators.insert(identity.clone(), *next);
            *next = next.checked_add(1).expect("rename discriminator exhausted");
        }
        // Start with version 0 on the stack (representing "undefined" or function entry)
        self.stacks
            .entry(identity.clone())
            .or_insert_with(|| vec![0]);
        self.counters.entry(projection).or_insert(0);
    }

    /// Get the current version of a variable (for reading).
    pub fn current_version(&self, identity: &RenameIdentity) -> u32 {
        self.stacks
            .get(identity)
            .and_then(|stack| stack.last().copied())
            .unwrap_or(0)
    }

    /// Generate a new version of a variable (for writing).
    pub fn new_version(&mut self, identity: &RenameIdentity) -> u32 {
        let counter = self
            .counters
            .entry(RenameProjection::from(identity))
            .or_insert(0);
        *counter += 1;
        let version = *counter;
        self.stacks
            .entry(identity.clone())
            .or_default()
            .push(version);
        version
    }

    /// Pop a version from a variable's stack (when leaving a block's scope).
    pub fn pop_version(&mut self, identity: &RenameIdentity) {
        if let Some(stack) = self.stacks.get_mut(identity) {
            stack.pop();
        }
    }

    /// Create an SSAVar for reading one exact rename identity.
    pub fn read_var(&self, identity: &RenameIdentity) -> SSAVar {
        self.var_at(identity, self.current_version(identity))
    }

    fn var_at(&self, identity: &RenameIdentity, version: u32) -> SSAVar {
        identity.as_var(
            version,
            self.disambiguators.get(identity).copied().unwrap_or(0),
        )
    }

    /// Create an SSAVar for writing one exact rename identity.
    pub fn write_var(&mut self, identity: &RenameIdentity) -> SSAVar {
        let disambiguator = self.disambiguators.get(identity).copied().unwrap_or(0);
        identity.as_var(self.new_version(identity), disambiguator)
    }

    /// Find initialized identities with this register spelling and exact width.
    pub fn matching_identities_ci(&self, name: &str, size: u32) -> Vec<RenameIdentity> {
        let needle = name.to_ascii_lowercase();
        let mut matches: Vec<RenameIdentity> = self
            .stacks
            .keys()
            .filter(|candidate| {
                candidate.size == size && candidate.name.to_ascii_lowercase() == needle
            })
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
    /// Lifted storage provenance for SSA values.
    ///
    /// This map is populated directly from source varnodes while renaming. A
    /// display name is only the key that associates the already-proven source
    /// identity with its SSA version; it is never parsed or resolved through
    /// architecture register names.
    pub canonical_storage_by_var: BTreeMap<SSAVar, CanonicalStorageId>,
    ambiguous_storage_vars: BTreeSet<SSAVar>,
}

impl RenamedFunction {
    /// Create a new empty renamed function.
    pub fn new(entry: u64) -> Self {
        Self {
            blocks: HashMap::new(),
            block_order: Vec::new(),
            entry,
            canonical_storage_by_var: BTreeMap::new(),
            ambiguous_storage_vars: BTreeSet::new(),
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
    definitions: &DefinitionSitesByIdentity,
) -> RenamedFunction {
    rename_function_with_names(cfg, domtree, phi_placement, definitions, None)
}

/// Perform SSA renaming on a CFG with optional register names.
pub fn rename_function_with_names(
    cfg: &CFG,
    domtree: &DomTree,
    phi_placement: &PhiPlacement,
    definitions: &DefinitionSitesByIdentity,
    reg_names: Option<&RegisterNameMap>,
) -> RenamedFunction {
    rename_function_with_names_and_call_boundaries(
        cfg,
        domtree,
        phi_placement,
        definitions,
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
    definitions: &DefinitionSitesByIdentity,
    reg_names: Option<&RegisterNameMap>,
    call_boundaries: Option<&CallBoundaryConfig>,
) -> RenamedFunction {
    rename_function_with_names_and_call_boundaries_and_control(
        cfg,
        domtree,
        phi_placement,
        definitions,
        reg_names,
        call_boundaries,
        &UncheckedSsaWorkControl,
    )
    .expect("unchecked SSA renaming cannot stop")
}

/// Perform SSA renaming while polling its block and operation worklists.
#[allow(clippy::too_many_arguments)]
pub fn rename_function_with_names_and_call_boundaries_and_control<C: SsaWorkControl + ?Sized>(
    cfg: &CFG,
    domtree: &DomTree,
    phi_placement: &PhiPlacement,
    definitions: &DefinitionSitesByIdentity,
    reg_names: Option<&RegisterNameMap>,
    call_boundaries: Option<&CallBoundaryConfig>,
    control: &C,
) -> Result<RenamedFunction, SsaExecutionStopReason> {
    control.poll()?;
    let mut ctx = RenameContext::new();
    let mut result = RenamedFunction::new(cfg.entry);

    // Initialize all variables
    for identity in definitions.keys() {
        control.poll()?;
        ctx.init_identity(identity.clone());
    }

    // Also initialize variables from phi nodes
    let mut phi_blocks: Vec<u64> = phi_placement.phis.keys().copied().collect();
    phi_blocks.sort_unstable();
    for block_addr in phi_blocks {
        control.poll()?;
        for phi in phi_placement.get_phis(block_addr) {
            control.poll()?;
            ctx.init_identity(phi.identity.clone());
        }
    }

    // Get block order (reverse postorder for dominator tree traversal)
    result.block_order = cfg.reverse_postorder();

    // Initialize empty blocks
    for &addr in &result.block_order {
        control.poll()?;
        result.blocks.insert(addr, Vec::new());
    }

    // Prepopulate phi placeholders so predecessor-edge source propagation can update them
    // even if the merge block is renamed later in dominator traversal.
    for &addr in &result.block_order {
        control.poll()?;
        let block_ops = result.blocks.get_mut(&addr).expect("preinitialized block");
        for phi in phi_placement.get_phis(addr) {
            control.poll()?;
            let sources: Vec<SSAVar> = phi
                .predecessors
                .iter()
                .map(|_| ctx.var_at(&phi.identity, 0))
                .collect();
            block_ops.push(SSAOp::Phi {
                dst: ctx.var_at(&phi.identity, 0),
                sources,
            });
        }
    }

    // Rename starting from entry block using dominator tree traversal.
    rename_block(
        cfg.entry,
        cfg,
        domtree,
        phi_placement,
        &mut ctx,
        &mut result,
        reg_names,
        call_boundaries,
        control,
    )?;

    control.poll()?;
    Ok(result)
}

/// Rename a block and its dominated descendants.
#[allow(clippy::too_many_arguments)]
fn rename_block<C: SsaWorkControl + ?Sized>(
    block_addr: u64,
    cfg: &CFG,
    domtree: &DomTree,
    phi_placement: &PhiPlacement,
    ctx: &mut RenameContext,
    result: &mut RenamedFunction,
    reg_names: Option<&RegisterNameMap>,
    call_boundaries: Option<&CallBoundaryConfig>,
    control: &C,
) -> Result<(), SsaExecutionStopReason> {
    // An exit frame keeps each block's definitions live until all dominated
    // children have been renamed, matching the recursive traversal's scope.
    let mut stack: Vec<(u64, Option<Vec<RenameIdentity>>)> = vec![(block_addr, None)];
    while let Some((block_addr, exit_defs)) = stack.pop() {
        control.poll()?;
        if let Some(defined_vars) = exit_defs {
            for var in defined_vars {
                ctx.pop_version(&var);
            }
            continue;
        }

        // Track variables defined in this block for cleanup.
        let mut defined_vars: Vec<RenameIdentity> = Vec::new();

        // 1. Rename phi node destinations.
        let phis = phi_placement.get_phis(block_addr);
        let block_ops = result
            .blocks
            .get_mut(&block_addr)
            .expect("preinitialized block");
        for (phi_idx, phi) in phis.iter().enumerate() {
            control.poll()?;
            let dst = ctx.write_var(&phi.identity);
            if let Some(storage) = phi.storage {
                record_canonical_storage(
                    &mut result.canonical_storage_by_var,
                    &mut result.ambiguous_storage_vars,
                    &dst,
                    storage,
                );
            }
            defined_vars.push(phi.identity.clone());

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
                            .map(|_| ctx.var_at(&phi.identity, 0))
                            .collect();
                    }
                }
                _ => {
                    let sources: Vec<SSAVar> = phi
                        .predecessors
                        .iter()
                        .map(|_| ctx.var_at(&phi.identity, 0))
                        .collect();
                    block_ops.insert(phi_idx, SSAOp::Phi { dst, sources });
                }
            }
        }

        // 2. Rename operations in the block.
        if let Some(block) = cfg.get_block(block_addr) {
            for op in &block.ops {
                control.poll()?;
                let renamed_op = rename_op(op, ctx, &mut defined_vars, reg_names);
                record_renamed_op_storage(op, &renamed_op, result);
                result.blocks.get_mut(&block_addr).unwrap().push(renamed_op);

                if matches!(op, r2il::R2ILOp::Call { .. } | r2il::R2ILOp::CallInd { .. })
                    && let Some(boundary) = call_boundaries
                {
                    let boundary_defs = append_call_boundary_defs(
                        &mut result.blocks,
                        block_addr,
                        ctx,
                        &mut defined_vars,
                        boundary,
                        reg_names,
                    );
                    for (dst, storage) in boundary_defs {
                        record_canonical_storage(
                            &mut result.canonical_storage_by_var,
                            &mut result.ambiguous_storage_vars,
                            &dst,
                            storage,
                        );
                    }
                }
            }
        }

        // 3. Fill in phi sources in successor blocks.
        for succ_addr in cfg.successors(block_addr) {
            control.poll()?;
            fill_phi_sources(block_addr, succ_addr, phi_placement, ctx, result);
        }

        // 4. Rename dominated children before leaving this block's scope.
        stack.push((block_addr, Some(defined_vars)));
        for &child in domtree.children(block_addr).iter().rev() {
            stack.push((child, None));
        }
    }
    Ok(())
}

fn record_renamed_op_storage(source: &r2il::R2ILOp, renamed: &SSAOp, result: &mut RenamedFunction) {
    if let (Some(varnode), Some(var)) = (source.output(), renamed.dst()) {
        record_canonical_storage(
            &mut result.canonical_storage_by_var,
            &mut result.ambiguous_storage_vars,
            var,
            CanonicalStorageId::from_varnode(varnode),
        );
    }

    let source_inputs = source.inputs();
    let renamed_inputs = renamed.sources();
    if source_inputs.len() != renamed_inputs.len() {
        // A mismatched operation contract cannot safely attach positional
        // provenance. Leaving these values unbound makes proof consumers fail
        // closed rather than assigning the wrong storage identity.
        return;
    }
    for (varnode, var) in source_inputs.into_iter().zip(renamed_inputs) {
        record_canonical_storage(
            &mut result.canonical_storage_by_var,
            &mut result.ambiguous_storage_vars,
            var,
            CanonicalStorageId::from_varnode(varnode),
        );
    }
}

fn record_canonical_storage(
    storage_by_var: &mut BTreeMap<SSAVar, CanonicalStorageId>,
    ambiguous_vars: &mut BTreeSet<SSAVar>,
    var: &SSAVar,
    storage: CanonicalStorageId,
) {
    if ambiguous_vars.contains(var) {
        return;
    }
    if storage_by_var
        .get(var)
        .is_some_and(|existing| *existing != storage)
    {
        storage_by_var.remove(var);
        ambiguous_vars.insert(var.clone());
        return;
    }
    storage_by_var.insert(var.clone(), storage);
}

fn append_call_boundary_defs(
    blocks: &mut HashMap<u64, Vec<SSAOp>>,
    block_addr: u64,
    ctx: &mut RenameContext,
    defined_vars: &mut Vec<RenameIdentity>,
    call_boundaries: &CallBoundaryConfig,
    reg_names: Option<&RegisterNameMap>,
) -> Vec<(SSAVar, CanonicalStorageId)> {
    let Some(block_ops) = blocks.get_mut(&block_addr) else {
        return Vec::new();
    };
    let mut retained = Vec::new();

    for reg in &call_boundaries.defined_regs {
        let mut actual_identities: BTreeSet<RenameIdentity> = ctx
            .matching_identities_ci(&reg.name, reg.size)
            .into_iter()
            .collect();
        if actual_identities.is_empty()
            && let Some(reg_names) = reg_names
        {
            for ((offset, size), candidate) in reg_names {
                if *size == reg.size && candidate.eq_ignore_ascii_case(&reg.name) {
                    actual_identities.insert(RenameIdentity::new(
                        candidate,
                        CanonicalStorageId {
                            space: crate::CanonicalStorageSpace::Register,
                            offset: *offset,
                            size: *size,
                        },
                    ));
                }
            }
        }
        if actual_identities.is_empty() {
            actual_identities.insert(RenameIdentity::synthetic(&reg.name, reg.size));
        }
        for identity in actual_identities {
            let storage = identity.storage;
            ctx.init_identity(identity.clone());
            let dst = ctx.write_var(&identity);
            defined_vars.push(identity);
            if matches!(storage.space, crate::CanonicalStorageSpace::Register) {
                retained.push((dst.clone(), storage));
            }
            block_ops.push(SSAOp::CallDefine { dst });
        }
    }
    retained
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

    let incoming = phis
        .iter()
        .map(|phi| {
            let source = ctx.read_var(&phi.identity);
            if let Some(storage) = phi.storage
                && storage.size == source.size
            {
                record_canonical_storage(
                    &mut result.canonical_storage_by_var,
                    &mut result.ambiguous_storage_vars,
                    &source,
                    storage,
                );
            }
            source
        })
        .collect::<Vec<_>>();

    // Update phi sources in the result
    let block_ops = result.blocks.get_mut(&succ_addr).unwrap();
    let mut phi_idx = 0;

    for op in block_ops.iter_mut() {
        if let SSAOp::Phi { sources, .. } = op
            && phi_idx < phis.len()
        {
            if pred_idx < sources.len() {
                sources[pred_idx] = incoming[phi_idx].clone();
            }
            phi_idx += 1;
        }
    }
}

/// Rename a single r2il operation to an SSA operation.
fn write_varnode(
    varnode: &r2il::Varnode,
    ctx: &mut RenameContext,
    defined_vars: &mut Vec<RenameIdentity>,
    reg_names: Option<&RegisterNameMap>,
) -> SSAVar {
    let identity = RenameIdentity::from_varnode(varnode, reg_names);
    let renamed = ctx.write_var(&identity);
    defined_vars.push(identity);
    renamed
}

fn rename_op(
    op: &r2il::R2ILOp,
    ctx: &mut RenameContext,
    defined_vars: &mut Vec<RenameIdentity>,
    reg_names: Option<&RegisterNameMap>,
) -> SSAOp {
    use r2il::R2ILOp::*;

    match op {
        Copy { dst, src } => {
            let src_ssa = read_varnode(src, ctx, reg_names);
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::Copy {
                dst: dst_ssa,
                src: src_ssa,
            }
        }

        Load { dst, addr, space } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::Load {
                dst: dst_ssa,
                addr: addr_ssa,
                space: *space,
            }
        }

        Store { addr, val, space } => {
            let addr_ssa = read_varnode(addr, ctx, reg_names);
            let val_ssa = read_varnode(val, ctx, reg_names);
            SSAOp::Store {
                addr: addr_ssa,
                val: val_ssa,
                space: *space,
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::LoadLinked {
                dst: dst_ssa,
                addr: addr_ssa,
                space: *space,
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
            let result_ssa = result
                .as_ref()
                .map(|r| write_varnode(r, ctx, defined_vars, reg_names));
            SSAOp::StoreConditional {
                result: result_ssa,
                addr: addr_ssa,
                val: val_ssa,
                space: *space,
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::AtomicCAS {
                dst: dst_ssa,
                space: *space,
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::LoadGuarded {
                dst: dst_ssa,
                addr: addr_ssa,
                guard: guard_ssa,
                space: *space,
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
                space: *space,
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::Piece {
                dst: dst_ssa,
                hi: hi_ssa,
                lo: lo_ssa,
            }
        }

        Subpiece { dst, src, offset } => {
            let src_ssa = read_varnode(src, ctx, reg_names);
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let output_ssa = output
                .as_ref()
                .map(|v| write_varnode(v, ctx, defined_vars, reg_names));
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::SegmentOp {
                dst: dst_ssa,
                segment: seg_ssa,
                offset: off_ssa,
            }
        }

        New { dst, src } => {
            let src_ssa = read_varnode(src, ctx, reg_names);
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::Insert {
                dst: dst_ssa,
                src: src_ssa,
                value: val_ssa,
                position: pos_ssa,
            }
        }

        Select {
            dst,
            cond,
            if_true,
            if_false,
        } => {
            let cond_ssa = read_varnode(cond, ctx, reg_names);
            let true_ssa = read_varnode(if_true, ctx, reg_names);
            let false_ssa = read_varnode(if_false, ctx, reg_names);
            let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
            SSAOp::Select {
                dst: dst_ssa,
                cond: cond_ssa,
                if_true: true_ssa,
                if_false: false_ssa,
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
    defined_vars: &mut Vec<RenameIdentity>,
    reg_names: Option<&RegisterNameMap>,
    f: F,
) -> SSAOp
where
    F: FnOnce(SSAVar, SSAVar, SSAVar) -> SSAOp,
{
    let src1_ssa = read_varnode(src1, ctx, reg_names);
    let src2_ssa = read_varnode(src2, ctx, reg_names);
    let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
    f(dst_ssa, src1_ssa, src2_ssa)
}

/// Helper for renaming unary operations.
fn rename_unary_op<F>(
    dst: &r2il::Varnode,
    src: &r2il::Varnode,
    ctx: &mut RenameContext,
    defined_vars: &mut Vec<RenameIdentity>,
    reg_names: Option<&RegisterNameMap>,
    f: F,
) -> SSAOp
where
    F: FnOnce(SSAVar, SSAVar) -> SSAOp,
{
    let src_ssa = read_varnode(src, ctx, reg_names);
    let dst_ssa = write_varnode(dst, ctx, defined_vars, reg_names);
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
            let identity = RenameIdentity::from_varnode(vn, reg_names);
            ctx.read_var(&identity)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::CFG;
    use crate::phi::{collect_defs_from_cfg, collect_defs_from_cfg_with_names};
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

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

    fn make_unique(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Unique,
            offset,
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
        let defs = collect_defs_from_cfg(&cfg);
        let phi_placement = PhiPlacement::compute(&cfg, &domtree, &defs);
        let result = rename_function(&cfg, &domtree, &phi_placement, &defs);

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
        let defs = collect_defs_from_cfg(&cfg);
        let phi_placement = PhiPlacement::compute(&cfg, &domtree, &defs);
        let result = rename_function(&cfg, &domtree, &phi_placement, &defs);

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

    #[test]
    fn phi_live_in_source_retains_lifted_storage() {
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
                ops: Vec::new(),
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
        let defs = collect_defs_from_cfg(&cfg);
        let storage = CanonicalStorageId::from_varnode(&make_reg(0, 8));
        let storage_by_identity =
            BTreeMap::from([(RenameIdentity::new("reg:0", storage), storage)]);
        let phi_placement =
            PhiPlacement::compute_with_storage(&cfg, &domtree, &defs, &storage_by_identity);
        let result = rename_function(&cfg, &domtree, &phi_placement, &defs);
        let SSAOp::Phi { sources, .. } = &result.get_block(0x100c)[0] else {
            panic!("expected merge phi");
        };
        let live_in = sources
            .iter()
            .find(|source| source.version == 0)
            .expect("entry live-in source");
        assert_eq!(result.canonical_storage_by_var.get(live_in), Some(&storage));
    }

    #[test]
    fn call_boundary_preserves_register_map_alias_width_for_read_only_alias() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
                R2ILOp::IntEqual {
                    dst: make_reg(0x80, 1),
                    a: make_reg(0, 4),
                    b: make_const(0, 4),
                },
                R2ILOp::Return {
                    target: make_const(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let cfg = CFG::from_blocks(&blocks).unwrap();
        let domtree = DomTree::compute(&cfg);
        let mut reg_names = RegisterNameMap::new();
        reg_names.insert((0, 8), "RAX".to_string());
        reg_names.insert((0, 4), "EAX".to_string());
        let defs = collect_defs_from_cfg_with_names(&cfg, Some(&reg_names));
        let phi_placement = PhiPlacement::compute(&cfg, &domtree, &defs);
        let boundary = CallBoundaryConfig {
            defined_regs: vec![
                CallBoundaryDef {
                    name: "rax".to_string(),
                    size: 8,
                },
                CallBoundaryDef {
                    name: "eax".to_string(),
                    size: 4,
                },
            ],
        };
        let result = rename_function_with_names_and_call_boundaries(
            &cfg,
            &domtree,
            &phi_placement,
            &defs,
            Some(&reg_names),
            Some(&boundary),
        );

        let call_defines: Vec<&SSAVar> = result
            .get_block(0x1000)
            .iter()
            .filter_map(|op| match op {
                SSAOp::CallDefine { dst } => Some(dst),
                _ => None,
            })
            .collect();
        assert!(
            call_defines
                .iter()
                .any(|dst| dst.name == "RAX" && dst.size == 8)
        );
        assert!(
            call_defines
                .iter()
                .any(|dst| dst.name == "EAX" && dst.size == 4)
        );
    }

    #[test]
    fn reused_unique_widths_have_distinct_deterministic_diamond_phis() {
        let narrow = make_unique(0x200, 4);
        let wide = make_unique(0x200, 8);
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
                        dst: narrow.clone(),
                        src: make_const(1, 4),
                    },
                    R2ILOp::Copy {
                        dst: wide.clone(),
                        src: make_const(2, 8),
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
                ops: vec![
                    R2ILOp::Copy {
                        dst: narrow.clone(),
                        src: make_const(3, 4),
                    },
                    R2ILOp::Copy {
                        dst: wide.clone(),
                        src: make_const(4, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 4),
                        src: narrow,
                    },
                    R2ILOp::Copy {
                        dst: make_reg(8, 8),
                        src: wide,
                    },
                    R2ILOp::Return {
                        target: make_const(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let cfg = CFG::from_blocks(&blocks).expect("diamond CFG");
        let domtree = DomTree::compute(&cfg);
        let (defs, storage_by_identity) =
            crate::phi::collect_defs_from_cfg_with_names_and_storage(&cfg, None);
        let placement =
            PhiPlacement::compute_with_storage(&cfg, &domtree, &defs, &storage_by_identity);
        let first = rename_function(&cfg, &domtree, &placement, &defs);
        let second = rename_function(&cfg, &domtree, &placement, &defs);

        assert_eq!(first.block_order, second.block_order);
        assert_eq!(first.blocks, second.blocks);
        assert_eq!(
            first.canonical_storage_by_var,
            second.canonical_storage_by_var
        );

        let merge = first.get_block(0x100c);
        let phis: Vec<(&SSAVar, &Vec<SSAVar>)> = merge
            .iter()
            .filter_map(|op| match op {
                SSAOp::Phi { dst, sources } => Some((dst, sources)),
                _ => None,
            })
            .collect();
        assert_eq!(phis.len(), 2, "one phi is required for each exact width");
        assert_eq!(
            phis.iter().map(|(dst, _)| dst.size).collect::<Vec<_>>(),
            vec![4, 8]
        );

        let definitions: BTreeSet<SSAVar> = first
            .blocks
            .values()
            .flat_map(|ops| ops.iter().filter_map(SSAOp::dst).cloned())
            .collect();
        for (dst, sources) in phis {
            assert_eq!(
                dst.version, 3,
                "each width must own an independent version sequence"
            );
            assert_eq!(sources.len(), 2);
            assert_eq!(
                sources
                    .iter()
                    .map(|source| source.version)
                    .collect::<Vec<_>>(),
                vec![1, 2]
            );
            for source in sources {
                assert_eq!(source.name, dst.name);
                assert_eq!(source.size, dst.size);
                assert!(
                    source.version == 0 || definitions.contains(source),
                    "phi source {source:?} has no incoming SSA definition"
                );
            }
        }
    }

    #[test]
    fn same_named_same_width_storages_keep_distinct_live_ins_and_graph_values() {
        let mut arch = ArchSpec::new("rename-storage-collision");
        arch.add_register(RegisterDef::new("alias", 0, 8));
        arch.add_register(RegisterDef::new("alias", 8, 8));
        let blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_unique(0x100, 8),
                    src: make_reg(0, 8),
                },
                R2ILOp::Copy {
                    dst: make_unique(0x108, 8),
                    src: make_reg(8, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(1, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(8, 8),
                    src: make_const(2, 8),
                },
                R2ILOp::Return {
                    target: make_const(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let function = crate::function::SSAFunction::from_blocks_raw(&blocks, Some(&arch))
            .expect("raw SSA with colliding register spellings");
        let ops = &function.get_block(0x2000).expect("entry block").ops;
        let (
            SSAOp::Copy {
                src: first_live_in, ..
            },
            SSAOp::Copy {
                src: second_live_in,
                ..
            },
        ) = (&ops[0], &ops[1])
        else {
            panic!("expected two live-in copies");
        };
        assert_eq!(first_live_in.name, second_live_in.name);
        assert_eq!(first_live_in.size, second_live_in.size);
        assert_eq!(first_live_in.version, 0);
        assert_eq!(second_live_in.version, 0);
        assert_ne!(
            first_live_in, second_live_in,
            "exact storage must survive the shared display projection"
        );

        let first_def = ops[2].dst().expect("first alias definition");
        let second_def = ops[3].dst().expect("second alias definition");
        assert_ne!(first_def, second_def);
        assert_eq!((first_def.version, second_def.version), (1, 2));

        let graph = crate::graph::SsaGraph::from_function(&function);
        let first_value = graph
            .value_id_for_var(first_live_in)
            .expect("first live-in graph value");
        let second_value = graph
            .value_id_for_var(second_live_in)
            .expect("second live-in graph value");
        assert_ne!(first_value, second_value);
        assert_eq!(
            graph.canonical_storage_for_var(first_live_in),
            Some(CanonicalStorageId::from_varnode(&make_reg(0, 8)))
        );
        assert_eq!(
            graph.canonical_storage_for_var(second_live_in),
            Some(CanonicalStorageId::from_varnode(&make_reg(8, 8)))
        );
    }
}
