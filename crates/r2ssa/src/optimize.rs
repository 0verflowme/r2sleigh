//! SSA optimization pipeline.
//!
//! This module applies a sequence of lightweight, SSA-safe optimizations
//! intended to simplify analysis and decompilation output.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::control::{SsaExecutionStopReason, SsaWorkControl, UncheckedSsaWorkControl};
use crate::{
    BlockTerminator, CanonicalStorageId, CanonicalStorageSpace, PhiNode, SSAFunction, SSAOp,
    SSAVar, SourceCarrierKind, SourceFunctionInterface, SourceFunctionReturn, SourceSite,
    SourceTypeKind,
};

/// Configuration for SSA optimization passes.
#[derive(Debug, Clone)]
pub struct OptimizationConfig {
    pub max_iterations: usize,
    pub enable_sccp: bool,
    pub enable_inst_combine: bool,
    pub preserve_memory_reads: bool,
}

/// Configuration for preparing SSA for decompilation.
///
/// The decompiler needs provenance-preserving SSA more than aggressively
/// simplified SSA, so the default intentionally disables destructive
/// simplification passes and only allows explicitly opted-in transforms.
#[derive(Debug, Clone)]
pub struct DecompilePrepConfig {
    pub max_iterations: usize,
    pub enable_inst_combine: bool,
}

impl Default for OptimizationConfig {
    fn default() -> Self {
        Self {
            max_iterations: 4,
            enable_sccp: true,
            enable_inst_combine: true,
            preserve_memory_reads: false,
        }
    }
}

impl Default for DecompilePrepConfig {
    fn default() -> Self {
        Self {
            max_iterations: 1,
            enable_inst_combine: true,
        }
    }
}

impl From<&DecompilePrepConfig> for OptimizationConfig {
    fn from(value: &DecompilePrepConfig) -> Self {
        Self {
            max_iterations: value.max_iterations.max(1),
            enable_sccp: false,
            enable_inst_combine: value.enable_inst_combine,
            preserve_memory_reads: true,
        }
    }
}

/// Optimization statistics for a single run.
#[derive(Debug, Clone, Default)]
pub struct OptimizationStats {
    pub iterations: usize,
    pub sccp_constants_found: usize,
    pub sccp_edges_pruned: usize,
    pub sccp_blocks_removed: usize,
    pub constants_propagated: usize,
    pub ops_simplified: usize,
}

/// Run the SSA optimization pipeline on a function.
pub fn optimize_function(func: &mut SSAFunction, config: &OptimizationConfig) -> OptimizationStats {
    optimize_function_with_control(func, config, &UncheckedSsaWorkControl)
        .expect("unchecked SSA optimization cannot stop")
}

pub(crate) fn optimize_function_with_control<C: SsaWorkControl + ?Sized>(
    func: &mut SSAFunction,
    config: &OptimizationConfig,
    control: &C,
) -> Result<OptimizationStats, SsaExecutionStopReason> {
    optimize_function_with_interface_and_control(func, config, None, control)
}

pub(crate) fn optimize_function_with_interface_and_control<C: SsaWorkControl + ?Sized>(
    func: &mut SSAFunction,
    config: &OptimizationConfig,
    function_interface: Option<&SourceFunctionInterface>,
    control: &C,
) -> Result<OptimizationStats, SsaExecutionStopReason> {
    control.poll()?;
    let mut stats = OptimizationStats::default();
    let max_iters = config.max_iterations.max(1);

    if config.enable_sccp {
        let (consts, executable_edges) = sccp_with_control(func, control)?;
        control.poll()?;
        apply_sccp_results(
            func,
            &consts,
            &executable_edges,
            function_interface,
            &mut stats,
        );
    }

    for _ in 0..max_iters {
        control.poll()?;
        let mut changed = false;

        if config.enable_inst_combine && inst_combine(func, &mut stats) {
            changed = true;
        }

        stats.iterations += 1;
        if !changed {
            break;
        }
    }

    control.poll()?;
    Ok(stats)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct VarKey {
    name: String,
    version: u32,
    size: u32,
    rename_disambiguator: u32,
}

type SccpResult = (HashMap<VarKey, u64>, HashSet<(u64, u64)>);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LatticeValue {
    Top,
    Const(u64),
    Bottom,
}

impl LatticeValue {
    fn meet(self, other: Self) -> Self {
        match (self, other) {
            (LatticeValue::Top, x) | (x, LatticeValue::Top) => x,
            (LatticeValue::Bottom, _) | (_, LatticeValue::Bottom) => LatticeValue::Bottom,
            (LatticeValue::Const(a), LatticeValue::Const(b)) => {
                if a == b {
                    LatticeValue::Const(a)
                } else {
                    LatticeValue::Bottom
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
enum UseLocation {
    Phi { block_addr: u64, phi_idx: usize },
    Op { block_addr: u64, op_idx: usize },
}

impl VarKey {
    fn from_var(var: &SSAVar) -> Self {
        Self {
            name: var.name.clone(),
            version: var.version,
            size: var.size,
            rename_disambiguator: var.rename_disambiguator(),
        }
    }
}

impl Ord for VarKey {
    fn cmp(&self, other: &Self) -> Ordering {
        (
            self.name.as_str(),
            self.version,
            self.size,
            self.rename_disambiguator,
        )
            .cmp(&(
                other.name.as_str(),
                other.version,
                other.size,
                other.rename_disambiguator,
            ))
    }
}

impl PartialOrd for VarKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn build_use_map(func: &SSAFunction) -> HashMap<VarKey, Vec<UseLocation>> {
    let mut uses = HashMap::new();
    for block in func.blocks() {
        block.for_each_source(|src| {
            let use_loc = match src.site {
                SourceSite::Phi { phi_idx, .. } => UseLocation::Phi {
                    block_addr: block.addr,
                    phi_idx,
                },
                SourceSite::Op { op_idx, .. } => UseLocation::Op {
                    block_addr: block.addr,
                    op_idx,
                },
            };
            uses.entry(VarKey::from_var(src.var))
                .or_insert_with(Vec::new)
                .push(use_loc);
        });
    }
    uses
}

fn get_lattice_value(var: &SSAVar, lattice: &HashMap<VarKey, LatticeValue>) -> LatticeValue {
    if let Some(val) = const_value(var) {
        return LatticeValue::Const(val);
    }
    lattice
        .get(&VarKey::from_var(var))
        .copied()
        .unwrap_or(LatticeValue::Top)
}

fn init_if_input(var: &SSAVar, lattice: &mut HashMap<VarKey, LatticeValue>) {
    if var.version == 0 && var.constant_bits().is_none() {
        lattice
            .entry(VarKey::from_var(var))
            .or_insert(LatticeValue::Bottom);
    }
}

fn update_lattice(
    lattice: &mut HashMap<VarKey, LatticeValue>,
    var: &SSAVar,
    new_val: LatticeValue,
) -> bool {
    let key = VarKey::from_var(var);
    let old_val = lattice.get(&key).copied().unwrap_or(LatticeValue::Top);
    let merged = old_val.meet(new_val);
    if merged != old_val {
        lattice.insert(key, merged);
        return true;
    }
    false
}

fn evaluate_op_sccp(op: &SSAOp, lattice: &HashMap<VarKey, LatticeValue>) -> LatticeValue {
    if matches!(
        op,
        SSAOp::Load { .. }
            | SSAOp::Store { .. }
            | SSAOp::Call { .. }
            | SSAOp::CallInd { .. }
            | SSAOp::CallOther { .. }
            | SSAOp::CpuId { .. }
            | SSAOp::New { .. }
    ) {
        return LatticeValue::Bottom;
    }

    let mut has_top = false;
    let mut temp_consts = HashMap::new();
    for src in op.sources() {
        match get_lattice_value(src, lattice) {
            LatticeValue::Bottom => return LatticeValue::Bottom,
            LatticeValue::Top => {
                has_top = true;
            }
            LatticeValue::Const(c) => {
                temp_consts.insert(VarKey::from_var(src), c);
            }
        }
    }

    if has_top {
        return LatticeValue::Top;
    }

    match eval_const_op(op, &temp_consts) {
        Some(c) => LatticeValue::Const(c),
        None => LatticeValue::Bottom,
    }
}

fn evaluate_phi_sccp(
    phi: &PhiNode,
    executable: &HashSet<(u64, u64)>,
    lattice: &HashMap<VarKey, LatticeValue>,
    block_addr: u64,
) -> LatticeValue {
    let mut value = LatticeValue::Top;
    for (pred_addr, src) in &phi.sources {
        if !executable.contains(&(*pred_addr, block_addr)) {
            continue;
        }
        value = value.meet(get_lattice_value(src, lattice));
    }
    value
}

fn find_cbranch_condition(
    func: &SSAFunction,
    block_addr: u64,
    lattice: &HashMap<VarKey, LatticeValue>,
) -> LatticeValue {
    let Some(block) = func.get_block(block_addr) else {
        return LatticeValue::Bottom;
    };
    for op in block.ops.iter().rev() {
        if let SSAOp::CBranch { cond, .. } = op {
            return get_lattice_value(cond, lattice);
        }
    }
    LatticeValue::Bottom
}

fn evaluate_terminator_sccp(
    func: &SSAFunction,
    block_addr: u64,
    lattice: &HashMap<VarKey, LatticeValue>,
    cfg_worklist: &mut VecDeque<(u64, u64)>,
) {
    let Some(cfg_block) = func.cfg().get_block(block_addr) else {
        return;
    };

    match &cfg_block.terminator {
        BlockTerminator::ConditionalBranch {
            true_target,
            false_target,
        } => match find_cbranch_condition(func, block_addr, lattice) {
            LatticeValue::Const(0) => cfg_worklist.push_back((block_addr, *false_target)),
            LatticeValue::Const(_) => cfg_worklist.push_back((block_addr, *true_target)),
            LatticeValue::Top | LatticeValue::Bottom => {
                cfg_worklist.push_back((block_addr, *true_target));
                cfg_worklist.push_back((block_addr, *false_target));
            }
        },
        _ => {
            for succ in func.successors(block_addr) {
                cfg_worklist.push_back((block_addr, succ));
            }
        }
    }
}

#[cfg(test)]
fn sccp(func: &SSAFunction) -> (HashMap<VarKey, u64>, HashSet<(u64, u64)>) {
    sccp_with_control(func, &UncheckedSsaWorkControl).expect("unchecked SCCP cannot stop")
}

fn sccp_with_control<C: SsaWorkControl + ?Sized>(
    func: &SSAFunction,
    control: &C,
) -> Result<SccpResult, SsaExecutionStopReason> {
    control.poll()?;
    let mut lattice = HashMap::new();
    let mut executable = HashSet::new();
    let mut block_visited = HashSet::new();
    let mut cfg_worklist = VecDeque::new();
    let mut ssa_worklist = VecDeque::new();
    let use_map = build_use_map(func);

    for block in func.blocks() {
        control.poll()?;
        block.for_each_def(|def| init_if_input(def.var, &mut lattice));
        block.for_each_source(|src| init_if_input(src.var, &mut lattice));
    }

    cfg_worklist.push_back((u64::MAX, func.entry));

    while !cfg_worklist.is_empty() || !ssa_worklist.is_empty() {
        control.poll()?;
        while let Some((from, to)) = cfg_worklist.pop_front() {
            control.poll()?;
            if !executable.insert((from, to)) {
                continue;
            }

            let Some(block) = func.get_block(to) else {
                continue;
            };

            for phi in &block.phis {
                control.poll()?;
                let new_val = evaluate_phi_sccp(phi, &executable, &lattice, to);
                if update_lattice(&mut lattice, &phi.dst, new_val) {
                    ssa_worklist.push_back(VarKey::from_var(&phi.dst));
                }
            }

            if block_visited.insert(to) {
                for op in &block.ops {
                    control.poll()?;
                    if let Some(dst) = op.dst() {
                        let new_val = evaluate_op_sccp(op, &lattice);
                        if update_lattice(&mut lattice, dst, new_val) {
                            ssa_worklist.push_back(VarKey::from_var(dst));
                        }
                    }
                }
                evaluate_terminator_sccp(func, to, &lattice, &mut cfg_worklist);
            }
        }

        while let Some(var_key) = ssa_worklist.pop_front() {
            control.poll()?;
            let Some(use_locs) = use_map.get(&var_key) else {
                continue;
            };
            for use_loc in use_locs {
                control.poll()?;
                match use_loc {
                    UseLocation::Phi {
                        block_addr,
                        phi_idx,
                    } => {
                        if !block_visited.contains(block_addr) {
                            continue;
                        }
                        let Some(block) = func.get_block(*block_addr) else {
                            continue;
                        };
                        let Some(phi) = block.phis.get(*phi_idx) else {
                            continue;
                        };
                        let new_val = evaluate_phi_sccp(phi, &executable, &lattice, *block_addr);
                        if update_lattice(&mut lattice, &phi.dst, new_val) {
                            ssa_worklist.push_back(VarKey::from_var(&phi.dst));
                        }
                    }
                    UseLocation::Op { block_addr, op_idx } => {
                        if !block_visited.contains(block_addr) {
                            continue;
                        }
                        let Some(block) = func.get_block(*block_addr) else {
                            continue;
                        };
                        let Some(op) = block.ops.get(*op_idx) else {
                            continue;
                        };

                        if let Some(dst) = op.dst() {
                            let new_val = evaluate_op_sccp(op, &lattice);
                            if update_lattice(&mut lattice, dst, new_val) {
                                ssa_worklist.push_back(VarKey::from_var(dst));
                            }
                        }

                        if matches!(op, SSAOp::CBranch { .. }) {
                            evaluate_terminator_sccp(
                                func,
                                *block_addr,
                                &lattice,
                                &mut cfg_worklist,
                            );
                        }
                    }
                }
            }
        }
    }

    let consts = lattice
        .iter()
        .filter_map(|(k, v)| match v {
            LatticeValue::Const(c) => Some((k.clone(), *c)),
            LatticeValue::Top | LatticeValue::Bottom => None,
        })
        .collect();
    control.poll()?;
    Ok((consts, executable))
}

fn const_value(var: &SSAVar) -> Option<u64> {
    var.constant_bits()
}

fn mask_for_bits(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else if bits == 0 {
        0
    } else {
        (1u64 << bits) - 1
    }
}

fn sign_extend(value: u64, bits: u32) -> i64 {
    if bits == 0 {
        return 0;
    }
    if bits >= 64 {
        return value as i64;
    }
    let shift = 64 - bits;
    ((value << shift) as i64) >> shift
}

fn const_for_var(var: &SSAVar, consts: &HashMap<VarKey, u64>) -> Option<u64> {
    if let Some(val) = const_value(var) {
        return Some(val);
    }
    consts.get(&VarKey::from_var(var)).copied()
}

fn eval_const_op(op: &SSAOp, consts: &HashMap<VarKey, u64>) -> Option<u64> {
    use SSAOp::*;

    let dst = op.dst()?;
    let bits = dst.size.saturating_mul(8);
    let mask = mask_for_bits(bits);

    let unary = |src: &SSAVar| const_for_var(src, consts);
    let binary =
        |a: &SSAVar, b: &SSAVar| Some((const_for_var(a, consts)?, const_for_var(b, consts)?));

    let val = match op {
        Copy { src, .. } => unary(src)?,
        IntNegate { src, .. } => (!unary(src)?).wrapping_add(1),
        IntNot { src, .. } => !unary(src)?,
        BoolNot { src, .. } => (unary(src)? == 0) as u64,
        IntZExt { src, .. } => unary(src)?,
        IntSExt { src, .. } => {
            let src_bits = src.size.saturating_mul(8);
            sign_extend(unary(src)?, src_bits) as u64
        }
        Trunc { src, .. } => unary(src)? & mask_for_bits(bits),
        IntAdd { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            a.wrapping_add(b)
        }
        IntSub { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            a.wrapping_sub(b)
        }
        IntMult { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            a.wrapping_mul(b)
        }
        IntDiv { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            if b == 0 {
                return None;
            }
            a / b
        }
        IntSDiv { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            if b == 0 {
                return None;
            }
            let signed = sign_extend(a, bits) / sign_extend(b, bits);
            signed as u64
        }
        IntRem { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            if b == 0 {
                return None;
            }
            a % b
        }
        IntSRem { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            if b == 0 {
                return None;
            }
            let signed = sign_extend(a, bits) % sign_extend(b, bits);
            signed as u64
        }
        IntAnd { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            a & b
        }
        IntOr { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            a | b
        }
        IntXor { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            a ^ b
        }
        IntLeft { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            if b >= bits as u64 {
                return None;
            }
            a.wrapping_shl(b as u32)
        }
        IntRight { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            if b >= bits as u64 {
                return None;
            }
            a >> (b as u32)
        }
        IntSRight { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            if b >= bits as u64 {
                return None;
            }
            let signed = sign_extend(a, bits) >> (b as u32);
            signed as u64
        }
        IntEqual { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            (a == b) as u64
        }
        IntNotEqual { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            (a != b) as u64
        }
        IntLess { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            (a < b) as u64
        }
        IntLessEqual { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            (a <= b) as u64
        }
        IntSLess { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            (sign_extend(a, bits) < sign_extend(b, bits)) as u64
        }
        IntSLessEqual { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            (sign_extend(a, bits) <= sign_extend(b, bits)) as u64
        }
        BoolAnd { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            ((a != 0) && (b != 0)) as u64
        }
        BoolOr { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            ((a != 0) || (b != 0)) as u64
        }
        BoolXor { a, b, .. } => {
            let (a, b) = binary(a, b)?;
            ((a != 0) ^ (b != 0)) as u64
        }
        Piece { hi, lo, .. } => {
            let hi_val = const_for_var(hi, consts)?;
            let lo_val = const_for_var(lo, consts)?;
            let lo_bits = lo.size.saturating_mul(8);
            if lo_bits >= 64 {
                return None;
            }
            (hi_val << lo_bits) | (lo_val & mask_for_bits(lo_bits))
        }
        Subpiece { src, offset, .. } => {
            let val = unary(src)?;
            let shift = offset.saturating_mul(8);
            if shift >= 64 {
                return None;
            }
            val >> shift
        }
        PopCount { src, .. } => (unary(src)? & mask).count_ones() as u64,
        Lzcount { src, .. } => {
            let val = unary(src)? & mask;
            let width = bits.min(64);
            if width == 0 {
                0
            } else {
                let leading = val.leading_zeros();
                (leading.saturating_sub(64 - width)) as u64
            }
        }
        PtrAdd {
            base,
            index,
            element_size,
            ..
        } => {
            let (base, index) = binary(base, index)?;
            base.wrapping_add(index.wrapping_mul(*element_size as u64))
        }
        PtrSub {
            base,
            index,
            element_size,
            ..
        } => {
            let (base, index) = binary(base, index)?;
            base.wrapping_sub(index.wrapping_mul(*element_size as u64))
        }
        _ => return None,
    };

    Some(val & mask)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TerminalStorageProjection {
    carrier: CanonicalStorageId,
    logical: CanonicalStorageId,
}

fn coherent_return_projection(
    function_interface: Option<&SourceFunctionInterface>,
) -> Option<TerminalStorageProjection> {
    let interface = function_interface?;
    let SourceFunctionReturn::Register { storage } = interface.return_kind() else {
        return None;
    };
    let logical = interface.return_logical_value()?;
    let graph = interface.type_graph()?;
    let source_type = graph
        .types()
        .get(usize::try_from(logical.type_id()).ok()?)?;
    let carrier = logical.carrier();
    let storage_bits = u64::from(storage.size).checked_mul(8)?;
    if storage.space != CanonicalStorageSpace::Register
        || storage.size == 0
        || carrier.offset_bits() != 0
        || carrier.size_bits() == 0
        || carrier.size_bits() != source_type.size_bits()
        || carrier.size_bits() % 8 != 0
        || carrier.size_bits() > storage_bits
    {
        return None;
    }
    let logical = match carrier.kind() {
        SourceCarrierKind::Full if carrier.size_bits() == storage_bits => storage,
        SourceCarrierKind::LowBits
            if carrier.size_bits() < storage_bits
                && matches!(
                    source_type.kind(),
                    SourceTypeKind::SignedInteger | SourceTypeKind::UnsignedInteger
                ) =>
        {
            CanonicalStorageId {
                space: storage.space,
                offset: storage.offset,
                size: u32::try_from(carrier.size_bits() / 8).ok()?,
            }
        }
        _ => return None,
    };
    Some(TerminalStorageProjection {
        carrier: storage,
        logical,
    })
}

fn replace_sources_with_constants(
    func: &mut SSAFunction,
    consts: &HashMap<VarKey, u64>,
    function_interface: Option<&SourceFunctionInterface>,
    stats: &mut OptimizationStats,
) -> bool {
    let mut changed = false;
    let block_addrs = func.block_addrs().to_vec();
    let return_storage =
        coherent_return_projection(function_interface).map(|projection| projection.carrier);

    for addr in block_addrs {
        let is_return_block = func
            .cfg()
            .get_block(addr)
            .is_some_and(|cfg_block| cfg_block.is_return());
        let Some(block) = func.get_block_mut(addr) else {
            continue;
        };

        for phi in &mut block.phis {
            let preserve_phi_sources = is_return_block
                && return_storage.is_some_and(|storage| phi.canonical_storage == Some(storage));
            for (_, src) in &mut phi.sources {
                if preserve_phi_sources {
                    continue;
                }
                let key = VarKey::from_var(src);
                if let Some(val) = consts.get(&key).copied() {
                    let new_var = SSAVar::constant(val, src.size);
                    if &new_var != src {
                        *src = new_var;
                        stats.constants_propagated += 1;
                        changed = true;
                    }
                }
            }
        }

        for op in &mut block.ops {
            let new_op = map_sources_in_op(op, &|var| {
                let key = VarKey::from_var(var);
                if let Some(val) = consts.get(&key).copied() {
                    SSAVar::constant(val, var.size)
                } else {
                    var.clone()
                }
            });
            if &new_op != op {
                let delta = count_source_replacements(op, &new_op);
                if delta > 0 {
                    stats.constants_propagated += delta;
                }
                *op = new_op;
                changed = true;
            }
        }
    }

    changed
}

fn apply_sccp_results(
    func: &mut SSAFunction,
    consts: &HashMap<VarKey, u64>,
    executable_edges: &HashSet<(u64, u64)>,
    function_interface: Option<&SourceFunctionInterface>,
    stats: &mut OptimizationStats,
) -> bool {
    let mut changed = false;
    let mut cfg_changed = false;

    if replace_sources_with_constants(func, consts, function_interface, stats) {
        changed = true;
    }
    stats.sccp_constants_found = consts.len();

    #[derive(Debug, Clone, Copy)]
    struct BranchRewrite {
        block_addr: u64,
        op_idx: usize,
        keep_target: u64,
        dead_target: u64,
        take_true: bool,
    }

    let mut rewrites = Vec::new();
    for &addr in func.block_addrs() {
        let Some(block) = func.get_block(addr) else {
            continue;
        };
        let Some(cfg_block) = func.cfg().get_block(addr) else {
            continue;
        };
        let BlockTerminator::ConditionalBranch {
            true_target,
            false_target,
        } = &cfg_block.terminator
        else {
            continue;
        };

        for (op_idx, op) in block.ops.iter().enumerate() {
            if let SSAOp::CBranch { cond, .. } = op
                && let Some(value) = const_value(cond)
            {
                let take_true = value != 0;
                let (keep_target, dead_target) = if take_true {
                    (*true_target, *false_target)
                } else {
                    (*false_target, *true_target)
                };
                rewrites.push(BranchRewrite {
                    block_addr: addr,
                    op_idx,
                    keep_target,
                    dead_target,
                    take_true,
                });
                break;
            }
        }
    }

    for rw in rewrites {
        if let Some(block) = func.get_block_mut(rw.block_addr)
            && let Some(op) = block.ops.get_mut(rw.op_idx)
        {
            if rw.take_true {
                if let SSAOp::CBranch { target, .. } = op {
                    *op = SSAOp::Branch {
                        target: target.clone(),
                    };
                }
            } else {
                *op = SSAOp::Nop;
            }
        }

        func.cfg_mut().remove_edge(rw.block_addr, rw.dead_target);
        func.cfg_mut().set_terminator(
            rw.block_addr,
            BlockTerminator::Branch {
                target: rw.keep_target,
            },
        );
        func.remove_phi_source(rw.dead_target, rw.block_addr);
        stats.sccp_edges_pruned += 1;
        changed = true;
        cfg_changed = true;
    }

    let block_addrs = func.block_addrs().to_vec();
    for addr in block_addrs {
        let succs = func.successors(addr);
        for succ in succs {
            if !executable_edges.contains(&(addr, succ)) {
                func.cfg_mut().remove_edge(addr, succ);
                func.remove_phi_source(succ, addr);
                stats.sccp_edges_pruned += 1;
                changed = true;
                cfg_changed = true;
            }
        }
    }

    let mut reachable = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(func.entry);
    while let Some(addr) = queue.pop_front() {
        if !reachable.insert(addr) {
            continue;
        }
        for succ in func.successors(addr) {
            queue.push_back(succ);
        }
    }

    let all_addrs = func.block_addrs().to_vec();
    for addr in all_addrs {
        if !reachable.contains(&addr) {
            let succs = func.successors(addr);
            for succ in succs {
                func.remove_phi_source(succ, addr);
            }
            func.remove_block(addr);
            stats.sccp_blocks_removed += 1;
            changed = true;
            cfg_changed = true;
        }
    }

    if cfg_changed {
        func.refresh_after_cfg_mutation();
    }

    changed
}

fn count_source_replacements(before: &SSAOp, after: &SSAOp) -> usize {
    let mut count = 0;
    let before_sources = before.sources();
    let after_sources = after.sources();
    for (a, b) in before_sources.iter().zip(after_sources.iter()) {
        if a != b {
            count += 1;
        }
    }
    count
}

fn inst_combine(func: &mut SSAFunction, stats: &mut OptimizationStats) -> bool {
    let mut changed = false;
    let block_addrs = func.block_addrs().to_vec();

    for addr in block_addrs {
        let Some(block) = func.get_block_mut(addr) else {
            continue;
        };
        for op in &mut block.ops {
            if let Some(new_op) = simplify_op(op)
                && &new_op != op
            {
                *op = new_op;
                stats.ops_simplified += 1;
                changed = true;
            }
        }
    }

    changed
}

fn simplify_op(op: &SSAOp) -> Option<SSAOp> {
    use SSAOp::*;

    let dst = op.dst()?.clone();
    let bits = dst.size.saturating_mul(8);
    let mask = mask_for_bits(bits);

    let const_of = |var: &SSAVar| const_value(var);

    let make_const = |val: u64| SSAOp::Copy {
        dst: dst.clone(),
        src: SSAVar::constant(val & mask, dst.size),
    };

    let make_copy = |src: &SSAVar| SSAOp::Copy {
        dst: dst.clone(),
        src: src.clone(),
    };

    let simplified = match op {
        Copy { .. } => return None,
        IntAdd { a, b, .. } => match (const_of(a), const_of(b)) {
            (Some(0), _) => make_copy(b),
            (_, Some(0)) => make_copy(a),
            (Some(av), Some(bv)) => make_const(av.wrapping_add(bv)),
            _ => return None,
        },
        IntSub { a, b, .. } => match (const_of(a), const_of(b)) {
            (_, Some(0)) => make_copy(a),
            _ if a == b => make_const(0),
            (Some(av), Some(bv)) => make_const(av.wrapping_sub(bv)),
            _ => return None,
        },
        IntMult { a, b, .. } => match (const_of(a), const_of(b)) {
            (Some(0), _) | (_, Some(0)) => make_const(0),
            (Some(1), _) => make_copy(b),
            (_, Some(1)) => make_copy(a),
            (Some(av), Some(bv)) => make_const(av.wrapping_mul(bv)),
            _ => return None,
        },
        IntDiv { a, b, .. } => match (const_of(a), const_of(b)) {
            (_, Some(1)) => make_copy(a),
            (Some(_), Some(0)) => return None,
            (Some(av), Some(bv)) => make_const(av / bv),
            _ => return None,
        },
        IntSDiv { a, b, .. } => match (const_of(a), const_of(b)) {
            (_, Some(1)) => make_copy(a),
            (Some(_), Some(0)) => return None,
            (Some(av), Some(bv)) => {
                let res = sign_extend(av, bits) / sign_extend(bv, bits);
                make_const(res as u64)
            }
            _ => return None,
        },
        IntRem { a, b, .. } => match (const_of(a), const_of(b)) {
            (Some(_), Some(0)) => return None,
            (Some(av), Some(bv)) => make_const(av % bv),
            _ => return None,
        },
        IntSRem { a, b, .. } => match (const_of(a), const_of(b)) {
            (Some(_), Some(0)) => return None,
            (Some(av), Some(bv)) => {
                let res = sign_extend(av, bits) % sign_extend(bv, bits);
                make_const(res as u64)
            }
            _ => return None,
        },
        IntNegate { src, .. } => match const_of(src) {
            Some(val) => make_const((!val).wrapping_add(1)),
            _ => return None,
        },
        IntAnd { a, b, .. } => match (const_of(a), const_of(b)) {
            (Some(0), _) | (_, Some(0)) => make_const(0),
            (Some(av), Some(bv)) => make_const(av & bv),
            (Some(av), _) if av == mask => make_copy(b),
            (_, Some(bv)) if bv == mask => make_copy(a),
            _ => return None,
        },
        IntOr { a, b, .. } => match (const_of(a), const_of(b)) {
            (Some(0), _) => make_copy(b),
            (_, Some(0)) => make_copy(a),
            (Some(av), Some(bv)) => make_const(av | bv),
            _ => return None,
        },
        IntXor { a, b, .. } => match (const_of(a), const_of(b)) {
            (Some(0), _) => make_copy(b),
            (_, Some(0)) => make_copy(a),
            (Some(av), Some(bv)) => make_const(av ^ bv),
            _ if a == b => make_const(0),
            _ => return None,
        },
        IntNot { src, .. } => match const_of(src) {
            Some(val) => make_const(!val),
            _ => return None,
        },
        IntLeft { a, b, .. } | IntRight { a, b, .. } | IntSRight { a, b, .. } => {
            match (const_of(a), const_of(b)) {
                (Some(av), Some(bv)) => {
                    if bv >= bits as u64 {
                        return None;
                    }
                    let res = match op {
                        IntLeft { .. } => av.wrapping_shl(bv as u32),
                        IntRight { .. } => av >> (bv as u32),
                        IntSRight { .. } => (sign_extend(av, bits) >> (bv as u32)) as u64,
                        _ => av,
                    };
                    make_const(res)
                }
                (_, Some(0)) => make_copy(a),
                _ => return None,
            }
        }
        IntEqual { a, b, .. }
        | IntNotEqual { a, b, .. }
        | IntLess { a, b, .. }
        | IntLessEqual { a, b, .. }
        | IntSLess { a, b, .. }
        | IntSLessEqual { a, b, .. } => {
            if a == b {
                let val = matches!(
                    op,
                    IntEqual { .. } | IntLessEqual { .. } | IntSLessEqual { .. }
                ) as u64;
                return Some(make_const(val));
            }
            match (const_of(a), const_of(b)) {
                (Some(av), Some(bv)) => {
                    let result = match op {
                        IntEqual { .. } => av == bv,
                        IntNotEqual { .. } => av != bv,
                        IntLess { .. } => av < bv,
                        IntLessEqual { .. } => av <= bv,
                        IntSLess { .. } => sign_extend(av, bits) < sign_extend(bv, bits),
                        IntSLessEqual { .. } => sign_extend(av, bits) <= sign_extend(bv, bits),
                        _ => false,
                    };
                    make_const(result as u64)
                }
                _ => return None,
            }
        }
        BoolNot { src, .. } => match const_of(src) {
            Some(val) => make_const((val == 0) as u64),
            _ => return None,
        },
        BoolAnd { a, b, .. } | BoolOr { a, b, .. } | BoolXor { a, b, .. } => {
            match (const_of(a), const_of(b)) {
                (Some(av), Some(bv)) => {
                    let a = av != 0;
                    let b = bv != 0;
                    let res = match op {
                        BoolAnd { .. } => a && b,
                        BoolOr { .. } => a || b,
                        BoolXor { .. } => a ^ b,
                        _ => false,
                    };
                    make_const(res as u64)
                }
                (Some(0), _) if matches!(op, BoolAnd { .. }) => make_const(0),
                (_, Some(0)) if matches!(op, BoolAnd { .. }) => make_const(0),
                (Some(1), _) if matches!(op, BoolOr { .. }) => make_const(1),
                (_, Some(1)) if matches!(op, BoolOr { .. }) => make_const(1),
                _ => return None,
            }
        }
        IntZExt { src, .. } => match const_of(src) {
            Some(val) => make_const(val),
            _ if src.size == dst.size => make_copy(src),
            _ => return None,
        },
        IntSExt { src, .. } => match const_of(src) {
            Some(val) => {
                let src_bits = src.size.saturating_mul(8);
                make_const(sign_extend(val, src_bits) as u64)
            }
            _ if src.size == dst.size => make_copy(src),
            _ => return None,
        },
        Trunc { src, .. } => match const_of(src) {
            Some(val) => make_const(val & mask_for_bits(bits)),
            _ => return None,
        },
        Piece { hi, lo, .. } => match (const_of(hi), const_of(lo)) {
            (Some(h), Some(l)) => {
                let lo_bits = lo.size.saturating_mul(8);
                if lo_bits >= 64 {
                    return None;
                }
                make_const((h << lo_bits) | (l & mask_for_bits(lo_bits)))
            }
            _ => return None,
        },
        Subpiece { src, offset, .. } => match const_of(src) {
            Some(val) => {
                let shift = offset.saturating_mul(8);
                if shift >= 64 {
                    return None;
                }
                make_const(val >> shift)
            }
            _ => return None,
        },
        PtrAdd {
            base,
            index,
            element_size,
            ..
        } => match (const_of(base), const_of(index)) {
            (Some(b), Some(i)) => make_const(b.wrapping_add(i.wrapping_mul(*element_size as u64))),
            _ => return None,
        },
        PtrSub {
            base,
            index,
            element_size,
            ..
        } => match (const_of(base), const_of(index)) {
            (Some(b), Some(i)) => make_const(b.wrapping_sub(i.wrapping_mul(*element_size as u64))),
            _ => return None,
        },
        _ => return None,
    };

    Some(simplified)
}

pub(crate) fn map_sources_in_op<F>(op: &SSAOp, map: &F) -> SSAOp
where
    F: Fn(&SSAVar) -> SSAVar,
{
    use SSAOp::*;

    match op {
        Phi { dst, sources } => Phi {
            dst: dst.clone(),
            sources: sources.iter().map(map).collect(),
        },
        Copy { dst, src } => Copy {
            dst: dst.clone(),
            src: map(src),
        },
        Load { dst, space, addr } => Load {
            dst: dst.clone(),
            space: *space,
            addr: map(addr),
        },
        Store { space, addr, val } => Store {
            space: *space,
            addr: map(addr),
            val: map(val),
        },
        Fence { ordering } => Fence {
            ordering: *ordering,
        },
        LoadLinked {
            dst,
            space,
            addr,
            ordering,
        } => LoadLinked {
            dst: dst.clone(),
            space: *space,
            addr: map(addr),
            ordering: *ordering,
        },
        StoreConditional {
            result,
            space,
            addr,
            val,
            ordering,
        } => StoreConditional {
            result: result.clone(),
            space: *space,
            addr: map(addr),
            val: map(val),
            ordering: *ordering,
        },
        AtomicCAS {
            dst,
            space,
            addr,
            expected,
            replacement,
            ordering,
        } => AtomicCAS {
            dst: dst.clone(),
            space: *space,
            addr: map(addr),
            expected: map(expected),
            replacement: map(replacement),
            ordering: *ordering,
        },
        LoadGuarded {
            dst,
            space,
            addr,
            guard,
            ordering,
        } => LoadGuarded {
            dst: dst.clone(),
            space: *space,
            addr: map(addr),
            guard: map(guard),
            ordering: *ordering,
        },
        StoreGuarded {
            space,
            addr,
            val,
            guard,
            ordering,
        } => StoreGuarded {
            space: *space,
            addr: map(addr),
            val: map(val),
            guard: map(guard),
            ordering: *ordering,
        },
        IntAdd { dst, a, b } => IntAdd {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntSub { dst, a, b } => IntSub {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntMult { dst, a, b } => IntMult {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntDiv { dst, a, b } => IntDiv {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntSDiv { dst, a, b } => IntSDiv {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntRem { dst, a, b } => IntRem {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntSRem { dst, a, b } => IntSRem {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntNegate { dst, src } => IntNegate {
            dst: dst.clone(),
            src: map(src),
        },
        IntCarry { dst, a, b } => IntCarry {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntSCarry { dst, a, b } => IntSCarry {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntSBorrow { dst, a, b } => IntSBorrow {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntAnd { dst, a, b } => IntAnd {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntOr { dst, a, b } => IntOr {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntXor { dst, a, b } => IntXor {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntNot { dst, src } => IntNot {
            dst: dst.clone(),
            src: map(src),
        },
        IntLeft { dst, a, b } => IntLeft {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntRight { dst, a, b } => IntRight {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntSRight { dst, a, b } => IntSRight {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntEqual { dst, a, b } => IntEqual {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntNotEqual { dst, a, b } => IntNotEqual {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntLess { dst, a, b } => IntLess {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntSLess { dst, a, b } => IntSLess {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntLessEqual { dst, a, b } => IntLessEqual {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntSLessEqual { dst, a, b } => IntSLessEqual {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        IntZExt { dst, src } => IntZExt {
            dst: dst.clone(),
            src: map(src),
        },
        IntSExt { dst, src } => IntSExt {
            dst: dst.clone(),
            src: map(src),
        },
        BoolNot { dst, src } => BoolNot {
            dst: dst.clone(),
            src: map(src),
        },
        BoolAnd { dst, a, b } => BoolAnd {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        BoolOr { dst, a, b } => BoolOr {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        BoolXor { dst, a, b } => BoolXor {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        Piece { dst, hi, lo } => Piece {
            dst: dst.clone(),
            hi: map(hi),
            lo: map(lo),
        },
        Subpiece { dst, src, offset } => Subpiece {
            dst: dst.clone(),
            src: map(src),
            offset: *offset,
        },
        PopCount { dst, src } => PopCount {
            dst: dst.clone(),
            src: map(src),
        },
        Lzcount { dst, src } => Lzcount {
            dst: dst.clone(),
            src: map(src),
        },
        Branch { target } => Branch {
            target: map(target),
        },
        CBranch { target, cond } => CBranch {
            target: map(target),
            cond: map(cond),
        },
        BranchInd { target } => BranchInd {
            target: map(target),
        },
        Call { target } => Call {
            target: map(target),
        },
        CallInd { target } => CallInd {
            target: map(target),
        },
        CallDefine { dst } => CallDefine { dst: dst.clone() },
        CallRestore { dst, src } => CallRestore {
            dst: dst.clone(),
            src: map(src),
        },
        Return { target } => Return {
            target: map(target),
        },
        FloatAdd { dst, a, b } => FloatAdd {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        FloatSub { dst, a, b } => FloatSub {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        FloatMult { dst, a, b } => FloatMult {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        FloatDiv { dst, a, b } => FloatDiv {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        FloatNeg { dst, src } => FloatNeg {
            dst: dst.clone(),
            src: map(src),
        },
        FloatAbs { dst, src } => FloatAbs {
            dst: dst.clone(),
            src: map(src),
        },
        FloatSqrt { dst, src } => FloatSqrt {
            dst: dst.clone(),
            src: map(src),
        },
        FloatCeil { dst, src } => FloatCeil {
            dst: dst.clone(),
            src: map(src),
        },
        FloatFloor { dst, src } => FloatFloor {
            dst: dst.clone(),
            src: map(src),
        },
        FloatRound { dst, src } => FloatRound {
            dst: dst.clone(),
            src: map(src),
        },
        FloatNaN { dst, src } => FloatNaN {
            dst: dst.clone(),
            src: map(src),
        },
        FloatEqual { dst, a, b } => FloatEqual {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        FloatNotEqual { dst, a, b } => FloatNotEqual {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        FloatLess { dst, a, b } => FloatLess {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        FloatLessEqual { dst, a, b } => FloatLessEqual {
            dst: dst.clone(),
            a: map(a),
            b: map(b),
        },
        Int2Float { dst, src } => Int2Float {
            dst: dst.clone(),
            src: map(src),
        },
        Float2Int { dst, src } => Float2Int {
            dst: dst.clone(),
            src: map(src),
        },
        FloatFloat { dst, src } => FloatFloat {
            dst: dst.clone(),
            src: map(src),
        },
        Trunc { dst, src } => Trunc {
            dst: dst.clone(),
            src: map(src),
        },
        CallOther {
            output,
            userop,
            inputs,
        } => CallOther {
            output: output.clone(),
            userop: *userop,
            inputs: inputs.iter().map(map).collect(),
        },
        CpuId { dst } => CpuId { dst: dst.clone() },
        PtrAdd {
            dst,
            base,
            index,
            element_size,
        } => PtrAdd {
            dst: dst.clone(),
            base: map(base),
            index: map(index),
            element_size: *element_size,
        },
        PtrSub {
            dst,
            base,
            index,
            element_size,
        } => PtrSub {
            dst: dst.clone(),
            base: map(base),
            index: map(index),
            element_size: *element_size,
        },
        SegmentOp {
            dst,
            segment,
            offset,
        } => SegmentOp {
            dst: dst.clone(),
            segment: map(segment),
            offset: map(offset),
        },
        New { dst, src } => New {
            dst: dst.clone(),
            src: map(src),
        },
        Cast { dst, src } => Cast {
            dst: dst.clone(),
            src: map(src),
        },
        Extract { dst, src, position } => Extract {
            dst: dst.clone(),
            src: map(src),
            position: map(position),
        },
        Insert {
            dst,
            src,
            value,
            position,
        } => Insert {
            dst: dst.clone(),
            src: map(src),
            value: map(value),
            position: map(position),
        },
        Select {
            dst,
            cond,
            if_true,
            if_false,
        } => Select {
            dst: dst.clone(),
            cond: map(cond),
            if_true: map(if_true),
            if_false: map(if_false),
        },
        Nop => Nop,
        Unimplemented => Unimplemented,
        Breakpoint => Breakpoint,
    }
}

#[cfg(test)]
mod sccp_tests {
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

    fn raw_func(blocks: Vec<R2ILBlock>) -> SSAFunction {
        SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA function should build")
    }

    #[test]
    fn meet_top_top() {
        assert_eq!(LatticeValue::Top.meet(LatticeValue::Top), LatticeValue::Top);
    }

    #[test]
    fn meet_top_const() {
        assert_eq!(
            LatticeValue::Top.meet(LatticeValue::Const(5)),
            LatticeValue::Const(5)
        );
    }

    #[test]
    fn meet_const_same() {
        assert_eq!(
            LatticeValue::Const(5).meet(LatticeValue::Const(5)),
            LatticeValue::Const(5)
        );
    }

    #[test]
    fn meet_const_diff() {
        assert_eq!(
            LatticeValue::Const(5).meet(LatticeValue::Const(7)),
            LatticeValue::Bottom
        );
    }

    #[test]
    fn meet_bottom_absorbs() {
        assert_eq!(
            LatticeValue::Bottom.meet(LatticeValue::Const(9)),
            LatticeValue::Bottom
        );
    }

    #[test]
    fn sccp_constant_identity_ignores_display_names() {
        let spoofed = SSAVar::new("const:2a", 0, 8);
        assert_eq!(const_value(&spoofed), None);
        let mut lattice = HashMap::new();
        init_if_input(&spoofed, &mut lattice);
        assert_eq!(
            lattice.get(&VarKey::from_var(&spoofed)),
            Some(&LatticeValue::Bottom)
        );

        let mut renamed = SSAVar::constant(0x2a, 8);
        renamed.name = "renamed-value".to_string();
        assert_eq!(const_value(&renamed), Some(0x2a));
    }

    #[test]
    fn sccp_simple_const() {
        let func = raw_func(vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: make_reg(0, 8),
                    a: make_const(5, 8),
                    b: make_const(3, 8),
                },
                R2ILOp::Return {
                    target: make_ram(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }]);

        let (consts, _) = sccp(&func);
        assert!(
            consts.values().any(|v| *v == 8),
            "SCCP should discover y = 8"
        );
    }

    #[test]
    fn sccp_phi_one_dead_edge() {
        let func = raw_func(vec![
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
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
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
                addr: 0x100c,
                size: 4,
                ops: vec![
                    R2ILOp::IntAdd {
                        dst: make_reg(8, 8),
                        a: make_reg(0, 8),
                        b: make_const(1, 8),
                    },
                    R2ILOp::Return {
                        target: make_ram(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ]);

        let (consts, executable) = sccp(&func);
        assert!(
            !executable.contains(&(0x1000, 0x1004)),
            "false edge should be non-executable"
        );
        assert!(
            consts.values().any(|v| *v == 2 || *v == 3),
            "phi should resolve to live input constant on the executable edge"
        );
    }

    #[test]
    fn sccp_params_stay_bottom() {
        let func = raw_func(vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: make_reg(8, 8),
                    a: make_reg(0, 8),
                    b: make_const(1, 8),
                },
                R2ILOp::Return {
                    target: make_ram(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }]);

        let (consts, _) = sccp(&func);
        assert!(
            !consts.keys().any(|k| k.name == "reg:8"),
            "param-derived values should not be treated as constants"
        );
    }

    #[test]
    fn sccp_load_stays_bottom() {
        let func = raw_func(vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Load {
                    dst: make_reg(8, 8),
                    space: SpaceId::Ram,
                    addr: make_reg(0, 8),
                },
                R2ILOp::Return {
                    target: make_ram(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }]);

        let (consts, _) = sccp(&func);
        assert!(
            !consts.keys().any(|k| k.name == "reg:8"),
            "loads are conservative Bottom in SCCP"
        );
    }

    #[test]
    fn sccp_noop_on_no_consts() {
        let func = raw_func(vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: make_reg(8, 8),
                    a: make_reg(0, 8),
                    b: make_reg(16, 8),
                },
                R2ILOp::Return {
                    target: make_ram(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }]);

        let (consts, _) = sccp(&func);
        assert!(consts.is_empty(), "no constants should be discovered");
    }

    #[test]
    fn sccp_apply_prunes_edges_and_blocks() {
        let mut func = raw_func(vec![
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
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
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
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ]);

        let (consts, executable) = sccp(&func);
        let mut stats = OptimizationStats::default();
        let changed = apply_sccp_results(&mut func, &consts, &executable, None, &mut stats);
        assert!(changed);
        assert!(
            func.get_block(0x1004).is_none(),
            "dead branch block should be removed"
        );
        assert!(!func.cfg().has_edge(0x1000, 0x1004));
        assert!(stats.sccp_edges_pruned > 0);
        assert!(stats.sccp_blocks_removed > 0);
    }
}
