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
    pub enable_const_prop: bool,
    pub enable_inst_combine: bool,
    pub enable_copy_prop: bool,
    pub enable_cse: bool,
    pub enable_dce: bool,
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
    pub enable_cse: bool,
}

impl Default for OptimizationConfig {
    fn default() -> Self {
        Self {
            max_iterations: 4,
            enable_sccp: true,
            enable_const_prop: true,
            enable_inst_combine: true,
            enable_copy_prop: true,
            enable_cse: true,
            enable_dce: true,
            preserve_memory_reads: false,
        }
    }
}

impl Default for DecompilePrepConfig {
    fn default() -> Self {
        Self {
            max_iterations: 1,
            enable_inst_combine: true,
            enable_cse: false,
        }
    }
}

impl From<&DecompilePrepConfig> for OptimizationConfig {
    fn from(value: &DecompilePrepConfig) -> Self {
        Self {
            max_iterations: value.max_iterations.max(1),
            enable_sccp: false,
            enable_const_prop: false,
            enable_inst_combine: value.enable_inst_combine,
            enable_copy_prop: false,
            enable_cse: value.enable_cse,
            enable_dce: false,
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
    pub copies_propagated: usize,
    pub phis_simplified: usize,
    pub cse_replacements: usize,
    pub dce_removed_ops: usize,
    pub dce_removed_phis: usize,
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

        if config.enable_const_prop && !config.enable_sccp {
            let consts = compute_constants_with_control(func, max_iters, control)?;
            control.poll()?;
            if replace_sources_with_constants(func, &consts, function_interface, &mut stats) {
                changed = true;
            }
        }

        if config.enable_inst_combine && inst_combine(func, &mut stats) {
            changed = true;
        }

        control.poll()?;
        if config.enable_cse && common_subexpr_elim(func, &mut stats) {
            changed = true;
        }

        control.poll()?;
        if config.enable_copy_prop && copy_propagation(func, function_interface, &mut stats) {
            changed = true;
        }

        control.poll()?;
        if config.enable_dce && dead_code_elim(func, config, function_interface, &mut stats) {
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

fn compute_constants_with_control<C: SsaWorkControl + ?Sized>(
    func: &SSAFunction,
    max_iters: usize,
    control: &C,
) -> Result<HashMap<VarKey, u64>, SsaExecutionStopReason> {
    let mut consts = HashMap::new();

    for _ in 0..max_iters {
        control.poll()?;
        let mut changed = false;

        for phi in func.all_phis() {
            control.poll()?;
            let dst_key = VarKey::from_var(&phi.dst);
            if consts.contains_key(&dst_key) {
                continue;
            }
            let mut iter = phi.sources.iter();
            let Some((_, first)) = iter.next() else {
                continue;
            };
            let Some(first_val) = const_for_var(first, &consts) else {
                continue;
            };
            if iter.all(|(_, src)| const_for_var(src, &consts) == Some(first_val)) {
                consts.insert(dst_key, first_val);
                changed = true;
            }
        }

        for op in func.all_ops() {
            control.poll()?;
            let Some(dst) = op.dst() else { continue };
            let dst_key = VarKey::from_var(dst);
            if consts.contains_key(&dst_key) {
                continue;
            }
            if let Some(val) = eval_const_op(op, &consts) {
                consts.insert(dst_key, val);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    control.poll()?;
    Ok(consts)
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

fn copy_propagation(
    func: &mut SSAFunction,
    function_interface: Option<&SourceFunctionInterface>,
    stats: &mut OptimizationStats,
) -> bool {
    let (replacements, changed) = build_copy_replacements(func, stats);
    let applied = if replacements.is_empty() {
        false
    } else {
        apply_replacements(func, &replacements, function_interface, stats)
    };
    changed || applied
}

fn build_copy_replacements(
    func: &mut SSAFunction,
    stats: &mut OptimizationStats,
) -> (HashMap<VarKey, SSAVar>, bool) {
    let mut replacements = HashMap::new();
    let mut changed = false;
    let block_addrs = func.block_addrs().to_vec();

    for addr in block_addrs {
        let Some(block) = func.get_block_mut(addr) else {
            continue;
        };

        block.phis.retain(|phi| {
            let mut iter = phi.sources.iter();
            let Some((_, first)) = iter.next() else {
                return true;
            };
            if iter.all(|(_, src)| src == first) {
                let dst_key = VarKey::from_var(&phi.dst);
                if phi.dst != *first {
                    replacements.insert(dst_key, first.clone());
                }
                stats.phis_simplified += 1;
                changed = true;
                false
            } else {
                true
            }
        });

        for op in &block.ops {
            if let SSAOp::Copy { dst, src } = op
                && dst.size == src.size
                && dst != src
            {
                replacements.insert(VarKey::from_var(dst), src.clone());
            }
        }
    }

    (resolve_replacements(replacements), changed)
}

fn resolve_replacements(mut replacements: HashMap<VarKey, SSAVar>) -> HashMap<VarKey, SSAVar> {
    let keys: Vec<VarKey> = replacements.keys().cloned().collect();
    for key in keys {
        let mut visited = HashSet::new();
        let mut current_key = key.clone();
        let mut current_var = replacements.get(&current_key).cloned();
        while let Some(next) = current_var {
            let next_key = VarKey::from_var(&next);
            if !visited.insert(next_key.clone()) {
                break;
            }
            if let Some(follow) = replacements.get(&next_key).cloned() {
                current_var = Some(follow);
                current_key = next_key;
            } else {
                replacements.insert(key.clone(), next);
                break;
            }
        }
    }
    replacements
}

fn apply_replacements(
    func: &mut SSAFunction,
    replacements: &HashMap<VarKey, SSAVar>,
    function_interface: Option<&SourceFunctionInterface>,
    stats: &mut OptimizationStats,
) -> bool {
    let mut changed = false;
    let block_addrs = func.block_addrs().to_vec();
    let return_storage =
        coherent_return_projection(function_interface).map(|projection| projection.carrier);

    let mapper = |var: &SSAVar| -> SSAVar {
        let mut visited = HashSet::new();
        let mut current = var.clone();
        let mut key = VarKey::from_var(&current);
        while let Some(next) = replacements.get(&key).cloned() {
            if !visited.insert(key) {
                return var.clone();
            }
            current = next;
            key = VarKey::from_var(&current);
        }
        current
    };

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
                let new_src = if preserve_phi_sources {
                    src.clone()
                } else {
                    mapper(src)
                };
                if new_src != *src {
                    *src = new_src;
                    stats.copies_propagated += 1;
                    changed = true;
                }
            }
        }

        for op in &mut block.ops {
            let new_op = map_sources_in_op(op, &mapper);
            if &new_op != op {
                let delta = count_source_replacements(op, &new_op);
                if delta > 0 {
                    stats.copies_propagated += delta;
                }
                *op = new_op;
                changed = true;
            }
        }
    }

    changed
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ExprKind {
    Unary(&'static str),
    Binary(&'static str),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ExprKey {
    kind: ExprKind,
    dst_size: u32,
    args: Vec<VarKey>,
}

fn expr_key(op: &SSAOp) -> Option<ExprKey> {
    use SSAOp::*;
    let dst = op.dst()?;
    let key = match op {
        IntNegate { src, .. } => ExprKey {
            kind: ExprKind::Unary("IntNegate"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        IntNot { src, .. } => ExprKey {
            kind: ExprKind::Unary("IntNot"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        BoolNot { src, .. } => ExprKey {
            kind: ExprKind::Unary("BoolNot"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        IntZExt { src, .. } => ExprKey {
            kind: ExprKind::Unary("IntZExt"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        IntSExt { src, .. } => ExprKey {
            kind: ExprKind::Unary("IntSExt"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        Trunc { src, .. } => ExprKey {
            kind: ExprKind::Unary("Trunc"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        FloatNeg { src, .. } => ExprKey {
            kind: ExprKind::Unary("FloatNeg"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        FloatAbs { src, .. } => ExprKey {
            kind: ExprKind::Unary("FloatAbs"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        FloatSqrt { src, .. } => ExprKey {
            kind: ExprKind::Unary("FloatSqrt"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        Int2Float { src, .. } => ExprKey {
            kind: ExprKind::Unary("Int2Float"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        Float2Int { src, .. } => ExprKey {
            kind: ExprKind::Unary("Float2Int"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        FloatFloat { src, .. } => ExprKey {
            kind: ExprKind::Unary("FloatFloat"),
            dst_size: dst.size,
            args: vec![VarKey::from_var(src)],
        },
        IntAdd { a, b, .. }
        | IntMult { a, b, .. }
        | IntAnd { a, b, .. }
        | IntOr { a, b, .. }
        | IntXor { a, b, .. }
        | IntEqual { a, b, .. }
        | IntNotEqual { a, b, .. }
        | BoolAnd { a, b, .. }
        | BoolOr { a, b, .. }
        | BoolXor { a, b, .. }
        | FloatAdd { a, b, .. }
        | FloatMult { a, b, .. }
        | FloatEqual { a, b, .. }
        | FloatNotEqual { a, b, .. } => {
            let mut args = vec![VarKey::from_var(a), VarKey::from_var(b)];
            args.sort();
            let kind = match op {
                IntAdd { .. } => ExprKind::Binary("IntAdd"),
                IntMult { .. } => ExprKind::Binary("IntMult"),
                IntAnd { .. } => ExprKind::Binary("IntAnd"),
                IntOr { .. } => ExprKind::Binary("IntOr"),
                IntXor { .. } => ExprKind::Binary("IntXor"),
                IntEqual { .. } => ExprKind::Binary("IntEqual"),
                IntNotEqual { .. } => ExprKind::Binary("IntNotEqual"),
                BoolAnd { .. } => ExprKind::Binary("BoolAnd"),
                BoolOr { .. } => ExprKind::Binary("BoolOr"),
                BoolXor { .. } => ExprKind::Binary("BoolXor"),
                FloatAdd { .. } => ExprKind::Binary("FloatAdd"),
                FloatMult { .. } => ExprKind::Binary("FloatMult"),
                FloatEqual { .. } => ExprKind::Binary("FloatEqual"),
                FloatNotEqual { .. } => ExprKind::Binary("FloatNotEqual"),
                _ => return None,
            };
            ExprKey {
                kind,
                dst_size: dst.size,
                args,
            }
        }
        IntSub { a, b, .. }
        | IntDiv { a, b, .. }
        | IntSDiv { a, b, .. }
        | IntRem { a, b, .. }
        | IntSRem { a, b, .. }
        | IntLeft { a, b, .. }
        | IntRight { a, b, .. }
        | IntSRight { a, b, .. }
        | IntLess { a, b, .. }
        | IntLessEqual { a, b, .. }
        | IntSLess { a, b, .. }
        | IntSLessEqual { a, b, .. }
        | FloatSub { a, b, .. }
        | FloatDiv { a, b, .. }
        | FloatLess { a, b, .. }
        | FloatLessEqual { a, b, .. } => {
            let args = vec![VarKey::from_var(a), VarKey::from_var(b)];
            let kind = match op {
                IntSub { .. } => ExprKind::Binary("IntSub"),
                IntDiv { .. } => ExprKind::Binary("IntDiv"),
                IntSDiv { .. } => ExprKind::Binary("IntSDiv"),
                IntRem { .. } => ExprKind::Binary("IntRem"),
                IntSRem { .. } => ExprKind::Binary("IntSRem"),
                IntLeft { .. } => ExprKind::Binary("IntLeft"),
                IntRight { .. } => ExprKind::Binary("IntRight"),
                IntSRight { .. } => ExprKind::Binary("IntSRight"),
                IntLess { .. } => ExprKind::Binary("IntLess"),
                IntLessEqual { .. } => ExprKind::Binary("IntLessEqual"),
                IntSLess { .. } => ExprKind::Binary("IntSLess"),
                IntSLessEqual { .. } => ExprKind::Binary("IntSLessEqual"),
                FloatSub { .. } => ExprKind::Binary("FloatSub"),
                FloatDiv { .. } => ExprKind::Binary("FloatDiv"),
                FloatLess { .. } => ExprKind::Binary("FloatLess"),
                FloatLessEqual { .. } => ExprKind::Binary("FloatLessEqual"),
                _ => return None,
            };
            ExprKey {
                kind,
                dst_size: dst.size,
                args,
            }
        }
        _ => return None,
    };

    Some(key)
}

fn common_subexpr_elim(func: &mut SSAFunction, stats: &mut OptimizationStats) -> bool {
    let mut changed = false;
    let block_addrs = func.block_addrs().to_vec();

    for addr in block_addrs {
        let Some(block) = func.get_block_mut(addr) else {
            continue;
        };
        let mut available: HashMap<ExprKey, SSAVar> = HashMap::new();

        for op in &mut block.ops {
            let Some(dst) = op.dst().cloned() else {
                continue;
            };
            let Some(key) = expr_key(op) else { continue };

            if let Some(existing) = available.get(&key).cloned() {
                if existing.size == dst.size {
                    *op = SSAOp::Copy { dst, src: existing };
                    stats.cse_replacements += 1;
                    changed = true;
                }
            } else {
                available.insert(key, dst);
            }
        }
    }

    changed
}

fn dead_code_elim(
    func: &mut SSAFunction,
    config: &OptimizationConfig,
    function_interface: Option<&SourceFunctionInterface>,
    stats: &mut OptimizationStats,
) -> bool {
    let mut changed = false;

    loop {
        let use_set = collect_uses(func, function_interface);
        let mut local_change = false;
        let block_addrs = func.block_addrs().to_vec();

        for addr in block_addrs {
            let Some(block) = func.get_block_mut(addr) else {
                continue;
            };

            let before_ops = block.ops.len();
            block.ops.retain(|op| {
                if let Some(dst) = op.dst() {
                    let key = VarKey::from_var(dst);
                    if !use_set.contains(&key)
                        && !op.has_observable_effects(config.preserve_memory_reads)
                    {
                        stats.dce_removed_ops += 1;
                        return false;
                    }
                }
                true
            });

            let before_phis = block.phis.len();
            block.phis.retain(|phi| {
                let key = VarKey::from_var(&phi.dst);
                if !use_set.contains(&key) {
                    stats.dce_removed_phis += 1;
                    return false;
                }
                true
            });

            if block.ops.len() != before_ops || block.phis.len() != before_phis {
                local_change = true;
            }
        }

        if !local_change {
            break;
        }
        changed = true;
    }

    changed
}

#[cfg(test)]
fn canonical_register_storages_overlap(
    left: CanonicalStorageId,
    right: CanonicalStorageId,
) -> bool {
    if left.space != CanonicalStorageSpace::Register
        || right.space != CanonicalStorageSpace::Register
    {
        return false;
    }
    let Some(left_end) = left.offset.checked_add(u64::from(left.size)) else {
        return false;
    };
    let Some(right_end) = right.offset.checked_add(u64::from(right.size)) else {
        return false;
    };
    left.offset < right_end && right.offset < left_end
}

fn canonical_register_storage_is_contained(
    container: CanonicalStorageId,
    contained: CanonicalStorageId,
) -> bool {
    if container.space != CanonicalStorageSpace::Register
        || contained.space != CanonicalStorageSpace::Register
        || container.size == 0
        || contained.size == 0
        || contained.offset < container.offset
    {
        return false;
    }
    let Some(container_end) = container.offset.checked_add(u64::from(container.size)) else {
        return false;
    };
    let Some(contained_end) = contained.offset.checked_add(u64::from(contained.size)) else {
        return false;
    };
    contained_end <= container_end
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

fn cover_uncovered_register_bytes(
    uncovered: &mut Vec<(u64, u64)>,
    storage: CanonicalStorageId,
) -> bool {
    let Some(storage_end) = storage.offset.checked_add(u64::from(storage.size)) else {
        return false;
    };
    let mut covered = false;
    let mut remaining = Vec::with_capacity(uncovered.len().saturating_add(1));
    for &(start, end) in uncovered.iter() {
        if storage_end <= start || storage.offset >= end {
            remaining.push((start, end));
            continue;
        }
        covered = true;
        if start < storage.offset {
            remaining.push((start, storage.offset));
        }
        if storage_end < end {
            remaining.push((storage_end, end));
        }
    }
    *uncovered = remaining;
    covered
}

fn register_storage_overlaps_ranges(storage: CanonicalStorageId, ranges: &[(u64, u64)]) -> bool {
    if storage.space != CanonicalStorageSpace::Register {
        return false;
    }
    let Some(storage_end) = storage.offset.checked_add(u64::from(storage.size)) else {
        return false;
    };
    ranges
        .iter()
        .any(|&(start, end)| storage.offset < end && start < storage_end)
}

fn merge_register_ranges(ranges: &mut Vec<(u64, u64)>, incoming: &[(u64, u64)]) -> bool {
    let previous = ranges.clone();
    ranges.extend_from_slice(incoming);
    ranges.sort_unstable();
    let mut merged = Vec::with_capacity(ranges.len());
    for &(start, end) in ranges.iter() {
        if let Some((_, previous_end)) = merged.last_mut()
            && start <= *previous_end
        {
            *previous_end = (*previous_end).max(end);
        } else {
            merged.push((start, end));
        }
    }
    *ranges = merged;
    *ranges != previous
}

struct TerminalStorageLiveness {
    uncovered_register_ranges: Vec<(u64, u64)>,
    preserved_definitions: HashSet<VarKey>,
}

fn transfer_terminal_storage_liveness(
    func: &SSAFunction,
    block_addr: u64,
    projection: TerminalStorageProjection,
    live_out: &[(u64, u64)],
) -> Option<TerminalStorageLiveness> {
    let block = func.get_block(block_addr)?;
    let mut uncovered = live_out.to_vec();
    let mut preserved = HashSet::new();
    for op in block.ops.iter().rev() {
        if uncovered.is_empty() {
            break;
        }
        let Some(dst) = op.dst() else {
            continue;
        };
        let Some(storage) = func.canonical_storage_for_var(dst) else {
            continue;
        };
        if !register_storage_overlaps_ranges(storage, &uncovered) {
            continue;
        }
        if !canonical_register_storage_is_contained(projection.carrier, storage) {
            return None;
        }
        if cover_uncovered_register_bytes(&mut uncovered, storage) {
            preserved.insert(VarKey::from_var(dst));
        }
    }

    for phi in block.phis.iter().rev() {
        if uncovered.is_empty() {
            break;
        }
        let Some(storage) = phi.canonical_storage else {
            continue;
        };
        if !register_storage_overlaps_ranges(storage, &uncovered) {
            continue;
        }
        if !canonical_register_storage_is_contained(projection.carrier, storage) {
            return None;
        }
        if cover_uncovered_register_bytes(&mut uncovered, storage) {
            preserved.insert(VarKey::from_var(&phi.dst));
            for (_, source) in &phi.sources {
                preserved.insert(VarKey::from_var(source));
            }
        }
    }
    Some(TerminalStorageLiveness {
        uncovered_register_ranges: uncovered,
        preserved_definitions: preserved,
    })
}

fn collect_preserved_projection_defs(
    func: &SSAFunction,
    projection: TerminalStorageProjection,
) -> HashSet<VarKey> {
    let mut preserved = HashSet::new();
    let Some(logical_end) = projection
        .logical
        .offset
        .checked_add(u64::from(projection.logical.size))
    else {
        return preserved;
    };
    let seed = [(projection.logical.offset, logical_end)];
    let mut live_out_by_block = HashMap::<u64, Vec<(u64, u64)>>::new();
    let mut pending = VecDeque::new();
    for block in func.blocks() {
        let Some(cfg_block) = func.cfg().get_block(block.addr) else {
            continue;
        };
        if cfg_block.is_return()
            && merge_register_ranges(live_out_by_block.entry(block.addr).or_default(), &seed)
        {
            pending.push_back(block.addr);
        }
    }

    while let Some(block_addr) = pending.pop_front() {
        let Some(live_out) = live_out_by_block.get(&block_addr) else {
            continue;
        };
        let Some(liveness) =
            transfer_terminal_storage_liveness(func, block_addr, projection, live_out)
        else {
            continue;
        };
        let live_in = liveness.uncovered_register_ranges;
        if live_in.is_empty() {
            continue;
        }
        for predecessor in func.predecessors(block_addr) {
            if merge_register_ranges(live_out_by_block.entry(predecessor).or_default(), &live_in) {
                pending.push_back(predecessor);
            }
        }
    }

    for (block_addr, live_out) in live_out_by_block {
        if let Some(liveness) =
            transfer_terminal_storage_liveness(func, block_addr, projection, &live_out)
        {
            preserved.extend(liveness.preserved_definitions);
        }
    }
    preserved
}

fn collect_preserved_return_defs_in_terminal_blocks(
    func: &SSAFunction,
    projection: TerminalStorageProjection,
) -> HashSet<VarKey> {
    let mut preserved = HashSet::new();
    let Some(logical_end) = projection
        .logical
        .offset
        .checked_add(u64::from(projection.logical.size))
    else {
        return preserved;
    };
    let seed = [(projection.logical.offset, logical_end)];
    for block in func.blocks() {
        let Some(cfg_block) = func.cfg().get_block(block.addr) else {
            continue;
        };
        if !cfg_block.is_return() {
            continue;
        }
        let Some(liveness) =
            transfer_terminal_storage_liveness(func, block.addr, projection, &seed)
        else {
            continue;
        };
        if liveness.uncovered_register_ranges.is_empty() {
            preserved.extend(liveness.preserved_definitions);
        }
    }
    preserved
}

fn collect_preserved_terminal_defs(
    func: &SSAFunction,
    function_interface: Option<&SourceFunctionInterface>,
) -> HashSet<VarKey> {
    let mut preserved = HashSet::new();
    if let Some(projection) = coherent_return_projection(function_interface) {
        preserved.extend(collect_preserved_return_defs_in_terminal_blocks(
            func, projection,
        ));
    }
    if let Some(storage) =
        function_interface.and_then(SourceFunctionInterface::exact_frame_pointer_storage)
    {
        preserved.extend(collect_preserved_projection_defs(
            func,
            TerminalStorageProjection {
                carrier: storage,
                logical: storage,
            },
        ));
    }

    preserved
}

fn collect_uses(
    func: &SSAFunction,
    function_interface: Option<&SourceFunctionInterface>,
) -> HashSet<VarKey> {
    let mut uses = HashSet::new();

    for phi in func.all_phis() {
        for (_, src) in &phi.sources {
            uses.insert(VarKey::from_var(src));
        }
    }

    for op in func.all_ops() {
        for src in op.sources() {
            uses.insert(VarKey::from_var(src));
        }
    }

    uses.extend(collect_preserved_terminal_defs(func, function_interface));

    uses
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
    use crate::{
        CanonicalStorageId, CanonicalStorageSpace, InstPayload, SourceCarrierProjection,
        SourceLogicalValue, SourceStackSlotSpec, SourceType, SourceTypeGraph, SsaGraph,
        StackAddressBase,
    };
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

    fn raw_func(blocks: Vec<R2ILBlock>) -> SSAFunction {
        SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA function should build")
    }

    fn register_storage(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    fn exact_u32_return_interface(storage: CanonicalStorageId) -> SourceFunctionInterface {
        let graph = SourceTypeGraph::new(
            [SourceType::new(0, SourceTypeKind::UnsignedInteger, 32, 32)],
            [],
        )
        .expect("u32 type graph");
        SourceFunctionInterface::new_exact_with_logical_types(
            b"return-liveness-test-v1".to_vec(),
            "test-cc",
            [],
            SourceFunctionReturn::Register { storage },
            [],
            [],
            Some(SourceLogicalValue::new(
                0,
                SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32),
            )),
            Some(graph),
        )
        .expect("exact logical return interface")
    }

    fn exact_frame_pointer_interface(storage: CanonicalStorageId) -> SourceFunctionInterface {
        SourceFunctionInterface::new_exact(
            b"frame-liveness-test-v1".to_vec(),
            "test-cc",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                storage,
                -16,
                8,
            )],
        )
        .expect("exact frame-pointer interface")
        .with_return_address_storage(register_storage(0x80, 8))
        .expect("return-address storage")
        .with_stack_pointer_storage(register_storage(0x40, 8))
        .expect("stack-pointer storage")
    }

    fn inexact_frame_pointer_interface(storage: CanonicalStorageId) -> SourceFunctionInterface {
        SourceFunctionInterface::new(
            b"frame-liveness-test-v1".to_vec(),
            "test-cc",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new(
                StackAddressBase::FramePointer,
                storage,
                -16,
                8,
            )],
        )
        .expect("advisory frame-pointer interface")
    }

    fn exact_stack_pointer_only_interface(storage: CanonicalStorageId) -> SourceFunctionInterface {
        SourceFunctionInterface::new_exact(
            b"frame-liveness-test-v1".to_vec(),
            "test-cc",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::StackPointer,
                storage,
                0,
                8,
            )],
        )
        .expect("exact stack-pointer-only interface")
    }

    fn frame_pop_function(frame_name: &str, frame_offset: u64) -> SSAFunction {
        let mut arch = ArchSpec::new("frame-pop-test");
        arch.add_register(RegisterDef::new(frame_name, frame_offset, 8));
        arch.add_register(RegisterDef::new("stack_base", 0x40, 8));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Load {
            dst: make_unique(0x100, 8),
            space: SpaceId::Ram,
            addr: make_reg(0x40, 8),
        });
        block.push(R2ILOp::Copy {
            dst: make_reg(frame_offset, 8),
            src: make_unique(0x100, 8),
        });
        // A non-register destination may share the FP's numeric offset. It
        // must not terminate register-storage liveness.
        block.push(R2ILOp::Copy {
            dst: make_unique(frame_offset, 8),
            src: make_const(0x55, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: make_reg(0x40, 8),
            a: make_reg(0x40, 8),
            b: make_const(16, 8),
        });
        block.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("frame pop SSA")
    }

    fn predecessor_frame_restore_function(
        frame_offset: u64,
        split_after_restore: bool,
    ) -> SSAFunction {
        let mut arch = ArchSpec::new("predecessor-frame-restore-test");
        arch.add_register(RegisterDef::new("frame_carrier", frame_offset, 8));
        arch.add_register(RegisterDef::new("condition", 0x20, 1));
        arch.add_register(RegisterDef::new("stack_base", 0x40, 8));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut restore = R2ILBlock::new(0x1000, 4);
        restore.push(R2ILOp::Load {
            dst: make_unique(0x100, 8),
            space: SpaceId::Ram,
            addr: make_reg(0x40, 8),
        });
        restore.push(R2ILOp::Copy {
            dst: make_reg(frame_offset, 8),
            src: make_unique(0x100, 8),
        });
        if split_after_restore {
            restore.push(R2ILOp::CBranch {
                target: make_const(0x1008, 8),
                cond: make_reg(0x20, 1),
            });
        } else {
            restore.push(R2ILOp::Branch {
                target: make_const(0x1004, 8),
            });
        }
        let mut first_return = R2ILBlock::new(0x1004, 4);
        first_return.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        let mut blocks = vec![restore, first_return];
        if split_after_restore {
            let mut second_return = R2ILBlock::new(0x1008, 4);
            second_return.push(R2ILOp::Return {
                target: make_reg(0x80, 8),
            });
            blocks.push(second_return);
        }
        SSAFunction::from_blocks_raw(&blocks, Some(&arch)).expect("predecessor frame restore SSA")
    }

    fn frame_restore_chain_is_present(function: &SSAFunction, storage: CanonicalStorageId) -> bool {
        let Some(block) = function.get_block(0x1000) else {
            return false;
        };
        let load_dst = block.ops.iter().find_map(|op| match op {
            SSAOp::Load { dst, .. } => Some(dst),
            _ => None,
        });
        block.ops.iter().any(|op| match op {
            SSAOp::Copy { dst, src } => {
                function.canonical_storage_for_var(dst) == Some(storage) && load_dst == Some(src)
            }
            _ => false,
        })
    }

    fn return_alias_function(whole_name: &str, low_name: &str) -> SSAFunction {
        let mut arch = ArchSpec::new("return-alias-test");
        arch.add_register(RegisterDef::new(whole_name, 0, 8));
        arch.add_register(RegisterDef::sub(low_name, 0, 1, whole_name));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: make_reg(0, 8),
            src: make_const(0, 8),
        });
        block.push(R2ILOp::Copy {
            dst: make_reg(0, 1),
            src: make_const(1, 1),
        });
        block.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("return alias SSA")
    }

    fn narrow_return_function(whole_name: &str, low_name: &str) -> SSAFunction {
        let mut arch = ArchSpec::new("narrow-return-test");
        arch.add_register(RegisterDef::new(whole_name, 0, 8));
        arch.add_register(RegisterDef::sub(low_name, 0, 4, whole_name));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: make_reg(0, 4),
            src: make_const(7, 4),
        });
        block.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("narrow return SSA")
    }

    fn return_phi_overlay_function(whole_name: &str, low_name: &str) -> SSAFunction {
        let mut arch = ArchSpec::new("return-phi-overlay-test");
        arch.add_register(RegisterDef::new(whole_name, 0, 8));
        arch.add_register(RegisterDef::sub(low_name, 0, 1, whole_name));
        arch.add_register(RegisterDef::new("cond", 0x40, 1));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: make_const(0x1008, 8),
            cond: make_reg(0x40, 1),
        });
        let mut left = R2ILBlock::new(0x1004, 4);
        left.push(R2ILOp::Copy {
            dst: make_reg(0, 8),
            src: make_const(1, 8),
        });
        left.push(R2ILOp::Branch {
            target: make_const(0x100c, 8),
        });
        let mut right = R2ILBlock::new(0x1008, 4);
        right.push(R2ILOp::Copy {
            dst: make_reg(0, 8),
            src: make_const(2, 8),
        });
        right.push(R2ILOp::Branch {
            target: make_const(0x100c, 8),
        });
        let mut merge = R2ILBlock::new(0x100c, 4);
        merge.push(R2ILOp::Copy {
            dst: make_reg(0, 1),
            src: make_const(3, 1),
        });
        merge.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[entry, left, right, merge], Some(&arch))
            .expect("return phi overlay SSA")
    }

    fn shadowed_overlay_function(whole_name: &str, low_name: &str) -> SSAFunction {
        let mut arch = ArchSpec::new("shadowed-return-overlay-test");
        arch.add_register(RegisterDef::new(whole_name, 0, 8));
        arch.add_register(RegisterDef::sub(low_name, 0, 1, whole_name));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: make_reg(0, 8),
            src: make_const(0, 8),
        });
        block.push(R2ILOp::Copy {
            dst: make_reg(0, 1),
            src: make_const(1, 1),
        });
        block.push(R2ILOp::Copy {
            dst: make_reg(0, 1),
            src: make_const(2, 1),
        });
        block.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("shadowed return overlay SSA")
    }

    fn optimize_with_interface(
        function: &mut SSAFunction,
        interface: &SourceFunctionInterface,
    ) -> OptimizationStats {
        optimize_function_with_interface_and_control(
            function,
            &OptimizationConfig::default(),
            Some(interface),
            &UncheckedSsaWorkControl,
        )
        .expect("unchecked typed optimization")
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

    #[test]
    fn dce_without_interface_does_not_guess_return_phi_from_name() {
        let mut func = raw_func(vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1008, 8),
                    cond: make_reg(32, 1),
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
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x100c, 8),
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
        ]);

        func.get_block_mut(0x1000).expect("entry block").ops = vec![SSAOp::CBranch {
            target: SSAVar::new("ram:1008", 0, 8),
            cond: SSAVar::new("tmp:cond", 0, 1),
        }];
        func.get_block_mut(0x1004).expect("left block").ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("rax", 1, 8),
                src: SSAVar::constant(1, 8),
            },
            SSAOp::Branch {
                target: SSAVar::new("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x1008).expect("right block").ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("rax", 2, 8),
                src: SSAVar::constant(0, 8),
            },
            SSAOp::Branch {
                target: SSAVar::new("ram:100c", 0, 8),
            },
        ];
        func.get_block_mut(0x100c).expect("merge block").phis = vec![PhiNode {
            dst: SSAVar::new("rax", 3, 8),
            sources: vec![
                (0x1004, SSAVar::new("rax", 1, 8)),
                (0x1008, SSAVar::new("rax", 2, 8)),
            ],
            canonical_storage: None,
        }];

        let stats = optimize_function(&mut func, &OptimizationConfig::default());
        let merge = func.get_block(0x100c).expect("merge block");
        assert!(
            merge.phis.is_empty(),
            "a detached textual register name must not preserve a phi"
        );
        assert!(
            !func.get_block(0x1004).expect("left block").ops.iter().any(
                |op| matches!(op, SSAOp::Copy { dst, .. } if dst == &SSAVar::new("rax", 1, 8))
            ),
            "left name-only write must be removed"
        );
        assert!(
            !func.get_block(0x1008).expect("right block").ops.iter().any(
                |op| matches!(op, SSAOp::Copy { dst, .. } if dst == &SSAVar::new("rax", 2, 8))
            ),
            "right name-only write must be removed"
        );
        assert!(
            stats.dce_removed_phis > 0,
            "the detached name-only phi must be accounted as dead"
        );
    }

    #[test]
    fn phi_storage_identity_survives_removing_preceding_phi() {
        let mut func = raw_func(vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1008, 8),
                    cond: make_reg(32, 1),
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
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(8, 8),
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
                        src: make_const(0, 8),
                    },
                    R2ILOp::Copy {
                        dst: make_reg(8, 8),
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
        let retained_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 8,
            size: 8,
        };
        let merge = func.get_block_mut(0x100c).expect("merge block");
        assert_eq!(merge.phis.len(), 2, "both lifted registers require phis");
        let removed_phi = merge
            .phis
            .iter_mut()
            .find(|phi| {
                phi.canonical_storage
                    .is_some_and(|storage| storage.offset == 0)
            })
            .expect("first register phi");
        let shared_source = removed_phi.sources[0].1.clone();
        for (_, source) in &mut removed_phi.sources {
            *source = shared_source.clone();
        }
        let retained_dst = merge
            .phis
            .iter()
            .find(|phi| phi.canonical_storage == Some(retained_storage))
            .expect("second register phi")
            .dst
            .clone();
        merge.ops = vec![SSAOp::Return {
            target: retained_dst.clone(),
        }];

        let config = OptimizationConfig {
            max_iterations: 1,
            enable_sccp: false,
            enable_const_prop: false,
            enable_inst_combine: false,
            enable_copy_prop: true,
            enable_cse: false,
            enable_dce: false,
            preserve_memory_reads: false,
        };
        let stats = optimize_function(&mut func, &config);

        assert_eq!(stats.phis_simplified, 1);
        let merge = func.get_block(0x100c).expect("merge block");
        assert_eq!(merge.phis.len(), 1);
        assert_eq!(merge.phis[0].dst, retained_dst);
        assert_eq!(merge.phis[0].canonical_storage, Some(retained_storage));

        let graph = SsaGraph::from_function(&func);
        let graph_phi = graph
            .insts
            .iter()
            .find(|inst| matches!(inst.payload, InstPayload::Phi { .. }))
            .expect("retained graph phi");
        assert_eq!(graph_phi.canonical_storage, Some(retained_storage));
    }

    #[test]
    fn dce_without_interface_does_not_guess_direct_return_from_name() {
        let mut func = raw_func(vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }]);

        func.get_block_mut(0x1000).expect("entry block").ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("eax", 1, 4),
                src: SSAVar::constant(1, 4),
            },
            SSAOp::Return {
                target: SSAVar::new("ram:0", 0, 8),
            },
        ];

        optimize_function(&mut func, &OptimizationConfig::default());
        assert!(
            !func.get_block(0x1000).expect("entry block").ops.iter().any(
                |op| matches!(op, SSAOp::Copy { dst, .. } if dst == &SSAVar::new("eax", 1, 4))
            ),
            "a return-like textual name has no authority without an exact interface"
        );
    }

    #[test]
    fn typed_dce_retains_exact_frame_pointer_pop_chain() {
        let frame_storage = register_storage(0, 8);
        let mut func = frame_pop_function("callee_frame_carrier", 0);
        let interface = exact_frame_pointer_interface(frame_storage);

        optimize_with_interface(&mut func, &interface);

        assert!(
            frame_restore_chain_is_present(&func, frame_storage),
            "the exact full-width frame restore and its feeding load must remain"
        );
    }

    #[test]
    fn frame_pointer_liveness_requires_exact_frame_slot_authority() {
        let frame_storage = register_storage(0, 8);
        let mut absent = frame_pop_function("frame_like", 0);
        let mut inexact = absent.clone();
        let mut stack_only = absent.clone();

        optimize_function(&mut absent, &OptimizationConfig::default());
        optimize_with_interface(
            &mut inexact,
            &inexact_frame_pointer_interface(frame_storage),
        );
        optimize_with_interface(
            &mut stack_only,
            &exact_stack_pointer_only_interface(frame_storage),
        );

        for function in [&absent, &inexact, &stack_only] {
            assert!(
                !frame_restore_chain_is_present(function, frame_storage),
                "no interface, advisory roles, and SP-only slots must not preserve FP evidence"
            );
        }
    }

    #[test]
    fn typed_frame_pointer_liveness_uses_canonical_storage_not_name() {
        let frame_storage = register_storage(0, 8);
        let interface = exact_frame_pointer_interface(frame_storage);
        let mut first = frame_pop_function("ordinary_saved_base", 0);
        let mut renamed = frame_pop_function("unrelated_display_name", 0);

        optimize_with_interface(&mut first, &interface);
        optimize_with_interface(&mut renamed, &interface);

        assert!(frame_restore_chain_is_present(&first, frame_storage));
        assert!(frame_restore_chain_is_present(&renamed, frame_storage));
        assert_eq!(
            first.get_block(0x1000).expect("return block").ops.len(),
            renamed.get_block(0x1000).expect("return block").ops.len()
        );
    }

    #[test]
    fn typed_frame_pointer_liveness_does_not_preserve_wrong_storage() {
        let exact_storage = register_storage(0, 8);
        let wrong_storage = register_storage(0x20, 8);
        let interface = exact_frame_pointer_interface(exact_storage);
        let mut func = frame_pop_function("frame_pointer", wrong_storage.offset);

        optimize_with_interface(&mut func, &interface);

        assert!(
            !frame_restore_chain_is_present(&func, wrong_storage),
            "a frame-pointer-like name at the wrong storage has no liveness authority"
        );
        let block = func.get_block(0x1000).expect("return block");
        assert!(!block.ops.iter().any(|op| {
            op.dst()
                .is_some_and(|dst| func.canonical_storage_for_var(dst) == Some(wrong_storage))
        }));
        assert!(!block.ops.iter().any(|op| matches!(op, SSAOp::Load { .. })));
    }

    #[test]
    fn typed_dce_retains_frame_pointer_restore_on_each_return() {
        let frame_storage = register_storage(0, 8);
        let mut arch = ArchSpec::new("multi-return-frame-restore-test");
        arch.add_register(RegisterDef::new("frame_carrier", 0, 8));
        arch.add_register(RegisterDef::new("cond", 0x20, 1));
        arch.add_register(RegisterDef::new("stack_base", 0x40, 8));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: make_const(0x1008, 8),
            cond: make_reg(0x20, 1),
        });
        let mut left = R2ILBlock::new(0x1004, 4);
        left.push(R2ILOp::Load {
            dst: make_unique(0x100, 8),
            space: SpaceId::Ram,
            addr: make_reg(0x40, 8),
        });
        left.push(R2ILOp::Copy {
            dst: make_reg(0, 8),
            src: make_unique(0x100, 8),
        });
        left.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        let mut right = R2ILBlock::new(0x1008, 4);
        right.push(R2ILOp::Load {
            dst: make_unique(0x200, 8),
            space: SpaceId::Ram,
            addr: make_reg(0x40, 8),
        });
        right.push(R2ILOp::Copy {
            dst: make_reg(0, 8),
            src: make_unique(0x200, 8),
        });
        right.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        let mut func = SSAFunction::from_blocks_raw(&[entry, left, right], Some(&arch))
            .expect("multi-return frame restore SSA");

        optimize_with_interface(&mut func, &exact_frame_pointer_interface(frame_storage));

        for address in [0x1004, 0x1008] {
            let block = func.get_block(address).expect("return block");
            assert!(block.ops.iter().any(|op| {
                matches!(op, SSAOp::Copy { dst, .. }
                    if func.canonical_storage_for_var(dst) == Some(frame_storage))
            }));
            assert!(block.ops.iter().any(|op| matches!(op, SSAOp::Load { .. })));
        }
    }

    #[test]
    fn typed_dce_retains_frame_pointer_restore_in_return_predecessor() {
        let frame_storage = register_storage(0, 8);
        let mut function = predecessor_frame_restore_function(frame_storage.offset, false);

        optimize_with_interface(&mut function, &exact_frame_pointer_interface(frame_storage));

        assert!(frame_restore_chain_is_present(&function, frame_storage));
        assert!(matches!(
            function
                .get_block(0x1004)
                .expect("terminal return block")
                .ops
                .as_slice(),
            [SSAOp::Return { .. }]
        ));
    }

    #[test]
    fn typed_dce_retains_one_shared_restore_for_multiple_returns() {
        let frame_storage = register_storage(0, 8);
        let mut function = predecessor_frame_restore_function(frame_storage.offset, true);

        optimize_with_interface(&mut function, &exact_frame_pointer_interface(frame_storage));

        assert!(frame_restore_chain_is_present(&function, frame_storage));
        for address in [0x1004, 0x1008] {
            assert!(matches!(
                function
                    .get_block(address)
                    .expect("terminal return block")
                    .ops
                    .as_slice(),
                [SSAOp::Return { .. }]
            ));
        }
    }

    #[test]
    fn typed_dce_does_not_retain_wrong_predecessor_storage() {
        let frame_storage = register_storage(0, 8);
        let wrong_storage = register_storage(0x18, 8);
        let mut function = predecessor_frame_restore_function(wrong_storage.offset, true);

        optimize_with_interface(&mut function, &exact_frame_pointer_interface(frame_storage));

        let restore = function.get_block(0x1000).expect("restore predecessor");
        assert!(
            !restore
                .ops
                .iter()
                .any(|op| matches!(op, SSAOp::Load { .. }))
        );
        assert!(!restore.ops.iter().any(|op| {
            op.dst()
                .is_some_and(|dst| function.canonical_storage_for_var(dst) == Some(wrong_storage))
        }));
    }

    #[test]
    fn typed_dce_retains_wide_return_base_and_low_overlay() {
        let mut func = return_alias_function("carrier", "low_lane");
        let interface = exact_u32_return_interface(register_storage(0, 8));

        optimize_with_interface(&mut func, &interface);

        let retained = func
            .get_block(0x1000)
            .expect("return block")
            .ops
            .iter()
            .filter_map(|op| op.dst())
            .filter_map(|dst| func.canonical_storage_for_var(dst))
            .filter(|storage| canonical_register_storages_overlap(*storage, register_storage(0, 8)))
            .collect::<Vec<_>>();
        assert_eq!(
            retained,
            vec![register_storage(0, 8), register_storage(0, 1)],
            "the exact physical base and later low overlay form one return composition"
        );
    }

    #[test]
    fn typed_dce_retains_narrow_only_lowbits_return() {
        let mut func = narrow_return_function("carrier", "logical_result");
        let interface = exact_u32_return_interface(register_storage(0, 8));

        optimize_with_interface(&mut func, &interface);

        let retained = func
            .get_block(0x1000)
            .expect("return block")
            .ops
            .iter()
            .filter_map(|op| op.dst())
            .filter_map(|dst| func.canonical_storage_for_var(dst))
            .collect::<Vec<_>>();
        assert_eq!(
            retained,
            vec![register_storage(0, 4)],
            "a narrow write exactly covering the logical LowBits projection is the return value"
        );
    }

    #[test]
    fn typed_dce_retains_full_phi_beneath_later_overlay() {
        let mut func = return_phi_overlay_function("carrier", "low_lane");
        let interface = exact_u32_return_interface(register_storage(0, 8));

        optimize_with_interface(&mut func, &interface);

        let merge = func.get_block(0x100c).expect("return merge block");
        assert_eq!(merge.phis.len(), 1, "the return base phi must remain live");
        assert_eq!(
            merge.phis[0].canonical_storage,
            Some(register_storage(0, 8))
        );
        let overlays = merge
            .ops
            .iter()
            .filter_map(|op| op.dst())
            .filter_map(|dst| func.canonical_storage_for_var(dst))
            .collect::<Vec<_>>();
        assert_eq!(overlays, vec![register_storage(0, 1)]);
        for predecessor in [0x1004, 0x1008] {
            assert!(
                func.get_block(predecessor)
                    .expect("return predecessor")
                    .ops
                    .iter()
                    .filter_map(|op| op.dst())
                    .filter_map(|dst| func.canonical_storage_for_var(dst))
                    .any(|storage| storage == register_storage(0, 8)),
                "the retained phi must keep each predecessor definition live"
            );
        }
    }

    #[test]
    fn typed_dce_drops_shadowed_overlays_independent_of_names() {
        let interface = exact_u32_return_interface(register_storage(0, 8));
        let mut first = shadowed_overlay_function("whole_a", "slice_a");
        let mut renamed = shadowed_overlay_function("whole_b", "slice_b");

        optimize_with_interface(&mut first, &interface);
        optimize_with_interface(&mut renamed, &interface);

        let retained_writes = |function: &SSAFunction| {
            function
                .get_block(0x1000)
                .expect("return block")
                .ops
                .iter()
                .filter_map(|op| match op {
                    SSAOp::Copy { dst, src } => function
                        .canonical_storage_for_var(dst)
                        .map(|storage| (storage, src.constant_bits())),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        let expected = vec![
            (register_storage(0, 8), Some(0)),
            (register_storage(0, 1), Some(2)),
        ];
        assert_eq!(retained_writes(&first), expected);
        assert_eq!(retained_writes(&renamed), expected);
    }

    #[test]
    fn typed_return_liveness_is_carrier_name_independent() {
        let interface = exact_u32_return_interface(register_storage(0, 8));
        let mut first = return_alias_function("whole_a", "slice_a");
        let mut renamed = return_alias_function("whole_b", "slice_b");

        optimize_with_interface(&mut first, &interface);
        optimize_with_interface(&mut renamed, &interface);

        let retained_storages = |function: &SSAFunction| {
            function
                .get_block(0x1000)
                .expect("return block")
                .ops
                .iter()
                .filter_map(|op| op.dst())
                .filter_map(|dst| function.canonical_storage_for_var(dst))
                .collect::<Vec<_>>()
        };
        assert_eq!(retained_storages(&first), retained_storages(&renamed));
        let op_count = |function: &SSAFunction| {
            function
                .blocks()
                .map(|block| block.ops.len())
                .sum::<usize>()
        };
        assert_eq!(op_count(&first), op_count(&renamed));
    }

    #[test]
    fn typed_dce_ignores_spoofed_return_like_register_name() {
        let mut arch = ArchSpec::new("spoofed-return-name-test");
        arch.add_register(RegisterDef::new("actual_carrier", 0, 8));
        arch.add_register(RegisterDef::new("rax", 0x40, 8));
        arch.add_register(RegisterDef::new("pc", 0x80, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: make_reg(0, 8),
            src: make_const(7, 8),
        });
        block.push(R2ILOp::Copy {
            dst: make_reg(0x40, 8),
            src: make_const(9, 8),
        });
        block.push(R2ILOp::Return {
            target: make_reg(0x80, 8),
        });
        let mut func = SSAFunction::from_blocks_raw(&[block], Some(&arch)).expect("spoofed SSA");
        let interface = exact_u32_return_interface(register_storage(0, 8));

        optimize_with_interface(&mut func, &interface);

        let retained = func
            .get_block(0x1000)
            .expect("return block")
            .ops
            .iter()
            .filter_map(|op| op.dst())
            .filter_map(|dst| func.canonical_storage_for_var(dst))
            .collect::<Vec<_>>();
        assert!(retained.contains(&register_storage(0, 8)));
        assert!(
            !retained.contains(&register_storage(0x40, 8)),
            "a spoofed rax name outside the source-owned return storage must be dead"
        );
    }
}
