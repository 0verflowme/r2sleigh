//! Taint analysis built on SSA def-use chains.
//!
//! Tracks data flow from taint sources to sinks through the SSA graph.
//!
//! # Example
//!
//! ```ignore
//! use r2ssa::{SSAFunction, TaintAnalysis, DefaultTaintPolicy};
//!
//! let func = SSAFunction::from_blocks(&blocks).unwrap();
//! let policy = DefaultTaintPolicy::all_inputs();
//! let analysis = TaintAnalysis::new(&func, policy);
//! let result = analysis.analyze();
//!
//! for hit in &result.sink_hits {
//!     println!("Taint reaches sink at 0x{:x}", hit.block_addr);
//! }
//! ```

use std::collections::{HashMap, HashSet, VecDeque};

use r2il::ArchSpec;
use serde::{Deserialize, Serialize};

use crate::function::{SSABlock, SSAFunction, SourceSite, UseLocation};
use crate::op::SSAOp;
use crate::var::SSAVar;

/// A label identifying a taint source.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TaintLabel {
    /// Unique identifier for this taint source.
    pub id: String,
    /// Human-readable description.
    pub description: Option<String>,
}

impl TaintLabel {
    /// Create a new taint label with the given ID.
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            description: None,
        }
    }

    /// Add a description to this label.
    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }
}

/// Taint state for a single variable: set of labels that taint it.
pub type TaintSet = HashSet<TaintLabel>;

/// Policy for defining taint sources, sinks, and sanitizers.
///
/// Implement this trait to customize taint analysis behavior.
pub trait TaintPolicy {
    /// Check if a variable is a taint source. Returns labels if so.
    fn is_source(&self, var: &SSAVar, block_addr: u64) -> Option<Vec<TaintLabel>>;

    /// Check if an operation is a taint sink.
    fn is_sink(&self, op: &SSAOp, block_addr: u64) -> bool;

    /// Check if an operation sanitizes (clears) taint from its output.
    /// Default: no sanitizers.
    fn is_sanitizer(&self, _op: &SSAOp) -> bool {
        false
    }

    /// Custom propagation rule. By default, taint flows from all sources to dst.
    /// Return None to use default (union of source taints).
    fn propagate(&self, _op: &SSAOp, _source_taints: &[&TaintSet]) -> Option<TaintSet> {
        None
    }
}

const X86_64_SYSV_ARG_REGS: [&str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
const NO_CALL_ARG_REGS: [&str; 0] = [];

/// Return calling-convention argument registers for the active architecture.
///
/// Currently populated only for x86-64 SysV and intentionally empty for all
/// other/unknown architectures.
pub fn call_arg_regs(arch: Option<&ArchSpec>) -> &'static [&'static str] {
    let Some(arch) = arch else {
        return &NO_CALL_ARG_REGS;
    };
    let arch_name = arch.name.to_ascii_lowercase();
    let looks_x86 = arch_name.contains("x86");
    let looks_64 = arch.addr_size == 8 || arch_name.contains("64");
    if looks_x86 && looks_64 {
        &X86_64_SYSV_ARG_REGS
    } else {
        &NO_CALL_ARG_REGS
    }
}

/// Default policy: function inputs (version 0 registers) are sources.
#[derive(Debug, Clone, Default)]
pub struct DefaultTaintPolicy {
    /// Variable names to treat as sources. If empty, all version-0 registers are sources.
    pub sources: HashSet<String>,
    /// Whether calls are sinks.
    pub sink_calls: bool,
    /// Whether stores are sinks.
    pub sink_stores: bool,
}

impl DefaultTaintPolicy {
    /// Create a new default policy.
    pub fn new() -> Self {
        Self {
            sources: HashSet::new(),
            sink_calls: true,
            sink_stores: true,
        }
    }

    /// Add a specific variable name as a source.
    pub fn with_source(mut self, name: impl Into<String>) -> Self {
        self.sources.insert(name.into());
        self
    }

    /// Mark all function inputs (version 0 non-const, non-temp) as sources.
    pub fn all_inputs() -> Self {
        Self {
            sources: HashSet::new(), // Empty means all inputs
            sink_calls: true,
            sink_stores: true,
        }
    }

    /// Configure whether calls are sinks.
    pub fn with_sink_calls(mut self, enabled: bool) -> Self {
        self.sink_calls = enabled;
        self
    }

    /// Configure whether stores are sinks.
    pub fn with_sink_stores(mut self, enabled: bool) -> Self {
        self.sink_stores = enabled;
        self
    }
}

impl TaintPolicy for DefaultTaintPolicy {
    fn is_source(&self, var: &SSAVar, _block_addr: u64) -> Option<Vec<TaintLabel>> {
        // Version 0 variables that are registers (not const/temp) are inputs
        if var.version == 0
            && var.is_register()
            && (self.sources.is_empty() || self.sources.contains(&var.name))
        {
            return Some(vec![TaintLabel::new(format!("input:{}", var.name))]);
        }
        None
    }

    fn is_sink(&self, op: &SSAOp, _block_addr: u64) -> bool {
        match op {
            SSAOp::Call { .. } | SSAOp::CallInd { .. } if self.sink_calls => true,
            SSAOp::Store { .. } if self.sink_stores => true,
            _ => false,
        }
    }
}

/// A taint reaching a sink.
#[derive(Debug, Clone)]
pub struct SinkHit {
    /// Block address where the sink is located.
    pub block_addr: u64,
    /// Operation index within the block.
    pub op_idx: usize,
    /// The sink operation.
    pub op: SSAOp,
    /// Variables that are tainted at this sink, with their taint labels.
    pub tainted_vars: Vec<(SSAVar, TaintSet)>,
}

/// Result of taint analysis.
#[derive(Debug, Clone, Default)]
pub struct TaintResult {
    /// Taint state for each variable (by display_name).
    pub var_taints: HashMap<String, TaintSet>,
    /// Sink violations: operations where tainted data reaches a sink.
    pub sink_hits: Vec<SinkHit>,
}

impl TaintResult {
    /// Check if a variable is tainted.
    pub fn is_tainted(&self, var: &SSAVar) -> bool {
        self.var_taints
            .get(&var.display_name())
            .map(|t| !t.is_empty())
            .unwrap_or(false)
    }

    /// Get taint labels for a variable.
    pub fn get_taint(&self, var: &SSAVar) -> Option<&TaintSet> {
        self.var_taints.get(&var.display_name())
    }

    /// Check if any sinks were hit by tainted data.
    pub fn has_violations(&self) -> bool {
        !self.sink_hits.is_empty()
    }

    /// Get the number of tainted variables.
    pub fn num_tainted(&self) -> usize {
        self.var_taints.values().filter(|t| !t.is_empty()).count()
    }

    /// Get all tainted variable names.
    pub fn tainted_vars(&self) -> impl Iterator<Item = &str> {
        self.var_taints
            .iter()
            .filter(|(_, t)| !t.is_empty())
            .map(|(name, _)| name.as_str())
    }
}

/// Taint analysis engine.
///
/// Performs forward taint propagation through SSA def-use chains.
pub struct TaintAnalysis<'a, P: TaintPolicy> {
    func: &'a SSAFunction,
    policy: P,
    call_arg_regs: Vec<&'static str>,
}

impl<'a, P: TaintPolicy> TaintAnalysis<'a, P> {
    /// Create a new taint analysis for the given function.
    pub fn new(func: &'a SSAFunction, policy: P) -> Self {
        Self {
            func,
            policy,
            call_arg_regs: Vec::new(),
        }
    }

    /// Create a taint analysis with architecture-aware call argument handling.
    pub fn with_arch(func: &'a SSAFunction, policy: P, arch: Option<&ArchSpec>) -> Self {
        Self {
            func,
            policy,
            call_arg_regs: call_arg_regs(arch).to_vec(),
        }
    }

    /// Run forward taint propagation.
    ///
    /// Returns a `TaintResult` containing the taint state for all variables
    /// and any sink violations found.
    pub fn analyze(&self) -> TaintResult {
        let mut var_taints: HashMap<SSAVar, TaintSet> = HashMap::new();
        let mut worklist: VecDeque<SSAVar> = VecDeque::new();
        let use_map = self.build_use_map();

        // Phase 1: Initialize sources
        self.initialize_sources(&mut var_taints, &mut worklist);

        // Phase 2: Forward propagation via worklist
        self.propagate(&use_map, &mut var_taints, &mut worklist);

        // Phase 3: Find sink hits
        let sink_hits = self.find_sink_hits(&var_taints);

        let var_taints = var_taints
            .into_iter()
            .map(|(var, taint)| (var.display_name(), taint))
            .collect();

        TaintResult {
            var_taints,
            sink_hits,
        }
    }

    /// Build variable use index for fast taint propagation lookups.
    fn build_use_map(&self) -> HashMap<SSAVar, Vec<(u64, UseLocation)>> {
        let mut uses: HashMap<SSAVar, Vec<(u64, UseLocation)>> = HashMap::new();
        for block in self.func.blocks() {
            block.for_each_source(|src| {
                let use_loc = match src.site {
                    SourceSite::Phi {
                        phi_idx, src_idx, ..
                    } => UseLocation::Phi { phi_idx, src_idx },
                    SourceSite::Op { op_idx, src_idx } => UseLocation::Op { op_idx, src_idx },
                };
                uses.entry(src.var.clone())
                    .or_default()
                    .push((block.addr, use_loc));
            });
        }
        uses
    }

    /// Initialize taint sources.
    fn initialize_sources(
        &self,
        var_taints: &mut HashMap<SSAVar, TaintSet>,
        worklist: &mut VecDeque<SSAVar>,
    ) {
        for block in self.func.blocks() {
            block.for_each_source(|src| {
                self.maybe_add_source(src.var, block.addr, var_taints, worklist);
            });
        }
    }

    /// Check if a variable is a source and add it to the taint state.
    fn maybe_add_source(
        &self,
        var: &SSAVar,
        block_addr: u64,
        var_taints: &mut HashMap<SSAVar, TaintSet>,
        worklist: &mut VecDeque<SSAVar>,
    ) {
        if let Some(labels) = self.policy.is_source(var, block_addr) {
            let taint = var_taints.entry(var.clone()).or_default();
            let old_size = taint.len();
            taint.extend(labels);
            if taint.len() > old_size {
                worklist.push_back(var.clone());
            }
        }
    }

    /// Forward propagation via worklist algorithm.
    ///
    /// Uses taint-state tracking instead of a simple visited set to ensure
    /// all labels are propagated even when a variable is reached via multiple paths.
    fn propagate(
        &self,
        use_map: &HashMap<SSAVar, Vec<(u64, UseLocation)>>,
        var_taints: &mut HashMap<SSAVar, TaintSet>,
        worklist: &mut VecDeque<SSAVar>,
    ) {
        // Track the taint state we've already propagated for each variable.
        // This allows re-propagation when new labels are added.
        let mut propagated: HashMap<SSAVar, TaintSet> = HashMap::new();

        while let Some(var) = worklist.pop_front() {
            let current_taint = match var_taints.get(&var) {
                Some(t) if !t.is_empty() => t.clone(),
                _ => continue,
            };

            // Check if we have new labels to propagate
            let already_propagated = propagated.entry(var.clone()).or_default();
            let new_labels: TaintSet = current_taint
                .difference(already_propagated)
                .cloned()
                .collect();

            if new_labels.is_empty() {
                continue;
            }

            // Mark these labels as propagated
            already_propagated.extend(new_labels.clone());

            let Some(uses) = use_map.get(&var) else {
                continue;
            };
            for (block_addr, use_loc) in uses {
                match use_loc {
                    UseLocation::Phi { phi_idx, .. } => {
                        self.propagate_to_phi(
                            *block_addr,
                            *phi_idx,
                            &new_labels,
                            var_taints,
                            worklist,
                        );
                    }
                    UseLocation::Op { op_idx, .. } => {
                        self.propagate_to_op(
                            *block_addr,
                            *op_idx,
                            &new_labels,
                            var_taints,
                            worklist,
                        );
                    }
                }
            }
        }
    }

    /// Propagate taint through a phi node.
    fn propagate_to_phi(
        &self,
        block_addr: u64,
        phi_idx: usize,
        current_taint: &TaintSet,
        var_taints: &mut HashMap<SSAVar, TaintSet>,
        worklist: &mut VecDeque<SSAVar>,
    ) {
        if let Some(block) = self.func.get_block(block_addr)
            && let Some(phi) = block.phis.get(phi_idx)
        {
            let dst_taint = var_taints.entry(phi.dst.clone()).or_default();
            let old_size = dst_taint.len();
            dst_taint.extend(current_taint.clone());
            if dst_taint.len() > old_size {
                worklist.push_back(phi.dst.clone());
            }
        }
    }

    /// Propagate taint through an operation.
    fn propagate_to_op(
        &self,
        block_addr: u64,
        op_idx: usize,
        current_taint: &TaintSet,
        var_taints: &mut HashMap<SSAVar, TaintSet>,
        worklist: &mut VecDeque<SSAVar>,
    ) {
        if let Some(block) = self.func.get_block(block_addr)
            && let Some(op) = block.ops.get(op_idx)
        {
            // Check sanitizer
            if self.policy.is_sanitizer(op) {
                return;
            }

            // Propagate to destination
            if let Some(dst) = op.dst() {
                // Collect all source taints for custom propagation
                let source_taints: Vec<&TaintSet> = op
                    .sources()
                    .into_iter()
                    .filter_map(|src| var_taints.get(src))
                    .collect();

                // Try custom propagation rule first
                let new_taint = if let Some(custom) = self.policy.propagate(op, &source_taints) {
                    custom
                } else {
                    // Default: union of incoming taint
                    current_taint.clone()
                };

                let dst_taint = var_taints.entry(dst.clone()).or_default();
                let old_size = dst_taint.len();
                dst_taint.extend(new_taint);
                if dst_taint.len() > old_size {
                    worklist.push_back(dst.clone());
                }
            }
        }
    }

    /// Find all sink hits.
    fn find_sink_hits(&self, var_taints: &HashMap<SSAVar, TaintSet>) -> Vec<SinkHit> {
        let mut sink_hits = Vec::new();

        for block in self.func.blocks() {
            for (op_idx, op) in block.ops.iter().enumerate() {
                if self.policy.is_sink(op, block.addr) {
                    let mut tainted_vars = Vec::new();
                    for src in self.sink_sources_for_op(block, op_idx, op) {
                        if let Some(taint) = var_taints.get(&src)
                            && !taint.is_empty()
                        {
                            tainted_vars.push((src, taint.clone()));
                        }
                    }
                    if !tainted_vars.is_empty() {
                        sink_hits.push(SinkHit {
                            block_addr: block.addr,
                            op_idx,
                            op: op.clone(),
                            tainted_vars,
                        });
                    }
                }
            }
        }

        sink_hits
    }

    /// Collect source variables relevant for sink checking.
    ///
    /// For call sinks, we include both call target source(s) and the latest
    /// in-block argument register setup before the call.
    fn sink_sources_for_op(&self, block: &SSABlock, op_idx: usize, op: &SSAOp) -> Vec<SSAVar> {
        let mut sink_sources: Vec<SSAVar> = op.sources().into_iter().cloned().collect();
        if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
            sink_sources.extend(self.collect_call_arg_vars(block, op_idx));
        }

        let mut seen = HashSet::new();
        sink_sources.retain(|var| seen.insert(var.clone()));
        sink_sources
    }

    /// Collect inferred call argument variables set before a call.
    ///
    /// NOTE: This is intentionally intra-block only. Optimized binaries may
    /// prepare call arguments in predecessor blocks; cross-block reaching-def
    /// recovery is a follow-up.
    fn collect_call_arg_vars(&self, block: &SSABlock, call_op_idx: usize) -> Vec<SSAVar> {
        if self.call_arg_regs.is_empty() || call_op_idx == 0 {
            return Vec::new();
        }

        let mut found: HashMap<&'static str, SSAVar> = HashMap::new();
        let mut idx = call_op_idx;
        while idx > 0 {
            idx -= 1;
            let prev = &block.ops[idx];

            if matches!(prev, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
                break;
            }

            let Some(dst) = prev.dst() else {
                continue;
            };
            let Some(canonical) = Self::canonical_x86_64_arg_reg(&dst.name) else {
                continue;
            };
            if !self.call_arg_regs.contains(&canonical) {
                continue;
            }

            // Backward scan: first match per arg is the last chronological write.
            found.entry(canonical).or_insert_with(|| dst.clone());
        }

        let mut ordered = Vec::new();
        for reg in &self.call_arg_regs {
            if let Some(var) = found.remove(reg) {
                ordered.push(var);
            }
        }
        ordered
    }

    fn canonical_x86_64_arg_reg(name: &str) -> Option<&'static str> {
        let base = name.split('_').next().unwrap_or(name).to_ascii_lowercase();
        match base.as_str() {
            "rdi" | "edi" | "di" | "dil" => Some("rdi"),
            "rsi" | "esi" | "si" | "sil" => Some("rsi"),
            "rdx" | "edx" | "dx" | "dl" | "dh" => Some("rdx"),
            "rcx" | "ecx" | "cx" | "cl" | "ch" => Some("rcx"),
            "r8" | "r8d" | "r8w" | "r8b" => Some("r8"),
            "r9" | "r9d" | "r9w" | "r9b" => Some("r9"),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    fn make_var(name: &str, version: u32) -> SSAVar {
        SSAVar::new(name, version, 8)
    }

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn make_const(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    fn make_x86_64_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("eax", 0, 4));
        arch.add_register(RegisterDef::new("rsi", 32, 8));
        arch.add_register(RegisterDef::new("esi", 32, 4));
        arch.add_register(RegisterDef::new("rdi", 56, 8));
        arch.add_register(RegisterDef::new("edi", 56, 4));
        arch.add_register(RegisterDef::new("rdx", 64, 8));
        arch.add_register(RegisterDef::new("edx", 64, 4));
        arch.add_register(RegisterDef::new("rcx", 80, 8));
        arch.add_register(RegisterDef::new("ecx", 80, 4));
        arch.add_register(RegisterDef::new("r8", 88, 8));
        arch.add_register(RegisterDef::new("r8d", 88, 4));
        arch.add_register(RegisterDef::new("r9", 96, 8));
        arch.add_register(RegisterDef::new("r9d", 96, 4));
        arch
    }

    #[test]
    fn test_taint_label() {
        let label = TaintLabel::new("user_input").with_description("From stdin");
        assert_eq!(label.id, "user_input");
        assert_eq!(label.description, Some("From stdin".to_string()));
    }

    #[test]
    fn test_taint_label_equality() {
        let l1 = TaintLabel::new("src1");
        let l2 = TaintLabel::new("src1");
        let l3 = TaintLabel::new("src2");

        assert_eq!(l1, l2);
        assert_ne!(l1, l3);
    }

    #[test]
    fn test_default_policy_source_all_inputs() {
        let policy = DefaultTaintPolicy::all_inputs();

        // Version 0 register is a source
        let reg = make_var("RAX", 0);
        assert!(policy.is_source(&reg, 0x1000).is_some());

        // Version 1 is not a source (already defined)
        let reg_v1 = make_var("RAX", 1);
        assert!(policy.is_source(&reg_v1, 0x1000).is_none());

        // Const is not a source
        let cst = make_var("const:42", 0);
        assert!(policy.is_source(&cst, 0x1000).is_none());

        // Temp is not a source
        let tmp = make_var("tmp:0x1000", 0);
        assert!(policy.is_source(&tmp, 0x1000).is_none());
    }

    #[test]
    fn test_default_policy_source_specific() {
        let policy = DefaultTaintPolicy::new()
            .with_source("RDI")
            .with_source("RSI");

        // RDI v0 is a source
        let rdi = make_var("RDI", 0);
        assert!(policy.is_source(&rdi, 0x1000).is_some());

        // RSI v0 is a source
        let rsi = make_var("RSI", 0);
        assert!(policy.is_source(&rsi, 0x1000).is_some());

        // RAX v0 is NOT a source (not in list)
        let rax = make_var("RAX", 0);
        assert!(policy.is_source(&rax, 0x1000).is_none());
    }

    #[test]
    fn test_default_policy_sink() {
        let policy = DefaultTaintPolicy::new();

        let call_op = SSAOp::Call {
            target: make_var("const:0x1000", 0),
        };
        assert!(policy.is_sink(&call_op, 0));

        let call_ind_op = SSAOp::CallInd {
            target: make_var("RAX", 1),
        };
        assert!(policy.is_sink(&call_ind_op, 0));

        let store_op = SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: make_var("RAX", 1),
            val: make_var("RBX", 0),
        };
        assert!(policy.is_sink(&store_op, 0));

        let add_op = SSAOp::IntAdd {
            dst: make_var("RAX", 2),
            a: make_var("RAX", 1),
            b: make_var("RBX", 0),
        };
        assert!(!policy.is_sink(&add_op, 0));
    }

    #[test]
    fn test_default_policy_sink_disabled() {
        let policy = DefaultTaintPolicy::new()
            .with_sink_calls(false)
            .with_sink_stores(false);

        let call_op = SSAOp::Call {
            target: make_var("const:0x1000", 0),
        };
        assert!(!policy.is_sink(&call_op, 0));

        let store_op = SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: make_var("RAX", 1),
            val: make_var("RBX", 0),
        };
        assert!(!policy.is_sink(&store_op, 0));
    }

    #[test]
    fn test_taint_result_empty() {
        let result = TaintResult::default();
        assert!(!result.has_violations());
        assert_eq!(result.num_tainted(), 0);

        let var = make_var("RAX", 0);
        assert!(!result.is_tainted(&var));
        assert!(result.get_taint(&var).is_none());
    }

    #[test]
    fn test_taint_result_with_data() {
        let mut result = TaintResult::default();

        let var = make_var("RAX", 1);
        let mut taint = TaintSet::new();
        taint.insert(TaintLabel::new("input:RDI"));
        result.var_taints.insert(var.display_name(), taint);

        assert!(result.is_tainted(&var));
        assert_eq!(result.num_tainted(), 1);

        let taint_labels = result.get_taint(&var).unwrap();
        assert!(taint_labels.contains(&TaintLabel::new("input:RDI")));
    }

    #[test]
    fn test_taint_set_operations() {
        let mut set = TaintSet::new();
        set.insert(TaintLabel::new("src1"));
        set.insert(TaintLabel::new("src2"));

        assert_eq!(set.len(), 2);
        assert!(set.contains(&TaintLabel::new("src1")));
        assert!(set.contains(&TaintLabel::new("src2")));
        assert!(!set.contains(&TaintLabel::new("src3")));
    }

    #[test]
    fn call_sink_uses_last_intrablock_arg_write() {
        let arch = make_x86_64_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 3,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(56, 8), // rdi
                    src: make_reg(0, 8),  // rax
                },
                R2ILOp::Copy {
                    dst: make_reg(56, 4), // edi (later write to same arg register)
                    src: make_reg(0, 4),  // eax
                },
                R2ILOp::Call {
                    target: make_const(0x401000, 8),
                },
            ],
        }];

        let func = SSAFunction::from_blocks_raw(&blocks, Some(&arch))
            .expect("Failed to build SSA function");
        let policy = DefaultTaintPolicy::all_inputs().with_sink_stores(false);
        let analysis = TaintAnalysis::with_arch(&func, policy, Some(&arch));
        let result = analysis.analyze();

        let call_hit = result
            .sink_hits
            .iter()
            .find(|hit| matches!(hit.op, SSAOp::Call { .. }))
            .expect("Expected a call sink hit");
        let names: Vec<String> = call_hit
            .tainted_vars
            .iter()
            .map(|(var, _)| var.display_name())
            .collect();

        assert!(
            names.iter().any(|name| name == "EDI_1"),
            "Backward scan should pick the latest intrablock write to arg register"
        );
        assert!(
            !names.iter().any(|name| name == "RDI_1"),
            "Earlier arg write should be ignored when a later write exists"
        );
    }

    #[test]
    fn call_sink_detects_tainted_arg_when_target_not_tainted() {
        let arch = make_x86_64_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 2,
            switch_info: None,
            op_metadata: Default::default(),
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(56, 8), // rdi
                    src: make_reg(32, 8), // rsi
                },
                R2ILOp::Call {
                    target: make_const(0x402000, 8),
                },
            ],
        }];

        let func = SSAFunction::from_blocks_raw(&blocks, Some(&arch))
            .expect("Failed to build SSA function");
        let policy = DefaultTaintPolicy::new()
            .with_source("rsi")
            .with_sink_stores(false);
        let analysis = TaintAnalysis::with_arch(&func, policy, Some(&arch));
        let result = analysis.analyze();

        let call_hit = result
            .sink_hits
            .iter()
            .find(|hit| matches!(hit.op, SSAOp::Call { .. }))
            .expect("Expected a call sink hit from tainted argument setup");
        let names: Vec<String> = call_hit
            .tainted_vars
            .iter()
            .map(|(var, _)| var.display_name())
            .collect();

        assert!(
            names.iter().any(|name| name == "RDI_1"),
            "Call sink should include tainted call argument register"
        );
        assert!(
            !names.iter().any(|name| {
                crate::var::SSAVarNameKind::classify(&name.to_ascii_lowercase()).is_constant()
            }),
            "Call target constant should not be treated as a tainted argument source"
        );
    }

    #[test]
    fn taint_propagates_through_phi_merge_to_store_sink() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                op_metadata: std::collections::BTreeMap::new(),
                switch_info: None,
                ops: vec![R2ILOp::CBranch {
                    cond: make_const(1, 1),
                    target: make_const(0x1008, 8),
                }],
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                op_metadata: std::collections::BTreeMap::new(),
                switch_info: None,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_reg(8, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x100c, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                op_metadata: std::collections::BTreeMap::new(),
                switch_info: None,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x100c, 8),
                    },
                ],
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                op_metadata: std::collections::BTreeMap::new(),
                switch_info: None,
                ops: vec![R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: make_const(0x2000, 8),
                    val: make_reg(0, 8),
                }],
            },
        ];

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let merge = func.get_block(0x100c).expect("merge block");
        assert!(
            !merge.phis.is_empty(),
            "fixture must include a merge phi for reg:0"
        );

        let policy = DefaultTaintPolicy::all_inputs()
            .with_sink_calls(false)
            .with_sink_stores(true);
        let analysis = TaintAnalysis::new(&func, policy);
        let result = analysis.analyze();

        let sink_hit = result
            .sink_hits
            .iter()
            .find(|hit| matches!(hit.op, SSAOp::Store { .. }))
            .expect("store sink should be present");
        assert!(
            sink_hit
                .tainted_vars
                .iter()
                .any(|(var, _)| var.name == "reg:0"),
            "taint should flow through phi-merged reg:0 into the store sink"
        );
    }

    // Custom policy for testing
    struct TestPolicy {
        source_var: String,
    }

    impl TaintPolicy for TestPolicy {
        fn is_source(&self, var: &SSAVar, _block_addr: u64) -> Option<Vec<TaintLabel>> {
            if var.name == self.source_var && var.version == 0 {
                Some(vec![TaintLabel::new("test_source")])
            } else {
                None
            }
        }

        fn is_sink(&self, op: &SSAOp, _block_addr: u64) -> bool {
            matches!(op, SSAOp::Store { .. })
        }

        fn is_sanitizer(&self, op: &SSAOp) -> bool {
            // XOR with self is a sanitizer (common zeroing pattern)
            if let SSAOp::IntXor { a, b, .. } = op {
                a == b
            } else {
                false
            }
        }
    }

    #[test]
    fn test_custom_policy() {
        let policy = TestPolicy {
            source_var: "user_data".to_string(),
        };

        let src = SSAVar::new("user_data", 0, 8);
        assert!(policy.is_source(&src, 0).is_some());

        let other = SSAVar::new("RAX", 0, 8);
        assert!(policy.is_source(&other, 0).is_none());

        let store = SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: SSAVar::new("RAX", 1, 8),
            val: SSAVar::new("RBX", 0, 8),
        };
        assert!(policy.is_sink(&store, 0));

        let call = SSAOp::Call {
            target: SSAVar::new("const:0x1000", 0, 8),
        };
        assert!(!policy.is_sink(&call, 0));

        // XOR RAX, RAX is a sanitizer
        let xor_self = SSAOp::IntXor {
            dst: SSAVar::new("RAX", 2, 8),
            a: SSAVar::new("RAX", 1, 8),
            b: SSAVar::new("RAX", 1, 8),
        };
        assert!(policy.is_sanitizer(&xor_self));

        // XOR RAX, RBX is not a sanitizer
        let xor_other = SSAOp::IntXor {
            dst: SSAVar::new("RAX", 2, 8),
            a: SSAVar::new("RAX", 1, 8),
            b: SSAVar::new("RBX", 0, 8),
        };
        assert!(!policy.is_sanitizer(&xor_other));
    }
}
