//! Function-level SSA representation.
//!
//! This module provides the `SSAFunction` type which combines all SSA
//! components for a complete function: CFG, dominator tree, phi nodes,
//! and renamed operations.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Deref;
use std::sync::{Arc, OnceLock, RwLock};

use r2il::{ArchSpec, R2ILBlock};
use serde::{Deserialize, Serialize};

use crate::AssumptionSet;
use crate::block::SSABlock as LocalSSABlock;
use crate::cfg::{CFG, CFGEdge};
use crate::defuse::{BackwardSlice, SliceOpRef, backward_slice_from_op, backward_slice_from_var};
use crate::domtree::DomTree;
use crate::graph::SsaGraph;
use crate::naming::{ArchCacheTag, cached_register_name_map};
use crate::op::SSAOp;
use crate::phi::{PhiPlacement, collect_defs_from_cfg_with_names};
use crate::rename::{
    CallBoundaryConfig, CallBoundaryDef, rename_function_with_names,
    rename_function_with_names_and_call_boundaries,
};
use crate::semantic::{
    CallSiteFacts, MemoryDefFact, MemorySSAFacts, MemoryUseFact, ObjectId, ObjectModel,
    PredicateFacts, PreparedFunctionFacts, StructuredDataflowFacts,
};
use crate::var::SSAVar;

/// Switch case information: Vec of (case_value, target_address) pairs and optional default target.
pub type SwitchInfo = (Vec<(u64, u64)>, Option<u64>);

/// Query-only CFG risk summary for decompilation preflight.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CFGRiskSummary {
    pub block_count: usize,
    pub loop_count: usize,
    pub back_edge_count: usize,
    pub switch_block_count: usize,
    pub max_switch_cases: usize,
}

/// Canonical base used to form a proven stack address.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StackAddressBase {
    FramePointer,
    StackPointer,
}

/// Proven stack-address root: `base +/- offset`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StackAddressRoot {
    pub base: StackAddressBase,
    pub offset: i64,
}

/// Decompiler-prep analysis facts derived from SSA.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DecompilePrepFacts {
    pub canonical_value_roots: BTreeMap<SSAVar, SSAVar>,
    pub stack_address_roots: BTreeMap<SSAVar, StackAddressRoot>,
}

/// Typed preparation mode for downstream SSA consumers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionPrepareMode {
    Generic,
    Raw,
    Decompile,
    Patterns,
    DataRefs,
    Symbolic,
}

/// Canonical SSA artifact consumed by downstream analysis layers.
#[derive(Debug, Clone)]
pub struct SsaArtifact {
    function: SSAFunction,
    graph: SsaGraph,
    mode: FunctionPrepareMode,
    facts: PreparedFunctionFacts,
}

impl SsaArtifact {
    fn new(function: SSAFunction, mode: FunctionPrepareMode) -> Self {
        let graph = SsaGraph::from_function(&function);
        let facts = PreparedFunctionFacts::collect(&function, &graph);
        Self {
            function,
            graph,
            mode,
            facts,
        }
    }

    pub fn from_blocks(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new(
            SSAFunction::from_blocks_with_arch(blocks, arch)?,
            FunctionPrepareMode::Generic,
        ))
    }

    pub fn raw(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new(
            SSAFunction::from_blocks_raw(blocks, arch)?,
            FunctionPrepareMode::Raw,
        ))
    }

    pub fn for_decompile(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new(
            SSAFunction::from_blocks_for_decompile(blocks, arch)?,
            FunctionPrepareMode::Decompile,
        ))
    }

    pub fn for_patterns(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new(
            SSAFunction::from_blocks_for_patterns(blocks, arch)?,
            FunctionPrepareMode::Patterns,
        ))
    }

    pub fn for_data_refs(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new(
            SSAFunction::from_blocks_for_data_refs(blocks, arch)?,
            FunctionPrepareMode::DataRefs,
        ))
    }

    pub fn for_symbolic(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        let mut function = SSAFunction::from_blocks_raw(blocks, arch)?;
        function.refresh_decompile_prep_facts(arch);
        Some(Self::new(function, FunctionPrepareMode::Symbolic))
    }

    pub fn mode(&self) -> FunctionPrepareMode {
        self.mode
    }

    pub fn function(&self) -> &SSAFunction {
        &self.function
    }

    pub fn graph(&self) -> &SsaGraph {
        &self.graph
    }

    pub fn into_function(self) -> SSAFunction {
        self.function
    }

    pub fn facts(&self) -> &PreparedFunctionFacts {
        &self.facts
    }

    pub fn with_assumptions(&self, assumptions: &AssumptionSet) -> Self {
        let facts = PreparedFunctionFacts::collect_with_assumptions(
            &self.function,
            &self.graph,
            assumptions,
        );
        Self {
            function: self.function.clone(),
            graph: self.graph.clone(),
            mode: self.mode,
            facts,
        }
    }

    pub fn objects(&self) -> &ObjectModel {
        &self.facts.objects
    }

    pub fn memory(&self) -> &MemorySSAFacts {
        &self.facts.memory
    }

    pub fn predicates(&self) -> &PredicateFacts {
        &self.facts.predicates
    }

    pub fn call_sites(&self) -> &CallSiteFacts {
        &self.facts.call_sites
    }

    pub fn structured(&self) -> &StructuredDataflowFacts {
        &self.facts.structured
    }

    pub fn resolved_call_target(&self, call: &crate::semantic::CallSiteFact) -> Option<u64> {
        call.direct_target.or_else(|| {
            let value_id = canonical_root_value_id(self, call.target);
            let var = self.value_var(value_id)?;
            parse_literal_value_name(&var.name)
        })
    }

    pub fn value_var(&self, value_id: crate::graph::ValueId) -> Option<&SSAVar> {
        self.graph.value(value_id).map(|value| &value.var)
    }

    pub fn inst_op_site(&self, inst_id: crate::graph::InstId) -> Option<(u64, usize)> {
        self.graph.op_site_for_inst(inst_id)
    }

    pub fn object_for_var(&self, var: &SSAVar) -> Option<ObjectId> {
        self.graph
            .value_id_for_var(var)
            .and_then(|value_id| self.objects().object_for_value(value_id))
    }

    pub fn memory_uses_for_op_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&[MemoryUseFact]> {
        self.graph
            .inst_id_for_op_site(block_addr, op_idx)
            .and_then(|inst_id| self.memory().uses_by_inst.get(&inst_id))
            .map(|facts| facts.as_slice())
    }

    pub fn memory_defs_for_op_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&[MemoryDefFact]> {
        self.graph
            .inst_id_for_op_site(block_addr, op_idx)
            .and_then(|inst_id| self.memory().defs_by_inst.get(&inst_id))
            .map(|facts| facts.as_slice())
    }

    pub fn with_name(mut self, name: impl Into<String>) -> Self {
        self.function = self.function.with_name(name);
        self
    }

    pub fn local_ssa_blocks(&self) -> Vec<LocalSSABlock> {
        self.function
            .blocks()
            .map(|block| LocalSSABlock {
                addr: block.addr,
                size: block.size,
                ops: block.ops.clone(),
            })
            .collect()
    }
}

fn canonical_root_value_id(
    prepared: &SsaArtifact,
    value_id: crate::graph::ValueId,
) -> crate::graph::ValueId {
    let Some(facts) = prepared.function().decompile_prep_facts() else {
        return value_id;
    };
    let Some(start) = prepared.value_var(value_id) else {
        return value_id;
    };
    let mut current = start.clone();
    let mut current_id = value_id;
    for _ in 0..32 {
        let Some(next) = facts.canonical_root_of(&current) else {
            break;
        };
        if next == &current {
            break;
        }
        let Some(next_id) = prepared.graph().value_id_for_var(next) else {
            break;
        };
        current = next.clone();
        current_id = next_id;
    }
    current_id
}

fn parse_literal_value_name(name: &str) -> Option<u64> {
    let value_str = if let Some(value) = name.strip_prefix("const:") {
        value
    } else if let Some(value) = name.strip_prefix("ram:") {
        value
    } else {
        return None;
    };
    let value_str = value_str.split('_').next().unwrap_or(value_str);
    if let Some(dec) = value_str
        .strip_prefix("0d")
        .or_else(|| value_str.strip_prefix("0D"))
    {
        return dec.parse().ok();
    }
    if let Some(hex) = value_str
        .strip_prefix("0x")
        .or_else(|| value_str.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }
    value_str.parse().ok()
}

impl Deref for SsaArtifact {
    type Target = SSAFunction;

    fn deref(&self) -> &Self::Target {
        &self.function
    }
}

impl DecompilePrepFacts {
    pub fn canonical_root_of(&self, var: &SSAVar) -> Option<&SSAVar> {
        self.canonical_value_roots.get(var)
    }

    pub fn stack_address_root_of(&self, var: &SSAVar) -> Option<&StackAddressRoot> {
        self.stack_address_roots.get(var)
    }
}

/// A function in SSA form.
///
/// This is the main entry point for function-level SSA analysis.
/// It contains the CFG, dominator tree, and SSA operations for all blocks.
#[derive(Debug)]
pub struct SSAFunction {
    /// The function's name (if known).
    pub name: Option<String>,
    /// Entry point address.
    pub entry: u64,
    /// Control flow graph.
    cfg: CFG,
    /// Dominator tree.
    domtree: DomTree,
    /// SSA operations for each block.
    blocks: HashMap<u64, SSABlock>,
    /// Block addresses in reverse postorder.
    block_order: Vec<u64>,
    /// Optional decompiler-prep fact snapshot for the current SSA state.
    decompile_prep_facts: Option<DecompilePrepFacts>,
    /// Structural def/use index for repeated SSA queries.
    query_index: RwLock<Option<SsaQueryIndex>>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct SsaQueryIndex {
    defs: HashMap<SSAVar, (u64, DefLocation)>,
    uses: HashMap<SSAVar, Vec<(u64, UseLocation)>>,
}

impl Clone for SSAFunction {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            entry: self.entry,
            cfg: self.cfg.clone(),
            domtree: self.domtree.clone(),
            blocks: self.blocks.clone(),
            block_order: self.block_order.clone(),
            decompile_prep_facts: self.decompile_prep_facts.clone(),
            query_index: RwLock::new(None),
        }
    }
}

/// A basic block in SSA form.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SSABlock {
    /// Block address.
    pub addr: u64,
    /// Block size in bytes.
    pub size: u32,
    /// SSA operations in this block.
    pub ops: Vec<SSAOp>,
    /// Phi nodes at the start of this block.
    pub phis: Vec<PhiNode>,
}

/// A phi node in SSA form.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PhiNode {
    /// The destination variable.
    pub dst: SSAVar,
    /// The source variables, one per predecessor.
    pub sources: Vec<(u64, SSAVar)>, // (predecessor addr, variable)
}

/// Location metadata for a source variable use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceSite {
    /// Source from a phi node input.
    Phi {
        phi_idx: usize,
        src_idx: usize,
        pred_addr: u64,
    },
    /// Source from a regular SSA operation input.
    Op { op_idx: usize, src_idx: usize },
}

/// A source variable with its location metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceRef<'a> {
    pub var: &'a SSAVar,
    pub site: SourceSite,
}

/// Location metadata for a destination variable definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefSite {
    /// Destination written by a phi node.
    Phi { phi_idx: usize },
    /// Destination written by a regular operation.
    Op { op_idx: usize },
}

/// A destination variable with its definition site metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefRef<'a> {
    pub var: &'a SSAVar,
    pub site: DefSite,
}

fn decompile_call_boundary_config(arch: Option<&ArchSpec>) -> Option<CallBoundaryConfig> {
    let arch = arch?;
    let lower = arch.name.to_ascii_lowercase();
    let defined_regs: Vec<CallBoundaryDef> = match lower.as_str() {
        "x86-64" | "x86_64" | "x64" | "amd64" => vec![
            CallBoundaryDef {
                name: "rax".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "eax".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "rdi".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "rsi".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "rdx".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "rcx".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "r8".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "r9".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "r10".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "r11".to_string(),
                size: 8,
            },
        ],
        "x86" | "x86-32" | "i386" | "i686" => vec![
            CallBoundaryDef {
                name: "eax".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "ecx".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "edx".to_string(),
                size: 4,
            },
        ],
        "arm" if arch.addr_size == 4 => vec![
            CallBoundaryDef {
                name: "r0".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "r1".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "r2".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "r3".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "r12".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "lr".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "ip".to_string(),
                size: 4,
            },
        ],
        "aarch64" | "arm64" => vec![
            CallBoundaryDef {
                name: "x0".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w0".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x1".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w1".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x2".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w2".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x3".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w3".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x4".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w4".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x5".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w5".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x6".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w6".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x7".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w7".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x8".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w8".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x9".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w9".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x10".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w10".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x11".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w11".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x12".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w12".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x13".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w13".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x14".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w14".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x15".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w15".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x16".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w16".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x17".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w17".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "x30".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "w30".to_string(),
                size: 4,
            },
        ],
        "riscv32" | "rv32" | "rv32gc" => vec![
            CallBoundaryDef {
                name: "ra".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "t0".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "t1".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "t2".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "t3".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "t4".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "t5".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "t6".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "a0".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "a1".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "a2".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "a3".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "a4".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "a5".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "a6".to_string(),
                size: 4,
            },
            CallBoundaryDef {
                name: "a7".to_string(),
                size: 4,
            },
        ],
        "riscv64" | "rv64" | "rv64gc" => vec![
            CallBoundaryDef {
                name: "ra".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "t0".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "t1".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "t2".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "t3".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "t4".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "t5".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "t6".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "a0".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "a1".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "a2".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "a3".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "a4".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "a5".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "a6".to_string(),
                size: 8,
            },
            CallBoundaryDef {
                name: "a7".to_string(),
                size: 8,
            },
        ],
        _ => Vec::new(),
    };

    (!defined_regs.is_empty()).then_some(CallBoundaryConfig { defined_regs })
}

impl SSAFunction {
    /// Build an SSA function from a sequence of r2il blocks.
    pub fn from_blocks(blocks: &[R2ILBlock]) -> Option<Self> {
        Self::from_blocks_with_arch(blocks, None)
    }

    /// Build an SSA function from blocks with constructor-time SCCP enabled.
    pub fn from_blocks_with_arch(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        let mut func = Self::from_blocks_raw(blocks, arch)?;
        // Constructor path applies SCCP by default while keeping legacy SSA consumers stable.
        let cfg = crate::optimize::OptimizationConfig {
            max_iterations: 1,
            enable_sccp: true,
            enable_const_prop: false,
            enable_inst_combine: false,
            enable_copy_prop: false,
            enable_cse: false,
            enable_dce: false,
            preserve_memory_reads: false,
        };
        func.optimize(&cfg);
        Some(func)
    }

    /// Build SSA prepared for decompilation.
    ///
    /// Unlike the generic constructor path, this preserves copy/cast and
    /// address-provenance roots by default and only applies explicitly
    /// configured decompiler-safe cleanup.
    pub fn from_blocks_for_decompile(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
    ) -> Option<Self> {
        let mut func = Self::from_blocks_raw_for_decompile(blocks, arch)?;
        func.prepare_for_decompile(&crate::optimize::DecompilePrepConfig::default());
        if let Some(arch) = arch {
            func.normalize_subregister_sources_for_decompile(arch);
        }
        func.refresh_decompile_prep_facts(arch);
        Some(func)
    }

    /// Build SSA prepared for pattern/type inference.
    ///
    /// This keeps memory reads and address arithmetic intact while still
    /// applying limited whole-function SCCP so layout-sensitive patterns
    /// collapse to a canonical indexed+offset form for downstream consumers.
    pub fn from_blocks_for_patterns(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        let mut func = Self::from_blocks_raw(blocks, arch)?;
        let cfg = crate::optimize::OptimizationConfig {
            max_iterations: 1,
            enable_sccp: true,
            enable_const_prop: false,
            enable_inst_combine: false,
            enable_copy_prop: false,
            enable_cse: false,
            enable_dce: false,
            preserve_memory_reads: true,
        };
        func.optimize(&cfg);
        if let Some(arch) = arch {
            func.normalize_subregister_sources_for_decompile(arch);
        }
        func.refresh_decompile_prep_facts(arch);
        Some(func)
    }

    /// Build SSA for data-reference recovery.
    ///
    /// This keeps memory reads intact and applies a single SCCP pass to
    /// recover cross-block constant targets without paying the extra
    /// subregister normalization and decompile-prep cost.
    pub fn from_blocks_for_data_refs(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
    ) -> Option<Self> {
        let mut func = Self::from_blocks_raw(blocks, arch)?;
        let cfg = crate::optimize::OptimizationConfig {
            max_iterations: 1,
            enable_sccp: true,
            enable_const_prop: false,
            enable_inst_combine: false,
            enable_copy_prop: false,
            enable_cse: false,
            enable_dce: false,
            preserve_memory_reads: true,
        };
        func.optimize(&cfg);
        Some(func)
    }

    /// Build an SSA function from blocks without running optimization passes.
    ///
    /// This performs raw SSA construction:
    /// 1. Build CFG from blocks
    /// 2. Compute dominator tree
    /// 3. Place phi nodes
    /// 4. Rename variables
    pub fn from_blocks_raw(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Self::from_blocks_raw_with_policy(blocks, arch, None)
    }

    /// Build raw SSA prepared with decompiler-safe call boundaries.
    pub fn from_blocks_raw_for_decompile(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
    ) -> Option<Self> {
        let policy = decompile_call_boundary_config(arch);
        Self::from_blocks_raw_with_policy(blocks, arch, policy.as_ref())
    }

    fn from_blocks_raw_with_policy(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        call_boundaries: Option<&CallBoundaryConfig>,
    ) -> Option<Self> {
        if blocks.is_empty() {
            return None;
        }

        // Build CFG
        let cfg = CFG::from_blocks(blocks)?;
        let entry = cfg.entry;

        // Compute dominator tree
        let domtree = DomTree::compute(&cfg);

        let reg_names = arch.map(cached_register_name_map);
        let reg_names_ref = reg_names.as_deref();

        // Collect variable definitions and sizes
        let (defs, var_sizes) = collect_defs_from_cfg_with_names(&cfg, reg_names_ref);

        // Place phi nodes
        let phi_placement = PhiPlacement::compute(&cfg, &domtree, &defs, &var_sizes);

        // Rename variables
        let renamed = if let Some(boundary) = call_boundaries {
            rename_function_with_names_and_call_boundaries(
                &cfg,
                &domtree,
                &phi_placement,
                &var_sizes,
                reg_names_ref,
                Some(boundary),
            )
        } else {
            rename_function_with_names(&cfg, &domtree, &phi_placement, &var_sizes, reg_names_ref)
        };

        // Build SSA blocks
        let mut ssa_blocks = HashMap::new();
        for &addr in &renamed.block_order {
            let cfg_block = cfg.get_block(addr)?;
            let ops = renamed.blocks.get(&addr).cloned().unwrap_or_default();

            // Separate phi nodes from other ops
            let (phi_ops, other_ops): (Vec<_>, Vec<_>) = ops
                .into_iter()
                .partition(|op| matches!(op, SSAOp::Phi { .. }));

            // Convert phi ops to PhiNode structs
            let preds = cfg.predecessors(addr);
            let phis: Vec<PhiNode> = phi_ops
                .into_iter()
                .filter_map(|op| {
                    if let SSAOp::Phi { dst, sources } = op {
                        let phi_sources: Vec<(u64, SSAVar)> = sources
                            .into_iter()
                            .zip(preds.iter())
                            .map(|(var, &pred)| (pred, var))
                            .collect();
                        Some(PhiNode {
                            dst,
                            sources: phi_sources,
                        })
                    } else {
                        None
                    }
                })
                .collect();

            let ssa_block = SSABlock {
                addr,
                size: cfg_block.size,
                ops: other_ops,
                phis,
            };
            ssa_blocks.insert(addr, ssa_block);
        }

        Some(Self {
            name: None,
            entry,
            cfg,
            domtree,
            blocks: ssa_blocks,
            block_order: renamed.block_order,
            decompile_prep_facts: None,
            query_index: RwLock::new(None),
        })
    }

    /// Build raw SSA without architecture metadata.
    pub fn from_blocks_raw_no_arch(blocks: &[R2ILBlock]) -> Option<Self> {
        Self::from_blocks_raw(blocks, None)
    }

    /// Set the function name.
    pub fn with_name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }

    /// Get the entry block.
    pub fn entry_block(&self) -> Option<&SSABlock> {
        self.blocks.get(&self.entry)
    }

    /// Get a block by address.
    pub fn get_block(&self, addr: u64) -> Option<&SSABlock> {
        self.blocks.get(&addr)
    }

    /// Get a mutable block by address.
    pub fn get_block_mut(&mut self, addr: u64) -> Option<&mut SSABlock> {
        self.invalidate_query_index();
        self.decompile_prep_facts = None;
        self.blocks.get_mut(&addr)
    }

    /// Get all blocks in reverse postorder.
    pub fn blocks(&self) -> impl Iterator<Item = &SSABlock> {
        self.block_order
            .iter()
            .filter_map(|&addr| self.blocks.get(&addr))
    }

    /// Get block addresses in reverse postorder.
    pub fn block_addrs(&self) -> &[u64] {
        &self.block_order
    }

    /// Get the number of blocks.
    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    /// Get the CFG.
    pub fn cfg(&self) -> &CFG {
        &self.cfg
    }

    /// Get mutable access to the CFG.
    pub fn cfg_mut(&mut self) -> &mut CFG {
        self.invalidate_query_index();
        self.decompile_prep_facts = None;
        &mut self.cfg
    }

    /// Get the dominator tree.
    pub fn domtree(&self) -> &DomTree {
        &self.domtree
    }

    /// Get predecessors of a block.
    pub fn predecessors(&self, addr: u64) -> Vec<u64> {
        self.cfg.predecessors(addr)
    }

    /// Get successors of a block.
    pub fn successors(&self, addr: u64) -> Vec<u64> {
        self.cfg.successors(addr)
    }

    /// Get switch info for a block, if it's a switch terminator.
    /// Returns Some((cases, default)) where cases is Vec<(value, target)>.
    pub fn switch_info(&self, addr: u64) -> Option<SwitchInfo> {
        let block = self.cfg.get_block(addr)?;
        if let crate::cfg::BlockTerminator::Switch { cases, default } = &block.terminator {
            Some((cases.clone(), *default))
        } else {
            None
        }
    }

    /// Check if block A dominates block B.
    pub fn dominates(&self, a: u64, b: u64) -> bool {
        self.domtree.dominates(a, b)
    }

    /// Summarize CFG features that are useful for conservative decompiler preflight.
    ///
    /// This is intentionally query-only: it reports structure, but does not encode
    /// fallback policy or mutate SSA state.
    pub fn cfg_risk_summary(&self) -> CFGRiskSummary {
        let back_edges = self.collect_back_edges();
        let back_edge_count = back_edges.values().map(Vec::len).sum();
        let loop_count = back_edges.len();
        let mut switch_block_count = 0usize;
        let mut max_switch_cases = 0usize;

        for block in self.blocks() {
            if let Some((cases, default)) = self.switch_info(block.addr) {
                switch_block_count += 1;
                let case_count = cases.len() + usize::from(default.is_some());
                max_switch_cases = max_switch_cases.max(case_count);
            }
        }

        let block_count = self.num_blocks().max(self.cfg.block_addrs().count());

        CFGRiskSummary {
            block_count,
            loop_count,
            back_edge_count,
            switch_block_count,
            max_switch_cases,
        }
    }

    /// Get the immediate dominator of a block.
    pub fn idom(&self, block: u64) -> Option<u64> {
        self.domtree.idom(block)
    }

    /// Get the edge type between two blocks.
    pub fn edge_type(&self, from: u64, to: u64) -> Option<CFGEdge> {
        self.cfg.edge_type(from, to)
    }

    /// Remove a block from SSA and CFG.
    pub fn remove_block(&mut self, addr: u64) {
        self.blocks.remove(&addr);
        self.block_order.retain(|&a| a != addr);
        self.cfg.remove_block(addr);
        self.decompile_prep_facts = None;
        self.invalidate_query_index();
    }

    /// Remove phi sources for a specific predecessor edge.
    pub fn remove_phi_source(&mut self, block_addr: u64, pred_addr: u64) {
        if let Some(block) = self.blocks.get_mut(&block_addr) {
            for phi in &mut block.phis {
                phi.sources.retain(|(pred, _)| *pred != pred_addr);
            }
        }
        self.decompile_prep_facts = None;
        self.invalidate_query_index();
    }

    /// Recompute cached metadata after CFG mutation.
    pub fn refresh_after_cfg_mutation(&mut self) {
        self.blocks
            .retain(|addr, _| self.cfg.get_block(*addr).is_some());
        self.block_order = self.cfg.reverse_postorder();
        self.domtree = DomTree::compute(&self.cfg);
        self.decompile_prep_facts = None;
        self.invalidate_query_index();
    }

    /// Iterate over all SSA operations in the function.
    pub fn all_ops(&self) -> impl Iterator<Item = &SSAOp> {
        self.blocks.values().flat_map(|b| b.ops.iter())
    }

    /// Iterate over all phi nodes in the function.
    pub fn all_phis(&self) -> impl Iterator<Item = &PhiNode> {
        self.blocks.values().flat_map(|b| b.phis.iter())
    }

    /// Get all variables defined in this function.
    pub fn defined_vars(&self) -> Vec<SSAVar> {
        let mut vars = Vec::new();

        // Collect from phi nodes
        for phi in self.all_phis() {
            vars.push(phi.dst.clone());
        }

        // Collect from operations
        for op in self.all_ops() {
            if let Some(dst) = op.dst() {
                vars.push(dst.clone());
            }
        }

        vars
    }

    /// Get all variables used in this function.
    pub fn used_vars(&self) -> Vec<SSAVar> {
        let mut vars = Vec::new();

        // Collect from phi nodes
        for phi in self.all_phis() {
            for (_, var) in &phi.sources {
                vars.push(var.clone());
            }
        }

        // Collect from operations
        for op in self.all_ops() {
            for src in op.sources() {
                vars.push(src.clone());
            }
        }

        vars
    }

    /// Find the definition of a variable.
    ///
    /// Returns the block address and operation index where the variable is defined.
    pub fn find_def(&self, var: &SSAVar) -> Option<(u64, DefLocation)> {
        self.ensure_query_index();
        self.query_index
            .read()
            .expect("SSA query index lock poisoned")
            .as_ref()
            .and_then(|index| index.defs.get(var).copied())
    }

    /// Find all uses of a variable.
    ///
    /// Returns a list of (block address, use location) pairs.
    pub fn find_uses(&self, var: &SSAVar) -> Vec<(u64, UseLocation)> {
        self.ensure_query_index();
        self.query_index
            .read()
            .expect("SSA query index lock poisoned")
            .as_ref()
            .and_then(|index| index.uses.get(var).cloned())
            .unwrap_or_default()
    }

    /// Iterate over all source uses in all blocks.
    pub fn for_each_source<F: FnMut(u64, SourceRef<'_>)>(&self, mut f: F) {
        for block in self.blocks() {
            block.for_each_source(|src| f(block.addr, src));
        }
    }

    /// Iterate over all definitions in all blocks.
    pub fn for_each_def<F: FnMut(u64, DefRef<'_>)>(&self, mut f: F) {
        for block in self.blocks() {
            block.for_each_def(|def| f(block.addr, def));
        }
    }

    /// Compute a backward slice for a sink variable.
    pub fn backward_slice(&self, sink: &SSAVar) -> BackwardSlice {
        backward_slice_from_var(self, sink)
    }

    /// Compute a backward slice starting from an SSA operation.
    pub fn backward_slice_from_op(&self, block_addr: u64, op_idx: usize) -> BackwardSlice {
        backward_slice_from_op(self, SliceOpRef::Op { block_addr, op_idx })
    }

    /// Compute a backward slice starting from a phi node.
    pub fn backward_slice_from_phi(&self, block_addr: u64, phi_idx: usize) -> BackwardSlice {
        backward_slice_from_op(
            self,
            SliceOpRef::Phi {
                block_addr,
                phi_idx,
            },
        )
    }

    /// Run SSA optimizations on this function.
    pub fn optimize(
        &mut self,
        config: &crate::optimize::OptimizationConfig,
    ) -> crate::optimize::OptimizationStats {
        self.decompile_prep_facts = None;
        self.invalidate_query_index();
        crate::optimize::optimize_function(self, config)
    }

    /// Prepare SSA for decompilation using provenance-preserving defaults.
    pub fn prepare_for_decompile(
        &mut self,
        config: &crate::optimize::DecompilePrepConfig,
    ) -> crate::optimize::OptimizationStats {
        self.decompile_prep_facts = None;
        let cfg: crate::optimize::OptimizationConfig = config.into();
        self.optimize(&cfg)
    }

    fn normalize_subregister_sources_for_decompile(&mut self, arch: &ArchSpec) {
        self.decompile_prep_facts = None;
        self.invalidate_query_index();
        let family_info = cached_register_family_info(arch);
        if family_info.name_to_member.is_empty() {
            return;
        }

        let block_in_states = self.compute_decompile_family_in_states(&family_info);

        for &addr in &self.block_order {
            let mut state = block_in_states.get(&addr).cloned().unwrap_or_default();
            let Some(block) = self.blocks.get_mut(&addr) else {
                continue;
            };

            for phi in &block.phis {
                apply_phi_family_effect(phi, &mut state, &family_info);
            }

            for op in &mut block.ops {
                let rewritten = crate::optimize::map_sources_in_op(op, &|src| {
                    rewrite_decompile_family_source(src, &state, &family_info)
                });
                apply_op_family_effect(&rewritten, &mut state, &family_info);
                *op = rewritten;
            }
        }
    }

    /// Snapshot the current decompiler-prep fact view, if available.
    pub fn decompile_prep_facts(&self) -> Option<&DecompilePrepFacts> {
        self.decompile_prep_facts.as_ref()
    }

    /// Refresh the cached decompiler-prep facts for the current SSA state.
    pub fn refresh_decompile_prep_facts(&mut self, arch: Option<&ArchSpec>) {
        self.decompile_prep_facts = Some(self.collect_decompile_prep_facts(arch));
    }

    fn collect_decompile_prep_facts(&self, arch: Option<&ArchSpec>) -> DecompilePrepFacts {
        let cached_family_info = arch.map(cached_register_family_info);
        let empty_family_info = RegisterFamilyInfo::default();
        let family_info = cached_family_info.as_deref().unwrap_or(&empty_family_info);
        let family_in_states = if family_info.name_to_member.is_empty() {
            HashMap::new()
        } else {
            self.compute_decompile_family_in_states(family_info)
        };
        let mut facts = DecompilePrepFacts::default();

        let mut changed = true;
        while changed {
            changed = false;
            for &addr in &self.block_order {
                let mut family_state = family_in_states.get(&addr).cloned().unwrap_or_default();
                let Some(block) = self.get_block(addr) else {
                    continue;
                };

                for phi in &block.phis {
                    let source_roots = phi
                        .sources
                        .iter()
                        .map(|(_, src)| {
                            resolve_value_root(
                                src,
                                &facts.canonical_value_roots,
                                &family_state,
                                family_info,
                            )
                        })
                        .collect::<Vec<_>>();
                    if let Some(root) = common_root(&source_roots) {
                        changed |= insert_canonical_root(
                            &mut facts.canonical_value_roots,
                            phi.dst.clone(),
                            root,
                        );
                    }

                    if let Some(root) = common_stack_root(
                        &phi.sources,
                        &facts.canonical_value_roots,
                        &facts.stack_address_roots,
                        &family_state,
                        family_info,
                    ) {
                        changed |= insert_stack_root(
                            &mut facts.stack_address_roots,
                            phi.dst.clone(),
                            root,
                        );
                    }

                    apply_phi_family_effect(phi, &mut family_state, family_info);
                }

                for op in &block.ops {
                    match op {
                        SSAOp::Copy { dst, src }
                        | SSAOp::Cast { dst, src }
                        | SSAOp::New { dst, src } => {
                            let src_root = resolve_value_root(
                                src,
                                &facts.canonical_value_roots,
                                &family_state,
                                family_info,
                            );
                            changed |= insert_canonical_root(
                                &mut facts.canonical_value_roots,
                                dst.clone(),
                                src_root.clone(),
                            );
                            if let Some(stack_root) = resolve_stack_root(
                                src,
                                &facts.canonical_value_roots,
                                &facts.stack_address_roots,
                                &family_state,
                                family_info,
                            ) {
                                changed |= insert_stack_root(
                                    &mut facts.stack_address_roots,
                                    dst.clone(),
                                    normalize_copied_stack_root_for_dst(dst, stack_root),
                                );
                            }
                        }
                        SSAOp::Trunc { dst, src } | SSAOp::Subpiece { dst, src, .. } => {
                            let src_root = resolve_value_root(
                                src,
                                &facts.canonical_value_roots,
                                &family_state,
                                family_info,
                            );
                            let adapted = adapt_family_root(&src_root, dst.size)
                                .unwrap_or_else(|| src_root.clone());
                            changed |= insert_canonical_root(
                                &mut facts.canonical_value_roots,
                                dst.clone(),
                                adapted,
                            );
                        }
                        SSAOp::IntAdd { dst, a, b } => {
                            if let Some(root) = stack_address_root_from_add(
                                a,
                                b,
                                &facts.canonical_value_roots,
                                &facts.stack_address_roots,
                                &family_state,
                                family_info,
                            ) {
                                changed |= insert_stack_root(
                                    &mut facts.stack_address_roots,
                                    dst.clone(),
                                    root,
                                );
                            }
                        }
                        SSAOp::IntSub { dst, a, b } => {
                            if let Some(root) = stack_address_root_from_sub(
                                a,
                                b,
                                &facts.canonical_value_roots,
                                &facts.stack_address_roots,
                                &family_state,
                                family_info,
                            ) {
                                changed |= insert_stack_root(
                                    &mut facts.stack_address_roots,
                                    dst.clone(),
                                    root,
                                );
                            }
                        }
                        SSAOp::IntZExt { .. } | SSAOp::IntSExt { .. } => {}
                        _ => {}
                    }

                    if let Some(dst) = op.dst() {
                        apply_op_family_effect(op, &mut family_state, family_info);
                        changed |= ensure_value_root_identity(
                            &mut facts.canonical_value_roots,
                            dst.clone(),
                        );
                    }
                }
            }
        }

        facts
    }

    fn compute_decompile_family_in_states(
        &self,
        family_info: &RegisterFamilyInfo,
    ) -> HashMap<u64, FamilyRootState> {
        let mut in_states: HashMap<u64, FamilyRootState> = HashMap::new();
        let mut out_states: HashMap<u64, FamilyRootState> = HashMap::new();

        loop {
            let mut changed = false;

            for &addr in &self.block_order {
                let preds = self.predecessors(addr);
                let next_in = meet_family_states(&preds, &out_states);
                let next_out = self.transfer_family_state_for_block(addr, &next_in, family_info);

                if in_states.get(&addr) != Some(&next_in) {
                    in_states.insert(addr, next_in.clone());
                    changed = true;
                }
                if out_states.get(&addr) != Some(&next_out) {
                    out_states.insert(addr, next_out);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        in_states
    }

    fn transfer_family_state_for_block(
        &self,
        addr: u64,
        input: &FamilyRootState,
        family_info: &RegisterFamilyInfo,
    ) -> FamilyRootState {
        let mut state = input.clone();
        let Some(block) = self.get_block(addr) else {
            return state;
        };

        for phi in &block.phis {
            apply_phi_family_effect(phi, &mut state, family_info);
        }

        for op in &block.ops {
            let rewritten = crate::optimize::map_sources_in_op(op, &|src| {
                rewrite_decompile_family_source(src, &state, family_info)
            });
            apply_op_family_effect(&rewritten, &mut state, family_info);
        }

        state
    }

    /// Get the switch-selector SSA value that drives a switch block, if recoverable.
    pub fn infer_switch_selector_var(&self, block_addr: u64) -> Option<SSAVar> {
        let block = self.get_block(block_addr)?;
        let target = block.ops.iter().rev().find_map(|op| match op {
            SSAOp::BranchInd { target } => Some(target),
            _ => None,
        })?;
        self.infer_switch_selector_var_from_value(target, 0)
    }

    fn ensure_query_index(&self) {
        if self
            .query_index
            .read()
            .expect("SSA query index lock poisoned")
            .is_some()
        {
            return;
        }
        let index = SsaQueryIndex::build(self);
        *self
            .query_index
            .write()
            .expect("SSA query index lock poisoned") = Some(index);
    }

    fn invalidate_query_index(&self) {
        *self
            .query_index
            .write()
            .expect("SSA query index lock poisoned") = None;
    }

    fn infer_switch_selector_var_from_value(&self, var: &SSAVar, depth: u32) -> Option<SSAVar> {
        if depth > 16 {
            return None;
        }

        let (block_addr, DefLocation::Op(op_idx)) = self.find_def(var)? else {
            return None;
        };
        let block = self.get_block(block_addr)?;
        let op = block.ops.get(op_idx)?;
        match op {
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Subpiece { src, .. } => {
                self.infer_switch_selector_var_from_value(src, depth + 1)
            }
            SSAOp::Load { addr, .. } => {
                if self.is_stack_slot_address_var(addr, depth + 1) {
                    Some(var.clone())
                } else {
                    self.infer_switch_selector_var_from_address(addr, depth + 1)
                }
            }
            SSAOp::IntAdd { a, b, .. } | SSAOp::IntSub { a, b, .. } => {
                self.infer_switch_selector_var_from_sum(a, b, depth + 1)
            }
            SSAOp::IntMult { a, b, .. } => {
                self.infer_switch_selector_var_from_scaled(a, b, depth + 1)
            }
            _ => None,
        }
    }

    fn infer_switch_selector_var_from_address(&self, addr: &SSAVar, depth: u32) -> Option<SSAVar> {
        if depth > 16 {
            return None;
        }

        let (block_addr, DefLocation::Op(op_idx)) = self.find_def(addr)? else {
            return None;
        };
        let block = self.get_block(block_addr)?;
        let op = block.ops.get(op_idx)?;
        match op {
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Subpiece { src, .. } => {
                self.infer_switch_selector_var_from_address(src, depth + 1)
            }
            SSAOp::IntAdd { a, b, .. } | SSAOp::IntSub { a, b, .. } => {
                self.infer_switch_selector_var_from_sum(a, b, depth + 1)
            }
            SSAOp::IntMult { a, b, .. } => {
                self.infer_switch_selector_var_from_scaled(a, b, depth + 1)
            }
            _ => None,
        }
    }

    fn infer_switch_selector_var_from_sum(
        &self,
        a: &SSAVar,
        b: &SSAVar,
        depth: u32,
    ) -> Option<SSAVar> {
        if Self::is_constish_switch_value(a) {
            return self.infer_switch_selector_var_from_value(b, depth);
        }
        if Self::is_constish_switch_value(b) {
            return self.infer_switch_selector_var_from_value(a, depth);
        }
        self.infer_switch_selector_var_from_scaled(a, b, depth)
            .or_else(|| self.infer_switch_selector_var_from_scaled(b, a, depth))
    }

    fn infer_switch_selector_var_from_scaled(
        &self,
        a: &SSAVar,
        b: &SSAVar,
        depth: u32,
    ) -> Option<SSAVar> {
        if Self::is_constish_switch_value(a) {
            return self.infer_switch_selector_var_from_value(b, depth);
        }
        if Self::is_constish_switch_value(b) {
            return self.infer_switch_selector_var_from_value(a, depth);
        }
        None
    }

    fn is_stack_slot_address_var(&self, var: &SSAVar, depth: u32) -> bool {
        if depth > 16 {
            return false;
        }

        let lower = var.name.to_ascii_lowercase();
        let base = lower.split('_').next().unwrap_or(lower.as_str());
        if matches!(base, "rbp" | "rsp" | "ebp" | "esp" | "bp" | "sp") {
            return true;
        }

        let Some((block_addr, DefLocation::Op(op_idx))) = self.find_def(var) else {
            return false;
        };
        let Some(block) = self.get_block(block_addr) else {
            return false;
        };
        let Some(op) = block.ops.get(op_idx) else {
            return false;
        };
        match op {
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Subpiece { src, .. } => self.is_stack_slot_address_var(src, depth + 1),
            SSAOp::IntAdd { a, b, .. } | SSAOp::IntSub { a, b, .. } => {
                (self.is_stack_slot_address_var(a, depth + 1) && Self::is_constish_switch_value(b))
                    || (self.is_stack_slot_address_var(b, depth + 1)
                        && Self::is_constish_switch_value(a))
            }
            _ => false,
        }
    }

    fn is_constish_switch_value(var: &SSAVar) -> bool {
        var.is_const() || var.name.starts_with("ram:")
    }

    /// Print the function in a human-readable format.
    pub fn dump(&self) -> String {
        let mut out = String::new();

        out.push_str(&format!(
            "Function: {}\n",
            self.name.as_deref().unwrap_or("<unnamed>")
        ));
        out.push_str(&format!("Entry: 0x{:x}\n", self.entry));
        out.push_str(&format!("Blocks: {}\n\n", self.num_blocks()));

        for &addr in &self.block_order {
            if let Some(block) = self.blocks.get(&addr) {
                out.push_str(&format!("Block 0x{:x}:\n", addr));

                // Predecessors
                let preds = self.predecessors(addr);
                if !preds.is_empty() {
                    out.push_str(&format!(
                        "  preds: {}\n",
                        preds
                            .iter()
                            .map(|p| format!("0x{:x}", p))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }

                // Phi nodes
                for phi in &block.phis {
                    let sources: Vec<String> = phi
                        .sources
                        .iter()
                        .map(|(pred, var)| format!("[0x{:x}]: {}", pred, var))
                        .collect();
                    out.push_str(&format!("  {} = phi({})\n", phi.dst, sources.join(", ")));
                }

                // Operations
                for op in &block.ops {
                    out.push_str(&format!("  {:?}\n", op));
                }

                // Successors
                let succs = self.successors(addr);
                if !succs.is_empty() {
                    out.push_str(&format!(
                        "  succs: {}\n",
                        succs
                            .iter()
                            .map(|s| format!("0x{:x}", s))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }

                out.push('\n');
            }
        }

        out
    }

    fn collect_back_edges(&self) -> HashMap<u64, Vec<u64>> {
        let mut visited = HashSet::new();
        let mut in_stack = HashSet::new();
        let mut back_edges = HashMap::new();
        self.dfs_back_edges(self.entry, &mut visited, &mut in_stack, &mut back_edges);
        back_edges
    }

    fn dfs_back_edges(
        &self,
        block: u64,
        visited: &mut HashSet<u64>,
        in_stack: &mut HashSet<u64>,
        back_edges: &mut HashMap<u64, Vec<u64>>,
    ) {
        if visited.contains(&block) {
            return;
        }
        visited.insert(block);
        in_stack.insert(block);

        for succ in self.successors(block) {
            if in_stack.contains(&succ) {
                back_edges.entry(succ).or_default().push(block);
            } else {
                self.dfs_back_edges(succ, visited, in_stack, back_edges);
            }
        }

        in_stack.remove(&block);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RegisterFamilySlot {
    family_id: usize,
    width: u32,
}

#[derive(Debug, Clone, Copy)]
struct RegisterFamilyMember {
    family_id: usize,
    width: u32,
}

#[derive(Debug, Clone, Default)]
struct RegisterFamilyInfo {
    name_to_member: HashMap<String, RegisterFamilyMember>,
    family_widths: HashMap<usize, Vec<u32>>,
}

type FamilyRootState = HashMap<RegisterFamilySlot, SSAVar>;

fn register_family_info_cache() -> &'static RwLock<HashMap<ArchCacheTag, Arc<RegisterFamilyInfo>>> {
    static CACHE: OnceLock<RwLock<HashMap<ArchCacheTag, Arc<RegisterFamilyInfo>>>> =
        OnceLock::new();
    CACHE.get_or_init(|| RwLock::new(HashMap::new()))
}

fn cached_register_family_info(arch: &ArchSpec) -> Arc<RegisterFamilyInfo> {
    let cache_tag = ArchCacheTag::from_arch(arch);

    if let Some(cached) = register_family_info_cache()
        .read()
        .expect("register family cache read lock poisoned")
        .get(&cache_tag)
        .cloned()
    {
        return cached;
    }

    let info = Arc::new(RegisterFamilyInfo::from_arch(arch));
    register_family_info_cache()
        .write()
        .expect("register family cache write lock poisoned")
        .insert(cache_tag, info.clone());
    info
}

impl RegisterFamilyInfo {
    fn from_arch(arch: &ArchSpec) -> Self {
        #[derive(Clone)]
        struct RangeReg {
            name: String,
            offset: u64,
            size: u32,
        }

        fn find(parents: &mut [usize], idx: usize) -> usize {
            if parents[idx] != idx {
                let root = find(parents, parents[idx]);
                parents[idx] = root;
            }
            parents[idx]
        }

        fn union(parents: &mut [usize], a: usize, b: usize) {
            let root_a = find(parents, a);
            let root_b = find(parents, b);
            if root_a != root_b {
                parents[root_b] = root_a;
            }
        }

        fn range_end(reg: &RangeReg) -> u64 {
            reg.offset.saturating_add(reg.size as u64)
        }

        let regs: Vec<RangeReg> = arch
            .registers
            .iter()
            .map(|reg| RangeReg {
                name: reg.name.to_lowercase(),
                offset: reg.offset,
                size: reg.size,
            })
            .collect();

        if regs.is_empty() {
            return Self::default();
        }

        let mut parents: Vec<usize> = (0..regs.len()).collect();
        let mut sorted_indices: Vec<usize> = (0..regs.len()).collect();
        sorted_indices.sort_unstable_by_key(|&idx| (regs[idx].offset, range_end(&regs[idx])));

        let mut cluster_root = sorted_indices[0];
        let mut cluster_end = range_end(&regs[cluster_root]);
        for &idx in sorted_indices.iter().skip(1) {
            let reg = &regs[idx];
            if reg.offset < cluster_end {
                union(&mut parents, cluster_root, idx);
                cluster_end = cluster_end.max(range_end(reg));
            } else {
                cluster_root = idx;
                cluster_end = range_end(reg);
            }
        }

        let mut root_to_family = HashMap::new();
        let mut next_family_id = 0usize;
        let mut name_to_member = HashMap::new();
        let mut family_width_sets: HashMap<usize, HashSet<u32>> = HashMap::new();

        for (idx, reg) in regs.iter().enumerate() {
            let root = find(&mut parents, idx);
            let family_id = *root_to_family.entry(root).or_insert_with(|| {
                let id = next_family_id;
                next_family_id += 1;
                id
            });
            name_to_member.insert(
                reg.name.clone(),
                RegisterFamilyMember {
                    family_id,
                    width: reg.size,
                },
            );
            family_width_sets
                .entry(family_id)
                .or_default()
                .insert(reg.size);
        }

        let family_widths = family_width_sets
            .into_iter()
            .map(|(family_id, mut widths)| {
                let mut widths: Vec<u32> = widths.drain().collect();
                widths.sort_unstable();
                (family_id, widths)
            })
            .collect();

        Self {
            name_to_member,
            family_widths,
        }
    }

    fn member_for(&self, var: &SSAVar) -> Option<RegisterFamilyMember> {
        if let Some(member) = self.name_to_member.get(var.name.as_str()) {
            return Some(*member);
        }
        if var.name.bytes().any(|byte| byte.is_ascii_uppercase()) {
            return self
                .name_to_member
                .get(var.name.to_ascii_lowercase().as_str())
                .copied();
        }
        None
    }
}

fn meet_family_states(
    preds: &[u64],
    out_states: &HashMap<u64, FamilyRootState>,
) -> FamilyRootState {
    let mut pred_iter = preds.iter();
    let Some(first_pred) = pred_iter.next() else {
        return HashMap::new();
    };
    let Some(first_state) = out_states.get(first_pred).cloned() else {
        return HashMap::new();
    };

    let mut merged = first_state;
    for pred in pred_iter {
        let Some(state) = out_states.get(pred) else {
            return HashMap::new();
        };
        merged.retain(|slot, root| state.get(slot) == Some(root));
    }
    merged
}

fn apply_phi_family_effect(
    phi: &PhiNode,
    state: &mut FamilyRootState,
    family_info: &RegisterFamilyInfo,
) {
    let Some(member) = family_info.member_for(&phi.dst) else {
        return;
    };
    kill_family_roots(state, member.family_id);
    state.insert(
        RegisterFamilySlot {
            family_id: member.family_id,
            width: member.width,
        },
        phi.dst.clone(),
    );
}

fn apply_op_family_effect(
    op: &SSAOp,
    state: &mut FamilyRootState,
    family_info: &RegisterFamilyInfo,
) {
    let Some(dst) = op.dst() else {
        return;
    };
    let Some(member) = family_info.member_for(dst) else {
        return;
    };

    kill_family_roots(state, member.family_id);

    let exact_slot = RegisterFamilySlot {
        family_id: member.family_id,
        width: member.width,
    };

    match op {
        SSAOp::Copy { src, .. } | SSAOp::Cast { src, .. } | SSAOp::New { src, .. } => {
            if let Some(root) = adapt_family_root(src, member.width) {
                state.insert(exact_slot, root.clone());
                seed_narrow_family_roots(state, family_info, member.family_id, member.width, &root);
            } else {
                state.insert(exact_slot, dst.clone());
                seed_narrow_family_roots(state, family_info, member.family_id, member.width, dst);
            }
        }
        SSAOp::IntZExt { src, .. } | SSAOp::IntSExt { src, .. } => {
            state.insert(exact_slot, dst.clone());
            seed_narrow_family_roots(state, family_info, member.family_id, member.width, dst);
            if let Some(root) = adapt_family_root(src, src.size) {
                state.insert(
                    RegisterFamilySlot {
                        family_id: member.family_id,
                        width: src.size,
                    },
                    root,
                );
            }
        }
        SSAOp::Trunc { src, .. } | SSAOp::Subpiece { src, .. } => {
            if let Some(root) = adapt_family_root(src, member.width) {
                state.insert(exact_slot, root);
            } else {
                state.insert(exact_slot, dst.clone());
            }
        }
        _ => {
            state.insert(exact_slot, dst.clone());
        }
    }
}

fn rewrite_decompile_family_source(
    src: &SSAVar,
    state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> SSAVar {
    let Some(member) = family_info.member_for(src) else {
        return src.clone();
    };
    if src.version != 0
        && family_info
            .family_widths
            .get(&member.family_id)
            .and_then(|widths| widths.iter().copied().max())
            .is_none_or(|max_width| member.width >= max_width)
    {
        return src.clone();
    }
    let slot = RegisterFamilySlot {
        family_id: member.family_id,
        width: src.size,
    };
    let Some(root) = state.get(&slot) else {
        return src.clone();
    };
    let Some(adapted) = adapt_family_root(root, src.size) else {
        return src.clone();
    };
    if adapted == *src {
        src.clone()
    } else {
        adapted
    }
}

fn adapt_family_root(root: &SSAVar, width: u32) -> Option<SSAVar> {
    if root.size == width {
        return Some(root.clone());
    }
    if root.size > width && !root.is_const() {
        return Some(SSAVar::new(root.name.clone(), root.version, width));
    }
    if !root.is_const() {
        return None;
    }
    const_value(root).map(|value| SSAVar::constant(mask_const_to_width(value, width), width))
}

fn seed_narrow_family_roots(
    state: &mut FamilyRootState,
    family_info: &RegisterFamilyInfo,
    family_id: usize,
    written_width: u32,
    root: &SSAVar,
) {
    let Some(widths) = family_info.family_widths.get(&family_id) else {
        return;
    };

    for &width in widths {
        if width > written_width {
            continue;
        }
        let Some(adapted) = adapt_family_root(root, width) else {
            continue;
        };
        state.insert(RegisterFamilySlot { family_id, width }, adapted);
    }
}

fn kill_family_roots(state: &mut FamilyRootState, family_id: usize) {
    state.retain(|slot, _| slot.family_id != family_id);
}

fn const_value(var: &SSAVar) -> Option<u64> {
    if !var.is_const() {
        return None;
    }
    let hex = var.name.strip_prefix("const:")?;
    u64::from_str_radix(hex, 16).ok()
}

fn mask_const_to_width(value: u64, width: u32) -> u64 {
    let bits = width.saturating_mul(8);
    if bits >= 64 {
        value
    } else if bits == 0 {
        0
    } else {
        value & ((1u64 << bits) - 1)
    }
}

fn canonicalize_value_root(root: &SSAVar, roots: &BTreeMap<SSAVar, SSAVar>) -> SSAVar {
    let mut current = root.clone();
    let mut seen = HashSet::new();

    loop {
        let Some(next) = roots.get(&current) else {
            break;
        };
        if *next == current || !seen.insert(current.clone()) {
            break;
        }
        current = next.clone();
    }

    current
}

fn ensure_value_root_identity(roots: &mut BTreeMap<SSAVar, SSAVar>, var: SSAVar) -> bool {
    if roots.contains_key(&var) {
        return false;
    }
    roots.insert(var.clone(), var);
    true
}

fn insert_canonical_root(roots: &mut BTreeMap<SSAVar, SSAVar>, dst: SSAVar, root: SSAVar) -> bool {
    let root = canonicalize_value_root(&root, roots);
    let changed = !matches!(roots.get(&dst), Some(existing) if *existing == root);
    roots.insert(dst.clone(), root.clone());
    roots.entry(root.clone()).or_insert(root);
    changed
}

fn common_root(values: &[SSAVar]) -> Option<SSAVar> {
    let first = values.first()?.clone();
    if values.iter().all(|value| *value == first) {
        Some(first)
    } else {
        None
    }
}

fn stack_base_root_for_name(name: &str) -> Option<StackAddressRoot> {
    let lower = name.trim().to_ascii_lowercase();
    let base = match lower.as_str() {
        "sp" | "rsp" | "esp" | "wsp" => StackAddressBase::StackPointer,
        "fp" | "bp" | "rbp" | "ebp" | "x29" | "w29" | "s0" => StackAddressBase::FramePointer,
        _ => return None,
    };
    Some(StackAddressRoot { base, offset: 0 })
}

fn resolve_value_root(
    var: &SSAVar,
    roots: &BTreeMap<SSAVar, SSAVar>,
    family_state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> SSAVar {
    let canonical = canonicalize_value_root(var, roots);
    if canonical != *var {
        return canonical;
    }

    if var.version != 0 {
        return var.clone();
    }

    let Some(member) = family_info.member_for(var) else {
        return var.clone();
    };
    let slot = RegisterFamilySlot {
        family_id: member.family_id,
        width: var.size,
    };
    let Some(root) = family_state.get(&slot) else {
        return var.clone();
    };
    adapt_family_root(root, var.size)
        .map(|root| canonicalize_value_root(&root, roots))
        .unwrap_or_else(|| var.clone())
}

fn resolve_stack_root(
    var: &SSAVar,
    roots: &BTreeMap<SSAVar, SSAVar>,
    stack_roots: &BTreeMap<SSAVar, StackAddressRoot>,
    family_state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> Option<StackAddressRoot> {
    let resolved = resolve_value_root(var, roots, family_state, family_info);
    stack_roots
        .get(var)
        .copied()
        .or_else(|| stack_roots.get(&resolved).copied())
        .or_else(|| stack_base_root_for_name(&resolved.name))
}

fn normalize_copied_stack_root_for_dst(dst: &SSAVar, root: StackAddressRoot) -> StackAddressRoot {
    match stack_base_root_for_name(&dst.name) {
        Some(StackAddressRoot {
            base: StackAddressBase::FramePointer,
            ..
        }) => StackAddressRoot {
            base: StackAddressBase::FramePointer,
            offset: 0,
        },
        _ => root,
    }
}

fn common_stack_root(
    sources: &[(u64, SSAVar)],
    roots: &BTreeMap<SSAVar, SSAVar>,
    stack_roots: &BTreeMap<SSAVar, StackAddressRoot>,
    family_state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> Option<StackAddressRoot> {
    let mut iter = sources.iter();
    let (_, first_src) = iter.next()?;
    let first = resolve_stack_root(first_src, roots, stack_roots, family_state, family_info)?;
    if iter.all(|(_, src)| {
        resolve_stack_root(src, roots, stack_roots, family_state, family_info) == Some(first)
    }) {
        Some(first)
    } else {
        None
    }
}

fn stack_root_from_operand(
    var: &SSAVar,
    roots: &BTreeMap<SSAVar, SSAVar>,
    stack_roots: &BTreeMap<SSAVar, StackAddressRoot>,
    family_state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> Option<StackAddressRoot> {
    resolve_stack_root(var, roots, stack_roots, family_state, family_info)
}

fn stack_address_root_from_add(
    a: &SSAVar,
    b: &SSAVar,
    roots: &BTreeMap<SSAVar, SSAVar>,
    stack_roots: &BTreeMap<SSAVar, StackAddressRoot>,
    family_state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> Option<StackAddressRoot> {
    if let (Some(base), Some(delta)) = (
        stack_root_from_operand(a, roots, stack_roots, family_state, family_info),
        const_value(b).map(|value| value as i64),
    ) {
        return Some(StackAddressRoot {
            base: base.base,
            offset: base.offset.saturating_add(delta),
        });
    }
    if let (Some(base), Some(delta)) = (
        stack_root_from_operand(b, roots, stack_roots, family_state, family_info),
        const_value(a).map(|value| value as i64),
    ) {
        return Some(StackAddressRoot {
            base: base.base,
            offset: base.offset.saturating_add(delta),
        });
    }
    None
}

fn stack_address_root_from_sub(
    a: &SSAVar,
    b: &SSAVar,
    roots: &BTreeMap<SSAVar, SSAVar>,
    stack_roots: &BTreeMap<SSAVar, StackAddressRoot>,
    family_state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> Option<StackAddressRoot> {
    let base = stack_root_from_operand(a, roots, stack_roots, family_state, family_info)?;
    let delta = const_value(b).map(|value| value as i64)?;
    Some(StackAddressRoot {
        base: base.base,
        offset: base.offset.saturating_sub(delta),
    })
}

fn insert_stack_root(
    stack_roots: &mut BTreeMap<SSAVar, StackAddressRoot>,
    dst: SSAVar,
    root: StackAddressRoot,
) -> bool {
    match stack_roots.get(&dst) {
        Some(existing) if *existing == root => false,
        _ => {
            stack_roots.insert(dst, root);
            true
        }
    }
}

/// Location of a variable definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefLocation {
    /// Defined by a phi node at the given index.
    Phi(usize),
    /// Defined by an operation at the given index.
    Op(usize),
}

/// Location of a variable use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseLocation {
    /// Used in a phi node.
    Phi { phi_idx: usize, src_idx: usize },
    /// Used in an operation.
    Op { op_idx: usize, src_idx: usize },
}

impl SsaQueryIndex {
    fn build(function: &SSAFunction) -> Self {
        let mut defs = HashMap::new();
        let mut uses: HashMap<SSAVar, Vec<(u64, UseLocation)>> = HashMap::new();

        for block in function.blocks() {
            for (phi_idx, phi) in block.phis.iter().enumerate() {
                defs.insert(phi.dst.clone(), (block.addr, DefLocation::Phi(phi_idx)));
                for (src_idx, (_, src)) in phi.sources.iter().enumerate() {
                    uses.entry(src.clone())
                        .or_default()
                        .push((block.addr, UseLocation::Phi { phi_idx, src_idx }));
                }
            }

            for (op_idx, op) in block.ops.iter().enumerate() {
                if let Some(dst) = op.dst() {
                    defs.insert(dst.clone(), (block.addr, DefLocation::Op(op_idx)));
                }
                for (src_idx, src) in op.sources().into_iter().enumerate() {
                    uses.entry(src.clone())
                        .or_default()
                        .push((block.addr, UseLocation::Op { op_idx, src_idx }));
                }
            }
        }

        Self { defs, uses }
    }
}

impl SSABlock {
    /// Visit all phi source variables in deterministic index order.
    pub fn for_each_phi_source<F: FnMut(SourceRef<'_>)>(&self, mut f: F) {
        for (phi_idx, phi) in self.phis.iter().enumerate() {
            for (src_idx, (pred_addr, src)) in phi.sources.iter().enumerate() {
                f(SourceRef {
                    var: src,
                    site: SourceSite::Phi {
                        phi_idx,
                        src_idx,
                        pred_addr: *pred_addr,
                    },
                });
            }
        }
    }

    /// Visit all operation source variables in deterministic index order.
    pub fn for_each_op_source<F: FnMut(SourceRef<'_>)>(&self, mut f: F) {
        for (op_idx, op) in self.ops.iter().enumerate() {
            let mut src_idx = 0usize;
            op.for_each_source(|src| {
                f(SourceRef {
                    var: src,
                    site: SourceSite::Op { op_idx, src_idx },
                });
                src_idx += 1;
            });
        }
    }

    /// Visit all source variables (phis first, then ops) in index order.
    pub fn for_each_source<F: FnMut(SourceRef<'_>)>(&self, mut f: F) {
        self.for_each_phi_source(&mut f);
        self.for_each_op_source(f);
    }

    /// Visit all destination definitions (phis first, then ops) in index order.
    pub fn for_each_def<F: FnMut(DefRef<'_>)>(&self, mut f: F) {
        for (phi_idx, phi) in self.phis.iter().enumerate() {
            f(DefRef {
                var: &phi.dst,
                site: DefSite::Phi { phi_idx },
            });
        }

        for (op_idx, op) in self.ops.iter().enumerate() {
            if let Some(dst) = op.dst() {
                f(DefRef {
                    var: dst,
                    site: DefSite::Op { op_idx },
                });
            }
        }
    }

    /// Get all operations including phi nodes (as SSAOp::Phi).
    pub fn all_ops(&self) -> impl Iterator<Item = SSAOp> + '_ {
        let phi_ops = self.phis.iter().map(|phi| SSAOp::Phi {
            dst: phi.dst.clone(),
            sources: phi.sources.iter().map(|(_, v)| v.clone()).collect(),
        });
        phi_ops.chain(self.ops.iter().cloned())
    }

    /// Check if this block has any phi nodes.
    pub fn has_phis(&self) -> bool {
        !self.phis.is_empty()
    }

    /// Get the number of phi nodes.
    pub fn num_phis(&self) -> usize {
        self.phis.len()
    }

    /// Get the number of operations (excluding phi nodes).
    pub fn num_ops(&self) -> usize {
        self.ops.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{R2ILOp, RegisterDef, SpaceId, SwitchCase, SwitchInfo as R2ILSwitchInfo, Varnode};

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

    fn make_arm64_alias_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        arch.add_register(RegisterDef::new("w0", 0x00, 4));
        arch.add_register(RegisterDef::new("x8", 0x80, 8));
        arch.add_register(RegisterDef::new("w8", 0x80, 4));
        arch.add_register(RegisterDef::new("x9", 0x88, 8));
        arch.add_register(RegisterDef::new("w9", 0x88, 4));
        arch
    }

    fn make_x86_64_prep_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rbx", 8, 8));
        arch.add_register(RegisterDef::new("rsp", 16, 8));
        arch.add_register(RegisterDef::new("rbp", 24, 8));
        arch
    }

    #[test]
    fn test_ssa_function_linear() {
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

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).unwrap();
        assert_eq!(func.entry, 0x1000);
        assert_eq!(func.num_blocks(), 2);

        // Check that entry block has the copy operations
        let entry = func.entry_block().unwrap();
        assert_eq!(entry.num_ops(), 2);
        assert!(!entry.has_phis());
    }

    #[test]
    fn prepared_function_ssa_tracks_mode_and_keeps_named_blocks() {
        let arch = make_x86_64_prep_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(1, 8),
                },
                R2ILOp::Return {
                    target: make_reg(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let prepared = SsaArtifact::for_decompile(&blocks, Some(&arch))
            .expect("prepared SSA should build")
            .with_name("prepared_demo");

        assert_eq!(prepared.mode(), FunctionPrepareMode::Decompile);
        assert_eq!(prepared.name.as_deref(), Some("prepared_demo"));
        assert!(
            prepared.decompile_prep_facts().is_some(),
            "decompile preparation should retain prep facts"
        );

        let local_blocks = prepared.local_ssa_blocks();
        assert_eq!(local_blocks.len(), 1);
        assert_eq!(local_blocks[0].addr, 0x1000);
        assert_eq!(
            local_blocks[0].ops,
            prepared.blocks().next().expect("entry block").ops
        );

        let symbolic = SsaArtifact::for_symbolic(&blocks, Some(&arch))
            .expect("symbolic prepared SSA should build");
        assert_eq!(symbolic.mode(), FunctionPrepareMode::Symbolic);
        assert!(
            symbolic.decompile_prep_facts().is_some(),
            "symbolic preparation should retain canonical prep facts for shared consumers"
        );
    }

    #[test]
    fn prepared_function_ssa_collects_object_memory_and_predicate_facts() {
        let arch = make_x86_64_prep_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1100,
                size: 4,
                ops: vec![
                    R2ILOp::IntSub {
                        dst: Varnode {
                            space: SpaceId::Unique,
                            offset: 0x10,
                            size: 8,
                            meta: None,
                        },
                        a: make_reg(24, 8),
                        b: make_const(0x20, 8),
                    },
                    R2ILOp::Load {
                        dst: make_reg(0, 8),
                        space: SpaceId::Ram,
                        addr: Varnode {
                            space: SpaceId::Unique,
                            offset: 0x10,
                            size: 8,
                            meta: None,
                        },
                    },
                    R2ILOp::Store {
                        space: SpaceId::Ram,
                        addr: make_const(0x4040, 8),
                        val: make_reg(0, 8),
                    },
                    R2ILOp::IntEqual {
                        dst: make_reg(8, 1),
                        a: make_reg(0, 8),
                        b: make_const(0, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1108, 8),
                        cond: make_reg(8, 1),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1104,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1108,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared =
            SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA should build");

        assert!(
            prepared
                .objects()
                .stack_objects
                .contains_key(&StackAddressRoot {
                    base: StackAddressBase::FramePointer,
                    offset: -32,
                }),
            "stack-root-derived stack object should be materialized"
        );
        assert!(
            prepared
                .objects()
                .global_objects
                .iter()
                .any(|(key, _)| key.address == 0x4040),
            "constant RAM address should seed a global object"
        );

        let entry = prepared.get_block(0x1100).expect("entry block");
        let load_ref = SliceOpRef::Op {
            block_addr: 0x1100,
            op_idx: 1,
        };
        let store_ref = SliceOpRef::Op {
            block_addr: 0x1100,
            op_idx: 2,
        };
        let load_inst = prepared
            .graph()
            .inst_id_for_op_site(load_ref.block_addr(), 1)
            .expect("load inst");
        let store_inst = prepared
            .graph()
            .inst_id_for_op_site(store_ref.block_addr(), 2)
            .expect("store inst");
        assert!(
            prepared.memory().uses_by_inst.contains_key(&load_inst),
            "load should read through MemorySSA facts"
        );
        assert!(
            prepared.memory().defs_by_inst.contains_key(&store_inst),
            "store should define a new memory version"
        );
        assert_eq!(entry.ops.len(), 5);

        assert_eq!(prepared.predicates().predicates.len(), 1);
        let predicate = prepared
            .predicates()
            .predicates
            .values()
            .next()
            .expect("branch predicate");
        assert_eq!(predicate.block_addr, 0x1100);
        assert_eq!(predicate.true_target, 0x1108);
        assert_eq!(predicate.false_target, 0x1104);
        assert_eq!(
            predicate.comparison.as_ref().map(|cmp| cmp.kind),
            Some(crate::semantic::CompareKind::Equal)
        );
        assert!(
            prepared
                .predicates()
                .block_assumptions
                .contains_key(&0x1104)
        );
        assert!(
            prepared
                .predicates()
                .block_assumptions
                .contains_key(&0x1108)
        );
    }

    #[test]
    fn ssa_artifact_exposes_typed_graph_queries() {
        let arch = make_x86_64_prep_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x1080,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(0x33, 8),
                },
                R2ILOp::Return {
                    target: make_reg(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let artifact = SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("artifact");
        let graph = artifact.graph();
        let value = artifact
            .blocks()
            .next()
            .and_then(|block| block.ops.first())
            .and_then(|op| op.dst())
            .cloned()
            .expect("destination value");
        let value_id = graph.value_id_for_var(&value).expect("value id");
        let def_inst = graph.def_inst(value_id).expect("definition");
        let use_sites = graph.use_sites(value_id);

        assert_eq!(
            graph.value(value_id).expect("value").var,
            value,
            "graph should retain render metadata for each typed value"
        );
        assert_eq!(
            graph.inst(def_inst).expect("inst").output,
            Some(value_id),
            "def_of should point back to the defining instruction"
        );
        assert_eq!(
            use_sites.len(),
            1,
            "return should consume the copied value once"
        );
    }

    #[test]
    fn ssa_artifact_graph_ids_are_deterministic() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1200,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1204,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let first = SsaArtifact::raw(&blocks, None).expect("first artifact");
        let second = SsaArtifact::raw(&blocks, None).expect("second artifact");

        assert_eq!(
            first.graph(),
            second.graph(),
            "graph ids should be stable across builds"
        );
    }

    #[test]
    fn prepared_function_ssa_collects_call_sites_and_memory_effects() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1200,
                size: 4,
                ops: vec![R2ILOp::Call {
                    target: make_const(0x401000, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1204,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared = SsaArtifact::raw(&blocks, None).expect("prepared SSA should build");
        let call = prepared
            .call_sites()
            .by_id
            .values()
            .next()
            .expect("call site fact");
        assert_eq!(call.direct_target, Some(0x401000));
        assert_eq!(call.fallthrough, Some(0x1204));
        assert_eq!(
            call.memory_effect,
            crate::semantic::CallMemoryEffect::Unknown
        );

        let call_ref = call.at;
        let uses = prepared
            .memory()
            .uses_by_inst
            .get(&call_ref)
            .expect("call memory use fact");
        let defs = prepared
            .memory()
            .defs_by_inst
            .get(&call_ref)
            .expect("call memory def fact");
        assert_eq!(uses.len(), 1);
        assert_eq!(defs.len(), 1);
        assert_eq!(uses[0].location.object, defs[0].location.object);
        assert_eq!(
            prepared
                .objects()
                .object(uses[0].location.object)
                .map(|fact| &fact.kind),
            Some(&crate::semantic::ObjectKind::EscapedUnknown)
        );
    }

    #[test]
    fn decompile_ssa_models_post_call_arm64_return_register_clobber() {
        let arch = make_arm64_alias_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x1400,
            size: 16,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(0x00, 8),
                    src: make_const(0, 8),
                },
                R2ILOp::Call {
                    target: make_ram(0x401000, 8),
                },
                R2ILOp::Copy {
                    dst: make_reg(0x80, 8),
                    src: make_reg(0x00, 8),
                },
                R2ILOp::IntEqual {
                    dst: Varnode {
                        space: SpaceId::Unique,
                        offset: 0x20,
                        size: 1,
                        meta: None,
                    },
                    a: make_reg(0x80, 8),
                    b: make_const(0, 8),
                },
                R2ILOp::CBranch {
                    target: make_const(0x1410, 8),
                    cond: Varnode {
                        space: SpaceId::Unique,
                        offset: 0x20,
                        size: 1,
                        meta: None,
                    },
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let prepared =
            SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA should build");
        let ops = &prepared.get_block(0x1400).expect("entry block").ops;
        let post_call_x0 = ops
            .iter()
            .find_map(|op| match op {
                SSAOp::CallDefine { dst } if dst.name == "x0" => Some(dst.clone()),
                _ => None,
            })
            .expect("decompile SSA should define a fresh x0 after calls");

        let copied_x8_source = ops
            .iter()
            .find_map(|op| match op {
                SSAOp::Copy { dst, src } if dst.name == "x8" => Some(src.clone()),
                _ => None,
            })
            .expect("expected x8 copy from call return register");

        assert_eq!(
            copied_x8_source, post_call_x0,
            "post-call x8 copy must use the fresh call result owner, not the pre-call x0"
        );
        assert_ne!(
            copied_x8_source,
            SSAVar::constant(0, 8),
            "call result must not fold back to the pre-call literal"
        );
    }

    #[test]
    fn prepared_function_ssa_recovers_direct_call_target_from_ram_literal() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1300,
                size: 4,
                ops: vec![R2ILOp::Call {
                    target: make_ram(0x401239, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1304,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared = SsaArtifact::raw(&blocks, None).expect("prepared SSA should build");
        let call = prepared
            .call_sites()
            .by_id
            .values()
            .next()
            .expect("call site fact");
        assert_eq!(call.direct_target, Some(0x401239));
        assert_eq!(call.fallthrough, Some(0x1304));
    }

    #[test]
    fn symbolic_function_ssa_recovers_indirect_call_target_from_copied_ram_literal() {
        let tmp = Varnode {
            space: SpaceId::Unique,
            offset: 0x10,
            size: 8,
            meta: None,
        };
        let blocks = vec![
            R2ILBlock {
                addr: 0x1310,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: tmp.clone(),
                        src: make_ram(0x1400a6010, 8),
                    },
                    R2ILOp::CallInd { target: tmp },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1314,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared =
            SsaArtifact::for_symbolic(&blocks, None).expect("symbolic prepared SSA should build");
        let call = prepared
            .call_sites()
            .by_id
            .values()
            .next()
            .expect("call site fact");
        assert_eq!(call.direct_target, Some(0x1400a6010));
        assert_eq!(call.fallthrough, Some(0x1314));
    }

    #[test]
    fn prepared_function_ssa_builds_memory_phis_per_object() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1300,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1308, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1304,
                size: 4,
                ops: vec![
                    R2ILOp::Store {
                        space: SpaceId::Ram,
                        addr: make_const(0x5000, 8),
                        val: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x130c, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1308,
                size: 4,
                ops: vec![R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: make_const(0x5000, 8),
                    val: make_const(2, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x130c,
                size: 4,
                ops: vec![
                    R2ILOp::Load {
                        dst: make_reg(0, 8),
                        space: SpaceId::Ram,
                        addr: make_const(0x5000, 8),
                    },
                    R2ILOp::Return {
                        target: make_reg(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared = SsaArtifact::raw(&blocks, None).expect("prepared SSA should build");
        let phis = prepared
            .memory()
            .phis_by_block
            .get(&0x130c)
            .expect("merge-block memory phi");
        assert_eq!(phis.len(), 1);
        assert_eq!(phis[0].inputs.len(), 2);

        let load_ref = SliceOpRef::Op {
            block_addr: 0x130c,
            op_idx: 0,
        };
        let load_inst = prepared
            .graph()
            .inst_id_for_op_site(load_ref.block_addr(), 0)
            .expect("load inst");
        let load_use = prepared
            .memory()
            .uses_by_inst
            .get(&load_inst)
            .and_then(|facts| facts.first())
            .expect("load use");
        assert_eq!(load_use.version, phis[0].output_version);
    }

    #[test]
    fn prepared_function_ssa_collects_structured_dataflow_facts() {
        let loop_blocks = vec![
            R2ILBlock {
                addr: 0x1400,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1408, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1404,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1408,
                size: 4,
                ops: vec![
                    R2ILOp::Store {
                        space: SpaceId::Ram,
                        addr: make_const(0x5000, 8),
                        val: make_const(7, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1400, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared = SsaArtifact::raw(&loop_blocks, None).expect("prepared SSA should build");
        let structured = prepared.structured();
        let loop_fact = structured.loops.values().next().expect("natural loop fact");
        assert_eq!(structured.loops.len(), 1);
        assert_eq!(loop_fact.header, 0x1400);
        assert_eq!(loop_fact.latches, vec![0x1408]);
        assert_eq!(loop_fact.exits, vec![0x1404]);
        assert!(loop_fact.body.contains(&0x1400));
        assert!(loop_fact.body.contains(&0x1408));
        assert!(loop_fact.condition.is_some());
        assert!(structured.memory_accesses.values().any(|access| {
            access.block_addr == 0x1408 && access.op_index == 0 && access.is_write
        }));

        let recursive_blocks = vec![
            R2ILBlock {
                addr: 0x1500,
                size: 4,
                ops: vec![R2ILOp::Call {
                    target: make_const(0x1500, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1504,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let recursive =
            SsaArtifact::raw(&recursive_blocks, None).expect("recursive SSA should build");
        let call = recursive
            .structured()
            .recursive_calls
            .values()
            .next()
            .expect("recursive call fact");
        assert_eq!(recursive.structured().recursive_calls.len(), 1);
        assert_eq!(call.block_addr, 0x1500);
        assert_eq!(call.target, 0x1500);
    }

    #[test]
    fn prepared_predicates_recover_signed_less_from_of_sf_flags() {
        let lhs = make_reg(0, 4);
        let rhs = make_reg(4, 4);
        let of = Varnode {
            space: SpaceId::Unique,
            offset: 0x2000,
            size: 1,
            meta: None,
        };
        let sf = Varnode {
            space: SpaceId::Unique,
            offset: 0x2001,
            size: 1,
            meta: None,
        };
        let sub = Varnode {
            space: SpaceId::Unique,
            offset: 0x2002,
            size: 4,
            meta: None,
        };
        let cond = Varnode {
            space: SpaceId::Unique,
            offset: 0x2003,
            size: 1,
            meta: None,
        };
        let blocks = vec![
            R2ILBlock {
                addr: 0x1600,
                size: 4,
                ops: vec![
                    R2ILOp::IntSBorrow {
                        dst: of.clone(),
                        a: lhs.clone(),
                        b: rhs.clone(),
                    },
                    R2ILOp::IntSub {
                        dst: sub.clone(),
                        a: lhs,
                        b: rhs,
                    },
                    R2ILOp::IntSLess {
                        dst: sf.clone(),
                        a: sub,
                        b: make_const(0, 4),
                    },
                    R2ILOp::IntNotEqual {
                        dst: cond.clone(),
                        a: of,
                        b: sf,
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1608, 8),
                        cond,
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1604,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1608,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_const(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared = SsaArtifact::raw(&blocks, None).expect("prepared SSA should build");
        let predicate = prepared
            .predicates()
            .predicates
            .values()
            .next()
            .expect("predicate fact");
        let compare = predicate
            .comparison
            .as_ref()
            .expect("signed compare provenance");
        assert_eq!(compare.kind, crate::semantic::CompareKind::SignedLess);
        assert_ne!(compare.lhs, compare.rhs);
    }

    #[test]
    fn test_ssa_function_diamond() {
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

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).unwrap();
        assert_eq!(func.num_blocks(), 4);

        // Merge block should have a phi node
        let merge = func.get_block(0x100c).unwrap();
        assert!(merge.has_phis());
        assert_eq!(merge.num_phis(), 1);

        // Phi should have two sources
        let phi = &merge.phis[0];
        assert_eq!(phi.sources.len(), 2);
    }

    #[test]
    fn cfg_risk_summary_reports_loops_and_switch_density() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1020, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_const(0x1000, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1020,
                size: 4,
                ops: vec![],
                switch_info: Some(R2ILSwitchInfo {
                    switch_addr: 0x1020,
                    min_val: 0,
                    max_val: 2,
                    default_target: Some(0x1040),
                    cases: vec![
                        SwitchCase {
                            value: 0,
                            target: 0x1030,
                        },
                        SwitchCase {
                            value: 1,
                            target: 0x1040,
                        },
                    ],
                }),
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1030,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1040,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_ram(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("ssa function");
        let summary = func.cfg_risk_summary();

        assert_eq!(summary.block_count, 6);
        assert_eq!(
            summary.loop_count, 1,
            "expected one natural loop, got {summary:?}"
        );
        assert_eq!(
            summary.back_edge_count, 1,
            "expected one back edge from loop latch, got {summary:?}"
        );
        assert_eq!(summary.switch_block_count, 1);
        assert_eq!(summary.max_switch_cases, 3);
    }

    #[test]
    fn test_raw_ssa_construction_is_deterministic_across_runs() {
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
                    R2ILOp::Copy {
                        dst: make_reg(8, 8),
                        src: make_reg(0, 8),
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
                    R2ILOp::Copy {
                        dst: make_reg(8, 8),
                        src: make_reg(0, 8),
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
                    R2ILOp::IntXor {
                        dst: make_reg(16, 8),
                        a: make_reg(8, 8),
                        b: make_reg(0, 8),
                    },
                    R2ILOp::Return {
                        target: make_ram(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let mut dumps = std::collections::BTreeSet::new();
        for _ in 0..32 {
            let func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
            dumps.insert(func.dump());
        }

        assert_eq!(
            dumps.len(),
            1,
            "raw SSA output should stay stable across repeated construction"
        );
    }

    #[test]
    fn test_find_def_use() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::IntAdd {
                    dst: make_reg(8, 8),
                    a: make_reg(0, 8),
                    b: make_const(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).unwrap();

        // Find definition of reg:0 v1
        let var = SSAVar::new("reg:0", 1, 8);
        let def = func.find_def(&var);
        assert!(def.is_some());
        let (addr, loc) = def.unwrap();
        assert_eq!(addr, 0x1000);
        assert!(matches!(loc, DefLocation::Op(0)));

        // Find uses of reg:0 v1
        let uses = func.find_uses(&var);
        assert!(!uses.is_empty());
    }

    #[test]
    fn test_dump() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(42, 8),
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
        ];

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks)
            .unwrap()
            .with_name("test_func");

        let dump = func.dump();
        assert!(dump.contains("test_func"));
        assert!(dump.contains("0x1000"));
        assert!(dump.contains("0x1004"));
    }

    #[test]
    fn test_from_blocks_default_runs_optimization() {
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

        let func = SSAFunction::from_blocks(&blocks).expect("optimized SSA should build");
        assert!(
            func.num_blocks() < blocks.len(),
            "optimized constructor should prune dead branch blocks via SCCP"
        );
    }

    #[test]
    fn test_refresh_after_cfg_mutation_recomputes_order_and_domtree() {
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
        ];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        func.remove_block(0x1004);
        func.refresh_after_cfg_mutation();

        assert!(!func.block_addrs().contains(&0x1004));
        assert!(func.get_block(0x1004).is_none());
        assert_eq!(func.idom(0x1008), Some(0x1000));
    }

    #[test]
    fn test_for_each_source_reports_phi_and_op_sites() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1008, 8),
                    cond: make_const(1, 1),
                }],
                op_metadata: std::collections::BTreeMap::new(),
                switch_info: None,
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
                op_metadata: std::collections::BTreeMap::new(),
                switch_info: None,
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
                op_metadata: std::collections::BTreeMap::new(),
                switch_info: None,
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::IntAdd {
                    dst: make_reg(8, 8),
                    a: make_reg(0, 8),
                    b: make_const(3, 8),
                }],
                op_metadata: std::collections::BTreeMap::new(),
                switch_info: None,
            },
        ];

        let func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let merge = func.get_block(0x100c).expect("merge block");
        assert!(merge.has_phis(), "fixture should produce a merge phi");

        let mut seen = Vec::new();
        merge.for_each_source(|src| {
            seen.push(match src.site {
                SourceSite::Phi {
                    phi_idx,
                    src_idx,
                    pred_addr,
                } => format!(
                    "phi:{}:{}:0x{:x}:{}",
                    phi_idx,
                    src_idx,
                    pred_addr,
                    src.var.display_name()
                ),
                SourceSite::Op { op_idx, src_idx } => {
                    format!("op:{}:{}:{}", op_idx, src_idx, src.var.display_name())
                }
            });
        });

        assert_eq!(seen.len(), 4, "2 phi sources + 2 IntAdd sources expected");
        assert!(
            seen[0].starts_with("phi:0:0:"),
            "first source should be first phi input"
        );
        assert!(
            seen[1].starts_with("phi:0:1:"),
            "second source should be second phi input"
        );
        assert!(
            seen[2].starts_with("op:0:0:"),
            "third source should be first op input"
        );
        assert!(
            seen[3].starts_with("op:0:1:"),
            "fourth source should be second op input"
        );
    }

    #[test]
    fn test_for_each_def_reports_phi_and_op_defs() {
        let block = SSABlock {
            addr: 0x2000,
            size: 4,
            phis: vec![PhiNode {
                dst: SSAVar::new("reg:0", 2, 8),
                sources: vec![(0x1000, SSAVar::new("reg:0", 0, 8))],
            }],
            ops: vec![
                SSAOp::Copy {
                    dst: SSAVar::new("reg:8", 1, 8),
                    src: SSAVar::new("reg:0", 2, 8),
                },
                SSAOp::Return {
                    target: SSAVar::new("reg:8", 1, 8),
                },
            ],
        };

        let mut seen = Vec::new();
        block.for_each_def(|def| {
            seen.push(match def.site {
                DefSite::Phi { phi_idx } => format!("phi:{}:{}", phi_idx, def.var.display_name()),
                DefSite::Op { op_idx } => format!("op:{}:{}", op_idx, def.var.display_name()),
            });
        });

        assert_eq!(
            seen,
            vec!["phi:0:reg:0_2".to_string(), "op:0:reg:8_1".to_string()]
        );
    }

    #[test]
    fn test_decompile_normalization_rewrites_same_block_subregister_root() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let block = func.get_block_mut(0x1000).expect("entry block");
        block.ops = vec![
            SSAOp::IntZExt {
                dst: SSAVar::new("x9", 1, 8),
                src: SSAVar::new("tmp:24c00", 3, 4),
            },
            SSAOp::IntSExt {
                dst: SSAVar::new("tmp:5f80", 1, 8),
                src: SSAVar::new("w9", 0, 4),
            },
        ];

        func.normalize_subregister_sources_for_decompile(&make_arm64_alias_arch());

        match &func.get_block(0x1000).expect("entry block").ops[1] {
            SSAOp::IntSExt { src, .. } => {
                assert_eq!(src, &SSAVar::new("tmp:24c00", 3, 4));
            }
            other => panic!("expected IntSExt, got {other:?}"),
        }
    }

    #[test]
    fn test_decompile_normalization_rewrites_narrow_alias_after_wide_zext_write() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let block = func.get_block_mut(0x1000).expect("entry block");
        block.ops = vec![
            SSAOp::IntZExt {
                dst: SSAVar::new("x8", 1, 8),
                src: SSAVar::new("tmp:25500", 1, 1),
            },
            SSAOp::IntRight {
                dst: SSAVar::new("tmp:18900", 1, 4),
                a: SSAVar::new("w8", 0, 4),
                b: SSAVar::constant(0, 4),
            },
        ];

        func.normalize_subregister_sources_for_decompile(&make_arm64_alias_arch());

        match &func.get_block(0x1000).expect("entry block").ops[1] {
            SSAOp::IntRight { a, .. } => {
                assert_eq!(a, &SSAVar::new("x8", 1, 4));
            }
            other => panic!("expected IntRight, got {other:?}"),
        }
    }

    #[test]
    fn test_decompile_normalization_propagates_family_root_across_cfg_edge() {
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

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        func.get_block_mut(0x1000).expect("entry block").ops = vec![
            SSAOp::IntZExt {
                dst: SSAVar::new("x8", 1, 8),
                src: SSAVar::new("tmp:24c00", 1, 4),
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1008", 0, 8),
                cond: SSAVar::constant(1, 1),
            },
        ];
        func.get_block_mut(0x1004).expect("fallthrough block").ops = vec![SSAOp::Copy {
            dst: SSAVar::new("tmp:300", 1, 4),
            src: SSAVar::new("w8", 0, 4),
        }];
        func.get_block_mut(0x1008).expect("taken block").ops = vec![SSAOp::Copy {
            dst: SSAVar::new("tmp:301", 1, 4),
            src: SSAVar::new("w8", 0, 4),
        }];

        func.normalize_subregister_sources_for_decompile(&make_arm64_alias_arch());

        for addr in [0x1004, 0x1008] {
            match &func.get_block(addr).expect("block").ops[0] {
                SSAOp::Copy { src, .. } => {
                    assert_eq!(src, &SSAVar::new("tmp:24c00", 1, 4));
                }
                other => panic!("expected Copy, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_decompile_normalization_truncates_wide_const_for_narrow_alias_use() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let block = func.get_block_mut(0x1000).expect("entry block");
        block.ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("x9", 1, 8),
                src: SSAVar::constant(0xdead, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:3e480", 1, 4),
                src: SSAVar::new("w9", 0, 4),
            },
        ];

        func.normalize_subregister_sources_for_decompile(&make_arm64_alias_arch());

        match &func.get_block(0x1000).expect("entry block").ops[1] {
            SSAOp::Copy { src, .. } => {
                assert_eq!(src, &SSAVar::constant(0xdead, 4));
            }
            other => panic!("expected Copy, got {other:?}"),
        }
    }

    #[test]
    fn test_decompile_prep_facts_collapse_copy_chain_and_trivial_phi_roots() {
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
                        src: make_const(0x42, 8),
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
                    src: make_const(0x42, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let arch = make_x86_64_prep_arch();
        let func = SSAFunction::from_blocks_for_decompile(&blocks, Some(&arch))
            .expect("prepared SSA should build");
        let facts = func.decompile_prep_facts().expect("prep facts");
        let merge = func.get_block(0x100c).expect("merge block");
        assert_eq!(merge.phis.len(), 1, "expected trivial merge phi");

        let const_root = SSAVar::constant(0x42, 8);
        let phi_dst = &merge.phis[0].dst;
        assert_eq!(
            facts.canonical_root_of(phi_dst),
            Some(&const_root),
            "merge phi should collapse to the shared constant root"
        );

        let left_dst = func
            .get_block(0x1004)
            .expect("left block")
            .ops
            .first()
            .and_then(|op| op.dst())
            .expect("left copy dst");
        let right_dst = func
            .get_block(0x1008)
            .expect("right block")
            .ops
            .first()
            .and_then(|op| op.dst())
            .expect("right copy dst");

        assert_eq!(facts.canonical_root_of(left_dst), Some(&const_root));
        assert_eq!(facts.canonical_root_of(right_dst), Some(&const_root));
        assert_eq!(facts.canonical_root_of(&const_root), Some(&const_root));
    }

    #[test]
    fn test_decompile_prep_facts_track_stack_pointer_and_frame_pointer_roots() {
        let blocks = vec![R2ILBlock {
            addr: 0x2000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        func.get_block_mut(0x2000).expect("entry block").ops = vec![
            SSAOp::IntAdd {
                dst: SSAVar::new("tmp:1", 1, 8),
                a: SSAVar::new("rsp", 0, 8),
                b: SSAVar::constant(0xfffffffffffffff0, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:2", 1, 8),
                src: SSAVar::new("tmp:1", 1, 8),
            },
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:3", 1, 8),
                a: SSAVar::new("rbp", 0, 8),
                b: SSAVar::constant(0x20, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:4", 1, 8),
                src: SSAVar::new("tmp:3", 1, 8),
            },
        ];
        func.refresh_decompile_prep_facts(None);

        let facts = func.decompile_prep_facts().expect("prep facts");
        let rsp_root = StackAddressRoot {
            base: StackAddressBase::StackPointer,
            offset: -16,
        };
        let rbp_root = StackAddressRoot {
            base: StackAddressBase::FramePointer,
            offset: -32,
        };

        assert_eq!(
            facts.stack_address_root_of(&SSAVar::new("tmp:1", 1, 8)),
            Some(&rsp_root)
        );
        assert_eq!(
            facts.stack_address_root_of(&SSAVar::new("tmp:2", 1, 8)),
            Some(&rsp_root)
        );
        assert_eq!(
            facts.stack_address_root_of(&SSAVar::new("tmp:3", 1, 8)),
            Some(&rbp_root)
        );
        assert_eq!(
            facts.stack_address_root_of(&SSAVar::new("tmp:4", 1, 8)),
            Some(&rbp_root)
        );
        assert_eq!(
            facts.canonical_root_of(&SSAVar::new("tmp:2", 1, 8)),
            Some(&SSAVar::new("tmp:1", 1, 8))
        );
        assert_eq!(
            facts.canonical_root_of(&SSAVar::new("tmp:4", 1, 8)),
            Some(&SSAVar::new("tmp:3", 1, 8))
        );
    }

    #[test]
    fn test_frame_pointer_copy_rebases_stack_root_to_zero() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntSub {
                dst: SSAVar::new("rsp", 1, 8),
                a: SSAVar::new("rsp", 0, 8),
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("rbp", 1, 8),
                src: SSAVar::new("rsp", 1, 8),
            },
            SSAOp::IntAdd {
                dst: SSAVar::new("tmp:fp_slot", 1, 8),
                a: SSAVar::new("rbp", 1, 8),
                b: SSAVar::constant(0xffffffffffffffe8, 8),
            },
        ];
        func.refresh_decompile_prep_facts(None);

        let facts = func.decompile_prep_facts().expect("prep facts");
        assert_eq!(
            facts.stack_address_root_of(&SSAVar::new("rsp", 1, 8)),
            Some(&StackAddressRoot {
                base: StackAddressBase::StackPointer,
                offset: -8,
            })
        );
        assert_eq!(
            facts.stack_address_root_of(&SSAVar::new("rbp", 1, 8)),
            Some(&StackAddressRoot {
                base: StackAddressBase::FramePointer,
                offset: 0,
            })
        );
        assert_eq!(
            facts.stack_address_root_of(&SSAVar::new("tmp:fp_slot", 1, 8)),
            Some(&StackAddressRoot {
                base: StackAddressBase::FramePointer,
                offset: -24,
            })
        );
    }
}
