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
use crate::CanonicalStorageId;
use crate::aggregate_access::{
    AggregateAccessProjectionFacts, collect_aggregate_access_projections,
};
use crate::block::SSABlock as LocalSSABlock;
use crate::cfg::{CFG, CFGEdge};
use crate::control::{
    SsaExecutionStopReason, SsaPrepareError, SsaWorkControl, UncheckedSsaWorkControl,
};
use crate::defuse::{BackwardSlice, SliceOpRef, backward_slice_from_op, backward_slice_from_var};
use crate::domtree::DomTree;
use crate::graph::SsaGraph;
use crate::machine_context::{
    SourceCallSiteInterface, SourceFunctionInterface, SourceMachineContext,
};
use crate::naming::{ARCH_DERIVED_CACHE_MAX_ENTRIES, ArchCacheTag, cached_register_name_map};
use crate::op::SSAOp;
use crate::phi::{PhiPlacement, collect_defs_from_cfg_with_names_storage_and_control};
use crate::private_frame::{PrivateFrameFact, collect_private_frame_fact};
use crate::rename::{
    CallBoundaryConfig, CallBoundaryDef, rename_function_with_names_and_call_boundaries_and_control,
};
use crate::semantic::{
    CallResultCertificate, CallSiteFacts, CallSiteId, CallsiteCertificate, MemoryAccessCertificate,
    MemoryDefFact, MemorySSAFacts, MemoryUseFact, ObjectId, ObjectModel, PredicateFacts,
    PreparedFunctionFacts, ReturnValueCertificate, StackReloadSourceCertificate,
    StructuredDataflowFacts,
};
use crate::var::{SSAVar, SSAVarNameKind};

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
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum StackAddressBase {
    FramePointer,
    StackPointer,
}

/// Proven stack-address root: `base +/- offset`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct StackAddressRoot {
    pub base: StackAddressBase,
    pub offset: i64,
}

/// Decompiler-prep analysis facts derived from SSA.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DecompilePrepFacts {
    pub canonical_value_roots: BTreeMap<SSAVar, SSAVar>,
    pub stack_address_roots: BTreeMap<SSAVar, StackAddressRoot>,
    /// Entry SSA values bound to canonical ABI parameter slots.
    pub formal_parameters: BTreeMap<SSAVar, usize>,
    /// Full-width entry ABI values that may serve as parameter address bases.
    pub formal_parameter_bases: BTreeMap<SSAVar, usize>,
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
    machine_context: SourceMachineContext,
    aggregate_accesses: AggregateAccessProjectionFacts,
    private_frame: Option<PrivateFrameFact>,
}

impl SsaArtifact {
    #[cfg(test)]
    fn new(function: SSAFunction, mode: FunctionPrepareMode) -> Self {
        Self::new_with_context(function, mode, SourceMachineContext::from_blocks(&[], None))
    }

    fn new_with_context(
        function: SSAFunction,
        mode: FunctionPrepareMode,
        machine_context: SourceMachineContext,
    ) -> Self {
        Self::new_with_context_and_control(
            function,
            mode,
            machine_context,
            &UncheckedSsaWorkControl,
        )
        .expect("unchecked SSA artifact construction cannot stop")
    }

    fn new_with_context_and_control<C: SsaWorkControl + ?Sized>(
        function: SSAFunction,
        mode: FunctionPrepareMode,
        mut machine_context: SourceMachineContext,
        control: &C,
    ) -> Result<Self, SsaExecutionStopReason> {
        control.poll()?;
        machine_context.remap_memory_sites_to_prepared(&function);
        let graph = SsaGraph::from_function_with_storage(&function);
        control.poll()?;
        let facts = PreparedFunctionFacts::collect_with_context(
            &function,
            &graph,
            &AssumptionSet::default(),
            &machine_context,
        );
        let aggregate_accesses = collect_aggregate_access_projections(
            &graph,
            &facts.addresses,
            &facts.structured.memory_accesses,
            &machine_context,
        );
        let private_frame = machine_context.function_interface().and_then(|interface| {
            collect_private_frame_fact(
                mode,
                &function,
                &graph,
                &facts,
                &machine_context,
                interface.revision_identity(),
            )
        });
        control.poll()?;
        Ok(Self {
            function,
            graph,
            mode,
            facts,
            machine_context,
            aggregate_accesses,
            private_frame,
        })
    }

    pub fn from_blocks(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new_with_context(
            SSAFunction::from_blocks_with_arch(blocks, arch)?,
            FunctionPrepareMode::Generic,
            SourceMachineContext::from_blocks(blocks, arch),
        ))
    }

    pub fn raw(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new_with_context(
            SSAFunction::from_blocks_raw(blocks, arch)?,
            FunctionPrepareMode::Raw,
            SourceMachineContext::from_blocks(blocks, arch),
        ))
    }

    /// Build raw SSA with an explicit, revision-bound function interface.
    pub fn raw_with_interface(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        function_interface: SourceFunctionInterface,
    ) -> Option<Self> {
        Self::raw_with_interfaces(blocks, arch, Some(function_interface), Vec::new())
    }

    /// Build raw SSA with explicit, revision-bound function and callsite
    /// interfaces. A missing function interface does not weaken the per-callsite
    /// revision and carrier checks.
    pub fn raw_with_interfaces(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        function_interface: Option<SourceFunctionInterface>,
        call_site_interfaces: Vec<SourceCallSiteInterface>,
    ) -> Option<Self> {
        Some(Self::new_with_context(
            SSAFunction::from_blocks_raw(blocks, arch)?,
            FunctionPrepareMode::Raw,
            SourceMachineContext::from_blocks_with_interfaces(
                blocks,
                arch,
                function_interface,
                call_site_interfaces,
            ),
        ))
    }

    pub fn for_decompile(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new_with_context(
            SSAFunction::from_blocks_for_decompile(blocks, arch)?,
            FunctionPrepareMode::Decompile,
            SourceMachineContext::from_blocks(blocks, arch),
        ))
    }

    /// Build a complete decompiler SSA artifact under cooperative control.
    ///
    /// Work is assembled in local values. A stop returns an explicit error and
    /// drops all intermediate state rather than exposing a partial artifact.
    pub fn for_decompile_with_control<C: SsaWorkControl + ?Sized>(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        control: &C,
    ) -> Result<Self, SsaPrepareError> {
        let function = SSAFunction::from_blocks_for_decompile_with_control(blocks, arch, control)?;
        control.poll()?;
        let machine_context = SourceMachineContext::from_blocks(blocks, arch);
        Self::new_with_context_and_control(
            function,
            FunctionPrepareMode::Decompile,
            machine_context,
            control,
        )
        .map_err(Into::into)
    }

    /// Build decompiler-prepared SSA with an explicit function interface.
    pub fn for_decompile_with_interface(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        function_interface: SourceFunctionInterface,
    ) -> Option<Self> {
        Self::for_decompile_with_interfaces(blocks, arch, Some(function_interface), Vec::new())
    }

    /// Build decompiler-prepared SSA with explicit, revision-bound function and
    /// callsite interfaces.
    pub fn for_decompile_with_interfaces(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        function_interface: Option<SourceFunctionInterface>,
        call_site_interfaces: Vec<SourceCallSiteInterface>,
    ) -> Option<Self> {
        Some(Self::new_with_context(
            SSAFunction::from_blocks_for_decompile(blocks, arch)?,
            FunctionPrepareMode::Decompile,
            SourceMachineContext::from_blocks_with_interfaces(
                blocks,
                arch,
                function_interface,
                call_site_interfaces,
            ),
        ))
    }

    /// Build controlled decompiler SSA with explicit source interfaces.
    pub fn for_decompile_with_interfaces_and_control<C: SsaWorkControl + ?Sized>(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        function_interface: Option<SourceFunctionInterface>,
        call_site_interfaces: Vec<SourceCallSiteInterface>,
        control: &C,
    ) -> Result<Self, SsaPrepareError> {
        let function = SSAFunction::from_blocks_for_decompile_with_control(blocks, arch, control)?;
        control.poll()?;
        let machine_context = SourceMachineContext::from_blocks_with_interfaces(
            blocks,
            arch,
            function_interface,
            call_site_interfaces,
        );
        Self::new_with_context_and_control(
            function,
            FunctionPrepareMode::Decompile,
            machine_context,
            control,
        )
        .map_err(Into::into)
    }

    pub fn for_patterns(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new_with_context(
            SSAFunction::from_blocks_for_patterns(blocks, arch)?,
            FunctionPrepareMode::Patterns,
            SourceMachineContext::from_blocks(blocks, arch),
        ))
    }

    /// Build a complete pattern/type-inference SSA artifact under cooperative control.
    pub fn for_patterns_with_control<C: SsaWorkControl + ?Sized>(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        control: &C,
    ) -> Result<Self, SsaPrepareError> {
        let function = SSAFunction::from_blocks_for_patterns_with_control(blocks, arch, control)?;
        control.poll()?;
        Self::new_with_context_and_control(
            function,
            FunctionPrepareMode::Patterns,
            SourceMachineContext::from_blocks(blocks, arch),
            control,
        )
        .map_err(Into::into)
    }

    pub fn for_data_refs(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Some(Self::new_with_context(
            SSAFunction::from_blocks_for_data_refs(blocks, arch)?,
            FunctionPrepareMode::DataRefs,
            SourceMachineContext::from_blocks(blocks, arch),
        ))
    }

    pub fn for_symbolic(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        let mut function = SSAFunction::from_blocks_raw(blocks, arch)?;
        function.refresh_decompile_prep_facts(arch);
        Some(Self::new_with_context(
            function,
            FunctionPrepareMode::Symbolic,
            SourceMachineContext::from_blocks(blocks, arch),
        ))
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

    pub const fn machine_context(&self) -> &SourceMachineContext {
        &self.machine_context
    }

    pub const fn aggregate_accesses(&self) -> &AggregateAccessProjectionFacts {
        &self.aggregate_accesses
    }

    pub const fn private_frame(&self) -> Option<&PrivateFrameFact> {
        self.private_frame.as_ref()
    }

    pub fn with_assumptions(&self, assumptions: &AssumptionSet) -> Self {
        let facts = PreparedFunctionFacts::collect_with_context(
            &self.function,
            &self.graph,
            assumptions,
            &self.machine_context,
        );
        let aggregate_accesses = collect_aggregate_access_projections(
            &self.graph,
            &facts.addresses,
            &facts.structured.memory_accesses,
            &self.machine_context,
        );
        let private_frame = self
            .machine_context
            .function_interface()
            .and_then(|interface| {
                collect_private_frame_fact(
                    self.mode,
                    &self.function,
                    &self.graph,
                    &facts,
                    &self.machine_context,
                    interface.revision_identity(),
                )
            });
        Self {
            function: self.function.clone(),
            graph: self.graph.clone(),
            mode: self.mode,
            facts,
            machine_context: self.machine_context.clone(),
            aggregate_accesses,
            private_frame,
        }
    }

    pub fn objects(&self) -> &ObjectModel {
        &self.facts.objects
    }

    pub fn addresses(&self) -> &crate::AddressProvenanceFacts {
        &self.facts.addresses
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

    pub fn control_domains(&self) -> &crate::semantic::ControlDomainFacts {
        &self.facts.control_domains
    }

    pub fn certificates(&self) -> &crate::semantic::PreparedFunctionCertificates {
        &self.facts.certificates
    }

    pub fn obligations(&self) -> &crate::obligation::SemanticObligationInventory {
        &self.facts.obligations
    }

    pub fn callsite_certificate_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&CallsiteCertificate> {
        let inst = self.graph.inst_id_for_op_site(block_addr, op_idx)?;
        let callsite = self.facts.certificates.callsites_by_inst.get(&inst)?;
        self.facts.certificates.callsites.get(callsite)
    }

    pub fn memory_certificates_for_op_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Vec<&MemoryAccessCertificate> {
        let certs = &self.facts.certificates;
        let read = certs
            .memory_accesses_by_op
            .get(&(block_addr, op_idx, false))
            .into_iter()
            .flatten();
        let write = certs
            .memory_accesses_by_op
            .get(&(block_addr, op_idx, true))
            .into_iter()
            .flatten();
        read.chain(write)
            .filter_map(|id| certs.memory_accesses.get(id))
            .collect()
    }

    pub fn memory_certificate_for_op_site(
        &self,
        block_addr: u64,
        op_idx: usize,
        is_write: bool,
    ) -> Option<&MemoryAccessCertificate> {
        let certs = &self.facts.certificates;
        self.facts
            .certificates
            .memory_accesses_by_op
            .get(&(block_addr, op_idx, is_write))?
            .iter()
            .filter_map(|id| certs.memory_accesses.get(id))
            .find(|cert| cert.is_write == is_write)
    }

    pub fn stack_reload_certificate_for_value(
        &self,
        value_id: crate::graph::ValueId,
    ) -> Option<&StackReloadSourceCertificate> {
        self.facts.certificates.stack_reloads.get(&value_id)
    }

    pub fn stack_reload_certificate_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&StackReloadSourceCertificate> {
        let inst = self.graph.inst_id_for_op_site(block_addr, op_idx)?;
        let value = self.graph.inst(inst)?.output?;
        self.facts.certificates.stack_reloads.get(&value)
    }

    pub fn call_result_certificate_for_value(
        &self,
        value_id: crate::graph::ValueId,
    ) -> Option<&CallResultCertificate> {
        self.facts.certificates.call_results.get(&value_id)
    }

    pub fn call_result_certificate_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&CallResultCertificate> {
        let inst = self.graph.inst_id_for_op_site(block_addr, op_idx)?;
        let value = self.facts.certificates.call_results_by_inst.get(&inst)?;
        self.facts.certificates.call_results.get(value)
    }

    pub fn call_result_certificates_for_callsite(
        &self,
        call_site: CallSiteId,
    ) -> Vec<&CallResultCertificate> {
        self.facts
            .certificates
            .call_results_by_callsite
            .get(&call_site)
            .into_iter()
            .flatten()
            .filter_map(|value| self.facts.certificates.call_results.get(value))
            .collect()
    }

    pub fn return_certificate_for_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<&ReturnValueCertificate> {
        let inst = self.graph.inst_id_for_op_site(block_addr, op_idx)?;
        let index = self.facts.certificates.returns_by_inst.get(&inst)?;
        self.facts.certificates.returns.get(*index)
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
    u64::from_str_radix(value_str, 16).ok()
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

    pub fn formal_parameter_of(&self, var: &SSAVar) -> Option<usize> {
        self.formal_parameters.get(var).copied()
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
    /// Canonical lifted storage retained during SSA renaming.
    ///
    /// Values are attached from raw varnodes at the lift/SSA seam. Consumers
    /// must not reconstruct this information from `SSAVar::name`.
    canonical_storage_by_var: BTreeMap<SSAVar, CanonicalStorageId>,
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
            canonical_storage_by_var: self.canonical_storage_by_var.clone(),
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
    /// Name-independent lifted storage identity.
    #[serde(default)]
    pub canonical_storage: Option<CanonicalStorageId>,
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
        Self::from_blocks_for_decompile_with_control(blocks, arch, &UncheckedSsaWorkControl).ok()
    }

    /// Build decompiler-prepared SSA while polling expensive worklists.
    ///
    /// The function is constructed locally and returned only after every
    /// preparation and canonicalization phase completes.
    pub fn from_blocks_for_decompile_with_control<C: SsaWorkControl + ?Sized>(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        control: &C,
    ) -> Result<Self, SsaPrepareError> {
        control.poll()?;
        let mut func = Self::from_blocks_raw_for_decompile_with_control(blocks, arch, control)?;
        func.prepare_for_decompile_with_control(
            &crate::optimize::DecompilePrepConfig::default(),
            control,
        )?;
        func.refresh_decompile_prep_facts_with_control(arch, control)?;
        control.poll()?;
        Ok(func)
    }

    /// Build SSA prepared for pattern/type inference.
    ///
    /// This keeps memory reads and address arithmetic intact while still
    /// applying limited whole-function SCCP so layout-sensitive patterns
    /// collapse to a canonical indexed+offset form for downstream consumers.
    pub fn from_blocks_for_patterns(blocks: &[R2ILBlock], arch: Option<&ArchSpec>) -> Option<Self> {
        Self::from_blocks_for_patterns_with_control(blocks, arch, &UncheckedSsaWorkControl).ok()
    }

    /// Build pattern/type-inference SSA while polling expensive worklists.
    pub fn from_blocks_for_patterns_with_control<C: SsaWorkControl + ?Sized>(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        control: &C,
    ) -> Result<Self, SsaPrepareError> {
        control.poll()?;
        let mut func = Self::from_blocks_raw_with_policy_and_control(blocks, arch, None, control)?;
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
        func.decompile_prep_facts = None;
        func.invalidate_query_index();
        crate::optimize::optimize_function_with_control(&mut func, &cfg, control)?;
        func.refresh_decompile_prep_facts_with_control(arch, control)?;
        control.poll()?;
        Ok(func)
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
        Self::from_blocks_raw_for_decompile_with_control(blocks, arch, &UncheckedSsaWorkControl)
            .ok()
    }

    /// Build raw decompiler SSA while polling construction worklists.
    pub fn from_blocks_raw_for_decompile_with_control<C: SsaWorkControl + ?Sized>(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        control: &C,
    ) -> Result<Self, SsaPrepareError> {
        let policy = decompile_call_boundary_config(arch);
        Self::from_blocks_raw_with_policy_and_control(blocks, arch, policy.as_ref(), control)
    }

    fn from_blocks_raw_with_policy(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        call_boundaries: Option<&CallBoundaryConfig>,
    ) -> Option<Self> {
        Self::from_blocks_raw_with_policy_and_control(
            blocks,
            arch,
            call_boundaries,
            &UncheckedSsaWorkControl,
        )
        .ok()
    }

    fn from_blocks_raw_with_policy_and_control<C: SsaWorkControl + ?Sized>(
        blocks: &[R2ILBlock],
        arch: Option<&ArchSpec>,
        call_boundaries: Option<&CallBoundaryConfig>,
        control: &C,
    ) -> Result<Self, SsaPrepareError> {
        control.poll()?;
        if blocks.is_empty() {
            return Err(SsaPrepareError::MalformedInput);
        }

        // Build CFG
        let cfg = CFG::from_blocks(blocks).ok_or(SsaPrepareError::MalformedInput)?;
        control.poll()?;
        let entry = cfg.entry;

        // Compute dominator tree
        let domtree = DomTree::compute_with_control(&cfg, control)?;

        let reg_names = arch.map(cached_register_name_map);
        let reg_names_ref = reg_names.as_deref();

        // Collect variable definitions and sizes
        let (defs, var_sizes, storage_by_name) =
            collect_defs_from_cfg_with_names_storage_and_control(&cfg, reg_names_ref, control)?;

        // Place phi nodes
        let phi_placement = PhiPlacement::compute_with_storage_and_control(
            &cfg,
            &domtree,
            &defs,
            &var_sizes,
            &storage_by_name,
            control,
        )?;

        // Rename variables
        let renamed = rename_function_with_names_and_call_boundaries_and_control(
            &cfg,
            &domtree,
            &phi_placement,
            &var_sizes,
            reg_names_ref,
            call_boundaries,
            control,
        )?;

        // Build SSA blocks
        let mut ssa_blocks = HashMap::new();
        for &addr in &renamed.block_order {
            control.poll()?;
            let cfg_block = cfg.get_block(addr).ok_or(SsaPrepareError::MalformedInput)?;
            let ops = renamed.blocks.get(&addr).cloned().unwrap_or_default();

            // Separate phi nodes from other ops
            let (phi_ops, other_ops): (Vec<_>, Vec<_>) = ops
                .into_iter()
                .partition(|op| matches!(op, SSAOp::Phi { .. }));

            // Convert phi ops to PhiNode structs
            let preds = cfg.predecessors(addr);
            let phis: Vec<PhiNode> = phi_ops
                .into_iter()
                .enumerate()
                .filter_map(|(phi_idx, op)| {
                    if let SSAOp::Phi { dst, sources } = op {
                        let phi_sources: Vec<(u64, SSAVar)> = sources
                            .into_iter()
                            .zip(preds.iter())
                            .map(|(var, &pred)| (pred, var))
                            .collect();
                        let canonical_storage = phi_placement
                            .get_phis(addr)
                            .get(phi_idx)
                            .and_then(|phi| phi.storage);
                        Some(PhiNode {
                            dst,
                            sources: phi_sources,
                            canonical_storage,
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

        let mut function = Self {
            name: None,
            entry,
            cfg,
            domtree,
            blocks: ssa_blocks,
            block_order: renamed.block_order,
            canonical_storage_by_var: renamed.canonical_storage_by_var,
            decompile_prep_facts: None,
            query_index: RwLock::new(None),
        };
        if let Some(arch) = arch {
            function.normalize_register_alias_sources_with_control(arch, control)?;
        }
        control.poll()?;
        Ok(function)
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

    /// Return name-independent storage provenance retained from the lifted
    /// varnode that produced or supplied this SSA value.
    pub(crate) fn canonical_storage_for_var(
        &self,
        var: &SSAVar,
    ) -> Option<CanonicalStorageId> {
        self.canonical_storage_by_var.get(var).copied()
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

    /// Return whether a value reaches any use other than a pure SSA carrier.
    ///
    /// Copy destinations and phi destinations are followed transitively. This
    /// makes dead carrier cycles removable without relying on register names,
    /// while conservatively treating malformed use locations as meaningful.
    pub fn has_noncarrier_use(&self, var: &SSAVar) -> bool {
        let mut pending = vec![var.clone()];
        let mut visited = HashSet::new();
        while let Some(current) = pending.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            for (block_addr, location) in self.find_uses(&current) {
                let Some(block) = self.get_block(block_addr) else {
                    return true;
                };
                let carrier = match location {
                    UseLocation::Phi { phi_idx, .. } => {
                        block.phis.get(phi_idx).map(|phi| phi.dst.clone())
                    }
                    UseLocation::Op { op_idx, .. } => {
                        block.ops.get(op_idx).and_then(|op| match op {
                            SSAOp::Copy { dst, .. } => Some(dst.clone()),
                            _ => None,
                        })
                    }
                };
                let Some(carrier) = carrier else {
                    return true;
                };
                pending.push(carrier);
            }
        }
        false
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
        self.prepare_for_decompile_with_control(config, &UncheckedSsaWorkControl)
            .expect("unchecked decompiler preparation cannot stop")
    }

    fn prepare_for_decompile_with_control<C: SsaWorkControl + ?Sized>(
        &mut self,
        config: &crate::optimize::DecompilePrepConfig,
        control: &C,
    ) -> Result<crate::optimize::OptimizationStats, SsaExecutionStopReason> {
        control.poll()?;
        self.decompile_prep_facts = None;
        self.invalidate_query_index();
        let cfg: crate::optimize::OptimizationConfig = config.into();
        crate::optimize::optimize_function_with_control(self, &cfg, control)
    }

    #[cfg(test)]
    fn normalize_register_alias_sources(&mut self, arch: &ArchSpec) {
        self.normalize_register_alias_sources_with_control(arch, &UncheckedSsaWorkControl)
            .expect("unchecked register alias normalization cannot stop");
    }

    fn normalize_register_alias_sources_with_control<C: SsaWorkControl + ?Sized>(
        &mut self,
        arch: &ArchSpec,
        control: &C,
    ) -> Result<(), SsaExecutionStopReason> {
        control.poll()?;
        self.decompile_prep_facts = None;
        self.invalidate_query_index();
        let family_info = cached_register_family_info(arch);
        if family_info.name_to_member.is_empty() {
            return Ok(());
        }

        let block_in_states = self
            .compute_decompile_family_states_with_control(&family_info, control)?
            .incoming;

        for &addr in &self.block_order {
            control.poll()?;
            let mut state = block_in_states.get(&addr).cloned().unwrap_or_default();
            let Some(block) = self.blocks.get_mut(&addr) else {
                continue;
            };

            for phi in &block.phis {
                control.poll()?;
                apply_phi_family_effect(phi, &mut state, &family_info);
            }

            let original_ops = std::mem::take(&mut block.ops);
            let mut normalized_ops = Vec::with_capacity(original_ops.len());
            for (op_index, op) in original_ops.into_iter().enumerate() {
                control.poll()?;
                let (materialized, rewritten) =
                    materialize_register_alias_sources(&op, &state, &family_info, addr, op_index);
                normalized_ops.extend(materialized);
                apply_op_family_effect(&rewritten, &mut state, &family_info);
                normalized_ops.push(rewritten);
            }
            block.ops = normalized_ops;
        }

        // Renaming treats overlapping register names as independent variables,
        // so a phi for a contained lane can still carry its version-zero name
        // on an edge where the predecessor actually wrote the wide register.
        // Recompute after ordinary source normalization: this makes edge state
        // refer to the materialized lane producers created above rather than to
        // stale alias names from the lifted input.
        let family_states =
            self.compute_decompile_family_states_with_control(&family_info, control)?;
        self.materialize_register_alias_phi_sources(
            &family_states.outgoing,
            &family_info,
            control,
        )?;
        control.poll()?;
        Ok(())
    }

    fn materialize_register_alias_phi_sources<C: SsaWorkControl + ?Sized>(
        &mut self,
        block_out_states: &HashMap<u64, FamilyRootState>,
        family_info: &RegisterFamilyInfo,
        control: &C,
    ) -> Result<(), SsaExecutionStopReason> {
        struct PhiSourceRewrite {
            block_addr: u64,
            phi_index: usize,
            source_index: usize,
            replacement: SSAVar,
            projection: Option<(u64, SSAOp)>,
        }

        let mut rewrites = Vec::new();
        for &block_addr in &self.block_order {
            control.poll()?;
            let Some(block) = self.blocks.get(&block_addr) else {
                continue;
            };
            for (phi_index, phi) in block.phis.iter().enumerate() {
                control.poll()?;
                for (source_index, (pred_addr, source)) in phi.sources.iter().enumerate() {
                    let Some(member) = family_info.member_for(source) else {
                        continue;
                    };
                    let requested = RegisterFamilySlot {
                        family_id: member.family_id,
                        offset: member.offset,
                        width: source.size,
                    };
                    let Some(root) = block_out_states
                        .get(pred_addr)
                        .and_then(|state| family_root_slice_for_range(state, requested))
                    else {
                        // An unavailable range stays unresolved. Adjacent or
                        // partial fragments must never be assembled implicitly.
                        continue;
                    };
                    if let Some(direct) = direct_family_root_value(&root, source.size) {
                        if direct != *source {
                            rewrites.push(PhiSourceRewrite {
                                block_addr,
                                phi_index,
                                source_index,
                                replacement: direct,
                                projection: None,
                            });
                        }
                        continue;
                    }
                    if root.value == *source && root.offset == 0 {
                        continue;
                    }
                    let projected = SSAVar::new(
                        format!("tmp:regalias:phi:{block_addr:x}:{phi_index:x}:{source_index:x}"),
                        1,
                        source.size,
                    );
                    rewrites.push(PhiSourceRewrite {
                        block_addr,
                        phi_index,
                        source_index,
                        replacement: projected.clone(),
                        projection: Some((
                            *pred_addr,
                            SSAOp::Subpiece {
                                dst: projected,
                                src: root.value,
                                offset: root.offset,
                            },
                        )),
                    });
                }
            }
        }

        for rewrite in rewrites {
            control.poll()?;
            let projection_inserted = match rewrite.projection {
                Some((pred_addr, projection)) => {
                    let Some(pred) = self.blocks.get_mut(&pred_addr) else {
                        continue;
                    };
                    let insert_at = pred
                        .ops
                        .last()
                        .filter(|op| {
                            matches!(
                                op,
                                SSAOp::Branch { .. }
                                    | SSAOp::CBranch { .. }
                                    | SSAOp::BranchInd { .. }
                                    | SSAOp::Return { .. }
                            )
                        })
                        .map_or(pred.ops.len(), |_| pred.ops.len().saturating_sub(1));
                    pred.ops.insert(insert_at, projection);
                    true
                }
                None => true,
            };
            if !projection_inserted {
                continue;
            }
            if let Some(phi) = self
                .blocks
                .get_mut(&rewrite.block_addr)
                .and_then(|block| block.phis.get_mut(rewrite.phi_index))
                && let Some((_, source)) = phi.sources.get_mut(rewrite.source_index)
            {
                *source = rewrite.replacement;
            }
        }
        Ok(())
    }

    /// Snapshot the current decompiler-prep fact view, if available.
    pub fn decompile_prep_facts(&self) -> Option<&DecompilePrepFacts> {
        self.decompile_prep_facts.as_ref()
    }

    /// Refresh the cached decompiler-prep facts for the current SSA state.
    pub fn refresh_decompile_prep_facts(&mut self, arch: Option<&ArchSpec>) {
        self.refresh_decompile_prep_facts_with_control(arch, &UncheckedSsaWorkControl)
            .expect("unchecked decompiler fact collection cannot stop");
    }

    fn refresh_decompile_prep_facts_with_control<C: SsaWorkControl + ?Sized>(
        &mut self,
        arch: Option<&ArchSpec>,
        control: &C,
    ) -> Result<(), SsaExecutionStopReason> {
        let facts = self.collect_decompile_prep_facts_with_control(arch, control)?;
        control.poll()?;
        self.decompile_prep_facts = Some(facts);
        Ok(())
    }

    fn collect_decompile_prep_facts_with_control<C: SsaWorkControl + ?Sized>(
        &self,
        arch: Option<&ArchSpec>,
        control: &C,
    ) -> Result<DecompilePrepFacts, SsaExecutionStopReason> {
        control.poll()?;
        let abi = crate::AbiProfile::from_arch(arch);
        let cached_family_info = arch.map(cached_register_family_info);
        let empty_family_info = RegisterFamilyInfo::default();
        let family_info = cached_family_info.as_deref().unwrap_or(&empty_family_info);
        let family_in_states = if family_info.name_to_member.is_empty() {
            HashMap::new()
        } else {
            self.compute_decompile_family_in_states_with_control(family_info, control)?
        };
        let mut facts = DecompilePrepFacts::default();
        for block in self.blocks() {
            control.poll()?;
            for phi in &block.phis {
                control.poll()?;
                for var in
                    std::iter::once(&phi.dst).chain(phi.sources.iter().map(|(_, source)| source))
                {
                    if let Some(index) = abi.formal_argument_index(var) {
                        facts.formal_parameters.insert(var.clone(), index);
                    }
                    if let Some(index) = abi.formal_address_argument_index(var) {
                        facts.formal_parameter_bases.insert(var.clone(), index);
                    }
                }
            }
            for op in &block.ops {
                control.poll()?;
                if let Some(dst) = op.dst()
                    && let Some(index) = abi.formal_argument_index(dst)
                {
                    facts.formal_parameters.insert(dst.clone(), index);
                }
                if let Some(dst) = op.dst()
                    && let Some(index) = abi.formal_address_argument_index(dst)
                {
                    facts.formal_parameter_bases.insert(dst.clone(), index);
                }
                op.for_each_source(&mut |source| {
                    if let Some(index) = abi.formal_argument_index(source) {
                        facts.formal_parameters.insert(source.clone(), index);
                    }
                    if let Some(index) = abi.formal_address_argument_index(source) {
                        facts.formal_parameter_bases.insert(source.clone(), index);
                    }
                });
            }
        }

        let mut changed = true;
        while changed {
            control.poll()?;
            changed = false;
            for &addr in &self.block_order {
                control.poll()?;
                let mut family_state = family_in_states.get(&addr).cloned().unwrap_or_default();
                let Some(block) = self.get_block(addr) else {
                    continue;
                };

                for phi in &block.phis {
                    control.poll()?;
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
                    control.poll()?;
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

        control.poll()?;
        Ok(facts)
    }

    fn compute_decompile_family_in_states_with_control<C: SsaWorkControl + ?Sized>(
        &self,
        family_info: &RegisterFamilyInfo,
        control: &C,
    ) -> Result<HashMap<u64, FamilyRootState>, SsaExecutionStopReason> {
        Ok(self
            .compute_decompile_family_states_with_control(family_info, control)?
            .incoming)
    }

    fn compute_decompile_family_states_with_control<C: SsaWorkControl + ?Sized>(
        &self,
        family_info: &RegisterFamilyInfo,
        control: &C,
    ) -> Result<DecompileFamilyStates, SsaExecutionStopReason> {
        control.poll()?;
        let mut in_states: HashMap<u64, FamilyRootState> = HashMap::new();
        let mut out_states: HashMap<u64, FamilyRootState> = HashMap::new();

        loop {
            control.poll()?;
            let mut changed = false;

            for &addr in &self.block_order {
                control.poll()?;
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

        control.poll()?;
        Ok(DecompileFamilyStates {
            incoming: in_states,
            outgoing: out_states,
        })
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

        let Some((block_addr, location)) = self.find_def(var) else {
            return (!Self::is_constish_switch_value(var)).then(|| var.clone());
        };
        let DefLocation::Op(op_idx) = location else {
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
        var.is_const() || var.is_memory()
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
        enum DfsStep {
            Enter(u64),
            ExamineEdge { from: u64, to: u64 },
            Exit(u64),
        }

        let mut stack = vec![DfsStep::Enter(block)];
        while let Some(step) = stack.pop() {
            match step {
                DfsStep::Enter(block) => {
                    if !visited.insert(block) {
                        continue;
                    }
                    in_stack.insert(block);
                    stack.push(DfsStep::Exit(block));
                    for succ in self.successors(block).into_iter().rev() {
                        stack.push(DfsStep::ExamineEdge {
                            from: block,
                            to: succ,
                        });
                    }
                }
                DfsStep::ExamineEdge { from, to } => {
                    if in_stack.contains(&to) {
                        back_edges.entry(to).or_default().push(from);
                    } else {
                        stack.push(DfsStep::Enter(to));
                    }
                }
                DfsStep::Exit(block) => {
                    in_stack.remove(&block);
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RegisterFamilySlot {
    family_id: usize,
    offset: u64,
    width: u32,
}

#[derive(Debug, Clone, Copy)]
struct RegisterFamilyMember {
    family_id: usize,
    offset: u64,
    width: u32,
}

#[derive(Debug, Clone, Default)]
struct RegisterFamilyInfo {
    name_to_member: HashMap<String, RegisterFamilyMember>,
    family_widths_by_offset: HashMap<(usize, u64), Vec<u32>>,
    family_slots: HashMap<usize, Vec<RegisterFamilySlot>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RegisterFamilyRoot {
    /// One real SSA definition that contains this storage range.
    value: SSAVar,
    /// Byte offset of the range inside `value`.
    offset: u32,
}

impl RegisterFamilyRoot {
    fn exact(value: SSAVar) -> Self {
        Self { value, offset: 0 }
    }
}

type FamilyRootState = HashMap<RegisterFamilySlot, RegisterFamilyRoot>;

#[derive(Debug, Clone, Default)]
struct DecompileFamilyStates {
    incoming: HashMap<u64, FamilyRootState>,
    outgoing: HashMap<u64, FamilyRootState>,
}

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
    let mut cache = register_family_info_cache()
        .write()
        .expect("register family cache write lock poisoned");
    if let Some(cached) = cache.get(&cache_tag) {
        return Arc::clone(cached);
    }
    if cache.len() >= ARCH_DERIVED_CACHE_MAX_ENTRIES {
        cache.clear();
    }
    cache.insert(cache_tag, info.clone());
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
        let mut family_width_sets: HashMap<(usize, u64), HashSet<u32>> = HashMap::new();

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
                    offset: reg.offset,
                    width: reg.size,
                },
            );
            family_width_sets
                .entry((family_id, reg.offset))
                .or_default()
                .insert(reg.size);
        }

        if arch.name.eq_ignore_ascii_case("x86-64") || arch.name.eq_ignore_ascii_case("x86") {
            seed_x86_low_register_aliases(&mut name_to_member, &mut family_width_sets);
        }

        let family_widths_by_offset: HashMap<(usize, u64), Vec<u32>> = family_width_sets
            .into_iter()
            .map(|(family_and_offset, mut widths)| {
                let mut widths: Vec<u32> = widths.drain().collect();
                widths.sort_unstable();
                (family_and_offset, widths)
            })
            .collect();
        let mut family_slots: HashMap<usize, Vec<RegisterFamilySlot>> = HashMap::new();
        for (&(family_id, offset), widths) in &family_widths_by_offset {
            family_slots
                .entry(family_id)
                .or_default()
                .extend(widths.iter().copied().map(|width| RegisterFamilySlot {
                    family_id,
                    offset,
                    width,
                }));
        }
        for slots in family_slots.values_mut() {
            slots.sort_unstable_by_key(|slot| (slot.offset, slot.width));
            slots.dedup();
        }

        Self {
            name_to_member,
            family_widths_by_offset,
            family_slots,
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

fn seed_x86_low_register_aliases(
    name_to_member: &mut HashMap<String, RegisterFamilyMember>,
    family_width_sets: &mut HashMap<(usize, u64), HashSet<u32>>,
) {
    const GPR_ALIASES: &[&[(&str, u32)]] = &[
        &[("rax", 8), ("eax", 4), ("ax", 2), ("al", 1)],
        &[("rbx", 8), ("ebx", 4), ("bx", 2), ("bl", 1)],
        &[("rcx", 8), ("ecx", 4), ("cx", 2), ("cl", 1)],
        &[("rdx", 8), ("edx", 4), ("dx", 2), ("dl", 1)],
        &[("rsi", 8), ("esi", 4), ("si", 2), ("sil", 1)],
        &[("rdi", 8), ("edi", 4), ("di", 2), ("dil", 1)],
        &[("rbp", 8), ("ebp", 4), ("bp", 2), ("bpl", 1)],
        &[("rsp", 8), ("esp", 4), ("sp", 2), ("spl", 1)],
        &[("r8", 8), ("r8d", 4), ("r8w", 2), ("r8b", 1)],
        &[("r9", 8), ("r9d", 4), ("r9w", 2), ("r9b", 1)],
        &[("r10", 8), ("r10d", 4), ("r10w", 2), ("r10b", 1)],
        &[("r11", 8), ("r11d", 4), ("r11w", 2), ("r11b", 1)],
        &[("r12", 8), ("r12d", 4), ("r12w", 2), ("r12b", 1)],
        &[("r13", 8), ("r13d", 4), ("r13w", 2), ("r13b", 1)],
        &[("r14", 8), ("r14d", 4), ("r14w", 2), ("r14b", 1)],
        &[("r15", 8), ("r15d", 4), ("r15w", 2), ("r15b", 1)],
    ];

    for family in GPR_ALIASES {
        let Some(member) = family
            .iter()
            .find_map(|(name, _)| name_to_member.get(*name).copied())
        else {
            continue;
        };
        let widths = family_width_sets
            .entry((member.family_id, member.offset))
            .or_default();
        for (name, width) in *family {
            widths.insert(*width);
            name_to_member
                .entry((*name).to_string())
                .or_insert(RegisterFamilyMember {
                    family_id: member.family_id,
                    offset: member.offset,
                    width: *width,
                });
        }
    }
}

fn meet_family_states(
    preds: &[u64],
    out_states: &HashMap<u64, FamilyRootState>,
) -> FamilyRootState {
    let mut pred_states = preds.iter().filter_map(|pred| out_states.get(pred));
    let Some(first_state) = pred_states.next() else {
        return HashMap::new();
    };
    let mut merged = first_state.clone();
    for state in pred_states {
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
    let written = RegisterFamilySlot {
        family_id: member.family_id,
        offset: member.offset,
        width: phi.dst.size,
    };
    kill_overlapping_family_roots(state, written);
    seed_family_roots(state, family_info, written, &phi.dst, &phi.dst);
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
    let written = RegisterFamilySlot {
        family_id: member.family_id,
        offset: member.offset,
        width: dst.size,
    };

    let preserved_narrow_roots =
        preserved_narrow_family_roots_for_widening(op, state, family_info, member);
    kill_overlapping_family_roots(state, written);

    match op {
        SSAOp::Copy { src, .. } | SSAOp::Cast { src, .. } | SSAOp::New { src, .. } => {
            let root = adapt_family_root(src, written.width).unwrap_or_else(|| dst.clone());
            let exact_root = if family_slot_is_maximal(family_info, written) {
                dst
            } else {
                &root
            };
            seed_family_roots(state, family_info, written, exact_root, &root);
        }
        SSAOp::IntZExt { src, .. } | SSAOp::IntSExt { src, .. } => {
            seed_family_roots(state, family_info, written, dst, dst);
            for (slot, root) in preserved_narrow_roots {
                state.insert(slot, root);
            }
            if src.size <= written.width {
                state.insert(
                    RegisterFamilySlot {
                        family_id: member.family_id,
                        offset: member.offset,
                        width: src.size,
                    },
                    RegisterFamilyRoot::exact(src.clone()),
                );
            }
        }
        SSAOp::Trunc { src, .. } => {
            let root = if src.is_const() {
                extract_constant_family_slice(src, 0, written.width).unwrap_or_else(|| dst.clone())
            } else {
                dst.clone()
            };
            seed_family_roots(state, family_info, written, &root, &root);
        }
        SSAOp::Subpiece { src, offset, .. } => {
            let root = if src.is_const() {
                extract_constant_family_slice(src, *offset, written.width)
                    .unwrap_or_else(|| dst.clone())
            } else {
                dst.clone()
            };
            seed_family_roots(state, family_info, written, &root, &root);
        }
        _ => {
            seed_family_roots(state, family_info, written, dst, dst);
        }
    }
}

fn preserved_narrow_family_roots_for_widening(
    op: &SSAOp,
    state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
    dst_member: RegisterFamilyMember,
) -> Vec<(RegisterFamilySlot, RegisterFamilyRoot)> {
    let src = match op {
        SSAOp::IntZExt { src, .. } | SSAOp::IntSExt { src, .. } => src,
        _ => return Vec::new(),
    };
    let Some(src_member) = family_info.member_for(src) else {
        return Vec::new();
    };
    if src_member.family_id != dst_member.family_id
        || src_member.offset != dst_member.offset
        || src.size >= dst_member.width
    {
        return Vec::new();
    }
    let Some(widths) = family_info
        .family_widths_by_offset
        .get(&(dst_member.family_id, dst_member.offset))
    else {
        return Vec::new();
    };

    widths
        .iter()
        .copied()
        .filter(|width| *width <= src.size)
        .filter_map(|width| {
            let slot = RegisterFamilySlot {
                family_id: dst_member.family_id,
                offset: dst_member.offset,
                width,
            };
            state.get(&slot).cloned().map(|root| (slot, root))
        })
        .collect()
}

fn materialize_register_alias_sources(
    op: &SSAOp,
    state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
    block_addr: u64,
    op_index: usize,
) -> (Vec<SSAOp>, SSAOp) {
    let mut materialized = Vec::new();
    let mut replacements = HashMap::<SSAVar, SSAVar>::new();
    let op =
        rewrite_decompile_family_subpiece(op, state, family_info).unwrap_or_else(|| op.clone());

    for (source_index, source) in op.sources().into_iter().enumerate() {
        if replacements.contains_key(source) {
            continue;
        }
        let rewritten = rewrite_decompile_family_source(source, state, family_info);
        if rewritten != *source {
            replacements.insert(source.clone(), rewritten);
            continue;
        }
        let Some(member) = family_info.member_for(source) else {
            continue;
        };
        let requested = RegisterFamilySlot {
            family_id: member.family_id,
            offset: member.offset,
            width: source.size,
        };
        let Some(root) = family_root_slice_for_range(state, requested) else {
            continue;
        };
        if let Some(direct) = direct_family_root_value(&root, source.size) {
            if direct != *source {
                replacements.insert(source.clone(), direct);
            }
            continue;
        }
        if root.value == *source && root.offset == 0 {
            continue;
        }
        let extracted = SSAVar::new(
            format!("tmp:regalias:{block_addr:x}:{op_index:x}:{source_index:x}"),
            1,
            source.size,
        );
        materialized.push(SSAOp::Subpiece {
            dst: extracted.clone(),
            src: root.value,
            offset: root.offset,
        });
        replacements.insert(source.clone(), extracted);
    }

    let rewritten = crate::optimize::map_sources_in_op(&op, &|source| {
        replacements
            .get(source)
            .cloned()
            .unwrap_or_else(|| source.clone())
    });
    (materialized, rewritten)
}

fn rewrite_decompile_family_subpiece(
    op: &SSAOp,
    state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> Option<SSAOp> {
    let SSAOp::Subpiece { dst, src, offset } = op else {
        return None;
    };
    let member = family_info.member_for(src)?;
    let requested_end = offset.checked_add(dst.size)?;
    if requested_end > src.size {
        return None;
    }
    let requested = RegisterFamilySlot {
        family_id: member.family_id,
        offset: member.offset.checked_add(u64::from(*offset))?,
        width: dst.size,
    };
    let root = family_root_slice_for_range(state, requested)?;
    if let Some(direct) = direct_family_root_value(&root, dst.size) {
        return Some(SSAOp::Copy {
            dst: dst.clone(),
            src: direct,
        });
    }
    Some(SSAOp::Subpiece {
        dst: dst.clone(),
        src: root.value,
        offset: root.offset,
    })
}

fn family_root_slice_for_range(
    state: &FamilyRootState,
    requested: RegisterFamilySlot,
) -> Option<RegisterFamilyRoot> {
    // A request must have one containing definition. Combining adjacent
    // fragments here would invent a wide value without an explicit Piece.
    state
        .iter()
        .filter(|(slot, _)| family_slot_contains(**slot, requested))
        .filter_map(|(slot, root)| {
            let relative = requested.offset.checked_sub(slot.offset)?;
            let relative = u32::try_from(relative).ok()?;
            let offset = root.offset.checked_add(relative)?;
            offset
                .checked_add(requested.width)
                .filter(|end| *end <= root.value.size)?;
            Some((
                slot.width,
                slot.offset,
                RegisterFamilyRoot {
                    value: root.value.clone(),
                    offset,
                },
            ))
        })
        .min_by_key(|(width, offset, _)| (*width, *offset))
        .map(|(_, _, root)| root)
}

fn rewrite_decompile_family_source(
    src: &SSAVar,
    state: &FamilyRootState,
    family_info: &RegisterFamilyInfo,
) -> SSAVar {
    let Some(member) = family_info.member_for(src) else {
        return src.clone();
    };
    let slot = RegisterFamilySlot {
        family_id: member.family_id,
        offset: member.offset,
        width: src.size,
    };
    if src.version != 0 && member.width == src.size && family_slot_is_maximal(family_info, slot) {
        return src.clone();
    }
    let Some(root) = state.get(&slot) else {
        return src.clone();
    };
    let Some(adapted) = direct_family_root_value(root, src.size) else {
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
    if root.size > width && can_width_adapt_register_family_root(root) {
        return Some(SSAVar::new(root.name.clone(), root.version, width));
    }
    if !root.is_const() {
        return None;
    }
    const_value(root).map(|value| SSAVar::constant(mask_const_to_width(value, width), width))
}

fn direct_family_root_value(root: &RegisterFamilyRoot, width: u32) -> Option<SSAVar> {
    if root.offset == 0 && root.value.size == width {
        return Some(root.value.clone());
    }
    extract_constant_family_slice(&root.value, root.offset, width)
}

fn extract_constant_family_slice(root: &SSAVar, offset: u32, width: u32) -> Option<SSAVar> {
    let value = const_value(root)?;
    offset.checked_add(width).filter(|end| *end <= root.size)?;
    let shift = offset.checked_mul(8)?;
    let shifted = if shift >= u64::BITS {
        0
    } else {
        value >> shift
    };
    Some(SSAVar::constant(mask_const_to_width(shifted, width), width))
}

fn can_width_adapt_register_family_root(root: &SSAVar) -> bool {
    !root.is_const()
        && !root.is_temp()
        && !matches!(
            root.name_kind(),
            SSAVarNameKind::Memory | SSAVarNameKind::AddressSpace
        )
}

fn seed_family_roots(
    state: &mut FamilyRootState,
    family_info: &RegisterFamilyInfo,
    written: RegisterFamilySlot,
    exact_root: &SSAVar,
    contained_root: &SSAVar,
) {
    if exact_root.size != written.width || contained_root.size != written.width {
        return;
    }
    // Views are internal bookkeeping only. A later narrow use emits a real
    // Subpiece before substituting the view into an SSA operation.
    state.insert(written, RegisterFamilyRoot::exact(exact_root.clone()));
    let Some(slots) = family_info.family_slots.get(&written.family_id) else {
        return;
    };
    for &slot in slots {
        if slot == written || !family_slot_contains(written, slot) {
            continue;
        }
        let Some(relative) = slot.offset.checked_sub(written.offset) else {
            continue;
        };
        let Ok(relative) = u32::try_from(relative) else {
            continue;
        };
        state.insert(
            slot,
            RegisterFamilyRoot {
                value: contained_root.clone(),
                offset: relative,
            },
        );
    }
}

fn family_slot_is_maximal(family_info: &RegisterFamilyInfo, slot: RegisterFamilySlot) -> bool {
    family_info
        .family_slots
        .get(&slot.family_id)
        .is_none_or(|slots| {
            !slots
                .iter()
                .any(|candidate| *candidate != slot && family_slot_contains(*candidate, slot))
        })
}

fn kill_overlapping_family_roots(state: &mut FamilyRootState, written: RegisterFamilySlot) {
    state.retain(|slot, _| !family_slots_overlap(*slot, written));
}

fn family_slot_contains(container: RegisterFamilySlot, contained: RegisterFamilySlot) -> bool {
    if container.family_id != contained.family_id || contained.offset < container.offset {
        return false;
    }
    let Some(container_end) = container.offset.checked_add(u64::from(container.width)) else {
        return false;
    };
    let Some(contained_end) = contained.offset.checked_add(u64::from(contained.width)) else {
        return false;
    };
    contained_end <= container_end
}

fn family_slots_overlap(a: RegisterFamilySlot, b: RegisterFamilySlot) -> bool {
    if a.family_id != b.family_id {
        return false;
    }
    let Some(a_end) = a.offset.checked_add(u64::from(a.width)) else {
        return true;
    };
    let Some(b_end) = b.offset.checked_add(u64::from(b.width)) else {
        return true;
    };
    a.offset < b_end && b.offset < a_end
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
        offset: member.offset,
        width: var.size,
    };
    let Some(root) = family_state.get(&slot) else {
        return var.clone();
    };
    direct_family_root_value(root, var.size)
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
        signed_stack_delta(b),
    ) {
        return Some(StackAddressRoot {
            base: base.base,
            offset: base.offset.checked_add(delta)?,
        });
    }
    if let (Some(base), Some(delta)) = (
        stack_root_from_operand(b, roots, stack_roots, family_state, family_info),
        signed_stack_delta(a),
    ) {
        return Some(StackAddressRoot {
            base: base.base,
            offset: base.offset.checked_add(delta)?,
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
    let delta = signed_stack_delta(b)?;
    Some(StackAddressRoot {
        base: base.base,
        offset: base.offset.checked_sub(delta)?,
    })
}

fn signed_stack_delta(var: &SSAVar) -> Option<i64> {
    let value = var.constant_bits()?;
    let bits = var.size.checked_mul(8)?;
    match bits {
        0 => None,
        64 => Some(value as i64),
        1..=63 => {
            let sign = 1u64.checked_shl(bits - 1)?;
            let mask = 1u64.checked_shl(bits)?.wrapping_sub(1);
            let value = value & mask;
            Some(if value & sign == 0 {
                value as i64
            } else {
                (value | !mask) as i64
            })
        }
        _ => None,
    }
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
    use crate::semantic::{
        CallArgumentLocation, CallResultValueRelation, ReturnCarrier, SemanticId, ValueOwner,
    };
    use r2il::{R2ILOp, RegisterDef, SpaceId, SwitchCase, SwitchInfo as R2ILSwitchInfo, Varnode};
    use std::cell::Cell;
    use std::collections::BTreeSet;
    use std::time::{Duration, Instant};

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

    fn make_x86_vector_alias_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("XMM0", 0x100, 16));
        arch.add_register(RegisterDef::sub("XMM0_L0", 0x100, 4, "XMM0"));
        arch.add_register(RegisterDef::sub("XMM0_L1", 0x104, 4, "XMM0"));
        arch.add_register(RegisterDef::sub("XMM0_L2", 0x108, 4, "XMM0"));
        arch.add_register(RegisterDef::sub("XMM0_L3", 0x10c, 4, "XMM0"));
        arch.add_register(RegisterDef::sub("XMM0_LO", 0x100, 8, "XMM0"));
        arch.add_register(RegisterDef::sub("XMM0_MID", 0x104, 8, "XMM0"));
        arch.add_register(RegisterDef::sub("XMM0_HI", 0x108, 8, "XMM0"));
        arch
    }

    fn normalize_manual_vector_alias_ops(ops: Vec<SSAOp>) -> Vec<SSAOp> {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        function.get_block_mut(0x1000).expect("entry block").ops = ops;
        function.normalize_register_alias_sources(&make_x86_vector_alias_arch());
        function.get_block(0x1000).expect("entry block").ops.clone()
    }

    fn vector_loop_alias_arch(prefix: &str) -> ArchSpec {
        let mut arch = ArchSpec::new("range-alias-test");
        let acc = format!("{prefix}_acc");
        let loaded = format!("{prefix}_loaded");
        arch.add_register(RegisterDef::new(&acc, 0x100, 16));
        arch.add_register(RegisterDef::new(format!("{prefix}_acc_a"), 0x100, 4));
        arch.add_register(RegisterDef::new(format!("{prefix}_acc_b"), 0x104, 4));
        arch.add_register(RegisterDef::new(format!("{prefix}_acc_c"), 0x108, 4));
        arch.add_register(RegisterDef::new(format!("{prefix}_acc_d"), 0x10c, 4));
        arch.add_register(RegisterDef::new(&loaded, 0x200, 16));
        arch.add_register(RegisterDef::new(format!("{prefix}_load_a"), 0x200, 4));
        arch.add_register(RegisterDef::new(format!("{prefix}_load_b"), 0x204, 4));
        arch.add_register(RegisterDef::new(format!("{prefix}_load_c"), 0x208, 4));
        arch.add_register(RegisterDef::new(format!("{prefix}_load_d"), 0x20c, 4));
        arch.add_register(RegisterDef::new(format!("{prefix}_return64"), 0x300, 8));
        arch.add_register(RegisterDef::new(format!("{prefix}_return32"), 0x300, 4));
        arch
    }

    fn vector_loop_alias_blocks(base: u64) -> Vec<R2ILBlock> {
        let header = base + 4;
        let exit = base + 8;
        let body = base + 12;
        let mut body_ops = vec![R2ILOp::Load {
            dst: make_reg(0x200, 16),
            space: SpaceId::Ram,
            addr: make_const(0x8000, 8),
        }];
        for lane in 0u64..4 {
            let offset = lane * 4;
            body_ops.push(R2ILOp::IntAdd {
                dst: make_reg(0x100 + offset, 4),
                a: make_reg(0x100 + offset, 4),
                b: make_reg(0x200 + offset, 4),
            });
        }
        body_ops.push(R2ILOp::Branch {
            target: make_const(header, 8),
        });

        vec![
            R2ILBlock {
                addr: base,
                size: 4,
                ops: vec![
                    R2ILOp::IntXor {
                        dst: make_reg(0x100, 16),
                        a: make_reg(0x100, 16),
                        b: make_reg(0x100, 16),
                    },
                    R2ILOp::Branch {
                        target: make_const(header, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: header,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(body, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: exit,
                size: 4,
                ops: vec![
                    R2ILOp::Subpiece {
                        dst: make_reg(0x300, 4),
                        src: make_reg(0x100, 16),
                        offset: 0,
                    },
                    R2ILOp::IntZExt {
                        dst: make_reg(0x300, 8),
                        src: make_reg(0x300, 4),
                    },
                    R2ILOp::Return {
                        target: make_reg(0x300, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: body,
                size: 4,
                ops: body_ops,
                switch_info: None,
                op_metadata: Default::default(),
            },
        ]
    }

    #[test]
    fn graph_value_storage_is_retained_from_varnodes_across_cosmetic_names() {
        fn arch(prefix: &str) -> ArchSpec {
            let mut arch = ArchSpec::new("storage-provenance-test");
            arch.add_register(RegisterDef::new(format!("{prefix}_out"), 0x10, 8));
            arch.add_register(RegisterDef::new(format!("{prefix}_input"), 0x20, 8));
            arch.add_register(RegisterDef::new(format!("{prefix}_return"), 0x30, 8));
            arch
        }

        let blocks = [R2ILBlock {
            addr: 0x2200,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: make_reg(0x10, 8),
                    a: make_reg(0x20, 8),
                    b: make_const(7, 8),
                },
                R2ILOp::Return {
                    target: make_reg(0x30, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let left = SSAFunction::from_blocks_raw(&blocks, Some(&arch("left")))
            .expect("left SSA must build");
        let right = SSAFunction::from_blocks_raw(&blocks, Some(&arch("right")))
            .expect("right SSA must build");
        let left_graph = SsaGraph::from_function(&left);
        let right_graph = SsaGraph::from_function(&right);

        let projection = |graph: &SsaGraph| {
            graph
                .values
                .iter()
                .map(|value| {
                    (
                        value.id,
                        value.var.version,
                        value.var.size,
                        value.canonical_storage,
                        graph.def_inst(value.id),
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(projection(&left_graph), projection(&right_graph));
        assert_ne!(
            left_graph
                .values
                .iter()
                .map(|value| value.var.name.as_str())
                .collect::<Vec<_>>(),
            right_graph
                .values
                .iter()
                .map(|value| value.var.name.as_str())
                .collect::<Vec<_>>()
        );
        let storages = left_graph
            .values
            .iter()
            .map(|value| value.canonical_storage.expect("raw value provenance"))
            .collect::<BTreeSet<_>>();
        assert_eq!(
            storages,
            BTreeSet::from([
                CanonicalStorageId {
                    space: crate::CanonicalStorageSpace::Register,
                    offset: 0x10,
                    size: 8,
                },
                CanonicalStorageId {
                    space: crate::CanonicalStorageSpace::Register,
                    offset: 0x20,
                    size: 8,
                },
                CanonicalStorageId {
                    space: crate::CanonicalStorageSpace::Register,
                    offset: 0x30,
                    size: 8,
                },
                CanonicalStorageId {
                    space: crate::CanonicalStorageSpace::Constant,
                    offset: 7,
                    size: 8,
                },
            ])
        );
    }

    fn assert_vector_loop_alias_provenance(base: u64, prefix: &str) {
        let function = SSAFunction::from_blocks_raw(
            &vector_loop_alias_blocks(base),
            Some(&vector_loop_alias_arch(prefix)),
        )
        .expect("vector loop SSA should build");
        let header = function.get_block(base + 4).expect("loop header");
        let accumulator_phis = header
            .phis
            .iter()
            .filter(|phi| {
                phi.canonical_storage.is_some_and(|storage| {
                    storage.offset >= 0x100 && storage.offset < 0x110 && storage.size == 4
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(accumulator_phis.len(), 4, "one accumulator phi per lane");

        let graph = SsaGraph::from_function(&function);
        for phi in &accumulator_phis {
            assert_eq!(phi.sources.len(), 2);
            for (_, source) in &phi.sources {
                let value = graph.value_id_for_var(source).expect("phi input value");
                assert!(
                    graph.def_inst(value).is_some(),
                    "every lane phi input must have an SSA producer: {source}"
                );
            }
        }

        let entry = function.get_block(base).expect("preheader");
        let zero = entry
            .ops
            .iter()
            .find_map(|op| match op {
                SSAOp::IntXor { dst, .. } if dst.size == 16 => Some(dst.clone()),
                _ => None,
            })
            .expect("wide zero definition");
        let zero_lane_offsets = entry
            .ops
            .iter()
            .filter_map(|op| match op {
                SSAOp::Subpiece { src, offset, dst } if *src == zero && dst.size == 4 => {
                    Some(*offset)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(zero_lane_offsets, vec![0, 4, 8, 12]);

        let body = function.get_block(base + 12).expect("vector body");
        let loaded = body
            .ops
            .iter()
            .find_map(|op| match op {
                SSAOp::Load { dst, .. } if dst.size == 16 => Some(dst.clone()),
                _ => None,
            })
            .expect("wide vector load");
        let loaded_lane_offsets = body
            .ops
            .iter()
            .filter_map(|op| match op {
                SSAOp::Subpiece { src, offset, dst } if *src == loaded && dst.size == 4 => {
                    Some(*offset)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(loaded_lane_offsets, vec![0, 4, 8, 12]);

        let low_phi = accumulator_phis
            .iter()
            .find(|phi| {
                phi.canonical_storage
                    .is_some_and(|storage| storage.offset == 0x100)
            })
            .expect("low-lane phi");
        let exit = function.get_block(base + 8).expect("loop exit");
        assert!(exit.ops.iter().any(|op| matches!(
            op,
            SSAOp::Copy { dst, src }
                if dst.size == 4 && *src == low_phi.dst
        )));
        assert!(
            !function
                .blocks()
                .flat_map(|block| &block.ops)
                .any(|op| matches!(op, SSAOp::Piece { .. }))
        );
    }

    #[test]
    fn decompile_artifact_two_address_stack_updates_read_incoming_versions() {
        let mut arch = make_x86_64_prep_arch();
        arch.add_register(RegisterDef::new("rip", 32, 8));
        let rsp = make_reg(16, 8);
        let rbp = make_reg(24, 8);
        let rip = make_reg(32, 8);
        let saved_fp = make_unique(0x10, 8);
        let restored_fp = make_unique(0x18, 8);
        let return_target = make_unique(0x20, 8);
        let blocks = [R2ILBlock {
            addr: 0x1000,
            size: 9,
            ops: vec![
                R2ILOp::Copy {
                    dst: saved_fp.clone(),
                    src: rbp.clone(),
                },
                R2ILOp::IntSub {
                    dst: rsp.clone(),
                    a: rsp.clone(),
                    b: make_const(8, 8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: rsp.clone(),
                    val: saved_fp,
                },
                R2ILOp::Load {
                    dst: restored_fp.clone(),
                    space: SpaceId::Ram,
                    addr: rsp.clone(),
                },
                R2ILOp::IntAdd {
                    dst: rsp.clone(),
                    a: rsp.clone(),
                    b: make_const(8, 8),
                },
                R2ILOp::Copy {
                    dst: rbp,
                    src: restored_fp,
                },
                R2ILOp::Load {
                    dst: return_target.clone(),
                    space: SpaceId::Ram,
                    addr: rsp.clone(),
                },
                R2ILOp::IntAdd {
                    dst: rsp.clone(),
                    a: rsp,
                    b: make_const(8, 8),
                },
                R2ILOp::Copy {
                    dst: rip,
                    src: return_target,
                },
                R2ILOp::Return {
                    target: make_reg(32, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let interface = SourceFunctionInterface::new_exact(
            b"two-address-stack-updates".to_vec(),
            "sysv",
            [],
            crate::SourceFunctionReturn::Void,
            [],
        )
        .expect("exact source interface");
        let artifact = SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
            .expect("decompile SSA artifact");
        let updates = artifact
            .function()
            .get_block(0x1000)
            .expect("entry block")
            .ops
            .iter()
            .filter_map(|op| match op {
                SSAOp::IntSub { dst, a, .. } | SSAOp::IntAdd { dst, a, .. }
                    if dst.name == "rsp" =>
                {
                    Some((dst.version, a.name.as_str(), a.version))
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        assert_eq!(
            updates,
            vec![(1, "rsp", 0), (2, "rsp", 1), (3, "rsp", 2)],
            "PUSH-, POP-, and RET-like SP updates must read the incoming SSA version"
        );
    }

    fn controlled_prep_blocks() -> Vec<R2ILBlock> {
        vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(1, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(8, 8),
                        src: make_reg(0, 8),
                    },
                    R2ILOp::Return {
                        target: make_ram(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ]
    }

    struct StopAtPoll {
        polls: Cell<usize>,
        stop_at: usize,
        cancellation: crate::SsaCancellationToken,
        execution: crate::SsaExecutionControl,
    }

    impl StopAtPoll {
        fn new(stop_at: usize) -> Self {
            let cancellation = crate::SsaCancellationToken::default();
            let execution = crate::SsaExecutionControl::with_cancellation(cancellation.clone());
            Self {
                polls: Cell::new(0),
                stop_at,
                cancellation,
                execution,
            }
        }
    }

    impl SsaWorkControl for StopAtPoll {
        fn poll(&self) -> Result<(), SsaExecutionStopReason> {
            let polls = self.polls.get() + 1;
            self.polls.set(polls);
            if polls == self.stop_at {
                self.cancellation.cancel();
            }
            self.execution.poll()
        }
    }

    #[test]
    fn checked_decompile_builder_reports_pre_cancelled() {
        let cancellation = crate::SsaCancellationToken::default();
        cancellation.cancel();
        let control = crate::SsaExecutionControl::with_cancellation(cancellation);

        let result =
            SsaArtifact::for_decompile_with_control(&controlled_prep_blocks(), None, &control);

        assert!(matches!(result, Err(SsaPrepareError::Cancelled)));
    }

    #[test]
    fn checked_decompile_builder_reports_expired_deadline() {
        let deadline = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("one millisecond is representable");
        let control = crate::SsaExecutionControl::with_deadline(deadline);

        let result =
            SsaArtifact::for_decompile_with_control(&controlled_prep_blocks(), None, &control);

        assert!(matches!(result, Err(SsaPrepareError::DeadlineExceeded)));
        assert!(matches!(
            SsaArtifact::for_decompile_with_control(
                &[],
                None,
                &crate::SsaExecutionControl::default()
            ),
            Err(SsaPrepareError::MalformedInput)
        ));
    }

    #[test]
    fn checked_decompile_builder_observes_mid_dominator_worklist_cancellation() {
        // Polls 1-3 cover builder/CFG boundaries; poll 6 occurs while the
        // two-entry RPO index is being assembled by the dominator builder.
        let control = StopAtPoll::new(6);

        let result =
            SsaArtifact::for_decompile_with_control(&controlled_prep_blocks(), None, &control);

        assert!(matches!(result, Err(SsaPrepareError::Cancelled)));
        assert_eq!(control.polls.get(), 6);
    }

    #[test]
    fn unchecked_and_controlled_decompile_builders_produce_identical_artifacts() {
        let blocks = controlled_prep_blocks();
        let unchecked = SsaArtifact::for_decompile(&blocks, None).expect("unchecked artifact");
        let controlled = SsaArtifact::for_decompile_with_control(
            &blocks,
            None,
            &crate::SsaExecutionControl::default(),
        )
        .expect("controlled artifact");

        assert_eq!(unchecked.mode(), controlled.mode());
        assert_eq!(
            unchecked.function().block_addrs(),
            controlled.function().block_addrs()
        );
        for (lhs, rhs) in unchecked
            .function()
            .blocks()
            .zip(controlled.function().blocks())
        {
            assert_eq!(lhs.addr, rhs.addr);
            assert_eq!(lhs.size, rhs.size);
            assert_eq!(lhs.ops, rhs.ops);
            assert_eq!(lhs.phis.len(), rhs.phis.len());
            for (lhs_phi, rhs_phi) in lhs.phis.iter().zip(&rhs.phis) {
                assert_eq!(lhs_phi.dst, rhs_phi.dst);
                assert_eq!(lhs_phi.sources, rhs_phi.sources);
                assert_eq!(lhs_phi.canonical_storage, rhs_phi.canonical_storage);
            }
        }
        assert_eq!(
            unchecked.function().decompile_prep_facts(),
            controlled.function().decompile_prep_facts()
        );
        assert_eq!(unchecked.graph(), controlled.graph());
        assert_eq!(unchecked.facts(), controlled.facts());
        assert_eq!(unchecked.machine_context(), controlled.machine_context());
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
    fn architecture_aware_raw_ssa_resolves_register_aliases_at_construction() {
        let arch = make_arm64_alias_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(0x88, 8),
                    src: make_const(0xdead, 8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: make_const(0x4000, 8),
                    val: make_reg(0x88, 4),
                },
                R2ILOp::Return {
                    target: make_ram(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let func = SSAFunction::from_blocks_raw(&blocks, Some(&arch)).expect("raw SSA");
        match &func.entry_block().expect("entry block").ops[1] {
            SSAOp::Store { val, .. } => assert_eq!(val, &SSAVar::constant(0xdead, 4)),
            other => panic!("expected store, got {other:?}"),
        }
    }

    #[test]
    fn decompile_optimization_cannot_delete_register_alias_definition() {
        let arch = make_arm64_alias_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(0x88, 8),
                    src: make_const(0xdead, 8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: make_const(0x4000, 8),
                    val: make_reg(0x88, 4),
                },
                R2ILOp::Return {
                    target: make_ram(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let func =
            SSAFunction::from_blocks_for_decompile(&blocks, Some(&arch)).expect("decompile SSA");
        let store = func
            .entry_block()
            .expect("entry block")
            .ops
            .iter()
            .find_map(|op| match op {
                SSAOp::Store { val, .. } => Some(val),
                _ => None,
            })
            .expect("observable store");
        assert_eq!(store, &SSAVar::constant(0xdead, 4));
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
    fn prepared_function_certifies_only_the_control_return_effect() {
        let arch = make_x86_64_prep_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_const(0x1010, 8),
                    cond: make_reg(8, 8),
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
                        target: make_const(0x1014, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(2, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1014, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1014,
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
        assert_eq!(prepared.certificates().returns.len(), 1);
        assert!(prepared.return_certificate_for_op(0x1014, 0).is_some());
        assert!(prepared.return_certificate_for_op(0x1004, 0).is_none());
        assert!(prepared.return_certificate_for_op(0x1010, 0).is_none());
    }

    #[test]
    fn prepared_function_certifies_unique_return_phi_at_control_return() {
        let blocks = vec![R2ILBlock {
            addr: 0x1114,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let phi_dst = SSAVar::new("RAX", 1, 8);
        function.get_block_mut(0x1114).expect("return block").phis = vec![PhiNode {
            dst: phi_dst.clone(),
            sources: vec![
                (0x1104, SSAVar::constant(7, 8)),
                (0x1110, SSAVar::constant(7, 8)),
            ],
            canonical_storage: None,
        }];
        function.get_block_mut(0x1114).expect("return block").ops = vec![SSAOp::Return {
            target: SSAVar::new("RIP", 1, 8),
        }];

        let prepared = SsaArtifact::new(function, FunctionPrepareMode::Raw);
        let cert = prepared
            .return_certificate_for_op(0x1114, 0)
            .expect("control return should certify unique return phi");
        let value = prepared.value_var(cert.value).expect("return value var");
        assert!(
            value.name.eq_ignore_ascii_case("rax"),
            "control return certificate must bind the return-register phi, got {value:?}"
        );
        assert_eq!(
            cert.carrier,
            Some(ReturnCarrier::Register {
                name: value.name.clone()
            })
        );
        assert!(
            prepared
                .certificates()
                .expressions
                .get(&cert.value)
                .is_some_and(|expr| expr.renderable),
            "identity return phi should carry a renderable expression certificate"
        );
    }

    #[test]
    fn prepared_function_does_not_render_memory_backed_return_phi_at_control_return() {
        let blocks = vec![R2ILBlock {
            addr: 0x1214,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let load = SSAVar::new("tmp:load", 1, 4);
        let phi_dst = SSAVar::new("RAX", 1, 4);
        function.get_block_mut(0x1214).expect("return block").phis = vec![PhiNode {
            dst: phi_dst,
            sources: vec![(0x1204, load.clone()), (0x1210, load.clone())],
            canonical_storage: None,
        }];
        function.get_block_mut(0x1214).expect("return block").ops = vec![
            SSAOp::Load {
                dst: load,
                space: "ram".to_string(),
                addr: SSAVar::new("RDI", 0, 8),
            },
            SSAOp::Return {
                target: SSAVar::new("RIP", 1, 8),
            },
        ];

        let prepared = SsaArtifact::new(function, FunctionPrepareMode::Raw);
        let cert = prepared
            .return_certificate_for_op(0x1214, 1)
            .expect("control return should identify the unique return phi");
        assert!(
            prepared
                .certificates()
                .expressions
                .get(&cert.value)
                .is_some_and(|expr| expr.renderable),
            "memory-backed phi should be renderable; structurer handles rejection"
        );
    }

    #[test]
    fn prepared_function_certifies_stack_reload_at_control_return() {
        let mut arch = make_x86_64_prep_arch();
        arch.add_register(RegisterDef::new("rip", 0x30, 8));
        let slot = make_unique(0x1880, 8);
        let stored = make_unique(0x1888, 8);
        let blocks = vec![
            R2ILBlock {
                addr: 0x1880,
                size: 4,
                ops: vec![
                    R2ILOp::IntAdd {
                        dst: slot.clone(),
                        a: make_reg(24, 8),
                        b: make_const(u64::MAX - 7, 8),
                    },
                    R2ILOp::Call {
                        target: make_const(0x401000, 8),
                    },
                    R2ILOp::Copy {
                        dst: stored.clone(),
                        src: make_reg(0, 8),
                    },
                    R2ILOp::Store {
                        space: SpaceId::Ram,
                        addr: slot.clone(),
                        val: stored,
                    },
                    R2ILOp::Load {
                        dst: make_reg(0, 8),
                        space: SpaceId::Ram,
                        addr: slot,
                    },
                    R2ILOp::Branch {
                        target: make_const(0x1890, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1890,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(0x30, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared =
            SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA should build");
        let return_op_idx = prepared
            .function()
            .get_block(0x1890)
            .and_then(|block| {
                block
                    .ops
                    .iter()
                    .position(|op| matches!(op, SSAOp::Return { target } if target.name.eq_ignore_ascii_case("rip")))
            })
            .expect("control return op");
        let cert = prepared
            .return_certificate_for_op(0x1890, return_op_idx)
            .expect("control return should certify the preceding stack reload");

        assert_eq!(
            cert.carrier,
            Some(ReturnCarrier::Register {
                name: "rax".to_string()
            })
        );
        assert!(
            prepared
                .stack_reload_certificate_for_value(cert.value)
                .is_some_and(|reload| reload.offset == -8),
            "control return value must retain stack reload proof, got {cert:?}"
        );
        assert!(
            prepared
                .call_result_certificate_for_value(cert.value)
                .is_some_and(|call| matches!(
                    call.owner,
                    Some(ValueOwner::StackSlot { offset: -8, .. })
                )),
            "control return value must retain malloc-result stack ownership"
        );
    }

    #[test]
    fn prepared_function_merges_zero_return_with_equal_stack_slot_at_control_return() {
        let mut arch = make_x86_64_prep_arch();
        arch.add_register(RegisterDef::new("rip", 0x30, 8));
        let slot = make_unique(0x1900, 8);
        let cmp_load = make_unique(0x1908, 8);
        let cond = make_unique(0x1910, 1);
        let blocks = vec![
            R2ILBlock {
                addr: 0x1900,
                size: 4,
                ops: vec![
                    R2ILOp::IntAdd {
                        dst: slot.clone(),
                        a: make_reg(24, 8),
                        b: make_const(u64::MAX - 7, 8),
                    },
                    R2ILOp::Store {
                        space: SpaceId::Ram,
                        addr: slot.clone(),
                        val: make_reg(8, 8),
                    },
                    R2ILOp::Load {
                        dst: cmp_load.clone(),
                        space: SpaceId::Ram,
                        addr: slot.clone(),
                    },
                    R2ILOp::IntEqual {
                        dst: cond.clone(),
                        a: cmp_load,
                        b: make_const(0, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1908, 8),
                        cond,
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1904,
                size: 4,
                ops: vec![
                    R2ILOp::Load {
                        dst: make_reg(0, 8),
                        space: SpaceId::Ram,
                        addr: slot,
                    },
                    R2ILOp::Branch {
                        target: make_const(0x190c, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1908,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(0, 8),
                    },
                    R2ILOp::Branch {
                        target: make_const(0x190c, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x190c,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_reg(0x30, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let prepared =
            SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA should build");
        let return_op_idx = prepared
            .function()
            .get_block(0x190c)
            .and_then(|block| {
                block
                    .ops
                    .iter()
                    .position(|op| matches!(op, SSAOp::Return { target } if target.name.eq_ignore_ascii_case("rip")))
            })
            .expect("control return op");
        let cert = prepared
            .return_certificate_for_op(0x190c, return_op_idx)
            .expect("control return should merge equality-proven return values");

        assert!(
            prepared
                .stack_reload_certificate_for_value(cert.value)
                .is_some_and(|reload| reload.offset == -8),
            "merged control return must use the stack-slot value, got {cert:?}"
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
        let call = prepared
            .callsite_certificate_for_op(0x1400, 1)
            .expect("callsite certificate");
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

        let x0_value = prepared
            .graph()
            .value_id_for_var(&post_call_x0)
            .expect("post-call x0 value");
        let x0_cert = prepared
            .call_result_certificate_for_value(x0_value)
            .expect("x0 call-result certificate");
        assert_eq!(x0_cert.block_addr, 0x1400);
        assert_eq!(x0_cert.call_site, call.call_site);
        assert_eq!(
            x0_cert.carrier,
            ReturnCarrier::Register {
                name: "x0".to_string()
            }
        );

        let copied_x8_dst = ops
            .iter()
            .find_map(|op| match op {
                SSAOp::Copy { dst, src } if dst.name == "x8" && src == &post_call_x0 => {
                    Some(dst.clone())
                }
                _ => None,
            })
            .expect("expected x8 alias of the certified call result");
        let copied_x8_value = prepared
            .graph()
            .value_id_for_var(&copied_x8_dst)
            .expect("copied x8 value");
        let copied_x8_cert = prepared
            .call_result_certificate_for_value(copied_x8_value)
            .expect("x8 alias certificate");
        assert_eq!(copied_x8_cert.call_site, call.call_site);
        assert_eq!(copied_x8_cert.owner, Some(ValueOwner::Value(x0_value)));

        for op in ops {
            if let SSAOp::CallDefine { dst } = op
                && dst.name == "x8"
            {
                let x8_call_define_value = prepared
                    .graph()
                    .value_id_for_var(dst)
                    .expect("x8 call-define value");
                assert!(
                    prepared
                        .call_result_certificate_for_value(x8_call_define_value)
                        .is_none(),
                    "caller-saved x8 clobber must not be certified as a return value"
                );
            }
        }
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
    fn resolved_call_target_uses_canonical_copied_const_root_when_fact_is_unresolved() {
        let tmp = Varnode {
            space: SpaceId::Unique,
            offset: 0x10,
            size: 8,
            meta: None,
        };
        let blocks = vec![R2ILBlock {
            addr: 0x1310,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: tmp.clone(),
                    src: make_const(0x401050, 8),
                },
                R2ILOp::CallInd { target: tmp },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let prepared =
            SsaArtifact::for_symbolic(&blocks, None).expect("symbolic prepared SSA should build");
        let call = prepared
            .call_sites()
            .by_id
            .values()
            .next()
            .expect("call site fact");
        assert_eq!(call.direct_target, Some(0x401050));
        assert_eq!(prepared.resolved_call_target(call), Some(0x401050));

        let mut unresolved_fact = call.clone();
        unresolved_fact.direct_target = None;
        assert_eq!(
            prepared.resolved_call_target(&unresolved_fact),
            Some(0x401050),
            "resolved call target must use the prepared canonical copied const root"
        );
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
        let certificates = prepared.certificates();
        assert_eq!(certificates.loops.len(), 1);
        assert!(certificates.switches.is_empty());
        assert!(!certificates.expressions.is_empty());
        assert_eq!(
            certificates.memory_accesses.len(),
            structured.memory_accesses.len()
        );
        assert!(!certificates.returns.is_empty());

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
    fn prepared_certificates_index_call_args_memory_and_returns() {
        let arch = make_arm64_alias_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x1600,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(7, 8),
                },
                R2ILOp::Load {
                    dst: make_reg(0x80, 8),
                    space: SpaceId::Ram,
                    addr: make_const(0x5000, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x2000, 8),
                },
                R2ILOp::Return {
                    target: make_reg(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let prepared = SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA");
        let call = prepared
            .callsite_certificate_for_op(0x1600, 2)
            .expect("callsite certificate");
        assert_eq!(call.block_addr, 0x1600);
        assert_eq!(call.op_index, 2);
        assert_eq!(call.argument_values.len(), 1);
        let arg = prepared
            .value_var(call.argument_values[0])
            .expect("arg value");
        assert!(arg.is_const());
        assert_eq!(call.argument_certificates.len(), 1);
        let typed_arg = &call.argument_certificates[0];
        assert_eq!(typed_arg.index, 0);
        assert_eq!(typed_arg.value, call.argument_values[0]);
        assert!(
            typed_arg.source_inst.is_some(),
            "register call argument proof must identify the producer instruction"
        );
        match &typed_arg.location {
            CallArgumentLocation::Register { name } => assert_eq!(name, "x0"),
            CallArgumentLocation::Stack { .. } => {
                panic!("register argument should not be certified as stack")
            }
        }

        let memory = prepared
            .memory_certificate_for_op_site(0x1600, 1, false)
            .expect("memory certificate");
        assert_eq!(memory.block_addr, 0x1600);
        assert_eq!(memory.op_index, 1);
        assert!(!memory.is_write);

        let return_idx = prepared
            .function()
            .get_block(0x1600)
            .and_then(|block| {
                block
                    .ops
                    .iter()
                    .position(|op| matches!(op, SSAOp::Return { .. }))
            })
            .expect("return op index");
        let ret = prepared
            .return_certificate_for_op(0x1600, return_idx)
            .expect("return certificate");
        assert_eq!(ret.block_addr, 0x1600);
        assert_eq!(ret.op_index, return_idx);
        assert_eq!(ret.width, 8);

        let result = prepared
            .function()
            .get_block(0x1600)
            .and_then(|block| {
                block
                    .ops
                    .iter()
                    .enumerate()
                    .find_map(|(op_idx, op)| match op {
                        SSAOp::CallDefine { dst } if dst.name == "x0" => Some((op_idx, dst)),
                        _ => None,
                    })
            })
            .expect("post-call result op");
        let result_cert = prepared
            .call_result_certificate_for_op(0x1600, result.0)
            .expect("call-result certificate by op");
        assert_eq!(result_cert.call_site, call.call_site);
        assert_eq!(
            result_cert.carrier,
            ReturnCarrier::Register {
                name: "x0".to_string()
            }
        );
        let by_callsite = prepared.call_result_certificates_for_callsite(call.call_site);
        assert!(
            by_callsite
                .iter()
                .any(|cert| cert.value == result_cert.value),
            "callsite index should contain the direct result value"
        );
    }

    #[test]
    fn prepared_call_result_certificates_stop_at_next_call_and_are_stable() {
        let arch = make_x86_64_prep_arch();
        let blocks = vec![R2ILBlock {
            addr: 0x1680,
            size: 4,
            ops: vec![
                R2ILOp::Call {
                    target: make_const(0x401000, 8),
                },
                R2ILOp::Copy {
                    dst: make_unique(0x20, 8),
                    src: make_reg(0, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x402000, 8),
                },
                R2ILOp::Copy {
                    dst: make_unique(0x30, 8),
                    src: make_reg(0, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let first = SsaArtifact::for_decompile(&blocks, Some(&arch))
            .expect("first prepared SSA should build");
        let second = SsaArtifact::for_decompile(&blocks, Some(&arch))
            .expect("second prepared SSA should build");
        assert_eq!(
            first.certificates().call_results,
            second.certificates().call_results,
            "call-result certificates must be deterministic"
        );

        let first_call = first
            .call_sites()
            .by_id
            .values()
            .find(|call| call.direct_target == Some(0x401000))
            .expect("first call");
        let second_call = first
            .call_sites()
            .by_id
            .values()
            .find(|call| call.direct_target == Some(0x402000))
            .expect("second call");
        let aliases = first
            .function()
            .get_block(0x1680)
            .expect("entry block")
            .ops
            .iter()
            .filter_map(|op| match op {
                SSAOp::Copy { dst, .. } if dst.name_kind().is_temporary() => first
                    .graph()
                    .value_id_for_var(dst)
                    .map(|value| (dst.name.clone(), value)),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let first_alias = *aliases.get("tmp:20").expect("first call alias");
        let second_alias = *aliases.get("tmp:30").expect("second call alias");

        let first_values = first
            .certificates()
            .call_results_by_callsite
            .get(&first_call.id)
            .expect("first call result values");
        assert!(first_values.contains(&first_alias));
        assert!(
            !first_values.contains(&second_alias),
            "first call certificate scan must stop at the second call"
        );
        let second_values = first
            .certificates()
            .call_results_by_callsite
            .get(&second_call.id)
            .expect("second call result values");
        assert!(second_values.contains(&second_alias));
    }

    #[test]
    fn prepared_call_result_certifies_stack_store_reload_owner() {
        let arch = make_x86_64_prep_arch();
        let slot = make_unique(0x1780, 8);
        let stored = make_unique(0x1788, 8);
        let loaded = make_unique(0x1790, 8);
        let alias = make_unique(0x1798, 8);
        let truncated = make_unique(0x17a0, 4);
        let blocks = vec![R2ILBlock {
            addr: 0x1780,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: slot.clone(),
                    a: make_reg(24, 8),
                    b: make_const(u64::MAX - 7, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x401000, 8),
                },
                R2ILOp::Copy {
                    dst: stored.clone(),
                    src: make_reg(0, 8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: slot.clone(),
                    val: stored,
                },
                R2ILOp::Load {
                    dst: loaded.clone(),
                    space: SpaceId::Ram,
                    addr: slot,
                },
                R2ILOp::Copy {
                    dst: alias.clone(),
                    src: loaded.clone(),
                },
                R2ILOp::Subpiece {
                    dst: truncated.clone(),
                    src: loaded,
                    offset: 0,
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let prepared =
            SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA should build");
        let alias_var = prepared
            .function()
            .get_block(0x1780)
            .and_then(|block| {
                block.ops.iter().find_map(|op| match op {
                    SSAOp::Copy { dst, .. } if dst.name == "tmp:1798" => Some(dst.clone()),
                    _ => None,
                })
            })
            .expect("reloaded alias");
        let alias_value = prepared
            .graph()
            .value_id_for_var(&alias_var)
            .expect("alias value");
        let cert = prepared
            .call_result_certificate_for_value(alias_value)
            .expect("reloaded alias should have call-result certificate");
        assert_eq!(cert.relation, CallResultValueRelation::Identity);
        assert!(
            matches!(cert.owner, Some(ValueOwner::StackSlot { offset: -8, .. })),
            "reloaded call result should be owned by the frame slot, got {cert:?}"
        );
        let truncated_var = prepared
            .function()
            .get_block(0x1780)
            .and_then(|block| {
                block.ops.iter().find_map(|op| match op {
                    SSAOp::Subpiece { dst, .. } if dst.name == "tmp:17a0" => Some(dst),
                    _ => None,
                })
            })
            .expect("truncated call-result value");
        let truncated_cert = prepared
            .graph()
            .value_id_for_var(truncated_var)
            .and_then(|value| prepared.call_result_certificate_for_value(value))
            .expect("derived call-result certificate");
        assert_eq!(
            truncated_cert.relation,
            CallResultValueRelation::Derived,
            "width-changing transforms must retain provenance without claiming identity"
        );
    }

    #[test]
    fn prepared_stack_reload_certifies_param_home_source_through_extension() {
        let mut arch = make_x86_64_prep_arch();
        arch.add_register(RegisterDef::new("rsi", 32, 8));
        arch.add_register(RegisterDef::new("esi", 32, 4));

        let slot = make_unique(0x1820, 8);
        let loaded = make_unique(0x1828, 4);
        let extended = make_unique(0x1830, 8);
        let blocks = vec![R2ILBlock {
            addr: 0x1820,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: slot.clone(),
                    a: make_reg(24, 8),
                    b: make_const(0xffffffffffffffe0, 8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: slot.clone(),
                    val: make_reg(32, 4),
                },
                R2ILOp::Load {
                    dst: loaded.clone(),
                    space: SpaceId::Ram,
                    addr: slot,
                },
                R2ILOp::IntSExt {
                    dst: extended.clone(),
                    src: loaded,
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let prepared =
            SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA should build");
        let source_value = prepared
            .graph()
            .value_id_for_var(&SSAVar::new("esi", 0, 4))
            .expect("entry esi value");
        let load_cert = prepared
            .stack_reload_certificate_for_op(0x1820, 2)
            .expect("direct stack reload certificate");
        assert_eq!(load_cert.source, source_value);
        assert_eq!(load_cert.canonical_source, source_value);
        assert_eq!(load_cert.base, StackAddressBase::FramePointer);
        assert_eq!(load_cert.offset, -32);
        assert_eq!(load_cert.value_width, 4);
        assert_eq!(load_cert.memory_width, 4);

        let extended_value = prepared
            .graph()
            .value_id_for_var(&SSAVar::new("tmp:1830", 1, 8))
            .expect("extended index value");
        let extended_cert = prepared
            .stack_reload_certificate_for_value(extended_value)
            .expect("extension should carry stack reload source");
        assert_eq!(extended_cert.reload, load_cert.value);
        assert_eq!(extended_cert.source, source_value);
        assert_eq!(extended_cert.canonical_source, source_value);
        assert_eq!(extended_cert.offset, -32);
        assert_eq!(extended_cert.value_width, 8);
        assert_eq!(extended_cert.memory_width, 4);
        assert_eq!(extended_cert.store_access, load_cert.store_access);
        assert_eq!(extended_cert.load_access, load_cert.load_access);
    }

    #[test]
    fn prepared_callsite_certifies_stack_home_arguments() {
        let arch = make_x86_64_prep_arch();
        let stack_home = Varnode {
            space: SpaceId::Unique,
            offset: 0x1740,
            size: 8,
            meta: None,
        };
        let blocks = vec![R2ILBlock {
            addr: 0x1740,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: stack_home.clone(),
                    a: make_reg(16, 8),
                    b: make_const(0x20, 8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: stack_home,
                    val: make_const(7, 8),
                },
                R2ILOp::Call {
                    target: make_const(0x401000, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let prepared =
            SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA should build");
        let call = prepared
            .callsite_certificate_for_op(0x1740, 2)
            .expect("callsite certificate");

        assert_eq!(call.stack_argument_values.len(), 1);
        let stack_arg = &call.stack_argument_values[0];
        assert_eq!(stack_arg.stack_offset, 0x20);
        let value = prepared
            .value_var(stack_arg.value)
            .expect("stack argument value");
        assert!(value.is_const());
        assert_eq!(value.name, "const:7");

        assert_eq!(call.argument_certificates.len(), 1);
        let typed_arg = &call.argument_certificates[0];
        assert_eq!(typed_arg.index, 0);
        assert_eq!(typed_arg.value, stack_arg.value);
        assert_eq!(typed_arg.source_inst, Some(stack_arg.memory_access.inst));
        let memory = prepared
            .memory_certificate_for_op_site(0x1740, 1, true)
            .expect("stack argument write certificate");
        match &typed_arg.location {
            CallArgumentLocation::Stack {
                object,
                offset,
                memory_access,
            } => {
                assert_eq!(*object, memory.object);
                assert_eq!(*offset, 0x20);
                assert_eq!(*memory_access, stack_arg.memory_access);
            }
            CallArgumentLocation::Register { name } => {
                panic!("stack argument should not be certified as register {name}");
            }
        }
    }

    #[test]
    fn prepared_expression_certificates_require_structural_render_proof() {
        let pure_blocks = vec![R2ILBlock {
            addr: 0x1700,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(7, 8),
                },
                R2ILOp::IntAdd {
                    dst: make_reg(8, 8),
                    a: make_reg(0, 8),
                    b: make_const(1, 8),
                },
                R2ILOp::Return {
                    target: make_reg(8, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let pure = SsaArtifact::raw(&pure_blocks, None).expect("pure SSA");
        let pure_ret = pure
            .return_certificate_for_op(0x1700, 2)
            .expect("pure return certificate");
        assert!(
            pure.certificates()
                .expressions
                .get(&pure_ret.value)
                .is_some_and(|cert| cert.renderable),
            "pure expression outputs should be renderable"
        );

        let load_blocks = vec![R2ILBlock {
            addr: 0x1710,
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
        }];
        let loaded = SsaArtifact::raw(&load_blocks, None).expect("load SSA");
        let loaded_ret = loaded
            .return_certificate_for_op(0x1710, 1)
            .expect("loaded return certificate");
        assert!(
            loaded
                .certificates()
                .expressions
                .get(&loaded_ret.value)
                .is_some_and(|cert| cert.renderable),
            "memory-load expression outputs require a structured memory-read certificate"
        );

        let userop_out = Varnode {
            space: SpaceId::Unique,
            offset: 0x2222,
            size: 8,
            meta: None,
        };
        let userop_blocks = vec![R2ILBlock {
            addr: 0x1720,
            size: 4,
            ops: vec![
                R2ILOp::CallOther {
                    output: Some(userop_out.clone()),
                    userop: 99,
                    inputs: vec![make_reg(0, 8)],
                },
                R2ILOp::Return { target: userop_out },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let userop = SsaArtifact::raw(&userop_blocks, None).expect("userop SSA");
        let userop_ret = userop
            .return_certificate_for_op(0x1720, 1)
            .expect("userop return certificate");
        assert!(
            userop
                .certificates()
                .expressions
                .get(&userop_ret.value)
                .is_some_and(|cert| !cert.renderable),
            "opaque userop outputs must not be renderable by width alone"
        );
    }

    #[test]
    fn prepared_return_register_subpiece_zext_chain_is_renderable() {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0x00, 8));
        arch.add_register(RegisterDef::new("eax", 0x00, 4));
        arch.add_register(RegisterDef::new("rsi", 0x10, 8));
        arch.add_register(RegisterDef::new("esi", 0x10, 4));
        arch.add_register(RegisterDef::new("rdx", 0x18, 8));
        arch.add_register(RegisterDef::new("edx", 0x18, 4));
        arch.add_register(RegisterDef::new("rip", 0x20, 8));

        let blocks = vec![R2ILBlock {
            addr: 0x1740,
            size: 4,
            ops: vec![
                R2ILOp::IntAdd {
                    dst: make_unique(0x4000, 8),
                    a: make_reg(0x18, 8),
                    b: make_reg(0x10, 8),
                },
                R2ILOp::Subpiece {
                    dst: make_reg(0x00, 4),
                    src: make_unique(0x4000, 8),
                    offset: 0,
                },
                R2ILOp::IntZExt {
                    dst: make_reg(0x00, 8),
                    src: make_reg(0x00, 4),
                },
                R2ILOp::Return {
                    target: make_reg(0x20, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let prepared = SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA");
        let ret = prepared
            .certificates()
            .returns
            .iter()
            .find(|cert| {
                cert.block_addr == 0x1740
                    && prepared
                        .value_var(cert.value)
                        .is_some_and(|var| var.name.eq_ignore_ascii_case("rax"))
            })
            .expect("return-register certificate");

        let expr_cert = prepared
            .certificates()
            .expressions
            .get(&ret.value)
            .expect("return value expression certificate");
        let input_debug = expr_cert
            .inputs
            .iter()
            .map(|value| {
                let name = prepared
                    .value_var(*value)
                    .map(|var| var.display_name())
                    .unwrap_or_else(|| "<unknown>".to_string());
                let renderable = prepared
                    .certificates()
                    .expressions
                    .get(value)
                    .is_some_and(|cert| cert.renderable);
                format!("{name}:{renderable}")
            })
            .collect::<Vec<_>>();
        let mut tmp_debug = Vec::new();
        for value in &expr_cert.inputs {
            if let Some(cert) = prepared.certificates().expressions.get(value) {
                let value_name = prepared
                    .value_var(*value)
                    .map(|var| var.display_name())
                    .unwrap_or_else(|| "<unknown>".to_string());
                for input in &cert.inputs {
                    let input_name = prepared
                        .value_var(*input)
                        .map(|var| var.display_name())
                        .unwrap_or_else(|| "<unknown>".to_string());
                    let renderable = prepared
                        .certificates()
                        .expressions
                        .get(input)
                        .is_some_and(|cert| cert.renderable);
                    tmp_debug.push(format!("{value_name}->{input_name}:{renderable}"));
                }
            }
        }
        assert!(
            expr_cert.renderable,
            "return-register subpiece/zext chain should be renderable; ret={:?} inputs={:?} tmp_inputs={:?}",
            prepared.value_var(ret.value),
            input_debug,
            tmp_debug
        );
    }

    #[test]
    fn prepared_return_certificates_exclude_predecessor_register_writes() {
        let arch = make_x86_64_prep_arch();
        let blocks = vec![
            R2ILBlock {
                addr: 0x1760,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(7, 8),
                    },
                    R2ILOp::Branch {
                        target: Varnode::ram(0x1770, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1770,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_reg(0, 8),
                        src: make_const(9, 8),
                    },
                    R2ILOp::Return {
                        target: make_reg(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let prepared = SsaArtifact::for_decompile(&blocks, Some(&arch)).expect("prepared SSA");

        assert_eq!(prepared.certificates().returns.len(), 1);
        assert!(prepared.return_certificate_for_op(0x1770, 1).is_some());
        assert!(
            prepared.return_certificate_for_op(0x1760, 0).is_none(),
            "a predecessor return-register write is dataflow, not a return effect"
        );
    }

    #[test]
    fn prepared_expression_certificates_render_only_identity_phis() {
        fn prepared_with_phi_sources(sources: Vec<SSAVar>) -> SsaArtifact {
            let blocks = vec![R2ILBlock {
                addr: 0x1730,
                size: 4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }];
            let mut function =
                SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
            let phi_dst = SSAVar::new("reg:0", 1, 8);
            let phi_sources = sources
                .into_iter()
                .enumerate()
                .map(|(index, source)| (0x1720 + (index as u64 * 4), source))
                .collect();
            let block = function.get_block_mut(0x1730).expect("merge block");
            block.phis = vec![PhiNode {
                dst: phi_dst.clone(),
                sources: phi_sources,
                canonical_storage: None,
            }];
            block.ops = vec![SSAOp::Return { target: phi_dst }];
            SsaArtifact::new(function, FunctionPrepareMode::Raw)
        }

        let same_source = SSAVar::constant(7, 8);
        let identity_phi = prepared_with_phi_sources(vec![same_source.clone(), same_source]);
        let identity_ret = identity_phi
            .return_certificate_for_op(0x1730, 0)
            .expect("identity phi return certificate");
        assert!(
            identity_phi
                .certificates()
                .expressions
                .get(&identity_ret.value)
                .is_some_and(|cert| cert.renderable),
            "identity phi over one renderable ValueId should be renderable"
        );

        let mixed_phi =
            prepared_with_phi_sources(vec![SSAVar::constant(7, 8), SSAVar::constant(9, 8)]);
        let mixed_ret = mixed_phi
            .return_certificate_for_op(0x1730, 0)
            .expect("mixed phi return certificate");
        assert!(
            mixed_phi
                .certificates()
                .expressions
                .get(&mixed_ret.value)
                .is_some_and(|cert| cert.renderable),
            "non-memory phi with sibling values should be renderable; divergence handled by structurer"
        );
    }

    #[test]
    fn prepared_expression_certificates_render_loop_carried_recurrence_phi() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1800,
                size: 0x10,
                ops: vec![R2ILOp::Branch {
                    target: make_ram(0x1810, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1810,
                size: 0x4,
                ops: vec![R2ILOp::CBranch {
                    target: make_ram(0x1820, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1814,
                size: 0x4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1820,
                size: 0x4,
                ops: vec![R2ILOp::Branch {
                    target: make_ram(0x1810, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let mut function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let init = SSAVar::new("RAX", 0, 8);
        let phi = SSAVar::new("RAX", 2, 8);
        let update_source = SSAVar::new("tmp:update", 1, 8);
        let update = SSAVar::new("RAX", 3, 8);
        function.get_block_mut(0x1810).expect("loop header").phis = vec![PhiNode {
            dst: phi.clone(),
            sources: vec![(0x1800, init), (0x1820, update.clone())],
            canonical_storage: None,
        }];
        function.get_block_mut(0x1820).expect("loop latch").ops = vec![
            SSAOp::IntAdd {
                dst: update_source.clone(),
                a: phi.clone(),
                b: SSAVar::constant(1, 8),
            },
            SSAOp::Copy {
                dst: update,
                src: update_source.clone(),
            },
            SSAOp::Branch {
                target: SSAVar::new("ram:1810", 0, 8),
            },
        ];
        function.get_block_mut(0x1814).expect("loop exit").ops = vec![SSAOp::Return {
            target: phi.clone(),
        }];

        let prepared = SsaArtifact::new(function, FunctionPrepareMode::Raw);
        let carrier = prepared
            .structured()
            .loops
            .values()
            .flat_map(|loop_fact| loop_fact.carriers.iter())
            .find(|carrier| carrier.phi == prepared.graph().value_id_for_var(&phi).unwrap())
            .expect("loop-carried phi fact");
        assert_eq!(carrier.id, SemanticId::loop_carrier(carrier.phi));
        assert_eq!(carrier.entries.len(), 1);
        assert_eq!(carrier.updates.len(), 1);
        assert!(
            carrier.updates[0]
                .identity_values
                .contains(&prepared.graph().value_id_for_var(&update_source).unwrap()),
            "same-width copy sources retain exact update identity at the latch program point"
        );
        assert!(carrier.identity_values.contains(&carrier.phi));
        let ret = prepared
            .return_certificate_for_op(0x1814, 0)
            .expect("loop-carried return certificate");
        assert!(
            prepared
                .certificates()
                .expressions
                .get(&ret.value)
                .is_some_and(|cert| cert.renderable),
            "loop-header phi is renderable when the loop certificate proves the backedge and the update is pure modulo that phi"
        );
    }

    #[test]
    fn prepared_predicates_preserve_machine_point_comparison_before_normalization() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1900,
                size: 0x4,
                ops: vec![R2ILOp::CBranch {
                    target: make_ram(0x1910, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1904,
                size: 0x4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1910,
                size: 0x4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let mut function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let before = SSAVar::new("RAX", 0, 8);
        let one = SSAVar::constant(1, 8);
        let updated = SSAVar::new("tmp:updated", 1, 8);
        let zero = SSAVar::constant(0, 8);
        let condition = SSAVar::new("tmp:condition", 1, 1);
        function.get_block_mut(0x1900).expect("branch block").ops = vec![
            SSAOp::IntSub {
                dst: updated.clone(),
                a: before.clone(),
                b: one.clone(),
            },
            SSAOp::IntNotEqual {
                dst: condition.clone(),
                a: updated.clone(),
                b: zero.clone(),
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1910", 0, 8),
                cond: condition,
            },
        ];

        let prepared = SsaArtifact::new(function, FunctionPrepareMode::Raw);
        let predicate = prepared
            .predicates()
            .predicates
            .values()
            .find(|predicate| predicate.block_addr == 0x1900)
            .expect("branch predicate");
        let normalized = predicate
            .comparison
            .as_ref()
            .expect("normalized comparison");
        assert_eq!(normalized.kind, crate::CompareKind::NotEqual);
        assert_eq!(
            normalized.lhs,
            prepared.graph().value_id_for_var(&before).unwrap()
        );
        assert_eq!(
            normalized.rhs,
            prepared.graph().value_id_for_var(&one).unwrap()
        );
        let evaluated = predicate
            .evaluated_comparison
            .as_ref()
            .expect("machine-point comparison");
        assert_eq!(evaluated.kind, crate::CompareKind::NotEqual);
        assert_eq!(
            evaluated.lhs,
            prepared.graph().value_id_for_var(&updated).unwrap()
        );
        assert_eq!(
            evaluated.rhs,
            prepared.graph().value_id_for_var(&zero).unwrap()
        );
    }

    #[test]
    fn prepared_predicates_recover_signed_greater_equal_from_x86_flags() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1920,
                size: 0x4,
                ops: vec![R2ILOp::CBranch {
                    target: make_ram(0x1930, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1924,
                size: 0x4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1930,
                size: 0x4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let mut function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let lhs = SSAVar::new("EAX", 0, 4);
        let rhs = SSAVar::new("ECX", 0, 4);
        let difference = SSAVar::new("tmp:difference", 1, 4);
        let overflow = SSAVar::new("OF", 1, 1);
        let sign = SSAVar::new("SF", 1, 1);
        let condition = SSAVar::new("tmp:condition", 1, 1);
        function.get_block_mut(0x1920).expect("branch block").ops = vec![
            SSAOp::IntSBorrow {
                dst: overflow.clone(),
                a: lhs.clone(),
                b: rhs.clone(),
            },
            SSAOp::IntSub {
                dst: difference.clone(),
                a: lhs.clone(),
                b: rhs.clone(),
            },
            SSAOp::IntSLess {
                dst: sign.clone(),
                a: difference,
                b: SSAVar::constant(0, 4),
            },
            SSAOp::IntEqual {
                dst: condition.clone(),
                a: overflow,
                b: sign,
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1930", 0, 8),
                cond: condition,
            },
        ];

        let prepared = SsaArtifact::new(function, FunctionPrepareMode::Raw);
        let comparison = prepared
            .predicates()
            .predicates
            .values()
            .find(|predicate| predicate.block_addr == 0x1920)
            .and_then(|predicate| predicate.comparison.as_ref())
            .expect("signed flag comparison");

        assert_eq!(comparison.kind, crate::CompareKind::SignedLessEqual);
        assert_eq!(
            comparison.lhs,
            prepared.graph().value_id_for_var(&rhs).unwrap(),
            "OF == SF means rhs <= lhs"
        );
        assert_eq!(
            comparison.rhs,
            prepared.graph().value_id_for_var(&lhs).unwrap()
        );
    }

    #[test]
    fn loop_carrier_certifies_dominating_initializer_for_zero_iteration_exit() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1a00,
                size: 0x10,
                ops: vec![R2ILOp::CBranch {
                    target: make_ram(0x1a30, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1a10,
                size: 0x10,
                ops: vec![R2ILOp::Branch {
                    target: make_ram(0x1a20, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1a20,
                size: 0x10,
                ops: vec![R2ILOp::CBranch {
                    target: make_ram(0x1a20, 8),
                    cond: make_const(1, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1a30,
                size: 0x4,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let mut function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let init = SSAVar::new("RAX", 0, 8);
        let phi = SSAVar::new("RAX", 2, 8);
        let update_source = SSAVar::new("tmp:update", 1, 8);
        let update = SSAVar::new("RAX", 3, 8);
        let result = SSAVar::new("RAX", 4, 8);
        function.get_block_mut(0x1a20).expect("loop header").phis = vec![PhiNode {
            dst: phi.clone(),
            sources: vec![(0x1a10, init.clone()), (0x1a20, update.clone())],
            canonical_storage: None,
        }];
        function.get_block_mut(0x1a20).expect("loop header").ops = vec![
            SSAOp::IntAdd {
                dst: update_source.clone(),
                a: phi.clone(),
                b: SSAVar::constant(1, 8),
            },
            SSAOp::Copy {
                dst: update.clone(),
                src: update_source,
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1a20", 0, 8),
                cond: SSAVar::constant(1, 1),
            },
        ];
        function.get_block_mut(0x1a30).expect("loop exit").phis = vec![PhiNode {
            dst: result.clone(),
            sources: vec![(0x1a00, init.clone()), (0x1a20, update)],
            canonical_storage: None,
        }];
        function.get_block_mut(0x1a30).expect("loop exit").ops = vec![SSAOp::Return {
            target: result.clone(),
        }];

        let prepared = SsaArtifact::new(function, FunctionPrepareMode::Raw);
        let phi_value = prepared.graph().value_id_for_var(&phi).unwrap();
        let init_value = prepared.graph().value_id_for_var(&init).unwrap();
        let result_value = prepared.graph().value_id_for_var(&result).unwrap();
        let carrier = prepared
            .structured()
            .loops
            .values()
            .flat_map(|loop_fact| loop_fact.carriers.iter())
            .find(|carrier| carrier.phi == phi_value)
            .expect("loop carrier");
        assert!(carrier.identity_values.contains(&result_value));
        assert_eq!(
            carrier.dominating_initializers,
            vec![crate::LoopCarrierEdgeValue {
                predecessor: 0x1a00,
                value: init_value,
            }]
        );
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
    fn producerless_switch_selector_is_retained_as_a_leaf() {
        let mut selector = R2ILBlock::new(0x1080, 4);
        selector.push(R2ILOp::BranchInd {
            target: make_reg(8, 8),
        });
        selector.set_switch_info(R2ILSwitchInfo {
            switch_addr: 0x1080,
            min_val: 1,
            max_val: 2,
            default_target: Some(0x10b0),
            cases: vec![
                SwitchCase {
                    value: 1,
                    target: 0x1090,
                },
                SwitchCase {
                    value: 2,
                    target: 0x10a0,
                },
            ],
        });
        let arms = [0x1090, 0x10a0, 0x10b0].map(|addr| {
            let mut block = R2ILBlock::new(addr, 4);
            block.push(R2ILOp::Return {
                target: make_reg(16, 8),
            });
            block
        });
        let artifact = SsaArtifact::raw(
            &[selector, arms[0].clone(), arms[1].clone(), arms[2].clone()],
            None,
        )
        .expect("switch artifact");
        let certificate = artifact
            .certificates()
            .switches
            .get(&0x1080)
            .expect("switch certificate");
        let selector = certificate.selector.expect("producerless selector leaf");
        let value = artifact
            .graph()
            .value(selector)
            .expect("selector graph value");
        assert_eq!(value.var.size, 8);
        let branch = artifact
            .graph()
            .insts
            .iter()
            .find(|instruction| {
                matches!(
                    instruction.payload,
                    crate::graph::InstPayload::Op(SSAOp::BranchInd { .. })
                )
            })
            .expect("branch instruction");
        assert_eq!(branch.inputs, vec![selector]);
    }

    #[test]
    fn public_ssa_path_handles_a_deep_cycle_and_reports_its_back_edge() {
        const BLOCK_COUNT: usize = 8_192;
        const BASE: u64 = 0x10_0000;

        let blocks = (0..BLOCK_COUNT)
            .map(|index| R2ILBlock {
                addr: BASE + index as u64 * 4,
                size: 4,
                ops: if index + 1 == BLOCK_COUNT {
                    vec![R2ILOp::Branch {
                        target: make_const(BASE, 8),
                    }]
                } else {
                    vec![R2ILOp::Nop]
                },
                switch_info: None,
                op_metadata: Default::default(),
            })
            .collect::<Vec<_>>();
        let expected_order = blocks.iter().map(|block| block.addr).collect::<Vec<_>>();
        let latch = BASE + (BLOCK_COUNT as u64 - 1) * 4;

        let function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("SSA for deep cyclic CFG");
        let risk = function.cfg_risk_summary();

        assert_eq!(function.block_addrs(), expected_order);
        assert_eq!(risk.block_count, BLOCK_COUNT);
        assert_eq!(risk.loop_count, 1);
        assert_eq!(risk.back_edge_count, 1);
        assert_eq!(function.collect_back_edges().get(&BASE), Some(&vec![latch]));
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
    fn noncarrier_use_follows_copy_and_phi_chains() {
        let blocks = [R2ILBlock::new(0x1000, 4), R2ILBlock::new(0x1004, 4)];
        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA function");
        let source = SSAVar::new("flag", 1, 1);
        let copied = SSAVar::new("flag", 2, 1);
        let merged = SSAVar::new("flag", 3, 1);
        let forwarded = SSAVar::new("flag", 4, 1);
        func.get_block_mut(0x1000).expect("copy block").ops = vec![SSAOp::Copy {
            dst: copied.clone(),
            src: source.clone(),
        }];
        let merge = func.get_block_mut(0x1004).expect("merge block");
        merge.phis = vec![PhiNode {
            dst: merged.clone(),
            sources: vec![(0x1000, copied)],
            canonical_storage: None,
        }];
        merge.ops = vec![SSAOp::Copy {
            dst: forwarded.clone(),
            src: merged,
        }];

        assert!(!func.has_noncarrier_use(&source));

        func.get_block_mut(0x1004)
            .expect("consumer block")
            .ops
            .push(SSAOp::Return { target: forwarded });

        assert!(func.has_noncarrier_use(&source));
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
                canonical_storage: None,
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
    fn vector_alias_wide_definition_materializes_nonzero_lane_offsets() {
        let ops = normalize_manual_vector_alias_ops(vec![
            SSAOp::IntXor {
                dst: SSAVar::new("XMM0", 1, 16),
                a: SSAVar::new("XMM0", 0, 16),
                b: SSAVar::new("XMM0", 0, 16),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:low", 1, 4),
                src: SSAVar::new("XMM0_L0", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:high", 1, 4),
                src: SSAVar::new("XMM0_L2", 7, 4),
            },
        ]);

        assert_eq!(ops.len(), 5);
        match &ops[1] {
            SSAOp::Subpiece { src, offset, .. } => {
                assert_eq!(src, &SSAVar::new("XMM0", 1, 16));
                assert_eq!(*offset, 0);
            }
            other => panic!("expected low-lane extraction, got {other:?}"),
        }
        match &ops[3] {
            SSAOp::Subpiece { src, offset, .. } => {
                assert_eq!(src, &SSAVar::new("XMM0", 1, 16));
                assert_eq!(*offset, 8);
            }
            other => panic!("expected nonzero lane extraction, got {other:?}"),
        }
        assert!(ops.iter().skip(1).all(|op| {
            op.sources()
                .into_iter()
                .all(|src| src.name != "XMM0_L0" && src.name != "XMM0_L2")
        }));
    }

    #[test]
    fn vector_alias_loop_edges_keep_exact_lane_producers_across_names_and_relocation() {
        assert_vector_loop_alias_provenance(0x1000, "first_names");
        assert_vector_loop_alias_provenance(0x7fff_4000, "renamed_registers");
    }

    #[test]
    fn register_alias_maximal_copy_retains_the_written_ssa_definition() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::sub("EAX", 0, 4, "RAX"));

        let mut function =
            SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        function.get_block_mut(0x1000).expect("entry block").ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("RAX", 2, 8),
                src: SSAVar::constant(0x33, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:returned", 1, 8),
                src: SSAVar::new("RAX", 0, 8),
            },
        ];

        function.normalize_register_alias_sources(&arch);

        let ops = &function.get_block(0x1000).expect("entry block").ops;
        assert_eq!(ops.len(), 2);
        match &ops[1] {
            SSAOp::Copy { src, .. } => assert_eq!(src, &SSAVar::new("RAX", 2, 8)),
            other => panic!("expected maximal-register copy, got {other:?}"),
        }
    }

    #[test]
    fn vector_alias_narrow_write_preserves_disjoint_lane_roots() {
        let ops = normalize_manual_vector_alias_ops(vec![
            SSAOp::Copy {
                dst: SSAVar::new("XMM0", 1, 16),
                src: SSAVar::new("tmp:wide", 1, 16),
            },
            SSAOp::Copy {
                dst: SSAVar::new("XMM0_L2", 1, 4),
                src: SSAVar::new("tmp:new_l2", 1, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:read_l0", 1, 4),
                src: SSAVar::new("XMM0_L0", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:read_l2", 1, 4),
                src: SSAVar::new("XMM0_L2", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:read_l3", 1, 4),
                src: SSAVar::new("XMM0_L3", 0, 4),
            },
        ]);

        let lane_slices = ops
            .iter()
            .filter_map(|op| match op {
                SSAOp::Subpiece { src, offset, .. } if src.name == "tmp:wide" => Some(*offset),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(lane_slices, vec![0, 12]);
        let updated_lane_read = ops.iter().find_map(|op| match op {
            SSAOp::Copy { dst, src } if dst.name == "tmp:read_l2" => Some(src),
            _ => None,
        });
        assert_eq!(updated_lane_read, Some(&SSAVar::new("tmp:new_l2", 1, 4)));
    }

    #[test]
    fn vector_alias_subpiece_uses_exact_updated_lane_without_stale_wide_live_in() {
        let ops = normalize_manual_vector_alias_ops(vec![
            SSAOp::Copy {
                dst: SSAVar::new("XMM0", 1, 16),
                src: SSAVar::new("tmp:wide", 1, 16),
            },
            SSAOp::Copy {
                dst: SSAVar::new("XMM0_L2", 1, 4),
                src: SSAVar::new("tmp:new_l2", 1, 4),
            },
            SSAOp::Subpiece {
                dst: SSAVar::new("tmp:extracted_l2", 1, 4),
                src: SSAVar::new("XMM0", 0, 16),
                offset: 8,
            },
        ]);

        assert_eq!(ops.len(), 3);
        match &ops[2] {
            SSAOp::Copy { dst, src } => {
                assert_eq!(dst, &SSAVar::new("tmp:extracted_l2", 1, 4));
                assert_eq!(src, &SSAVar::new("tmp:new_l2", 1, 4));
            }
            other => panic!("expected exact updated-lane copy, got {other:?}"),
        }
        assert!(ops[2].sources().into_iter().all(|src| src.name != "XMM0"));
    }

    #[test]
    fn vector_alias_overlapping_write_invalidates_only_affected_ranges() {
        let ops = normalize_manual_vector_alias_ops(vec![
            SSAOp::Copy {
                dst: SSAVar::new("XMM0", 1, 16),
                src: SSAVar::new("tmp:wide", 1, 16),
            },
            SSAOp::Copy {
                dst: SSAVar::new("XMM0_MID", 1, 8),
                src: SSAVar::new("tmp:new_mid", 1, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:unaffected_low", 1, 4),
                src: SSAVar::new("XMM0_L0", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:affected_low_half", 1, 8),
                src: SSAVar::new("XMM0_LO", 0, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:unaffected_high", 1, 4),
                src: SSAVar::new("XMM0_L3", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:unresolved_whole", 1, 16),
                src: SSAVar::new("XMM0", 0, 16),
            },
        ]);

        assert!(ops.iter().any(|op| matches!(
            op,
            SSAOp::Subpiece { src, offset: 0, .. } if src.name == "tmp:wide"
        )));
        assert!(ops.iter().any(|op| matches!(
            op,
            SSAOp::Subpiece { src, offset: 12, .. } if src.name == "tmp:wide"
        )));
        let unresolved_overlap = ops.iter().find_map(|op| match op {
            SSAOp::Copy { dst, src } if dst.name == "tmp:affected_low_half" => Some(src),
            _ => None,
        });
        assert_eq!(unresolved_overlap, Some(&SSAVar::new("XMM0_LO", 0, 8)));
        let unresolved_whole = ops.iter().find_map(|op| match op {
            SSAOp::Copy { dst, src } if dst.name == "tmp:unresolved_whole" => Some(src),
            _ => None,
        });
        assert_eq!(unresolved_whole, Some(&SSAVar::new("XMM0", 0, 16)));
        assert!(!ops.iter().any(|op| matches!(op, SSAOp::Piece { .. })));
    }

    #[test]
    fn vector_alias_final_low_lane_survives_disjoint_lane_updates() {
        let ops = normalize_manual_vector_alias_ops(vec![
            SSAOp::IntXor {
                dst: SSAVar::new("XMM0", 1, 16),
                a: SSAVar::new("XMM0", 0, 16),
                b: SSAVar::new("XMM0", 0, 16),
            },
            SSAOp::Copy {
                dst: SSAVar::new("XMM0_L1", 1, 4),
                src: SSAVar::new("tmp:new_l1", 1, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("XMM0_L2", 1, 4),
                src: SSAVar::new("tmp:new_l2", 1, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("XMM0_L3", 1, 4),
                src: SSAVar::new("tmp:new_l3", 1, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:final_low", 1, 4),
                src: SSAVar::new("XMM0_L0", 0, 4),
            },
        ]);

        let final_low = ops
            .windows(2)
            .find_map(|window| match (&window[0], &window[1]) {
                (SSAOp::Subpiece { src, offset, .. }, SSAOp::Copy { dst, .. })
                    if dst.name == "tmp:final_low" =>
                {
                    Some((src, *offset))
                }
                _ => None,
            })
            .expect("final low-lane extraction");
        assert_eq!(final_low, (&SSAVar::new("XMM0", 1, 16), 0));
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

        func.normalize_register_alias_sources(&make_arm64_alias_arch());

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

        func.normalize_register_alias_sources(&make_arm64_alias_arch());

        let ops = &func.get_block(0x1000).expect("entry block").ops;
        let extracted = match &ops[1] {
            SSAOp::Subpiece { dst, src, offset } => {
                assert_eq!(src, &SSAVar::new("x8", 1, 8));
                assert_eq!(*offset, 0);
                dst.clone()
            }
            other => panic!("expected explicit narrow alias extraction, got {other:?}"),
        };
        match &ops[2] {
            SSAOp::IntRight { a, .. } => assert_eq!(a, &extracted),
            other => panic!("expected IntRight, got {other:?}"),
        }
    }

    #[test]
    fn test_decompile_normalization_seeds_missing_x86_low_byte_alias() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("EAX", 0x00, 4));

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let block = func.get_block_mut(0x1000).expect("entry block");
        block.ops = vec![
            SSAOp::IntZExt {
                dst: SSAVar::new("EAX", 1, 4),
                src: SSAVar::new("tmp:loaded_byte", 1, 1),
            },
            SSAOp::IntSub {
                dst: SSAVar::new("tmp:cmp", 1, 1),
                a: SSAVar::new("AL", 0, 1),
                b: SSAVar::constant(0x30, 1),
            },
        ];

        func.normalize_register_alias_sources(&arch);

        match &func.get_block(0x1000).expect("entry block").ops[1] {
            SSAOp::IntSub { a, .. } => {
                assert_eq!(a, &SSAVar::new("tmp:loaded_byte", 1, 1));
            }
            other => panic!("expected IntSub, got {other:?}"),
        }
    }

    #[test]
    fn test_decompile_normalization_preserves_low_byte_after_x86_widening() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("EAX", 0x00, 4));

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let block = func.get_block_mut(0x1000).expect("entry block");
        block.ops = vec![
            SSAOp::IntZExt {
                dst: SSAVar::new("EAX", 1, 4),
                src: SSAVar::new("tmp:loaded_byte", 1, 1),
            },
            SSAOp::IntZExt {
                dst: SSAVar::new("RAX", 2, 8),
                src: SSAVar::new("EAX", 1, 4),
            },
            SSAOp::IntLess {
                dst: SSAVar::new("CF", 1, 1),
                a: SSAVar::new("AL", 0, 1),
                b: SSAVar::constant(b'0' as u64, 1),
            },
        ];

        func.normalize_register_alias_sources(&arch);

        match &func.get_block(0x1000).expect("entry block").ops[2] {
            SSAOp::IntLess { a, .. } => {
                assert_eq!(a, &SSAVar::new("tmp:loaded_byte", 1, 1));
            }
            other => panic!("expected IntLess, got {other:?}"),
        }
    }

    #[test]
    fn test_decompile_normalization_reuses_exact_x86_narrow_root_after_widening() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::sub("EAX", 0, 4, "RAX"));

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let block = func.get_block_mut(0x1000).expect("entry block");
        block.ops = vec![
            SSAOp::IntAdd {
                dst: SSAVar::new("EAX", 2, 4),
                a: SSAVar::new("tmp:lhs", 1, 4),
                b: SSAVar::new("tmp:rhs", 1, 4),
            },
            SSAOp::IntZExt {
                dst: SSAVar::new("RAX", 2, 8),
                src: SSAVar::new("EAX", 2, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:stored_exact", 1, 4),
                src: SSAVar::new("EAX", 2, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:stored_mismatched_name", 1, 4),
                src: SSAVar::new("RAX", 2, 4),
            },
        ];

        func.normalize_register_alias_sources(&arch);

        let ops = &func.get_block(0x1000).expect("entry block").ops;
        assert_eq!(ops.len(), 4, "an exact narrow root needs no extraction");
        match &ops[2] {
            SSAOp::Copy { src, .. } => assert_eq!(src, &SSAVar::new("EAX", 2, 4)),
            other => panic!("expected narrow copy, got {other:?}"),
        }
        match &ops[3] {
            SSAOp::Copy { src, .. } => assert_eq!(src, &SSAVar::new("EAX", 2, 4)),
            other => panic!("expected width-corrected narrow copy, got {other:?}"),
        }
    }

    #[test]
    fn test_decompile_normalization_seeds_low_byte_after_x86_subpiece_write() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("R8", 0x40, 8));
        arch.add_register(RegisterDef::new("R8D", 0x40, 4));

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let block = func.get_block_mut(0x1000).expect("entry block");
        block.ops = vec![
            SSAOp::Subpiece {
                dst: SSAVar::new("R8D", 1, 4),
                src: SSAVar::new("tmp:src", 1, 8),
                offset: 0,
            },
            SSAOp::IntLess {
                dst: SSAVar::new("CF", 1, 1),
                a: SSAVar::new("R8B", 0, 1),
                b: SSAVar::constant(0x1a, 1),
            },
        ];

        func.normalize_register_alias_sources(&arch);

        let ops = &func.get_block(0x1000).expect("entry block").ops;
        let extracted = match &ops[1] {
            SSAOp::Subpiece { dst, src, offset } => {
                assert_eq!(src, &SSAVar::new("R8D", 1, 4));
                assert_eq!(*offset, 0);
                dst.clone()
            }
            other => panic!("expected explicit low-byte extraction, got {other:?}"),
        };
        match &ops[2] {
            SSAOp::IntLess { a, .. } => assert_eq!(a, &extracted),
            other => panic!("expected IntLess, got {other:?}"),
        }
    }

    #[test]
    fn test_decompile_normalization_materializes_x86_eax_after_wide_temporary_write() {
        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![R2ILOp::Return {
                target: make_ram(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::sub("EAX", 0, 4, "RAX"));

        let mut func = SSAFunction::from_blocks_raw_no_arch(&blocks).expect("raw SSA should build");
        let block = func.get_block_mut(0x1000).expect("entry block");
        block.ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("RAX", 2, 8),
                src: SSAVar::new("tmp:loaded_len", 1, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:narrow_len", 1, 4),
                src: SSAVar::new("EAX", 1, 4),
            },
        ];

        func.normalize_register_alias_sources(&arch);

        let ops = &func.get_block(0x1000).expect("entry block").ops;
        let extracted = match &ops[1] {
            SSAOp::Subpiece { dst, src, offset } => {
                assert_eq!(src, &SSAVar::new("tmp:loaded_len", 1, 8));
                assert_eq!(*offset, 0);
                dst.clone()
            }
            other => panic!("expected explicit EAX extraction, got {other:?}"),
        };
        match &ops[2] {
            SSAOp::Copy { dst, src } => {
                assert_eq!(dst, &SSAVar::new("tmp:narrow_len", 1, 4));
                assert_eq!(src, &extracted);
            }
            other => panic!("expected narrow copy, got {other:?}"),
        }
    }

    #[test]
    fn test_symbolic_ssa_normalizes_x86_low_byte_alias_sources() {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("EAX", 0x00, 4));
        arch.add_register(RegisterDef::new("AL", 0x00, 1));

        let blocks = vec![R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: make_reg(0, 4),
                    src: make_const(0x41, 4),
                },
                R2ILOp::IntEqual {
                    dst: make_reg(0x200, 1),
                    a: make_reg(0, 1),
                    b: make_const(0x41, 1),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let artifact =
            SsaArtifact::for_symbolic(&blocks, Some(&arch)).expect("symbolic SSA should build");
        let block = artifact.function().get_block(0x1000).expect("entry block");

        match &block.ops[1] {
            SSAOp::IntEqual { a, .. } => {
                assert_eq!(a, &SSAVar::constant(0x41, 1));
            }
            other => panic!("expected IntEqual, got {other:?}"),
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

        func.normalize_register_alias_sources(&make_arm64_alias_arch());

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
    fn test_decompile_normalization_preserves_loop_invariant_family_root() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::IntZExt {
                        dst: make_reg(0x80, 8),
                        src: make_unique(0x100, 4),
                    },
                    R2ILOp::Branch {
                        target: make_ram(0x1004, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::CBranch {
                    target: make_ram(0x100c, 8),
                    cond: make_unique(0x180, 1),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1008,
                size: 4,
                ops: vec![R2ILOp::Branch {
                    target: make_ram(0x1004, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x100c,
                size: 4,
                ops: vec![
                    R2ILOp::Copy {
                        dst: make_unique(0x200, 4),
                        src: make_reg(0x80, 4),
                    },
                    R2ILOp::Return {
                        target: make_ram(0, 8),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];

        let func = SSAFunction::from_blocks_raw(&blocks, Some(&make_arm64_alias_arch()))
            .expect("loop SSA should build");
        let ops = &func.get_block(0x100c).expect("loop exit block").ops;
        match &ops[0] {
            SSAOp::Copy { src, .. } => {
                assert_eq!(src, &SSAVar::new("tmp:100", 0, 4));
            }
            other => panic!("expected narrow alias copy, got {other:?}"),
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

        func.normalize_register_alias_sources(&make_arm64_alias_arch());

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
            SSAOp::IntAdd {
                dst: SSAVar::new("tmp:5", 1, 8),
                a: SSAVar::new("rsp", 0, 8),
                b: SSAVar::constant(0xffff_fff0, 4),
            },
            SSAOp::IntAdd {
                dst: SSAVar::new("tmp:max", 1, 8),
                a: SSAVar::new("rsp", 0, 8),
                b: SSAVar::constant(i64::MAX as u64, 8),
            },
            SSAOp::IntAdd {
                dst: SSAVar::new("tmp:overflow", 1, 8),
                a: SSAVar::new("tmp:max", 1, 8),
                b: SSAVar::constant(1, 8),
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
            facts.stack_address_root_of(&SSAVar::new("tmp:5", 1, 8)),
            Some(&rsp_root),
            "32-bit negative stack deltas must be sign-extended"
        );
        assert_eq!(
            facts.stack_address_root_of(&SSAVar::new("tmp:overflow", 1, 8)),
            None,
            "overflowing stack offsets must not saturate into false provenance"
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
