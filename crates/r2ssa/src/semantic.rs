//! Canonical semantic sidecar facts for prepared SSA functions.
//!
//! These facts keep object, memory, predicate, and call-site provenance in
//! `r2ssa` so downstream crates stop reconstructing them independently.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::assumption::{AssumptionSet, AssumptionSubject, AssumptionUsageReport, AssumptionValue};
use crate::cfg::BlockTerminator;
use crate::function::{DecompilePrepFacts, SSAFunction, StackAddressBase, StackAddressRoot};
use crate::graph::{InstId, InstPayload, SsaGraph, ValueId};
use crate::op::SSAOp;
use crate::var::SSAVar;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ObjectId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PredicateId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CallSiteId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobalObjectKey {
    pub space: String,
    pub address: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectKind {
    StackSlot { base: StackAddressBase, offset: i64 },
    FrameObject { base: StackAddressBase, offset: i64 },
    Global { space: String, address: u64 },
    HeapAlloc { call_site: CallSiteId },
    EscapedUnknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectFact {
    pub id: ObjectId,
    pub kind: ObjectKind,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ObjectModel {
    pub objects: BTreeMap<ObjectId, ObjectFact>,
    pub value_objects: BTreeMap<ValueId, ObjectId>,
    pub stack_objects: BTreeMap<StackAddressRoot, ObjectId>,
    pub global_objects: BTreeMap<GlobalObjectKey, ObjectId>,
    pub escaped_unknown: Option<ObjectId>,
}

impl ObjectModel {
    pub fn object_for_value(&self, value: ValueId) -> Option<ObjectId> {
        self.value_objects.get(&value).copied()
    }

    pub fn object_for_var(&self, graph: &SsaGraph, value: &SSAVar) -> Option<ObjectId> {
        graph
            .value_id_for_var(value)
            .and_then(|value_id| self.object_for_value(value_id))
    }

    pub fn object(&self, id: ObjectId) -> Option<&ObjectFact> {
        self.objects.get(&id)
    }

    pub fn escaped_unknown_object(&self) -> Option<ObjectId> {
        self.escaped_unknown
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryVersion {
    pub object: ObjectId,
    pub version: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryLocation {
    pub object: ObjectId,
    pub offset: i64,
    pub size: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryUseFact {
    pub location: MemoryLocation,
    pub version: MemoryVersion,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryDefFact {
    pub location: MemoryLocation,
    pub previous_version: MemoryVersion,
    pub next_version: MemoryVersion,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryPhiFact {
    pub object: ObjectId,
    pub output_version: MemoryVersion,
    pub inputs: Vec<(u64, MemoryVersion)>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MemorySSAFacts {
    pub uses_by_inst: BTreeMap<InstId, Vec<MemoryUseFact>>,
    pub defs_by_inst: BTreeMap<InstId, Vec<MemoryDefFact>>,
    pub phis_by_block: BTreeMap<u64, Vec<MemoryPhiFact>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareKind {
    Equal,
    NotEqual,
    Less,
    SignedLess,
    LessEqual,
    SignedLessEqual,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompareProvenance {
    pub kind: CompareKind,
    pub lhs: ValueId,
    pub rhs: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredicateFact {
    pub id: PredicateId,
    pub block_addr: u64,
    pub condition: ValueId,
    pub comparison: Option<CompareProvenance>,
    pub true_target: u64,
    pub false_target: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockAssumption {
    pub predecessor: u64,
    pub predicate: PredicateId,
    pub truth: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchPredicateFact {
    pub block_addr: u64,
    pub selector: Option<ValueId>,
    pub cases: Vec<(u64, u64)>,
    pub default: Option<u64>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PredicateFacts {
    pub predicates: BTreeMap<PredicateId, PredicateFact>,
    pub block_assumptions: BTreeMap<u64, Vec<BlockAssumption>>,
    pub switches: BTreeMap<u64, SwitchPredicateFact>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallMemoryEffect {
    ReadOnly,
    WriteOnly,
    ReadWrite,
    Alloc,
    Free,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallSiteFact {
    pub id: CallSiteId,
    pub at: InstId,
    pub target: ValueId,
    pub direct_target: Option<u64>,
    pub fallthrough: Option<u64>,
    pub memory_effect: CallMemoryEffect,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CallSiteFacts {
    pub by_id: BTreeMap<CallSiteId, CallSiteFact>,
    pub by_inst: BTreeMap<InstId, CallSiteId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LoopId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProofNodeId {
    pub owner: &'static str,
    pub kind: &'static str,
    pub anchor: u64,
    pub ordinal: u64,
}

impl ProofNodeId {
    pub const fn new(owner: &'static str, kind: &'static str, anchor: u64, ordinal: u64) -> Self {
        Self {
            owner,
            kind,
            anchor,
            ordinal,
        }
    }

    pub const fn loop_certificate(header: u64, loop_id: LoopId) -> Self {
        Self::new("r2ssa", "loop", header, loop_id.0 as u64)
    }

    pub const fn switch_certificate(block_addr: u64) -> Self {
        Self::new("r2ssa", "switch", block_addr, 0)
    }
}

impl std::fmt::Display for ProofNodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:0x{:x}:{}",
            self.owner, self.kind, self.anchor, self.ordinal
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructuredLoopKind {
    Natural,
    SelfLoop,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredLoopFact {
    pub id: LoopId,
    pub kind: StructuredLoopKind,
    pub header: u64,
    pub latches: Vec<u64>,
    pub body: Vec<u64>,
    pub exits: Vec<u64>,
    pub condition: Option<PredicateId>,
    pub induction_phi: Option<ValueId>,
    pub induction_init: Option<ValueId>,
    pub induction_update: Option<ValueId>,
    pub bound: Option<ValueId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructuredAccessId {
    pub inst: InstId,
    pub ordinal: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredMemoryAccessFact {
    pub id: StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub object: ObjectId,
    pub address: ValueId,
    pub value: Option<ValueId>,
    pub is_write: bool,
    pub width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredRecursiveCallFact {
    pub call_site: CallSiteId,
    pub block_addr: u64,
    pub op_index: usize,
    pub target: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCertificate {
    pub proof_node: ProofNodeId,
    pub loop_id: LoopId,
    pub header: u64,
    pub latches: Vec<u64>,
    pub body: Vec<u64>,
    pub exits: Vec<u64>,
    pub condition: Option<PredicateId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchCertificate {
    pub proof_node: ProofNodeId,
    pub block_addr: u64,
    pub selector: Option<ValueId>,
    pub cases: Vec<(u64, u64)>,
    pub default: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfRegionCertificate {
    pub predicate: PredicateId,
    pub block_addr: u64,
    pub true_target: u64,
    pub false_target: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionCertificate {
    pub value: ValueId,
    pub defining_inst: Option<InstId>,
    pub inputs: Vec<ValueId>,
    pub width: u32,
    pub renderable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryAccessCertificate {
    pub access: StructuredAccessId,
    pub block_addr: u64,
    pub op_index: usize,
    pub object: ObjectId,
    pub address: ValueId,
    pub value: Option<ValueId>,
    pub is_write: bool,
    pub width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackSlotCertificate {
    pub object: ObjectId,
    pub base: StackAddressBase,
    pub offset: i64,
    pub size: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallsiteCertificate {
    pub call_site: CallSiteId,
    pub at: InstId,
    pub block_addr: u64,
    pub op_index: usize,
    pub target: ValueId,
    pub direct_target: Option<u64>,
    pub fallthrough: Option<u64>,
    pub argument_values: Vec<ValueId>,
    pub stack_argument_values: Vec<StackCallArgumentCertificate>,
    pub argument_certificates: Vec<CallArgumentCertificate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackCallArgumentCertificate {
    pub stack_offset: i64,
    pub value: ValueId,
    pub memory_access: StructuredAccessId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallArgumentCertificate {
    pub index: usize,
    pub value: ValueId,
    pub location: CallArgumentLocation,
    pub source_inst: Option<InstId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallArgumentLocation {
    Register {
        name: String,
    },
    Stack {
        object: ObjectId,
        offset: i64,
        memory_access: StructuredAccessId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallResultCertificate {
    pub call_site: CallSiteId,
    pub at: InstId,
    pub block_addr: u64,
    pub op_index: usize,
    pub value: ValueId,
    pub width: u32,
    pub carrier: ReturnCarrier,
    pub owner: Option<ValueOwner>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReturnCarrier {
    Register {
        name: String,
    },
    StackSlot {
        object: ObjectId,
        offset: i64,
        memory_access: Option<StructuredAccessId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueOwner {
    Value(ValueId),
    StackSlot { object: ObjectId, offset: i64 },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackReloadSourceCertificate {
    pub value: ValueId,
    pub reload: ValueId,
    pub source: ValueId,
    pub canonical_source: ValueId,
    pub object: ObjectId,
    pub base: StackAddressBase,
    pub offset: i64,
    pub value_width: u32,
    pub memory_width: u32,
    pub store_access: StructuredAccessId,
    pub load_access: StructuredAccessId,
    pub store_inst: InstId,
    pub load_inst: InstId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnValueCertificate {
    pub at: InstId,
    pub block_addr: u64,
    pub op_index: usize,
    pub value: ValueId,
    pub width: u32,
    pub carrier: Option<ReturnCarrier>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedProofFailure {
    pub owner: &'static str,
    pub anchor: u64,
    pub obligation: &'static str,
    pub reason: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreparedFunctionCertificates {
    pub loops: BTreeMap<LoopId, LoopCertificate>,
    pub switches: BTreeMap<u64, SwitchCertificate>,
    pub if_regions: BTreeMap<PredicateId, IfRegionCertificate>,
    pub expressions: BTreeMap<ValueId, ExpressionCertificate>,
    pub memory_accesses: BTreeMap<StructuredAccessId, MemoryAccessCertificate>,
    pub memory_accesses_by_op: BTreeMap<(u64, usize, bool), Vec<StructuredAccessId>>,
    pub stack_slots: BTreeMap<ObjectId, StackSlotCertificate>,
    pub callsites: BTreeMap<CallSiteId, CallsiteCertificate>,
    pub callsites_by_inst: BTreeMap<InstId, CallSiteId>,
    pub call_results: BTreeMap<ValueId, CallResultCertificate>,
    pub call_results_by_inst: BTreeMap<InstId, ValueId>,
    pub call_results_by_callsite: BTreeMap<CallSiteId, Vec<ValueId>>,
    pub stack_reloads: BTreeMap<ValueId, StackReloadSourceCertificate>,
    pub returns: Vec<ReturnValueCertificate>,
    pub returns_by_inst: BTreeMap<InstId, usize>,
    pub failures: Vec<PreparedProofFailure>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StructuredDataflowFacts {
    pub loops: BTreeMap<LoopId, StructuredLoopFact>,
    pub memory_accesses: BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    pub recursive_calls: BTreeMap<CallSiteId, StructuredRecursiveCallFact>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreparedAssumptionBindingKind {
    Predicate {
        predicate: PredicateId,
        block_addr: u64,
        predecessor: Option<u64>,
        truth: bool,
    },
    Register {
        name: String,
        state_name: String,
        symbol_name: String,
        bits: u32,
    },
    StackSlot {
        base: StackAddressBase,
        offset: i64,
        object: ObjectId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedAssumptionBinding {
    pub assumption: crate::AnalysisAssumption,
    pub binding: PreparedAssumptionBindingKind,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreparedFunctionFacts {
    pub objects: ObjectModel,
    pub memory: MemorySSAFacts,
    pub predicates: PredicateFacts,
    pub call_sites: CallSiteFacts,
    pub structured: StructuredDataflowFacts,
    pub certificates: PreparedFunctionCertificates,
    pub assumptions: AssumptionSet,
    pub applied_assumption_bindings: Vec<PreparedAssumptionBinding>,
    pub assumption_usage: AssumptionUsageReport,
}

impl PreparedFunctionFacts {
    pub fn collect(function: &SSAFunction, graph: &SsaGraph) -> Self {
        Self::collect_with_assumptions(function, graph, &AssumptionSet::default())
    }

    pub fn collect_with_assumptions(
        function: &SSAFunction,
        graph: &SsaGraph,
        assumptions: &AssumptionSet,
    ) -> Self {
        let call_sites = collect_call_sites(function, graph, function.decompile_prep_facts());
        let (objects, memory) = collect_object_and_memory_facts(function, graph, &call_sites);
        let predicates = apply_assumptions_to_predicate_facts(
            collect_predicate_facts(function, graph),
            assumptions,
        );
        let structured = collect_structured_dataflow_facts(
            function,
            graph,
            &objects,
            &memory,
            &predicates,
            &call_sites,
        );
        let certificates = collect_prepared_function_certificates(
            function,
            graph,
            &objects,
            &memory,
            &predicates,
            &call_sites,
            &structured,
        );
        let (applied_assumption_bindings, assumption_usage) =
            collect_prepared_assumption_usage(graph, &objects, &predicates, assumptions);
        Self {
            objects,
            memory,
            predicates,
            call_sites,
            structured,
            certificates,
            assumptions: assumptions.clone(),
            applied_assumption_bindings,
            assumption_usage,
        }
    }
}

fn apply_assumptions_to_predicate_facts(
    mut predicates: PredicateFacts,
    assumptions: &AssumptionSet,
) -> PredicateFacts {
    for assumption in assumptions.iter() {
        let (predicate_id, block_addr, predecessor, truth) =
            match (&assumption.subject, &assumption.value) {
                (
                    AssumptionSubject::Predicate {
                        predicate,
                        block_addr,
                        predecessor,
                    },
                    AssumptionValue::Branch { truth },
                ) => (*predicate, *block_addr, *predecessor, *truth),
                _ => continue,
            };
        if !predicates.predicates.contains_key(&predicate_id) {
            continue;
        }
        let entry = predicates.block_assumptions.entry(block_addr).or_default();
        if entry.iter().any(|existing| {
            existing.predicate == predicate_id
                && existing.predecessor == predecessor.unwrap_or(existing.predecessor)
                && existing.truth == truth
        }) {
            continue;
        }
        entry.push(BlockAssumption {
            predecessor: predecessor.unwrap_or(block_addr),
            predicate: predicate_id,
            truth,
        });
    }
    predicates
}

fn collect_prepared_assumption_usage(
    graph: &SsaGraph,
    objects: &ObjectModel,
    predicates: &PredicateFacts,
    assumptions: &AssumptionSet,
) -> (Vec<PreparedAssumptionBinding>, AssumptionUsageReport) {
    let mut bindings = Vec::new();
    let mut usage = AssumptionUsageReport::default();

    for assumption in assumptions.iter() {
        match (&assumption.subject, &assumption.value) {
            (
                AssumptionSubject::Predicate {
                    predicate,
                    block_addr,
                    predecessor,
                },
                AssumptionValue::Branch { truth },
            ) => {
                let Some(fact) = predicates.predicates.get(predicate) else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                if fact.block_addr != *block_addr {
                    usage.mark_conflict(
                        assumption,
                        format!(
                            "predicate block mismatch (expected 0x{block_addr:x}, observed 0x{:x})",
                            fact.block_addr
                        ),
                    );
                    continue;
                }
                if let Some(pred) = predecessor {
                    let expected = if *truth {
                        fact.true_target
                    } else {
                        fact.false_target
                    };
                    if *pred != expected {
                        usage.mark_conflict(
                            assumption,
                            format!(
                                "branch predecessor 0x{pred:x} does not match selected edge 0x{expected:x}"
                            ),
                        );
                        continue;
                    }
                }
                usage.mark_applied(assumption);
                bindings.push(PreparedAssumptionBinding {
                    assumption: assumption.clone(),
                    binding: PreparedAssumptionBindingKind::Predicate {
                        predicate: *predicate,
                        block_addr: *block_addr,
                        predecessor: *predecessor,
                        truth: *truth,
                    },
                });
            }
            (AssumptionSubject::Register { name }, _) => {
                let Some(value) = graph.values.iter().find(|value| {
                    value.var.version == 0
                        && value.var.is_register()
                        && value.var.name.eq_ignore_ascii_case(name)
                }) else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                usage.mark_applied(assumption);
                bindings.push(PreparedAssumptionBinding {
                    assumption: assumption.clone(),
                    binding: PreparedAssumptionBindingKind::Register {
                        name: value.var.name.clone(),
                        state_name: value.var.display_name(),
                        symbol_name: value
                            .var
                            .name
                            .strip_prefix("reg:")
                            .unwrap_or(&value.var.name)
                            .to_ascii_lowercase(),
                        bits: value.var.size.saturating_mul(8),
                    },
                });
            }
            (AssumptionSubject::StackSlot { base, offset }, _) => {
                let Some((root, object)) =
                    objects.stack_objects.iter().find_map(|(root, object)| {
                        let matches_base = matches!(
                            (base.as_str(), root.base),
                            ("bp", StackAddressBase::FramePointer)
                                | ("frame", StackAddressBase::FramePointer)
                                | ("rbp", StackAddressBase::FramePointer)
                                | ("sp", StackAddressBase::StackPointer)
                                | ("stack", StackAddressBase::StackPointer)
                                | ("rsp", StackAddressBase::StackPointer)
                        );
                        (matches_base && root.offset == *offset).then_some((*root, *object))
                    })
                else {
                    usage.mark_ignored(assumption);
                    continue;
                };
                usage.mark_applied(assumption);
                bindings.push(PreparedAssumptionBinding {
                    assumption: assumption.clone(),
                    binding: PreparedAssumptionBindingKind::StackSlot {
                        base: root.base,
                        offset: root.offset,
                        object,
                    },
                });
            }
            _ => usage.mark_ignored(assumption),
        }
    }

    (bindings, usage)
}

#[derive(Debug, Clone)]
struct ObjectModelBuilder<'a> {
    facts: Option<&'a DecompilePrepFacts>,
    objects: BTreeMap<ObjectId, ObjectFact>,
    value_objects: BTreeMap<ValueId, ObjectId>,
    stack_objects: BTreeMap<StackAddressRoot, ObjectId>,
    global_objects: BTreeMap<GlobalObjectKey, ObjectId>,
    escaped_unknown: ObjectId,
    next_object_id: u32,
}

impl<'a> ObjectModelBuilder<'a> {
    fn new(facts: Option<&'a DecompilePrepFacts>) -> Self {
        let escaped_unknown = ObjectId(0);
        let mut objects = BTreeMap::new();
        objects.insert(
            escaped_unknown,
            ObjectFact {
                id: escaped_unknown,
                kind: ObjectKind::EscapedUnknown,
            },
        );
        Self {
            facts,
            objects,
            value_objects: BTreeMap::new(),
            stack_objects: BTreeMap::new(),
            global_objects: BTreeMap::new(),
            escaped_unknown,
            next_object_id: 1,
        }
    }

    fn build(mut self, function: &SSAFunction, graph: &SsaGraph) -> ObjectModel {
        if let Some(facts) = self.facts {
            let mut stack_roots: Vec<StackAddressRoot> =
                facts.stack_address_roots.values().copied().collect();
            stack_roots.sort_unstable();
            stack_roots.dedup();
            for root in stack_roots {
                self.ensure_stack_object(root);
            }
            for var in facts.stack_address_roots.keys() {
                let _ = self.object_for_address_value(graph, var, "ram");
            }
        }

        for block in function.blocks() {
            for op in &block.ops {
                match op {
                    SSAOp::Load { addr, space, .. }
                    | SSAOp::Store { addr, space, .. }
                    | SSAOp::LoadLinked { addr, space, .. }
                    | SSAOp::StoreConditional { addr, space, .. }
                    | SSAOp::AtomicCAS { addr, space, .. }
                    | SSAOp::LoadGuarded { addr, space, .. }
                    | SSAOp::StoreGuarded { addr, space, .. } => {
                        let _ = self.object_for_address_value(graph, addr, space);
                    }
                    _ => {}
                }
            }
        }

        ObjectModel {
            objects: self.objects,
            value_objects: self.value_objects,
            stack_objects: self.stack_objects,
            global_objects: self.global_objects,
            escaped_unknown: Some(self.escaped_unknown),
        }
    }

    fn object_for_address_value(
        &mut self,
        graph: &SsaGraph,
        value: &SSAVar,
        space: &str,
    ) -> ObjectId {
        let Some(value_id) = graph.value_id_for_var(value) else {
            return self.escaped_unknown;
        };
        if let Some(object) = self.value_objects.get(&value_id).copied() {
            return object;
        }

        if let Some(root) = resolve_stack_root(self.facts, value) {
            let object = self.ensure_stack_object(root);
            self.value_objects.insert(value_id, object);
            return object;
        }

        if let Some(address) = resolve_const_value(self.facts, value) {
            let object = self.ensure_global_object(GlobalObjectKey {
                space: space.to_string(),
                address,
            });
            self.value_objects.insert(value_id, object);
            return object;
        }

        self.value_objects.insert(value_id, self.escaped_unknown);
        self.escaped_unknown
    }

    fn ensure_stack_object(&mut self, root: StackAddressRoot) -> ObjectId {
        if let Some(object) = self.stack_objects.get(&root).copied() {
            return object;
        }
        let id = self.alloc_object_id();
        self.objects.insert(
            id,
            ObjectFact {
                id,
                kind: ObjectKind::StackSlot {
                    base: root.base,
                    offset: root.offset,
                },
            },
        );
        self.stack_objects.insert(root, id);
        id
    }

    fn ensure_global_object(&mut self, key: GlobalObjectKey) -> ObjectId {
        if let Some(object) = self.global_objects.get(&key).copied() {
            return object;
        }
        let id = self.alloc_object_id();
        self.objects.insert(
            id,
            ObjectFact {
                id,
                kind: ObjectKind::Global {
                    space: key.space.clone(),
                    address: key.address,
                },
            },
        );
        self.global_objects.insert(key, id);
        id
    }

    fn alloc_object_id(&mut self) -> ObjectId {
        let id = ObjectId(self.next_object_id);
        self.next_object_id = self.next_object_id.saturating_add(1);
        id
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AccessSummary {
    uses: Vec<MemoryLocation>,
    defs: Vec<MemoryLocation>,
}

fn collect_object_and_memory_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_sites: &CallSiteFacts,
) -> (ObjectModel, MemorySSAFacts) {
    let facts = function.decompile_prep_facts();
    let builder = ObjectModelBuilder::new(facts);
    let object_model = builder.build(function, graph);
    let access_summaries =
        collect_access_summaries(function, graph, facts, &object_model, call_sites);
    let memory = build_memory_ssa(function, graph, &object_model, access_summaries);
    (object_model, memory)
}

fn collect_access_summaries(
    function: &SSAFunction,
    graph: &SsaGraph,
    prep_facts: Option<&DecompilePrepFacts>,
    object_model: &ObjectModel,
    call_sites: &CallSiteFacts,
) -> BTreeMap<InstId, AccessSummary> {
    let mut summaries = BTreeMap::new();
    let escaped_unknown = object_model.escaped_unknown_object().unwrap_or(ObjectId(0));

    for block in function.blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            let Some(inst_id) = graph.inst_id_for_op_site(block.addr, op_idx) else {
                continue;
            };
            let mut uses = Vec::new();
            let mut defs = Vec::new();
            match op {
                SSAOp::Load { dst, addr, space }
                | SSAOp::LoadLinked {
                    dst, addr, space, ..
                }
                | SSAOp::LoadGuarded {
                    dst, addr, space, ..
                } => {
                    uses.push(memory_location_for_addr(
                        prep_facts,
                        object_model,
                        graph,
                        addr,
                        space,
                        dst.size,
                    ));
                }
                SSAOp::Store { addr, val, space }
                | SSAOp::StoreGuarded {
                    addr, val, space, ..
                } => {
                    defs.push(memory_location_for_addr(
                        prep_facts,
                        object_model,
                        graph,
                        addr,
                        space,
                        val.size,
                    ));
                }
                SSAOp::StoreConditional {
                    addr, val, space, ..
                } => {
                    let location = memory_location_for_addr(
                        prep_facts,
                        object_model,
                        graph,
                        addr,
                        space,
                        val.size,
                    );
                    uses.push(location);
                    defs.push(location);
                }
                SSAOp::AtomicCAS {
                    addr,
                    expected,
                    replacement,
                    space,
                    ..
                } => {
                    let location = memory_location_for_addr(
                        prep_facts,
                        object_model,
                        graph,
                        addr,
                        space,
                        expected.size.max(replacement.size),
                    );
                    uses.push(location);
                    defs.push(location);
                }
                SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                    if call_sites.by_inst.contains_key(&inst_id) {
                        let location = MemoryLocation {
                            object: escaped_unknown,
                            offset: 0,
                            size: 0,
                        };
                        uses.push(location);
                        defs.push(location);
                    }
                }
                _ => {}
            }
            if !uses.is_empty() || !defs.is_empty() {
                summaries.insert(inst_id, AccessSummary { uses, defs });
            }
        }
    }

    summaries
}

fn build_memory_ssa(
    function: &SSAFunction,
    graph: &SsaGraph,
    object_model: &ObjectModel,
    access_summaries: BTreeMap<InstId, AccessSummary>,
) -> MemorySSAFacts {
    let mut phis_by_block = BTreeMap::new();

    let mut next_version_by_object = BTreeMap::<ObjectId, u32>::new();
    for object in object_model.objects.keys() {
        next_version_by_object.insert(*object, 1);
    }

    let mut def_versions = BTreeMap::<InstId, Vec<MemoryVersion>>::new();
    for (inst_id, summary) in &access_summaries {
        if summary.defs.is_empty() {
            continue;
        }
        let versions = summary
            .defs
            .iter()
            .map(|location| {
                let next = next_version_by_object.entry(location.object).or_insert(1);
                let version = MemoryVersion {
                    object: location.object,
                    version: *next,
                };
                *next = next.saturating_add(1);
                version
            })
            .collect::<Vec<_>>();
        def_versions.insert(*inst_id, versions);
    }

    let object_ids = object_model.objects.keys().copied().collect::<Vec<_>>();
    let mut in_states = BTreeMap::<u64, BTreeMap<ObjectId, MemoryVersion>>::new();
    let mut out_states = BTreeMap::<u64, BTreeMap<ObjectId, MemoryVersion>>::new();
    let mut phi_versions = BTreeMap::<(u64, ObjectId), MemoryVersion>::new();
    let mut phi_inputs = BTreeMap::<(u64, ObjectId), Vec<(u64, MemoryVersion)>>::new();
    let (uses_by_inst, defs_by_inst) = loop {
        let mut changed = false;
        let mut uses_by_inst = BTreeMap::<InstId, Vec<MemoryUseFact>>::new();
        let mut defs_by_inst = BTreeMap::<InstId, Vec<MemoryDefFact>>::new();
        for &block_addr in function.block_addrs() {
            let preds = function.predecessors(block_addr);
            let mut in_state = BTreeMap::new();

            if !preds.is_empty() {
                for object in &object_ids {
                    let inputs = preds
                        .iter()
                        .map(|pred| {
                            let version = out_states
                                .get(pred)
                                .and_then(|state| state.get(object).copied())
                                .unwrap_or(MemoryVersion {
                                    object: *object,
                                    version: 0,
                                });
                            (*pred, version)
                        })
                        .collect::<Vec<_>>();
                    let first_version = inputs.first().map(|(_, version)| *version);
                    let merged = if inputs
                        .iter()
                        .all(|(_, version)| Some(*version) == first_version)
                    {
                        first_version.expect("inputs is not empty")
                    } else {
                        let key = (block_addr, *object);
                        let phi = phi_versions.entry(key).or_insert_with(|| {
                            let next = next_version_by_object.entry(*object).or_insert(1);
                            let version = MemoryVersion {
                                object: *object,
                                version: *next,
                            };
                            *next = next.saturating_add(1);
                            version
                        });
                        phi_inputs.insert(key, inputs);
                        *phi
                    };
                    if merged.version != 0 {
                        in_state.insert(*object, merged);
                    }
                }
            }

            if in_states.get(&block_addr) != Some(&in_state) {
                in_states.insert(block_addr, in_state.clone());
                changed = true;
            }

            let mut state = in_state;
            let Some(block) = function.get_block(block_addr) else {
                continue;
            };
            for (op_idx, _) in block.ops.iter().enumerate() {
                let Some(inst_id) = graph.inst_id_for_op_site(block_addr, op_idx) else {
                    continue;
                };
                let Some(summary) = access_summaries.get(&inst_id) else {
                    continue;
                };
                for location in &summary.uses {
                    let version = state
                        .get(&location.object)
                        .copied()
                        .unwrap_or(MemoryVersion {
                            object: location.object,
                            version: 0,
                        });
                    uses_by_inst
                        .entry(inst_id)
                        .or_default()
                        .push(MemoryUseFact {
                            location: *location,
                            version,
                        });
                }
                if let Some(def_versions_for_op) = def_versions.get(&inst_id) {
                    for (location, next_version) in
                        summary.defs.iter().zip(def_versions_for_op.iter())
                    {
                        let previous_version =
                            state
                                .get(&location.object)
                                .copied()
                                .unwrap_or(MemoryVersion {
                                    object: location.object,
                                    version: 0,
                                });
                        defs_by_inst
                            .entry(inst_id)
                            .or_default()
                            .push(MemoryDefFact {
                                location: *location,
                                previous_version,
                                next_version: *next_version,
                            });
                        state.insert(location.object, *next_version);
                    }
                }
            }

            if out_states.get(&block_addr) != Some(&state) {
                out_states.insert(block_addr, state);
                changed = true;
            }
        }

        if !changed {
            break (uses_by_inst, defs_by_inst);
        }
    };

    for ((block_addr, object), output_version) in phi_versions {
        let inputs = phi_inputs.remove(&(block_addr, object)).unwrap_or_default();
        phis_by_block
            .entry(block_addr)
            .or_insert_with(Vec::new)
            .push(MemoryPhiFact {
                object,
                output_version,
                inputs,
            });
    }

    MemorySSAFacts {
        uses_by_inst,
        defs_by_inst,
        phis_by_block,
    }
}

fn collect_structured_dataflow_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    predicates: &PredicateFacts,
    call_sites: &CallSiteFacts,
) -> StructuredDataflowFacts {
    StructuredDataflowFacts {
        loops: collect_structured_loop_facts(function, graph, predicates),
        memory_accesses: collect_structured_memory_access_facts(function, graph, objects, memory),
        recursive_calls: collect_structured_recursive_call_facts(function, graph, call_sites),
    }
}

fn collect_prepared_function_certificates(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    predicates: &PredicateFacts,
    call_sites: &CallSiteFacts,
    structured: &StructuredDataflowFacts,
) -> PreparedFunctionCertificates {
    let loops = structured
        .loops
        .iter()
        .map(|(id, fact)| {
            (
                *id,
                LoopCertificate {
                    proof_node: ProofNodeId::loop_certificate(fact.header, *id),
                    loop_id: *id,
                    header: fact.header,
                    latches: fact.latches.clone(),
                    body: fact.body.clone(),
                    exits: fact.exits.clone(),
                    condition: fact.condition,
                },
            )
        })
        .collect();

    let switches = predicates
        .switches
        .iter()
        .filter(|(_, fact)| !fact.cases.is_empty())
        .map(|(block_addr, fact)| {
            (
                *block_addr,
                SwitchCertificate {
                    proof_node: ProofNodeId::switch_certificate(*block_addr),
                    block_addr: *block_addr,
                    selector: fact.selector,
                    cases: fact.cases.clone(),
                    default: fact.default,
                },
            )
        })
        .collect();

    let if_regions = predicates
        .predicates
        .iter()
        .map(|(id, fact)| {
            (
                *id,
                IfRegionCertificate {
                    predicate: *id,
                    block_addr: fact.block_addr,
                    true_target: fact.true_target,
                    false_target: fact.false_target,
                },
            )
        })
        .collect();

    let renderable_expressions = collect_renderable_expression_values(graph, structured);
    let expressions = graph
        .values
        .iter()
        .map(|value| {
            let defining_inst = graph.def_of.get(value.id.0 as usize).and_then(|id| *id);
            let inputs = defining_inst
                .and_then(|inst| graph.inst(inst))
                .map(|inst| inst.inputs.clone())
                .unwrap_or_default();
            (
                value.id,
                ExpressionCertificate {
                    value: value.id,
                    defining_inst,
                    inputs,
                    width: value.var.size,
                    renderable: renderable_expressions.contains(&value.id),
                },
            )
        })
        .collect();

    let mut memory_accesses_by_op = BTreeMap::<(u64, usize, bool), Vec<StructuredAccessId>>::new();
    let memory_accesses = structured
        .memory_accesses
        .iter()
        .map(|(id, fact)| {
            memory_accesses_by_op
                .entry((fact.block_addr, fact.op_index, fact.is_write))
                .or_default()
                .push(*id);
            (
                *id,
                MemoryAccessCertificate {
                    access: *id,
                    block_addr: fact.block_addr,
                    op_index: fact.op_index,
                    object: fact.object,
                    address: fact.address,
                    value: fact.value,
                    is_write: fact.is_write,
                    width: fact.width,
                },
            )
        })
        .collect();

    let stack_slots = objects
        .objects
        .iter()
        .filter_map(|(object, fact)| match fact.kind {
            ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset } => {
                Some((
                    *object,
                    StackSlotCertificate {
                        object: *object,
                        base,
                        offset,
                        size: None,
                    },
                ))
            }
            ObjectKind::Global { .. }
            | ObjectKind::HeapAlloc { .. }
            | ObjectKind::EscapedUnknown => None,
        })
        .collect();

    let mut callsites_by_inst = BTreeMap::new();
    let callsites = call_sites
        .by_id
        .iter()
        .map(|(id, fact)| {
            let (block_addr, op_index) = graph.op_site_for_inst(fact.at).unwrap_or_default();
            let stack_argument_values =
                collect_stack_call_argument_values(function, graph, objects, structured, fact);
            let mut argument_certificates =
                collect_register_call_argument_certificates(function, graph, fact);
            argument_certificates.extend(collect_stack_call_argument_certificates(
                &stack_argument_values,
                structured,
            ));
            callsites_by_inst.insert(fact.at, *id);
            (
                *id,
                CallsiteCertificate {
                    call_site: *id,
                    at: fact.at,
                    block_addr,
                    op_index,
                    target: fact.target,
                    direct_target: fact.direct_target,
                    fallthrough: fact.fallthrough,
                    argument_values: collect_call_argument_values(function, graph, fact),
                    stack_argument_values,
                    argument_certificates,
                },
            )
        })
        .collect();

    let (call_results, call_results_by_inst, call_results_by_callsite) =
        collect_call_result_certificates(function, graph, objects, call_sites, structured);
    let stack_reloads =
        collect_stack_reload_source_certificates(function, graph, objects, memory, structured);
    let (returns, returns_by_inst) = collect_return_value_certificates(function, graph);

    PreparedFunctionCertificates {
        loops,
        switches,
        if_regions,
        expressions,
        memory_accesses,
        memory_accesses_by_op,
        stack_slots,
        callsites,
        callsites_by_inst,
        call_results,
        call_results_by_inst,
        call_results_by_callsite,
        stack_reloads,
        returns,
        returns_by_inst,
        failures: Vec::new(),
    }
}

fn collect_renderable_expression_values(
    graph: &SsaGraph,
    structured: &StructuredDataflowFacts,
) -> BTreeSet<ValueId> {
    let certified_memory_read_insts = structured
        .memory_accesses
        .values()
        .filter(|access| !access.is_write && access.width > 0)
        .map(|access| access.id.inst)
        .collect::<BTreeSet<_>>();
    let mut renderable = BTreeSet::new();
    let mut ready = VecDeque::new();

    for value in &graph.values {
        if expression_leaf_is_renderable(value) && renderable.insert(value.id) {
            ready.push_back(value.id);
        }
    }

    let mut eligible = vec![false; graph.insts.len()];
    let mut missing_inputs = vec![0usize; graph.insts.len()];
    for inst in &graph.insts {
        let Some(output) = inst.output else {
            continue;
        };
        if graph.value(output).is_none_or(|value| value.var.size == 0) {
            continue;
        }
        if !expression_inst_is_renderable(inst, &certified_memory_read_insts) {
            continue;
        }

        eligible[inst.id.0 as usize] = true;
        missing_inputs[inst.id.0 as usize] = inst
            .inputs
            .iter()
            .filter(|input| !renderable.contains(input))
            .count();
        if missing_inputs[inst.id.0 as usize] == 0 && renderable.insert(output) {
            ready.push_back(output);
        }
    }

    loop {
        while let Some(value) = ready.pop_front() {
            for use_site in graph.use_sites(value) {
                let inst_idx = use_site.inst.0 as usize;
                if !eligible.get(inst_idx).copied().unwrap_or(false)
                    || missing_inputs.get(inst_idx).copied().unwrap_or(0) == 0
                {
                    continue;
                }
                missing_inputs[inst_idx] -= 1;
                if missing_inputs[inst_idx] == 0
                    && let Some(output) = graph.inst(use_site.inst).and_then(|inst| inst.output)
                    && renderable.insert(output)
                {
                    ready.push_back(output);
                }
            }
        }

        let mut added_loop_phi = false;
        for inst in &graph.insts {
            let Some(output) = inst.output else {
                continue;
            };
            if renderable.contains(&output) {
                continue;
            }
            if expression_loop_phi_is_renderable(
                graph,
                structured,
                inst,
                &renderable,
                &certified_memory_read_insts,
            ) && renderable.insert(output)
            {
                ready.push_back(output);
                added_loop_phi = true;
            }
        }
        if !added_loop_phi {
            break;
        }
    }

    renderable
}

fn expression_leaf_is_renderable(value: &crate::graph::GraphValue) -> bool {
    value.var.size > 0
        && (value.var.is_const() || (value.var.version == 0 && value.var.is_register()))
}

fn expression_inst_is_renderable(
    inst: &crate::graph::GraphInst,
    certified_memory_read_insts: &BTreeSet<InstId>,
) -> bool {
    match &inst.payload {
        InstPayload::Phi { .. } => expression_phi_is_identity(inst),
        InstPayload::Op(op) => {
            expression_op_is_pure(op)
                || (op.is_memory_read() && certified_memory_read_insts.contains(&inst.id))
        }
    }
}

fn expression_phi_is_identity(inst: &crate::graph::GraphInst) -> bool {
    let Some(first) = inst.inputs.first() else {
        return false;
    };
    inst.inputs.iter().all(|input| input == first)
}

fn expression_loop_phi_is_renderable(
    graph: &SsaGraph,
    structured: &StructuredDataflowFacts,
    inst: &crate::graph::GraphInst,
    renderable: &BTreeSet<ValueId>,
    certified_memory_read_insts: &BTreeSet<InstId>,
) -> bool {
    let InstPayload::Phi { predecessors } = &inst.payload else {
        return false;
    };
    let Some(output) = inst.output else {
        return false;
    };
    let Some(header) = graph.block(inst.block).map(|block| block.addr) else {
        return false;
    };
    let Some(loop_fact) = structured.loops.values().find(|fact| fact.header == header) else {
        return false;
    };
    if inst.inputs.len() != predecessors.len() {
        return false;
    }

    let latches = loop_fact.latches.iter().copied().collect::<BTreeSet<_>>();
    let mut saw_entry = false;
    let mut saw_backedge = false;
    for (pred_id, input) in predecessors.iter().zip(inst.inputs.iter().copied()) {
        let Some(pred_addr) = graph.block(*pred_id).map(|block| block.addr) else {
            return false;
        };
        if latches.contains(&pred_addr) {
            saw_backedge = true;
            let mut visited = BTreeSet::new();
            if !value_renderable_modulo_loop_phi(
                graph,
                input,
                output,
                renderable,
                certified_memory_read_insts,
                &mut visited,
                0,
            ) {
                return false;
            }
        } else {
            saw_entry = true;
            if !renderable.contains(&input) {
                return false;
            }
        }
    }

    saw_entry && saw_backedge
}

fn value_renderable_modulo_loop_phi(
    graph: &SsaGraph,
    value: ValueId,
    loop_phi: ValueId,
    renderable: &BTreeSet<ValueId>,
    certified_memory_read_insts: &BTreeSet<InstId>,
    visited: &mut BTreeSet<ValueId>,
    depth: usize,
) -> bool {
    if value == loop_phi || renderable.contains(&value) {
        return true;
    }
    if depth >= 32 || !visited.insert(value) {
        return false;
    }

    let result = graph
        .def_inst(value)
        .and_then(|inst_id| graph.inst(inst_id))
        .is_some_and(|inst| {
            let eligible = match &inst.payload {
                InstPayload::Phi { .. } => expression_phi_is_identity(inst),
                InstPayload::Op(op) => {
                    expression_op_is_pure(op)
                        || (op.is_memory_read() && certified_memory_read_insts.contains(&inst.id))
                }
            };
            eligible
                && inst.inputs.iter().all(|input| {
                    value_renderable_modulo_loop_phi(
                        graph,
                        *input,
                        loop_phi,
                        renderable,
                        certified_memory_read_insts,
                        visited,
                        depth + 1,
                    )
                })
        });

    visited.remove(&value);
    result
}

fn expression_op_is_pure(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Copy { .. }
            | SSAOp::IntAdd { .. }
            | SSAOp::IntSub { .. }
            | SSAOp::IntMult { .. }
            | SSAOp::IntDiv { .. }
            | SSAOp::IntSDiv { .. }
            | SSAOp::IntRem { .. }
            | SSAOp::IntSRem { .. }
            | SSAOp::IntNegate { .. }
            | SSAOp::IntCarry { .. }
            | SSAOp::IntSCarry { .. }
            | SSAOp::IntSBorrow { .. }
            | SSAOp::IntAnd { .. }
            | SSAOp::IntOr { .. }
            | SSAOp::IntXor { .. }
            | SSAOp::IntNot { .. }
            | SSAOp::IntLeft { .. }
            | SSAOp::IntRight { .. }
            | SSAOp::IntSRight { .. }
            | SSAOp::IntEqual { .. }
            | SSAOp::IntNotEqual { .. }
            | SSAOp::IntLess { .. }
            | SSAOp::IntSLess { .. }
            | SSAOp::IntLessEqual { .. }
            | SSAOp::IntSLessEqual { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::BoolNot { .. }
            | SSAOp::BoolAnd { .. }
            | SSAOp::BoolOr { .. }
            | SSAOp::BoolXor { .. }
            | SSAOp::Piece { .. }
            | SSAOp::Subpiece { .. }
            | SSAOp::PopCount { .. }
            | SSAOp::Lzcount { .. }
            | SSAOp::FloatAdd { .. }
            | SSAOp::FloatSub { .. }
            | SSAOp::FloatMult { .. }
            | SSAOp::FloatDiv { .. }
            | SSAOp::FloatNeg { .. }
            | SSAOp::FloatAbs { .. }
            | SSAOp::FloatSqrt { .. }
            | SSAOp::FloatCeil { .. }
            | SSAOp::FloatFloor { .. }
            | SSAOp::FloatRound { .. }
            | SSAOp::FloatNaN { .. }
            | SSAOp::FloatEqual { .. }
            | SSAOp::FloatNotEqual { .. }
            | SSAOp::FloatLess { .. }
            | SSAOp::FloatLessEqual { .. }
            | SSAOp::Int2Float { .. }
            | SSAOp::Float2Int { .. }
            | SSAOp::FloatFloat { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::PtrAdd { .. }
            | SSAOp::PtrSub { .. }
            | SSAOp::SegmentOp { .. }
            | SSAOp::Cast { .. }
            | SSAOp::Extract { .. }
            | SSAOp::Insert { .. }
    )
}

fn collect_return_value_certificates(
    function: &SSAFunction,
    graph: &SsaGraph,
) -> (Vec<ReturnValueCertificate>, BTreeMap<InstId, usize>) {
    let mut returns = Vec::new();
    let mut returns_by_inst = BTreeMap::new();
    let mut return_blocks = BTreeSet::new();

    for block in function.blocks() {
        let cfg_return = function
            .cfg()
            .get_block(block.addr)
            .is_some_and(|cfg_block| matches!(cfg_block.terminator, BlockTerminator::Return));
        if cfg_return
            || block
                .ops
                .iter()
                .any(|op| matches!(op, SSAOp::Return { .. }))
        {
            return_blocks.insert(block.addr);
        }
    }

    let mut return_context_blocks = return_blocks.clone();
    for block in function.blocks() {
        if function
            .successors(block.addr)
            .iter()
            .any(|succ| return_blocks.contains(succ))
        {
            return_context_blocks.insert(block.addr);
        }
    }

    for block in function.blocks() {
        let mut last_return_value_write = None;
        for (op_idx, op) in block.ops.iter().enumerate() {
            if let SSAOp::Return { target } = op {
                push_return_value_certificate(
                    graph,
                    &mut returns,
                    &mut returns_by_inst,
                    block.addr,
                    op_idx,
                    target,
                );
                continue;
            }

            if return_context_blocks.contains(&block.addr)
                && let Some(dst) = op.dst()
                && is_return_value_register(dst)
            {
                last_return_value_write = Some((op_idx, dst));
            }
        }

        if let Some((op_idx, dst)) = last_return_value_write {
            push_return_value_certificate(
                graph,
                &mut returns,
                &mut returns_by_inst,
                block.addr,
                op_idx,
                dst,
            );
        }
    }

    (returns, returns_by_inst)
}

fn collect_stack_reload_source_certificates(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    structured: &StructuredDataflowFacts,
) -> BTreeMap<ValueId, StackReloadSourceCertificate> {
    let store_sources = collect_stack_store_sources(function, graph, objects, memory, structured);
    let mut certificates = BTreeMap::new();
    let mut ready = VecDeque::new();

    for access in structured
        .memory_accesses
        .values()
        .filter(|access| !access.is_write)
    {
        let Some(value) = access.value else {
            continue;
        };
        let Some((base, offset)) = stack_object_root(objects, access.object) else {
            continue;
        };
        let Some(use_fact) = unique_memory_use_for_access(memory, access) else {
            continue;
        };
        let Some(source) = store_sources.get(&use_fact.version) else {
            continue;
        };
        if source.object != access.object || source.memory_width != access.width {
            continue;
        }
        let cert = StackReloadSourceCertificate {
            value,
            reload: value,
            source: source.value,
            canonical_source: source.canonical_source,
            object: access.object,
            base,
            offset,
            value_width: graph
                .value(value)
                .map(|value| value.var.size)
                .unwrap_or(access.width),
            memory_width: access.width,
            store_access: source.access,
            load_access: access.id,
            store_inst: source.access.inst,
            load_inst: access.id.inst,
        };
        insert_stack_reload_source_certificate(&mut certificates, &mut ready, cert);
    }

    while let Some(value) = ready.pop_front() {
        let Some(cert) = certificates.get(&value).cloned() else {
            continue;
        };
        for use_site in graph.use_sites(value) {
            let Some(inst) = graph.inst(use_site.inst) else {
                continue;
            };
            let Some(output) = stack_reload_propagation_output(inst, value) else {
                continue;
            };
            if certificates.contains_key(&output) {
                continue;
            }
            let value_width = graph
                .value(output)
                .map(|value| value.var.size)
                .unwrap_or(cert.value_width);
            insert_stack_reload_source_certificate(
                &mut certificates,
                &mut ready,
                StackReloadSourceCertificate {
                    value: output,
                    value_width,
                    ..cert.clone()
                },
            );
        }
    }

    certificates
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct StackStoreSource {
    value: ValueId,
    canonical_source: ValueId,
    object: ObjectId,
    memory_width: u32,
    access: StructuredAccessId,
}

fn collect_stack_store_sources(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
    structured: &StructuredDataflowFacts,
) -> BTreeMap<MemoryVersion, StackStoreSource> {
    let mut sources = BTreeMap::new();
    for access in structured
        .memory_accesses
        .values()
        .filter(|access| access.is_write)
    {
        let Some(value) = access.value else {
            continue;
        };
        if stack_object_root(objects, access.object).is_none() {
            continue;
        }
        let Some(def_fact) = unique_memory_def_for_access(memory, access) else {
            continue;
        };
        sources.insert(
            def_fact.next_version,
            StackStoreSource {
                value,
                canonical_source: canonical_stack_source_value(function, graph, value),
                object: access.object,
                memory_width: access.width,
                access: access.id,
            },
        );
    }
    sources
}

fn insert_stack_reload_source_certificate(
    certificates: &mut BTreeMap<ValueId, StackReloadSourceCertificate>,
    ready: &mut VecDeque<ValueId>,
    cert: StackReloadSourceCertificate,
) {
    let value = cert.value;
    if certificates.contains_key(&value) {
        return;
    }
    certificates.insert(value, cert);
    ready.push_back(value);
}

fn stack_reload_propagation_output(
    inst: &crate::graph::GraphInst,
    source: ValueId,
) -> Option<ValueId> {
    let output = inst.output?;
    match &inst.payload {
        InstPayload::Op(
            SSAOp::Copy { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::Cast { .. }
            | SSAOp::Subpiece { .. },
        ) if inst.inputs.len() == 1 && inst.inputs.first().copied() == Some(source) => Some(output),
        InstPayload::Phi { .. } if expression_phi_is_identity(inst) => {
            (inst.inputs.first().copied() == Some(source)).then_some(output)
        }
        _ => None,
    }
}

fn unique_memory_def_for_access<'a>(
    memory: &'a MemorySSAFacts,
    access: &StructuredMemoryAccessFact,
) -> Option<&'a MemoryDefFact> {
    let mut matches = memory
        .defs_by_inst
        .get(&access.id.inst)
        .into_iter()
        .flatten()
        .filter(|def| def.location.object == access.object && def.location.size == access.width);
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn unique_memory_use_for_access<'a>(
    memory: &'a MemorySSAFacts,
    access: &StructuredMemoryAccessFact,
) -> Option<&'a MemoryUseFact> {
    let mut matches = memory
        .uses_by_inst
        .get(&access.id.inst)
        .into_iter()
        .flatten()
        .filter(|use_fact| {
            use_fact.location.object == access.object && use_fact.location.size == access.width
        });
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn canonical_stack_source_value(
    function: &SSAFunction,
    graph: &SsaGraph,
    source: ValueId,
) -> ValueId {
    let Some(var) = graph.value(source).map(|value| &value.var) else {
        return source;
    };
    let root = canonical_value_root(function.decompile_prep_facts(), var);
    graph.value_id_for_var(root).unwrap_or(source)
}

type CallResultCertificateIndexes = (
    BTreeMap<ValueId, CallResultCertificate>,
    BTreeMap<InstId, ValueId>,
    BTreeMap<CallSiteId, Vec<ValueId>>,
);

fn collect_call_result_certificates(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    call_sites: &CallSiteFacts,
    structured: &StructuredDataflowFacts,
) -> CallResultCertificateIndexes {
    let mut call_results = BTreeMap::new();
    let mut call_results_by_inst = BTreeMap::new();
    let mut call_results_by_callsite = BTreeMap::<CallSiteId, Vec<ValueId>>::new();
    let callsites_by_op = call_sites
        .by_id
        .iter()
        .filter_map(|(id, fact)| graph.op_site_for_inst(fact.at).map(|site| (site, *id)))
        .collect::<BTreeMap<_, _>>();
    let mut out_states = BTreeMap::<u64, CallResultFlowState>::new();
    let mut worklist = function
        .blocks()
        .map(|block| block.addr)
        .collect::<VecDeque<_>>();
    let mut queued = function
        .blocks()
        .map(|block| block.addr)
        .collect::<BTreeSet<_>>();

    while let Some(block_addr) = worklist.pop_front() {
        queued.remove(&block_addr);
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        let input = merge_call_result_flow_predecessors(function, &out_states, block_addr);
        let output = process_call_result_flow_block(
            block,
            graph,
            objects,
            call_sites,
            structured,
            &callsites_by_op,
            input,
            &mut call_results,
            &mut call_results_by_inst,
            &mut call_results_by_callsite,
        );
        if out_states.get(&block_addr) == Some(&output) {
            continue;
        }
        out_states.insert(block_addr, output);
        for succ in function.successors(block_addr) {
            if queued.insert(succ) {
                worklist.push_back(succ);
            }
        }
    }

    for values in call_results_by_callsite.values_mut() {
        values.sort_unstable();
        values.dedup();
    }

    (call_results, call_results_by_inst, call_results_by_callsite)
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct CallResultFlowState {
    tracked: BTreeMap<ValueId, CallResultCertificate>,
    stack_owners: BTreeMap<(ObjectId, i64), CallResultCertificate>,
}

fn merge_call_result_flow_predecessors(
    function: &SSAFunction,
    out_states: &BTreeMap<u64, CallResultFlowState>,
    block_addr: u64,
) -> CallResultFlowState {
    let preds = function.predecessors(block_addr);
    let Some((first, rest)) = preds.split_first() else {
        return CallResultFlowState::default();
    };
    let mut merged = out_states.get(first).cloned().unwrap_or_default();
    for pred in rest {
        let pred_state = out_states.get(pred).cloned().unwrap_or_default();
        merged
            .tracked
            .retain(|value, cert| pred_state.tracked.get(value) == Some(cert));
        merged
            .stack_owners
            .retain(|slot, cert| pred_state.stack_owners.get(slot) == Some(cert));
    }
    merged
}

#[allow(clippy::too_many_arguments)]
fn process_call_result_flow_block(
    block: &crate::FunctionSSABlock,
    graph: &SsaGraph,
    objects: &ObjectModel,
    call_sites: &CallSiteFacts,
    structured: &StructuredDataflowFacts,
    callsites_by_op: &BTreeMap<(u64, usize), CallSiteId>,
    mut state: CallResultFlowState,
    call_results: &mut BTreeMap<ValueId, CallResultCertificate>,
    call_results_by_inst: &mut BTreeMap<InstId, ValueId>,
    call_results_by_callsite: &mut BTreeMap<CallSiteId, Vec<ValueId>>,
) -> CallResultFlowState {
    let mut active_call = None;
    for (op_index, op) in block.ops.iter().enumerate() {
        match op {
            SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                kill_return_register_flow_values(&mut state, graph);
                active_call = callsites_by_op.get(&(block.addr, op_index)).copied();
            }
            SSAOp::CallDefine { dst } => {
                let Some(call_site_id) = active_call else {
                    continue;
                };
                let Some(call_site) = call_sites.by_id.get(&call_site_id) else {
                    continue;
                };
                let Some(carrier) = return_carrier_for_value(dst) else {
                    continue;
                };
                let Some(value) = graph.value_id_for_var(dst) else {
                    continue;
                };
                let cert = CallResultCertificate {
                    call_site: call_site_id,
                    at: graph
                        .inst_id_for_op_site(block.addr, op_index)
                        .unwrap_or(call_site.at),
                    block_addr: block.addr,
                    op_index,
                    value,
                    width: dst.size,
                    carrier,
                    owner: Some(ValueOwner::Value(value)),
                };
                insert_call_result_certificate(
                    call_results,
                    call_results_by_inst,
                    call_results_by_callsite,
                    &mut state.tracked,
                    cert,
                );
            }
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Cast { dst, src, .. }
            | SSAOp::Subpiece { dst, src, .. } => {
                let Some(src_value) = graph.value_id_for_var(src) else {
                    continue;
                };
                let Some(source) = state.tracked.get(&src_value) else {
                    continue;
                };
                let Some(dst_value) = graph.value_id_for_var(dst) else {
                    continue;
                };
                let cert = CallResultCertificate {
                    call_site: source.call_site,
                    at: graph
                        .inst_id_for_op_site(block.addr, op_index)
                        .unwrap_or(source.at),
                    block_addr: block.addr,
                    op_index,
                    value: dst_value,
                    width: dst.size,
                    carrier: source.carrier.clone(),
                    owner: source.owner.clone().or(Some(ValueOwner::Value(src_value))),
                };
                insert_call_result_certificate(
                    call_results,
                    call_results_by_inst,
                    call_results_by_callsite,
                    &mut state.tracked,
                    cert,
                );
            }
            SSAOp::Store { val, .. } => {
                let value = graph.value_id_for_var(val);
                let stack_access = value
                    .and_then(|value| {
                        stack_memory_access_at(
                            structured,
                            objects,
                            block.addr,
                            op_index,
                            true,
                            Some(value),
                        )
                    })
                    .or_else(|| {
                        stack_memory_access_at(
                            structured, objects, block.addr, op_index, true, None,
                        )
                    });
                let Some((object, offset, _access)) = stack_access else {
                    continue;
                };
                let Some(value) = value else {
                    state.stack_owners.remove(&(object, offset));
                    continue;
                };
                let Some(source) = state.tracked.get(&value).cloned() else {
                    state.stack_owners.remove(&(object, offset));
                    continue;
                };
                state.stack_owners.insert(
                    (object, offset),
                    CallResultCertificate {
                        owner: Some(ValueOwner::StackSlot { object, offset }),
                        ..source.clone()
                    },
                );
                call_results.entry(value).and_modify(|cert| {
                    cert.owner = Some(ValueOwner::StackSlot { object, offset });
                });
                state.tracked.entry(value).and_modify(|cert| {
                    cert.owner = Some(ValueOwner::StackSlot { object, offset });
                });
            }
            SSAOp::Load { dst, .. } => {
                let Some(dst_value) = graph.value_id_for_var(dst) else {
                    continue;
                };
                let Some((object, offset, access)) = stack_memory_access_at(
                    structured,
                    objects,
                    block.addr,
                    op_index,
                    false,
                    Some(dst_value),
                ) else {
                    continue;
                };
                let Some(source) = state.stack_owners.get(&(object, offset)) else {
                    continue;
                };
                let cert = CallResultCertificate {
                    call_site: source.call_site,
                    at: graph
                        .inst_id_for_op_site(block.addr, op_index)
                        .unwrap_or(source.at),
                    block_addr: block.addr,
                    op_index,
                    value: dst_value,
                    width: dst.size,
                    carrier: ReturnCarrier::StackSlot {
                        object,
                        offset,
                        memory_access: Some(access),
                    },
                    owner: Some(ValueOwner::StackSlot { object, offset }),
                };
                insert_call_result_certificate(
                    call_results,
                    call_results_by_inst,
                    call_results_by_callsite,
                    &mut state.tracked,
                    cert,
                );
            }
            _ => {}
        }
    }
    state
}

fn kill_return_register_flow_values(state: &mut CallResultFlowState, graph: &SsaGraph) {
    state.tracked.retain(|value, _| {
        graph
            .value(*value)
            .is_none_or(|value| !is_return_value_register(&value.var))
    });
}

fn insert_call_result_certificate(
    call_results: &mut BTreeMap<ValueId, CallResultCertificate>,
    call_results_by_inst: &mut BTreeMap<InstId, ValueId>,
    call_results_by_callsite: &mut BTreeMap<CallSiteId, Vec<ValueId>>,
    tracked: &mut BTreeMap<ValueId, CallResultCertificate>,
    cert: CallResultCertificate,
) {
    call_results_by_inst.insert(cert.at, cert.value);
    call_results_by_callsite
        .entry(cert.call_site)
        .or_default()
        .push(cert.value);
    tracked.insert(cert.value, cert.clone());
    call_results.insert(cert.value, cert);
}

fn stack_memory_access_at(
    structured: &StructuredDataflowFacts,
    objects: &ObjectModel,
    block_addr: u64,
    op_index: usize,
    is_write: bool,
    value: Option<ValueId>,
) -> Option<(ObjectId, i64, StructuredAccessId)> {
    structured
        .memory_accesses
        .iter()
        .filter(|(_, access)| {
            access.block_addr == block_addr
                && access.op_index == op_index
                && access.is_write == is_write
                && value.is_none_or(|value| access.value == Some(value))
        })
        .filter_map(|(access_id, access)| {
            stack_object_offset(objects, access.object)
                .map(|offset| (access.object, offset, *access_id))
        })
        .next()
}

fn push_return_value_certificate(
    graph: &SsaGraph,
    returns: &mut Vec<ReturnValueCertificate>,
    returns_by_inst: &mut BTreeMap<InstId, usize>,
    block_addr: u64,
    op_idx: usize,
    value_var: &SSAVar,
) {
    let Some(at) = graph.inst_id_for_op_site(block_addr, op_idx) else {
        return;
    };
    if returns_by_inst.contains_key(&at) {
        return;
    }
    let Some(value) = graph.value_id_for_var(value_var) else {
        return;
    };
    returns_by_inst.insert(at, returns.len());
    returns.push(ReturnValueCertificate {
        at,
        block_addr,
        op_index: op_idx,
        value,
        width: value_var.size,
        carrier: return_carrier_for_value(value_var),
    });
}

fn return_carrier_for_value(value: &SSAVar) -> Option<ReturnCarrier> {
    if is_return_value_register(value) {
        return Some(ReturnCarrier::Register {
            name: value.name.clone(),
        });
    }
    None
}

fn is_return_value_register(value: &SSAVar) -> bool {
    if !value.is_register() {
        return false;
    }
    let name = value
        .name
        .trim()
        .trim_start_matches('$')
        .to_ascii_lowercase();
    matches!(
        name.as_str(),
        "rax" | "eax" | "ax" | "al" | "xmm0" | "st0" | "x0" | "w0" | "r0" | "v0" | "a0" | "r3"
    )
}

fn collect_structured_loop_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    predicates: &PredicateFacts,
) -> BTreeMap<LoopId, StructuredLoopFact> {
    let mut latches_by_header = BTreeMap::<u64, BTreeSet<u64>>::new();
    for &block_addr in function.block_addrs() {
        for succ in function.successors(block_addr) {
            if function.dominates(succ, block_addr) {
                latches_by_header
                    .entry(succ)
                    .or_default()
                    .insert(block_addr);
            }
        }
    }

    let mut loops = BTreeMap::new();
    for (idx, (header, latches)) in latches_by_header.into_iter().enumerate() {
        let id = LoopId(idx as u32);
        let body_set = natural_loop_body(function, header, &latches);
        let body = body_set.iter().copied().collect::<Vec<_>>();
        let exits = loop_exits(function, &body_set);
        let condition = loop_condition(predicates, header, &body_set, &exits);
        let (induction_phi, induction_init, induction_update) =
            loop_induction_values(graph, header, &latches, &body_set);
        let bound = loop_bound_value(
            graph,
            predicates,
            condition,
            induction_phi,
            induction_update,
        );
        loops.insert(
            id,
            StructuredLoopFact {
                id,
                kind: if latches.contains(&header) {
                    StructuredLoopKind::SelfLoop
                } else {
                    StructuredLoopKind::Natural
                },
                header,
                latches: latches.iter().copied().collect(),
                body,
                exits,
                condition,
                induction_phi,
                induction_init,
                induction_update,
                bound,
            },
        );
    }
    loops
}

fn natural_loop_body(
    function: &SSAFunction,
    header: u64,
    latches: &BTreeSet<u64>,
) -> BTreeSet<u64> {
    let mut body = BTreeSet::new();
    body.insert(header);
    let mut stack = latches.iter().copied().collect::<Vec<_>>();
    while let Some(addr) = stack.pop() {
        if !function.dominates(header, addr) {
            continue;
        }
        if !body.insert(addr) {
            continue;
        }
        for pred in function.predecessors(addr) {
            if !body.contains(&pred) {
                stack.push(pred);
            }
        }
    }
    body
}

fn loop_exits(function: &SSAFunction, body: &BTreeSet<u64>) -> Vec<u64> {
    let mut exits = BTreeSet::new();
    for block in body {
        for succ in function.successors(*block) {
            if !body.contains(&succ) {
                exits.insert(succ);
            }
        }
    }
    exits.into_iter().collect()
}

fn loop_condition(
    predicates: &PredicateFacts,
    header: u64,
    body: &BTreeSet<u64>,
    exits: &[u64],
) -> Option<PredicateId> {
    let exit_set = exits.iter().copied().collect::<BTreeSet<_>>();
    predicates
        .predicates
        .values()
        .filter(|predicate| body.contains(&predicate.block_addr))
        .filter(|predicate| {
            (body.contains(&predicate.true_target) && exit_set.contains(&predicate.false_target))
                || (body.contains(&predicate.false_target)
                    && exit_set.contains(&predicate.true_target))
        })
        .min_by_key(|predicate| {
            (
                usize::from(predicate.block_addr != header),
                predicate.block_addr,
                predicate.id,
            )
        })
        .map(|predicate| predicate.id)
}

fn loop_induction_values(
    graph: &SsaGraph,
    header: u64,
    latches: &BTreeSet<u64>,
    body: &BTreeSet<u64>,
) -> (Option<ValueId>, Option<ValueId>, Option<ValueId>) {
    let Some(header_id) = graph.block_id_for_addr(header) else {
        return (None, None, None);
    };
    let Some(header_block) = graph.block(header_id) else {
        return (None, None, None);
    };

    let mut best = None;
    for inst_id in &header_block.insts {
        let Some(inst) = graph.inst(*inst_id) else {
            continue;
        };
        let InstPayload::Phi { predecessors } = &inst.payload else {
            continue;
        };
        let Some(output) = inst.output else {
            continue;
        };
        let mut init = None;
        let mut update = None;
        for (pred_id, input) in predecessors
            .iter()
            .copied()
            .zip(inst.inputs.iter().copied())
        {
            let Some(pred_addr) = graph.block(pred_id).map(|block| block.addr) else {
                continue;
            };
            if latches.contains(&pred_addr) {
                update = Some(input);
            } else if !body.contains(&pred_addr) {
                init = Some(input);
            }
        }
        if init.is_none() || update.is_none() {
            continue;
        }
        let score = if is_low_value_induction_phi(graph, output) {
            1
        } else {
            0
        };
        let candidate = (score, output, init, update);
        if best.as_ref().is_none_or(
            |current: &(usize, ValueId, Option<ValueId>, Option<ValueId>)| candidate < *current,
        ) {
            best = Some(candidate);
        }
    }
    best.map(|(_, phi, init, update)| (Some(phi), init, update))
        .unwrap_or((None, None, None))
}

fn is_low_value_induction_phi(graph: &SsaGraph, value: ValueId) -> bool {
    let Some(var) = graph.value(value).map(|value| &value.var) else {
        return true;
    };
    let name = var.name.trim_start_matches("reg:").to_ascii_lowercase();
    matches!(name.as_str(), "cf" | "pf" | "af" | "zf" | "sf" | "of")
        || name.starts_with("flag")
        || name.starts_with("tmp")
        || name == "rsp"
        || name == "esp"
        || name == "rbp"
        || name == "ebp"
}

fn loop_bound_value(
    graph: &SsaGraph,
    predicates: &PredicateFacts,
    condition: Option<PredicateId>,
    induction_phi: Option<ValueId>,
    induction_update: Option<ValueId>,
) -> Option<ValueId> {
    let comparison = predicates
        .predicates
        .get(&condition?)?
        .comparison
        .as_ref()?;
    let induction = induction_phi.or(induction_update)?;
    let lhs_depends = value_depends_on(graph, comparison.lhs, induction);
    let rhs_depends = value_depends_on(graph, comparison.rhs, induction);
    match (lhs_depends, rhs_depends) {
        (true, false) => Some(comparison.rhs),
        (false, true) => Some(comparison.lhs),
        _ => None,
    }
}

fn value_depends_on(graph: &SsaGraph, value: ValueId, needle: ValueId) -> bool {
    if value == needle {
        return true;
    }
    let mut visited = BTreeSet::new();
    let mut stack = vec![(value, 0usize)];
    while let Some((current, depth)) = stack.pop() {
        if current == needle {
            return true;
        }
        if depth >= 16 || !visited.insert(current) {
            continue;
        }
        let Some(def_inst) = graph.def_inst(current) else {
            continue;
        };
        let Some(inst) = graph.inst(def_inst) else {
            continue;
        };
        for input in &inst.inputs {
            stack.push((*input, depth + 1));
        }
    }
    false
}

fn collect_structured_memory_access_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    memory: &MemorySSAFacts,
) -> BTreeMap<StructuredAccessId, StructuredMemoryAccessFact> {
    let mut access_facts = BTreeMap::new();
    for block in function.blocks() {
        for (op_index, op) in block.ops.iter().enumerate() {
            let Some(inst) = graph.inst_id_for_op_site(block.addr, op_index) else {
                continue;
            };
            let mut ordinal = 0u32;
            match op {
                SSAOp::Load { dst, addr, .. }
                | SSAOp::LoadLinked { dst, addr, .. }
                | SSAOp::LoadGuarded { dst, addr, .. } => {
                    if let Some(address) = graph.value_id_for_var(addr) {
                        for use_fact in memory.uses_by_inst.get(&inst).into_iter().flatten() {
                            insert_structured_memory_access(
                                &mut access_facts,
                                inst,
                                &mut ordinal,
                                block.addr,
                                op_index,
                                use_fact.location.object,
                                address,
                                graph.value_id_for_var(dst),
                                false,
                                use_fact.location.size,
                            );
                        }
                    }
                }
                SSAOp::Store { addr, val, .. } | SSAOp::StoreGuarded { addr, val, .. } => {
                    if let Some(address) = graph.value_id_for_var(addr) {
                        for def_fact in memory.defs_by_inst.get(&inst).into_iter().flatten() {
                            insert_structured_memory_access(
                                &mut access_facts,
                                inst,
                                &mut ordinal,
                                block.addr,
                                op_index,
                                def_fact.location.object,
                                address,
                                graph.value_id_for_var(val),
                                true,
                                def_fact.location.size,
                            );
                        }
                    }
                }
                SSAOp::StoreConditional { addr, val, .. } => {
                    if let Some(address) = graph.value_id_for_var(addr) {
                        for use_fact in memory.uses_by_inst.get(&inst).into_iter().flatten() {
                            insert_structured_memory_access(
                                &mut access_facts,
                                inst,
                                &mut ordinal,
                                block.addr,
                                op_index,
                                use_fact.location.object,
                                address,
                                None,
                                false,
                                use_fact.location.size,
                            );
                        }
                        for def_fact in memory.defs_by_inst.get(&inst).into_iter().flatten() {
                            insert_structured_memory_access(
                                &mut access_facts,
                                inst,
                                &mut ordinal,
                                block.addr,
                                op_index,
                                def_fact.location.object,
                                address,
                                graph.value_id_for_var(val),
                                true,
                                def_fact.location.size,
                            );
                        }
                    }
                }
                SSAOp::AtomicCAS {
                    dst,
                    addr,
                    replacement,
                    ..
                } => {
                    if let Some(address) = graph.value_id_for_var(addr) {
                        for use_fact in memory.uses_by_inst.get(&inst).into_iter().flatten() {
                            insert_structured_memory_access(
                                &mut access_facts,
                                inst,
                                &mut ordinal,
                                block.addr,
                                op_index,
                                use_fact.location.object,
                                address,
                                graph.value_id_for_var(dst),
                                false,
                                use_fact.location.size,
                            );
                        }
                        for def_fact in memory.defs_by_inst.get(&inst).into_iter().flatten() {
                            insert_structured_memory_access(
                                &mut access_facts,
                                inst,
                                &mut ordinal,
                                block.addr,
                                op_index,
                                def_fact.location.object,
                                address,
                                graph.value_id_for_var(replacement),
                                true,
                                def_fact.location.size,
                            );
                        }
                    }
                }
                _ => {}
            }
            if ordinal == 0
                && let Some((address_var, value_var, is_write, width)) =
                    fallback_memory_access_shape(op)
                && let Some(address) = graph.value_id_for_var(address_var)
            {
                let object = objects.escaped_unknown_object().unwrap_or(ObjectId(0));
                insert_structured_memory_access(
                    &mut access_facts,
                    inst,
                    &mut ordinal,
                    block.addr,
                    op_index,
                    object,
                    address,
                    value_var.and_then(|value| graph.value_id_for_var(value)),
                    is_write,
                    width,
                );
            }
        }
    }
    access_facts
}

fn fallback_memory_access_shape(op: &SSAOp) -> Option<(&SSAVar, Option<&SSAVar>, bool, u32)> {
    match op {
        SSAOp::Load { dst, addr, .. }
        | SSAOp::LoadLinked { dst, addr, .. }
        | SSAOp::LoadGuarded { dst, addr, .. } => Some((addr, Some(dst), false, dst.size)),
        SSAOp::Store { addr, val, .. } | SSAOp::StoreGuarded { addr, val, .. } => {
            Some((addr, Some(val), true, val.size))
        }
        SSAOp::StoreConditional { addr, val, .. } => Some((addr, Some(val), true, val.size)),
        SSAOp::AtomicCAS {
            addr, replacement, ..
        } => Some((addr, Some(replacement), true, replacement.size)),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn insert_structured_memory_access(
    access_facts: &mut BTreeMap<StructuredAccessId, StructuredMemoryAccessFact>,
    inst: InstId,
    ordinal: &mut u32,
    block_addr: u64,
    op_index: usize,
    object: ObjectId,
    address: ValueId,
    value: Option<ValueId>,
    is_write: bool,
    width: u32,
) {
    let id = StructuredAccessId {
        inst,
        ordinal: *ordinal,
    };
    *ordinal = (*ordinal).saturating_add(1);
    access_facts.insert(
        id,
        StructuredMemoryAccessFact {
            id,
            block_addr,
            op_index,
            object,
            address,
            value,
            is_write,
            width,
        },
    );
}

fn collect_structured_recursive_call_facts(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_sites: &CallSiteFacts,
) -> BTreeMap<CallSiteId, StructuredRecursiveCallFact> {
    let mut recursive_calls = BTreeMap::new();
    for (call_site, fact) in &call_sites.by_id {
        let Some(target) = fact.direct_target else {
            continue;
        };
        if target != function.entry {
            continue;
        }
        let Some((block_addr, op_index)) = graph.op_site_for_inst(fact.at) else {
            continue;
        };
        recursive_calls.insert(
            *call_site,
            StructuredRecursiveCallFact {
                call_site: *call_site,
                block_addr,
                op_index,
                target,
            },
        );
    }
    recursive_calls
}

fn collect_predicate_facts(function: &SSAFunction, graph: &SsaGraph) -> PredicateFacts {
    let mut predicates = BTreeMap::new();
    let mut block_assumptions = BTreeMap::<u64, Vec<BlockAssumption>>::new();
    let mut switches = BTreeMap::new();
    let compare_defs = collect_compare_defs(function, graph);
    let mut next_predicate_id = 0u32;

    for &block_addr in function.block_addrs() {
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        let Some(cfg_block) = function.cfg().get_block(block_addr) else {
            continue;
        };
        match &cfg_block.terminator {
            BlockTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => {
                let Some(SSAOp::CBranch { cond, .. }) = block.ops.last() else {
                    continue;
                };
                let id = PredicateId(next_predicate_id);
                next_predicate_id = next_predicate_id.saturating_add(1);
                predicates.insert(
                    id,
                    PredicateFact {
                        id,
                        block_addr,
                        condition: graph
                            .value_id_for_var(cond)
                            .expect("predicate condition in graph"),
                        comparison: compare_defs.get(cond).cloned(),
                        true_target: *true_target,
                        false_target: *false_target,
                    },
                );
                block_assumptions
                    .entry(*true_target)
                    .or_default()
                    .push(BlockAssumption {
                        predecessor: block_addr,
                        predicate: id,
                        truth: true,
                    });
                block_assumptions
                    .entry(*false_target)
                    .or_default()
                    .push(BlockAssumption {
                        predecessor: block_addr,
                        predicate: id,
                        truth: false,
                    });
            }
            BlockTerminator::Switch { cases, default } => {
                switches.insert(
                    block_addr,
                    SwitchPredicateFact {
                        block_addr,
                        selector: function
                            .infer_switch_selector_var(block.addr)
                            .and_then(|selector| graph.value_id_for_var(&selector)),
                        cases: cases.clone(),
                        default: *default,
                    },
                );
            }
            _ => {}
        }
    }

    PredicateFacts {
        predicates,
        block_assumptions,
        switches,
    }
}

fn collect_call_sites(
    function: &SSAFunction,
    graph: &SsaGraph,
    prep_facts: Option<&DecompilePrepFacts>,
) -> CallSiteFacts {
    let mut by_id = BTreeMap::new();
    let mut by_inst = BTreeMap::new();
    let mut next_id = 0u32;

    for &block_addr in function.block_addrs() {
        let Some(block) = function.get_block(block_addr) else {
            continue;
        };
        let fallthrough = match function
            .cfg()
            .get_block(block_addr)
            .map(|block| &block.terminator)
        {
            Some(BlockTerminator::Call { fallthrough, .. })
            | Some(BlockTerminator::IndirectCall { fallthrough }) => *fallthrough,
            _ => None,
        };

        for (op_idx, op) in block.ops.iter().enumerate() {
            let target = match op {
                SSAOp::Call { target } | SSAOp::CallInd { target } => target.clone(),
                _ => continue,
            };
            let Some(inst_id) = graph.inst_id_for_op_site(block_addr, op_idx) else {
                continue;
            };
            let Some(target_id) = graph.value_id_for_var(&target) else {
                continue;
            };
            let id = CallSiteId(next_id);
            next_id = next_id.saturating_add(1);
            let direct_target = resolve_const_value(prep_facts, &target);
            by_inst.insert(inst_id, id);
            by_id.insert(
                id,
                CallSiteFact {
                    id,
                    at: inst_id,
                    target: target_id,
                    direct_target,
                    fallthrough: if op_idx + 1 == block.ops.len() {
                        fallthrough
                    } else {
                        None
                    },
                    memory_effect: CallMemoryEffect::Unknown,
                },
            );
        }
    }

    CallSiteFacts { by_id, by_inst }
}

fn collect_call_argument_values(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_site: &CallSiteFact,
) -> Vec<ValueId> {
    let Some((block_addr, op_idx)) = graph.op_site_for_inst(call_site.at) else {
        return Vec::new();
    };
    let Some(block) = function.get_block(block_addr) else {
        return Vec::new();
    };

    let mut by_index = BTreeMap::<usize, ValueId>::new();
    for op in block.ops[..op_idx].iter().rev() {
        if matches!(
            op,
            SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::Return { .. }
        ) {
            break;
        }
        let Some((index, value, _)) = call_argument_value_for_op(op, graph) else {
            continue;
        };
        by_index.entry(index).or_insert(value);
    }

    let mut values = Vec::new();
    for index in 0..16 {
        let Some(value) = by_index.remove(&index) else {
            break;
        };
        values.push(value);
    }
    values
}

fn collect_register_call_argument_certificates(
    function: &SSAFunction,
    graph: &SsaGraph,
    call_site: &CallSiteFact,
) -> Vec<CallArgumentCertificate> {
    let Some((block_addr, op_idx)) = graph.op_site_for_inst(call_site.at) else {
        return Vec::new();
    };
    let Some(block) = function.get_block(block_addr) else {
        return Vec::new();
    };

    let mut by_index = BTreeMap::<usize, CallArgumentCertificate>::new();
    for (producer_idx, op) in block.ops[..op_idx].iter().enumerate().rev() {
        if matches!(
            op,
            SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::Return { .. }
        ) {
            break;
        }
        let Some((index, value, register)) = call_argument_value_for_op(op, graph) else {
            continue;
        };
        by_index.entry(index).or_insert(CallArgumentCertificate {
            index,
            value,
            location: CallArgumentLocation::Register { name: register },
            source_inst: graph.inst_id_for_op_site(block_addr, producer_idx),
        });
    }

    let mut certificates = Vec::new();
    for index in 0..16 {
        let Some(certificate) = by_index.remove(&index) else {
            break;
        };
        certificates.push(certificate);
    }
    certificates
}

fn collect_stack_call_argument_values(
    function: &SSAFunction,
    graph: &SsaGraph,
    objects: &ObjectModel,
    structured: &StructuredDataflowFacts,
    call_site: &CallSiteFact,
) -> Vec<StackCallArgumentCertificate> {
    let Some((block_addr, op_idx)) = graph.op_site_for_inst(call_site.at) else {
        return Vec::new();
    };
    let Some(block) = function.get_block(block_addr) else {
        return Vec::new();
    };

    let mut by_offset = BTreeMap::<i64, StackCallArgumentCertificate>::new();
    for (producer_idx, op) in block.ops[..op_idx].iter().enumerate().rev() {
        if matches!(
            op,
            SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::Return { .. }
        ) {
            break;
        }
        let SSAOp::Store { val, .. } = op else {
            continue;
        };
        let Some(value) = graph.value_id_for_var(val) else {
            continue;
        };

        for (access_id, access) in structured.memory_accesses.iter().filter(|(_, access)| {
            access.block_addr == block_addr && access.op_index == producer_idx && access.is_write
        }) {
            if access.value != Some(value) {
                continue;
            }
            let Some(offset) = stack_pointer_object_offset(objects, access.object) else {
                continue;
            };
            if offset < 0 {
                continue;
            }
            by_offset
                .entry(offset)
                .or_insert(StackCallArgumentCertificate {
                    stack_offset: offset,
                    value,
                    memory_access: *access_id,
                });
        }
    }

    by_offset.into_values().collect()
}

fn collect_stack_call_argument_certificates(
    stack_argument_values: &[StackCallArgumentCertificate],
    structured: &StructuredDataflowFacts,
) -> Vec<CallArgumentCertificate> {
    stack_argument_values
        .iter()
        .enumerate()
        .filter_map(|(index, stack_arg)| {
            let access = structured.memory_accesses.get(&stack_arg.memory_access)?;
            Some(CallArgumentCertificate {
                index,
                value: stack_arg.value,
                location: CallArgumentLocation::Stack {
                    object: access.object,
                    offset: stack_arg.stack_offset,
                    memory_access: stack_arg.memory_access,
                },
                source_inst: Some(stack_arg.memory_access.inst),
            })
        })
        .collect()
}

fn stack_pointer_object_offset(objects: &ObjectModel, object: ObjectId) -> Option<i64> {
    let fact = objects.object(object)?;
    match fact.kind {
        ObjectKind::StackSlot {
            base: StackAddressBase::StackPointer,
            offset,
        }
        | ObjectKind::FrameObject {
            base: StackAddressBase::StackPointer,
            offset,
        } => Some(offset),
        _ => None,
    }
}

fn stack_object_offset(objects: &ObjectModel, object: ObjectId) -> Option<i64> {
    stack_object_root(objects, object).map(|(_, offset)| offset)
}

fn stack_object_root(objects: &ObjectModel, object: ObjectId) -> Option<(StackAddressBase, i64)> {
    let fact = objects.object(object)?;
    match fact.kind {
        ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset } => {
            Some((base, offset))
        }
        _ => None,
    }
}

fn call_argument_value_for_op(op: &SSAOp, graph: &SsaGraph) -> Option<(usize, ValueId, String)> {
    let dst = op.dst()?;
    let index = canonical_abi_arg_index(&dst.name)?;
    let source = match op {
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => graph.value_id_for_var(src),
        _ => None,
    }
    .or_else(|| graph.value_id_for_var(dst))?;
    Some((index, source, dst.name.clone()))
}

fn canonical_abi_arg_index(name: &str) -> Option<usize> {
    match name.to_ascii_lowercase().as_str() {
        "rdi" | "edi" | "di" | "dil" => Some(0),
        "rsi" | "esi" | "si" | "sil" => Some(1),
        "rdx" | "edx" | "dx" | "dl" => Some(2),
        "rcx" | "ecx" | "cx" | "cl" => Some(3),
        "r8" | "r8d" | "r8w" | "r8b" => Some(4),
        "r9" | "r9d" | "r9w" | "r9b" => Some(5),
        "x0" | "w0" | "a0" => Some(0),
        "x1" | "w1" | "a1" => Some(1),
        "x2" | "w2" | "a2" => Some(2),
        "x3" | "w3" | "a3" => Some(3),
        "x4" | "w4" | "a4" => Some(4),
        "x5" | "w5" | "a5" => Some(5),
        "x6" | "w6" | "a6" => Some(6),
        "x7" | "w7" | "a7" => Some(7),
        _ => None,
    }
}

fn collect_compare_defs(
    function: &SSAFunction,
    graph: &SsaGraph,
) -> BTreeMap<SSAVar, CompareProvenance> {
    let mut compare_defs = BTreeMap::new();
    let mut sub_sources = BTreeMap::<SSAVar, (ValueId, ValueId)>::new();
    let mut signed_overflow_sources = BTreeMap::<SSAVar, (ValueId, ValueId)>::new();
    let mut signed_sign_sources = BTreeMap::<SSAVar, (ValueId, ValueId)>::new();
    for block in function.blocks() {
        for op in &block.ops {
            match op {
                SSAOp::IntSub { dst, a, b } => {
                    if let (Some(lhs), Some(rhs)) =
                        (graph.value_id_for_var(a), graph.value_id_for_var(b))
                    {
                        sub_sources.insert(dst.clone(), (lhs, rhs));
                    }
                }
                SSAOp::IntSBorrow { dst, a, b } => {
                    if let (Some(lhs), Some(rhs)) =
                        (graph.value_id_for_var(a), graph.value_id_for_var(b))
                    {
                        signed_overflow_sources.insert(dst.clone(), (lhs, rhs));
                    }
                }
                SSAOp::IntSLess { dst, a, b } if const_value(b) == Some(0) => {
                    if let Some((lhs, rhs)) = sub_sources.get(a).copied() {
                        signed_sign_sources.insert(dst.clone(), (lhs, rhs));
                    }
                }
                _ => {}
            }
            let Some((dst, kind, lhs, rhs)) = compare_components(op) else {
                if let Some((dst, kind, lhs, rhs)) = signed_flag_compare_components(
                    op,
                    &signed_overflow_sources,
                    &signed_sign_sources,
                ) {
                    compare_defs.insert(dst.clone(), CompareProvenance { kind, lhs, rhs });
                }
                continue;
            };
            let Some(lhs_id) = graph.value_id_for_var(lhs) else {
                continue;
            };
            let Some(rhs_id) = graph.value_id_for_var(rhs) else {
                continue;
            };
            compare_defs.insert(
                dst.clone(),
                CompareProvenance {
                    kind,
                    lhs: lhs_id,
                    rhs: rhs_id,
                },
            );
            if let Some((dst, kind, lhs, rhs)) =
                signed_flag_compare_components(op, &signed_overflow_sources, &signed_sign_sources)
            {
                compare_defs.insert(dst.clone(), CompareProvenance { kind, lhs, rhs });
            }
        }
    }
    compare_defs
}

fn signed_flag_compare_components<'a>(
    op: &'a SSAOp,
    signed_overflow_sources: &BTreeMap<SSAVar, (ValueId, ValueId)>,
    signed_sign_sources: &BTreeMap<SSAVar, (ValueId, ValueId)>,
) -> Option<(&'a SSAVar, CompareKind, ValueId, ValueId)> {
    let SSAOp::IntNotEqual { dst, a, b } = op else {
        return None;
    };
    let overflow = signed_overflow_sources.get(a);
    let sign = signed_sign_sources.get(b);
    let (lhs, rhs) = overflow
        .zip(sign)
        .filter(|(overflow, sign)| overflow == sign)
        .map(|(overflow, _)| *overflow)
        .or_else(|| {
            let overflow = signed_overflow_sources.get(b);
            let sign = signed_sign_sources.get(a);
            overflow
                .zip(sign)
                .filter(|(overflow, sign)| overflow == sign)
                .map(|(overflow, _)| *overflow)
        })?;
    Some((dst, CompareKind::SignedLess, lhs, rhs))
}

fn compare_components(op: &SSAOp) -> Option<(&SSAVar, CompareKind, &SSAVar, &SSAVar)> {
    match op {
        SSAOp::IntEqual { dst, a, b } => Some((dst, CompareKind::Equal, a, b)),
        SSAOp::IntNotEqual { dst, a, b } => Some((dst, CompareKind::NotEqual, a, b)),
        SSAOp::IntLess { dst, a, b } => Some((dst, CompareKind::Less, a, b)),
        SSAOp::IntSLess { dst, a, b } => Some((dst, CompareKind::SignedLess, a, b)),
        SSAOp::IntLessEqual { dst, a, b } => Some((dst, CompareKind::LessEqual, a, b)),
        SSAOp::IntSLessEqual { dst, a, b } => Some((dst, CompareKind::SignedLessEqual, a, b)),
        _ => None,
    }
}

fn memory_location_for_addr(
    prep_facts: Option<&DecompilePrepFacts>,
    object_model: &ObjectModel,
    graph: &SsaGraph,
    addr: &SSAVar,
    space: &str,
    size: u32,
) -> MemoryLocation {
    let object = object_model
        .object_for_var(graph, addr)
        .or_else(|| {
            resolve_stack_root(prep_facts, addr)
                .and_then(|root| object_model.stack_objects.get(&root).copied())
        })
        .or_else(|| {
            resolve_const_value(prep_facts, addr).and_then(|address| {
                object_model
                    .global_objects
                    .get(&GlobalObjectKey {
                        space: space.to_string(),
                        address,
                    })
                    .copied()
            })
        })
        .or_else(|| object_model.escaped_unknown_object())
        .unwrap_or(ObjectId(0));
    MemoryLocation {
        object,
        offset: 0,
        size,
    }
}

fn resolve_const_value(facts: Option<&DecompilePrepFacts>, var: &SSAVar) -> Option<u64> {
    let root = canonical_value_root(facts, var);
    const_value(root).or_else(|| const_value(var))
}

fn resolve_stack_root(
    facts: Option<&DecompilePrepFacts>,
    var: &SSAVar,
) -> Option<StackAddressRoot> {
    let facts = facts?;
    let root = canonical_value_root(Some(facts), var);
    facts
        .stack_address_root_of(var)
        .copied()
        .or_else(|| facts.stack_address_root_of(root).copied())
        .or_else(|| stack_base_root_for_name(&root.name))
}

fn canonical_value_root<'a>(facts: Option<&'a DecompilePrepFacts>, var: &'a SSAVar) -> &'a SSAVar {
    let Some(facts) = facts else {
        return var;
    };
    let mut current = var;
    for _ in 0..32 {
        let Some(next) = facts.canonical_root_of(current) else {
            break;
        };
        if next == current {
            break;
        }
        current = next;
    }
    current
}

fn const_value(var: &SSAVar) -> Option<u64> {
    let value_str = if let Some(value) = var.name.strip_prefix("const:") {
        value
    } else if let Some(value) = var.name.strip_prefix("ram:") {
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

fn stack_base_root_for_name(name: &str) -> Option<StackAddressRoot> {
    let lower = name.trim().to_ascii_lowercase();
    let base = match lower.as_str() {
        "sp" | "rsp" | "esp" | "wsp" => StackAddressBase::StackPointer,
        "fp" | "bp" | "rbp" | "ebp" | "x29" | "w29" | "s0" => StackAddressBase::FramePointer,
        _ => return None,
    };
    Some(StackAddressRoot { base, offset: 0 })
}

#[cfg(test)]
mod tests {
    use super::{LoopId, ProofNodeId};

    #[test]
    fn proof_node_ids_are_owner_qualified_and_stable() {
        let loop_node = ProofNodeId::loop_certificate(0x401000, LoopId(7));
        assert_eq!(loop_node.owner, "r2ssa");
        assert_eq!(loop_node.kind, "loop");
        assert_eq!(loop_node.anchor, 0x401000);
        assert_eq!(loop_node.ordinal, 7);
        assert_eq!(loop_node.to_string(), "r2ssa:loop:0x401000:7");

        let switch_node = ProofNodeId::switch_certificate(0x401020);
        assert_eq!(switch_node.owner, "r2ssa");
        assert_eq!(switch_node.kind, "switch");
        assert_eq!(switch_node.anchor, 0x401020);
        assert_eq!(switch_node.ordinal, 0);
        assert_eq!(switch_node.to_string(), "r2ssa:switch:0x401020:0");
    }
}
