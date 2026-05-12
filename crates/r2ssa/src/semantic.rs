//! Canonical semantic sidecar facts for prepared SSA functions.
//!
//! These facts keep object, memory, predicate, and call-site provenance in
//! `r2ssa` so downstream crates stop reconstructing them independently.

use std::collections::{BTreeMap, BTreeSet};

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
        let (applied_assumption_bindings, assumption_usage) =
            collect_prepared_assumption_usage(graph, &objects, &predicates, assumptions);
        Self {
            objects,
            memory,
            predicates,
            call_sites,
            structured,
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
                && (op.is_memory_read() || op.is_memory_write())
                && let Some(address) = op
                    .sources()
                    .into_iter()
                    .find_map(|source| graph.value_id_for_var(source))
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
                    op.dst().and_then(|dst| graph.value_id_for_var(dst)),
                    op.is_memory_write(),
                    0,
                );
            }
        }
    }
    access_facts
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
