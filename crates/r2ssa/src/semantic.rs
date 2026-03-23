//! Canonical semantic sidecar facts for prepared SSA functions.
//!
//! These facts keep object, memory, predicate, and call-site provenance in
//! `r2ssa` so downstream crates stop reconstructing them independently.

use std::collections::BTreeMap;

use crate::FunctionSSABlock;
use crate::cfg::BlockTerminator;
use crate::defuse::SliceOpRef;
use crate::function::{
    DecompilePrepFacts, DefLocation, SSAFunction, StackAddressBase, StackAddressRoot,
};
use crate::op::SSAOp;
use crate::var::SSAVar;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObjectId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PredicateId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub value_objects: BTreeMap<SSAVar, ObjectId>,
    pub stack_objects: BTreeMap<StackAddressRoot, ObjectId>,
    pub global_objects: BTreeMap<GlobalObjectKey, ObjectId>,
    pub escaped_unknown: Option<ObjectId>,
}

impl ObjectModel {
    pub fn object_for_value(&self, value: &SSAVar) -> Option<ObjectId> {
        self.value_objects.get(value).copied()
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
    pub uses_by_op: BTreeMap<SliceOpRef, Vec<MemoryUseFact>>,
    pub defs_by_op: BTreeMap<SliceOpRef, Vec<MemoryDefFact>>,
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
    pub lhs: SSAVar,
    pub rhs: SSAVar,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredicateFact {
    pub id: PredicateId,
    pub block_addr: u64,
    pub condition: SSAVar,
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
    pub selector: Option<SSAVar>,
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
    pub at: SliceOpRef,
    pub target: SSAVar,
    pub direct_target: Option<u64>,
    pub fallthrough: Option<u64>,
    pub memory_effect: CallMemoryEffect,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CallSiteFacts {
    pub by_id: BTreeMap<CallSiteId, CallSiteFact>,
    pub by_op: BTreeMap<SliceOpRef, CallSiteId>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreparedFunctionFacts {
    pub objects: ObjectModel,
    pub memory: MemorySSAFacts,
    pub predicates: PredicateFacts,
    pub call_sites: CallSiteFacts,
}

impl PreparedFunctionFacts {
    pub fn collect(function: &SSAFunction) -> Self {
        let call_sites = collect_call_sites(function);
        let (objects, memory) = collect_object_and_memory_facts(function, &call_sites);
        let predicates = collect_predicate_facts(function);
        Self {
            objects,
            memory,
            predicates,
            call_sites,
        }
    }
}

#[derive(Debug, Clone)]
struct ObjectModelBuilder<'a> {
    facts: Option<&'a DecompilePrepFacts>,
    objects: BTreeMap<ObjectId, ObjectFact>,
    value_objects: BTreeMap<SSAVar, ObjectId>,
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

    fn build(mut self, function: &SSAFunction) -> ObjectModel {
        if let Some(facts) = self.facts {
            let mut stack_roots: Vec<StackAddressRoot> =
                facts.stack_address_roots.values().copied().collect();
            stack_roots.sort_unstable();
            stack_roots.dedup();
            for root in stack_roots {
                self.ensure_stack_object(root);
            }
            for var in facts.stack_address_roots.keys() {
                let _ = self.object_for_address_value(var, "ram");
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
                        let _ = self.object_for_address_value(addr, space);
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

    fn object_for_address_value(&mut self, value: &SSAVar, space: &str) -> ObjectId {
        if let Some(object) = self.value_objects.get(value).copied() {
            return object;
        }

        if let Some(root) = resolve_stack_root(self.facts, value) {
            let object = self.ensure_stack_object(root);
            self.value_objects.insert(value.clone(), object);
            return object;
        }

        if let Some(address) = resolve_const_value(self.facts, value) {
            let object = self.ensure_global_object(GlobalObjectKey {
                space: space.to_string(),
                address,
            });
            self.value_objects.insert(value.clone(), object);
            return object;
        }

        self.value_objects
            .insert(value.clone(), self.escaped_unknown);
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
    call_sites: &CallSiteFacts,
) -> (ObjectModel, MemorySSAFacts) {
    let facts = function.decompile_prep_facts();
    let builder = ObjectModelBuilder::new(facts);
    let object_model = builder.build(function);
    let access_summaries = collect_access_summaries(function, facts, &object_model, call_sites);
    let memory = build_memory_ssa(function, &object_model, access_summaries);
    (object_model, memory)
}

fn collect_access_summaries(
    function: &SSAFunction,
    prep_facts: Option<&DecompilePrepFacts>,
    object_model: &ObjectModel,
    call_sites: &CallSiteFacts,
) -> BTreeMap<SliceOpRef, AccessSummary> {
    let mut summaries = BTreeMap::new();
    let escaped_unknown = object_model.escaped_unknown_object().unwrap_or(ObjectId(0));

    for block in function.blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            let op_ref = SliceOpRef::Op {
                block_addr: block.addr,
                op_idx,
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
                        addr,
                        space,
                        val.size,
                    ));
                }
                SSAOp::StoreConditional {
                    addr, val, space, ..
                } => {
                    let location =
                        memory_location_for_addr(prep_facts, object_model, addr, space, val.size);
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
                        addr,
                        space,
                        expected.size.max(replacement.size),
                    );
                    uses.push(location);
                    defs.push(location);
                }
                SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                    if call_sites.by_op.contains_key(&op_ref) {
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
                summaries.insert(op_ref, AccessSummary { uses, defs });
            }
        }
    }

    summaries
}

fn build_memory_ssa(
    function: &SSAFunction,
    object_model: &ObjectModel,
    access_summaries: BTreeMap<SliceOpRef, AccessSummary>,
) -> MemorySSAFacts {
    let mut phis_by_block = BTreeMap::new();

    let mut next_version_by_object = BTreeMap::<ObjectId, u32>::new();
    for object in object_model.objects.keys() {
        next_version_by_object.insert(*object, 1);
    }

    let mut def_versions = BTreeMap::<SliceOpRef, Vec<MemoryVersion>>::new();
    for (op_ref, summary) in &access_summaries {
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
        def_versions.insert(*op_ref, versions);
    }

    let object_ids = object_model.objects.keys().copied().collect::<Vec<_>>();
    let mut in_states = BTreeMap::<u64, BTreeMap<ObjectId, MemoryVersion>>::new();
    let mut out_states = BTreeMap::<u64, BTreeMap<ObjectId, MemoryVersion>>::new();
    let mut phi_versions = BTreeMap::<(u64, ObjectId), MemoryVersion>::new();
    let mut phi_inputs = BTreeMap::<(u64, ObjectId), Vec<(u64, MemoryVersion)>>::new();
    let (uses_by_op, defs_by_op) = loop {
        let mut changed = false;
        let mut uses_by_op = BTreeMap::<SliceOpRef, Vec<MemoryUseFact>>::new();
        let mut defs_by_op = BTreeMap::<SliceOpRef, Vec<MemoryDefFact>>::new();
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
                let op_ref = SliceOpRef::Op { block_addr, op_idx };
                let Some(summary) = access_summaries.get(&op_ref) else {
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
                    uses_by_op.entry(op_ref).or_default().push(MemoryUseFact {
                        location: *location,
                        version,
                    });
                }
                if let Some(def_versions_for_op) = def_versions.get(&op_ref) {
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
                        defs_by_op.entry(op_ref).or_default().push(MemoryDefFact {
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
            break (uses_by_op, defs_by_op);
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
        uses_by_op,
        defs_by_op,
        phis_by_block,
    }
}

fn collect_predicate_facts(function: &SSAFunction) -> PredicateFacts {
    let mut predicates = BTreeMap::new();
    let mut block_assumptions = BTreeMap::<u64, Vec<BlockAssumption>>::new();
    let mut switches = BTreeMap::new();
    let compare_defs = collect_compare_defs(function);
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
                        condition: cond.clone(),
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
                        selector: infer_switch_selector(function, block),
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

fn infer_switch_selector(function: &SSAFunction, block: &FunctionSSABlock) -> Option<SSAVar> {
    let target = block.ops.iter().rev().find_map(|op| match op {
        SSAOp::BranchInd { target } => Some(target),
        _ => None,
    })?;
    infer_switch_selector_from_var(function, target, 0)
}

fn infer_switch_selector_from_var(
    function: &SSAFunction,
    var: &SSAVar,
    depth: u32,
) -> Option<SSAVar> {
    if depth > 16 {
        return None;
    }

    let (block_addr, DefLocation::Op(op_idx)) = function.find_def(var)? else {
        return None;
    };
    let block = function.get_block(block_addr)?;
    let op = block.ops.get(op_idx)?;
    match op {
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => infer_switch_selector_from_var(function, src, depth + 1),
        SSAOp::Load { addr, .. } => {
            if is_stack_slot_address(function, addr, depth + 1) {
                Some(var.clone())
            } else {
                infer_switch_selector_from_addr(function, addr, depth + 1)
            }
        }
        SSAOp::IntAdd { a, b, .. } => infer_switch_selector_from_sum(function, a, b, depth + 1),
        SSAOp::IntSub { a, b, .. } => infer_switch_selector_from_sum(function, a, b, depth + 1),
        SSAOp::IntMult { a, b, .. } => infer_scaled_switch_selector(function, a, b, depth + 1),
        _ => None,
    }
}

fn infer_switch_selector_from_addr(
    function: &SSAFunction,
    addr: &SSAVar,
    depth: u32,
) -> Option<SSAVar> {
    if depth > 16 {
        return None;
    }

    let (block_addr, DefLocation::Op(op_idx)) = function.find_def(addr)? else {
        return None;
    };
    let block = function.get_block(block_addr)?;
    let op = block.ops.get(op_idx)?;
    match op {
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => infer_switch_selector_from_addr(function, src, depth + 1),
        SSAOp::IntAdd { a, b, .. } => infer_switch_selector_from_sum(function, a, b, depth + 1),
        SSAOp::IntSub { a, b, .. } => infer_switch_selector_from_sum(function, a, b, depth + 1),
        SSAOp::IntMult { a, b, .. } => infer_scaled_switch_selector(function, a, b, depth + 1),
        _ => None,
    }
}

fn infer_switch_selector_from_sum(
    function: &SSAFunction,
    a: &SSAVar,
    b: &SSAVar,
    depth: u32,
) -> Option<SSAVar> {
    if is_constish_var(a) {
        return infer_switch_selector_from_var(function, b, depth);
    }
    if is_constish_var(b) {
        return infer_switch_selector_from_var(function, a, depth);
    }
    infer_scaled_switch_selector(function, a, b, depth)
        .or_else(|| infer_scaled_switch_selector(function, b, a, depth))
}

fn infer_scaled_switch_selector(
    function: &SSAFunction,
    a: &SSAVar,
    b: &SSAVar,
    depth: u32,
) -> Option<SSAVar> {
    if is_constish_var(a) {
        return infer_switch_selector_from_var(function, b, depth);
    }
    if is_constish_var(b) {
        return infer_switch_selector_from_var(function, a, depth);
    }
    None
}

fn is_constish_var(var: &SSAVar) -> bool {
    var.is_const() || var.name.starts_with("ram:")
}

fn is_stack_slot_address(function: &SSAFunction, var: &SSAVar, depth: u32) -> bool {
    if depth > 16 {
        return false;
    }

    let base = var.name.to_ascii_lowercase();
    let base = base.split('_').next().unwrap_or(base.as_str());
    if matches!(base, "rbp" | "rsp" | "ebp" | "esp" | "bp" | "sp") {
        return true;
    }

    let Some((block_addr, DefLocation::Op(op_idx))) = function.find_def(var) else {
        return false;
    };
    let Some(block) = function.get_block(block_addr) else {
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
        | SSAOp::Subpiece { src, .. } => is_stack_slot_address(function, src, depth + 1),
        SSAOp::IntAdd { a, b, .. } | SSAOp::IntSub { a, b, .. } => {
            (is_stack_slot_address(function, a, depth + 1) && is_constish_var(b))
                || (is_stack_slot_address(function, b, depth + 1) && is_constish_var(a))
        }
        _ => false,
    }
}

fn collect_call_sites(function: &SSAFunction) -> CallSiteFacts {
    let mut by_id = BTreeMap::new();
    let mut by_op = BTreeMap::new();
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
            let id = CallSiteId(next_id);
            next_id = next_id.saturating_add(1);
            let op_ref = SliceOpRef::Op { block_addr, op_idx };
            let direct_target = resolve_const_value(None, &target);
            by_op.insert(op_ref, id);
            by_id.insert(
                id,
                CallSiteFact {
                    id,
                    at: op_ref,
                    target,
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

    CallSiteFacts { by_id, by_op }
}

fn collect_compare_defs(function: &SSAFunction) -> BTreeMap<SSAVar, CompareProvenance> {
    let mut compare_defs = BTreeMap::new();
    for block in function.blocks() {
        for op in &block.ops {
            let Some((dst, kind, lhs, rhs)) = compare_components(op) else {
                continue;
            };
            compare_defs.insert(
                dst.clone(),
                CompareProvenance {
                    kind,
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                },
            );
        }
    }
    compare_defs
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
    addr: &SSAVar,
    space: &str,
    size: u32,
) -> MemoryLocation {
    let object = object_model
        .object_for_value(addr)
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
