//! Stable, presentation-independent identity for prepared SSA semantics.

use std::collections::BTreeMap;

use crate::{
    AssumptionProvenance, AssumptionScope, AssumptionSubject, AssumptionValue, BlockId,
    BlockTerminator, CanonicalStorageId, CanonicalStorageSpace, CompareKind, GraphBlock, GraphInst,
    InstId, InstPayload, MemoryDefFact, MemoryLocation, MemoryPhiFact, MemoryVersion, ObjectId,
    ObjectKind, PredicateId, PreparedAssumptionBindingKind, RelativeMemoryAddress, SSAOp,
    SsaArtifact, SsaGraph, StackAddressBase, StackAddressRoot, ValueId,
};
use r2il::{MemoryOrdering, SpaceId};

/// Version of the byte-level semantic fingerprint contract.
///
/// Bump this whenever a tag or field encoding below changes.
pub const SSA_SEMANTIC_FINGERPRINT_SCHEMA_VERSION: u32 = 6;

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

struct FingerprintWriter(u64);

impl FingerprintWriter {
    fn new() -> Self {
        Self(FNV_OFFSET)
    }

    fn bytes(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(FNV_PRIME);
        }
    }

    fn tag(&mut self, value: u16) {
        self.bytes(&value.to_le_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.bytes(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes(&value.to_le_bytes());
    }

    fn i64(&mut self, value: i64) {
        self.bytes(&value.to_le_bytes());
    }

    fn usize(&mut self, value: usize) {
        self.u64(value as u64);
    }

    fn option_u64(&mut self, value: Option<u64>) {
        match value {
            Some(value) => {
                self.tag(1);
                self.u64(value);
            }
            None => self.tag(0),
        }
    }

    fn string(&mut self, value: &str) {
        self.usize(value.len());
        self.bytes(value.as_bytes());
    }

    fn finish(self) -> u64 {
        self.0
    }
}

fn hash_ordering(writer: &mut FingerprintWriter, ordering: MemoryOrdering) {
    writer.tag(match ordering {
        MemoryOrdering::Relaxed => 1,
        MemoryOrdering::Acquire => 2,
        MemoryOrdering::Release => 3,
        MemoryOrdering::AcqRel => 4,
        MemoryOrdering::SeqCst => 5,
        MemoryOrdering::Unknown => 6,
    });
}

fn hash_space(writer: &mut FingerprintWriter, space: SpaceId) {
    match space {
        SpaceId::Ram => writer.tag(1),
        SpaceId::Register => writer.tag(2),
        SpaceId::Unique => writer.tag(3),
        SpaceId::Const => writer.tag(4),
        SpaceId::Custom(id) => {
            writer.tag(5);
            writer.u32(id);
        }
    }
}

fn space_key(space: SpaceId) -> (u8, u32) {
    match space {
        SpaceId::Ram => (1, 0),
        SpaceId::Register => (2, 0),
        SpaceId::Unique => (3, 0),
        SpaceId::Const => (4, 0),
        SpaceId::Custom(id) => (5, id),
    }
}

fn stack_base_tag(base: StackAddressBase) -> u16 {
    match base {
        StackAddressBase::StackPointer => 1,
        StackAddressBase::FramePointer => 2,
    }
}

fn hash_stack_root(writer: &mut FingerprintWriter, root: StackAddressRoot) {
    writer.tag(stack_base_tag(root.base));
    writer.i64(root.offset);
}

fn hash_storage(writer: &mut FingerprintWriter, storage: Option<CanonicalStorageId>) {
    let Some(storage) = storage else {
        writer.tag(0);
        return;
    };
    writer.tag(1);
    match storage.space {
        CanonicalStorageSpace::Ram => writer.tag(1),
        CanonicalStorageSpace::Register => writer.tag(2),
        CanonicalStorageSpace::Unique => writer.tag(3),
        CanonicalStorageSpace::Constant => writer.tag(4),
        CanonicalStorageSpace::Custom(id) => {
            writer.tag(5);
            writer.u32(id);
        }
        CanonicalStorageSpace::Unknown => writer.tag(6),
    }
    writer.u64(storage.offset);
    writer.u32(storage.size);
}

fn hash_terminator(writer: &mut FingerprintWriter, terminator: &BlockTerminator) {
    match terminator {
        BlockTerminator::Fallthrough { next } => {
            writer.tag(1);
            writer.u64(*next);
        }
        BlockTerminator::Branch { target } => {
            writer.tag(2);
            writer.u64(*target);
        }
        BlockTerminator::ConditionalBranch {
            true_target,
            false_target,
        } => {
            writer.tag(3);
            writer.u64(*true_target);
            writer.u64(*false_target);
        }
        BlockTerminator::IndirectBranch => writer.tag(4),
        BlockTerminator::Switch { cases, default } => {
            writer.tag(5);
            let mut cases = cases.clone();
            cases.sort_unstable();
            writer.usize(cases.len());
            for (value, target) in cases {
                writer.u64(value);
                writer.u64(target);
            }
            writer.option_u64(*default);
        }
        BlockTerminator::Call {
            target,
            fallthrough,
        } => {
            writer.tag(6);
            writer.u64(*target);
            writer.option_u64(*fallthrough);
        }
        BlockTerminator::IndirectCall { fallthrough } => {
            writer.tag(7);
            writer.option_u64(*fallthrough);
        }
        BlockTerminator::Return => writer.tag(8),
        BlockTerminator::None => writer.tag(9),
    }
}

fn hash_op(writer: &mut FingerprintWriter, op: &SSAOp) {
    use SSAOp::*;
    match op {
        Phi { .. } => writer.tag(1),
        Copy { .. } => writer.tag(2),
        Load { space, .. } => {
            writer.tag(3);
            hash_space(writer, *space);
        }
        Store { space, .. } => {
            writer.tag(4);
            hash_space(writer, *space);
        }
        Fence { ordering } => {
            writer.tag(5);
            hash_ordering(writer, *ordering);
        }
        LoadLinked {
            space, ordering, ..
        } => {
            writer.tag(6);
            hash_space(writer, *space);
            hash_ordering(writer, *ordering);
        }
        StoreConditional {
            space, ordering, ..
        } => {
            writer.tag(7);
            hash_space(writer, *space);
            hash_ordering(writer, *ordering);
        }
        AtomicCAS {
            space, ordering, ..
        } => {
            writer.tag(8);
            hash_space(writer, *space);
            hash_ordering(writer, *ordering);
        }
        LoadGuarded {
            space, ordering, ..
        } => {
            writer.tag(9);
            hash_space(writer, *space);
            hash_ordering(writer, *ordering);
        }
        StoreGuarded {
            space, ordering, ..
        } => {
            writer.tag(10);
            hash_space(writer, *space);
            hash_ordering(writer, *ordering);
        }
        IntAdd { .. } => writer.tag(11),
        IntSub { .. } => writer.tag(12),
        IntMult { .. } => writer.tag(13),
        IntDiv { .. } => writer.tag(14),
        IntSDiv { .. } => writer.tag(15),
        IntRem { .. } => writer.tag(16),
        IntSRem { .. } => writer.tag(17),
        IntNegate { .. } => writer.tag(18),
        IntCarry { .. } => writer.tag(19),
        IntSCarry { .. } => writer.tag(20),
        IntSBorrow { .. } => writer.tag(21),
        IntAnd { .. } => writer.tag(22),
        IntOr { .. } => writer.tag(23),
        IntXor { .. } => writer.tag(24),
        IntNot { .. } => writer.tag(25),
        IntLeft { .. } => writer.tag(26),
        IntRight { .. } => writer.tag(27),
        IntSRight { .. } => writer.tag(28),
        IntEqual { .. } => writer.tag(29),
        IntNotEqual { .. } => writer.tag(30),
        IntLess { .. } => writer.tag(31),
        IntSLess { .. } => writer.tag(32),
        IntLessEqual { .. } => writer.tag(33),
        IntSLessEqual { .. } => writer.tag(34),
        IntZExt { .. } => writer.tag(35),
        IntSExt { .. } => writer.tag(36),
        BoolNot { .. } => writer.tag(37),
        BoolAnd { .. } => writer.tag(38),
        BoolOr { .. } => writer.tag(39),
        BoolXor { .. } => writer.tag(40),
        Piece { .. } => writer.tag(41),
        Subpiece { offset, .. } => {
            writer.tag(42);
            writer.u32(*offset);
        }
        PopCount { .. } => writer.tag(43),
        Lzcount { .. } => writer.tag(44),
        Branch { .. } => writer.tag(45),
        CBranch { .. } => writer.tag(46),
        BranchInd { .. } => writer.tag(47),
        Call { .. } => writer.tag(48),
        CallInd { .. } => writer.tag(49),
        CallDefine { .. } => writer.tag(50),
        Return { .. } => writer.tag(51),
        FloatAdd { .. } => writer.tag(52),
        FloatSub { .. } => writer.tag(53),
        FloatMult { .. } => writer.tag(54),
        FloatDiv { .. } => writer.tag(55),
        FloatNeg { .. } => writer.tag(56),
        FloatAbs { .. } => writer.tag(57),
        FloatSqrt { .. } => writer.tag(58),
        FloatCeil { .. } => writer.tag(59),
        FloatFloor { .. } => writer.tag(60),
        FloatRound { .. } => writer.tag(61),
        FloatNaN { .. } => writer.tag(62),
        FloatEqual { .. } => writer.tag(63),
        FloatNotEqual { .. } => writer.tag(64),
        FloatLess { .. } => writer.tag(65),
        FloatLessEqual { .. } => writer.tag(66),
        Int2Float { .. } => writer.tag(67),
        Float2Int { .. } => writer.tag(68),
        FloatFloat { .. } => writer.tag(69),
        Trunc { .. } => writer.tag(70),
        CallOther { userop, .. } => {
            writer.tag(71);
            writer.u32(*userop);
        }
        Nop => writer.tag(72),
        Unimplemented => writer.tag(73),
        CpuId { .. } => writer.tag(74),
        Breakpoint => writer.tag(75),
        PtrAdd { element_size, .. } => {
            writer.tag(76);
            writer.u32(*element_size);
        }
        PtrSub { element_size, .. } => {
            writer.tag(77);
            writer.u32(*element_size);
        }
        SegmentOp { .. } => writer.tag(78),
        New { .. } => writer.tag(79),
        Cast { .. } => writer.tag(80),
        Extract { .. } => writer.tag(81),
        Insert { .. } => writer.tag(82),
        Select { .. } => writer.tag(83),
    }
}

fn canonical_blocks(graph: &SsaGraph) -> (Vec<&GraphBlock>, BTreeMap<BlockId, u32>) {
    let mut blocks = graph.blocks.iter().collect::<Vec<_>>();
    blocks.sort_unstable_by_key(|block| (block.addr, block.size));
    let ids = blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id, index as u32))
        .collect();
    (blocks, ids)
}

type CanonicalPhiSourceKey = (u32, Option<CanonicalStorageId>, u32, Option<u64>);
type CanonicalPhiSortKey = (
    Option<CanonicalStorageId>,
    u32,
    Option<u64>,
    Vec<CanonicalPhiSourceKey>,
);

fn phi_sort_key(
    graph: &SsaGraph,
    inst: &GraphInst,
    block_ids: &BTreeMap<BlockId, u32>,
) -> CanonicalPhiSortKey {
    let output = inst.output.and_then(|value| graph.value(value));
    let mut sources = match &inst.payload {
        InstPayload::Phi { predecessors } => predecessors
            .iter()
            .zip(&inst.inputs)
            .filter_map(|(predecessor, value)| {
                let value = graph.value(*value)?;
                Some((
                    block_ids.get(predecessor).copied().unwrap_or(u32::MAX),
                    value.canonical_storage,
                    value.var.size,
                    value.var.constant_bits(),
                ))
            })
            .collect::<Vec<_>>(),
        InstPayload::Op(_) => Vec::new(),
    };
    sources.sort_unstable();
    (
        inst.canonical_storage,
        output.map(|value| value.var.size).unwrap_or_default(),
        output.and_then(|value| value.var.constant_bits()),
        sources,
    )
}

fn canonical_instructions<'a>(
    graph: &'a SsaGraph,
    blocks: &[&GraphBlock],
    block_ids: &BTreeMap<BlockId, u32>,
) -> Vec<&'a GraphInst> {
    let mut result = Vec::with_capacity(graph.insts.len());
    for block in blocks {
        let mut phis = Vec::new();
        let mut ops = Vec::new();
        for id in &block.insts {
            let Some(inst) = graph.inst(*id) else {
                continue;
            };
            if matches!(inst.payload, InstPayload::Phi { .. }) {
                phis.push(inst);
            } else {
                ops.push(inst);
            }
        }
        phis.sort_by_key(|inst| phi_sort_key(graph, inst, block_ids));
        ops.sort_unstable_by_key(|inst| inst.ordinal);
        result.extend(phis);
        result.extend(ops);
    }
    result
}

fn intern_value(ids: &mut BTreeMap<ValueId, u32>, id: ValueId) {
    if !ids.contains_key(&id) {
        ids.insert(id, ids.len() as u32);
    }
}

fn canonical_value_ids(
    graph: &SsaGraph,
    instructions: &[&GraphInst],
    block_ids: &BTreeMap<BlockId, u32>,
) -> BTreeMap<ValueId, u32> {
    let mut ids = BTreeMap::new();
    for inst in instructions {
        match &inst.payload {
            InstPayload::Phi { predecessors } => {
                let mut sources = predecessors.iter().zip(&inst.inputs).collect::<Vec<_>>();
                sources.sort_unstable_by_key(|(predecessor, _)| {
                    block_ids.get(predecessor).copied().unwrap_or(u32::MAX)
                });
                for (_, input) in sources {
                    intern_value(&mut ids, *input);
                }
            }
            InstPayload::Op(_) => {
                for input in &inst.inputs {
                    intern_value(&mut ids, *input);
                }
            }
        }
        if let Some(output) = inst.output {
            intern_value(&mut ids, output);
        }
    }
    let mut remaining = graph
        .values
        .iter()
        .filter(|value| !ids.contains_key(&value.id))
        .collect::<Vec<_>>();
    remaining.sort_unstable_by_key(|value| {
        (
            value.canonical_storage,
            value.var.size,
            value.var.constant_bits(),
        )
    });
    for value in remaining {
        intern_value(&mut ids, value.id);
    }
    ids
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CanonicalObjectKindKey {
    StackSlot {
        space: (u8, u32),
        base: u16,
        offset: i64,
    },
    FrameObject {
        space: (u8, u32),
        base: u16,
        offset: i64,
    },
    Parameter {
        space: (u8, u32),
        index: usize,
    },
    Global {
        space: (u8, u32),
        address: u64,
    },
    HeapAlloc {
        space: (u8, u32),
        call_inst: u32,
    },
    EscapedUnknown {
        space: (u8, u32),
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct CanonicalObjectKey {
    kind: CanonicalObjectKindKey,
    values: Vec<(u32, (u8, u32))>,
    entry_stack_root: Option<(u16, i64)>,
}

fn canonical_object_kind_key(
    artifact: &SsaArtifact,
    kind: &ObjectKind,
    inst_ids: &BTreeMap<InstId, u32>,
) -> CanonicalObjectKindKey {
    match kind {
        ObjectKind::StackSlot {
            space,
            base,
            offset,
        } => CanonicalObjectKindKey::StackSlot {
            space: space_key(*space),
            base: stack_base_tag(*base),
            offset: *offset,
        },
        ObjectKind::FrameObject {
            space,
            base,
            offset,
        } => CanonicalObjectKindKey::FrameObject {
            space: space_key(*space),
            base: stack_base_tag(*base),
            offset: *offset,
        },
        ObjectKind::Parameter { space, index } => CanonicalObjectKindKey::Parameter {
            space: space_key(*space),
            index: *index,
        },
        ObjectKind::Global { space, address } => CanonicalObjectKindKey::Global {
            space: space_key(*space),
            address: *address,
        },
        ObjectKind::HeapAlloc { space, call_site } => {
            let call_inst = artifact
                .facts()
                .call_sites
                .by_id
                .get(call_site)
                .and_then(|call| inst_ids.get(&call.at))
                .copied()
                .unwrap_or(u32::MAX);
            CanonicalObjectKindKey::HeapAlloc {
                space: space_key(*space),
                call_inst,
            }
        }
        ObjectKind::EscapedUnknown { space } => CanonicalObjectKindKey::EscapedUnknown {
            space: space_key(*space),
        },
    }
}

fn canonical_object_ids(
    artifact: &SsaArtifact,
    value_ids: &BTreeMap<ValueId, u32>,
    inst_ids: &BTreeMap<InstId, u32>,
) -> (BTreeMap<ObjectId, u32>, Vec<CanonicalObjectKey>) {
    let objects = artifact.objects();
    let mut values_by_object = BTreeMap::<ObjectId, Vec<(u32, (u8, u32))>>::new();
    for (key, object) in &objects.value_objects {
        values_by_object.entry(*object).or_default().push((
            value_ids.get(&key.value).copied().unwrap_or(u32::MAX),
            space_key(key.space),
        ));
    }
    for values in values_by_object.values_mut() {
        values.sort_unstable();
        values.dedup();
    }

    let mut keyed = objects
        .objects
        .iter()
        .map(|(object, fact)| {
            let entry_stack_root = objects
                .entry_stack_roots
                .get(object)
                .map(|root| (stack_base_tag(root.base), root.offset));
            (
                *object,
                CanonicalObjectKey {
                    kind: canonical_object_kind_key(artifact, &fact.kind, inst_ids),
                    values: values_by_object.remove(object).unwrap_or_default(),
                    entry_stack_root,
                },
            )
        })
        .collect::<Vec<_>>();
    keyed.sort_by(|left, right| left.1.cmp(&right.1));

    let mut canonical_keys = Vec::<CanonicalObjectKey>::new();
    let mut ids = BTreeMap::new();
    for (object, key) in keyed {
        let canonical = if canonical_keys.last() == Some(&key) {
            canonical_keys.len().saturating_sub(1) as u32
        } else {
            canonical_keys.push(key);
            canonical_keys.len().saturating_sub(1) as u32
        };
        ids.insert(object, canonical);
    }
    (ids, canonical_keys)
}

fn hash_object_kind(writer: &mut FingerprintWriter, kind: &CanonicalObjectKindKey) {
    match kind {
        CanonicalObjectKindKey::StackSlot {
            space,
            base,
            offset,
        } => {
            writer.tag(1);
            writer.tag(u16::from(space.0));
            writer.u32(space.1);
            writer.tag(*base);
            writer.i64(*offset);
        }
        CanonicalObjectKindKey::FrameObject {
            space,
            base,
            offset,
        } => {
            writer.tag(2);
            writer.tag(u16::from(space.0));
            writer.u32(space.1);
            writer.tag(*base);
            writer.i64(*offset);
        }
        CanonicalObjectKindKey::Parameter { space, index } => {
            writer.tag(3);
            writer.tag(u16::from(space.0));
            writer.u32(space.1);
            writer.usize(*index);
        }
        CanonicalObjectKindKey::Global { space, address } => {
            writer.tag(4);
            writer.tag(u16::from(space.0));
            writer.u32(space.1);
            writer.u64(*address);
        }
        CanonicalObjectKindKey::HeapAlloc { space, call_inst } => {
            writer.tag(5);
            writer.tag(u16::from(space.0));
            writer.u32(space.1);
            writer.u32(*call_inst);
        }
        CanonicalObjectKindKey::EscapedUnknown { space } => {
            writer.tag(6);
            writer.tag(u16::from(space.0));
            writer.u32(space.1);
        }
    }
}

fn hash_object_table(
    writer: &mut FingerprintWriter,
    artifact: &SsaArtifact,
    object_keys: &[CanonicalObjectKey],
) {
    writer.tag(0x101);
    writer.usize(artifact.objects().address_bits_by_space.len());
    for (space, bits) in &artifact.objects().address_bits_by_space {
        hash_space(writer, space.0);
        writer.u32(*bits);
    }
    writer.usize(object_keys.len());
    for key in object_keys {
        hash_object_kind(writer, &key.kind);
        writer.usize(key.values.len());
        for (value, space) in &key.values {
            writer.u32(*value);
            writer.tag(u16::from(space.0));
            writer.u32(space.1);
        }
        match key.entry_stack_root {
            Some((base, offset)) => {
                writer.tag(1);
                writer.tag(base);
                writer.i64(offset);
            }
            None => writer.tag(0),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CanonicalRelativeAddressKey {
    Exact(i64),
    Affine(Vec<(u32, i64)>, i64),
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct CanonicalMemoryLocationKey {
    space: (u8, u32),
    object: u32,
    address: CanonicalRelativeAddressKey,
    size: u32,
}

fn canonical_location_key(
    location: &MemoryLocation,
    object_ids: &BTreeMap<ObjectId, u32>,
    value_ids: &BTreeMap<ValueId, u32>,
) -> CanonicalMemoryLocationKey {
    let address = match &location.address {
        RelativeMemoryAddress::Exact(offset) => CanonicalRelativeAddressKey::Exact(*offset),
        RelativeMemoryAddress::Affine { terms, offset } => {
            let mut terms = terms
                .iter()
                .map(|term| {
                    (
                        value_ids.get(&term.value).copied().unwrap_or(u32::MAX),
                        term.coefficient,
                    )
                })
                .collect::<Vec<_>>();
            terms.sort_unstable();
            CanonicalRelativeAddressKey::Affine(terms, *offset)
        }
        RelativeMemoryAddress::Unknown => CanonicalRelativeAddressKey::Unknown,
    };
    CanonicalMemoryLocationKey {
        space: space_key(location.space),
        object: object_ids
            .get(&location.object)
            .copied()
            .unwrap_or(u32::MAX),
        address,
        size: location.size,
    }
}

fn hash_location(writer: &mut FingerprintWriter, location: &CanonicalMemoryLocationKey) {
    writer.tag(u16::from(location.space.0));
    writer.u32(location.space.1);
    writer.u32(location.object);
    match &location.address {
        CanonicalRelativeAddressKey::Exact(offset) => {
            writer.tag(1);
            writer.i64(*offset);
        }
        CanonicalRelativeAddressKey::Affine(terms, offset) => {
            writer.tag(2);
            writer.usize(terms.len());
            for (value, coefficient) in terms {
                writer.u32(*value);
                writer.i64(*coefficient);
            }
            writer.i64(*offset);
        }
        CanonicalRelativeAddressKey::Unknown => writer.tag(3),
    }
    writer.u32(location.size);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CanonicalMemoryVersionKey {
    Entry {
        object: u32,
    },
    Definition {
        object: u32,
        inst: u32,
        ordinal: u32,
    },
    Phi {
        object: u32,
        block_addr: u64,
        ordinal: u32,
    },
    Unresolved {
        object: u32,
    },
}

fn canonical_version_key(
    version: MemoryVersion,
    versions: &BTreeMap<MemoryVersion, CanonicalMemoryVersionKey>,
    object_ids: &BTreeMap<ObjectId, u32>,
) -> CanonicalMemoryVersionKey {
    let object = object_ids.get(&version.object).copied().unwrap_or(u32::MAX);
    if version.version == 0 {
        CanonicalMemoryVersionKey::Entry { object }
    } else {
        versions
            .get(&version)
            .cloned()
            .unwrap_or(CanonicalMemoryVersionKey::Unresolved { object })
    }
}

fn hash_version(writer: &mut FingerprintWriter, version: &CanonicalMemoryVersionKey) {
    match version {
        CanonicalMemoryVersionKey::Entry { object } => {
            writer.tag(1);
            writer.u32(*object);
        }
        CanonicalMemoryVersionKey::Definition {
            object,
            inst,
            ordinal,
        } => {
            writer.tag(2);
            writer.u32(*object);
            writer.u32(*inst);
            writer.u32(*ordinal);
        }
        CanonicalMemoryVersionKey::Phi {
            object,
            block_addr,
            ordinal,
        } => {
            writer.tag(3);
            writer.u32(*object);
            writer.u64(*block_addr);
            writer.u32(*ordinal);
        }
        CanonicalMemoryVersionKey::Unresolved { object } => {
            writer.tag(4);
            writer.u32(*object);
        }
    }
}

fn definition_sort_key(
    fact: &MemoryDefFact,
    object_ids: &BTreeMap<ObjectId, u32>,
    value_ids: &BTreeMap<ValueId, u32>,
) -> (CanonicalMemoryLocationKey, u32, u32) {
    (
        canonical_location_key(&fact.location, object_ids, value_ids),
        object_ids
            .get(&fact.previous_version.object)
            .copied()
            .unwrap_or(u32::MAX),
        object_ids
            .get(&fact.next_version.object)
            .copied()
            .unwrap_or(u32::MAX),
    )
}

fn phi_sort_key_memory(
    fact: &MemoryPhiFact,
    object_ids: &BTreeMap<ObjectId, u32>,
    value_ids: &BTreeMap<ValueId, u32>,
) -> (CanonicalMemoryLocationKey, u32, Vec<(u64, u32)>) {
    let mut inputs = fact
        .inputs
        .iter()
        .map(|(predecessor, version)| {
            (
                *predecessor,
                object_ids.get(&version.object).copied().unwrap_or(u32::MAX),
            )
        })
        .collect::<Vec<_>>();
    inputs.sort_unstable();
    (
        canonical_location_key(&fact.location, object_ids, value_ids),
        object_ids.get(&fact.object).copied().unwrap_or(u32::MAX),
        inputs,
    )
}

fn canonical_memory_versions(
    artifact: &SsaArtifact,
    inst_ids: &BTreeMap<InstId, u32>,
    object_ids: &BTreeMap<ObjectId, u32>,
    value_ids: &BTreeMap<ValueId, u32>,
) -> BTreeMap<MemoryVersion, CanonicalMemoryVersionKey> {
    let memory = artifact.memory();
    let mut definitions = memory
        .defs_by_inst
        .iter()
        .flat_map(|(inst, facts)| {
            let canonical_inst = inst_ids.get(inst).copied().unwrap_or(u32::MAX);
            let mut facts = facts.iter().collect::<Vec<_>>();
            facts.sort_by_key(|fact| definition_sort_key(fact, object_ids, value_ids));
            facts
                .into_iter()
                .enumerate()
                .map(move |(ordinal, fact)| (canonical_inst, ordinal as u32, fact))
        })
        .collect::<Vec<_>>();
    definitions.sort_by_key(|(inst, ordinal, fact)| {
        (
            *inst,
            definition_sort_key(fact, object_ids, value_ids),
            *ordinal,
        )
    });

    let mut versions = BTreeMap::new();
    for (inst, ordinal, fact) in definitions {
        let object = object_ids
            .get(&fact.next_version.object)
            .copied()
            .unwrap_or(u32::MAX);
        versions.insert(
            fact.next_version,
            CanonicalMemoryVersionKey::Definition {
                object,
                inst,
                ordinal,
            },
        );
    }

    for (block_addr, facts) in &memory.phis_by_block {
        let mut facts = facts.iter().collect::<Vec<_>>();
        facts.sort_by_key(|fact| phi_sort_key_memory(fact, object_ids, value_ids));
        for (ordinal, fact) in facts.into_iter().enumerate() {
            let object = object_ids
                .get(&fact.output_version.object)
                .copied()
                .unwrap_or(u32::MAX);
            versions.insert(
                fact.output_version,
                CanonicalMemoryVersionKey::Phi {
                    object,
                    block_addr: *block_addr,
                    ordinal: ordinal as u32,
                },
            );
        }
    }
    versions
}

fn hash_memory_ssa(
    writer: &mut FingerprintWriter,
    artifact: &SsaArtifact,
    inst_ids: &BTreeMap<InstId, u32>,
    object_ids: &BTreeMap<ObjectId, u32>,
    value_ids: &BTreeMap<ValueId, u32>,
) {
    let memory = artifact.memory();
    let versions = canonical_memory_versions(artifact, inst_ids, object_ids, value_ids);
    writer.tag(0x102);

    let mut uses = Vec::new();
    for (inst, facts) in &memory.uses_by_inst {
        let inst = inst_ids.get(inst).copied().unwrap_or(u32::MAX);
        for fact in facts {
            uses.push((
                inst,
                canonical_location_key(&fact.location, object_ids, value_ids),
                canonical_version_key(fact.version, &versions, object_ids),
            ));
        }
    }
    uses.sort_unstable();
    writer.usize(uses.len());
    for (inst, location, version) in uses {
        writer.u32(inst);
        hash_location(writer, &location);
        hash_version(writer, &version);
    }

    let mut defs = Vec::new();
    for (inst, facts) in &memory.defs_by_inst {
        let inst = inst_ids.get(inst).copied().unwrap_or(u32::MAX);
        for fact in facts {
            defs.push((
                inst,
                canonical_location_key(&fact.location, object_ids, value_ids),
                canonical_version_key(fact.previous_version, &versions, object_ids),
                canonical_version_key(fact.next_version, &versions, object_ids),
            ));
        }
    }
    defs.sort_unstable();
    writer.usize(defs.len());
    for (inst, location, previous, next) in defs {
        writer.u32(inst);
        hash_location(writer, &location);
        hash_version(writer, &previous);
        hash_version(writer, &next);
    }

    let mut phis = Vec::new();
    for (block_addr, facts) in &memory.phis_by_block {
        for fact in facts {
            let mut inputs = fact
                .inputs
                .iter()
                .map(|(predecessor, version)| {
                    (
                        *predecessor,
                        canonical_version_key(*version, &versions, object_ids),
                    )
                })
                .collect::<Vec<_>>();
            inputs.sort_unstable();
            phis.push((
                *block_addr,
                object_ids.get(&fact.object).copied().unwrap_or(u32::MAX),
                canonical_location_key(&fact.location, object_ids, value_ids),
                canonical_version_key(fact.output_version, &versions, object_ids),
                inputs,
            ));
        }
    }
    phis.sort_unstable();
    writer.usize(phis.len());
    for (block_addr, object, location, output, inputs) in phis {
        writer.u64(block_addr);
        writer.u32(object);
        hash_location(writer, &location);
        hash_version(writer, &output);
        writer.usize(inputs.len());
        for (predecessor, input) in inputs {
            writer.u64(predecessor);
            hash_version(writer, &input);
        }
    }
}

fn canonical_value_for_var(
    artifact: &SsaArtifact,
    value_ids: &BTreeMap<ValueId, u32>,
    var: &crate::SSAVar,
) -> Option<u32> {
    artifact
        .graph()
        .value_id_for_var(var)
        .and_then(|value| value_ids.get(&value).copied())
}

fn hash_decompile_prep_facts(
    writer: &mut FingerprintWriter,
    artifact: &SsaArtifact,
    value_ids: &BTreeMap<ValueId, u32>,
) {
    writer.tag(0x100);
    let Some(facts) = artifact.function().decompile_prep_facts() else {
        writer.tag(0);
        return;
    };
    writer.tag(1);
    let mut canonical_roots = facts
        .canonical_value_roots
        .iter()
        .filter_map(|(value, root)| {
            Some((
                canonical_value_for_var(artifact, value_ids, value)?,
                canonical_value_for_var(artifact, value_ids, root)?,
            ))
        })
        .collect::<Vec<_>>();
    canonical_roots.sort_unstable();
    writer.usize(canonical_roots.len());
    for (value, root) in canonical_roots {
        writer.u32(value);
        writer.u32(root);
    }

    let mut stack_roots = facts
        .stack_address_roots
        .iter()
        .filter_map(|(var, root)| Some((canonical_value_for_var(artifact, value_ids, var)?, *root)))
        .collect::<Vec<_>>();
    stack_roots.sort_unstable();
    writer.usize(stack_roots.len());
    for (value, root) in stack_roots {
        writer.u32(value);
        hash_stack_root(writer, root);
    }

    let mut entry_roots = facts
        .entry_stack_address_roots
        .iter()
        .filter_map(|(var, root)| Some((canonical_value_for_var(artifact, value_ids, var)?, *root)))
        .collect::<Vec<_>>();
    entry_roots.sort_unstable();
    writer.usize(entry_roots.len());
    for (value, root) in entry_roots {
        writer.u32(value);
        hash_stack_root(writer, root);
    }

    for formal_map in [&facts.formal_parameters, &facts.formal_parameter_bases] {
        let mut formals = formal_map
            .iter()
            .filter_map(|(var, index)| {
                Some((canonical_value_for_var(artifact, value_ids, var)?, *index))
            })
            .collect::<Vec<_>>();
        formals.sort_unstable();
        writer.usize(formals.len());
        for (value, index) in formals {
            writer.u32(value);
            writer.usize(index);
        }
    }
}

fn hash_machine_context(writer: &mut FingerprintWriter, artifact: &SsaArtifact) {
    writer.tag(0x103);
    let identity = artifact.machine_context().semantic_identity_bytes();
    writer.usize(identity.len());
    writer.bytes(&identity);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct CanonicalCompareKey {
    kind: u16,
    lhs: u32,
    rhs: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct CanonicalPredicateKey {
    block_addr: u64,
    condition: u32,
    comparison: Option<CanonicalCompareKey>,
    evaluated_comparison: Option<CanonicalCompareKey>,
    true_target: u64,
    false_target: u64,
}

fn compare_kind_tag(kind: CompareKind) -> u16 {
    match kind {
        CompareKind::Equal => 1,
        CompareKind::NotEqual => 2,
        CompareKind::Less => 3,
        CompareKind::SignedLess => 4,
        CompareKind::LessEqual => 5,
        CompareKind::SignedLessEqual => 6,
    }
}

fn canonical_compare_key(
    comparison: &crate::CompareProvenance,
    value_ids: &BTreeMap<ValueId, u32>,
) -> CanonicalCompareKey {
    CanonicalCompareKey {
        kind: compare_kind_tag(comparison.kind),
        lhs: value_ids.get(&comparison.lhs).copied().unwrap_or(u32::MAX),
        rhs: value_ids.get(&comparison.rhs).copied().unwrap_or(u32::MAX),
    }
}

fn canonical_predicate_ids(
    artifact: &SsaArtifact,
    value_ids: &BTreeMap<ValueId, u32>,
) -> (BTreeMap<PredicateId, u32>, Vec<CanonicalPredicateKey>) {
    let mut keyed = artifact
        .predicates()
        .predicates
        .iter()
        .map(|(predicate, fact)| {
            (
                *predicate,
                CanonicalPredicateKey {
                    block_addr: fact.block_addr,
                    condition: value_ids.get(&fact.condition).copied().unwrap_or(u32::MAX),
                    comparison: fact
                        .comparison
                        .as_ref()
                        .map(|comparison| canonical_compare_key(comparison, value_ids)),
                    evaluated_comparison: fact
                        .evaluated_comparison
                        .as_ref()
                        .map(|comparison| canonical_compare_key(comparison, value_ids)),
                    true_target: fact.true_target,
                    false_target: fact.false_target,
                },
            )
        })
        .collect::<Vec<_>>();
    keyed.sort_by(|left, right| left.1.cmp(&right.1));

    let mut keys = Vec::<CanonicalPredicateKey>::new();
    let mut ids = BTreeMap::new();
    for (predicate, key) in keyed {
        let canonical = if keys.last() == Some(&key) {
            keys.len().saturating_sub(1) as u32
        } else {
            keys.push(key);
            keys.len().saturating_sub(1) as u32
        };
        ids.insert(predicate, canonical);
    }
    (ids, keys)
}

fn hash_compare_key(writer: &mut FingerprintWriter, comparison: &CanonicalCompareKey) {
    writer.tag(comparison.kind);
    writer.u32(comparison.lhs);
    writer.u32(comparison.rhs);
}

fn hash_predicate_key(writer: &mut FingerprintWriter, predicate: &CanonicalPredicateKey) {
    writer.u64(predicate.block_addr);
    writer.u32(predicate.condition);
    for comparison in [&predicate.comparison, &predicate.evaluated_comparison] {
        match comparison {
            Some(comparison) => {
                writer.tag(1);
                hash_compare_key(writer, comparison);
            }
            None => writer.tag(0),
        }
    }
    writer.u64(predicate.true_target);
    writer.u64(predicate.false_target);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CanonicalAssumptionValueKey {
    Constant(u64),
    Range(u64, u64),
    FiniteSet(Vec<u64>),
    EnumDomain(Vec<i64>),
    TypeHint(String),
    Branch(bool),
}

fn canonical_assumption_value(value: &AssumptionValue) -> CanonicalAssumptionValueKey {
    match value {
        AssumptionValue::Constant { value } => CanonicalAssumptionValueKey::Constant(*value),
        AssumptionValue::Range { min, max } => CanonicalAssumptionValueKey::Range(*min, *max),
        AssumptionValue::FiniteSet { values } => {
            let mut values = values.clone();
            values.sort_unstable();
            values.dedup();
            CanonicalAssumptionValueKey::FiniteSet(values)
        }
        AssumptionValue::EnumDomain { values, .. } => {
            let mut values = values.clone();
            values.sort_unstable();
            values.dedup();
            CanonicalAssumptionValueKey::EnumDomain(values)
        }
        AssumptionValue::TypeHint { ty } => CanonicalAssumptionValueKey::TypeHint(ty.clone()),
        AssumptionValue::Branch { truth } => CanonicalAssumptionValueKey::Branch(*truth),
    }
}

fn assumption_scope_tag(scope: &AssumptionScope) -> u16 {
    match scope {
        AssumptionScope::Function => 1,
        AssumptionScope::Query => 2,
        AssumptionScope::Replay => 3,
    }
}

fn assumption_provenance_tag(provenance: &AssumptionProvenance) -> u16 {
    match provenance {
        AssumptionProvenance::User => 1,
        AssumptionProvenance::ImportedContext => 2,
        AssumptionProvenance::Replay => 3,
        AssumptionProvenance::Derived => 4,
    }
}

fn hash_assumption_value(writer: &mut FingerprintWriter, value: &CanonicalAssumptionValueKey) {
    match value {
        CanonicalAssumptionValueKey::Constant(value) => {
            writer.tag(1);
            writer.u64(*value);
        }
        CanonicalAssumptionValueKey::Range(min, max) => {
            writer.tag(2);
            writer.u64(*min);
            writer.u64(*max);
        }
        CanonicalAssumptionValueKey::FiniteSet(values) => {
            writer.tag(3);
            writer.usize(values.len());
            for value in values {
                writer.u64(*value);
            }
        }
        CanonicalAssumptionValueKey::EnumDomain(values) => {
            writer.tag(4);
            writer.usize(values.len());
            for value in values {
                writer.i64(*value);
            }
        }
        CanonicalAssumptionValueKey::TypeHint(ty) => {
            writer.tag(5);
            writer.string(ty);
        }
        CanonicalAssumptionValueKey::Branch(truth) => {
            writer.tag(6);
            writer.tag(u16::from(*truth));
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CanonicalAssumptionBindingKey {
    Predicate {
        predicate: u32,
        block_addr: u64,
        predecessor: Option<u64>,
        truth: bool,
        scope: u16,
        provenance: u16,
        value: CanonicalAssumptionValueKey,
    },
    Register {
        storage: CanonicalStorageId,
        value_id: u32,
        bits: u32,
        scope: u16,
        provenance: u16,
        value: CanonicalAssumptionValueKey,
    },
    StackSlot {
        base: u16,
        offset: i64,
        object: u32,
        scope: u16,
        provenance: u16,
        value: CanonicalAssumptionValueKey,
    },
}

fn hash_assumption_binding(
    writer: &mut FingerprintWriter,
    binding: &CanonicalAssumptionBindingKey,
) {
    match binding {
        CanonicalAssumptionBindingKey::Predicate {
            predicate,
            block_addr,
            predecessor,
            truth,
            scope,
            provenance,
            value,
        } => {
            writer.tag(1);
            writer.u32(*predicate);
            writer.u64(*block_addr);
            writer.option_u64(*predecessor);
            writer.tag(u16::from(*truth));
            writer.tag(*scope);
            writer.tag(*provenance);
            hash_assumption_value(writer, value);
        }
        CanonicalAssumptionBindingKey::Register {
            storage,
            value_id,
            bits,
            scope,
            provenance,
            value,
        } => {
            writer.tag(2);
            hash_storage(writer, Some(*storage));
            writer.u32(*value_id);
            writer.u32(*bits);
            writer.tag(*scope);
            writer.tag(*provenance);
            hash_assumption_value(writer, value);
        }
        CanonicalAssumptionBindingKey::StackSlot {
            base,
            offset,
            object,
            scope,
            provenance,
            value,
        } => {
            writer.tag(3);
            writer.tag(*base);
            writer.i64(*offset);
            writer.u32(*object);
            writer.tag(*scope);
            writer.tag(*provenance);
            hash_assumption_value(writer, value);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CanonicalTypeHintKey {
    Parameter {
        index: usize,
        ty: String,
        scope: u16,
        provenance: u16,
    },
    Register {
        storage: CanonicalStorageId,
        value_id: u32,
        bits: u32,
        ty: String,
        scope: u16,
        provenance: u16,
    },
    StackSlot {
        base: u16,
        offset: i64,
        object: u32,
        ty: String,
        scope: u16,
        provenance: u16,
    },
}

fn hash_type_hint(writer: &mut FingerprintWriter, hint: &CanonicalTypeHintKey) {
    match hint {
        CanonicalTypeHintKey::Parameter {
            index,
            ty,
            scope,
            provenance,
        } => {
            writer.tag(1);
            writer.usize(*index);
            writer.string(ty);
            writer.tag(*scope);
            writer.tag(*provenance);
        }
        CanonicalTypeHintKey::Register {
            storage,
            value_id,
            bits,
            ty,
            scope,
            provenance,
        } => {
            writer.tag(2);
            hash_storage(writer, Some(*storage));
            writer.u32(*value_id);
            writer.u32(*bits);
            writer.string(ty);
            writer.tag(*scope);
            writer.tag(*provenance);
        }
        CanonicalTypeHintKey::StackSlot {
            base,
            offset,
            object,
            ty,
            scope,
            provenance,
        } => {
            writer.tag(3);
            writer.tag(*base);
            writer.i64(*offset);
            writer.u32(*object);
            writer.string(ty);
            writer.tag(*scope);
            writer.tag(*provenance);
        }
    }
}

fn hash_assumption_conditioned_semantics(
    writer: &mut FingerprintWriter,
    artifact: &SsaArtifact,
    value_ids: &BTreeMap<ValueId, u32>,
    object_ids: &BTreeMap<ObjectId, u32>,
) {
    writer.tag(0x104);
    let (predicate_ids, predicate_keys) = canonical_predicate_ids(artifact, value_ids);
    writer.usize(predicate_keys.len());
    for predicate in &predicate_keys {
        hash_predicate_key(writer, predicate);
    }

    let mut block_assumptions = artifact
        .predicates()
        .block_assumptions
        .iter()
        .flat_map(|(block_addr, assumptions)| {
            assumptions.iter().map(|assumption| {
                (
                    *block_addr,
                    assumption.predecessor,
                    predicate_ids
                        .get(&assumption.predicate)
                        .copied()
                        .unwrap_or(u32::MAX),
                    assumption.truth,
                )
            })
        })
        .collect::<Vec<_>>();
    block_assumptions.sort_unstable();
    block_assumptions.dedup();
    writer.usize(block_assumptions.len());
    for (block_addr, predecessor, predicate, truth) in block_assumptions {
        writer.u64(block_addr);
        writer.u64(predecessor);
        writer.u32(predicate);
        writer.tag(u16::from(truth));
    }

    let mut switches = artifact
        .predicates()
        .switches
        .values()
        .map(|switch| {
            let mut cases = switch.cases.clone();
            cases.sort_unstable();
            cases.dedup();
            (
                switch.block_addr,
                switch
                    .selector
                    .and_then(|selector| value_ids.get(&selector).copied()),
                cases,
                switch.default,
            )
        })
        .collect::<Vec<_>>();
    switches.sort_unstable();
    writer.usize(switches.len());
    for (block_addr, selector, cases, default) in switches {
        writer.u64(block_addr);
        match selector {
            Some(selector) => {
                writer.tag(1);
                writer.u32(selector);
            }
            None => writer.tag(0),
        }
        writer.usize(cases.len());
        for (value, target) in cases {
            writer.u64(value);
            writer.u64(target);
        }
        writer.option_u64(default);
    }

    let mut bindings = artifact
        .facts()
        .applied_assumption_bindings
        .iter()
        .map(|binding| {
            let value = canonical_assumption_value(&binding.assumption.value);
            let scope = assumption_scope_tag(&binding.assumption.scope);
            let provenance = assumption_provenance_tag(&binding.assumption.provenance);
            match &binding.binding {
                PreparedAssumptionBindingKind::Predicate {
                    predicate,
                    block_addr,
                    predecessor,
                    truth,
                } => CanonicalAssumptionBindingKey::Predicate {
                    predicate: predicate_ids.get(predicate).copied().unwrap_or(u32::MAX),
                    block_addr: *block_addr,
                    predecessor: *predecessor,
                    truth: *truth,
                    scope,
                    provenance,
                    value,
                },
                PreparedAssumptionBindingKind::Register {
                    storage,
                    value: bound_value,
                    bits,
                    ..
                } => CanonicalAssumptionBindingKey::Register {
                    storage: *storage,
                    value_id: value_ids.get(bound_value).copied().unwrap_or(u32::MAX),
                    bits: *bits,
                    scope,
                    provenance,
                    value,
                },
                PreparedAssumptionBindingKind::StackSlot {
                    base,
                    offset,
                    object,
                } => CanonicalAssumptionBindingKey::StackSlot {
                    base: stack_base_tag(*base),
                    offset: *offset,
                    object: object_ids.get(object).copied().unwrap_or(u32::MAX),
                    scope,
                    provenance,
                    value,
                },
            }
        })
        .collect::<Vec<_>>();
    bindings.sort_unstable();
    bindings.dedup();
    writer.usize(bindings.len());
    for binding in &bindings {
        hash_assumption_binding(writer, binding);
    }

    let mut type_hints = artifact
        .facts()
        .applied_assumption_bindings
        .iter()
        .filter_map(|binding| {
            let AssumptionValue::TypeHint { ty } = &binding.assumption.value else {
                return None;
            };
            let scope = assumption_scope_tag(&binding.assumption.scope);
            let provenance = assumption_provenance_tag(&binding.assumption.provenance);
            match &binding.binding {
                PreparedAssumptionBindingKind::Register {
                    storage,
                    value: bound_value,
                    bits,
                    ..
                } => Some(CanonicalTypeHintKey::Register {
                    storage: *storage,
                    value_id: value_ids.get(bound_value).copied().unwrap_or(u32::MAX),
                    bits: *bits,
                    ty: ty.clone(),
                    scope,
                    provenance,
                }),
                PreparedAssumptionBindingKind::StackSlot {
                    base,
                    offset,
                    object,
                } => Some(CanonicalTypeHintKey::StackSlot {
                    base: stack_base_tag(*base),
                    offset: *offset,
                    object: object_ids.get(object).copied().unwrap_or(u32::MAX),
                    ty: ty.clone(),
                    scope,
                    provenance,
                }),
                PreparedAssumptionBindingKind::Predicate { .. } => None,
            }
        })
        .chain(
            artifact
                .facts()
                .assumptions
                .iter()
                .filter_map(|assumption| {
                    let (AssumptionSubject::Parameter { index }, AssumptionValue::TypeHint { ty }) =
                        (&assumption.subject, &assumption.value)
                    else {
                        return None;
                    };
                    Some(CanonicalTypeHintKey::Parameter {
                        index: *index,
                        ty: ty.clone(),
                        scope: assumption_scope_tag(&assumption.scope),
                        provenance: assumption_provenance_tag(&assumption.provenance),
                    })
                }),
        )
        .collect::<Vec<_>>();
    type_hints.sort_unstable();
    type_hints.dedup();
    writer.usize(type_hints.len());
    for hint in &type_hints {
        hash_type_hint(writer, hint);
    }

    let mut memory_windows = artifact
        .facts()
        .assumptions
        .iter()
        .filter_map(|assumption| {
            let AssumptionSubject::MemoryWindow { addr, size } = &assumption.subject else {
                return None;
            };
            Some((
                *addr,
                *size,
                assumption_scope_tag(&assumption.scope),
                assumption_provenance_tag(&assumption.provenance),
                canonical_assumption_value(&assumption.value),
            ))
        })
        .collect::<Vec<_>>();
    memory_windows.sort_unstable();
    memory_windows.dedup();
    writer.usize(memory_windows.len());
    for (addr, size, scope, provenance, value) in memory_windows {
        writer.u64(addr);
        writer.u32(size);
        writer.tag(scope);
        writer.tag(provenance);
        hash_assumption_value(writer, &value);
    }
}

/// Fingerprint every semantic component of a prepared SSA artifact while
/// excluding function and SSA-variable presentation names.
pub fn stable_ssa_semantic_fingerprint(artifact: &SsaArtifact) -> u64 {
    let mut writer = FingerprintWriter::new();
    writer.string("r2ssa-semantic-fingerprint");
    writer.u32(SSA_SEMANTIC_FINGERPRINT_SCHEMA_VERSION);

    let function = artifact.function();
    let graph = artifact.graph();
    let (blocks, block_ids) = canonical_blocks(graph);
    let instructions = canonical_instructions(graph, &blocks, &block_ids);
    let value_ids = canonical_value_ids(graph, &instructions, &block_ids);
    let inst_ids = instructions
        .iter()
        .enumerate()
        .map(|(ordinal, inst)| (inst.id, ordinal as u32))
        .collect::<BTreeMap<_, _>>();
    let (object_ids, object_keys) = canonical_object_ids(artifact, &value_ids, &inst_ids);
    writer.u64(function.entry);
    writer.u32(block_ids.get(&graph.entry).copied().unwrap_or(u32::MAX));

    writer.usize(blocks.len());
    for block in &blocks {
        writer.u32(block_ids[&block.id]);
        writer.u64(block.addr);
        writer.u32(block.size);
        let mut predecessors = block
            .predecessors
            .iter()
            .filter_map(|id| block_ids.get(id).copied())
            .collect::<Vec<_>>();
        predecessors.sort_unstable();
        writer.usize(predecessors.len());
        for predecessor in predecessors {
            writer.u32(predecessor);
        }
        let mut successors = block
            .successors
            .iter()
            .filter_map(|id| block_ids.get(id).copied())
            .collect::<Vec<_>>();
        successors.sort_unstable();
        writer.usize(successors.len());
        for successor in successors {
            writer.u32(successor);
        }
        writer.usize(block.insts.len());
        if let Some(source) = function.cfg().get_block(block.addr) {
            writer.tag(1);
            hash_terminator(&mut writer, &source.terminator);
            writer.option_u64(source.terminal_instruction_addr());
            match &source.switch_info {
                Some(switch) => {
                    writer.tag(1);
                    writer.u64(switch.switch_addr);
                    writer.u64(switch.min_val);
                    writer.u64(switch.max_val);
                    writer.option_u64(switch.default_target);
                    let mut cases = switch
                        .cases
                        .iter()
                        .map(|case| (case.value, case.target))
                        .collect::<Vec<_>>();
                    cases.sort_unstable();
                    writer.usize(cases.len());
                    for (value, target) in cases {
                        writer.u64(value);
                        writer.u64(target);
                    }
                }
                None => writer.tag(0),
            }
        } else {
            writer.tag(0);
        }
    }

    let mut values = graph.values.iter().collect::<Vec<_>>();
    values.sort_unstable_by_key(|value| value_ids[&value.id]);
    writer.usize(values.len());
    for value in values {
        writer.u32(value_ids[&value.id]);
        writer.u32(value.var.size);
        writer.option_u64(value.var.constant_bits());
        hash_storage(&mut writer, value.canonical_storage);
    }

    writer.usize(instructions.len());
    for (ordinal, inst) in instructions.iter().enumerate() {
        writer.u32(ordinal as u32);
        writer.u32(block_ids[&inst.block]);
        match inst.output {
            Some(output) => {
                writer.tag(1);
                writer.u32(value_ids[&output]);
            }
            None => writer.tag(0),
        }
        hash_storage(&mut writer, inst.canonical_storage);
        match &inst.payload {
            InstPayload::Phi { predecessors } => {
                writer.tag(1);
                let mut sources = predecessors.iter().zip(&inst.inputs).collect::<Vec<_>>();
                sources.sort_unstable_by_key(|(predecessor, _)| {
                    block_ids.get(predecessor).copied().unwrap_or(u32::MAX)
                });
                writer.usize(sources.len());
                for (predecessor, input) in sources {
                    writer.u32(block_ids[predecessor]);
                    writer.u32(value_ids[input]);
                }
            }
            InstPayload::Op(op) => {
                writer.tag(2);
                writer.usize(inst.inputs.len());
                for input in &inst.inputs {
                    writer.u32(value_ids[input]);
                }
                hash_op(&mut writer, op);
            }
        }
    }
    hash_decompile_prep_facts(&mut writer, artifact, &value_ids);
    hash_object_table(&mut writer, artifact, &object_keys);
    hash_memory_ssa(&mut writer, artifact, &inst_ids, &object_ids, &value_ids);
    hash_assumption_conditioned_semantics(&mut writer, artifact, &value_ids, &object_ids);
    hash_machine_context(&mut writer, artifact);
    writer.finish()
}

#[cfg(test)]
mod tests {
    use r2il::{
        AddressSpace, ArchSpec, MemoryOrdering, R2ILBlock, R2ILOp, RegisterDef, SpaceId,
        SwitchCase, SwitchInfo, Varnode,
    };

    use super::{SSA_SEMANTIC_FINGERPRINT_SCHEMA_VERSION, stable_ssa_semantic_fingerprint};
    use crate::{
        AnalysisAssumption, AssumptionProvenance, AssumptionScope, AssumptionSet,
        AssumptionSubject, AssumptionValue, CanonicalStorageId, CanonicalStorageSpace, SSAOp,
        SourceFunctionInterface, SourceFunctionReturn, SourceMachineRoles,
        SourceStackAllocationContract, SourceStackGrowth, SourceStackSlotSpec, SsaArtifact,
        StackAddressBase,
    };

    fn constant(value: u64) -> Varnode {
        Varnode::constant(value, 8)
    }

    fn register(offset: u64) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size: 8,
            meta: None,
        }
    }

    fn unique(offset: u64) -> Varnode {
        Varnode {
            space: SpaceId::Unique,
            offset,
            size: 8,
            meta: None,
        }
    }

    fn branch_blocks() -> Vec<R2ILBlock> {
        vec![
            R2ILBlock {
                addr: 0x1000,
                size: 1,
                ops: vec![R2ILOp::CBranch {
                    target: constant(0x1010),
                    cond: register(0),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1001,
                size: 1,
                ops: vec![
                    R2ILOp::Copy {
                        dst: register(8),
                        src: constant(1),
                    },
                    R2ILOp::Copy {
                        dst: register(16),
                        src: constant(3),
                    },
                    R2ILOp::Branch {
                        target: constant(0x1020),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 1,
                ops: vec![
                    R2ILOp::Copy {
                        dst: register(8),
                        src: constant(2),
                    },
                    R2ILOp::Copy {
                        dst: register(16),
                        src: constant(4),
                    },
                    R2ILOp::Branch {
                        target: constant(0x1020),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1020,
                size: 1,
                ops: vec![
                    R2ILOp::IntAdd {
                        dst: unique(0),
                        a: register(8),
                        b: register(16),
                    },
                    R2ILOp::Return { target: unique(0) },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ]
    }

    fn arch(first: &str, second: &str, third: &str) -> ArchSpec {
        let mut arch = ArchSpec::new("fingerprint-test");
        arch.add_register(RegisterDef::new(first, 0, 8));
        arch.add_register(RegisterDef::new(second, 8, 8));
        arch.add_register(RegisterDef::new(third, 16, 8));
        arch
    }

    #[test]
    fn fingerprint_ignores_register_names_and_source_block_order() {
        let blocks = branch_blocks();
        let first = SsaArtifact::for_symbolic(&blocks, Some(&arch("condition", "alpha", "zeta")))
            .expect("first SSA");
        let reordered = vec![
            blocks[0].clone(),
            blocks[2].clone(),
            blocks[1].clone(),
            blocks[3].clone(),
        ];
        let second =
            SsaArtifact::for_symbolic(&reordered, Some(&arch("renamed0", "zeta", "alpha")))
                .expect("reordered SSA");
        assert_eq!(
            stable_ssa_semantic_fingerprint(&first),
            stable_ssa_semantic_fingerprint(&second)
        );
        assert_eq!(first.function().get_block(0x1020).unwrap().phis.len(), 2);
    }

    #[test]
    fn fingerprint_binds_predicate_assumption_without_mutating_source_facts() {
        let base =
            SsaArtifact::for_symbolic(&branch_blocks(), Some(&arch("condition", "alpha", "zeta")))
                .expect("base SSA");
        let predicate = base
            .predicates()
            .predicates
            .values()
            .next()
            .expect("branch predicate");
        let conditioned = base.with_assumptions(&AssumptionSet::new(vec![AnalysisAssumption {
            id: Some("presentation-only-id".to_string()),
            subject: AssumptionSubject::Predicate {
                predicate: predicate.id,
                block_addr: predicate.block_addr,
                predecessor: Some(predicate.true_target),
            },
            value: AssumptionValue::Branch { truth: true },
            scope: AssumptionScope::Query,
            provenance: AssumptionProvenance::User,
        }]));

        assert_eq!(base.graph().blocks, conditioned.graph().blocks);
        assert_eq!(base.graph().insts, conditioned.graph().insts);
        assert_eq!(base.graph().values, conditioned.graph().values);
        assert_eq!(base.predicates(), conditioned.predicates());
        assert_eq!(base.structured(), conditioned.structured());
        assert_eq!(base.certificates(), conditioned.certificates());
        assert_eq!(conditioned.facts().applied_assumption_bindings.len(), 1);
        assert_ne!(
            stable_ssa_semantic_fingerprint(&base),
            stable_ssa_semantic_fingerprint(&conditioned)
        );
    }

    fn entry_register_name(artifact: &SsaArtifact, storage: CanonicalStorageId) -> String {
        artifact
            .graph()
            .values
            .iter()
            .find(|value| {
                value.var.version == 0
                    && value.var.is_register()
                    && value.canonical_storage == Some(storage)
            })
            .map(|value| value.var.name.clone())
            .expect("canonical entry register")
    }

    fn register_value_assumption(name: String) -> AnalysisAssumption {
        AnalysisAssumption {
            id: Some(format!("display:{name}")),
            subject: AssumptionSubject::Register { name },
            value: AssumptionValue::FiniteSet {
                values: vec![9, 3, 9],
            },
            scope: AssumptionScope::Function,
            provenance: AssumptionProvenance::ImportedContext,
        }
    }

    fn memory_window_assumption() -> AnalysisAssumption {
        AnalysisAssumption {
            id: Some("window-label".to_string()),
            subject: AssumptionSubject::MemoryWindow {
                addr: 0x8000,
                size: 4,
            },
            value: AssumptionValue::EnumDomain {
                name: Some("presentation-enum-name".to_string()),
                values: vec![7, -1, 7],
            },
            scope: AssumptionScope::Query,
            provenance: AssumptionProvenance::Replay,
        }
    }

    #[test]
    fn fingerprint_canonicalizes_assumption_order_register_names_and_set_order() {
        let blocks = branch_blocks();
        let first = SsaArtifact::for_symbolic(&blocks, Some(&arch("condition", "alpha", "zeta")))
            .expect("first SSA");
        let reordered = vec![
            blocks[0].clone(),
            blocks[2].clone(),
            blocks[1].clone(),
            blocks[3].clone(),
        ];
        let second =
            SsaArtifact::for_symbolic(&reordered, Some(&arch("renamed0", "zeta", "alpha")))
                .expect("renamed SSA");
        let first_register = register_value_assumption(entry_register_name(
            &first,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            },
        ));
        let mut second_register = register_value_assumption(entry_register_name(
            &second,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            },
        ));
        second_register.id = Some("different-presentation-id".to_string());
        second_register.value = AssumptionValue::FiniteSet { values: vec![3, 9] };
        let first = first.with_assumptions(&AssumptionSet::new(vec![
            first_register,
            memory_window_assumption(),
        ]));
        let mut renamed_window = memory_window_assumption();
        renamed_window.id = None;
        renamed_window.value = AssumptionValue::EnumDomain {
            name: Some("renamed-enum".to_string()),
            values: vec![-1, 7],
        };
        let second =
            second.with_assumptions(&AssumptionSet::new(vec![renamed_window, second_register]));

        assert_eq!(first.facts().applied_assumption_bindings.len(), 1);
        assert_eq!(second.facts().applied_assumption_bindings.len(), 1);
        assert_eq!(
            stable_ssa_semantic_fingerprint(&first),
            stable_ssa_semantic_fingerprint(&second)
        );
    }

    fn parameter_type_hint(
        id: Option<&str>,
        provenance: AssumptionProvenance,
    ) -> AnalysisAssumption {
        AnalysisAssumption {
            id: id.map(str::to_string),
            subject: AssumptionSubject::Parameter { index: 0 },
            value: AssumptionValue::TypeHint {
                ty: "const char *".to_string(),
            },
            scope: AssumptionScope::Function,
            provenance,
        }
    }

    #[test]
    fn fingerprint_binds_type_hint_authority_but_not_presentation_id() {
        let base =
            SsaArtifact::for_symbolic(&branch_blocks(), Some(&arch("condition", "alpha", "zeta")))
                .expect("base SSA");
        let first = base.with_assumptions(&AssumptionSet::new(vec![parameter_type_hint(
            Some("first-id"),
            AssumptionProvenance::ImportedContext,
        )]));
        let renamed = base.with_assumptions(&AssumptionSet::new(vec![parameter_type_hint(
            Some("renamed-id"),
            AssumptionProvenance::ImportedContext,
        )]));
        let stronger = base.with_assumptions(&AssumptionSet::new(vec![parameter_type_hint(
            Some("first-id"),
            AssumptionProvenance::User,
        )]));

        assert_ne!(
            stable_ssa_semantic_fingerprint(&base),
            stable_ssa_semantic_fingerprint(&first)
        );
        assert_eq!(
            stable_ssa_semantic_fingerprint(&first),
            stable_ssa_semantic_fingerprint(&renamed)
        );
        assert_ne!(
            stable_ssa_semantic_fingerprint(&first),
            stable_ssa_semantic_fingerprint(&stronger)
        );
    }

    fn payload_artifact(ordering: MemoryOrdering, userop: u32, value: u64) -> SsaArtifact {
        SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x3000,
                size: 1,
                ops: vec![
                    R2ILOp::Fence { ordering },
                    R2ILOp::CallOther {
                        output: None,
                        userop,
                        inputs: vec![constant(value)],
                    },
                    R2ILOp::Return {
                        target: constant(0),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            None,
        )
        .expect("payload SSA")
    }

    #[test]
    fn fingerprint_binds_constants_ordering_and_userop_payloads() {
        let base = payload_artifact(MemoryOrdering::Acquire, 7, 1);
        assert_ne!(
            stable_ssa_semantic_fingerprint(&base),
            stable_ssa_semantic_fingerprint(&payload_artifact(MemoryOrdering::SeqCst, 7, 1))
        );
        assert_ne!(
            stable_ssa_semantic_fingerprint(&base),
            stable_ssa_semantic_fingerprint(&payload_artifact(MemoryOrdering::Acquire, 8, 1))
        );
        assert_ne!(
            stable_ssa_semantic_fingerprint(&base),
            stable_ssa_semantic_fingerprint(&payload_artifact(MemoryOrdering::Acquire, 7, 2))
        );
    }

    fn memory_space_artifact(space: SpaceId) -> SsaArtifact {
        SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x3800,
                size: 1,
                ops: vec![R2ILOp::Load {
                    dst: register(0),
                    space,
                    addr: constant(0x4000),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            None,
        )
        .expect("memory-space SSA")
    }

    #[test]
    fn fingerprint_binds_exact_typed_memory_space() {
        let ram = memory_space_artifact(SpaceId::Ram);
        let custom_one = memory_space_artifact(SpaceId::Custom(1));
        let custom_two = memory_space_artifact(SpaceId::Custom(2));
        assert_ne!(
            stable_ssa_semantic_fingerprint(&ram),
            stable_ssa_semantic_fingerprint(&custom_one)
        );
        assert_ne!(
            stable_ssa_semantic_fingerprint(&custom_one),
            stable_ssa_semantic_fingerprint(&custom_two)
        );
        let SSAOp::Load { space, .. } = &custom_one.function().entry_block().unwrap().ops[0] else {
            panic!("expected load");
        };
        assert_eq!(*space, SpaceId::Custom(1));
    }

    fn switch_artifact(cases: Vec<SwitchCase>) -> SsaArtifact {
        let mut blocks = vec![R2ILBlock {
            addr: 0x4000,
            size: 1,
            ops: vec![R2ILOp::BranchInd {
                target: register(0),
            }],
            switch_info: Some(SwitchInfo {
                switch_addr: 0x4000,
                min_val: 0,
                max_val: 1,
                default_target: Some(0x4030),
                cases,
            }),
            op_metadata: Default::default(),
        }];
        for addr in [0x4010, 0x4020, 0x4030] {
            blocks.push(R2ILBlock {
                addr,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: constant(addr),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            });
        }
        SsaArtifact::for_symbolic(&blocks, None).expect("switch SSA")
    }

    #[test]
    fn fingerprint_canonicalizes_case_order_and_binds_switch_mapping() {
        let first = switch_artifact(vec![
            SwitchCase {
                value: 0,
                target: 0x4010,
            },
            SwitchCase {
                value: 1,
                target: 0x4020,
            },
        ]);
        let reordered = switch_artifact(vec![
            SwitchCase {
                value: 1,
                target: 0x4020,
            },
            SwitchCase {
                value: 0,
                target: 0x4010,
            },
        ]);
        let changed = switch_artifact(vec![
            SwitchCase {
                value: 0,
                target: 0x4010,
            },
            SwitchCase {
                value: 1,
                target: 0x4030,
            },
        ]);
        assert_eq!(
            stable_ssa_semantic_fingerprint(&first),
            stable_ssa_semantic_fingerprint(&reordered)
        );
        assert_ne!(
            stable_ssa_semantic_fingerprint(&first),
            stable_ssa_semantic_fingerprint(&changed)
        );
    }

    fn register_storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn framed_relation_artifact(
        frame_pointer_offset: u64,
        implicit_active_sp_bytes: u32,
    ) -> SsaArtifact {
        let sp = register(0);
        let first_fp = register(8);
        let second_fp = register(16);
        let return_address = register(24);
        let first_address = unique(0x100);
        let second_address = unique(0x108);
        let blocks = [R2ILBlock {
            addr: 0x5000,
            size: 1,
            ops: vec![
                R2ILOp::IntSub {
                    dst: first_fp.clone(),
                    a: sp.clone(),
                    b: constant(8),
                },
                R2ILOp::IntSub {
                    dst: second_fp.clone(),
                    a: sp,
                    b: constant(16),
                },
                R2ILOp::IntSub {
                    dst: first_address.clone(),
                    a: first_fp,
                    b: constant(8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: first_address,
                    val: constant(1),
                },
                R2ILOp::IntSub {
                    dst: second_address.clone(),
                    a: second_fp,
                    b: constant(8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: second_address,
                    val: constant(2),
                },
                R2ILOp::Return {
                    target: return_address,
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }];

        let mut arch = ArchSpec::new("fingerprint-frame-relation-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("fp_a", 8, 8));
        arch.add_register(RegisterDef::new("fp_b", 16, 8));
        arch.add_register(RegisterDef::new("ra", 24, 8));
        arch.add_space(AddressSpace::ram(8));

        let frame_pointer = register_storage(frame_pointer_offset);
        let interface = SourceFunctionInterface::new_exact(
            b"fingerprint-frame-relation-v1".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                frame_pointer,
                -8,
                8,
            )],
        )
        .and_then(|interface| interface.with_return_address_storage(register_storage(24)))
        .and_then(|interface| interface.with_stack_pointer_storage(register_storage(0)))
        .and_then(|interface| interface.with_frame_pointer_storage(frame_pointer))
        .expect("coherent exact frame interface");
        let roles = SourceMachineRoles::new(Some(register_storage(24)), Some(register_storage(0)))
            .and_then(|roles| {
                roles.with_stack_allocation_contract(
                    SourceStackAllocationContract::with_implicit_active_sp_bytes(
                        SourceStackGrowth::LowerAddresses,
                        implicit_active_sp_bytes,
                    ),
                )
            })
            .expect("coherent exact machine roles");
        SsaArtifact::for_decompile_with_interfaces_and_machine_roles(
            &blocks,
            Some(&arch),
            Some(interface),
            roles,
            Vec::new(),
        )
        .expect("framed relation artifact")
    }

    #[test]
    fn fingerprint_binds_same_graph_different_coherent_frame_entry_relations() {
        let first = framed_relation_artifact(8, 0);
        let second = framed_relation_artifact(16, 0);
        assert_eq!(first.graph().blocks, second.graph().blocks);
        assert_eq!(first.graph().insts, second.graph().insts);
        assert_eq!(first.graph().values, second.graph().values);
        // The two describe the same geometry, and now say so. Both compute
        // their frame register from the stack pointer, and both store at the
        // same entry-relative addresses; the only difference is which register
        // the interface calls the frame pointer. That declaration used to move
        // every object, because a slot's position was recorded against
        // whichever register named it. In one coordinate it moves nothing.
        assert_eq!(
            first.objects().entry_stack_roots,
            second.objects().entry_stack_roots
        );
        // The declaration is still part of what the function is, so the
        // semantic fingerprint continues to separate them.
        assert_ne!(
            stable_ssa_semantic_fingerprint(&first),
            stable_ssa_semantic_fingerprint(&second)
        );
    }

    #[test]
    fn fingerprint_binds_source_owned_implicit_stack_contract() {
        let explicit_only = framed_relation_artifact(8, 0);
        let with_implicit = framed_relation_artifact(8, 128);
        assert_eq!(explicit_only.graph().blocks, with_implicit.graph().blocks);
        assert_eq!(explicit_only.graph().insts, with_implicit.graph().insts);
        assert_eq!(explicit_only.graph().values, with_implicit.graph().values);
        assert_eq!(explicit_only.objects(), with_implicit.objects());
        assert_eq!(explicit_only.memory(), with_implicit.memory());
        assert_ne!(
            stable_ssa_semantic_fingerprint(&explicit_only),
            stable_ssa_semantic_fingerprint(&with_implicit)
        );
    }

    #[test]
    fn semantic_fingerprint_schema_is_v6() {
        assert_eq!(SSA_SEMANTIC_FINGERPRINT_SCHEMA_VERSION, 6);
    }
}
