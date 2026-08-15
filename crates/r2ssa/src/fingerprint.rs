//! Stable, presentation-independent identity for prepared SSA semantics.

use std::collections::BTreeMap;

use crate::{
    BlockId, BlockTerminator, CanonicalStorageId, CanonicalStorageSpace, GraphBlock, GraphInst,
    InstPayload, SSAOp, SsaArtifact, SsaGraph, ValueId,
};
use r2il::{MemoryOrdering, SpaceId};

/// Version of the byte-level semantic fingerprint contract.
///
/// Bump this whenever a tag or field encoding below changes.
pub const SSA_SEMANTIC_FINGERPRINT_SCHEMA_VERSION: u32 = 2;

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

fn phi_sort_key(
    graph: &SsaGraph,
    inst: &GraphInst,
    block_ids: &BTreeMap<BlockId, u32>,
) -> (
    Option<CanonicalStorageId>,
    u32,
    Option<u64>,
    Vec<(u32, Option<CanonicalStorageId>, u32, Option<u64>)>,
) {
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
    writer.finish()
}

#[cfg(test)]
mod tests {
    use r2il::{
        ArchSpec, MemoryOrdering, R2ILBlock, R2ILOp, RegisterDef, SpaceId, SwitchCase, SwitchInfo,
        Varnode,
    };

    use super::stable_ssa_semantic_fingerprint;
    use crate::{SSAOp, SsaArtifact};

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
}
