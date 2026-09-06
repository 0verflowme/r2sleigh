use std::collections::{BTreeMap, BTreeSet};

use r2il::{ArchSpec, R2ILBlock, SpaceId};
use serde::{Deserialize, Serialize};

use crate::{CanonicalStorageSpace, GraphInst, InstPayload, SSAOp, SsaArtifact, SsaGraph, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum DataRefKind {
    Code,
    Data,
}

impl DataRefKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Code => "c",
            Self::Data => "d",
        }
    }

    pub const fn as_char(self) -> char {
        match self {
            Self::Code => 'c',
            Self::Data => 'd',
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DataRefFact {
    pub from: u64,
    pub to: u64,
    pub kind: DataRefKind,
    pub space: SpaceId,
}

impl Ord for DataRefFact {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.from
            .cmp(&other.from)
            .then_with(|| self.to.cmp(&other.to))
            .then_with(|| self.kind.cmp(&other.kind))
            .then_with(|| memory_space_order(self.space).cmp(&memory_space_order(other.space)))
    }
}

impl PartialOrd for DataRefFact {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl DataRefFact {
    const fn data(from: u64, to: u64, space: SpaceId) -> Self {
        Self {
            from,
            to,
            kind: DataRefKind::Data,
            space,
        }
    }

    const fn code(from: u64, to: u64, space: SpaceId) -> Self {
        Self {
            from,
            to,
            kind: DataRefKind::Code,
            space,
        }
    }
}

fn memory_space_order(space: SpaceId) -> (u8, u32) {
    match space {
        SpaceId::Ram => (0, 0),
        SpaceId::Register => (1, 0),
        SpaceId::Unique => (2, 0),
        SpaceId::Const => (3, 0),
        SpaceId::Custom(id) => (4, id),
    }
}

fn sort_and_dedup_refs(refs: &mut Vec<DataRefFact>) {
    refs.sort();
    refs.dedup();
}

/// Parse a legacy constant display spelling.
///
/// This remains a presentation helper for callers that have no proof-bearing
/// role. Data-reference recovery deliberately does not call it: constants in
/// that analysis come only from the sealed graph value.
pub fn parse_const_value(name: &str) -> Option<u64> {
    let val_str = name
        .strip_prefix("const:")
        .or_else(|| name.strip_prefix("CONST:"))?;
    let val_str = val_str.split('_').next().unwrap_or(val_str);
    if let Some(hex) = val_str
        .strip_prefix("0x")
        .or_else(|| val_str.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }
    if let Some(dec) = val_str
        .strip_prefix("0d")
        .or_else(|| val_str.strip_prefix("0D"))
    {
        return dec.parse::<u64>().ok();
    }
    if val_str.chars().all(|c| c.is_ascii_hexdigit()) {
        return u64::from_str_radix(val_str, 16).ok();
    }
    val_str.parse::<u64>().ok()
}

const fn bit_width(size: u32) -> u32 {
    let bits = size.saturating_mul(8);
    if bits > 64 { 64 } else { bits }
}

fn mask_to_bits(value: u64, bits: u32) -> u64 {
    match bits {
        0 => 0,
        64.. => value,
        n => value & ((1u64 << n) - 1),
    }
}

fn sign_extend_bits(value: u64, bits: u32) -> u64 {
    if bits == 0 {
        return 0;
    }
    if bits >= 64 {
        return value;
    }
    let masked = mask_to_bits(value, bits);
    let sign_bit = 1u64 << (bits - 1);
    if (masked & sign_bit) != 0 {
        masked | (!0u64 << bits)
    } else {
        masked
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstantState {
    Unknown,
    Exact(u64),
    Overdefined,
}

impl ConstantState {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Overdefined, _) | (_, Self::Overdefined) => Self::Overdefined,
            (Self::Unknown, value) | (value, Self::Unknown) => value,
            (Self::Exact(left), Self::Exact(right)) if left == right => Self::Exact(left),
            (Self::Exact(_), Self::Exact(_)) => Self::Overdefined,
        }
    }

    const fn exact(self) -> Option<u64> {
        match self {
            Self::Exact(value) => Some(value),
            Self::Unknown | Self::Overdefined => None,
        }
    }
}

fn exact_graph_constant(graph: &SsaGraph, value: ValueId) -> Option<u64> {
    let value = graph.value(value)?;
    let bits = value.var.constant_bits()?;
    let storage = value.canonical_storage?;
    (storage.space == CanonicalStorageSpace::Constant
        && storage.offset == bits
        && storage.size == value.var.size)
        .then(|| mask_to_bits(bits, bit_width(value.var.size)))
}

fn state_of(states: &[ConstantState], value: ValueId) -> ConstantState {
    states
        .get(value.0 as usize)
        .copied()
        .unwrap_or(ConstantState::Overdefined)
}

fn output_bits(graph: &SsaGraph, inst: &GraphInst) -> u32 {
    inst.output
        .and_then(|value| graph.value(value))
        .map(|value| bit_width(value.var.size))
        .unwrap_or(64)
}

fn unary_state<F>(states: &[ConstantState], input: ValueId, map: F) -> ConstantState
where
    F: FnOnce(u64) -> u64,
{
    match state_of(states, input) {
        ConstantState::Unknown => ConstantState::Unknown,
        ConstantState::Exact(value) => ConstantState::Exact(map(value)),
        ConstantState::Overdefined => ConstantState::Overdefined,
    }
}

fn binary_state<F>(states: &[ConstantState], inputs: &[ValueId], map: F) -> ConstantState
where
    F: FnOnce(u64, u64) -> u64,
{
    let [left, right] = inputs else {
        return ConstantState::Overdefined;
    };
    match (state_of(states, *left), state_of(states, *right)) {
        (ConstantState::Overdefined, _) | (_, ConstantState::Overdefined) => {
            ConstantState::Overdefined
        }
        (ConstantState::Exact(left), ConstantState::Exact(right)) => {
            ConstantState::Exact(map(left, right))
        }
        _ => ConstantState::Unknown,
    }
}

fn transfer_constant_state<F>(
    graph: &SsaGraph,
    inst: &GraphInst,
    states: &[ConstantState],
    reload_source: &mut F,
) -> ConstantState
where
    F: FnMut(&GraphInst, ValueId, &SSAOp) -> Option<ValueId>,
{
    let bits = output_bits(graph, inst);
    match &inst.payload {
        InstPayload::Phi { .. } => inst
            .inputs
            .iter()
            .copied()
            .fold(ConstantState::Unknown, |state, input| {
                state.join(state_of(states, input))
            }),
        InstPayload::Op(op) => match op {
            SSAOp::Copy { .. } | SSAOp::Cast { .. } | SSAOp::New { .. } => {
                let Some(input) = inst.inputs.first().copied() else {
                    return ConstantState::Overdefined;
                };
                unary_state(states, input, |value| mask_to_bits(value, bits))
            }
            SSAOp::IntAdd { .. } => binary_state(states, &inst.inputs, |left, right| {
                mask_to_bits(left.wrapping_add(right), bits)
            }),
            SSAOp::IntSub { .. } => binary_state(states, &inst.inputs, |left, right| {
                mask_to_bits(left.wrapping_sub(right), bits)
            }),
            SSAOp::PtrAdd { element_size, .. } => {
                binary_state(states, &inst.inputs, |base, index| {
                    mask_to_bits(
                        base.wrapping_add(index.wrapping_mul(u64::from(*element_size))),
                        bits,
                    )
                })
            }
            SSAOp::PtrSub { element_size, .. } => {
                binary_state(states, &inst.inputs, |base, index| {
                    mask_to_bits(
                        base.wrapping_sub(index.wrapping_mul(u64::from(*element_size))),
                        bits,
                    )
                })
            }
            SSAOp::IntZExt { .. } => {
                let Some(input) = inst.inputs.first().copied() else {
                    return ConstantState::Overdefined;
                };
                let input_bits = graph
                    .value(input)
                    .map(|value| bit_width(value.var.size))
                    .unwrap_or(64);
                unary_state(states, input, |value| {
                    mask_to_bits(mask_to_bits(value, input_bits), bits)
                })
            }
            SSAOp::IntSExt { .. } => {
                let Some(input) = inst.inputs.first().copied() else {
                    return ConstantState::Overdefined;
                };
                let input_bits = graph
                    .value(input)
                    .map(|value| bit_width(value.var.size))
                    .unwrap_or(64);
                unary_state(states, input, |value| {
                    mask_to_bits(sign_extend_bits(value, input_bits), bits)
                })
            }
            SSAOp::Load { .. } => inst
                .output
                .and_then(|output| reload_source(inst, output, op))
                .map(|source| unary_state(states, source, |value| mask_to_bits(value, bits)))
                .unwrap_or(ConstantState::Overdefined),
            _ => ConstantState::Overdefined,
        },
    }
}

fn propagated_constants<F>(graph: &SsaGraph, mut reload_source: F) -> Vec<ConstantState>
where
    F: FnMut(&GraphInst, ValueId, &SSAOp) -> Option<ValueId>,
{
    let mut states = graph
        .values
        .iter()
        .map(|value| {
            exact_graph_constant(graph, value.id)
                .map(ConstantState::Exact)
                .unwrap_or(ConstantState::Unknown)
        })
        .collect::<Vec<_>>();
    let mut ready = graph
        .insts
        .iter()
        .map(|inst| inst.id)
        .collect::<BTreeSet<_>>();
    while let Some(inst_id) = ready.pop_first() {
        let Some(inst) = graph.inst(inst_id) else {
            continue;
        };
        let Some(output) = inst.output else {
            continue;
        };
        let next = transfer_constant_state(graph, inst, &states, &mut reload_source);
        let slot = output.0 as usize;
        let Some(current) = states.get(slot).copied() else {
            continue;
        };
        let next = current.join(next);
        if next == current {
            continue;
        }
        states[slot] = next;
        for use_site in graph.use_sites(output) {
            ready.insert(use_site.inst);
        }
    }
    states
}

fn push_data_ref(
    refs: &mut Vec<DataRefFact>,
    states: &[ConstantState],
    value: Option<ValueId>,
    from: u64,
    space: SpaceId,
) {
    if let Some(target) = value
        .and_then(|value| state_of(states, value).exact())
        .filter(|target| *target >= 0x10000)
    {
        refs.push(DataRefFact::data(from, target, space));
    }
}

fn push_code_ref(
    refs: &mut Vec<DataRefFact>,
    states: &[ConstantState],
    value: Option<ValueId>,
    from: u64,
) {
    if let Some(target) = value
        .and_then(|value| state_of(states, value).exact())
        .filter(|target| *target >= 0x10000)
    {
        refs.push(DataRefFact::code(from, target, SpaceId::Ram));
    }
}

fn collect_graph_refs<F>(
    graph: &SsaGraph,
    op_sources: &BTreeMap<(u64, usize), u64>,
    reload_source: F,
) -> Vec<DataRefFact>
where
    F: FnMut(&GraphInst, ValueId, &SSAOp) -> Option<ValueId>,
{
    let states = propagated_constants(graph, reload_source);
    let mut refs = Vec::new();
    for inst in &graph.insts {
        let InstPayload::Op(op) = &inst.payload else {
            continue;
        };
        let Some((block_addr, op_idx)) = graph.op_site_for_inst(inst.id) else {
            continue;
        };
        let from = op_sources
            .get(&(block_addr, op_idx))
            .copied()
            .unwrap_or(block_addr);
        match op {
            SSAOp::Copy { .. }
            | SSAOp::Cast { .. }
            | SSAOp::New { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. } => push_data_ref(
                &mut refs,
                &states,
                inst.inputs.first().copied(),
                from,
                SpaceId::Ram,
            ),
            SSAOp::Load { space, .. }
            | SSAOp::LoadLinked { space, .. }
            | SSAOp::LoadGuarded { space, .. } => {
                push_data_ref(
                    &mut refs,
                    &states,
                    inst.inputs.first().copied(),
                    from,
                    *space,
                );
                push_data_ref(&mut refs, &states, inst.output, from, SpaceId::Ram);
            }
            SSAOp::Store { space, .. }
            | SSAOp::StoreConditional { space, .. }
            | SSAOp::StoreGuarded { space, .. } => {
                push_data_ref(
                    &mut refs,
                    &states,
                    inst.inputs.first().copied(),
                    from,
                    *space,
                );
                push_data_ref(
                    &mut refs,
                    &states,
                    inst.inputs.get(1).copied(),
                    from,
                    SpaceId::Ram,
                );
            }
            SSAOp::AtomicCAS { space, .. } => push_data_ref(
                &mut refs,
                &states,
                inst.inputs.first().copied(),
                from,
                *space,
            ),
            SSAOp::IntAdd { .. } | SSAOp::IntSub { .. } => {
                for input in &inst.inputs {
                    push_data_ref(&mut refs, &states, Some(*input), from, SpaceId::Ram);
                }
                push_data_ref(&mut refs, &states, inst.output, from, SpaceId::Ram);
            }
            SSAOp::PtrAdd { .. } | SSAOp::PtrSub { .. } => {
                push_data_ref(&mut refs, &states, inst.output, from, SpaceId::Ram)
            }
            SSAOp::Call { .. }
            | SSAOp::CallInd { .. }
            | SSAOp::Branch { .. }
            | SSAOp::BranchInd { .. }
            | SSAOp::CBranch { .. } => {
                push_code_ref(&mut refs, &states, inst.inputs.first().copied(), from)
            }
            _ => {}
        }
    }
    sort_and_dedup_refs(&mut refs);
    refs
}

/// Recover references from one sealed SSA artifact.
///
/// `op_sources` binds graph operation sites to their native instruction. When
/// an operation has no finer source address, its canonical block address is
/// used. No variable display spelling participates in identity or propagation.
pub fn data_refs_from_artifact_with_op_sources(
    artifact: &SsaArtifact,
    op_sources: &BTreeMap<(u64, usize), u64>,
) -> Vec<DataRefFact> {
    collect_graph_refs(artifact.graph(), op_sources, |inst, output, op| {
        let SSAOp::Load { space, .. } = op else {
            return None;
        };
        let cert = artifact.stack_reload_certificate_for_value(output)?;
        let address = inst.inputs.first().copied()?;
        (cert.value == output
            && cert.reload == output
            && cert.load_inst == inst.id
            && artifact.objects().object(cert.object).is_some()
            && artifact.objects().object_for_value(address, *space) == Some(cert.object))
        .then_some(cert.canonical_source)
    })
}

/// Build the one authoritative SSA artifact used by the plugin xref callback.
pub fn data_refs_from_blocks(
    blocks: &[R2ILBlock],
    arch: Option<&ArchSpec>,
) -> Option<Vec<DataRefFact>> {
    let artifact = SsaArtifact::for_data_refs(blocks, arch)?;
    if artifact.graph().blocks.is_empty() {
        return None;
    }
    let op_sources = blocks
        .iter()
        .flat_map(|block| {
            block.ops.iter().enumerate().map(|(op_idx, _)| {
                let instruction_addr = block
                    .op_metadata(op_idx)
                    .and_then(|metadata| metadata.instruction_addr)
                    .unwrap_or(block.addr);
                ((block.addr, op_idx), instruction_addr)
            })
        })
        .collect::<BTreeMap<_, _>>();
    Some(data_refs_from_artifact_with_op_sources(
        &artifact,
        &op_sources,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BlockId, CanonicalStorageId, GraphBlock, GraphValue, InstId, SSAVar, UseSite};
    use r2il::{R2ILOp, Varnode};

    fn graph_value(id: u32, var: SSAVar, space: CanonicalStorageSpace, offset: u64) -> GraphValue {
        GraphValue {
            id: ValueId(id),
            canonical_storage: Some(CanonicalStorageId {
                space,
                offset,
                size: var.size,
            }),
            var,
        }
    }

    fn graph_with_ops(
        values: Vec<GraphValue>,
        ops: Vec<(Vec<ValueId>, Option<ValueId>, SSAOp)>,
    ) -> SsaGraph {
        let block = BlockId(0);
        let mut insts = Vec::new();
        let mut def_of = vec![None; values.len()];
        let mut uses_of = vec![Vec::new(); values.len()];
        let mut op_inst_by_site = BTreeMap::new();
        let mut op_site_by_inst = BTreeMap::new();
        for (ordinal, (inputs, output, op)) in ops.into_iter().enumerate() {
            let id = InstId(ordinal as u32);
            for (input_idx, input) in inputs.iter().copied().enumerate() {
                uses_of[input.0 as usize].push(UseSite {
                    inst: id,
                    input_idx,
                });
            }
            if let Some(output) = output {
                def_of[output.0 as usize] = Some(id);
            }
            op_inst_by_site.insert((0x401000, ordinal), id);
            op_site_by_inst.insert(id, (0x401000, ordinal));
            insts.push(GraphInst {
                id,
                block,
                ordinal,
                inputs,
                output,
                canonical_storage: output
                    .and_then(|value| values.get(value.0 as usize))
                    .and_then(|value| value.canonical_storage),
                payload: InstPayload::Op(op),
            });
        }
        let inst_ids = insts.iter().map(|inst| inst.id).collect::<Vec<_>>();
        let value_by_var = values
            .iter()
            .map(|value| (value.var.clone(), value.id))
            .collect();
        SsaGraph {
            entry: block,
            block_order: vec![block],
            blocks: vec![GraphBlock {
                id: block,
                addr: 0x401000,
                size: 4,
                predecessors: Vec::new(),
                successors: Vec::new(),
                insts: inst_ids,
            }],
            insts,
            values,
            def_of,
            uses_of,
            block_by_addr: BTreeMap::from([(0x401000, block)]),
            value_by_var,
            op_inst_by_site,
            op_site_by_inst,
        }
    }

    #[test]
    fn exact_value_ids_keep_case_colliding_names_separate() {
        let first_constant = SSAVar::constant(0x410000, 8);
        let second_constant = SSAVar::constant(0x520000, 8);
        let first = SSAVar::new("Alias", 1, 8);
        let second = SSAVar::new("alias", 1, 8);
        let first_load = SSAVar::new("first_load", 1, 8);
        let second_load = SSAVar::new("second_load", 1, 8);
        let graph = graph_with_ops(
            vec![
                graph_value(
                    0,
                    first_constant.clone(),
                    CanonicalStorageSpace::Constant,
                    0x410000,
                ),
                graph_value(
                    1,
                    second_constant.clone(),
                    CanonicalStorageSpace::Constant,
                    0x520000,
                ),
                graph_value(2, first.clone(), CanonicalStorageSpace::Unique, 0x10),
                graph_value(3, second.clone(), CanonicalStorageSpace::Unique, 0x20),
                graph_value(4, first_load.clone(), CanonicalStorageSpace::Unique, 0x30),
                graph_value(5, second_load.clone(), CanonicalStorageSpace::Unique, 0x40),
            ],
            vec![
                (
                    vec![ValueId(0)],
                    Some(ValueId(2)),
                    SSAOp::Copy {
                        dst: first.clone(),
                        src: first_constant,
                    },
                ),
                (
                    vec![ValueId(1)],
                    Some(ValueId(3)),
                    SSAOp::Copy {
                        dst: second.clone(),
                        src: second_constant,
                    },
                ),
                (
                    vec![ValueId(2)],
                    Some(ValueId(4)),
                    SSAOp::Load {
                        dst: first_load,
                        space: SpaceId::Ram,
                        addr: first,
                    },
                ),
                (
                    vec![ValueId(3)],
                    Some(ValueId(5)),
                    SSAOp::Load {
                        dst: second_load,
                        space: SpaceId::Ram,
                        addr: second,
                    },
                ),
            ],
        );
        let sources = BTreeMap::from([((0x401000, 2), 0x401008), ((0x401000, 3), 0x40100c)]);
        let refs = collect_graph_refs(&graph, &sources, |_, _, _| None);
        assert!(refs.contains(&DataRefFact::data(0x401008, 0x410000, SpaceId::Ram)));
        assert!(refs.contains(&DataRefFact::data(0x40100c, 0x520000, SpaceId::Ram)));
        assert!(!refs.contains(&DataRefFact::data(0x401008, 0x520000, SpaceId::Ram)));
        assert!(!refs.contains(&DataRefFact::data(0x40100c, 0x410000, SpaceId::Ram)));
    }

    #[test]
    fn constant_spelling_without_exact_bits_is_not_evidence() {
        let spoofed = SSAVar::new("const:deadbeef", 0, 8);
        let loaded = SSAVar::new("loaded", 1, 8);
        let graph = graph_with_ops(
            vec![
                graph_value(0, spoofed.clone(), CanonicalStorageSpace::Unique, 0x10),
                graph_value(1, loaded.clone(), CanonicalStorageSpace::Unique, 0x20),
            ],
            vec![(
                vec![ValueId(0)],
                Some(ValueId(1)),
                SSAOp::Load {
                    dst: loaded,
                    space: SpaceId::Ram,
                    addr: spoofed,
                },
            )],
        );
        assert!(collect_graph_refs(&graph, &BTreeMap::new(), |_, _, _| None).is_empty());
    }

    #[test]
    fn artifact_api_uses_exact_constants_and_op_source_sites() {
        let mut block = R2ILBlock::new(0x404000, 0x20);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(0x404d00, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(0x108, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x30, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x20, 8),
        });
        let artifact = SsaArtifact::for_data_refs(&[block], None).expect("valid SSA artifact");
        let sources = BTreeMap::from([
            ((0x404000, 0), 0x404008),
            ((0x404000, 1), 0x40400c),
            ((0x404000, 2), 0x404010),
        ]);
        let refs = data_refs_from_artifact_with_op_sources(&artifact, &sources);
        assert!(refs.contains(&DataRefFact::data(0x40400c, 0x404e08, SpaceId::Ram)));
        assert!(refs.contains(&DataRefFact::data(0x404010, 0x404e08, SpaceId::Ram)));
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    #[kani::proof]
    fn data_ref_bit_width_clamps_to_machine_word() {
        let size: u32 = kani::any();
        let bits = bit_width(size);
        assert!(bits <= 64);
        if size <= 8 {
            assert_eq!(bits, size * 8);
        } else {
            assert_eq!(bits, 64);
        }
    }

    #[kani::proof]
    fn data_ref_mask_to_bits_is_total_and_bounded() {
        let value: u64 = kani::any();
        let bits: u32 = kani::any();
        let masked = mask_to_bits(value, bits);
        if bits == 0 {
            assert_eq!(masked, 0);
        } else if bits >= 64 {
            assert_eq!(masked, value);
        } else {
            let expected = value & ((1u64 << bits) - 1);
            assert_eq!(masked, expected);
            assert_eq!(masked >> bits, 0);
        }
    }
}
