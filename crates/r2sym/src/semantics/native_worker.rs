use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    FunctionSemanticSummary, SSAOp, SSAVar, SsaArtifact, SummaryAllocationEffect,
    SummaryAtomicEffect, SummaryLifetimeEffect, SummaryMemoryEffect, SummaryMemoryEffectKind,
    SummaryMemoryLocation, SummaryMemoryRange, SummaryMemoryRegion, SummarySyncEffect,
    SummaryTransferEffect, SummaryTransferLength,
};

use crate::semantics::{
    NativeLoopSummary, NativeMemoryAccessKind, NativeMemoryAccessSummary, NativeParserKind,
    NativeParserSummary, NativeReductionSummary, NativeRegionSummary, NativeWorkerFold,
    NativeWorkerFoldOperation, NativeWorkerLoopSummary, NativeWorkerSummary,
    NativeWorkerSummaryKind, NativeWorkerTerminator, ResidualReason, SemanticEvidence,
    SemanticEvidenceAmbiguity, SemanticEvidenceCoverage, SemanticEvidenceProvenance,
    SemanticEvidenceReason,
};

pub(super) const NATIVE_WORKER_SUMMARY_MAX: usize = 32;

type NativeWorkerSummarySortKey = (
    u64,
    NativeWorkerSummaryKind,
    Option<SummaryMemoryLocation>,
    Option<SummaryMemoryLocation>,
    Option<SummaryMemoryLocation>,
    Option<SummaryTransferLength>,
    Option<SummaryAllocationEffect>,
    Option<SummaryLifetimeEffect>,
    Option<SummarySyncEffect>,
    Option<SummaryAtomicEffect>,
    Option<NativeParserSummary>,
    Option<NativeWorkerLoopSummary>,
);

type NativeRegionSummarySortKey = (
    u64,
    NativeWorkerSummaryKind,
    BTreeSet<u64>,
    BTreeSet<u64>,
    BTreeSet<u64>,
    Option<NativeLoopSummary>,
    Vec<NativeMemoryAccessSummary>,
    Vec<NativeReductionSummary>,
    Option<NativeParserSummary>,
);

type NativeRegionSummaryJoinKey = (NativeWorkerSummaryKind, BTreeSet<u64>, Option<u64>);

type NativeMemoryLocationJoinKey = (SummaryMemoryRegion, Option<u32>);
type NativeMemoryAccessJoinKey = (
    NativeMemoryAccessKind,
    Option<NativeMemoryLocationJoinKey>,
    Option<NativeMemoryLocationJoinKey>,
    Option<NativeMemoryLocationJoinKey>,
    Option<SummaryTransferLength>,
    Option<u32>,
);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct LoopIsland {
    header: u64,
    body: BTreeSet<u64>,
    entries: BTreeSet<u64>,
    exits: BTreeSet<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct LargeCfgMemoryTransfer {
    pub(super) block_addr: u64,
    pub(super) dst_arg: usize,
    pub(super) src_arg: usize,
    pub(super) size: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LoadedSource {
    location: SummaryMemoryLocation,
    size: u32,
    block_addr: u64,
    value_delta: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RegisterAliasSpec {
    family: String,
    offset_bits: u32,
    width_bits: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DataflowValue<T> {
    Exact(T),
    Unknown,
}

impl<T> DataflowValue<T> {
    fn exact(&self) -> Option<&T> {
        match self {
            Self::Exact(value) => Some(value),
            Self::Unknown => None,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct WorkerDataflowState {
    roots: BTreeMap<SSAVar, DataflowValue<SummaryMemoryRegion>>,
    load_sources: BTreeMap<SSAVar, DataflowValue<LoadedSource>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ParserByteRange {
    lo: u8,
    hi: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScanObservation {
    anchor: u64,
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FoldObservation {
    anchor: u64,
    source: LoadedSource,
    accumulator: String,
    operation: NativeWorkerFoldOperation,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ParserLoopEvidence {
    anchor: u64,
    byte_values: BTreeSet<u8>,
    byte_ranges: BTreeSet<ParserByteRange>,
    accepts_sign: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct BlockWorkerObservations {
    scans: Vec<ScanObservation>,
    folds: Vec<FoldObservation>,
    parser_comparisons: BTreeMap<usize, ParserLoopEvidence>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct LoopEffectSummary {
    island: LoopIsland,
    natural_loop: bool,
    scans: Vec<ScanObservation>,
    folds: Vec<FoldObservation>,
    parser_comparisons: BTreeMap<usize, ParserLoopEvidence>,
}

pub(super) fn bounded_evidence() -> SemanticEvidence {
    SemanticEvidence::likely(SemanticEvidenceReason::SummaryBudget)
        .with_coverage(SemanticEvidenceCoverage::Bounded)
        .with_provenance(SemanticEvidenceProvenance::Stable)
        .with_budget_limited(true)
}

fn native_worker_summary_sort_key(summary: &NativeWorkerSummary) -> NativeWorkerSummarySortKey {
    (
        summary.anchor,
        summary.kind,
        summary.dst,
        summary.src,
        summary.memory,
        summary.len,
        summary.allocation,
        summary.lifetime,
        summary.sync,
        summary.atomic,
        summary.parser.clone(),
        summary.loop_summary.clone(),
    )
}

pub(super) fn bounded_worker_summaries(
    mut summaries: Vec<NativeWorkerSummary>,
) -> Vec<NativeWorkerSummary> {
    summaries.sort_by_key(native_worker_summary_sort_key);
    summaries.dedup();
    summaries.truncate(NATIVE_WORKER_SUMMARY_MAX);
    summaries
}

fn native_region_summary_sort_key(summary: &NativeRegionSummary) -> NativeRegionSummarySortKey {
    (
        summary.anchor,
        summary.kind,
        summary.blocks.clone(),
        summary.entries.clone(),
        summary.exits.clone(),
        summary.loop_summary.clone(),
        summary.memory_accesses.clone(),
        summary.reductions.clone(),
        summary.parser.clone(),
    )
}

fn native_region_summary_join_key(summary: &NativeRegionSummary) -> NativeRegionSummaryJoinKey {
    (
        summary.kind,
        summary.blocks.clone(),
        summary
            .loop_summary
            .as_ref()
            .map(|loop_summary| loop_summary.header),
    )
}

fn memory_location_join_key(
    location: Option<SummaryMemoryLocation>,
) -> Option<NativeMemoryLocationJoinKey> {
    location.map(|location| {
        (
            location.region,
            location.range.and_then(|range| range.width),
        )
    })
}

fn memory_access_join_key(access: &NativeMemoryAccessSummary) -> NativeMemoryAccessJoinKey {
    (
        access.kind,
        memory_location_join_key(access.location),
        memory_location_join_key(access.dst),
        memory_location_join_key(access.src),
        access.len,
        access.width,
    )
}

fn join_memory_range(
    left: Option<SummaryMemoryRange>,
    right: Option<SummaryMemoryRange>,
) -> Option<SummaryMemoryRange> {
    match (left, right) {
        (Some(left), Some(right)) => Some(SummaryMemoryRange {
            offset_lo: left.offset_lo.min(right.offset_lo),
            offset_hi: left.offset_hi.max(right.offset_hi),
            width: if left.width == right.width {
                left.width
            } else {
                None
            },
        }),
        _ => None,
    }
}

fn join_memory_location(
    left: Option<SummaryMemoryLocation>,
    right: Option<SummaryMemoryLocation>,
) -> Option<SummaryMemoryLocation> {
    match (left, right) {
        (Some(left), Some(right)) if left.region == right.region => Some(SummaryMemoryLocation {
            region: left.region,
            range: join_memory_range(left.range, right.range),
        }),
        (Some(left), None) => Some(SummaryMemoryLocation {
            region: left.region,
            range: None,
        }),
        (None, Some(right)) => Some(SummaryMemoryLocation {
            region: right.region,
            range: None,
        }),
        _ => None,
    }
}

fn canonical_memory_access_summaries(
    accesses: Vec<NativeMemoryAccessSummary>,
) -> Vec<NativeMemoryAccessSummary> {
    let mut joined = BTreeMap::<NativeMemoryAccessJoinKey, NativeMemoryAccessSummary>::new();
    for access in accesses {
        let key = memory_access_join_key(&access);
        if let Some(existing) = joined.get_mut(&key) {
            existing.location = join_memory_location(existing.location, access.location);
            existing.dst = join_memory_location(existing.dst, access.dst);
            existing.src = join_memory_location(existing.src, access.src);
        } else {
            joined.insert(key, access);
        }
    }
    joined.into_values().collect()
}

fn join_optional_exact<T: Eq>(left: &mut Option<T>, right: Option<T>) {
    match (left.as_ref(), right) {
        (Some(left_value), Some(right_value)) if *left_value == right_value => {}
        (None, None) => {}
        _ => *left = None,
    }
}

fn join_loop_summary(left: &mut Option<NativeLoopSummary>, right: Option<NativeLoopSummary>) {
    match (left.as_mut(), right) {
        (Some(left_summary), Some(right_summary)) => {
            left_summary.header = left_summary.header.min(right_summary.header);
            left_summary.body.extend(right_summary.body);
            left_summary.entries.extend(right_summary.entries);
            left_summary.exits.extend(right_summary.exits);
            join_optional_exact(&mut left_summary.iterations, right_summary.iterations);
            join_optional_exact(&mut left_summary.length_arg, right_summary.length_arg);
            join_optional_exact(&mut left_summary.stride, right_summary.stride);
            join_optional_exact(&mut left_summary.terminator, right_summary.terminator);
        }
        (Some(_), None) => *left = None,
        (None, Some(_)) | (None, None) => {}
    }
}

fn join_region_summary(left: &mut NativeRegionSummary, right: NativeRegionSummary) {
    left.anchor = left.anchor.min(right.anchor);
    left.blocks.extend(right.blocks);
    left.entries.extend(right.entries);
    left.exits.extend(right.exits);
    left.memory_accesses.extend(right.memory_accesses);
    left.memory_accesses =
        canonical_memory_access_summaries(std::mem::take(&mut left.memory_accesses));
    join_loop_summary(&mut left.loop_summary, right.loop_summary);
    left.reductions.extend(right.reductions);
    left.reductions.sort();
    left.reductions.dedup();
    join_optional_exact(&mut left.parser, right.parser);
    left.residual_reasons.extend(right.residual_reasons);
    left.residual_reasons.sort();
    left.residual_reasons.dedup();
    left.evidence = left
        .evidence
        .combined_with(&right.evidence)
        .with_ambiguity(SemanticEvidenceAmbiguity::Bounded);
    left.confidence = left.evidence.tier;
    left.stable_id = stable_region_summary_id(left.anchor, left.kind, &left.blocks);
}

pub(super) fn canonical_region_summaries(
    mut summaries: Vec<NativeRegionSummary>,
) -> Vec<NativeRegionSummary> {
    for summary in &mut summaries {
        summary.memory_accesses =
            canonical_memory_access_summaries(std::mem::take(&mut summary.memory_accesses));
        summary.reductions.sort();
        summary.reductions.dedup();
        summary.residual_reasons.sort();
        summary.residual_reasons.dedup();
    }
    let mut joined = BTreeMap::<NativeRegionSummaryJoinKey, NativeRegionSummary>::new();
    for summary in summaries {
        let key = native_region_summary_join_key(&summary);
        if let Some(existing) = joined.get_mut(&key) {
            join_region_summary(existing, summary);
        } else {
            joined.insert(key, summary);
        }
    }
    let mut summaries = joined.into_values().collect::<Vec<_>>();
    summaries.sort_by_key(native_region_summary_sort_key);
    summaries
}

fn worker_kind_rank(kind: NativeWorkerSummaryKind) -> u64 {
    match kind {
        NativeWorkerSummaryKind::MemoryTransfer => 1,
        NativeWorkerSummaryKind::MemoryRead => 2,
        NativeWorkerSummaryKind::MemoryWrite => 3,
        NativeWorkerSummaryKind::MemoryEscape => 4,
        NativeWorkerSummaryKind::MemoryFree => 5,
        NativeWorkerSummaryKind::StringScan => 6,
        NativeWorkerSummaryKind::HashFold => 7,
        NativeWorkerSummaryKind::TableWalk => 8,
        NativeWorkerSummaryKind::Parser => 9,
        NativeWorkerSummaryKind::Allocation => 10,
        NativeWorkerSummaryKind::Lifetime => 11,
        NativeWorkerSummaryKind::Synchronization => 12,
        NativeWorkerSummaryKind::Atomic => 13,
        NativeWorkerSummaryKind::Unknown => 14,
    }
}

fn stable_region_summary_id(
    anchor: u64,
    kind: NativeWorkerSummaryKind,
    blocks: &BTreeSet<u64>,
) -> u64 {
    let mut id = anchor.rotate_left(13) ^ (worker_kind_rank(kind) << 56);
    id ^= (blocks.len() as u64).rotate_left(7);
    if let Some(first) = blocks.first() {
        id ^= first.rotate_left(23);
    }
    if let Some(last) = blocks.last() {
        id ^= last.rotate_left(37);
    }
    id
}

fn memory_effect_worker_kind(kind: SummaryMemoryEffectKind) -> NativeWorkerSummaryKind {
    match kind {
        SummaryMemoryEffectKind::Read => NativeWorkerSummaryKind::MemoryRead,
        SummaryMemoryEffectKind::Write => NativeWorkerSummaryKind::MemoryWrite,
        SummaryMemoryEffectKind::Escape => NativeWorkerSummaryKind::MemoryEscape,
        SummaryMemoryEffectKind::Free => NativeWorkerSummaryKind::MemoryFree,
    }
}

pub(super) fn transfer_worker_summary(
    anchor: u64,
    effect: SummaryTransferEffect,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::MemoryTransfer,
        dst: Some(effect.dst),
        src: Some(effect.src),
        memory: None,
        len: Some(effect.len),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn memory_worker_summary(anchor: u64, effect: SummaryMemoryEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: memory_effect_worker_kind(effect.kind),
        dst: None,
        src: None,
        memory: Some(effect.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn allocation_worker_summary(anchor: u64, effect: SummaryAllocationEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Allocation,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: Some(effect),
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn lifetime_worker_summary(anchor: u64, effect: SummaryLifetimeEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Lifetime,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: None,
        lifetime: Some(effect),
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn sync_worker_summary(anchor: u64, effect: SummarySyncEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Synchronization,
        dst: None,
        src: None,
        memory: None,
        len: None,
        allocation: None,
        lifetime: None,
        sync: Some(effect),
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn atomic_worker_summary(anchor: u64, effect: SummaryAtomicEffect) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Atomic,
        dst: None,
        src: None,
        memory: Some(effect.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: Some(effect),
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

pub(super) fn summaries_from_interproc_summary_unbounded(
    anchor: u64,
    summary: &FunctionSemanticSummary,
) -> Vec<NativeWorkerSummary> {
    let mut worker_summaries = Vec::new();
    worker_summaries.extend(
        summary
            .transfer_effects
            .iter()
            .copied()
            .map(|effect| transfer_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .memory_effects
            .iter()
            .copied()
            .map(|effect| memory_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .allocation_effects
            .iter()
            .copied()
            .map(|effect| allocation_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .lifetime_effects
            .iter()
            .copied()
            .map(|effect| lifetime_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .sync_effects
            .iter()
            .copied()
            .map(|effect| sync_worker_summary(anchor, effect)),
    );
    worker_summaries.extend(
        summary
            .atomic_effects
            .iter()
            .copied()
            .map(|effect| atomic_worker_summary(anchor, effect)),
    );
    worker_summaries
}

fn parse_hexish_u64(text: &str) -> Option<u64> {
    let trimmed = text.trim();
    let hex = trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
        .unwrap_or(trimmed);
    u64::from_str_radix(hex, 16).ok()
}

fn const_value(var: &SSAVar) -> Option<u64> {
    var.name.strip_prefix("const:").and_then(parse_hexish_u64)
}

fn ram_address(var: &SSAVar) -> Option<u64> {
    var.name.strip_prefix("ram:").and_then(parse_hexish_u64)
}

fn register_base_name(var: &SSAVar) -> &str {
    var.name
        .strip_prefix("reg:")
        .unwrap_or(var.name.as_str())
        .trim_start_matches('_')
}

fn x86_register_alias_spec(base: &str) -> Option<RegisterAliasSpec> {
    let upper = base.to_ascii_uppercase();
    let fixed = match upper.as_str() {
        "AL" => Some(("RAX", 0, 8)),
        "AH" => Some(("RAX", 8, 8)),
        "AX" => Some(("RAX", 0, 16)),
        "EAX" => Some(("RAX", 0, 32)),
        "RAX" => Some(("RAX", 0, 64)),
        "BL" => Some(("RBX", 0, 8)),
        "BH" => Some(("RBX", 8, 8)),
        "BX" => Some(("RBX", 0, 16)),
        "EBX" => Some(("RBX", 0, 32)),
        "RBX" => Some(("RBX", 0, 64)),
        "CL" => Some(("RCX", 0, 8)),
        "CH" => Some(("RCX", 8, 8)),
        "CX" => Some(("RCX", 0, 16)),
        "ECX" => Some(("RCX", 0, 32)),
        "RCX" => Some(("RCX", 0, 64)),
        "DL" => Some(("RDX", 0, 8)),
        "DH" => Some(("RDX", 8, 8)),
        "DX" => Some(("RDX", 0, 16)),
        "EDX" => Some(("RDX", 0, 32)),
        "RDX" => Some(("RDX", 0, 64)),
        "SIL" => Some(("RSI", 0, 8)),
        "SI" => Some(("RSI", 0, 16)),
        "ESI" => Some(("RSI", 0, 32)),
        "RSI" => Some(("RSI", 0, 64)),
        "DIL" => Some(("RDI", 0, 8)),
        "DI" => Some(("RDI", 0, 16)),
        "EDI" => Some(("RDI", 0, 32)),
        "RDI" => Some(("RDI", 0, 64)),
        "BPL" => Some(("RBP", 0, 8)),
        "BP" => Some(("RBP", 0, 16)),
        "EBP" => Some(("RBP", 0, 32)),
        "RBP" => Some(("RBP", 0, 64)),
        "SPL" => Some(("RSP", 0, 8)),
        "SP" => Some(("RSP", 0, 16)),
        "ESP" => Some(("RSP", 0, 32)),
        "RSP" => Some(("RSP", 0, 64)),
        _ => None,
    };
    if let Some((family, offset_bits, width_bits)) = fixed {
        return Some(RegisterAliasSpec {
            family: family.to_string(),
            offset_bits,
            width_bits,
        });
    }

    let (family, width_bits) = if let Some(family) = upper.strip_suffix('B') {
        (family.to_string(), 8)
    } else if let Some(family) = upper.strip_suffix('W') {
        (family.to_string(), 16)
    } else if let Some(family) = upper.strip_suffix('D') {
        (family.to_string(), 32)
    } else {
        (upper, 64)
    };
    if !family.starts_with('R') {
        return None;
    }
    let digits = &family[1..];
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    Some(RegisterAliasSpec {
        family,
        offset_bits: 0,
        width_bits,
    })
}

fn x86_alias_covers(candidate: &RegisterAliasSpec, requested: &RegisterAliasSpec) -> bool {
    candidate.family == requested.family
        && candidate.offset_bits <= requested.offset_bits
        && candidate.offset_bits + candidate.width_bits
            >= requested.offset_bits + requested.width_bits
}

fn same_x86_alias_family(left: &SSAVar, right: &SSAVar) -> bool {
    let Some(left) = x86_register_alias_spec(register_base_name(left)) else {
        return false;
    };
    let Some(right) = x86_register_alias_spec(register_base_name(right)) else {
        return false;
    };
    left.family == right.family
}

fn abi_pointer_arg_index(var: &SSAVar) -> Option<usize> {
    let name = register_base_name(var).to_ascii_lowercase();
    match name.as_str() {
        "x0" | "w0" | "rdi" | "edi" | "di" | "a0" => Some(0),
        "x1" | "w1" | "rsi" | "esi" | "si" | "a1" => Some(1),
        "x2" | "w2" | "rdx" | "edx" | "dx" | "a2" => Some(2),
        "x3" | "w3" | "rcx" | "ecx" | "cx" | "a3" => Some(3),
        "x4" | "w4" | "r8" | "r8d" | "a4" => Some(4),
        "x5" | "w5" | "r9" | "r9d" | "a5" => Some(5),
        "x6" | "w6" | "a6" => Some(6),
        "x7" | "w7" | "a7" => Some(7),
        _ => None,
    }
}

fn rooted_region(
    var: &SSAVar,
    roots: &BTreeMap<SSAVar, SummaryMemoryRegion>,
) -> Option<SummaryMemoryRegion> {
    abi_pointer_arg_index(var)
        .map(|index| SummaryMemoryRegion::Arg { index })
        .or_else(|| ram_address(var).map(|address| SummaryMemoryRegion::Global { address }))
        .or_else(|| roots.get(var).copied())
}

fn rooted_arg_var(var: &SSAVar, roots: &BTreeMap<SSAVar, SummaryMemoryRegion>) -> Option<usize> {
    match rooted_region(var, roots)? {
        SummaryMemoryRegion::Arg { index } => Some(index),
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => None,
    }
}

fn location_from_region(region: SummaryMemoryRegion, width: u32) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region,
        range: Some(SummaryMemoryRange {
            offset_lo: 0,
            offset_hi: 0,
            width: Some(width),
        }),
    }
}

fn copy_root_if_known(
    dst: &SSAVar,
    src: &SSAVar,
    roots: &mut BTreeMap<SSAVar, SummaryMemoryRegion>,
) {
    if let Some(root) = rooted_region(src, roots) {
        roots.insert(dst.clone(), root);
    }
}

fn copy_binary_root_if_unambiguous(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    roots: &mut BTreeMap<SSAVar, SummaryMemoryRegion>,
) {
    let a_root = rooted_region(a, roots);
    let b_root = rooted_region(b, roots);
    match (a_root, b_root) {
        (Some(root), None) | (None, Some(root)) => {
            roots.insert(dst.clone(), root);
        }
        (Some(a_root), Some(b_root)) if a_root == b_root => {
            roots.insert(dst.clone(), a_root);
        }
        _ => {}
    }
}

fn copy_phi_root_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    roots: &mut BTreeMap<SSAVar, SummaryMemoryRegion>,
) {
    let mut source_roots = sources
        .into_iter()
        .filter_map(|src| rooted_region(src, roots));
    if let Some(first) = source_roots.next()
        && source_roots.all(|root| root == first)
    {
        roots.insert(dst.clone(), first);
    }
}

fn loaded_source(
    var: &SSAVar,
    load_sources: &BTreeMap<SSAVar, LoadedSource>,
) -> Option<LoadedSource> {
    if let Some(source) = load_sources.get(var).copied() {
        return Some(source);
    }
    let requested = x86_register_alias_spec(register_base_name(var))?;
    load_sources
        .iter()
        .filter_map(|(candidate, source)| {
            let candidate_spec = x86_register_alias_spec(register_base_name(candidate))?;
            x86_alias_covers(&candidate_spec, &requested).then_some((
                candidate.version,
                candidate_spec.width_bits,
                *source,
            ))
        })
        .max_by_key(|(version, width_bits, _)| (*version, *width_bits))
        .map(|(_, _, source)| source)
}

fn exact_dataflow_value<T: Copy>(value: Option<&DataflowValue<T>>) -> Option<T> {
    value.and_then(DataflowValue::exact).copied()
}

fn join_dataflow_value<T: Clone + Eq>(
    left: &mut DataflowValue<T>,
    right: &DataflowValue<T>,
) -> bool {
    match (&*left, right) {
        (DataflowValue::Unknown, _) | (_, DataflowValue::Unknown) => {
            if !matches!(left, DataflowValue::Unknown) {
                *left = DataflowValue::Unknown;
                return true;
            }
            false
        }
        (DataflowValue::Exact(left_value), DataflowValue::Exact(right_value)) => {
            if left_value == right_value {
                false
            } else {
                *left = DataflowValue::Unknown;
                true
            }
        }
    }
}

fn join_dataflow_map<T: Clone + Eq>(
    left: &mut BTreeMap<SSAVar, DataflowValue<T>>,
    right: &BTreeMap<SSAVar, DataflowValue<T>>,
) -> bool {
    let mut changed = false;
    for (key, right_value) in right {
        if let Some(left_value) = left.get_mut(key) {
            changed |= join_dataflow_value(left_value, right_value);
        } else {
            left.insert(key.clone(), right_value.clone());
            changed = true;
        }
    }
    changed
}

fn join_worker_state(left: &mut WorkerDataflowState, right: &WorkerDataflowState) -> bool {
    let roots_changed = join_dataflow_map(&mut left.roots, &right.roots);
    let loads_changed = join_dataflow_map(&mut left.load_sources, &right.load_sources);
    roots_changed || loads_changed
}

fn insert_exact_dataflow_value<T: Clone + Eq>(
    map: &mut BTreeMap<SSAVar, DataflowValue<T>>,
    key: &SSAVar,
    value: T,
) {
    match map.get_mut(key) {
        Some(existing @ DataflowValue::Unknown) => {
            *existing = DataflowValue::Exact(value);
        }
        Some(existing) => {
            let _ = join_dataflow_value(existing, &DataflowValue::Exact(value));
        }
        None => {
            map.insert(key.clone(), DataflowValue::Exact(value));
        }
    }
}

fn dataflow_rooted_region(
    var: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<SummaryMemoryRegion> {
    abi_pointer_arg_index(var)
        .map(|index| SummaryMemoryRegion::Arg { index })
        .or_else(|| ram_address(var).map(|address| SummaryMemoryRegion::Global { address }))
        .or_else(|| exact_dataflow_value(state.roots.get(var)))
}

fn dataflow_loaded_source(var: &SSAVar, state: &WorkerDataflowState) -> Option<LoadedSource> {
    if let Some(source) = exact_dataflow_value(state.load_sources.get(var)) {
        return Some(source);
    }
    let requested = x86_register_alias_spec(register_base_name(var))?;
    state
        .load_sources
        .iter()
        .filter_map(|(candidate, source)| {
            let source = source.exact().copied()?;
            let candidate_spec = x86_register_alias_spec(register_base_name(candidate))?;
            x86_alias_covers(&candidate_spec, &requested).then_some((
                candidate.version,
                candidate_spec.width_bits,
                source,
            ))
        })
        .max_by_key(|(version, width_bits, _)| (*version, *width_bits))
        .map(|(_, _, source)| source)
}

fn dataflow_kill_load_source_aliases(dst: &SSAVar, state: &mut WorkerDataflowState) {
    if x86_register_alias_spec(register_base_name(dst)).is_none() {
        state.load_sources.remove(dst);
        state
            .load_sources
            .insert(dst.clone(), DataflowValue::Unknown);
        return;
    }
    state
        .load_sources
        .retain(|candidate, _| !same_x86_alias_family(candidate, dst));
    state
        .load_sources
        .insert(dst.clone(), DataflowValue::Unknown);
}

fn dataflow_copy_root_if_known(dst: &SSAVar, src: &SSAVar, state: &mut WorkerDataflowState) {
    if let Some(root) = dataflow_rooted_region(src, state) {
        insert_exact_dataflow_value(&mut state.roots, dst, root);
    }
}

fn dataflow_copy_load_source_if_known(dst: &SSAVar, src: &SSAVar, state: &mut WorkerDataflowState) {
    let source = dataflow_loaded_source(src, state);
    dataflow_kill_load_source_aliases(dst, state);
    if let Some(source) = source {
        insert_exact_dataflow_value(&mut state.load_sources, dst, source);
    }
}

fn dataflow_copy_binary_root_if_unambiguous(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    state: &mut WorkerDataflowState,
) {
    let a_root = dataflow_rooted_region(a, state);
    let b_root = dataflow_rooted_region(b, state);
    match (a_root, b_root) {
        (Some(root), None) | (None, Some(root)) => {
            insert_exact_dataflow_value(&mut state.roots, dst, root);
        }
        (Some(a_root), Some(b_root)) if a_root == b_root => {
            insert_exact_dataflow_value(&mut state.roots, dst, a_root);
        }
        _ => {}
    }
}

fn dataflow_copy_phi_root_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    state: &mut WorkerDataflowState,
) {
    let mut source_roots = sources
        .into_iter()
        .filter_map(|src| dataflow_rooted_region(src, state));
    if let Some(first) = source_roots.next()
        && source_roots.all(|root| root == first)
    {
        insert_exact_dataflow_value(&mut state.roots, dst, first);
    }
}

fn dataflow_copy_phi_load_source_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    state: &mut WorkerDataflowState,
) {
    let mut source_roots = sources
        .into_iter()
        .filter_map(|src| dataflow_loaded_source(src, state));
    let source = if let Some(first) = source_roots.next()
        && source_roots.all(|root| root == first)
    {
        Some(first)
    } else {
        None
    };
    dataflow_kill_load_source_aliases(dst, state);
    if let Some(first) = source {
        insert_exact_dataflow_value(&mut state.load_sources, dst, first);
    }
}

fn dataflow_insert_transformed_load_source(
    dst: &SSAVar,
    source: LoadedSource,
    delta: i64,
    state: &mut WorkerDataflowState,
) {
    let source = dataflow_transformed_load_source(source, delta, dst.size);
    dataflow_kill_load_source_aliases(dst, state);
    insert_exact_dataflow_value(&mut state.load_sources, dst, source);
}

fn dataflow_transformed_load_source(
    source: LoadedSource,
    delta: i64,
    dst_size: u32,
) -> LoadedSource {
    LoadedSource {
        location: source.location,
        size: dst_size,
        block_addr: source.block_addr,
        value_delta: source.value_delta.saturating_add(delta),
    }
}

fn const_i64(var: &SSAVar) -> Option<i64> {
    const_value(var).and_then(|value| i64::try_from(value).ok())
}

fn dataflow_copy_additive_load_source(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    subtract_rhs: bool,
    state: &mut WorkerDataflowState,
) {
    let a_source = dataflow_loaded_source(a, state);
    let b_source = dataflow_loaded_source(b, state);
    match (a_source, const_i64(b), b_source, const_i64(a)) {
        (Some(source), Some(delta), None, _) => {
            let delta = if subtract_rhs { -delta } else { delta };
            dataflow_insert_transformed_load_source(dst, source, delta, state);
        }
        (None, _, Some(source), Some(delta)) if !subtract_rhs => {
            dataflow_insert_transformed_load_source(dst, source, delta, state);
        }
        _ => dataflow_kill_load_source_aliases(dst, state),
    }
}

fn dataflow_copy_binary_load_source_if_unambiguous(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    state: &mut WorkerDataflowState,
) {
    let a_source = dataflow_loaded_source(a, state);
    let b_source = dataflow_loaded_source(b, state);
    let source = match (a_source, b_source) {
        (Some(source), None) | (None, Some(source)) => Some(source),
        (Some(a_source), Some(b_source)) if a_source == b_source => Some(a_source),
        _ => None,
    };
    dataflow_kill_load_source_aliases(dst, state);
    if let Some(source) = source {
        insert_exact_dataflow_value(&mut state.load_sources, dst, source);
    }
}

fn copy_load_source_if_known(
    dst: &SSAVar,
    src: &SSAVar,
    load_sources: &mut BTreeMap<SSAVar, LoadedSource>,
) {
    if let Some(source) = loaded_source(src, load_sources) {
        load_sources.insert(dst.clone(), source);
    }
}

fn copy_binary_load_source_if_unambiguous(
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    load_sources: &mut BTreeMap<SSAVar, LoadedSource>,
) {
    let a_source = loaded_source(a, load_sources);
    let b_source = loaded_source(b, load_sources);
    match (a_source, b_source) {
        (Some(source), None) | (None, Some(source)) => {
            load_sources.insert(dst.clone(), source);
        }
        (Some(a_source), Some(b_source)) if a_source.location == b_source.location => {
            load_sources.insert(dst.clone(), a_source);
        }
        _ => {}
    }
}

fn copy_phi_load_source_if_unambiguous<'a>(
    dst: &SSAVar,
    sources: impl IntoIterator<Item = &'a SSAVar>,
    load_sources: &mut BTreeMap<SSAVar, LoadedSource>,
) {
    let mut source_roots = sources
        .into_iter()
        .filter_map(|src| loaded_source(src, load_sources));
    if let Some(first) = source_roots.next()
        && source_roots.all(|root| root.location == first.location)
    {
        load_sources.insert(dst.clone(), first);
    }
}

pub(super) fn large_cfg_memory_transfers(func: &SsaArtifact) -> BTreeSet<LargeCfgMemoryTransfer> {
    let mut roots = BTreeMap::<SSAVar, SummaryMemoryRegion>::new();
    let mut load_sources = BTreeMap::<SSAVar, LoadedSource>::new();
    let mut transfers = BTreeSet::<LargeCfgMemoryTransfer>::new();

    for block in func.function().blocks() {
        for phi in &block.phis {
            copy_phi_root_if_unambiguous(
                &phi.dst,
                phi.sources.iter().map(|(_, src)| src),
                &mut roots,
            );
            copy_phi_load_source_if_unambiguous(
                &phi.dst,
                phi.sources.iter().map(|(_, src)| src),
                &mut load_sources,
            );
        }

        for op in &block.ops {
            match op {
                SSAOp::Phi { dst, sources } => {
                    copy_phi_root_if_unambiguous(dst, sources, &mut roots);
                    copy_phi_load_source_if_unambiguous(dst, sources, &mut load_sources);
                }
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Subpiece { dst, src, .. }
                | SSAOp::Cast { dst, src }
                | SSAOp::Trunc { dst, src } => {
                    copy_root_if_known(dst, src, &mut roots);
                    copy_load_source_if_known(dst, src, &mut load_sources);
                }
                SSAOp::IntAdd { dst, a, b }
                | SSAOp::IntSub { dst, a, b }
                | SSAOp::IntAnd { dst, a, b }
                | SSAOp::IntOr { dst, a, b }
                | SSAOp::PtrAdd {
                    dst,
                    base: a,
                    index: b,
                    ..
                }
                | SSAOp::PtrSub {
                    dst,
                    base: a,
                    index: b,
                    ..
                } => {
                    copy_binary_root_if_unambiguous(dst, a, b, &mut roots);
                    if matches!(op, SSAOp::IntAnd { .. }) {
                        copy_binary_load_source_if_unambiguous(dst, a, b, &mut load_sources);
                    }
                }
                SSAOp::Load { dst, addr, .. }
                | SSAOp::LoadLinked { dst, addr, .. }
                | SSAOp::LoadGuarded { dst, addr, .. } => {
                    if let Some(region) = rooted_region(addr, &roots) {
                        load_sources.insert(
                            dst.clone(),
                            LoadedSource {
                                location: location_from_region(region, dst.size),
                                size: dst.size,
                                block_addr: block.addr,
                                value_delta: 0,
                            },
                        );
                    }
                }
                SSAOp::Store { addr, val, .. }
                | SSAOp::StoreGuarded { addr, val, .. }
                | SSAOp::StoreConditional { addr, val, .. } => {
                    if let (Some(dst_arg), Some(src_arg)) = (
                        rooted_arg_var(addr, &roots),
                        loaded_source(val, &load_sources).and_then(|source| {
                            match source.location.region {
                                SummaryMemoryRegion::Arg { index } => Some(index),
                                SummaryMemoryRegion::Global { .. }
                                | SummaryMemoryRegion::HeapReturn
                                | SummaryMemoryRegion::Unknown => None,
                            }
                        }),
                    ) && dst_arg != src_arg
                    {
                        transfers.insert(LargeCfgMemoryTransfer {
                            block_addr: block.addr,
                            dst_arg,
                            src_arg,
                            size: val.size,
                        });
                    }
                }
                _ => {}
            }
        }
    }

    transfers
}

pub(super) fn summary_for_transfer(transfer: LargeCfgMemoryTransfer) -> NativeWorkerSummary {
    transfer_worker_summary(
        transfer.block_addr,
        SummaryTransferEffect {
            dst: SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg {
                    index: transfer.dst_arg,
                },
                range: Some(SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 0,
                    width: Some(transfer.size),
                }),
            },
            src: SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg {
                    index: transfer.src_arg,
                },
                range: Some(SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 0,
                    width: Some(transfer.size),
                }),
            },
            len: SummaryTransferLength::Unknown,
        },
    )
}

fn loop_exit_target(func: &SsaArtifact, header: u64) -> Option<u64> {
    func.function()
        .successors(header)
        .into_iter()
        .find(|target| *target > header)
        .or_else(|| {
            func.function()
                .successors(header)
                .into_iter()
                .find(|target| *target != header)
        })
}

fn loop_summary(
    func: &SsaArtifact,
    header: u64,
    terminator: NativeWorkerTerminator,
    fold: Option<NativeWorkerFold>,
) -> NativeWorkerLoopSummary {
    NativeWorkerLoopSummary {
        header,
        exit_target: loop_exit_target(func, header),
        iterations: None,
        length_arg: None,
        stride: Some(1),
        terminator: Some(terminator),
        fold,
    }
}

fn loop_summary_from_island(
    island: &LoopIsland,
    terminator: NativeWorkerTerminator,
    fold: Option<NativeWorkerFold>,
    length_arg: Option<usize>,
) -> NativeWorkerLoopSummary {
    NativeWorkerLoopSummary {
        header: island.header,
        exit_target: island.exits.iter().copied().next(),
        iterations: None,
        length_arg,
        stride: Some(1),
        terminator: Some(terminator),
        fold,
    }
}

fn collect_natural_loop_islands(func: &SsaArtifact) -> BTreeMap<u64, LoopIsland> {
    let function = func.function();
    let mut islands = BTreeMap::<u64, LoopIsland>::new();
    for &block in function.block_addrs() {
        for succ in function.successors(block) {
            if !function.dominates(succ, block) {
                continue;
            }
            let island = islands.entry(succ).or_insert_with(|| LoopIsland {
                header: succ,
                body: BTreeSet::from([succ]),
                entries: BTreeSet::new(),
                exits: BTreeSet::new(),
            });
            island.body.insert(block);
            let mut stack = vec![block];
            while let Some(current) = stack.pop() {
                for pred in function.predecessors(current) {
                    if island.body.insert(pred) && pred != succ {
                        stack.push(pred);
                    }
                }
            }
        }
    }

    for island in islands.values_mut() {
        for block in island.body.clone() {
            for pred in function.predecessors(block) {
                if !island.body.contains(&pred) {
                    island.entries.insert(block);
                }
            }
            for succ in function.successors(block) {
                if !island.body.contains(&succ) {
                    island.exits.insert(succ);
                }
            }
        }
        if island.entries.is_empty() {
            island.entries.insert(island.header);
        }
    }
    islands
}

fn loop_island_for_anchor(islands: &BTreeMap<u64, LoopIsland>, anchor: u64) -> Option<&LoopIsland> {
    islands
        .values()
        .filter(|island| island.body.contains(&anchor))
        .min_by_key(|island| (island.body.len(), island.header))
}

fn singleton_island(func: &SsaArtifact, anchor: u64) -> LoopIsland {
    let mut entries = BTreeSet::new();
    entries.insert(anchor);
    LoopIsland {
        header: anchor,
        body: BTreeSet::from([anchor]),
        entries,
        exits: func.function().successors(anchor).into_iter().collect(),
    }
}

fn native_loop_summary_from_worker(
    worker: &NativeWorkerSummary,
    island: &LoopIsland,
) -> Option<NativeLoopSummary> {
    let worker_loop = worker.loop_summary.as_ref()?;
    Some(NativeLoopSummary {
        header: worker_loop.header,
        body: island.body.clone(),
        entries: island.entries.clone(),
        exits: island.exits.clone(),
        iterations: worker_loop.iterations,
        length_arg: worker_loop.length_arg,
        stride: worker_loop.stride,
        terminator: worker_loop.terminator,
    })
}

fn location_width(location: Option<SummaryMemoryLocation>) -> Option<u32> {
    location
        .and_then(|location| location.range)
        .and_then(|range| range.width)
}

fn memory_access_kind(kind: NativeWorkerSummaryKind) -> NativeMemoryAccessKind {
    match kind {
        NativeWorkerSummaryKind::MemoryTransfer => NativeMemoryAccessKind::Transfer,
        NativeWorkerSummaryKind::MemoryRead
        | NativeWorkerSummaryKind::StringScan
        | NativeWorkerSummaryKind::HashFold
        | NativeWorkerSummaryKind::TableWalk
        | NativeWorkerSummaryKind::Parser => NativeMemoryAccessKind::Read,
        NativeWorkerSummaryKind::MemoryWrite => NativeMemoryAccessKind::Write,
        NativeWorkerSummaryKind::MemoryEscape => NativeMemoryAccessKind::Escape,
        NativeWorkerSummaryKind::MemoryFree => NativeMemoryAccessKind::Free,
        NativeWorkerSummaryKind::Allocation => NativeMemoryAccessKind::Allocation,
        NativeWorkerSummaryKind::Lifetime => NativeMemoryAccessKind::Lifetime,
        NativeWorkerSummaryKind::Synchronization => NativeMemoryAccessKind::Synchronization,
        NativeWorkerSummaryKind::Atomic => NativeMemoryAccessKind::Atomic,
        NativeWorkerSummaryKind::Unknown => NativeMemoryAccessKind::Unknown,
    }
}

fn memory_accesses_from_worker(worker: &NativeWorkerSummary) -> Vec<NativeMemoryAccessSummary> {
    let mut accesses = Vec::new();
    if worker.memory.is_some()
        || worker.dst.is_some()
        || worker.src.is_some()
        || worker.len.is_some()
    {
        accesses.push(NativeMemoryAccessSummary {
            kind: memory_access_kind(worker.kind),
            location: worker.memory,
            dst: worker.dst,
            src: worker.src,
            len: worker.len,
            width: location_width(worker.memory)
                .or_else(|| location_width(worker.dst))
                .or_else(|| location_width(worker.src)),
        });
    }
    if let Some(effect) = worker.allocation {
        accesses.push(NativeMemoryAccessSummary {
            kind: NativeMemoryAccessKind::Allocation,
            location: None,
            dst: None,
            src: None,
            len: effect.size_arg.map(SummaryTransferLength::Arg),
            width: None,
        });
    }
    if let Some(effect) = worker.lifetime {
        accesses.push(NativeMemoryAccessSummary {
            kind: NativeMemoryAccessKind::Lifetime,
            location: Some(SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: effect.arg },
                range: None,
            }),
            dst: None,
            src: None,
            len: None,
            width: None,
        });
    }
    if let Some(effect) = worker.sync {
        accesses.push(NativeMemoryAccessSummary {
            kind: NativeMemoryAccessKind::Synchronization,
            location: Some(SummaryMemoryLocation {
                region: SummaryMemoryRegion::Arg { index: effect.arg },
                range: None,
            }),
            dst: None,
            src: None,
            len: None,
            width: None,
        });
    }
    if let Some(effect) = worker.atomic {
        accesses.push(NativeMemoryAccessSummary {
            kind: NativeMemoryAccessKind::Atomic,
            location: Some(effect.location),
            dst: None,
            src: None,
            len: None,
            width: location_width(Some(effect.location)),
        });
    }
    accesses.sort();
    accesses.dedup();
    accesses
}

fn reductions_from_worker(worker: &NativeWorkerSummary) -> Vec<NativeReductionSummary> {
    worker
        .loop_summary
        .as_ref()
        .and_then(|loop_summary| loop_summary.fold.as_ref())
        .map(|fold| NativeReductionSummary {
            accumulator: fold.accumulator.clone(),
            bits: fold.bits,
            operation: fold.operation,
            source: worker.memory.or(worker.src),
        })
        .into_iter()
        .collect()
}

fn region_summary_from_worker(
    func: &SsaArtifact,
    islands: &BTreeMap<u64, LoopIsland>,
    worker: NativeWorkerSummary,
) -> NativeRegionSummary {
    let island = loop_island_for_anchor(islands, worker.anchor)
        .cloned()
        .unwrap_or_else(|| singleton_island(func, worker.anchor));
    let loop_summary = native_loop_summary_from_worker(&worker, &island);
    let blocks = loop_summary
        .as_ref()
        .map(|summary| summary.body.clone())
        .unwrap_or_else(|| island.body.clone());
    let residual_reasons = worker
        .evidence
        .budget_limited
        .then_some(ResidualReason::LargeCfg)
        .into_iter()
        .collect();
    NativeRegionSummary {
        stable_id: stable_region_summary_id(worker.anchor, worker.kind, &blocks),
        anchor: worker.anchor,
        kind: worker.kind,
        blocks,
        entries: island.entries,
        exits: island.exits,
        memory_accesses: memory_accesses_from_worker(&worker),
        loop_summary,
        reductions: reductions_from_worker(&worker),
        parser: worker.parser.clone(),
        residual_reasons,
        confidence: worker.evidence.tier,
        evidence: worker.evidence,
    }
}

pub(super) fn classify_native_region_summaries(
    func: &SsaArtifact,
    worker_summaries: &[NativeWorkerSummary],
) -> Vec<NativeRegionSummary> {
    let islands = collect_natural_loop_islands(func);
    canonical_region_summaries(
        worker_summaries
            .iter()
            .cloned()
            .map(|worker| region_summary_from_worker(func, &islands, worker))
            .collect(),
    )
}

fn source_arg(source: LoadedSource) -> Option<usize> {
    match source.location.region {
        SummaryMemoryRegion::Arg { index } => Some(index),
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => None,
    }
}

fn dataflow_loaded_compare<'a>(
    a: &'a SSAVar,
    b: &'a SSAVar,
    state: &WorkerDataflowState,
) -> Option<(LoadedSource, &'a SSAVar)> {
    dataflow_loaded_source(a, state)
        .map(|source| (source, b))
        .or_else(|| dataflow_loaded_source(b, state).map(|source| (source, a)))
}

fn dataflow_loaded_binary_source(
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<(LoadedSource, String)> {
    dataflow_loaded_source(a, state)
        .map(|source| (source, b.display_name()))
        .or_else(|| dataflow_loaded_source(b, state).map(|source| (source, a.display_name())))
}

fn merge_parser_byte_value(
    observations: &mut BlockWorkerObservations,
    arg: usize,
    anchor: u64,
    value: u8,
) {
    let evidence = observations
        .parser_comparisons
        .entry(arg)
        .or_insert_with(|| ParserLoopEvidence {
            anchor,
            ..ParserLoopEvidence::default()
        });
    evidence.anchor = evidence.anchor.min(anchor);
    evidence.byte_values.insert(value);
    if matches!(value, b'+' | b'-') {
        evidence.accepts_sign = true;
    }
}

fn merge_parser_byte_range(
    observations: &mut BlockWorkerObservations,
    arg: usize,
    anchor: u64,
    range: ParserByteRange,
) {
    let evidence = observations
        .parser_comparisons
        .entry(arg)
        .or_insert_with(|| ParserLoopEvidence {
            anchor,
            ..ParserLoopEvidence::default()
        });
    evidence.anchor = evidence.anchor.min(anchor);
    evidence.byte_ranges.insert(range);
}

fn byte_range_from_upper_bound(
    source: LoadedSource,
    inclusive_upper: i64,
) -> Option<ParserByteRange> {
    if source.value_delta == -i64::from(b'0') && inclusive_upper == 9 {
        return Some(ParserByteRange { lo: b'0', hi: b'9' });
    }
    let hi = inclusive_upper.saturating_sub(source.value_delta);
    if !(0..=255).contains(&hi) {
        return None;
    }
    Some(ParserByteRange {
        lo: 0,
        hi: hi as u8,
    })
}

fn byte_range_from_lower_bound(
    source: LoadedSource,
    inclusive_lower: i64,
) -> Option<ParserByteRange> {
    let lo = inclusive_lower.saturating_sub(source.value_delta);
    if !(0..=255).contains(&lo) {
        return None;
    }
    Some(ParserByteRange {
        lo: lo as u8,
        hi: u8::MAX,
    })
}

fn record_parser_range_compare(
    observations: &mut BlockWorkerObservations,
    block_addr: u64,
    source: LoadedSource,
    other: &SSAVar,
    source_on_left: bool,
    less_equal: bool,
) {
    let Some(arg) = source_arg(source) else {
        return;
    };
    let Some(raw_bound) = const_i64(other) else {
        return;
    };
    let range = if source_on_left {
        let upper = if less_equal {
            raw_bound
        } else {
            raw_bound.saturating_sub(1)
        };
        byte_range_from_upper_bound(source, upper)
    } else {
        let lower = if less_equal {
            raw_bound
        } else {
            raw_bound.saturating_add(1)
        };
        byte_range_from_lower_bound(source, lower)
    };
    if let Some(range) = range {
        merge_parser_byte_range(observations, arg, block_addr, range);
    }
}

fn scan_summary(
    func: &SsaArtifact,
    anchor: u64,
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummary {
    let kind = match (source.location.region, terminator) {
        (SummaryMemoryRegion::Global { .. }, _) => NativeWorkerSummaryKind::TableWalk,
        (_, NativeWorkerTerminator::ZeroByte) => NativeWorkerSummaryKind::StringScan,
        _ => NativeWorkerSummaryKind::MemoryRead,
    };
    NativeWorkerSummary {
        anchor,
        kind,
        dst: None,
        src: None,
        memory: Some(source.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(loop_summary(func, anchor, terminator, None)),
        evidence: bounded_evidence(),
    }
}

fn scan_summary_for_island(
    island: &LoopIsland,
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummary {
    let kind = match (source.location.region, terminator) {
        (SummaryMemoryRegion::Global { .. }, _) => NativeWorkerSummaryKind::TableWalk,
        (_, NativeWorkerTerminator::ZeroByte) => NativeWorkerSummaryKind::StringScan,
        _ => NativeWorkerSummaryKind::MemoryRead,
    };
    NativeWorkerSummary {
        anchor: island.header,
        kind,
        dst: None,
        src: None,
        memory: Some(source.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(loop_summary_from_island(island, terminator, None, None)),
        evidence: bounded_evidence(),
    }
}

fn hash_fold_summary(
    func: &SsaArtifact,
    anchor: u64,
    source: LoadedSource,
    accumulator: String,
    operation: NativeWorkerFoldOperation,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::HashFold,
        dst: None,
        src: None,
        memory: Some(source.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(loop_summary(
            func,
            anchor,
            NativeWorkerTerminator::Unknown,
            Some(NativeWorkerFold {
                accumulator,
                bits: source.size.saturating_mul(8),
                operation,
            }),
        )),
        evidence: bounded_evidence(),
    }
}

fn hash_fold_summary_for_island(
    island: &LoopIsland,
    source: LoadedSource,
    accumulator: String,
    operation: NativeWorkerFoldOperation,
) -> NativeWorkerSummary {
    let fold = NativeWorkerFold {
        accumulator,
        bits: source.size.saturating_mul(8),
        operation,
    };
    NativeWorkerSummary {
        anchor: island.header,
        kind: NativeWorkerSummaryKind::HashFold,
        dst: None,
        src: None,
        memory: Some(source.location),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(loop_summary_from_island(
            island,
            NativeWorkerTerminator::Unknown,
            Some(fold),
            None,
        )),
        evidence: bounded_evidence(),
    }
}

fn parser_summary(
    func: &SsaArtifact,
    anchor: u64,
    arg: usize,
    parser: NativeParserSummary,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: None,
        src: None,
        memory: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: arg },
            range: Some(SummaryMemoryRange {
                offset_lo: 0,
                offset_hi: 0,
                width: Some(1),
            }),
        }),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(parser),
        loop_summary: Some(loop_summary(
            func,
            anchor,
            NativeWorkerTerminator::Unknown,
            None,
        )),
        evidence: bounded_evidence(),
    }
}

fn parser_summary_for_island(
    island: &LoopIsland,
    arg: usize,
    parser: NativeParserSummary,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor: island.header,
        kind: NativeWorkerSummaryKind::Parser,
        dst: None,
        src: None,
        memory: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: arg },
            range: Some(SummaryMemoryRange {
                offset_lo: 0,
                offset_hi: 0,
                width: Some(1),
            }),
        }),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(parser),
        loop_summary: Some(loop_summary_from_island(
            island,
            NativeWorkerTerminator::Unknown,
            None,
            None,
        )),
        evidence: bounded_evidence(),
    }
}

fn transfer_worker_block(
    block: &r2ssa::function::SSABlock,
    input: &WorkerDataflowState,
    mut observations: Option<&mut BlockWorkerObservations>,
) -> WorkerDataflowState {
    let mut state = input.clone();
    for phi in &block.phis {
        dataflow_copy_phi_root_if_unambiguous(
            &phi.dst,
            phi.sources.iter().map(|(_, src)| src),
            &mut state,
        );
        dataflow_copy_phi_load_source_if_unambiguous(
            &phi.dst,
            phi.sources.iter().map(|(_, src)| src),
            &mut state,
        );
    }

    for op in &block.ops {
        match op {
            SSAOp::Phi { dst, sources } => {
                dataflow_copy_phi_root_if_unambiguous(dst, sources, &mut state);
                dataflow_copy_phi_load_source_if_unambiguous(dst, sources, &mut state);
            }
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Subpiece { dst, src, .. }
            | SSAOp::Cast { dst, src }
            | SSAOp::Trunc { dst, src } => {
                dataflow_copy_root_if_known(dst, src, &mut state);
                dataflow_copy_load_source_if_known(dst, src, &mut state);
            }
            SSAOp::IntAdd { dst, a, b }
            | SSAOp::PtrAdd {
                dst,
                base: a,
                index: b,
                ..
            } => {
                dataflow_copy_binary_root_if_unambiguous(dst, a, b, &mut state);
                if let Some(observations) = observations.as_deref_mut()
                    && let Some((source, accumulator)) = dataflow_loaded_binary_source(a, b, &state)
                {
                    observations.folds.push(FoldObservation {
                        anchor: block.addr,
                        source,
                        accumulator,
                        operation: NativeWorkerFoldOperation::Add,
                    });
                }
                dataflow_copy_additive_load_source(dst, a, b, false, &mut state);
            }
            SSAOp::IntSub { dst, a, b }
            | SSAOp::PtrSub {
                dst,
                base: a,
                index: b,
                ..
            } => {
                dataflow_copy_binary_root_if_unambiguous(dst, a, b, &mut state);
                dataflow_copy_additive_load_source(dst, a, b, true, &mut state);
            }
            SSAOp::IntAnd { dst, a, b } | SSAOp::IntOr { dst, a, b } => {
                dataflow_copy_binary_root_if_unambiguous(dst, a, b, &mut state);
                dataflow_copy_binary_load_source_if_unambiguous(dst, a, b, &mut state);
            }
            SSAOp::IntXor { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some((source, accumulator)) = dataflow_loaded_binary_source(a, b, &state)
                {
                    observations.folds.push(FoldObservation {
                        anchor: block.addr,
                        source,
                        accumulator,
                        operation: NativeWorkerFoldOperation::Xor,
                    });
                }
                dataflow_copy_binary_load_source_if_unambiguous(dst, a, b, &mut state);
            }
            SSAOp::IntLeft { dst, a, b }
            | SSAOp::IntRight { dst, a, b }
            | SSAOp::IntSRight { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some((source, accumulator)) = dataflow_loaded_binary_source(a, b, &state)
                {
                    observations.folds.push(FoldObservation {
                        anchor: block.addr,
                        source,
                        accumulator,
                        operation: NativeWorkerFoldOperation::RotateMix,
                    });
                }
                dataflow_copy_binary_load_source_if_unambiguous(dst, a, b, &mut state);
            }
            SSAOp::IntEqual { dst, a, b } | SSAOp::IntNotEqual { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some((source, other)) = dataflow_loaded_compare(a, b, &state)
                {
                    let terminator = const_value(other)
                        .map(|value| {
                            if value == 0 {
                                NativeWorkerTerminator::ZeroByte
                            } else {
                                NativeWorkerTerminator::ByteEquals((value & 0xff) as u8)
                            }
                        })
                        .unwrap_or(NativeWorkerTerminator::Unknown);
                    if let Some(arg) = source_arg(source)
                        && let Some(value) = const_value(other).filter(|value| *value <= 0xff)
                    {
                        merge_parser_byte_value(observations, arg, block.addr, value as u8);
                    }
                    observations.scans.push(ScanObservation {
                        anchor: block.addr,
                        source,
                        terminator,
                    });
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
            }
            SSAOp::IntLess { dst, a, b } | SSAOp::IntSLess { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut() {
                    if let Some(source) = dataflow_loaded_source(a, &state) {
                        record_parser_range_compare(
                            observations,
                            block.addr,
                            source,
                            b,
                            true,
                            false,
                        );
                    }
                    if let Some(source) = dataflow_loaded_source(b, &state) {
                        record_parser_range_compare(
                            observations,
                            block.addr,
                            source,
                            a,
                            false,
                            false,
                        );
                    }
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
            }
            SSAOp::IntLessEqual { dst, a, b } | SSAOp::IntSLessEqual { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut() {
                    if let Some(source) = dataflow_loaded_source(a, &state) {
                        record_parser_range_compare(
                            observations,
                            block.addr,
                            source,
                            b,
                            true,
                            true,
                        );
                    }
                    if let Some(source) = dataflow_loaded_source(b, &state) {
                        record_parser_range_compare(
                            observations,
                            block.addr,
                            source,
                            a,
                            false,
                            true,
                        );
                    }
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
            }
            SSAOp::Load { dst, addr, .. }
            | SSAOp::LoadLinked { dst, addr, .. }
            | SSAOp::LoadGuarded { dst, addr, .. } => {
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(region) = dataflow_rooted_region(addr, &state) {
                    insert_exact_dataflow_value(
                        &mut state.load_sources,
                        dst,
                        LoadedSource {
                            location: location_from_region(region, dst.size),
                            size: dst.size,
                            block_addr: block.addr,
                            value_delta: 0,
                        },
                    );
                }
            }
            _ => {
                if let Some(dst) = op.dst() {
                    dataflow_kill_load_source_aliases(dst, &mut state);
                }
            }
        }
    }
    state
}

fn compute_worker_dataflow_inputs(func: &SsaArtifact) -> BTreeMap<u64, WorkerDataflowState> {
    let function = func.function();
    let block_addrs = function.block_addrs();
    let mut inputs = BTreeMap::<u64, WorkerDataflowState>::new();
    let mut outputs = BTreeMap::<u64, WorkerDataflowState>::new();
    let mut changed = true;

    while changed {
        changed = false;
        for block_addr in block_addrs {
            let mut input = WorkerDataflowState::default();
            for pred in function.predecessors(*block_addr) {
                if let Some(pred_output) = outputs.get(&pred) {
                    let _ = join_worker_state(&mut input, pred_output);
                }
            }
            if inputs.get(block_addr) != Some(&input) {
                inputs.insert(*block_addr, input.clone());
                changed = true;
            }
            let Some(block) = function.get_block(*block_addr) else {
                continue;
            };
            let output = transfer_worker_block(block, &input, None);
            if outputs.get(block_addr) != Some(&output) {
                outputs.insert(*block_addr, output);
                changed = true;
            }
        }
    }

    inputs
}

fn collect_block_worker_observations(func: &SsaArtifact) -> BTreeMap<u64, BlockWorkerObservations> {
    let inputs = compute_worker_dataflow_inputs(func);
    let mut observations = BTreeMap::new();
    for block in func.function().blocks() {
        let input = inputs.get(&block.addr).cloned().unwrap_or_default();
        let mut block_observations = BlockWorkerObservations::default();
        let _ = transfer_worker_block(block, &input, Some(&mut block_observations));
        observations.insert(block.addr, block_observations);
    }
    observations
}

fn merge_parser_evidence(left: &mut ParserLoopEvidence, right: ParserLoopEvidence) {
    if left.anchor == 0 {
        left.anchor = right.anchor;
    } else {
        left.anchor = left.anchor.min(right.anchor);
    }
    left.byte_values.extend(right.byte_values);
    left.byte_ranges.extend(right.byte_ranges);
    left.accepts_sign |= right.accepts_sign;
}

fn loop_effect_summaries(
    func: &SsaArtifact,
    observations: BTreeMap<u64, BlockWorkerObservations>,
) -> Vec<LoopEffectSummary> {
    let islands = collect_natural_loop_islands(func);
    let mut summaries = BTreeMap::<u64, LoopEffectSummary>::new();
    for (block_addr, block_observations) in observations {
        let (island, natural_loop) = loop_island_for_anchor(&islands, block_addr)
            .cloned()
            .map(|island| (island, true))
            .unwrap_or_else(|| (singleton_island(func, block_addr), false));
        let summary = summaries
            .entry(island.header)
            .or_insert_with(|| LoopEffectSummary {
                island,
                natural_loop,
                ..LoopEffectSummary::default()
            });
        summary.scans.extend(block_observations.scans);
        summary.folds.extend(block_observations.folds);
        for (arg, evidence) in block_observations.parser_comparisons {
            merge_parser_evidence(summary.parser_comparisons.entry(arg).or_default(), evidence);
        }
    }
    summaries.into_values().collect()
}

fn parser_summary_from_evidence(
    arg: usize,
    evidence: &ParserLoopEvidence,
) -> Option<NativeParserSummary> {
    let numeric_range = evidence
        .byte_ranges
        .iter()
        .any(|range| range.lo <= b'0' && range.hi >= b'9');
    let digit_values = evidence
        .byte_values
        .iter()
        .filter(|value| value.is_ascii_digit())
        .count();
    let kind = if numeric_range || digit_values >= 2 {
        NativeParserKind::Numeric
    } else if evidence.byte_values.len() >= 4 {
        NativeParserKind::Token
    } else {
        return None;
    };
    Some(NativeParserSummary {
        kind,
        cursor_arg: Some(arg),
        base: matches!(kind, NativeParserKind::Numeric).then_some(10),
        digit_min: matches!(kind, NativeParserKind::Numeric).then_some(b'0'),
        digit_max: matches!(kind, NativeParserKind::Numeric).then_some(b'9'),
        accepts_sign: evidence.accepts_sign,
    })
}

fn summaries_from_loop_effects(func: &SsaArtifact) -> Vec<NativeWorkerSummary> {
    let observations = collect_block_worker_observations(func);
    let mut summaries = Vec::<NativeWorkerSummary>::new();
    for effect in loop_effect_summaries(func, observations) {
        let mut seen_scans = BTreeSet::new();
        for scan in effect.scans {
            if seen_scans.insert((scan.source.location, scan.terminator)) {
                if effect.natural_loop {
                    summaries.push(scan_summary_for_island(
                        &effect.island,
                        scan.source,
                        scan.terminator,
                    ));
                } else {
                    summaries.push(scan_summary(
                        func,
                        scan.anchor,
                        scan.source,
                        scan.terminator,
                    ));
                }
            }
        }

        let mut seen_folds = BTreeSet::new();
        for fold in effect.folds {
            if seen_folds.insert((
                fold.source.location,
                fold.accumulator.clone(),
                fold.operation,
            )) {
                if effect.natural_loop {
                    summaries.push(hash_fold_summary_for_island(
                        &effect.island,
                        fold.source,
                        fold.accumulator,
                        fold.operation,
                    ));
                } else {
                    summaries.push(hash_fold_summary(
                        func,
                        fold.anchor,
                        fold.source,
                        fold.accumulator,
                        fold.operation,
                    ));
                }
            }
        }

        if effect.natural_loop {
            for (arg, evidence) in &effect.parser_comparisons {
                if let Some(parser) = parser_summary_from_evidence(*arg, evidence) {
                    summaries.push(parser_summary_for_island(&effect.island, *arg, parser));
                }
            }
        } else if has_loopish_or_dispatch_control(func) {
            for (arg, evidence) in &effect.parser_comparisons {
                if let Some(parser) = parser_summary_from_evidence(*arg, evidence) {
                    summaries.push(parser_summary(func, evidence.anchor, *arg, parser));
                }
            }
        }
    }
    summaries
}

fn has_loopish_or_dispatch_control(func: &SsaArtifact) -> bool {
    let risk = func.function().cfg_risk_summary();
    risk.loop_count > 0
        || risk.back_edge_count > 0
        || risk.switch_block_count > 0
        || risk.block_count >= 16
}

pub(super) fn classify_function_worker_summaries_unbounded(
    func: &SsaArtifact,
) -> Vec<NativeWorkerSummary> {
    summaries_from_loop_effects(func)
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    use super::*;

    fn aarch64_test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0x00, 8));
        arch.add_register(RegisterDef::new("x1", 0x08, 8));
        arch
    }

    fn x86_64_alias_test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0x00, 8));
        arch.add_register(RegisterDef::new("EAX", 0x00, 4));
        arch.add_register(RegisterDef::new("AX", 0x00, 2));
        arch.add_register(RegisterDef::new("AL", 0x00, 1));
        arch.add_register(RegisterDef::new("RDI", 0x20, 8));
        arch
    }

    #[test]
    fn classifier_detects_zero_terminated_string_scan() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x10, 1);
        let pred = Varnode::unique(0x11, 1);
        let mut block = R2ILBlock::new(0x4000, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred,
            a: loaded,
            b: Varnode::constant(0, 1),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("string scan SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::StringScan)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && summary
                    .loop_summary
                    .as_ref()
                    .and_then(|loop_summary| loop_summary.terminator)
                    == Some(NativeWorkerTerminator::ZeroByte)
        }));
    }

    #[test]
    fn classifier_detects_byte_hash_fold() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x20, 1);
        let acc = Varnode::unique(0x21, 8);
        let mut block = R2ILBlock::new(0x4010, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: acc.clone(),
            src: loaded,
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x22, 8),
            a: Varnode::register(0x08, 8),
            b: acc,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("hash fold SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::HashFold)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && summary
                    .loop_summary
                    .as_ref()
                    .and_then(|loop_summary| loop_summary.fold.as_ref())
                    .is_some_and(|fold| {
                        fold.operation == NativeWorkerFoldOperation::Add && fold.bits == 8
                    })
        }));
    }

    #[test]
    fn classifier_detects_numeric_parser_loop_from_digit_range() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x40, 1);
        let wide = Varnode::unique(0x41, 8);
        let digit = Varnode::unique(0x42, 8);
        let pred = Varnode::unique(0x43, 1);
        let mut block = R2ILBlock::new(0x4040, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: wide.clone(),
            src: loaded,
        });
        block.push(R2ILOp::IntSub {
            dst: digit.clone(),
            a: wide,
            b: Varnode::constant(u64::from(b'0'), 8),
        });
        block.push(R2ILOp::IntLessEqual {
            dst: pred.clone(),
            a: digit,
            b: Varnode::constant(9, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4040, 8),
            cond: pred,
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("numeric parser SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let parser = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
            .and_then(|summary| summary.parser.as_ref())
            .expect("numeric parser summary");
        assert_eq!(parser.kind, NativeParserKind::Numeric);
        assert_eq!(parser.cursor_arg, Some(0));
        assert_eq!(parser.base, Some(10));
        assert_eq!(parser.digit_min, Some(b'0'));
        assert_eq!(parser.digit_max, Some(b'9'));
    }

    #[test]
    fn classifier_detects_numeric_parser_through_x86_full_to_low_alias() {
        let arch = x86_64_alias_test_arch();
        let wide = Varnode::unique(0x50, 8);
        let digit = Varnode::unique(0x51, 8);
        let pred = Varnode::unique(0x52, 1);
        let mut block = R2ILBlock::new(0x4050, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::register(0x00, 4),
            space: SpaceId::Ram,
            addr: Varnode::register(0x20, 8),
        });
        block.push(R2ILOp::IntZExt {
            dst: wide.clone(),
            src: Varnode::register(0x00, 1),
        });
        block.push(R2ILOp::IntSub {
            dst: digit.clone(),
            a: wide,
            b: Varnode::constant(u64::from(b'0'), 8),
        });
        block.push(R2ILOp::IntLessEqual {
            dst: pred.clone(),
            a: digit,
            b: Varnode::constant(9, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4050, 8),
            cond: pred,
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("x86 numeric parser SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let parser = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
            .and_then(|summary| summary.parser.as_ref())
            .expect("numeric parser summary through EAX/AL alias");
        assert_eq!(parser.kind, NativeParserKind::Numeric);
        assert_eq!(parser.cursor_arg, Some(0));
        assert_eq!(parser.base, Some(10));
    }

    #[test]
    fn region_summaries_preserve_loop_island_shape() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x30, 1);
        let pred = Varnode::unique(0x31, 1);
        let mut block = R2ILBlock::new(0x4020, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred.clone(),
            a: loaded,
            b: Varnode::constant(0, 1),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4020, 8),
            cond: pred,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("loop scan SSA");
        let workers =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let regions = classify_native_region_summaries(&artifact, &workers);

        assert!(regions.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::StringScan)
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.header == 0x4020 && loop_summary.body.contains(&0x4020)
                })
                && summary.arg_indices().contains(&0)
        }));
    }

    #[test]
    fn region_summaries_preserve_full_domain_beyond_worker_display_cap() {
        let arch = aarch64_test_arch();
        let block = R2ILBlock::new(0x5000, 4);
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("fixture SSA");
        let workers = (0..(NATIVE_WORKER_SUMMARY_MAX + 8))
            .map(|index| {
                memory_worker_summary(
                    0x6000 + (index as u64 * 0x10),
                    SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location: SummaryMemoryLocation {
                            region: SummaryMemoryRegion::Arg { index },
                            range: None,
                        },
                    },
                )
            })
            .collect::<Vec<_>>();

        let display_workers = bounded_worker_summaries(workers.clone());
        let regions = classify_native_region_summaries(&artifact, &workers);

        assert_eq!(display_workers.len(), NATIVE_WORKER_SUMMARY_MAX);
        assert!(
            regions.len() > display_workers.len(),
            "region summaries are canonical analysis facts and must not be capped by display workers"
        );
        assert!(regions.iter().any(|summary| {
            summary
                .arg_indices()
                .contains(&(NATIVE_WORKER_SUMMARY_MAX + 7))
        }));
    }

    #[test]
    fn region_summaries_join_memory_access_ranges() {
        let arch = aarch64_test_arch();
        let block = R2ILBlock::new(0x7000, 4);
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("range join fixture SSA");
        let workers = (0..6)
            .map(|index| {
                memory_worker_summary(
                    0x7000,
                    SummaryMemoryEffect {
                        kind: SummaryMemoryEffectKind::Read,
                        location: SummaryMemoryLocation {
                            region: SummaryMemoryRegion::Arg { index: 0 },
                            range: Some(SummaryMemoryRange {
                                offset_lo: index * 8,
                                offset_hi: index * 8 + 7,
                                width: Some(8),
                            }),
                        },
                    },
                )
            })
            .collect::<Vec<_>>();

        let regions = classify_native_region_summaries(&artifact, &workers);

        let summary = regions
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::MemoryRead))
            .expect("read summary");
        assert_eq!(summary.memory_accesses.len(), 1);
        let range = summary.memory_accesses[0]
            .location
            .and_then(|location| location.range)
            .expect("joined range");
        assert_eq!(range.offset_lo, 0);
        assert_eq!(range.offset_hi, 47);
        assert_eq!(range.width, Some(8));
    }
}
