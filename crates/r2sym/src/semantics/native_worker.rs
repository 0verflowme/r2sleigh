use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    FunctionSemanticSummary, SSAOp, SSAVar, SsaArtifact, SummaryAllocationEffect,
    SummaryAtomicEffect, SummaryLifetimeEffect, SummaryLifetimeOp, SummaryMemoryEffect,
    SummaryMemoryEffectKind, SummaryMemoryLocation, SummaryMemoryRange, SummaryMemoryRegion,
    SummaryReturnRelation, SummarySyncEffect, SummaryTransferEffect, SummaryTransferLength,
};

use crate::semantics::{
    NativeLoopSummary, NativeMemoryAccessKind, NativeMemoryAccessSummary, NativeParserKind,
    NativeParserSummary, NativeReductionSummary, NativeRegionSummary, NativeWorkerFold,
    NativeWorkerFoldOperation, NativeWorkerLoopSummary, NativeWorkerSummary,
    NativeWorkerSummaryKind, NativeWorkerTerminator, ResidualReason, SemanticEvidence,
    SemanticEvidenceAmbiguity, SemanticEvidenceCoverage, SemanticEvidenceProvenance,
    SemanticEvidenceReason,
};

mod hash;

use self::hash::{
    hash_fold_family_worker_summaries, hash_fold_summary, hash_fold_summary_for_island,
    hash_statistics_worker_summaries, hash_table_family_worker_summaries,
    hash_table_worker_summaries, is_hash_fold_family_name, is_hash_table_family_name,
    named_hash_fold_worker_summary,
};

pub(super) const NATIVE_WORKER_SUMMARY_MAX: usize = 32;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NativeWorkerSummarySortKey {
    anchor: u64,
    priority: u8,
    kind: NativeWorkerSummaryKind,
    dst: Option<SummaryMemoryLocation>,
    src: Option<SummaryMemoryLocation>,
    memory: Option<SummaryMemoryLocation>,
    len: Option<SummaryTransferLength>,
    allocation: Option<SummaryAllocationEffect>,
    lifetime: Option<SummaryLifetimeEffect>,
    sync: Option<SummarySyncEffect>,
    atomic: Option<SummaryAtomicEffect>,
    parser: Option<NativeParserSummary>,
    loop_summary: Option<NativeWorkerLoopSummary>,
}

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
type LoadSourceAliasKey = (u32, u32, u32);
type LoadSourceAliasValues = BTreeMap<LoadSourceAliasKey, DataflowValue<LoadedSource>>;
type LoadSourceAliasIndex = BTreeMap<String, LoadSourceAliasValues>;

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
    load_source_aliases: LoadSourceAliasIndex,
    load_source_alias_members: BTreeMap<String, BTreeSet<SSAVar>>,
    control_sources: BTreeMap<SSAVar, DataflowValue<BTreeSet<usize>>>,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GlobalLoadObservation {
    anchor: u64,
    source: LoadedSource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OptionStringReadObservation {
    anchor: u64,
    arg: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OptionStringWriteObservation {
    anchor: u64,
    arg: usize,
    value: u8,
    control_args: BTreeSet<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NumericTransformObservation {
    anchor: u64,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
    accumulator: String,
    bits: u32,
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
    global_loads: Vec<GlobalLoadObservation>,
    option_string_reads: Vec<OptionStringReadObservation>,
    option_string_writes: Vec<OptionStringWriteObservation>,
    option_string_branch_controls: BTreeSet<usize>,
    numeric_transforms: Vec<NumericTransformObservation>,
    parser_comparisons: BTreeMap<usize, ParserLoopEvidence>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct LoopEffectSummary {
    island: LoopIsland,
    natural_loop: bool,
    scans: Vec<ScanObservation>,
    folds: Vec<FoldObservation>,
    global_loads: Vec<GlobalLoadObservation>,
    numeric_transforms: Vec<NumericTransformObservation>,
    parser_comparisons: BTreeMap<usize, ParserLoopEvidence>,
}

pub(super) fn bounded_evidence() -> SemanticEvidence {
    SemanticEvidence::likely(SemanticEvidenceReason::SummaryBudget)
        .with_coverage(SemanticEvidenceCoverage::Bounded)
        .with_provenance(SemanticEvidenceProvenance::Stable)
        .with_budget_limited(true)
}

fn name_hint_evidence() -> SemanticEvidence {
    SemanticEvidence::heuristic(SemanticEvidenceReason::NameHint)
        .with_coverage(SemanticEvidenceCoverage::Bounded)
        .with_provenance(SemanticEvidenceProvenance::Ranked)
        .with_ambiguity(SemanticEvidenceAmbiguity::Ranked)
        .with_budget_limited(true)
}

fn mark_name_hint_summaries(mut summaries: Vec<NativeWorkerSummary>) -> Vec<NativeWorkerSummary> {
    let name_hint = name_hint_evidence();
    for summary in &mut summaries {
        summary.evidence = summary.evidence.combined_with(&name_hint);
    }
    summaries
}

fn native_worker_summary_sort_key(summary: &NativeWorkerSummary) -> NativeWorkerSummarySortKey {
    NativeWorkerSummarySortKey {
        anchor: summary.anchor,
        priority: native_worker_summary_priority(summary.kind),
        kind: summary.kind,
        dst: summary.dst,
        src: summary.src,
        memory: summary.memory,
        len: summary.len,
        allocation: summary.allocation,
        lifetime: summary.lifetime,
        sync: summary.sync,
        atomic: summary.atomic,
        parser: summary.parser.clone(),
        loop_summary: summary.loop_summary.clone(),
    }
}

fn native_worker_summary_priority(kind: NativeWorkerSummaryKind) -> u8 {
    match kind {
        NativeWorkerSummaryKind::ProgramOrchestrator
        | NativeWorkerSummaryKind::FileTransfer
        | NativeWorkerSummaryKind::StringScan
        | NativeWorkerSummaryKind::HashFold
        | NativeWorkerSummaryKind::TableWalk
        | NativeWorkerSummaryKind::PathWalk
        | NativeWorkerSummaryKind::DirectoryTraversal
        | NativeWorkerSummaryKind::RecordStream
        | NativeWorkerSummaryKind::FieldSelection
        | NativeWorkerSummaryKind::OutputStream
        | NativeWorkerSummaryKind::FormatRender
        | NativeWorkerSummaryKind::MetadataProbe
        | NativeWorkerSummaryKind::SortMerge
        | NativeWorkerSummaryKind::NumericTransform
        | NativeWorkerSummaryKind::Parser
        | NativeWorkerSummaryKind::DiagnosticWrapper
        | NativeWorkerSummaryKind::FormatArgumentFetch => 0,
        NativeWorkerSummaryKind::Allocation
        | NativeWorkerSummaryKind::Lifetime
        | NativeWorkerSummaryKind::Synchronization
        | NativeWorkerSummaryKind::Atomic => 1,
        NativeWorkerSummaryKind::MemoryTransfer => 2,
        NativeWorkerSummaryKind::MemoryRead | NativeWorkerSummaryKind::MemoryWrite => 3,
        NativeWorkerSummaryKind::MemoryEscape | NativeWorkerSummaryKind::MemoryFree => 4,
        NativeWorkerSummaryKind::Unknown => 5,
    }
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
        NativeWorkerSummaryKind::ProgramOrchestrator => 1,
        NativeWorkerSummaryKind::MemoryTransfer => 2,
        NativeWorkerSummaryKind::FileTransfer => 3,
        NativeWorkerSummaryKind::MemoryRead => 4,
        NativeWorkerSummaryKind::MemoryWrite => 5,
        NativeWorkerSummaryKind::MemoryEscape => 6,
        NativeWorkerSummaryKind::MemoryFree => 7,
        NativeWorkerSummaryKind::StringScan => 8,
        NativeWorkerSummaryKind::HashFold => 9,
        NativeWorkerSummaryKind::TableWalk => 10,
        NativeWorkerSummaryKind::PathWalk => 11,
        NativeWorkerSummaryKind::DirectoryTraversal => 12,
        NativeWorkerSummaryKind::RecordStream => 13,
        NativeWorkerSummaryKind::FieldSelection => 14,
        NativeWorkerSummaryKind::OutputStream => 15,
        NativeWorkerSummaryKind::FormatRender => 16,
        NativeWorkerSummaryKind::MetadataProbe => 17,
        NativeWorkerSummaryKind::SortMerge => 18,
        NativeWorkerSummaryKind::NumericTransform => 19,
        NativeWorkerSummaryKind::Parser => 20,
        NativeWorkerSummaryKind::DiagnosticWrapper => 21,
        NativeWorkerSummaryKind::FormatArgumentFetch => 22,
        NativeWorkerSummaryKind::Allocation => 23,
        NativeWorkerSummaryKind::Lifetime => 24,
        NativeWorkerSummaryKind::Synchronization => 25,
        NativeWorkerSummaryKind::Atomic => 26,
        NativeWorkerSummaryKind::Unknown => 27,
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

fn arg_byte_location(index: usize) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Arg { index },
        range: Some(SummaryMemoryRange {
            offset_lo: 0,
            offset_hi: 0,
            width: Some(1),
        }),
    }
}

fn arg_location(index: usize) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Arg { index },
        range: None,
    }
}

fn global_byte_location(address: u64) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Global { address },
        range: Some(SummaryMemoryRange {
            offset_lo: 0,
            offset_hi: 0,
            width: Some(1),
        }),
    }
}

fn global_location(address: u64) -> SummaryMemoryLocation {
    SummaryMemoryLocation {
        region: SummaryMemoryRegion::Global { address },
        range: None,
    }
}

fn normalize_semantic_summary_name(name: &str) -> Option<String> {
    let name = name
        .trim()
        .trim_start_matches("sym.")
        .trim_start_matches("dbg.")
        .trim_start_matches("fcn.")
        .trim_start_matches("sub.")
        .to_ascii_lowercase();
    let name = strip_known_compiler_suffixes(&name).to_string();
    (!name.is_empty()).then_some(name)
}

fn strip_known_compiler_suffixes(name: &str) -> &str {
    let mut current = name;
    while let Some(stripped) = strip_one_compiler_suffix(current) {
        current = stripped;
    }
    current
}

fn strip_one_compiler_suffix(name: &str) -> Option<&str> {
    if let Some(stripped) = name.strip_suffix(".cold")
        && !stripped.is_empty()
    {
        return Some(stripped);
    }
    for marker in [".isra.", ".constprop.", ".part.", ".llvm."] {
        let Some((prefix, suffix)) = name.rsplit_once(marker) else {
            continue;
        };
        if !prefix.is_empty() && !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit()) {
            return Some(prefix);
        }
    }
    None
}

pub fn has_native_worker_summary_family(name: &str) -> bool {
    let Some(name) = normalize_semantic_summary_name(name) else {
        return false;
    };
    if name.starts_with("digest_file")
        || name.starts_with("shaxxx_stream")
        || name.starts_with("find_field")
        || name.starts_with("entry.init")
        || is_quotearg_family_name(&name)
        || is_quoting_options_family_name(&name)
        || is_version_etc_family_name(&name)
        || is_xalloc_family_name(&name)
        || is_hash_table_family_name(&name)
        || is_hash_fold_family_name(&name)
        || is_parser_family_name(&name)
        || is_path_family_name(&name)
        || is_directory_family_name(&name)
        || is_record_memory_family_name(&name)
    {
        return true;
    }
    matches!(
        name.as_str(),
        "main"
            | "wmain"
            | "diagnose"
            | "usage"
            | "keycompare"
            | "_md5_process_block"
            | "md5_process_block"
            | "md5_process_bytes"
            | "_internal_fnwmatch"
            | "internal_fnwmatch"
            | "fnmatch"
            | "rpl_fnmatch"
            | "getopt"
            | "rpl_getopt"
            | "_getopt_internal"
            | "_getopt_internal_r"
            | "getopt_long"
            | "getopt_long_only"
            | "rpl_getopt_long"
            | "rpl_getopt_long_only"
            | "argmatch"
            | "argmatch_exact"
            | "argmatch_invalid"
            | "argmatch_valid"
            | "__xargmatch_internal"
            | "binop"
            | "binary_operator"
            | "unary_operator"
            | "or"
            | "three_arguments"
            | "write_counts"
            | "verror_at_line"
            | "printf_fetchargs"
            | "printf_parse"
            | "oprintf_"
            | "print_formatted"
            | "print_esc"
            | "print_xfer_stats"
            | "vasnprintf"
            | "unicode_to_mb"
            | "readlinebuffer_delim"
            | "quotearg_buffer_restyled"
            | "rpl_mbrtoc32"
            | "mbrtoc32"
            | "rpl_mbrtowc"
            | "mbrtowc"
            | "xstrtoumax"
            | "xnumtoumax"
            | "xstrtoimax"
            | "vstrtoimax"
            | "strnumcmp"
            | "strintcmp"
            | "rpl_fopen"
            | "openat_safer"
            | "rpl_nanosleep"
            | "rpl_fcntl"
            | "freopen_safer"
            | "stream_open"
            | "gettext_quote"
            | "parse_long_options"
            | "parse_gnu_standard_options_only"
            | "human_options"
            | "parse_integer"
            | "parse_number"
            | "traverse_raw_number"
            | "synchronize_output"
            | "copy_with_unblock"
            | "copy_bytes"
            | "iwrite"
            | "iwrite.constprop.0"
            | "translate_charset"
            | "invalidate_cache"
            | "decode_preserve_arg"
            | "skip"
            | "wc"
            | "is_utf8_charset"
            | "canonicalize_filename_mode"
            | "skip_whitespace_run"
            | "scan_mb_blank_field"
            | "scan_mb_delim_field"
            | "mcel_scan"
            | "mcel_cmp"
            | "mcel_scant"
            | "mcel_scanz"
            | "copy_file_data"
            | "sparse_copy"
            | "copy_internal"
            | "do_copy"
            | "copy"
            | "do_move"
            | "overwrite_ok"
            | "areadlink_with_size"
            | "areadlinkat_with_size"
            | "mfile_name_concat"
            | "set_owner"
            | "set_process_security_ctx"
            | "same_nameat"
            | "force_linkat"
            | "force_symlinkat"
            | "make_dir_parents_private"
            | "backupfile_internal"
            | "utimecmpat"
            | "fdutimensat"
            | "strmode"
            | "do_statx"
            | "getuidbyname"
            | "setlocale_null_r_unlocked"
            | "set_program_name"
            | "defaultcon"
            | "restorecon_private"
            | "restorecon"
            | "re_protect"
            | "renameatu"
            | "streamsavedir"
            | "rpl_fts_open"
            | "rpl_fts_read"
            | "rpl_fts_close"
            | "fts_build"
            | "fts_safe_changedir"
            | "oputs_"
            | "prompt"
            | "cut_characters_mode"
            | "cut_fields_mb_any"
            | "cut_fields_bytesearch"
            | "cut_file"
            | "cut_bytes"
            | "memchr2"
            | "limfield"
            | "set_fields"
            | "print_name_with_quoting"
            | "print_long_format"
            | "length_of_file_name_and_frills"
            | "print_filename"
            | "get_funky_string"
            | "abformat_init"
            | "signal_setup"
            | "quote_name_buf"
            | "quote_name"
            | "calculate_columns"
            | "print_current_files"
            | "print_file_name_and_frills"
            | "print_with_separator"
            | "verrevcmp"
            | "filenvercmp"
            | "mpsort_with_tmp"
            | "gobble_file"
            | "print_dir"
            | "extract_dirs_from_files"
            | "sort_files"
            | "fts_sort"
            | "fdfile_has_aclinfo"
            | "human_readable"
            | "__strftime_internal"
            | "nstrftime"
            | "c_nstrftime"
            | "mktime_z"
            | "rm"
            | "close_stdin"
            | "get_dir_status"
            | "leave_dir"
            | "find_entry"
            | "write_line"
            | "mergefps"
            | "sortlines"
            | "pipe_child"
            | "merge"
            | "mergefiles"
            | "init_node"
            | "fts_stat"
            | "rpl_fts_children"
            | "transfer_entries"
            | "hash_print_statistics"
            | "hash_insert_if_absent"
            | "hash_rehash"
            | "hash_clear"
            | "hash_free"
            | "hash_remove"
            | "excise"
            | "fillbuf"
            | "maybe_create_temp"
            | "find_in_given_path"
            | "get_cgroup2_cpu_quota"
            | "isaac_refill"
            | "isaac_seed"
            | "wc_lines_avx2"
            | "wc_lines_avx512"
            | "mbsnwidth"
            | "readtokens0"
            | "add_range_pair"
            | "try_tempname_len"
            | "filesystem_type"
            | "close_stdout"
            | "rpl_fclose"
            | "write_bytes"
            | "yesno"
            | "error"
            | "error_at_line"
            | "file_escape"
            | "zaptemp"
            | "sequential_sort"
            | "open_input_files"
            | "get_meminfo"
            | "randread_new"
            | "randread"
            | "_gl_scratch_buffer_grow"
            | "_gl_scratch_buffer_grow_preserve"
            | "gl_scratch_buffer_grow"
            | "gl_scratch_buffer_grow_preserve"
            | "argv_iter"
            | "argv_iter_init_argv"
            | "argv_iter_init_stream"
            | "argv_iter_n_args"
            | "argv_iter_free"
            | "gregorian_to_persian"
            | "gregorian_to_ethiopian"
            | "next_prime"
            | "num_processors"
            | "physmem_claimable"
            | "rpl_pipe2"
            | "cycle_check_init"
            | "cycle_check"
    )
}

pub fn has_program_orchestrator_summary_family(name: &str) -> bool {
    let Some(name) = normalize_semantic_summary_name(name) else {
        return false;
    };
    matches!(name.as_str(), "main" | "wmain")
}

fn is_quotearg_family_name(name: &str) -> bool {
    matches!(
        name,
        "quotearg_buffer_restyled"
            | "quotearg_buffer"
            | "quotearg_alloc"
            | "quotearg_alloc_mem"
            | "quotearg_n_options"
            | "quotearg_n"
            | "quotearg"
            | "quotearg_n_mem"
            | "quotearg_mem"
            | "quotearg_n_style"
            | "quotearg_n_style_mem"
            | "quotearg_style"
            | "quotearg_style_mem"
            | "quotearg_char"
            | "quotearg_char_mem"
            | "quotearg_colon"
            | "quotearg_colon_mem"
            | "quotearg_n_style_colon"
            | "quotearg_n_custom"
            | "quotearg_n_custom_mem"
            | "quotearg_custom"
            | "quotearg_custom_mem"
            | "quote_n_mem"
            | "quote_mem"
            | "quote_n"
            | "quote"
            | "quotearg_free"
    )
}

fn is_quoting_options_family_name(name: &str) -> bool {
    matches!(
        name,
        "clone_quoting_options"
            | "get_quoting_style"
            | "set_quoting_style"
            | "set_char_quoting"
            | "set_quoting_flags"
            | "set_custom_quoting"
    )
}

fn is_version_etc_family_name(name: &str) -> bool {
    matches!(
        name,
        "version_etc_arn"
            | "version_etc_ar"
            | "version_etc_va"
            | "version_etc"
            | "emit_bug_reporting_address"
    )
}

fn is_xalloc_family_name(name: &str) -> bool {
    matches!(
        name,
        "xmalloc"
            | "ximalloc"
            | "xcharalloc"
            | "xrealloc"
            | "xirealloc"
            | "xreallocarray"
            | "xireallocarray"
            | "xnrealloc"
            | "xnmalloc"
            | "xinmalloc"
            | "x2realloc"
            | "x2nrealloc"
            | "xpalloc"
            | "xzalloc"
            | "xizalloc"
            | "xcalloc"
            | "xicalloc"
            | "xmemdup"
            | "ximemdup"
            | "ximemdup0"
            | "xstrdup"
            | "xalloc_die"
    )
}

fn is_parser_family_name(name: &str) -> bool {
    matches!(
        name,
        "decode_line_length"
            | "parse_field_count"
            | "parse_omp_threads"
            | "parse_symbols"
            | "sort_args"
            | "strcoll_loop"
    )
}

fn is_path_family_name(name: &str) -> bool {
    matches!(
        name,
        "concatenated_filename"
            | "dir_len"
            | "dir_name"
            | "dir_suffix"
            | "file_name_concat"
            | "find_backup_file_name"
            | "mdir_name"
            | "samedir_template"
            | "target_directory_operand"
    )
}

fn is_directory_family_name(name: &str) -> bool {
    matches!(
        name,
        "enter_dir"
            | "fts_alloc"
            | "fts_compare_ino"
            | "fts_palloc"
            | "opendirat"
            | "rpl_fts_children"
            | "rpl_fts_set"
            | "savedir"
            | "setup_dir"
    )
}

fn is_record_memory_family_name(name: &str) -> bool {
    matches!(
        name,
        "copy_with_block"
            | "full_read"
            | "full_write"
            | "iread"
            | "iread_fullblock"
            | "readtokens0_free"
            | "readtokens0_init"
            | "safe_read"
            | "safe_write"
            | "seek_records"
            | "skip_bytes"
            | "skip_records"
            | "write_output"
            | "write_zeros"
    )
}

fn semantic_summary_name(summary: &FunctionSemanticSummary) -> Option<String> {
    summary
        .name
        .as_deref()
        .and_then(normalize_semantic_summary_name)
}

fn diagnostic_wrapper_summary(anchor: u64) -> NativeWorkerSummary {
    diagnostic_wrapper_summary_for_arg(anchor, 1)
}

fn diagnostic_wrapper_summary_for_arg(anchor: u64, format_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::DiagnosticWrapper,
        dst: None,
        src: None,
        memory: Some(arg_byte_location(format_arg)),
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

fn usage_wrapper_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::DiagnosticWrapper,
        dst: None,
        src: None,
        memory: None,
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

fn format_argument_fetch_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::FormatArgumentFetch,
        dst: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: 1 },
            range: None,
        }),
        src: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: 0 },
            range: None,
        }),
        memory: None,
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

fn table_compare_summary(anchor: u64) -> NativeWorkerSummary {
    table_walk_worker_summary(anchor, 0)
}

fn table_walk_worker_summary(anchor: u64, table_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::TableWalk,
        dst: None,
        src: None,
        memory: Some(arg_location(table_arg)),
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

fn global_table_walk_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::TableWalk,
        dst: None,
        src: None,
        memory: Some(global_location(anchor)),
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

fn linebuffer_delimiter_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: Some(SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index: 0 },
            range: None,
        }),
        src: None,
        memory: Some(arg_byte_location(1)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Token,
            cursor_arg: Some(1),
            base: None,
            digit_min: None,
            digit_max: None,
            accepts_sign: false,
        }),
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn string_scan_worker_summary(
    anchor: u64,
    memory_arg: usize,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::StringScan,
        dst: dst_arg.map(|index| SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index },
            range: None,
        }),
        src: None,
        memory: Some(arg_byte_location(memory_arg)),
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: Some(1),
            terminator: Some(terminator),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn token_parser_worker_summary(
    anchor: u64,
    memory_arg: usize,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: dst_arg.map(|index| SummaryMemoryLocation {
            region: SummaryMemoryRegion::Arg { index },
            range: None,
        }),
        src: None,
        memory: Some(arg_byte_location(memory_arg)),
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Token,
            cursor_arg: Some(memory_arg),
            base: None,
            digit_min: None,
            digit_max: None,
            accepts_sign: false,
        }),
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::LengthBound),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn global_token_parser_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: None,
        src: None,
        memory: Some(global_byte_location(anchor)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Token,
            cursor_arg: None,
            base: None,
            digit_min: None,
            digit_max: None,
            accepts_sign: false,
        }),
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn numeric_parser_worker_summary(anchor: u64, memory_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: None,
        src: None,
        memory: Some(arg_byte_location(memory_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Numeric,
            cursor_arg: Some(memory_arg),
            base: Some(10),
            digit_min: Some(b'0'),
            digit_max: Some(b'9'),
            accepts_sign: true,
        }),
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn argv_option_parser_worker_summary(anchor: u64, argv_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Parser,
        dst: None,
        src: None,
        memory: Some(arg_location(argv_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: Some(NativeParserSummary {
            kind: NativeParserKind::Token,
            cursor_arg: Some(argv_arg),
            base: None,
            digit_min: None,
            digit_max: None,
            accepts_sign: false,
        }),
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn file_transfer_worker_summary(
    anchor: u64,
    src_arg: usize,
    dst_arg: usize,
    length_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::FileTransfer,
        dst: Some(arg_location(dst_arg)),
        src: Some(arg_location(src_arg)),
        memory: None,
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: None,
            terminator: Some(
                length_arg
                    .map(|_| NativeWorkerTerminator::LengthBound)
                    .unwrap_or(NativeWorkerTerminator::Unknown),
            ),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn memory_transfer_worker_summary(
    anchor: u64,
    dst_arg: usize,
    src_arg: usize,
    length_arg: usize,
) -> NativeWorkerSummary {
    transfer_worker_summary(
        anchor,
        SummaryTransferEffect {
            dst: arg_byte_location(dst_arg),
            src: arg_byte_location(src_arg),
            len: SummaryTransferLength::Arg(length_arg),
        },
    )
}

fn path_walk_worker_summary(anchor: u64, path_arg: usize) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::PathWalk,
        dst: None,
        src: None,
        memory: Some(arg_byte_location(path_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::ZeroByte),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn directory_traversal_worker_summary(
    anchor: u64,
    stream_arg: usize,
    entry_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::DirectoryTraversal,
        dst: entry_arg.map(arg_location),
        src: None,
        memory: Some(arg_location(stream_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: None,
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn record_stream_worker_summary(
    anchor: u64,
    stream_arg: usize,
    dst_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::RecordStream,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: Some(arg_location(stream_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: None,
            terminator: Some(NativeWorkerTerminator::ByteEquals(b'\n')),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn field_selection_worker_summary(
    anchor: u64,
    spec_arg: usize,
    dst_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::FieldSelection,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: Some(arg_byte_location(spec_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: Some(1),
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn output_stream_worker_summary(
    anchor: u64,
    memory_arg: usize,
    stream_arg: Option<usize>,
) -> NativeWorkerSummary {
    output_stream_worker_summary_with_len(anchor, memory_arg, stream_arg, None)
}

fn output_stream_worker_summary_with_len(
    anchor: u64,
    memory_arg: usize,
    stream_arg: Option<usize>,
    length_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::OutputStream,
        dst: stream_arg.map(arg_location),
        src: None,
        memory: Some(arg_byte_location(memory_arg)),
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: Some(1),
            terminator: Some(
                length_arg
                    .map(|_| NativeWorkerTerminator::LengthBound)
                    .unwrap_or(NativeWorkerTerminator::ZeroByte),
            ),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn format_render_worker_summary(
    anchor: u64,
    input_arg: usize,
    output_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::FormatRender,
        dst: output_arg.map(arg_location),
        src: None,
        memory: Some(arg_location(input_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: None,
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn metadata_probe_worker_summary(anchor: u64, subject_arg: usize) -> NativeWorkerSummary {
    metadata_probe_worker_summary_for_memory(anchor, Some(arg_location(subject_arg)))
}

fn metadata_probe_worker_summary_for_memory(
    anchor: u64,
    memory: Option<SummaryMemoryLocation>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::MetadataProbe,
        dst: None,
        src: None,
        memory,
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

fn sort_merge_worker_summary(
    anchor: u64,
    files_arg: usize,
    output_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::SortMerge,
        dst: output_arg.map(arg_location),
        src: None,
        memory: Some(arg_location(files_arg)),
        len: None,
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg: None,
            stride: None,
            terminator: Some(NativeWorkerTerminator::Unknown),
            fold: None,
        }),
        evidence: bounded_evidence(),
    }
}

fn program_orchestrator_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::ProgramOrchestrator,
        dst: None,
        src: None,
        memory: None,
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

fn fnmatch_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 0, None, None),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
    ]
}

fn getopt_worker_summaries(anchor: u64, long_options: bool) -> Vec<NativeWorkerSummary> {
    let mut summaries = vec![
        token_parser_worker_summary(anchor, 2, None, None),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::LengthBound),
    ];
    if long_options {
        summaries.push(table_walk_worker_summary(anchor, 3));
    }
    summaries
}

fn digest_stream_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        record_stream_worker_summary(anchor, 0, None),
        named_hash_fold_worker_summary(
            anchor,
            0,
            Some(1),
            None,
            "digest_state",
            32,
            NativeWorkerFoldOperation::RotateMix,
        ),
    ]
}

fn shaxxx_stream_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        record_stream_worker_summary(anchor, 0, Some(1)),
        named_hash_fold_worker_summary(
            anchor,
            1,
            Some(1),
            None,
            "digest_state",
            32,
            NativeWorkerFoldOperation::RotateMix,
        ),
    ]
}

fn expression_evaluator_worker_summaries(
    anchor: u64,
    operator_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    if let Some(operator_arg) = operator_arg {
        return vec![
            token_parser_worker_summary(anchor, operator_arg, None, None),
            table_walk_worker_summary(anchor, operator_arg),
        ];
    }
    vec![
        global_token_parser_worker_summary(anchor),
        global_table_walk_worker_summary(anchor),
    ]
}

fn argmatch_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        table_walk_worker_summary(anchor, 1),
        table_walk_worker_summary(anchor, 2),
    ]
}

fn xargmatch_internal_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
        table_walk_worker_summary(anchor, 2),
        table_walk_worker_summary(anchor, 3),
        diagnostic_wrapper_summary_for_arg(anchor, 0),
    ]
}

fn byte_stream_selection_worker_summaries(
    anchor: u64,
    stream_arg: usize,
) -> Vec<NativeWorkerSummary> {
    vec![
        record_stream_worker_summary(anchor, stream_arg, None),
        field_selection_worker_summary(anchor, stream_arg, None),
        output_stream_worker_summary(anchor, stream_arg, None),
    ]
}

fn memchr2_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(
            anchor,
            0,
            None,
            Some(3),
            NativeWorkerTerminator::LengthBound,
        ),
        token_parser_worker_summary(anchor, 0, None, Some(3)),
    ]
}

fn same_nameat_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 1),
        path_walk_worker_summary(anchor, 3),
        string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
        string_scan_worker_summary(anchor, 3, None, None, NativeWorkerTerminator::ZeroByte),
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 2),
    ]
}

fn file_ownership_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        metadata_probe_worker_summary(anchor, 5),
        metadata_probe_worker_summary(anchor, 7),
    ]
}

fn security_context_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        table_walk_worker_summary(anchor, 4),
    ]
}

fn force_link_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        path_walk_worker_summary(anchor, 3),
        metadata_probe_worker_summary(anchor, 4),
    ]
}

fn file_mode_render_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        format_render_worker_summary(anchor, 0, Some(1)),
        output_stream_worker_summary(anchor, 1, None),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn stat_probe_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        metadata_probe_worker_summary(anchor, 4),
    ]
}

fn multibyte_cell_scan_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(
            anchor,
            0,
            None,
            Some(1),
            NativeWorkerTerminator::LengthBound,
        ),
        token_parser_worker_summary(anchor, 0, None, Some(1)),
    ]
}

fn global_sort_files_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        sort_merge_worker_summary(anchor, 0, None),
        table_walk_worker_summary(anchor, 0),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn stream_open_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 1, None),
        record_stream_worker_summary(anchor, 0, None),
        output_stream_worker_summary(anchor, 0, None),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn directory_status_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        directory_traversal_worker_summary(anchor, 0, Some(1)),
        metadata_probe_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
    ]
}

fn file_name_concat_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        allocation_role_worker_summary(anchor, None, false),
        output_stream_worker_summary(anchor, 1, Some(2)),
    ]
}

fn user_id_lookup_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        table_walk_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn merge_node_init_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        sort_merge_worker_summary(anchor, 1, Some(2)),
        table_walk_worker_summary(anchor, 0),
        table_walk_worker_summary(anchor, 1),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn multibyte_cell_scant_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::Unknown),
        token_parser_worker_summary(anchor, 0, None, None),
    ]
}

fn file_version_compare_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(
            anchor,
            0,
            None,
            Some(1),
            NativeWorkerTerminator::LengthBound,
        ),
        string_scan_worker_summary(
            anchor,
            2,
            None,
            Some(3),
            NativeWorkerTerminator::LengthBound,
        ),
        numeric_parser_worker_summary(anchor, 0),
        numeric_parser_worker_summary(anchor, 2),
    ]
}

fn file_name_frills_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 0, Some(1)),
        output_stream_worker_summary(anchor, 0, None),
    ]
}

fn tempname_probe_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        metadata_probe_worker_summary(anchor, 0),
        table_walk_worker_summary(anchor, 2),
        table_walk_worker_summary(anchor, 3),
    ]
}

fn stream_close_worker_summaries(
    anchor: u64,
    stream_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let memory_arg = stream_arg.unwrap_or(0);
    vec![
        output_stream_worker_summary(anchor, memory_arg, stream_arg),
        metadata_probe_worker_summary(anchor, memory_arg),
        global_synchronization_worker_summary(anchor),
    ]
}

fn readlink_alloc_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        allocation_role_worker_summary(anchor, Some(2), false),
    ]
}

fn overwrite_probe_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        path_walk_worker_summary(anchor, 3),
        metadata_probe_worker_summary(anchor, 4),
    ]
}

fn byte_output_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        output_stream_worker_summary_with_len(anchor, 0, None, Some(1)),
        record_stream_worker_summary(anchor, 0, Some(1)),
    ]
}

fn file_escape_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        format_render_worker_summary(anchor, 0, None),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn temp_cleanup_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 0),
        global_lifetime_worker_summary(anchor),
    ]
}

fn sequential_sort_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        sort_merge_worker_summary(anchor, 0, Some(3)),
        record_stream_worker_summary(anchor, 0, Some(3)),
        table_walk_worker_summary(anchor, 0),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn open_input_files_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 0),
        record_stream_worker_summary(anchor, 0, Some(2)),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn get_meminfo_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        memory_write_worker_summary(anchor, 0, None),
        memory_write_worker_summary(anchor, 1, None),
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
    ]
}

fn randread_new_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        table_walk_worker_summary(anchor, 1),
        allocation_role_worker_summary(anchor, None, false),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn randread_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        memory_write_worker_summary(anchor, 1, Some(2)),
        named_hash_fold_worker_summary(
            anchor,
            0,
            Some(0),
            Some(2),
            "randread_state",
            64,
            NativeWorkerFoldOperation::RotateMix,
        ),
    ]
}

fn scratch_buffer_growth_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        allocation_role_worker_summary(anchor, None, false),
        memory_read_worker_summary(anchor, 0, None),
        memory_write_worker_summary(anchor, 0, None),
    ]
}

fn argv_iterator_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "argv_iter_init_argv" => vec![
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "argv_iter_init_stream" => vec![
            record_stream_worker_summary(anchor, 0, None),
            memory_write_worker_summary(anchor, 0, None),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "argv_iter" => vec![
            argv_option_parser_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "argv_iter_n_args" => vec![
            metadata_probe_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 0),
        ],
        "argv_iter_free" => vec![
            metadata_probe_worker_summary(anchor, 0),
            global_lifetime_worker_summary(anchor),
        ],
        _ => Vec::new(),
    }
}

fn stream_read_worker_summaries(
    anchor: u64,
    memory_arg: usize,
    len_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    vec![
        record_stream_worker_summary(anchor, memory_arg, None),
        memory_read_worker_summary(anchor, memory_arg, len_arg),
    ]
}

fn stream_write_worker_summaries(
    anchor: u64,
    memory_arg: usize,
    len_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    vec![
        output_stream_worker_summary_with_len(anchor, memory_arg, None, len_arg),
        memory_write_worker_summary(anchor, memory_arg, len_arg),
    ]
}

fn numeric_transform_worker_summary(
    anchor: u64,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
    accumulator: &str,
) -> NativeWorkerSummary {
    numeric_transform_worker_summary_with_loop(
        anchor,
        dst_arg,
        length_arg,
        accumulator.to_string(),
        64,
        NativeWorkerFoldOperation::Add,
        NativeWorkerLoopSummary {
            header: anchor,
            exit_target: None,
            iterations: None,
            length_arg,
            stride: None,
            terminator: Some(
                length_arg
                    .map(|_| NativeWorkerTerminator::LengthBound)
                    .unwrap_or(NativeWorkerTerminator::Unknown),
            ),
            fold: Some(NativeWorkerFold {
                accumulator: accumulator.to_string(),
                bits: 64,
                operation: NativeWorkerFoldOperation::Add,
            }),
        },
    )
}

fn numeric_transform_worker_summary_with_loop(
    anchor: u64,
    dst_arg: Option<usize>,
    length_arg: Option<usize>,
    accumulator: String,
    bits: u32,
    operation: NativeWorkerFoldOperation,
    loop_summary: NativeWorkerLoopSummary,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::NumericTransform,
        dst: dst_arg.map(arg_location),
        src: None,
        memory: None,
        len: length_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: Some(NativeWorkerLoopSummary {
            fold: Some(NativeWorkerFold {
                accumulator,
                bits,
                operation,
            }),
            ..loop_summary
        }),
        evidence: bounded_evidence(),
    }
}

fn calendar_transform_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![numeric_transform_worker_summary(
        anchor,
        Some(0),
        None,
        "calendar_date",
    )]
}

fn prime_search_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![numeric_transform_worker_summary(
        anchor,
        None,
        Some(0),
        "prime_candidate",
    )]
}

fn processor_probe_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        numeric_transform_worker_summary(anchor, None, None, "processor_count"),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn pipe_wrapper_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        memory_write_worker_summary(anchor, 0, Some(1)),
    ]
}

fn directory_extraction_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        directory_traversal_worker_summary(anchor, 0, None),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn quote_name_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 0, Some(2)),
        table_walk_worker_summary(anchor, 3),
    ]
}

fn filename_output_worker_summaries(anchor: u64, filename_arg: usize) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, filename_arg),
        output_stream_worker_summary(anchor, filename_arg, None),
    ]
}

fn vector_line_count_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        record_stream_worker_summary(anchor, 0, None),
        named_hash_fold_worker_summary(
            anchor,
            0,
            None,
            Some(1),
            "line_count",
            64,
            NativeWorkerFoldOperation::Add,
        ),
    ]
}

fn parser_family_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "parse_symbols" | "sort_args" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            table_walk_worker_summary(anchor, 0),
        ],
        "strcoll_loop" => vec![
            string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::Unknown),
            string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::Unknown),
            table_walk_worker_summary(anchor, 2),
        ],
        _ => vec![numeric_parser_worker_summary(anchor, 0)],
    }
}

fn path_family_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "file_name_concat" | "concatenated_filename" => file_name_concat_worker_summaries(anchor),
        "find_backup_file_name" => vec![
            path_walk_worker_summary(anchor, 0),
            table_walk_worker_summary(anchor, 1),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "target_directory_operand" => vec![
            path_walk_worker_summary(anchor, 0),
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "samedir_template" => vec![
            path_walk_worker_summary(anchor, 0),
            output_stream_worker_summary(anchor, 1, None),
        ],
        _ => vec![path_walk_worker_summary(anchor, 0)],
    }
}

fn directory_family_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "fts_alloc" | "fts_palloc" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "savedir" | "opendirat" | "setup_dir" | "enter_dir" => vec![
            path_walk_worker_summary(anchor, 0),
            directory_traversal_worker_summary(anchor, 0, None),
        ],
        "fts_compare_ino" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            table_walk_worker_summary(anchor, 0),
        ],
        _ => vec![directory_traversal_worker_summary(anchor, 0, None)],
    }
}

fn record_memory_family_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "full_read" | "safe_read" | "iread" | "iread_fullblock" => {
            stream_read_worker_summaries(anchor, 1, Some(2))
        }
        "full_write" | "safe_write" => stream_write_worker_summaries(anchor, 1, Some(2)),
        "copy_with_block" => vec![
            record_stream_worker_summary(anchor, 0, Some(1)),
            output_stream_worker_summary_with_len(anchor, 1, None, Some(2)),
        ],
        "write_output" => stream_write_worker_summaries(anchor, 0, None),
        "write_zeros" => stream_write_worker_summaries(anchor, 0, Some(1)),
        "readtokens0_init" => vec![
            record_stream_worker_summary(anchor, 0, Some(1)),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "readtokens0_free" => vec![global_lifetime_worker_summary(anchor)],
        "seek_records" | "skip_records" => vec![
            record_stream_worker_summary(anchor, 0, None),
            numeric_transform_worker_summary(anchor, None, Some(1), "record_cursor"),
        ],
        "skip_bytes" => vec![
            memory_read_worker_summary(anchor, 0, Some(1)),
            numeric_transform_worker_summary(anchor, None, Some(1), "byte_cursor"),
        ],
        _ => Vec::new(),
    }
}

fn isaac_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        named_hash_fold_worker_summary(
            anchor,
            0,
            Some(0),
            None,
            "isaac_state",
            64,
            NativeWorkerFoldOperation::RotateMix,
        ),
    ]
}

fn counter_output_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        format_render_worker_summary(anchor, 5, None),
        output_stream_worker_summary(anchor, 5, None),
    ]
}

fn transfer_stats_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![format_render_worker_summary(anchor, 0, None)]
}

fn allocation_effect(size_arg: Option<usize>, zeroed: bool) -> SummaryAllocationEffect {
    SummaryAllocationEffect { size_arg, zeroed }
}

fn allocation_role_worker_summary(
    anchor: u64,
    size_arg: Option<usize>,
    zeroed: bool,
) -> NativeWorkerSummary {
    allocation_worker_summary(anchor, allocation_effect(size_arg, zeroed))
}

fn memory_read_worker_summary(
    anchor: u64,
    memory_arg: usize,
    len_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::MemoryRead,
        dst: None,
        src: None,
        memory: Some(arg_location(memory_arg)),
        len: len_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn memory_write_worker_summary(
    anchor: u64,
    memory_arg: usize,
    len_arg: Option<usize>,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::MemoryWrite,
        dst: None,
        src: None,
        memory: Some(arg_location(memory_arg)),
        len: len_arg.map(SummaryTransferLength::Arg),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

fn global_lifetime_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Lifetime,
        dst: None,
        src: None,
        memory: None,
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

fn quote_argument_worker_summaries(
    anchor: u64,
    arg_index: usize,
    len_arg: Option<usize>,
    options_arg: Option<usize>,
    output_arg: Option<usize>,
    allocation_size_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let terminator = if len_arg.is_some() {
        NativeWorkerTerminator::LengthBound
    } else {
        NativeWorkerTerminator::ZeroByte
    };
    let mut summaries = vec![
        string_scan_worker_summary(anchor, arg_index, output_arg, len_arg, terminator),
        format_render_worker_summary(anchor, arg_index, output_arg),
    ];
    if let Some(options_arg) = options_arg {
        summaries.push(table_walk_worker_summary(anchor, options_arg));
    }
    if let Some(size_arg) = allocation_size_arg {
        summaries.push(allocation_role_worker_summary(
            anchor,
            Some(size_arg),
            false,
        ));
    }
    summaries
}

fn quote_custom_worker_summaries(
    anchor: u64,
    left_arg: usize,
    right_arg: usize,
    value_arg: usize,
    len_arg: Option<usize>,
    allocation_size_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let mut summaries = quote_argument_worker_summaries(
        anchor,
        value_arg,
        len_arg,
        None,
        None,
        allocation_size_arg,
    );
    summaries.push(string_scan_worker_summary(
        anchor,
        left_arg,
        None,
        None,
        NativeWorkerTerminator::ZeroByte,
    ));
    summaries.push(string_scan_worker_summary(
        anchor,
        right_arg,
        None,
        None,
        NativeWorkerTerminator::ZeroByte,
    ));
    summaries
}

fn quote_options_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    quote_argument_worker_summaries(anchor, 1, Some(2), Some(3), None, None)
}

fn quote_worker_summaries_for_name(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "quotearg_buffer_restyled" => {
            let mut summaries =
                quote_argument_worker_summaries(anchor, 2, Some(3), None, Some(0), None);
            summaries.push(table_walk_worker_summary(anchor, 6));
            summaries
        }
        "quotearg_buffer" => {
            quote_argument_worker_summaries(anchor, 2, Some(3), Some(4), Some(0), None)
        }
        "quotearg_alloc" => {
            quote_argument_worker_summaries(anchor, 0, Some(1), Some(2), None, Some(1))
        }
        "quotearg_alloc_mem" => {
            quote_argument_worker_summaries(anchor, 0, Some(1), Some(3), None, Some(1))
        }
        "quotearg_n_options" => quote_options_worker_summaries(anchor),
        "quotearg_n" => quote_argument_worker_summaries(anchor, 1, None, None, None, None),
        "quotearg" => quote_argument_worker_summaries(anchor, 0, None, None, None, None),
        "quotearg_n_mem" => quote_argument_worker_summaries(anchor, 1, Some(2), None, None, None),
        "quotearg_mem" => quote_argument_worker_summaries(anchor, 0, Some(1), None, None, None),
        "quotearg_n_style" => quote_argument_worker_summaries(anchor, 2, None, None, None, None),
        "quotearg_n_style_mem" => {
            quote_argument_worker_summaries(anchor, 2, Some(3), None, None, None)
        }
        "quotearg_style" => quote_argument_worker_summaries(anchor, 1, None, None, None, None),
        "quotearg_style_mem" => {
            quote_argument_worker_summaries(anchor, 1, Some(2), None, None, None)
        }
        "quotearg_char" => quote_argument_worker_summaries(anchor, 0, None, None, None, None),
        "quotearg_char_mem" => {
            quote_argument_worker_summaries(anchor, 0, Some(1), None, None, None)
        }
        "quotearg_colon" => quote_argument_worker_summaries(anchor, 0, None, None, None, None),
        "quotearg_colon_mem" => {
            quote_argument_worker_summaries(anchor, 0, Some(1), None, None, None)
        }
        "quotearg_n_style_colon" => {
            quote_argument_worker_summaries(anchor, 2, None, None, None, None)
        }
        "quotearg_n_custom" => quote_custom_worker_summaries(anchor, 1, 2, 3, None, None),
        "quotearg_n_custom_mem" => quote_custom_worker_summaries(anchor, 1, 2, 3, Some(4), None),
        "quotearg_custom" => quote_custom_worker_summaries(anchor, 0, 1, 2, None, None),
        "quotearg_custom_mem" => quote_custom_worker_summaries(anchor, 0, 1, 2, Some(3), None),
        "quote_n_mem" => quote_argument_worker_summaries(anchor, 1, Some(2), None, None, None),
        "quote_mem" => quote_argument_worker_summaries(anchor, 0, Some(1), None, None, None),
        "quote_n" => quote_argument_worker_summaries(anchor, 1, None, None, None, None),
        "quote" => quote_argument_worker_summaries(anchor, 0, None, None, None, None),
        "quotearg_free" => vec![global_lifetime_worker_summary(anchor)],
        _ => Vec::new(),
    }
}

fn quoting_options_worker_summaries_for_name(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "clone_quoting_options" => vec![
            table_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "get_quoting_style" => vec![table_walk_worker_summary(anchor, 0)],
        "set_quoting_style" | "set_char_quoting" | "set_quoting_flags" => {
            vec![table_walk_worker_summary(anchor, 0)]
        }
        "set_custom_quoting" => vec![
            table_walk_worker_summary(anchor, 0),
            string_scan_worker_summary(anchor, 1, None, None, NativeWorkerTerminator::ZeroByte),
            string_scan_worker_summary(anchor, 2, None, None, NativeWorkerTerminator::ZeroByte),
        ],
        _ => Vec::new(),
    }
}

fn selinux_path_worker_summaries(anchor: u64, path_arg: usize) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, path_arg),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn re_protect_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        path_walk_worker_summary(anchor, 3),
        table_walk_worker_summary(anchor, 4),
        metadata_probe_worker_summary(anchor, 5),
    ]
}

fn rename_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        path_walk_worker_summary(anchor, 1),
        metadata_probe_worker_summary(anchor, 2),
        path_walk_worker_summary(anchor, 3),
    ]
}

fn streamsavedir_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        directory_traversal_worker_summary(anchor, 0, None),
        allocation_role_worker_summary(anchor, None, false),
    ]
}

fn version_etc_worker_summaries(
    anchor: u64,
    authors_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let mut summaries = vec![
        format_render_worker_summary(anchor, 1, Some(0)),
        format_render_worker_summary(anchor, 2, Some(0)),
        format_render_worker_summary(anchor, 3, Some(0)),
    ];
    if let Some(authors_arg) = authors_arg {
        summaries.push(table_walk_worker_summary(anchor, authors_arg));
    }
    summaries
}

fn xalloc_worker_summaries(anchor: u64, name: &str) -> Vec<NativeWorkerSummary> {
    match name {
        "xalloc_die" => vec![diagnostic_wrapper_summary(anchor)],
        "xmalloc" | "ximalloc" | "xcharalloc" => {
            vec![allocation_role_worker_summary(anchor, Some(0), false)]
        }
        "xzalloc" | "xizalloc" => vec![allocation_role_worker_summary(anchor, Some(0), true)],
        "xcalloc" | "xicalloc" => vec![allocation_role_worker_summary(anchor, None, true)],
        "xnmalloc" | "xinmalloc" => vec![allocation_role_worker_summary(anchor, None, false)],
        "xrealloc" | "xirealloc" => vec![
            allocation_role_worker_summary(anchor, Some(1), false),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "xreallocarray" | "xireallocarray" | "xnrealloc" => vec![
            allocation_role_worker_summary(anchor, None, false),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "x2realloc" => vec![
            allocation_role_worker_summary(anchor, None, false),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "x2nrealloc" => vec![
            allocation_role_worker_summary(anchor, Some(2), false),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "xpalloc" => vec![
            allocation_role_worker_summary(anchor, Some(4), false),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "xmemdup" | "ximemdup" | "ximemdup0" => vec![
            memory_read_worker_summary(anchor, 0, Some(1)),
            allocation_role_worker_summary(anchor, Some(1), false),
        ],
        "xstrdup" => vec![
            string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
            allocation_role_worker_summary(anchor, None, false),
        ],
        _ => Vec::new(),
    }
}

fn multibyte_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 1, Some(0), Some(2)),
        string_scan_worker_summary(
            anchor,
            1,
            Some(0),
            Some(2),
            NativeWorkerTerminator::LengthBound,
        ),
    ]
}

fn printf_parser_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 0, None, None),
        table_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 0, None),
    ]
}

fn libc_file_wrapper_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        path_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 1, None),
        metadata_probe_worker_summary(anchor, 0),
    ]
}

fn locale_buffer_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        string_scan_worker_summary(
            anchor,
            1,
            Some(1),
            Some(2),
            NativeWorkerTerminator::LengthBound,
        ),
        memory_write_worker_summary(anchor, 1, Some(2)),
    ]
}

fn gettext_quote_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        table_walk_worker_summary(anchor, 1),
    ]
}

fn program_name_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        string_scan_worker_summary(anchor, 0, None, None, NativeWorkerTerminator::ZeroByte),
        global_synchronization_worker_summary(anchor),
    ]
}

fn time_format_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        format_render_worker_summary(anchor, 0, Some(1)),
        metadata_probe_worker_summary(anchor, 3),
    ]
}

fn time_zone_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        metadata_probe_worker_summary(anchor, 0),
        metadata_probe_worker_summary(anchor, 1),
        numeric_transform_worker_summary(anchor, Some(1), None, "time_value"),
    ]
}

fn yesno_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        token_parser_worker_summary(anchor, 0, None, None),
        record_stream_worker_summary(anchor, 0, None),
    ]
}

fn semantic_family_worker_summaries(
    anchor: u64,
    summary: &FunctionSemanticSummary,
) -> Vec<NativeWorkerSummary> {
    let Some(name) = semantic_summary_name(summary) else {
        return Vec::new();
    };
    let summaries = match name.as_str() {
        "main" | "wmain" => vec![program_orchestrator_worker_summary(anchor)],
        name if name.starts_with("entry.init") => vec![program_orchestrator_worker_summary(anchor)],
        name if is_quotearg_family_name(name) => quote_worker_summaries_for_name(anchor, name),
        name if is_quoting_options_family_name(name) => {
            quoting_options_worker_summaries_for_name(anchor, name)
        }
        name if is_xalloc_family_name(name) => xalloc_worker_summaries(anchor, name),
        "diagnose" => vec![diagnostic_wrapper_summary(anchor)],
        "usage" => vec![usage_wrapper_summary(anchor)],
        "keycompare" => vec![table_compare_summary(anchor)],
        "_md5_process_block" | "md5_process_block" | "md5_process_bytes" => {
            vec![named_hash_fold_worker_summary(
                anchor,
                0,
                Some(2),
                Some(1),
                "md5_state",
                32,
                NativeWorkerFoldOperation::RotateMix,
            )]
        }
        "_internal_fnwmatch" | "internal_fnwmatch" | "fnmatch" | "rpl_fnmatch" => {
            fnmatch_worker_summaries(anchor)
        }
        "getopt" | "rpl_getopt" => getopt_worker_summaries(anchor, false),
        "_getopt_internal"
        | "_getopt_internal_r"
        | "getopt_long"
        | "getopt_long_only"
        | "rpl_getopt_long"
        | "rpl_getopt_long_only" => getopt_worker_summaries(anchor, true),
        "argmatch" | "argmatch_exact" | "argmatch_valid" => argmatch_worker_summaries(anchor),
        "__xargmatch_internal" => xargmatch_internal_worker_summaries(anchor),
        "argmatch_invalid" => vec![diagnostic_wrapper_summary_for_arg(anchor, 1)],
        name if name.starts_with("digest_file") => digest_stream_worker_summaries(anchor),
        name if name.starts_with("shaxxx_stream") => shaxxx_stream_worker_summaries(anchor),
        "binop" | "binary_operator" => expression_evaluator_worker_summaries(anchor, Some(0)),
        "unary_operator" | "or" | "three_arguments" => {
            expression_evaluator_worker_summaries(anchor, None)
        }
        "write_counts" => counter_output_worker_summaries(anchor),
        "verror_at_line" => vec![diagnostic_wrapper_summary_for_arg(anchor, 4)],
        "printf_fetchargs" => vec![format_argument_fetch_summary(anchor)],
        "printf_parse" | "print_formatted" | "print_esc" | "vasnprintf" => {
            printf_parser_worker_summaries(anchor)
        }
        "oprintf_" => vec![
            format_render_worker_summary(anchor, 1, None),
            output_stream_worker_summary(anchor, 1, None),
        ],
        "print_xfer_stats" => transfer_stats_worker_summaries(anchor),
        "unicode_to_mb" => multibyte_worker_summaries(anchor),
        "readlinebuffer_delim" => vec![linebuffer_delimiter_summary(anchor)],
        "rpl_mbrtoc32" | "mbrtoc32" | "rpl_mbrtowc" | "mbrtowc" => {
            multibyte_worker_summaries(anchor)
        }
        "xstrtoumax" | "xnumtoumax" => vec![numeric_parser_worker_summary(anchor, 0)],
        "xstrtoimax" | "vstrtoimax" => vec![numeric_parser_worker_summary(anchor, 0)],
        "strnumcmp" => vec![
            numeric_parser_worker_summary(anchor, 0),
            numeric_parser_worker_summary(anchor, 1),
        ],
        "strintcmp" => vec![
            numeric_parser_worker_summary(anchor, 0),
            numeric_parser_worker_summary(anchor, 1),
        ],
        "rpl_fopen" | "freopen_safer" => libc_file_wrapper_summaries(anchor),
        "openat_safer" => vec![
            path_walk_worker_summary(anchor, 1),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "gettext_quote" => gettext_quote_worker_summaries(anchor),
        "rpl_nanosleep" => vec![
            metadata_probe_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 1),
            global_synchronization_worker_summary(anchor),
        ],
        "stream_open" => stream_open_worker_summaries(anchor),
        "rpl_fcntl" => vec![metadata_probe_worker_summary(anchor, 0)],
        "parse_long_options" | "parse_gnu_standard_options_only" => {
            vec![argv_option_parser_worker_summary(anchor, 1)]
        }
        "human_options" | "parse_integer" | "parse_number" | "traverse_raw_number" => {
            vec![numeric_parser_worker_summary(anchor, 0)]
        }
        "synchronize_output" => vec![global_synchronization_worker_summary(anchor)],
        "copy_with_unblock" => vec![output_stream_worker_summary_with_len(
            anchor,
            0,
            None,
            Some(1),
        )],
        "copy_bytes" => vec![memory_transfer_worker_summary(anchor, 0, 1, 2)],
        "iwrite" => vec![output_stream_worker_summary_with_len(
            anchor,
            1,
            None,
            Some(2),
        )],
        "translate_charset" => vec![table_walk_worker_summary(anchor, 0)],
        "invalidate_cache" => vec![metadata_probe_worker_summary(anchor, 0)],
        "decode_preserve_arg" => vec![
            token_parser_worker_summary(anchor, 0, None, None),
            table_walk_worker_summary(anchor, 0),
        ],
        "skip" => vec![record_stream_worker_summary(anchor, 0, None)],
        name if name.starts_with("find_field") => {
            vec![field_selection_worker_summary(anchor, 0, None)]
        }
        "wc" => vec![
            record_stream_worker_summary(anchor, 0, None),
            numeric_parser_worker_summary(anchor, 1),
        ],
        "is_utf8_charset" => vec![global_synchronization_worker_summary(anchor)],
        "setlocale_null_r_unlocked" => locale_buffer_worker_summaries(anchor),
        "set_program_name" => program_name_worker_summaries(anchor),
        "canonicalize_filename_mode" => vec![string_scan_worker_summary(
            anchor,
            0,
            None,
            None,
            NativeWorkerTerminator::ZeroByte,
        )],
        "skip_whitespace_run" | "scan_mb_blank_field" | "scan_mb_delim_field" => {
            vec![token_parser_worker_summary(anchor, 0, None, None)]
        }
        "mcel_scan" => multibyte_cell_scan_worker_summaries(anchor),
        "mcel_cmp" => vec![numeric_transform_worker_summary(
            anchor, None, None, "mcel_cmp",
        )],
        "mcel_scant" => multibyte_cell_scant_worker_summaries(anchor),
        "mcel_scanz" => multibyte_cell_scan_worker_summaries(anchor),
        "copy_file_data" => vec![file_transfer_worker_summary(anchor, 0, 4, Some(8))],
        "sparse_copy" => vec![file_transfer_worker_summary(anchor, 0, 1, Some(7))],
        "copy_internal" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
            file_transfer_worker_summary(anchor, 0, 1, None),
        ],
        "do_copy" => vec![
            directory_traversal_worker_summary(anchor, 1, None),
            file_transfer_worker_summary(anchor, 1, 2, None),
        ],
        "copy" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
            file_transfer_worker_summary(anchor, 0, 1, None),
            table_walk_worker_summary(anchor, 5),
        ],
        "do_move" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
            file_transfer_worker_summary(anchor, 0, 1, None),
            table_walk_worker_summary(anchor, 4),
        ],
        "overwrite_ok" => overwrite_probe_worker_summaries(anchor),
        "areadlink_with_size" => vec![
            path_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, Some(1), false),
        ],
        "areadlinkat_with_size" => readlink_alloc_worker_summaries(anchor),
        "mfile_name_concat" => file_name_concat_worker_summaries(anchor),
        "set_owner" => file_ownership_worker_summaries(anchor),
        "set_process_security_ctx" => security_context_worker_summaries(anchor),
        "same_nameat" => same_nameat_worker_summaries(anchor),
        "force_linkat" => force_link_worker_summaries(anchor),
        "force_symlinkat" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 1),
            path_walk_worker_summary(anchor, 2),
            metadata_probe_worker_summary(anchor, 4),
        ],
        "make_dir_parents_private" => vec![path_walk_worker_summary(anchor, 0)],
        "backupfile_internal" | "utimecmpat" => vec![path_walk_worker_summary(anchor, 1)],
        "fdutimensat" => vec![
            metadata_probe_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 1),
            path_walk_worker_summary(anchor, 2),
        ],
        "strmode" => file_mode_render_worker_summaries(anchor),
        "do_statx" => stat_probe_worker_summaries(anchor),
        "getuidbyname" => user_id_lookup_worker_summaries(anchor),
        "defaultcon" | "restorecon_private" | "restorecon" => {
            selinux_path_worker_summaries(anchor, 1)
        }
        "re_protect" => re_protect_worker_summaries(anchor),
        "renameatu" => rename_worker_summaries(anchor),
        "streamsavedir" => streamsavedir_worker_summaries(anchor),
        "rpl_fts_open" | "rpl_fts_read" | "rpl_fts_close" | "fts_build" => {
            vec![directory_traversal_worker_summary(anchor, 0, None)]
        }
        "fts_safe_changedir" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            path_walk_worker_summary(anchor, 3),
        ],
        "version_etc_arn" => version_etc_worker_summaries(anchor, Some(4)),
        "version_etc_ar" | "version_etc_va" => version_etc_worker_summaries(anchor, Some(4)),
        "version_etc" => version_etc_worker_summaries(anchor, None),
        "emit_bug_reporting_address" => vec![usage_wrapper_summary(anchor)],
        "oputs_" => vec![output_stream_worker_summary(anchor, 0, None)],
        "prompt" => vec![format_render_worker_summary(anchor, 0, None)],
        "cut_characters_mode" => vec![
            record_stream_worker_summary(anchor, 0, None),
            field_selection_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "cut_fields_mb_any" | "cut_fields_bytesearch" => vec![
            record_stream_worker_summary(anchor, 0, None),
            field_selection_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "cut_file" => byte_stream_selection_worker_summaries(anchor, 0),
        "cut_bytes" => byte_stream_selection_worker_summaries(anchor, 0),
        "memchr2" => memchr2_worker_summaries(anchor),
        "limfield" => vec![
            field_selection_worker_summary(anchor, 0, None),
            token_parser_worker_summary(anchor, 0, None, None),
            numeric_parser_worker_summary(anchor, 0),
        ],
        "set_fields" => vec![field_selection_worker_summary(anchor, 0, None)],
        "print_name_with_quoting" => vec![
            format_render_worker_summary(anchor, 0, Some(2)),
            path_walk_worker_summary(anchor, 0),
        ],
        "length_of_file_name_and_frills" => file_name_frills_worker_summaries(anchor),
        "print_long_format" => vec![
            format_render_worker_summary(anchor, 0, None),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "print_filename" => filename_output_worker_summaries(anchor, 0),
        "get_funky_string" => quote_name_worker_summaries(anchor),
        "abformat_init" => vec![
            table_walk_worker_summary(anchor, 0),
            format_render_worker_summary(anchor, 0, None),
        ],
        "signal_setup" => vec![
            global_synchronization_worker_summary(anchor),
            table_walk_worker_summary(anchor, 0),
        ],
        "quote_name_buf" | "quote_name" => quote_name_worker_summaries(anchor),
        "print_file_name_and_frills" => file_name_frills_worker_summaries(anchor),
        "print_with_separator" => vec![format_render_worker_summary(anchor, 0, None)],
        "calculate_columns" | "print_current_files" => vec![
            table_walk_worker_summary(anchor, 0),
            format_render_worker_summary(anchor, 0, None),
        ],
        "verrevcmp" => vec![
            string_scan_worker_summary(
                anchor,
                0,
                None,
                Some(1),
                NativeWorkerTerminator::LengthBound,
            ),
            string_scan_worker_summary(
                anchor,
                2,
                None,
                Some(3),
                NativeWorkerTerminator::LengthBound,
            ),
            numeric_parser_worker_summary(anchor, 0),
            numeric_parser_worker_summary(anchor, 2),
        ],
        "filenvercmp" => file_version_compare_worker_summaries(anchor),
        "mpsort_with_tmp" => vec![
            sort_merge_worker_summary(anchor, 0, Some(3)),
            table_walk_worker_summary(anchor, 0),
        ],
        "gobble_file" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "print_dir" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ],
        "extract_dirs_from_files" => directory_extraction_worker_summaries(anchor),
        "sort_files" => global_sort_files_worker_summaries(anchor),
        "fts_sort" => vec![
            sort_merge_worker_summary(anchor, 0, None),
            directory_traversal_worker_summary(anchor, 0, None),
            table_walk_worker_summary(anchor, 0),
        ],
        "fdfile_has_aclinfo" => vec![
            metadata_probe_worker_summary(anchor, 1),
            path_walk_worker_summary(anchor, 1),
        ],
        "human_readable" => vec![format_render_worker_summary(anchor, 0, Some(1))],
        "nstrftime" | "c_nstrftime" => time_format_worker_summaries(anchor),
        "mktime_z" => time_zone_worker_summaries(anchor),
        "__strftime_internal" => vec![
            format_render_worker_summary(anchor, 2, Some(0)),
            record_stream_worker_summary(anchor, 2, Some(0)),
        ],
        "rm" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            path_walk_worker_summary(anchor, 0),
        ],
        "close_stdin" => stream_close_worker_summaries(anchor, None),
        "get_dir_status" => directory_status_worker_summaries(anchor),
        "leave_dir" | "find_entry" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
        ],
        "write_line" => vec![
            output_stream_worker_summary(anchor, 0, Some(1)),
            record_stream_worker_summary(anchor, 0, Some(1)),
        ],
        "mergefps" => vec![
            sort_merge_worker_summary(anchor, 0, Some(3)),
            record_stream_worker_summary(anchor, 0, Some(3)),
        ],
        "sortlines" => vec![
            sort_merge_worker_summary(anchor, 0, Some(5)),
            record_stream_worker_summary(anchor, 0, Some(5)),
        ],
        "pipe_child" => vec![format_render_worker_summary(anchor, 0, Some(1))],
        "merge" => vec![sort_merge_worker_summary(anchor, 0, None)],
        "mergefiles" => vec![
            sort_merge_worker_summary(anchor, 0, Some(3)),
            record_stream_worker_summary(anchor, 0, Some(3)),
        ],
        "init_node" => merge_node_init_worker_summaries(anchor),
        "fts_stat" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "rpl_fts_children" => vec![directory_traversal_worker_summary(anchor, 0, None)],
        "transfer_entries" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            directory_traversal_worker_summary(anchor, 1, None),
        ],
        "hash_print_statistics" => hash_statistics_worker_summaries(anchor),
        "hash_insert_if_absent" => hash_table_worker_summaries(anchor, 0, Some(1)),
        "hash_rehash" => vec![
            table_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, Some(1), false),
        ],
        "hash_clear" | "hash_free" => vec![
            table_walk_worker_summary(anchor, 0),
            global_lifetime_worker_summary(anchor),
        ],
        "hash_remove" => hash_table_worker_summaries(anchor, 0, Some(1)),
        "excise" => vec![
            directory_traversal_worker_summary(anchor, 0, Some(1)),
            path_walk_worker_summary(anchor, 1),
            metadata_probe_worker_summary(anchor, 1),
        ],
        "fillbuf" => vec![
            record_stream_worker_summary(anchor, 0, Some(1)),
            memory_read_worker_summary(anchor, 1, Some(2)),
        ],
        "maybe_create_temp" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "find_in_given_path" => vec![
            path_walk_worker_summary(anchor, 0),
            path_walk_worker_summary(anchor, 1),
        ],
        "get_cgroup2_cpu_quota" => vec![
            path_walk_worker_summary(anchor, 0),
            metadata_probe_worker_summary(anchor, 0),
            numeric_parser_worker_summary(anchor, 0),
        ],
        "isaac_refill" | "isaac_seed" => isaac_worker_summaries(anchor),
        "wc_lines_avx2" | "wc_lines_avx512" => vector_line_count_worker_summaries(anchor),
        "mbsnwidth" => multibyte_cell_scan_worker_summaries(anchor),
        "readtokens0" => vec![
            record_stream_worker_summary(anchor, 0, Some(1)),
            token_parser_worker_summary(anchor, 0, Some(1), None),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "add_range_pair" => vec![
            table_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "try_tempname_len" => tempname_probe_worker_summaries(anchor),
        "filesystem_type" => vec![
            directory_traversal_worker_summary(anchor, 0, None),
            metadata_probe_worker_summary(anchor, 1),
            table_walk_worker_summary(anchor, 0),
        ],
        "close_stdout" => stream_close_worker_summaries(anchor, None),
        "rpl_fclose" => stream_close_worker_summaries(anchor, Some(0)),
        "write_bytes" => byte_output_worker_summaries(anchor),
        "yesno" => yesno_worker_summaries(anchor),
        "error" => vec![diagnostic_wrapper_summary_for_arg(anchor, 2)],
        "error_at_line" => vec![diagnostic_wrapper_summary_for_arg(anchor, 4)],
        "file_escape" => file_escape_worker_summaries(anchor),
        "zaptemp" => temp_cleanup_worker_summaries(anchor),
        "sequential_sort" => sequential_sort_worker_summaries(anchor),
        "open_input_files" => open_input_files_worker_summaries(anchor),
        "get_meminfo" => get_meminfo_worker_summaries(anchor),
        "randread_new" => randread_new_worker_summaries(anchor),
        "randread" => randread_worker_summaries(anchor),
        "_gl_scratch_buffer_grow"
        | "_gl_scratch_buffer_grow_preserve"
        | "gl_scratch_buffer_grow"
        | "gl_scratch_buffer_grow_preserve" => scratch_buffer_growth_worker_summaries(anchor),
        "argv_iter"
        | "argv_iter_init_argv"
        | "argv_iter_init_stream"
        | "argv_iter_n_args"
        | "argv_iter_free" => argv_iterator_worker_summaries(anchor, &name),
        "gregorian_to_persian" | "gregorian_to_ethiopian" => {
            calendar_transform_worker_summaries(anchor)
        }
        "next_prime" => prime_search_worker_summaries(anchor),
        "num_processors" | "physmem_claimable" => processor_probe_worker_summaries(anchor),
        "rpl_pipe2" => pipe_wrapper_worker_summaries(anchor),
        "cycle_check_init" => vec![
            metadata_probe_worker_summary(anchor, 0),
            memory_write_worker_summary(anchor, 0, None),
        ],
        "cycle_check" => vec![
            metadata_probe_worker_summary(anchor, 1),
            memory_read_worker_summary(anchor, 0, None),
            memory_write_worker_summary(anchor, 0, None),
        ],
        name if is_hash_table_family_name(name) => hash_table_family_worker_summaries(anchor, name),
        name if is_hash_fold_family_name(name) => hash_fold_family_worker_summaries(anchor, name),
        name if is_parser_family_name(name) => parser_family_worker_summaries(anchor, name),
        name if is_path_family_name(name) => path_family_worker_summaries(anchor, name),
        name if is_directory_family_name(name) => directory_family_worker_summaries(anchor, name),
        name if is_record_memory_family_name(name) => {
            record_memory_family_worker_summaries(anchor, name)
        }
        _ => Vec::new(),
    };
    mark_name_hint_summaries(summaries)
}

fn structural_worker_summaries_from_interproc_summary(
    anchor: u64,
    summary: &FunctionSemanticSummary,
) -> Vec<NativeWorkerSummary> {
    let mut summaries = Vec::new();

    if matches!(summary.return_relation, SummaryReturnRelation::HeapAlloc)
        && summary.allocation_effects.is_empty()
    {
        summaries.push(allocation_role_worker_summary(anchor, None, false));
    }

    let known_lifetime_frees = summary
        .lifetime_effects
        .iter()
        .filter(|effect| effect.op == SummaryLifetimeOp::Free)
        .map(|effect| effect.arg)
        .collect::<BTreeSet<_>>();
    let free_args = summary
        .memory_effects
        .iter()
        .filter(|effect| effect.kind == SummaryMemoryEffectKind::Free)
        .filter_map(|effect| match effect.location.region {
            SummaryMemoryRegion::Arg { index } => Some(index),
            SummaryMemoryRegion::Global { .. }
            | SummaryMemoryRegion::HeapReturn
            | SummaryMemoryRegion::Unknown => None,
        })
        .chain(
            summary
                .arg_effects
                .iter()
                .filter(|(_, effect)| effect.free)
                .map(|(arg, _)| *arg),
        )
        .collect::<BTreeSet<_>>();
    for arg in free_args.difference(&known_lifetime_frees) {
        summaries.push(lifetime_worker_summary(
            anchor,
            SummaryLifetimeEffect {
                arg: *arg,
                op: SummaryLifetimeOp::Free,
            },
        ));
    }

    let read_effects = summary
        .memory_effects
        .iter()
        .filter(|effect| effect.kind == SummaryMemoryEffectKind::Read)
        .collect::<Vec<_>>();
    let has_runtime_effects = summary.writes_global_memory
        || summary.touches_unknown_memory
        || summary.has_unknown_calls
        || summary
            .memory_effects
            .iter()
            .any(|effect| !matches!(effect.kind, SummaryMemoryEffectKind::Read));
    let mut global_reads = BTreeSet::new();
    let mut byte_arg_reads = BTreeSet::new();
    for effect in read_effects {
        match effect.location.region {
            SummaryMemoryRegion::Global { .. } => {
                global_reads.insert(effect.location);
            }
            SummaryMemoryRegion::Arg { index } => {
                if effect
                    .location
                    .range
                    .and_then(|range| range.width)
                    .is_some_and(|width| width == 1)
                {
                    byte_arg_reads.insert(index);
                }
            }
            SummaryMemoryRegion::HeapReturn | SummaryMemoryRegion::Unknown => {}
        }
    }
    if summary.reads_global_memory {
        for location in global_reads {
            summaries.push(metadata_probe_worker_summary_for_memory(
                anchor,
                Some(location),
            ));
        }
    }
    if has_runtime_effects {
        for arg in byte_arg_reads {
            summaries.push(path_walk_worker_summary(anchor, arg));
        }
    }

    summaries
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

fn global_synchronization_worker_summary(anchor: u64) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::Synchronization,
        dst: None,
        src: None,
        memory: None,
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
    worker_summaries.extend(semantic_family_worker_summaries(anchor, summary));
    worker_summaries.extend(structural_worker_summaries_from_interproc_summary(
        anchor, summary,
    ));
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

fn x86_alias_tuple(var: &SSAVar) -> Option<(String, u32, u32, u32)> {
    let spec = x86_register_alias_spec(register_base_name(var))?;
    Some((spec.family, spec.offset_bits, spec.width_bits, var.version))
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

fn join_dataflow_map<K: Clone + Ord, T: Clone + Eq>(
    left: &mut BTreeMap<K, DataflowValue<T>>,
    right: &BTreeMap<K, DataflowValue<T>>,
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
    let controls_changed = join_dataflow_map(&mut left.control_sources, &right.control_sources);
    if loads_changed {
        rebuild_load_source_alias_index(left);
    }
    roots_changed || loads_changed || controls_changed
}

fn insert_exact_dataflow_value<K: Clone + Ord, T: Clone + Eq>(
    map: &mut BTreeMap<K, DataflowValue<T>>,
    key: &K,
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

fn insert_dataflow_value<K: Clone + Ord, T: Clone + Eq>(
    map: &mut BTreeMap<K, DataflowValue<T>>,
    key: &K,
    value: DataflowValue<T>,
) {
    match map.get_mut(key) {
        Some(existing) => {
            let _ = join_dataflow_value(existing, &value);
        }
        None => {
            map.insert(key.clone(), value);
        }
    }
}

fn insert_load_source_dataflow_value(
    state: &mut WorkerDataflowState,
    key: &SSAVar,
    value: DataflowValue<LoadedSource>,
) {
    match value.clone() {
        DataflowValue::Exact(source) => {
            insert_exact_dataflow_value(&mut state.load_sources, key, source);
        }
        DataflowValue::Unknown => {
            insert_dataflow_value(&mut state.load_sources, key, DataflowValue::Unknown);
        }
    }
    if let Some((family, offset_bits, width_bits, version)) = x86_alias_tuple(key) {
        let alias_key = (offset_bits, width_bits, version);
        state
            .load_source_alias_members
            .entry(family.clone())
            .or_default()
            .insert(key.clone());
        match value {
            DataflowValue::Exact(source) => insert_exact_dataflow_value(
                state.load_source_aliases.entry(family).or_default(),
                &alias_key,
                source,
            ),
            DataflowValue::Unknown => insert_dataflow_value(
                state.load_source_aliases.entry(family).or_default(),
                &alias_key,
                DataflowValue::Unknown,
            ),
        }
    }
}

fn insert_exact_load_source_value(
    state: &mut WorkerDataflowState,
    key: &SSAVar,
    value: LoadedSource,
) {
    insert_load_source_dataflow_value(state, key, DataflowValue::Exact(value));
}

fn insert_unknown_load_source_value(state: &mut WorkerDataflowState, key: &SSAVar) {
    insert_load_source_dataflow_value(state, key, DataflowValue::Unknown);
}

fn insert_exact_control_source_value(
    state: &mut WorkerDataflowState,
    key: &SSAVar,
    value: BTreeSet<usize>,
) {
    insert_exact_dataflow_value(&mut state.control_sources, key, value);
}

fn insert_unknown_control_source_value(state: &mut WorkerDataflowState, key: &SSAVar) {
    insert_dataflow_value(&mut state.control_sources, key, DataflowValue::Unknown);
}

fn rebuild_load_source_alias_index(state: &mut WorkerDataflowState) {
    state.load_source_aliases.clear();
    state.load_source_alias_members.clear();
    for (var, source) in &state.load_sources {
        if let Some((family, offset_bits, width_bits, version)) = x86_alias_tuple(var) {
            let alias_key = (offset_bits, width_bits, version);
            state
                .load_source_alias_members
                .entry(family.clone())
                .or_default()
                .insert(var.clone());
            insert_dataflow_value(
                state.load_source_aliases.entry(family).or_default(),
                &alias_key,
                source.clone(),
            );
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
        .load_source_aliases
        .get(&requested.family)?
        .iter()
        .filter_map(|((offset_bits, width_bits, version), source)| {
            let source = source.exact().copied()?;
            let candidate = RegisterAliasSpec {
                family: requested.family.clone(),
                offset_bits: *offset_bits,
                width_bits: *width_bits,
            };
            x86_alias_covers(&candidate, &requested).then_some((*version, *width_bits, source))
        })
        .max_by_key(|(version, width_bits, _)| (*version, *width_bits))
        .map(|(_, _, source)| source)
}

fn source_control_args(source: LoadedSource) -> Option<BTreeSet<usize>> {
    let arg = source_arg(source)?;
    Some(BTreeSet::from([arg]))
}

fn dataflow_control_args(var: &SSAVar, state: &WorkerDataflowState) -> Option<BTreeSet<usize>> {
    state.control_sources.get(var)?.exact().cloned()
}

fn dataflow_control_args_from_operand(
    var: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<BTreeSet<usize>> {
    dataflow_control_args(var, state)
        .or_else(|| dataflow_loaded_source(var, state).and_then(source_control_args))
}

fn merge_control_args(
    left: Option<BTreeSet<usize>>,
    right: Option<BTreeSet<usize>>,
) -> Option<BTreeSet<usize>> {
    match (left, right) {
        (Some(mut left), Some(right)) => {
            left.extend(right);
            Some(left)
        }
        (Some(left), None) | (None, Some(left)) => Some(left),
        (None, None) => None,
    }
}

fn dataflow_kill_load_source_aliases(dst: &SSAVar, state: &mut WorkerDataflowState) {
    let Some(dst_spec) = x86_register_alias_spec(register_base_name(dst)) else {
        state.load_sources.remove(dst);
        insert_unknown_load_source_value(state, dst);
        insert_unknown_control_source_value(state, dst);
        return;
    };
    if let Some(members) = state.load_source_alias_members.remove(&dst_spec.family) {
        for member in members {
            state.load_sources.remove(&member);
        }
    }
    state.load_source_aliases.remove(&dst_spec.family);
    insert_unknown_load_source_value(state, dst);
    insert_unknown_control_source_value(state, dst);
}

fn dataflow_copy_root_if_known(dst: &SSAVar, src: &SSAVar, state: &mut WorkerDataflowState) {
    if let Some(root) = dataflow_rooted_region(src, state) {
        insert_exact_dataflow_value(&mut state.roots, dst, root);
    }
}

fn dataflow_copy_load_source_if_known(dst: &SSAVar, src: &SSAVar, state: &mut WorkerDataflowState) {
    let source = dataflow_loaded_source(src, state);
    let control_args = dataflow_control_args_from_operand(src, state);
    dataflow_kill_load_source_aliases(dst, state);
    if let Some(source) = source {
        insert_exact_load_source_value(state, dst, source);
    }
    if let Some(control_args) = control_args {
        insert_exact_control_source_value(state, dst, control_args);
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
        insert_exact_load_source_value(state, dst, first);
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
    insert_exact_load_source_value(state, dst, source);
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
    let control_args = merge_control_args(
        dataflow_control_args_from_operand(a, state),
        dataflow_control_args_from_operand(b, state),
    );
    let source = match (a_source, b_source) {
        (Some(source), None) | (None, Some(source)) => Some(source),
        (Some(a_source), Some(b_source)) if a_source == b_source => Some(a_source),
        _ => None,
    };
    dataflow_kill_load_source_aliases(dst, state);
    if let Some(source) = source {
        insert_exact_load_source_value(state, dst, source);
    }
    if let Some(control_args) = control_args {
        insert_exact_control_source_value(state, dst, control_args);
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
        NativeWorkerSummaryKind::MemoryTransfer | NativeWorkerSummaryKind::FileTransfer => {
            NativeMemoryAccessKind::Transfer
        }
        NativeWorkerSummaryKind::MemoryRead
        | NativeWorkerSummaryKind::ProgramOrchestrator
        | NativeWorkerSummaryKind::StringScan
        | NativeWorkerSummaryKind::HashFold
        | NativeWorkerSummaryKind::TableWalk
        | NativeWorkerSummaryKind::PathWalk
        | NativeWorkerSummaryKind::DirectoryTraversal
        | NativeWorkerSummaryKind::RecordStream
        | NativeWorkerSummaryKind::FieldSelection
        | NativeWorkerSummaryKind::OutputStream
        | NativeWorkerSummaryKind::FormatRender
        | NativeWorkerSummaryKind::MetadataProbe
        | NativeWorkerSummaryKind::SortMerge
        | NativeWorkerSummaryKind::NumericTransform
        | NativeWorkerSummaryKind::Parser
        | NativeWorkerSummaryKind::DiagnosticWrapper
        | NativeWorkerSummaryKind::FormatArgumentFetch => NativeMemoryAccessKind::Read,
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
    let has_explicit_location =
        worker.memory.is_some() || worker.dst.is_some() || worker.src.is_some();
    let has_transfer_len =
        worker.len.is_some() && worker.kind != NativeWorkerSummaryKind::NumericTransform;
    if has_explicit_location || has_transfer_len {
        let kind = if worker.kind == NativeWorkerSummaryKind::NumericTransform
            && worker.dst.is_some()
            && worker.memory.is_none()
        {
            NativeMemoryAccessKind::Write
        } else {
            memory_access_kind(worker.kind)
        };
        accesses.push(NativeMemoryAccessSummary {
            kind,
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

fn dataflow_compare_control_args(
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<BTreeSet<usize>> {
    merge_control_args(
        dataflow_control_args_from_operand(a, state),
        dataflow_control_args_from_operand(b, state),
    )
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

fn dataflow_arg_index(var: &SSAVar, state: &WorkerDataflowState) -> Option<usize> {
    abi_pointer_arg_index(var).or_else(|| match dataflow_rooted_region(var, state)? {
        SummaryMemoryRegion::Arg { index } => Some(index),
        SummaryMemoryRegion::Global { .. }
        | SummaryMemoryRegion::HeapReturn
        | SummaryMemoryRegion::Unknown => None,
    })
}

fn numeric_transform_binary_observation(
    anchor: u64,
    dst: &SSAVar,
    a: &SSAVar,
    b: &SSAVar,
    state: &WorkerDataflowState,
    operation: NativeWorkerFoldOperation,
) -> Option<NumericTransformObservation> {
    if dataflow_loaded_binary_source(a, b, state).is_some() {
        return None;
    }
    let length_arg = dataflow_arg_index(a, state).or_else(|| dataflow_arg_index(b, state));
    let has_const_operand = const_value(a).is_some() || const_value(b).is_some();
    if length_arg.is_none() && !has_const_operand {
        return None;
    }
    Some(NumericTransformObservation {
        anchor,
        dst_arg: dataflow_arg_index(dst, state),
        length_arg,
        accumulator: dst.display_name(),
        bits: dst.size.saturating_mul(8),
        operation,
    })
}

fn numeric_transform_unary_observation(
    anchor: u64,
    dst: &SSAVar,
    src: &SSAVar,
    state: &WorkerDataflowState,
) -> Option<NumericTransformObservation> {
    if dataflow_loaded_source(src, state).is_some() {
        return None;
    }
    let length_arg = dataflow_arg_index(src, state)?;
    Some(NumericTransformObservation {
        anchor,
        dst_arg: dataflow_arg_index(dst, state),
        length_arg: Some(length_arg),
        accumulator: dst.display_name(),
        bits: dst.size.saturating_mul(8),
        operation: NativeWorkerFoldOperation::Add,
    })
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

fn scan_worker_kind(
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummaryKind {
    match (source.location.region, terminator) {
        (SummaryMemoryRegion::Global { .. }, _) => NativeWorkerSummaryKind::TableWalk,
        (_, NativeWorkerTerminator::ByteEquals(b'/' | b'\\' | b':' | b'.')) => {
            NativeWorkerSummaryKind::PathWalk
        }
        (_, NativeWorkerTerminator::ZeroByte) => NativeWorkerSummaryKind::StringScan,
        _ => NativeWorkerSummaryKind::MemoryRead,
    }
}

fn scan_summary(
    func: &SsaArtifact,
    anchor: u64,
    source: LoadedSource,
    terminator: NativeWorkerTerminator,
) -> NativeWorkerSummary {
    let kind = scan_worker_kind(source, terminator);
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
    let kind = scan_worker_kind(source, terminator);
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

fn table_walk_summary_for_island(island: &LoopIsland, source: LoadedSource) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor: island.header,
        kind: NativeWorkerSummaryKind::TableWalk,
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
            None,
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

fn numeric_transform_summary_for_island(
    island: &LoopIsland,
    observation: NumericTransformObservation,
) -> NativeWorkerSummary {
    let length_arg = observation.length_arg;
    let terminator = length_arg
        .map(|_| NativeWorkerTerminator::LengthBound)
        .unwrap_or(NativeWorkerTerminator::Unknown);
    numeric_transform_worker_summary_with_loop(
        island.header,
        observation.dst_arg,
        length_arg,
        observation.accumulator,
        observation.bits,
        observation.operation,
        loop_summary_from_island(island, terminator, None, length_arg),
    )
}

fn numeric_transform_summary(
    func: &SsaArtifact,
    observation: NumericTransformObservation,
) -> NativeWorkerSummary {
    let length_arg = observation.length_arg;
    let terminator = length_arg
        .map(|_| NativeWorkerTerminator::LengthBound)
        .unwrap_or(NativeWorkerTerminator::Unknown);
    let exit_target = func
        .function()
        .successors(observation.anchor)
        .into_iter()
        .next();
    numeric_transform_worker_summary_with_loop(
        observation.anchor,
        observation.dst_arg,
        observation.length_arg,
        observation.accumulator,
        observation.bits,
        observation.operation,
        NativeWorkerLoopSummary {
            header: observation.anchor,
            exit_target,
            iterations: None,
            length_arg,
            stride: None,
            terminator: Some(terminator),
            fold: None,
        },
    )
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
            SSAOp::IntMult { dst, a, b }
            | SSAOp::IntDiv { dst, a, b }
            | SSAOp::IntSDiv { dst, a, b }
            | SSAOp::IntRem { dst, a, b }
            | SSAOp::IntSRem { dst, a, b } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(observation) = numeric_transform_binary_observation(
                        block.addr,
                        dst,
                        a,
                        b,
                        &state,
                        NativeWorkerFoldOperation::Add,
                    )
                {
                    observations.numeric_transforms.push(observation);
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
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
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(observation) = numeric_transform_binary_observation(
                        block.addr,
                        dst,
                        a,
                        b,
                        &state,
                        NativeWorkerFoldOperation::RotateMix,
                    )
                {
                    observations.numeric_transforms.push(observation);
                }
                dataflow_copy_binary_load_source_if_unambiguous(dst, a, b, &mut state);
            }
            SSAOp::PopCount { dst, src } | SSAOp::Lzcount { dst, src } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(observation) =
                        numeric_transform_unary_observation(block.addr, dst, src, &state)
                {
                    observations.numeric_transforms.push(observation);
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
            }
            SSAOp::IntEqual { dst, a, b } | SSAOp::IntNotEqual { dst, a, b } => {
                let control_args = dataflow_compare_control_args(a, b, &state);
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
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
            }
            SSAOp::IntLess { dst, a, b } | SSAOp::IntSLess { dst, a, b } => {
                let control_args = dataflow_compare_control_args(a, b, &state);
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
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
            }
            SSAOp::IntLessEqual { dst, a, b } | SSAOp::IntSLessEqual { dst, a, b } => {
                let control_args = dataflow_compare_control_args(a, b, &state);
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
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
            }
            SSAOp::BoolNot { dst, src } => {
                let control_args = dataflow_control_args_from_operand(src, &state);
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
            }
            SSAOp::BoolAnd { dst, a, b }
            | SSAOp::BoolOr { dst, a, b }
            | SSAOp::BoolXor { dst, a, b } => {
                let control_args = merge_control_args(
                    dataflow_control_args_from_operand(a, &state),
                    dataflow_control_args_from_operand(b, &state),
                );
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(control_args) = control_args {
                    insert_exact_control_source_value(&mut state, dst, control_args);
                }
            }
            SSAOp::Load { dst, addr, .. }
            | SSAOp::LoadLinked { dst, addr, .. }
            | SSAOp::LoadGuarded { dst, addr, .. } => {
                dataflow_kill_load_source_aliases(dst, &mut state);
                if let Some(region) = dataflow_rooted_region(addr, &state) {
                    let source = LoadedSource {
                        location: location_from_region(region, dst.size),
                        size: dst.size,
                        block_addr: block.addr,
                        value_delta: 0,
                    };
                    if let Some(observations) = observations.as_deref_mut()
                        && matches!(region, SummaryMemoryRegion::Global { .. })
                    {
                        observations.global_loads.push(GlobalLoadObservation {
                            anchor: block.addr,
                            source,
                        });
                    }
                    if let Some(observations) = observations.as_deref_mut()
                        && let SummaryMemoryRegion::Arg { index } = region
                    {
                        observations
                            .option_string_reads
                            .push(OptionStringReadObservation {
                                anchor: block.addr,
                                arg: index,
                            });
                    }
                    insert_exact_load_source_value(&mut state, dst, source);
                }
            }
            SSAOp::Store { addr, val, .. } => {
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(SummaryMemoryRegion::Arg { index }) =
                        dataflow_rooted_region(addr, &state)
                    && let Some(value) =
                        const_value(val).filter(|value| *value <= u64::from(u8::MAX))
                {
                    observations
                        .option_string_writes
                        .push(OptionStringWriteObservation {
                            anchor: block.addr,
                            arg: index,
                            value: value as u8,
                            control_args: BTreeSet::new(),
                        });
                }
            }
            SSAOp::StoreGuarded {
                addr, val, guard, ..
            } => {
                let control_args =
                    dataflow_control_args_from_operand(guard, &state).unwrap_or_default();
                if let Some(observations) = observations.as_deref_mut()
                    && let Some(SummaryMemoryRegion::Arg { index }) =
                        dataflow_rooted_region(addr, &state)
                    && let Some(value) =
                        const_value(val).filter(|value| *value <= u64::from(u8::MAX))
                {
                    observations
                        .option_string_writes
                        .push(OptionStringWriteObservation {
                            anchor: block.addr,
                            arg: index,
                            value: value as u8,
                            control_args,
                        });
                }
            }
            SSAOp::CBranch { cond, .. } => {
                if let Some(control_args) = dataflow_control_args_from_operand(cond, &state)
                    && let Some(observations) = observations.as_deref_mut()
                {
                    observations
                        .option_string_branch_controls
                        .extend(control_args);
                }
            }
            SSAOp::CpuId { dst } => {
                if let Some(observations) = observations.as_deref_mut() {
                    observations.global_loads.push(GlobalLoadObservation {
                        anchor: block.addr,
                        source: LoadedSource {
                            location: SummaryMemoryLocation {
                                region: SummaryMemoryRegion::Unknown,
                                range: None,
                            },
                            size: dst.size,
                            block_addr: block.addr,
                            value_delta: 0,
                        },
                    });
                }
                dataflow_kill_load_source_aliases(dst, &mut state);
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
        summary.global_loads.extend(block_observations.global_loads);
        summary
            .numeric_transforms
            .extend(block_observations.numeric_transforms);
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
    let token_range = evidence.byte_ranges.iter().any(|range| {
        range.lo <= b' '
            || (range.lo <= b'A' && range.hi >= b'Z')
            || (range.lo <= b'a' && range.hi >= b'z')
    });
    let delimiter_values = evidence
        .byte_values
        .iter()
        .filter(|value| !value.is_ascii_digit())
        .count();
    let kind = if numeric_range || digit_values >= 2 {
        NativeParserKind::Numeric
    } else if token_range || delimiter_values >= 2 || evidence.byte_values.len() >= 4 {
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

fn option_string_control_args_by_block(
    func: &SsaArtifact,
    observations: &BTreeMap<u64, BlockWorkerObservations>,
) -> BTreeMap<u64, BTreeSet<usize>> {
    let mut controls = BTreeMap::<u64, BTreeSet<usize>>::new();
    for (block_addr, assumptions) in &func.predicates().block_assumptions {
        for assumption in assumptions {
            let Some(branch_controls) = observations
                .get(&assumption.predecessor)
                .map(|block| &block.option_string_branch_controls)
                .filter(|controls| !controls.is_empty())
            else {
                continue;
            };
            controls
                .entry(*block_addr)
                .or_default()
                .extend(branch_controls.iter().copied());
        }
    }

    for (&branch_addr, block) in observations {
        if block.option_string_branch_controls.is_empty() {
            continue;
        }
        for succ in func.function().successors(branch_addr) {
            controls
                .entry(succ)
                .or_default()
                .extend(block.option_string_branch_controls.iter().copied());
        }
    }
    controls
}

fn option_string_render_summaries(
    func: &SsaArtifact,
    observations: &BTreeMap<u64, BlockWorkerObservations>,
) -> Vec<NativeWorkerSummary> {
    const MIN_INPUT_READS: usize = 4;
    const MIN_OPTION_BYTES: usize = 4;

    let mut input_reads = BTreeMap::<usize, (usize, u64)>::new();
    let mut output_bytes = BTreeMap::<(usize, usize), BTreeSet<u8>>::new();
    let mut output_zeroes = BTreeSet::<(usize, usize)>::new();
    let mut output_anchors = BTreeMap::<(usize, usize), u64>::new();
    let block_controls = option_string_control_args_by_block(func, observations);

    for (block_addr, block) in observations {
        for read in &block.option_string_reads {
            let entry = input_reads.entry(read.arg).or_insert((0, read.anchor));
            entry.0 += 1;
            entry.1 = entry.1.min(read.anchor);
        }
        for write in &block.option_string_writes {
            let mut control_args = write.control_args.clone();
            if let Some(block_control_args) = block_controls.get(block_addr) {
                control_args.extend(block_control_args.iter().copied());
            }
            for input_arg in control_args.into_iter().filter(|arg| *arg != write.arg) {
                let key = (input_arg, write.arg);
                output_anchors
                    .entry(key)
                    .and_modify(|anchor| *anchor = (*anchor).min(write.anchor))
                    .or_insert(write.anchor);
                if write.value == 0 {
                    output_zeroes.insert(key);
                } else if write.value.is_ascii_alphanumeric() {
                    output_bytes.entry(key).or_default().insert(write.value);
                }
            }
        }
    }

    output_bytes
        .into_iter()
        .filter(|(key, bytes)| output_zeroes.contains(key) && bytes.len() >= MIN_OPTION_BYTES)
        .filter_map(|((input_arg, output_arg), _)| {
            let (_, read_anchor) = input_reads
                .get(&input_arg)
                .filter(|(count, _)| *count >= MIN_INPUT_READS)?;
            let anchor = output_anchors
                .get(&(input_arg, output_arg))
                .copied()
                .unwrap_or(func.entry)
                .min(*read_anchor);
            Some(format_render_worker_summary(
                anchor,
                input_arg,
                Some(output_arg),
            ))
        })
        .collect()
}

fn summaries_from_loop_effects(func: &SsaArtifact) -> Vec<NativeWorkerSummary> {
    let observations = collect_block_worker_observations(func);
    let mut summaries = Vec::<NativeWorkerSummary>::new();
    summaries.extend(option_string_render_summaries(func, &observations));
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

        let mut seen_global_loads = BTreeSet::new();
        for load in effect.global_loads {
            if seen_global_loads.insert(load.source.location) {
                match (effect.natural_loop, load.source.location.region) {
                    (true, SummaryMemoryRegion::Global { .. }) => {
                        summaries.push(table_walk_summary_for_island(&effect.island, load.source));
                    }
                    _ => {
                        summaries.push(metadata_probe_worker_summary_for_memory(
                            load.anchor,
                            Some(load.source.location),
                        ));
                    }
                }
            }
        }

        let mut seen_numeric_transforms = BTreeSet::new();
        for transform in effect.numeric_transforms {
            if seen_numeric_transforms.insert((
                transform.dst_arg,
                transform.length_arg,
                transform.accumulator.clone(),
                transform.bits,
                transform.operation,
            )) {
                if effect.natural_loop {
                    summaries.push(numeric_transform_summary_for_island(
                        &effect.island,
                        transform,
                    ));
                } else if has_loopish_or_dispatch_control(func) {
                    summaries.push(numeric_transform_summary(func, transform));
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
    use crate::semantics::SemanticConfidence;

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

        let hash_fold = summaries
            .iter()
            .find(|summary| {
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
            })
            .expect("evidence-first hash fold summary");
        assert_eq!(hash_fold.evidence.tier, SemanticConfidence::Likely);
        assert_eq!(
            hash_fold.evidence.coverage,
            SemanticEvidenceCoverage::Bounded
        );
        assert_eq!(
            hash_fold.evidence.provenance,
            SemanticEvidenceProvenance::Stable
        );
        assert_eq!(
            hash_fold.evidence.reasons,
            vec![SemanticEvidenceReason::SummaryBudget]
        );
    }

    #[test]
    fn classifier_detects_option_string_render_without_name() {
        let arch = aarch64_test_arch();
        let guard = Varnode::unique(0x2f, 1);
        let mut block = R2ILBlock::new(0x4030, 4);
        for idx in 0..4 {
            let loaded = Varnode::unique(0x30 + idx, 1);
            block.push(R2ILOp::Load {
                dst: loaded.clone(),
                space: SpaceId::Ram,
                addr: Varnode::register(0x00, 8),
            });
            if idx == 0 {
                block.push(R2ILOp::IntNotEqual {
                    dst: guard.clone(),
                    a: loaded,
                    b: Varnode::constant(0, 1),
                });
            }
        }
        for byte in [b'b', b'd', b'f', b'g', 0] {
            block.push(R2ILOp::StoreGuarded {
                space: SpaceId::Ram,
                addr: Varnode::register(0x08, 8),
                val: Varnode::constant(u64::from(byte), 1),
                guard: guard.clone(),
                ordering: r2il::MemoryOrdering::Unknown,
            });
        }
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("option render SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let render = summaries
            .iter()
            .find(|summary| {
                matches!(summary.kind, NativeWorkerSummaryKind::FormatRender)
                    && matches!(
                        summary.memory.map(|memory| memory.region),
                        Some(SummaryMemoryRegion::Arg { index: 0 })
                    )
                    && matches!(
                        summary.dst.map(|dst| dst.region),
                        Some(SummaryMemoryRegion::Arg { index: 1 })
                    )
            })
            .expect("structural option string render summary");
        assert_eq!(render.evidence.tier, SemanticConfidence::Likely);
        assert_eq!(
            render.evidence.reasons,
            vec![SemanticEvidenceReason::SummaryBudget]
        );
        assert!(
            !render
                .evidence
                .reasons
                .contains(&SemanticEvidenceReason::NameHint)
        );
    }

    #[test]
    fn classifier_rejects_uncorrelated_option_reads_and_writes() {
        let arch = aarch64_test_arch();
        let mut block = R2ILBlock::new(0x4038, 4);
        for idx in 0..4 {
            let loaded = Varnode::unique(0x38 + idx, 1);
            block.push(R2ILOp::Load {
                dst: loaded,
                space: SpaceId::Ram,
                addr: Varnode::register(0x00, 8),
            });
        }
        for byte in [b'b', b'd', b'f', b'g', 0] {
            block.push(R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::register(0x08, 8),
                val: Varnode::constant(u64::from(byte), 1),
            });
        }
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("uncorrelated option SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(
            summaries
                .iter()
                .all(|summary| !matches!(summary.kind, NativeWorkerSummaryKind::FormatRender)),
            "uncorrelated reads/writes must not produce option-string summary: {summaries:?}"
        );
    }

    #[test]
    fn key_to_opts_name_alone_does_not_create_summary() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x4030),
            Some("dbg.key_to_opts".to_string()),
        );

        assert!(!has_native_worker_summary_family("dbg.key_to_opts"));
        assert!(
            summaries_from_interproc_summary_unbounded(0x4030, &summary)
                .iter()
                .all(|summary| !matches!(summary.kind, NativeWorkerSummaryKind::FormatRender))
        );
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
    fn classifier_detects_token_parser_loop_from_whitespace_range() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x60, 1);
        let pred = Varnode::unique(0x61, 1);
        let mut block = R2ILBlock::new(0x4060, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntLessEqual {
            dst: pred.clone(),
            a: loaded,
            b: Varnode::constant(0x20, 1),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4060, 8),
            cond: pred,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("token parser SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        let parser = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
            .and_then(|summary| summary.parser.as_ref())
            .expect("token parser summary");
        assert_eq!(parser.kind, NativeParserKind::Token);
        assert_eq!(parser.cursor_arg, Some(0));
    }

    #[test]
    fn classifier_detects_path_walk_from_path_delimiter_scan() {
        let arch = aarch64_test_arch();
        let loaded = Varnode::unique(0x70, 1);
        let pred = Varnode::unique(0x71, 1);
        let mut block = R2ILBlock::new(0x4070, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0x00, 8),
        });
        block.push(R2ILOp::IntEqual {
            dst: pred.clone(),
            a: loaded,
            b: Varnode::constant(u64::from(b'/'), 1),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x4070, 8),
            cond: pred,
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("path scan SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::PathWalk)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
    }

    #[test]
    fn classifier_detects_table_walk_from_global_loop_load() {
        let arch = aarch64_test_arch();
        let mut block = R2ILBlock::new(0x4080, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x80, 4),
            space: SpaceId::Ram,
            addr: Varnode::ram(0x9000, 8),
        });
        block.push(R2ILOp::Branch {
            target: Varnode::constant(0x4080, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("table walk SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::TableWalk)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Global { address: 0x9000 })
                )
                && summary.loop_summary.is_some()
        }));
    }

    #[test]
    fn classifier_detects_metadata_probe_from_single_global_load() {
        let arch = aarch64_test_arch();
        let mut block = R2ILBlock::new(0x4090, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x90, 4),
            space: SpaceId::Ram,
            addr: Varnode::ram(0xa000, 8),
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("metadata probe SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::MetadataProbe)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Global { address: 0xa000 })
                )
        }));
    }

    #[test]
    fn classifier_detects_numeric_transform_loop_without_name() {
        let arch = aarch64_test_arch();
        let product = Varnode::unique(0xa0, 8);
        let pred = Varnode::unique(0xa1, 1);
        let mut block = R2ILBlock::new(0x40a0, 4);
        block.push(R2ILOp::IntMult {
            dst: product.clone(),
            a: Varnode::register(0x00, 8),
            b: Varnode::constant(3, 8),
        });
        block.push(R2ILOp::IntNotEqual {
            dst: pred.clone(),
            a: product,
            b: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::CBranch {
            target: Varnode::constant(0x40a0, 8),
            cond: pred,
        });
        let artifact =
            SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("numeric transform SSA");

        let summaries =
            bounded_worker_summaries(classify_function_worker_summaries_unbounded(&artifact));

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::NumericTransform)
                && summary.loop_summary.as_ref().is_some_and(|loop_summary| {
                    loop_summary.header == 0x40a0
                        && loop_summary
                            .fold
                            .as_ref()
                            .is_some_and(|fold| fold.bits == 64)
                })
        }));
    }

    #[test]
    fn interproc_structural_summary_uses_effects_without_name() {
        let mut summary =
            FunctionSemanticSummary::unknown(r2ssa::InterprocFunctionId(0x6110), None);
        summary.return_relation = SummaryReturnRelation::HeapAlloc;
        summary.memory_effects.push(SummaryMemoryEffect {
            kind: SummaryMemoryEffectKind::Free,
            location: arg_location(0),
        });
        summary.memory_effects.push(SummaryMemoryEffect {
            kind: SummaryMemoryEffectKind::Read,
            location: SummaryMemoryLocation {
                region: SummaryMemoryRegion::Global { address: 0xb000 },
                range: Some(SummaryMemoryRange {
                    offset_lo: 0,
                    offset_hi: 3,
                    width: Some(4),
                }),
            },
        });
        summary.reads_global_memory = true;

        let summaries = summaries_from_interproc_summary_unbounded(0x6110, &summary);

        assert!(
            summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Allocation))
        );
        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Lifetime)
                && matches!(
                    summary.lifetime,
                    Some(SummaryLifetimeEffect {
                        arg: 0,
                        op: SummaryLifetimeOp::Free,
                    })
                )
        }));
        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::MetadataProbe)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Global { address: 0xb000 })
                )
        }));
    }

    #[test]
    fn dataflow_alias_index_uses_family_lookup_and_kills_stale_aliases() {
        let eax_0 = SSAVar::new("EAX", 0, 4);
        let eax_1 = SSAVar::new("EAX", 1, 4);
        let al_0 = SSAVar::new("AL", 0, 1);
        let first = LoadedSource {
            location: arg_byte_location(0),
            size: 4,
            block_addr: 0x4100,
            value_delta: 0,
        };
        let second = LoadedSource {
            location: arg_byte_location(1),
            size: 4,
            block_addr: 0x4110,
            value_delta: 0,
        };
        let mut state = WorkerDataflowState::default();

        insert_exact_load_source_value(&mut state, &eax_0, first);
        assert_eq!(dataflow_loaded_source(&al_0, &state), Some(first));

        dataflow_kill_load_source_aliases(&eax_1, &mut state);
        assert_eq!(dataflow_loaded_source(&al_0, &state), None);

        insert_exact_load_source_value(&mut state, &eax_1, second);
        assert_eq!(dataflow_loaded_source(&al_0, &state), Some(second));
    }

    #[test]
    fn dataflow_alias_index_rebuilds_after_join_conflict() {
        let eax = SSAVar::new("EAX", 0, 4);
        let al = SSAVar::new("AL", 0, 1);
        let mut left = WorkerDataflowState::default();
        let mut right = WorkerDataflowState::default();

        insert_exact_load_source_value(
            &mut left,
            &eax,
            LoadedSource {
                location: arg_byte_location(0),
                size: 4,
                block_addr: 0x4120,
                value_delta: 0,
            },
        );
        insert_exact_load_source_value(
            &mut right,
            &eax,
            LoadedSource {
                location: arg_byte_location(1),
                size: 4,
                block_addr: 0x4130,
                value_delta: 0,
            },
        );

        assert!(join_worker_state(&mut left, &right));
        assert_eq!(dataflow_loaded_source(&al, &left), None);
    }

    #[test]
    fn interproc_summary_adds_hash_pattern_and_getopt_families() {
        let md5 = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5000),
            Some("sym._md5_process_block".to_string()),
        );
        let fnmatch = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5010),
            Some("sym._internal_fnwmatch".to_string()),
        );
        let getopt = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5020),
            Some("sym._getopt_internal_r".to_string()),
        );

        let md5_summaries = summaries_from_interproc_summary_unbounded(0x5000, &md5);
        let fnmatch_summaries = summaries_from_interproc_summary_unbounded(0x5010, &fnmatch);
        let getopt_summaries = summaries_from_interproc_summary_unbounded(0x5020, &getopt);

        assert!(md5_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::HashFold)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(1)))
                && matches!(
                    summary.dst.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 2 })
                )
                && summary
                    .loop_summary
                    .as_ref()
                    .and_then(|loop_summary| loop_summary.fold.as_ref())
                    .is_some_and(|fold| {
                        fold.accumulator == "md5_state"
                            && fold.bits == 32
                            && fold.operation == NativeWorkerFoldOperation::RotateMix
                    })
        }));
        assert!(fnmatch_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
        assert!(fnmatch_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::StringScan)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
        }));
        assert!(getopt_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 2 })
                )
        }));
        assert!(getopt_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::TableWalk)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 3 })
                )
        }));
    }

    #[test]
    fn interproc_summary_adds_broad_coreutils_blocker_families() {
        let digest = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5030),
            Some("sym.digest_file.isra.0".to_string()),
        );
        let binop = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5040),
            Some("sym.binop".to_string()),
        );
        let quote = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5050),
            Some("sym.quotearg_n_options".to_string()),
        );
        let mbrtowc = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5060),
            Some("sym.rpl_mbrtowc".to_string()),
        );
        let write_counts = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5070),
            Some("dbg.write_counts".to_string()),
        );
        let verror = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5080),
            Some("dbg.verror_at_line".to_string()),
        );
        let argmatch = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5090),
            Some("dbg.argmatch".to_string()),
        );
        let renameatu = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50a0),
            Some("dbg.renameatu".to_string()),
        );
        let streamsavedir = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50b0),
            Some("sym.streamsavedir".to_string()),
        );
        let quote_alloc = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50c0),
            Some("sym.quotearg_alloc_mem".to_string()),
        );
        let xpalloc = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50d0),
            Some("sym.xpalloc".to_string()),
        );
        let version = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x50e0),
            Some("sym.version_etc_va".to_string()),
        );

        let digest_summaries = summaries_from_interproc_summary_unbounded(0x5030, &digest);
        let binop_summaries = summaries_from_interproc_summary_unbounded(0x5040, &binop);
        let quote_summaries = summaries_from_interproc_summary_unbounded(0x5050, &quote);
        let mbrtowc_summaries = summaries_from_interproc_summary_unbounded(0x5060, &mbrtowc);
        let write_counts_summaries =
            summaries_from_interproc_summary_unbounded(0x5070, &write_counts);
        let verror_summaries = summaries_from_interproc_summary_unbounded(0x5080, &verror);
        let argmatch_summaries = summaries_from_interproc_summary_unbounded(0x5090, &argmatch);
        let renameatu_summaries = summaries_from_interproc_summary_unbounded(0x50a0, &renameatu);
        let streamsavedir_summaries =
            summaries_from_interproc_summary_unbounded(0x50b0, &streamsavedir);
        let quote_alloc_summaries =
            summaries_from_interproc_summary_unbounded(0x50c0, &quote_alloc);
        let xpalloc_summaries = summaries_from_interproc_summary_unbounded(0x50d0, &xpalloc);
        let version_summaries = summaries_from_interproc_summary_unbounded(0x50e0, &version);

        assert!(
            digest_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::HashFold))
        );
        assert!(
            digest_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::RecordStream))
        );
        assert!(
            binop_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
        );
        assert!(
            binop_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::TableWalk))
        );
        let test_or = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5041),
            Some("dbg.or".to_string()),
        );
        let test_or_summaries = summaries_from_interproc_summary_unbounded(0x5041, &test_or);
        assert!(test_or_summaries.iter().all(|summary| {
            matches!(
                summary.memory.map(|location| location.region),
                Some(SummaryMemoryRegion::Global { .. })
            ) && summary.arg_indices().is_empty()
        }));
        assert!(quote_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::StringScan)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
        }));
        assert!(
            quote_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::FormatRender))
        );
        assert!(mbrtowc_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(2)))
        }));
        assert!(
            write_counts_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::FormatRender))
        );
        assert!(
            write_counts_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::OutputStream))
        );
        assert!(verror_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::DiagnosticWrapper)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 4 })
                )
        }));
        assert!(argmatch_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::TableWalk)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
        }));
        assert!(renameatu_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::PathWalk)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 3 })
                )
        }));
        assert!(
            streamsavedir_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::DirectoryTraversal))
        );
        assert!(
            quote_alloc_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Allocation))
        );
        assert!(quote_alloc_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::TableWalk)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 3 })
                )
        }));
        assert!(xpalloc_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Allocation)
                && matches!(
                    summary.allocation,
                    Some(SummaryAllocationEffect {
                        size_arg: Some(4),
                        zeroed: false,
                    })
                )
        }));
        assert!(
            version_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::FormatRender))
        );
    }

    #[test]
    fn interproc_summary_adds_named_worker_families() {
        let diagnose = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5100),
            Some("sym.diagnose".to_string()),
        );
        let printf_fetchargs = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5200),
            Some("sym.printf_fetchargs".to_string()),
        );
        let usage = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5300),
            Some("dbg.usage".to_string()),
        );
        let keycompare = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5400),
            Some("dbg.keycompare".to_string()),
        );
        let readlinebuffer = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5500),
            Some("sym.readlinebuffer_delim".to_string()),
        );
        let quotearg = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5600),
            Some("sym.quotearg_buffer_restyled".to_string()),
        );
        let mbrtoc32 = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5700),
            Some("sym.rpl_mbrtoc32".to_string()),
        );
        let xstrtoumax = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5800),
            Some("dbg.xstrtoumax".to_string()),
        );
        let vstrtoimax = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5801),
            Some("dbg.vstrtoimax".to_string()),
        );
        let copy_file_data = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5900),
            Some("sym.copy_file_data".to_string()),
        );
        let copy_with_unblock = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5901),
            Some("dbg.copy_with_unblock".to_string()),
        );
        let iwrite = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5902),
            Some("sym.iwrite.constprop.0".to_string()),
        );
        let translate_charset = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5903),
            Some("dbg.translate_charset".to_string()),
        );
        let invalidate_cache = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5904),
            Some("dbg.invalidate_cache".to_string()),
        );
        let parse_long_options = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5905),
            Some("dbg.parse_long_options".to_string()),
        );
        let parse_gnu_options = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5906),
            Some("dbg.parse_gnu_standard_options_only".to_string()),
        );
        let human_options = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5907),
            Some("dbg.human_options".to_string()),
        );
        let parse_integer = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5908),
            Some("dbg.parse_integer".to_string()),
        );
        let synchronize_output = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5909),
            Some("dbg.synchronize_output".to_string()),
        );
        let copy_internal = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5a00),
            Some("sym.copy_internal".to_string()),
        );
        let fts_read = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5b00),
            Some("sym.rpl_fts_read".to_string()),
        );
        let fts_close = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5b01),
            Some("sym.rpl_fts_close".to_string()),
        );
        let changedir = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5c00),
            Some("sym.fts_safe_changedir".to_string()),
        );
        let cut_fields = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5d00),
            Some("dbg.cut_fields_bytesearch".to_string()),
        );
        let print_long = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5e00),
            Some("dbg.print_long_format".to_string()),
        );
        let sort_merge = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x5f00),
            Some("dbg.mergefps".to_string()),
        );
        let main_summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x6000),
            Some("dbg.main".to_string()),
        );

        let diagnose_summaries = summaries_from_interproc_summary_unbounded(0x5100, &diagnose);
        let fetch_summaries = summaries_from_interproc_summary_unbounded(0x5200, &printf_fetchargs);
        let usage_summaries = summaries_from_interproc_summary_unbounded(0x5300, &usage);
        let keycompare_summaries = summaries_from_interproc_summary_unbounded(0x5400, &keycompare);
        let readlinebuffer_summaries =
            summaries_from_interproc_summary_unbounded(0x5500, &readlinebuffer);
        let quotearg_summaries = summaries_from_interproc_summary_unbounded(0x5600, &quotearg);
        let mbrtoc32_summaries = summaries_from_interproc_summary_unbounded(0x5700, &mbrtoc32);
        let xstrtoumax_summaries = summaries_from_interproc_summary_unbounded(0x5800, &xstrtoumax);
        let vstrtoimax_summaries = summaries_from_interproc_summary_unbounded(0x5801, &vstrtoimax);
        let copy_file_summaries =
            summaries_from_interproc_summary_unbounded(0x5900, &copy_file_data);
        let copy_with_unblock_summaries =
            summaries_from_interproc_summary_unbounded(0x5901, &copy_with_unblock);
        let iwrite_summaries = summaries_from_interproc_summary_unbounded(0x5902, &iwrite);
        let translate_charset_summaries =
            summaries_from_interproc_summary_unbounded(0x5903, &translate_charset);
        let invalidate_cache_summaries =
            summaries_from_interproc_summary_unbounded(0x5904, &invalidate_cache);
        let parse_long_options_summaries =
            summaries_from_interproc_summary_unbounded(0x5905, &parse_long_options);
        let parse_gnu_options_summaries =
            summaries_from_interproc_summary_unbounded(0x5906, &parse_gnu_options);
        let human_options_summaries =
            summaries_from_interproc_summary_unbounded(0x5907, &human_options);
        let parse_integer_summaries =
            summaries_from_interproc_summary_unbounded(0x5908, &parse_integer);
        let synchronize_output_summaries =
            summaries_from_interproc_summary_unbounded(0x5909, &synchronize_output);
        let copy_internal_summaries =
            summaries_from_interproc_summary_unbounded(0x5a00, &copy_internal);
        let fts_read_summaries = summaries_from_interproc_summary_unbounded(0x5b00, &fts_read);
        let fts_close_summaries = summaries_from_interproc_summary_unbounded(0x5b01, &fts_close);
        let changedir_summaries = summaries_from_interproc_summary_unbounded(0x5c00, &changedir);
        let cut_field_summaries = summaries_from_interproc_summary_unbounded(0x5d00, &cut_fields);
        let print_long_summaries = summaries_from_interproc_summary_unbounded(0x5e00, &print_long);
        let sort_merge_summaries = summaries_from_interproc_summary_unbounded(0x5f00, &sort_merge);
        let main_summaries = summaries_from_interproc_summary_unbounded(0x6000, &main_summary);

        assert!(diagnose_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::DiagnosticWrapper)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
        }));
        assert!(fetch_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::FormatArgumentFetch)
                && matches!(
                    summary.src.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(
                    summary.dst.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
        }));
        assert!(usage_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::DiagnosticWrapper)
                && summary.memory.is_none()
        }));
        assert!(keycompare_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::TableWalk)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
        assert!(readlinebuffer_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.dst.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
                && summary
                    .parser
                    .as_ref()
                    .is_some_and(|parser| parser.kind == NativeParserKind::Token)
        }));
        assert!(quotearg_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::StringScan)
                && matches!(
                    summary.dst.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 2 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(3)))
        }));
        assert!(mbrtoc32_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.dst.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(2)))
        }));
        assert!(xstrtoumax_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && summary
                    .parser
                    .as_ref()
                    .is_some_and(|parser| parser.kind == NativeParserKind::Numeric)
        }));
        assert!(vstrtoimax_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && summary
                    .parser
                    .as_ref()
                    .is_some_and(|parser| parser.kind == NativeParserKind::Numeric)
        }));
        assert!(copy_file_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::FileTransfer)
                && matches!(
                    summary.src.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(
                    summary.dst.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 4 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(8)))
        }));
        assert!(copy_with_unblock_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::OutputStream)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(1)))
        }));
        assert!(iwrite_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::OutputStream)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
                && matches!(summary.len, Some(SummaryTransferLength::Arg(2)))
        }));
        assert!(translate_charset_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::TableWalk)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
        assert!(invalidate_cache_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::MetadataProbe)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
        assert!(parse_long_options_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
                && summary
                    .parser
                    .as_ref()
                    .is_some_and(|parser| parser.kind == NativeParserKind::Token)
        }));
        assert!(parse_gnu_options_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 1 })
                )
                && summary
                    .parser
                    .as_ref()
                    .is_some_and(|parser| parser.kind == NativeParserKind::Token)
        }));
        assert!(human_options_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && summary
                    .parser
                    .as_ref()
                    .is_some_and(|parser| parser.kind == NativeParserKind::Numeric)
        }));
        assert!(parse_integer_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Parser)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
                && summary
                    .parser
                    .as_ref()
                    .is_some_and(|parser| parser.kind == NativeParserKind::Numeric)
        }));
        assert!(
            synchronize_output_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Synchronization))
        );
        assert!(copy_internal_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::PathWalk)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
        assert!(
            copy_internal_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::FileTransfer))
        );
        assert!(fts_read_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::DirectoryTraversal)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
        assert!(fts_close_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::DirectoryTraversal)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
        assert!(changedir_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::PathWalk)
                && matches!(
                    summary.memory.map(|location| location.region),
                    Some(SummaryMemoryRegion::Arg { index: 3 })
                )
        }));
        assert!(
            cut_field_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::RecordStream))
        );
        assert!(
            cut_field_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::FieldSelection))
        );
        assert!(
            cut_field_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::OutputStream))
        );
        assert!(
            print_long_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::FormatRender))
        );
        assert!(
            print_long_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::MetadataProbe))
        );
        assert!(
            sort_merge_summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::SortMerge))
        );
        assert!(main_summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::ProgramOrchestrator)
                && summary.memory.is_none()
                && summary.loop_summary.is_none()
        }));
    }

    #[test]
    fn interproc_summary_adds_broad_hard_failure_worker_families() {
        let cases: &[(&str, &[NativeWorkerSummaryKind])] = &[
            (
                "dbg.__xargmatch_internal",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::DiagnosticWrapper,
                ],
            ),
            (
                "dbg.cut_file",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::FieldSelection,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.memchr2",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.hash_print_statistics",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "sym.hash_insert_if_absent",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::HashFold,
                ],
            ),
            (
                "dbg.hash_lookup",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::HashFold,
                ],
            ),
            (
                "dbg.hash_get_entries",
                &[NativeWorkerSummaryKind::TableWalk],
            ),
            ("dbg.raw_hasher", &[NativeWorkerSummaryKind::HashFold]),
            (
                "sym.sha256_process_block",
                &[NativeWorkerSummaryKind::HashFold],
            ),
            (
                "sym.print_filename.part.0",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.file_name_concat",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.wc_lines_avx2",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::HashFold,
                ],
            ),
            (
                "dbg.full_read",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::MemoryRead,
                ],
            ),
            (
                "dbg.full_write",
                &[
                    NativeWorkerSummaryKind::OutputStream,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.copy_with_block",
                &[
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.isaac_refill",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::HashFold,
                ],
            ),
            (
                "dbg.sort_files",
                &[
                    NativeWorkerSummaryKind::SortMerge,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "dbg.stream_open",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.same_nameat",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "sym.mcel_scan",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.set_process_security_ctx",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg.strmode",
                &[
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.do_statx",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::PathWalk,
                ],
            ),
            (
                "dbg.mfile_name_concat",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.getuidbyname",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.init_node",
                &[
                    NativeWorkerSummaryKind::SortMerge,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "sym.mcel_scant",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.filenvercmp",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "sym.print_file_name_and_frills.isra.0",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::FormatRender,
                ],
            ),
            (
                "dbg.try_tempname_len",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.write_bytes",
                &[
                    NativeWorkerSummaryKind::OutputStream,
                    NativeWorkerSummaryKind::RecordStream,
                ],
            ),
            (
                "dbg.hash_clear",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Lifetime,
                ],
            ),
            (
                "dbg.hash_free",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Lifetime,
                ],
            ),
            (
                "sym.limfield.isra.0",
                &[
                    NativeWorkerSummaryKind::FieldSelection,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.fts_sort",
                &[
                    NativeWorkerSummaryKind::SortMerge,
                    NativeWorkerSummaryKind::DirectoryTraversal,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            ("dbg.xnumtoumax", &[NativeWorkerSummaryKind::Parser]),
            ("dbg.parse_field_count", &[NativeWorkerSummaryKind::Parser]),
            (
                "dbg.parse_symbols",
                &[
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "sym.leave_dir",
                &[
                    NativeWorkerSummaryKind::DirectoryTraversal,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "sym.find_entry",
                &[
                    NativeWorkerSummaryKind::DirectoryTraversal,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "sym.rpl_fts_children",
                &[NativeWorkerSummaryKind::DirectoryTraversal],
            ),
            (
                "dbg.decode_preserve_arg",
                &[
                    NativeWorkerSummaryKind::Parser,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg.areadlink_with_size",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "dbg.mbsnwidth",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Parser,
                ],
            ),
            (
                "dbg.file_escape",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "dbg.zaptemp",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::Lifetime,
                ],
            ),
            (
                "dbg.sequential_sort",
                &[
                    NativeWorkerSummaryKind::SortMerge,
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Allocation,
                ],
            ),
            (
                "dbg.open_input_files",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::RecordStream,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.get_meminfo",
                &[
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.randread_new",
                &[
                    NativeWorkerSummaryKind::PathWalk,
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::Allocation,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.randread",
                &[
                    NativeWorkerSummaryKind::TableWalk,
                    NativeWorkerSummaryKind::MemoryWrite,
                    NativeWorkerSummaryKind::HashFold,
                ],
            ),
            (
                "dbg.gregorian_to_persian",
                &[NativeWorkerSummaryKind::NumericTransform],
            ),
            (
                "dbg.next_prime",
                &[NativeWorkerSummaryKind::NumericTransform],
            ),
            (
                "dbg.num_processors",
                &[
                    NativeWorkerSummaryKind::NumericTransform,
                    NativeWorkerSummaryKind::MetadataProbe,
                ],
            ),
            (
                "dbg.rpl_pipe2",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.cycle_check",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::MemoryRead,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            ("dbg.copy_bytes", &[NativeWorkerSummaryKind::MemoryTransfer]),
            (
                "sym.oprintf_.constprop.0",
                &[
                    NativeWorkerSummaryKind::FormatRender,
                    NativeWorkerSummaryKind::OutputStream,
                ],
            ),
            (
                "dbg.setlocale_null_r_unlocked",
                &[
                    NativeWorkerSummaryKind::MetadataProbe,
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::MemoryWrite,
                ],
            ),
            (
                "dbg.gettext_quote",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::TableWalk,
                ],
            ),
            (
                "dbg.set_program_name",
                &[
                    NativeWorkerSummaryKind::StringScan,
                    NativeWorkerSummaryKind::Synchronization,
                ],
            ),
        ];

        for (idx, (name, expected_kinds)) in cases.iter().enumerate() {
            let summary = FunctionSemanticSummary::unknown(
                r2ssa::InterprocFunctionId(0x7000 + idx as u64),
                Some((*name).to_string()),
            );
            let summaries =
                summaries_from_interproc_summary_unbounded(0x7000 + idx as u64, &summary);
            for expected_kind in *expected_kinds {
                assert!(
                    summaries
                        .iter()
                        .any(|summary| summary.kind == *expected_kind),
                    "missing {expected_kind:?} for {name}: {summaries:?}"
                );
            }
        }
    }

    #[test]
    fn native_worker_family_predicate_recognizes_summary_owned_names() {
        assert!(has_native_worker_summary_family("dbg.readlinebuffer_delim"));
        assert!(has_native_worker_summary_family("sym.printf_fetchargs"));
        assert!(has_native_worker_summary_family("sym.oprintf_.constprop.0"));
        assert!(has_native_worker_summary_family(
            "sym.quotearg_buffer_restyled"
        ));
        assert!(has_native_worker_summary_family("sym._md5_process_block"));
        assert!(has_native_worker_summary_family("sym._internal_fnwmatch"));
        assert!(has_native_worker_summary_family("sym._getopt_internal_r"));
        assert!(has_native_worker_summary_family("sym.digest_file.isra.0"));
        assert!(has_native_worker_summary_family("sym.binop"));
        assert!(has_native_worker_summary_family("dbg.write_counts"));
        assert!(has_native_worker_summary_family("dbg.verror_at_line"));
        assert!(has_native_worker_summary_family("dbg.argmatch"));
        assert!(has_native_worker_summary_family("dbg.print_xfer_stats"));
        assert!(has_native_worker_summary_family("sym.quotearg_n_options"));
        assert!(has_native_worker_summary_family("sym.quotearg_alloc_mem"));
        assert!(has_native_worker_summary_family(
            "sym.clone_quoting_options"
        ));
        assert!(has_native_worker_summary_family("sym.version_etc_va"));
        assert!(has_native_worker_summary_family("dbg.renameatu"));
        assert!(has_native_worker_summary_family("dbg.streamsavedir"));
        assert!(has_native_worker_summary_family("sym.xpalloc"));
        assert!(has_native_worker_summary_family("sym.rpl_mbrtowc"));
        assert!(has_native_worker_summary_family("sym.rpl_fopen"));
        assert!(has_native_worker_summary_family("dbg.openat_safer"));
        assert!(has_native_worker_summary_family("dbg.rpl_nanosleep"));
        assert!(has_native_worker_summary_family("entry.init0"));
        assert!(has_native_worker_summary_family("sym.copy_file_data"));
        assert!(has_native_worker_summary_family("dbg.copy_with_unblock"));
        assert!(has_native_worker_summary_family("dbg.copy_bytes"));
        assert!(has_native_worker_summary_family("sym.iwrite.constprop.0"));
        assert!(has_native_worker_summary_family("dbg.translate_charset"));
        assert!(has_native_worker_summary_family("dbg.invalidate_cache"));
        assert!(has_native_worker_summary_family("dbg.parse_long_options"));
        assert!(has_native_worker_summary_family(
            "dbg.parse_gnu_standard_options_only"
        ));
        assert!(has_native_worker_summary_family("dbg.human_options"));
        assert!(has_native_worker_summary_family("dbg.parse_integer"));
        assert!(has_native_worker_summary_family("dbg.parse_number"));
        assert!(has_native_worker_summary_family("dbg.traverse_raw_number"));
        assert!(has_native_worker_summary_family("dbg.synchronize_output"));
        assert!(has_native_worker_summary_family("sym.rpl_fts_read"));
        assert!(has_native_worker_summary_family("sym.rpl_fts_close"));
        assert!(has_native_worker_summary_family("sym.fts_safe_changedir"));
        assert!(has_native_worker_summary_family(
            "dbg.cut_fields_bytesearch"
        ));
        assert!(has_native_worker_summary_family("dbg.print_long_format"));
        assert!(has_native_worker_summary_family("dbg.mergefps"));
        assert!(has_native_worker_summary_family("dbg.main"));
        assert!(has_native_worker_summary_family("dbg.__xargmatch_internal"));
        assert!(has_native_worker_summary_family("dbg.cut_file"));
        assert!(has_native_worker_summary_family("dbg.cut_bytes"));
        assert!(has_native_worker_summary_family("dbg.memchr2"));
        assert!(has_native_worker_summary_family(
            "dbg.hash_print_statistics"
        ));
        assert!(has_native_worker_summary_family(
            "sym.hash_insert_if_absent"
        ));
        assert!(has_native_worker_summary_family("sym.hash_rehash"));
        assert!(has_native_worker_summary_family("dbg.excise"));
        assert!(has_native_worker_summary_family(
            "sym.print_filename.part.0"
        ));
        assert!(has_native_worker_summary_family("dbg.wc_lines_avx512"));
        assert!(has_native_worker_summary_family("dbg.sort_files"));
        assert!(has_native_worker_summary_family("dbg.stream_open"));
        assert!(has_native_worker_summary_family("dbg.same_nameat"));
        assert!(has_native_worker_summary_family("sym.mcel_scan"));
        assert!(has_native_worker_summary_family("sym.mcel_cmp"));
        assert!(has_native_worker_summary_family(
            "dbg.set_process_security_ctx"
        ));
        assert!(has_native_worker_summary_family("dbg.strmode"));
        assert!(has_native_worker_summary_family("dbg.do_statx"));
        assert!(has_native_worker_summary_family("dbg.get_dir_status"));
        assert!(has_native_worker_summary_family("dbg.is_utf8_charset"));
        assert!(has_native_worker_summary_family("dbg.mfile_name_concat"));
        assert!(has_native_worker_summary_family("dbg.getuidbyname"));
        assert!(has_native_worker_summary_family("dbg.init_node"));
        assert!(has_native_worker_summary_family("dbg.mergefiles"));
        assert!(has_native_worker_summary_family("dbg.xnrealloc"));
        assert!(has_native_worker_summary_family("sym.mcel_scant"));
        assert!(has_native_worker_summary_family("dbg.filenvercmp"));
        assert!(has_native_worker_summary_family(
            "sym.print_file_name_and_frills.isra.0"
        ));
        assert!(has_native_worker_summary_family("dbg.try_tempname_len"));
        assert!(has_native_worker_summary_family("dbg.close_stdin"));
        assert!(has_native_worker_summary_family("dbg.rpl_fclose"));
        assert!(has_native_worker_summary_family("dbg.write_bytes"));
        assert!(has_native_worker_summary_family("dbg.hash_clear"));
        assert!(has_native_worker_summary_family("dbg.hash_free"));
        assert!(has_native_worker_summary_family("sym.limfield.isra.0"));
        assert!(has_native_worker_summary_family("dbg.fts_sort"));
        assert!(has_native_worker_summary_family("dbg.xnumtoumax"));
        assert!(has_native_worker_summary_family("sym.leave_dir"));
        assert!(has_native_worker_summary_family("sym.find_entry"));
        assert!(has_native_worker_summary_family("dbg.decode_preserve_arg"));
        assert!(has_native_worker_summary_family("dbg.areadlink_with_size"));
        assert!(has_native_worker_summary_family("dbg.mbsnwidth"));
        assert!(has_native_worker_summary_family(
            "sym.print_filename.part.0"
        ));
        assert!(has_native_worker_summary_family("dbg.prompt.constprop.0"));
        assert!(has_native_worker_summary_family("dbg.file_escape"));
        assert!(has_native_worker_summary_family("dbg.zaptemp"));
        assert!(has_native_worker_summary_family("dbg.sequential_sort"));
        assert!(has_native_worker_summary_family("dbg.open_input_files"));
        assert!(has_native_worker_summary_family("dbg.get_meminfo"));
        assert!(has_native_worker_summary_family("dbg.randread_new"));
        assert!(has_native_worker_summary_family("dbg.randread"));
        assert!(has_native_worker_summary_family(
            "dbg._gl_scratch_buffer_grow_preserve"
        ));
        assert!(has_native_worker_summary_family("dbg.argv_iter"));
        assert!(has_native_worker_summary_family("dbg.argv_iter_init_argv"));
        assert!(has_native_worker_summary_family(
            "dbg.argv_iter_init_stream"
        ));
        assert!(has_native_worker_summary_family("dbg.gregorian_to_persian"));
        assert!(has_native_worker_summary_family(
            "dbg.gregorian_to_ethiopian"
        ));
        assert!(has_native_worker_summary_family("dbg.next_prime"));
        assert!(has_native_worker_summary_family("dbg.num_processors"));
        assert!(has_native_worker_summary_family("sym.rpl_pipe2"));
        assert!(has_native_worker_summary_family("dbg.cycle_check_init"));
        assert!(has_native_worker_summary_family("dbg.cycle_check"));
        assert!(has_native_worker_summary_family("dbg.fdutimensat"));
        assert!(has_native_worker_summary_family(
            "dbg.setlocale_null_r_unlocked"
        ));
        assert!(has_native_worker_summary_family("dbg.gettext_quote"));
        assert!(has_native_worker_summary_family("dbg.set_program_name"));
        assert!(has_native_worker_summary_family("dbg.mcel_scanz"));
        assert!(has_native_worker_summary_family("dbg.nstrftime"));
        assert!(has_native_worker_summary_family("dbg.mktime_z"));
        assert!(has_native_worker_summary_family(
            "dbg.length_of_file_name_and_frills"
        ));
        assert!(has_native_worker_summary_family("dbg.yesno"));
        assert!(has_native_worker_summary_family("sym.sha256_process_block"));
        assert!(has_native_worker_summary_family("dbg.hash_lookup"));
        assert!(has_native_worker_summary_family("dbg.hash_get_entries"));
        assert!(has_native_worker_summary_family("dbg.raw_hasher"));
        assert!(has_native_worker_summary_family("dbg.parse_field_count"));
        assert!(has_native_worker_summary_family("dbg.parse_symbols"));
        assert!(has_native_worker_summary_family("dbg.file_name_concat"));
        assert!(has_native_worker_summary_family("dbg.rpl_fts_children"));
        assert!(has_native_worker_summary_family("dbg.full_read"));
        assert!(has_native_worker_summary_family("dbg.full_write"));
        assert!(has_native_worker_summary_family("dbg.copy_with_block"));
        assert!(!has_native_worker_summary_family(
            "dbg.test_symbolic_xor_guard"
        ));
    }

    #[test]
    fn named_worker_family_summaries_have_deterministic_bounded_evidence() {
        let names = [
            "dbg.full_write",
            "sym.sha256_process_block",
            "dbg.parse_symbols",
            "dbg.file_name_concat",
            "dbg.rpl_fts_children",
            "dbg.hash_lookup",
            "dbg.full_read",
        ];
        let summaries_for_names = |names: &[&str]| {
            names
                .iter()
                .enumerate()
                .flat_map(|(idx, name)| {
                    let summary = FunctionSemanticSummary::unknown(
                        r2ssa::InterprocFunctionId(0x8000 + idx as u64),
                        Some((*name).to_string()),
                    );
                    summaries_from_interproc_summary_unbounded(0x8000 + idx as u64, &summary)
                })
                .collect::<Vec<_>>()
        };

        let first = bounded_worker_summaries(summaries_for_names(&names));
        let second = bounded_worker_summaries(summaries_for_names(&names));

        assert_eq!(first, second);
        assert!(first.windows(2).all(|pair| {
            native_worker_summary_sort_key(&pair[0]) <= native_worker_summary_sort_key(&pair[1])
        }));
        for summary in first {
            assert_eq!(summary.evidence.tier, SemanticConfidence::Heuristic);
            assert_eq!(summary.evidence.coverage, SemanticEvidenceCoverage::Bounded);
            assert_eq!(
                summary.evidence.provenance,
                SemanticEvidenceProvenance::Ranked
            );
            assert_eq!(
                summary.evidence.ambiguity,
                SemanticEvidenceAmbiguity::Ranked
            );
            assert!(summary.evidence.budget_limited);
            assert_eq!(
                summary.evidence.reasons,
                vec![
                    SemanticEvidenceReason::SummaryBudget,
                    SemanticEvidenceReason::NameHint
                ]
            );
        }
    }

    #[test]
    fn named_hash_fold_family_remains_weak_hint() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x9000),
            Some("dbg.raw_hasher".to_string()),
        );

        let summaries = summaries_from_interproc_summary_unbounded(0x9000, &summary);
        let hash_fold = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::HashFold))
            .expect("named hash fold summary");

        assert_eq!(hash_fold.evidence.tier, SemanticConfidence::Heuristic);
        assert_eq!(
            hash_fold.evidence.provenance,
            SemanticEvidenceProvenance::Ranked
        );
        assert_eq!(
            hash_fold.evidence.ambiguity,
            SemanticEvidenceAmbiguity::Ranked
        );
        assert_eq!(
            hash_fold.evidence.reasons,
            vec![
                SemanticEvidenceReason::SummaryBudget,
                SemanticEvidenceReason::NameHint
            ]
        );
    }

    #[test]
    fn scratch_buffer_growth_summary_is_bounded_name_hint_not_transfer_proof() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x9100),
            Some("dbg._gl_scratch_buffer_grow_preserve".to_string()),
        );

        let summaries = summaries_from_interproc_summary_unbounded(0x9100, &summary);

        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::Allocation)
                && summary
                    .evidence
                    .reasons
                    .contains(&SemanticEvidenceReason::NameHint)
        }));
        assert!(summaries.iter().any(|summary| {
            matches!(summary.kind, NativeWorkerSummaryKind::MemoryWrite)
                && matches!(
                    summary.memory.map(|memory| memory.region),
                    Some(SummaryMemoryRegion::Arg { index: 0 })
                )
        }));
        assert!(
            summaries
                .iter()
                .all(|summary| !matches!(summary.kind, NativeWorkerSummaryKind::MemoryTransfer)),
            "grow_preserve must not claim a copy/preserve transfer without evidence"
        );
    }

    #[test]
    fn argv_iterator_summary_is_bounded_name_hint() {
        let summary = FunctionSemanticSummary::unknown(
            r2ssa::InterprocFunctionId(0x9200),
            Some("dbg.argv_iter".to_string()),
        );

        let summaries = summaries_from_interproc_summary_unbounded(0x9200, &summary);

        let parser = summaries
            .iter()
            .find(|summary| matches!(summary.kind, NativeWorkerSummaryKind::Parser))
            .expect("argv iterator parser summary");
        assert_eq!(parser.evidence.tier, SemanticConfidence::Heuristic);
        assert!(
            parser
                .evidence
                .reasons
                .contains(&SemanticEvidenceReason::NameHint)
        );
        assert!(
            summaries
                .iter()
                .any(|summary| matches!(summary.kind, NativeWorkerSummaryKind::TableWalk))
        );
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
    fn bounded_worker_summaries_keep_named_families_over_generic_memory_effects() {
        let anchor = 0x6000;
        let mut workers = vec![
            record_stream_worker_summary(anchor, 0, None),
            field_selection_worker_summary(anchor, 0, None),
            output_stream_worker_summary(anchor, 0, None),
        ];
        workers.extend((0..(NATIVE_WORKER_SUMMARY_MAX + 8)).map(|index| {
            memory_worker_summary(
                anchor,
                SummaryMemoryEffect {
                    kind: SummaryMemoryEffectKind::Read,
                    location: SummaryMemoryLocation {
                        region: SummaryMemoryRegion::Arg { index },
                        range: None,
                    },
                },
            )
        }));

        let display_workers = bounded_worker_summaries(workers);

        assert_eq!(display_workers.len(), NATIVE_WORKER_SUMMARY_MAX);
        assert!(
            display_workers
                .iter()
                .any(|summary| summary.kind == NativeWorkerSummaryKind::RecordStream)
        );
        assert!(
            display_workers
                .iter()
                .any(|summary| summary.kind == NativeWorkerSummaryKind::FieldSelection)
        );
        assert!(
            display_workers
                .iter()
                .any(|summary| summary.kind == NativeWorkerSummaryKind::OutputStream)
        );
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
