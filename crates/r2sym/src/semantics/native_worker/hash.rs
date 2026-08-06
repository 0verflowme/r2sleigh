use r2ssa::SsaArtifact;

use crate::semantics::{
    NativeWorkerFold, NativeWorkerFoldOperation, NativeWorkerSummary, NativeWorkerSummaryKind,
    NativeWorkerTerminator,
};

use super::{
    LoadedSource, LoopIsland, allocation_role_worker_summary, bounded_evidence,
    format_render_worker_summary, global_lifetime_worker_summary, loop_summary,
    loop_summary_from_island, output_stream_worker_summary, table_walk_worker_summary,
};

pub(super) fn is_hash_table_family_name(name: &str) -> bool {
    name.starts_with("hash_get_")
        || matches!(
            name,
            "hash_clear"
                | "hash_do_for_each"
                | "hash_free"
                | "hash_init"
                | "hash_initialize"
                | "hash_insert"
                | "hash_insert_if_absent"
                | "hash_lookup"
                | "hash_print_statistics"
                | "hash_rehash"
                | "hash_remove"
                | "hash_reset_tuning"
                | "hash_table_ok"
        )
}

pub(super) fn hash_table_worker_summaries(
    anchor: u64,
    table_arg: usize,
    key_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let _ = key_arg;
    vec![table_walk_worker_summary(anchor, table_arg)]
}

pub(super) fn hash_table_family_worker_summaries(
    anchor: u64,
    name: &str,
) -> Vec<NativeWorkerSummary> {
    match name {
        "hash_initialize" | "hash_init" | "hash_rehash" => vec![
            table_walk_worker_summary(anchor, 0),
            allocation_role_worker_summary(anchor, None, false),
        ],
        "hash_insert" | "hash_insert_if_absent" | "hash_lookup" | "hash_remove" => {
            hash_table_worker_summaries(anchor, 0, Some(1))
        }
        "hash_clear" | "hash_free" => vec![
            table_walk_worker_summary(anchor, 0),
            global_lifetime_worker_summary(anchor),
        ],
        "hash_print_statistics" => hash_statistics_worker_summaries(anchor),
        _ if name.starts_with("hash_get_")
            || matches!(
                name,
                "hash_do_for_each" | "hash_reset_tuning" | "hash_table_ok"
            ) =>
        {
            vec![table_walk_worker_summary(anchor, 0)]
        }
        _ => Vec::new(),
    }
}

pub(super) fn hash_statistics_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 1, None),
        output_stream_worker_summary(anchor, 1, None),
    ]
}

fn source_access_width(source: LoadedSource) -> u32 {
    source
        .location
        .range
        .and_then(|range| range.width)
        .unwrap_or(source.size)
}

pub(super) fn hash_fold_summary(
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
                bits: source_access_width(source).saturating_mul(8),
                operation,
                predicate: None,
                init: None,
                multiplier: None,
                byte_transform: None,
            }),
        )),
        evidence: bounded_evidence(),
    }
}

pub(super) fn hash_fold_summary_for_island(
    island: &LoopIsland,
    source: LoadedSource,
    accumulator: String,
    operation: NativeWorkerFoldOperation,
) -> NativeWorkerSummary {
    let fold = NativeWorkerFold {
        accumulator,
        bits: source_access_width(source).saturating_mul(8),
        operation,
        predicate: None,
        init: None,
        multiplier: None,
        byte_transform: None,
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
