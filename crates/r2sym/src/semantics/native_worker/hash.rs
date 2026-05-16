use r2ssa::{SsaArtifact, SummaryTransferLength};

use crate::semantics::{
    NativeWorkerFold, NativeWorkerFoldOperation, NativeWorkerLoopSummary, NativeWorkerSummary,
    NativeWorkerSummaryKind, NativeWorkerTerminator,
};

use super::{
    LoadedSource, LoopIsland, allocation_role_worker_summary, arg_byte_location, arg_location,
    bounded_evidence, format_render_worker_summary, global_lifetime_worker_summary, loop_summary,
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

pub(super) fn is_hash_fold_family_name(name: &str) -> bool {
    name.ends_with("_hash")
        || name.ends_with("_hasher")
        || matches!(
            name,
            "hash_pjw"
                | "blake2b_compress"
                | "sha224_buffer"
                | "sha224_process_block"
                | "sha224_process_bytes"
                | "sha224_stream"
                | "sha256_buffer"
                | "sha256_process_block"
                | "sha256_process_bytes"
                | "sha256_stream"
                | "sha384_read_ctx"
                | "sha512_buffer"
                | "sha512_process_block"
                | "sha512_process_bytes"
                | "sha512_read_ctx"
                | "sha512_stream"
                | "sm3_process_block"
                | "sm3_process_bytes"
                | "sm3_stream"
        )
}

pub(super) fn is_hash_context_read_name(name: &str) -> bool {
    matches!(name, "sha384_read_ctx" | "sha512_read_ctx")
}

pub(super) fn named_hash_fold_worker_summary(
    anchor: u64,
    memory_arg: usize,
    state_arg: Option<usize>,
    length_arg: Option<usize>,
    accumulator: &str,
    bits: u32,
    operation: NativeWorkerFoldOperation,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind: NativeWorkerSummaryKind::HashFold,
        dst: state_arg.map(arg_location),
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
                    .unwrap_or(NativeWorkerTerminator::Unknown),
            ),
            fold: Some(NativeWorkerFold {
                accumulator: accumulator.to_string(),
                bits,
                operation,
                predicate: None,
            }),
        }),
        evidence: bounded_evidence(),
    }
}

pub(super) fn hash_table_worker_summaries(
    anchor: u64,
    table_arg: usize,
    key_arg: Option<usize>,
) -> Vec<NativeWorkerSummary> {
    let mut summaries = vec![table_walk_worker_summary(anchor, table_arg)];
    if let Some(key_arg) = key_arg {
        summaries.push(named_hash_fold_worker_summary(
            anchor,
            key_arg,
            Some(table_arg),
            None,
            "hash_state",
            64,
            NativeWorkerFoldOperation::Xor,
        ));
    }
    summaries
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

pub(super) fn hash_fold_family_worker_summaries(
    anchor: u64,
    name: &str,
) -> Vec<NativeWorkerSummary> {
    if is_hash_context_read_name(name) {
        return hash_context_read_worker_summaries(anchor, name);
    }
    if name == "blake2b_compress" {
        return vec![named_hash_fold_worker_summary(
            anchor,
            1,
            Some(0),
            None,
            "blake2b_state",
            64,
            NativeWorkerFoldOperation::RotateMix,
        )];
    }
    if name.starts_with("sm3_") {
        return vec![named_hash_fold_worker_summary(
            anchor,
            0,
            name.contains("_process_").then_some(2),
            name.contains("_process_").then_some(1),
            "sm3_state",
            32,
            NativeWorkerFoldOperation::RotateMix,
        )];
    }
    let accumulator = if name.starts_with("sha") {
        "sha_state"
    } else {
        "hash_key"
    };
    let length_arg = name
        .contains("_process_")
        .then_some(1)
        .or_else(|| name.ends_with("_buffer").then_some(1));
    let state_arg = if name.starts_with("sha") && name.contains("_process_") {
        Some(2)
    } else {
        None
    };
    vec![named_hash_fold_worker_summary(
        anchor,
        0,
        state_arg,
        length_arg,
        accumulator,
        64,
        NativeWorkerFoldOperation::RotateMix,
    )]
}

fn fixed_memory_worker_summary(
    anchor: u64,
    kind: NativeWorkerSummaryKind,
    memory_arg: usize,
    byte_len: u64,
) -> NativeWorkerSummary {
    NativeWorkerSummary {
        anchor,
        kind,
        dst: None,
        src: None,
        memory: Some(arg_location(memory_arg)),
        len: Some(SummaryTransferLength::Const(byte_len)),
        allocation: None,
        lifetime: None,
        sync: None,
        atomic: None,
        parser: None,
        loop_summary: None,
        evidence: bounded_evidence(),
    }
}

pub(super) fn hash_context_read_worker_summaries(
    anchor: u64,
    name: &str,
) -> Vec<NativeWorkerSummary> {
    let byte_len = if name == "sha384_read_ctx" { 48 } else { 64 };
    let word_count = byte_len / 8;
    vec![
        fixed_memory_worker_summary(anchor, NativeWorkerSummaryKind::MemoryRead, 0, byte_len),
        fixed_memory_worker_summary(anchor, NativeWorkerSummaryKind::MemoryWrite, 1, byte_len),
        NativeWorkerSummary {
            anchor,
            kind: NativeWorkerSummaryKind::NumericTransform,
            dst: Some(arg_location(1)),
            src: Some(arg_location(0)),
            memory: None,
            len: Some(SummaryTransferLength::Const(byte_len)),
            allocation: None,
            lifetime: None,
            sync: None,
            atomic: None,
            parser: None,
            loop_summary: Some(NativeWorkerLoopSummary {
                header: anchor,
                exit_target: None,
                iterations: Some(word_count),
                length_arg: None,
                stride: Some(8),
                terminator: Some(NativeWorkerTerminator::LengthBound),
                fold: Some(NativeWorkerFold {
                    accumulator: "sha512_digest_state".to_string(),
                    bits: 64,
                    operation: NativeWorkerFoldOperation::RotateMix,
                    predicate: None,
                }),
            }),
            evidence: bounded_evidence(),
        },
    ]
}

pub(super) fn hash_statistics_worker_summaries(anchor: u64) -> Vec<NativeWorkerSummary> {
    vec![
        table_walk_worker_summary(anchor, 0),
        format_render_worker_summary(anchor, 1, None),
        output_stream_worker_summary(anchor, 1, None),
    ]
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
                bits: source.size.saturating_mul(8),
                operation,
                predicate: None,
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
        bits: source.size.saturating_mul(8),
        operation,
        predicate: None,
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
