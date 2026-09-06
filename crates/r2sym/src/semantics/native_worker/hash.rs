use r2ssa::SsaArtifact;

use crate::semantics::{
    NativeWorkerFold, NativeWorkerFoldOperation, NativeWorkerSummary, NativeWorkerSummaryKind,
    NativeWorkerTerminator,
};

use super::{LoadedSource, LoopIsland, bounded_evidence, loop_summary, loop_summary_from_island};

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
