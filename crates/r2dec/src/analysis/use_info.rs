use r2types::SourceOwnedFunctionFacts;

use super::SSABlock;

mod legacy;

pub(crate) use legacy::{
    analyze_with_definition_overrides, annotate_stack_slot_semantics, populate_frame_slot_merges,
};

/// Stage-3 seam for value/use analysis. It carries the exact source-owned
/// authority explicitly; the renderer may not reconstruct it from `PassEnv`.
#[allow(
    dead_code,
    reason = "Stage 1 API seam; Stage 3 moves existing analysis behind it"
)]
pub(crate) struct UseAnalysisInput<'a> {
    source: &'a SourceOwnedFunctionFacts,
}

#[allow(
    dead_code,
    reason = "Stage 1 API seam; Stage 3 moves existing analysis behind it"
)]
impl<'a> UseAnalysisInput<'a> {
    pub(crate) const fn new(source: &'a SourceOwnedFunctionFacts) -> Self {
        Self { source }
    }

    pub(crate) const fn source(&self) -> &'a SourceOwnedFunctionFacts {
        self.source
    }

    pub(crate) fn blocks(&self) -> impl Iterator<Item = &'a SSABlock> {
        self.source.source().function().blocks()
    }
}
