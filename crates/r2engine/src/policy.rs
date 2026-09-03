//! The engine's policy budgets.
//!
//! Every number here bounds work rather than describing the program: how many
//! symbolic paths to explore, how large a function may be before the decompile
//! route declines it, how long a post-analysis pass may run. They are collected
//! so that the values a run is governed by can be read in one place instead of
//! found among the planning code.
//!
//! Several are not derived from anything, which is recorded as known debt in
//! the roadmap rather than hidden here.

/// Worklist steps a path listing may take.
///
/// This was 500 wall-clock milliseconds, which made the set of paths a
/// function listed depend on how busy the machine was.
pub const SYMBOLIC_PATHS_LIMIT: usize = 32;
pub const SYMBOLIC_PATHS_CALL_FREE_MAX_STATES: usize = 16;
pub const SYMBOLIC_PATHS_CALL_FREE_MAX_DEPTH: usize = 64;
pub const SYMBOLIC_PATHS_CALL_HEAVY_MAX_STATES: usize = 8;
pub const SYMBOLIC_PATHS_CALL_HEAVY_MAX_DEPTH: usize = 32;
pub const SYMBOLIC_PATHS_MAX_STEPS: u64 = 5_000;
pub const SYMBOLIC_PATHS_SOLUTION_LIMIT: usize = 4;
pub const RADARE2_ANALYSIS_DEPTH_BASIC: u32 = 1;
pub const RADARE2_ANALYSIS_DEPTH_AGGRESSIVE: u32 = 3;
/// Post-analysis time a program is allowed, per function it contains.
///
/// This replaces three whole-program constants -- two, ten and thirty seconds
/// by mode -- that were not derived from anything. Ten seconds is not a fact
/// about a program: on the DecBench bzip2recover build, 38 functions, the sweep
/// finishes in about 1.5 seconds and the budget never binds, while on bzip2,
/// 154 functions, the same ten seconds stopped the sweep after a third of the
/// program. One number cannot be both, because the work scales with the
/// function count and the number did not.
///
/// The allowance is the project's own per-function performance bar, which is
/// already agreed and stated elsewhere: a function is expected to cost under
/// 100 milliseconds net. So the budget is not a new judgement about how long is
/// too long; it is the bar the sweep is already held to, multiplied by the work
/// in front of it. A function that exceeds it is a defect to fix rather than a
/// budget to widen, and the sweep saying so is the point.
///
/// Measured against it, with the per-callback split on bzip2recover: the whole
/// sweep costs about 39ms per function -- an 11.5ms snapshot walk, a 17.6ms
/// proof, and artifact submission for the rest -- so the bar is cleared by
/// roughly a factor of two and a slower machine still finishes.
///
/// The analysis mode is deliberately not a factor. A mode decides how much work
/// each function gets, not how long a wall clock may run, and expressing the
/// same policy twice was what let the two disagree.
pub const POST_ANALYSIS_PER_FUNCTION_BUDGET_USEC: u64 = 100_000;

/// Floor for a program with no functions, so a sweep with nothing to do still
/// has time to establish that rather than refusing on a zero budget.
pub const POST_ANALYSIS_MINIMUM_BUDGET_USEC: u64 = POST_ANALYSIS_PER_FUNCTION_BUDGET_USEC;

/// The post-analysis budget for a program of this size.
pub const fn post_analysis_budget_usec(function_count: usize) -> u64 {
    let derived = (function_count as u64).saturating_mul(POST_ANALYSIS_PER_FUNCTION_BUDGET_USEC);
    if derived < POST_ANALYSIS_MINIMUM_BUDGET_USEC {
        POST_ANALYSIS_MINIMUM_BUDGET_USEC
    } else {
        derived
    }
}
pub const TAINT_GLOBAL_MAX_FUNCTIONS: usize = 128;
pub const SIGNATURE_WRITEBACK_GLOBAL_MAX_FUNCTIONS: usize = 128;
pub const TYPE_WRITEBACK_GLOBAL_MAX_FUNCTIONS: usize = 128;
pub const ENGINE_DECOMPILE_MAX_BLOCKS: usize = 200;
pub const ENGINE_DECOMPILE_MAX_OPS: usize = 16384;
pub const AUTO_CALLBACK_MAX_BLOCKS: u32 = 96;
pub const AUTO_CALLBACK_MAX_COST: u32 = 512;
pub const AUTO_CALLBACK_MAX_LINEAR_SIZE: u64 = 256 * 1024;
pub const SYMBOLIC_SCOPE_MAX_FUNCTIONS: usize = 32;
pub const RUNTIME_MATERIALIZED_MAX_BYTES: u64 = 0x4000;
pub const RUNTIME_MATERIALIZED_SLOT_BYTES: u64 = 16;
pub const TYPE_WRITEBACK_MUTATION_SIGNATURE_ID: u32 = 0;
pub const TYPE_WRITEBACK_MUTATION_CALLCONV_ID: u32 = 1;
pub const TYPE_WRITEBACK_MUTATION_VAR_ID: u32 = 2;
pub const TYPE_WRITEBACK_MUTATION_VAR_RENAME_ID: u32 = 3;
pub const TYPE_WRITEBACK_MUTATION_VAR_TYPE_ID: u32 = 4;
pub const TYPE_WRITEBACK_MUTATION_XREF_ID: u32 = 5;
pub const TYPE_WRITEBACK_MUTATION_COMMENT_ID: u32 = 6;
pub const TYPE_WRITEBACK_MUTATION_FLAG_ID: u32 = 7;
pub const TYPE_WRITEBACK_MUTATION_TYPE_DECL_ID: u32 = 8;
pub const TYPE_WRITEBACK_MUTATION_TYPE_LINK_ID: u32 = 9;
pub const ENGINE_INTERPROC_HELPER_MAX_BLOCKS: u32 = 64;
pub const ENGINE_INTERPROC_HELPER_MAX_COST: u32 = 256;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_budget_grows_with_the_program_rather_than_with_the_mode() {
        // The case the three constants could not express: the same policy has
        // to give a 154-function binary four times what a 38-function one gets.
        assert_eq!(post_analysis_budget_usec(38), 3_800_000);
        assert_eq!(post_analysis_budget_usec(154), 15_400_000);
        assert!(post_analysis_budget_usec(154) > post_analysis_budget_usec(38));
    }

    #[test]
    fn a_program_with_nothing_to_sweep_still_has_time_to_say_so() {
        assert_eq!(
            post_analysis_budget_usec(0),
            POST_ANALYSIS_MINIMUM_BUDGET_USEC
        );
    }

    #[test]
    fn an_absurd_function_count_does_not_wrap_the_budget() {
        assert_eq!(post_analysis_budget_usec(usize::MAX), u64::MAX);
    }
}
