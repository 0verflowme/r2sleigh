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
pub const POST_ANALYSIS_FAST_BUDGET_USEC: u64 = 2 * 1_000_000;
pub const POST_ANALYSIS_BALANCED_BUDGET_USEC: u64 = 10 * 1_000_000;
pub const POST_ANALYSIS_AGGRESSIVE_BUDGET_USEC: u64 = 30 * 1_000_000;
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
