//! Versioned, panic-contained production boundary for engine requests.
//!
//! V2 exposes the lift core plus decompilation and function typing. Engine
//! requests use one native, versioned request graph.

use super::analysis::sym::R2ILFunctionBlocks;
use super::{R2ILBlock, R2ILContext};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CStr, CString, c_char, c_void};
use std::mem::{align_of, size_of};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::ptr;
use std::slice;
use std::str;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};
use std::thread::{self, ThreadId};
use std::time::{Duration, Instant};

pub const R2SLEIGH_ABI_V2: u32 = 2;
pub const R2SLEIGH_CAP_DECOMPILE_V2: u64 = 1 << 0;
pub const R2SLEIGH_CAP_TYPE_FUNCTION_V2: u64 = 1 << 1;
pub const R2SLEIGH_CAP_EXACT_FUNCTION_INTERFACE_V2: u64 = 1 << 2;
pub const R2SLEIGH_CAP_CALL_SITE_INTERFACES_V2: u64 = 1 << 3;
pub const R2SLEIGH_CAP_NATIVE_REQUEST_GRAPH_V2: u64 = 1 << 4;
pub const R2SLEIGH_CAP_RESPONSE_INFO_V2: u64 = 1 << 5;
pub const R2SLEIGH_CAP_EXECUTION_CONTROL_V2: u64 = 1 << 6;
pub const R2SLEIGH_CAP_EXACT_TYPE_LAYOUT_V2: u64 = 1 << 7;
pub const R2SLEIGH_CAP_EXACT_STACK_SLOT_ROLES_V2: u64 = 1 << 8;
pub const R2SLEIGH_CAP_LIFT_CORE_V2: u64 = 1 << 9;
pub const R2SLEIGH_CAP_PLANNER_QUERY_V2: u64 = 1 << 10;
pub const R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2: u64 = 1 << 11;
pub const R2SLEIGH_CAPABILITIES_V2: u64 = R2SLEIGH_CAP_DECOMPILE_V2
    | R2SLEIGH_CAP_TYPE_FUNCTION_V2
    | R2SLEIGH_CAP_EXACT_FUNCTION_INTERFACE_V2
    | R2SLEIGH_CAP_CALL_SITE_INTERFACES_V2
    | R2SLEIGH_CAP_NATIVE_REQUEST_GRAPH_V2
    | R2SLEIGH_CAP_RESPONSE_INFO_V2
    | R2SLEIGH_CAP_EXECUTION_CONTROL_V2
    | R2SLEIGH_CAP_EXACT_TYPE_LAYOUT_V2
    | R2SLEIGH_CAP_EXACT_STACK_SLOT_ROLES_V2
    | R2SLEIGH_CAP_LIFT_CORE_V2
    | R2SLEIGH_CAP_PLANNER_QUERY_V2
    | R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2;
pub const R2SLEIGH_RADARE_ABI_V2: u32 = 138;
pub const R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2: u32 = 8;
pub const R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2: u32 = 2;

pub const R2SLEIGH_STATUS_OK_V2: u32 = 0;
pub const R2SLEIGH_STATUS_INVALID_ARGUMENT_V2: u32 = 1;
pub const R2SLEIGH_STATUS_ABI_MISMATCH_V2: u32 = 2;
pub const R2SLEIGH_STATUS_UNSUPPORTED_V2: u32 = 3;
pub const R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2: u32 = 4;
pub const R2SLEIGH_STATUS_ENGINE_ERROR_V2: u32 = 5;
pub const R2SLEIGH_STATUS_PANIC_V2: u32 = 6;

pub const R2SLEIGH_REQUEST_DECOMPILE_V2: u32 = 1;
pub const R2SLEIGH_REQUEST_TYPE_FUNCTION_V2: u32 = 2;
pub const R2SLEIGH_FUNCTION_CONTEXT_SCHEMA_V2: u32 = 3;
pub const R2SLEIGH_INTERPROC_SCOPE_SCHEMA_V2: u32 = 1;
pub const R2SLEIGH_RESPONSE_INFO_SCHEMA_V2: u32 = 2;
pub const R2SLEIGH_OUTCOME_COMPLETED_V2: u32 = 0;
pub const R2SLEIGH_OUTCOME_REFUSED_V2: u32 = 1;
pub const R2SLEIGH_PHASE_SNAPSHOT_CONTEXT_V2: u32 = 0;
pub const R2SLEIGH_PHASE_LIFT_NORMALIZE_V2: u32 = 1;
pub const R2SLEIGH_PHASE_SSA_V2: u32 = 2;
pub const R2SLEIGH_PHASE_OBLIGATIONS_V2: u32 = 3;
pub const R2SLEIGH_PHASE_SYMBOLIC_V2: u32 = 4;
pub const R2SLEIGH_PHASE_TYPES_V2: u32 = 5;
pub const R2SLEIGH_PHASE_CERTIFICATION_V2: u32 = 6;
pub const R2SLEIGH_PHASE_STRUCTURING_V2: u32 = 7;
pub const R2SLEIGH_PHASE_NORMALIZATION_V2: u32 = 8;
pub const R2SLEIGH_PHASE_RENDERING_V2: u32 = 9;
pub const R2SLEIGH_PHASE_FFI_CONVERSION_V2: u32 = 10;
pub const R2SLEIGH_PHASE_COUNT_V2: usize = 11;
pub const R2SLEIGH_PHASE_STATUS_NOT_EXECUTED_V2: u32 = 0;
pub const R2SLEIGH_PHASE_STATUS_EXECUTED_V2: u32 = 1;
pub const R2SLEIGH_PHASE_STATUS_FOLDED_V2: u32 = 2;
pub const R2SLEIGH_PHASE_STATUS_REUSED_V2: u32 = 3;
pub const R2SLEIGH_PHASE_STATUS_REFUSED_V2: u32 = 4;
pub const R2SLEIGH_SOURCE_RETURN_VOID_V2: u32 = 1;
pub const R2SLEIGH_SOURCE_RETURN_REGISTER_V2: u32 = 2;
pub const R2SLEIGH_SOURCE_STACK_BASE_BP_V2: u32 = 1;
pub const R2SLEIGH_SOURCE_STACK_BASE_SP_V2: u32 = 2;
pub const R2SLEIGH_SOURCE_STACK_ROLE_LOCAL_V2: u32 = 1;
pub const R2SLEIGH_SOURCE_STACK_ROLE_PARAMETER_HOME_V2: u32 = 2;
pub const R2SLEIGH_SOURCE_PARAMETER_INDEX_INVALID_V2: u32 = u32::MAX;
pub const R2SLEIGH_SOURCE_STORAGE_RAM_V2: u32 = 1;
pub const R2SLEIGH_SOURCE_STORAGE_REGISTER_V2: u32 = 2;
pub const R2SLEIGH_SOURCE_STORAGE_UNIQUE_V2: u32 = 3;
pub const R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2: u32 = 4;
pub const R2SLEIGH_SOURCE_STORAGE_CUSTOM_V2: u32 = 5;
pub const R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2: u32 = 7;
pub const R2SLEIGH_SOURCE_CALL_SITE_SCHEMA_V2: u32 = 1;
pub const R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2: u32 = u32::MAX;
pub const R2SLEIGH_SOURCE_TYPE_SIGNED_INTEGER_V2: u32 = 1;
pub const R2SLEIGH_SOURCE_TYPE_UNSIGNED_INTEGER_V2: u32 = 2;
pub const R2SLEIGH_SOURCE_TYPE_POINTER_V2: u32 = 3;
pub const R2SLEIGH_SOURCE_TYPE_STRUCT_V2: u32 = 4;
pub const R2SLEIGH_SOURCE_CARRIER_INVALID_V2: u32 = 0;
pub const R2SLEIGH_SOURCE_CARRIER_FULL_V2: u32 = 1;
pub const R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2: u32 = 2;
pub const R2SLEIGH_MAX_FUNCTION_BLOCKS_V2: usize = 200;
pub const R2SLEIGH_MAX_FUNCTION_OPS_V2: usize = 512;
pub const R2SLEIGH_MAX_SWITCH_CASES_V2: usize = 4_096;
pub const R2SLEIGH_ANALYSIS_BLOCK_ESIL_V2: u32 = 1;
pub const R2SLEIGH_ANALYSIS_BLOCK_OP_JSON_V2: u32 = 2;
pub const R2SLEIGH_ANALYSIS_BLOCK_REGS_READ_V2: u32 = 3;
pub const R2SLEIGH_ANALYSIS_BLOCK_REGS_WRITE_V2: u32 = 4;
pub const R2SLEIGH_ANALYSIS_BLOCK_MEMORY_V2: u32 = 5;
pub const R2SLEIGH_ANALYSIS_BLOCK_VARNODES_V2: u32 = 6;
pub const R2SLEIGH_ANALYSIS_BLOCK_SSA_V2: u32 = 7;
pub const R2SLEIGH_ANALYSIS_BLOCK_DEFUSE_V2: u32 = 8;
pub const R2SLEIGH_ANALYSIS_FUNCTION_SSA_V2: u32 = 9;
pub const R2SLEIGH_ANALYSIS_FUNCTION_SSA_OPT_V2: u32 = 10;
pub const R2SLEIGH_ANALYSIS_FUNCTION_DEFUSE_V2: u32 = 11;
pub const R2SLEIGH_ANALYSIS_FUNCTION_DOMTREE_V2: u32 = 12;
pub const R2SLEIGH_ANALYSIS_FUNCTION_SLICE_V2: u32 = 13;
pub const R2SLEIGH_ANALYSIS_FUNCTION_TAINT_V2: u32 = 14;
pub const R2SLEIGH_ANALYSIS_FUNCTION_CFG_ASCII_V2: u32 = 15;
pub const R2SLEIGH_ANALYSIS_FUNCTION_CFG_JSON_V2: u32 = 16;
pub const R2SLEIGH_ANALYSIS_ENGINE_CACHE_STATS_V2: u32 = 17;
pub const R2SLEIGH_SCOPE_FUNCTION_V2: u32 = 1;
pub const R2SLEIGH_SCOPE_PATHS_V2: u32 = 2;
pub const R2SLEIGH_SCOPE_EXPLORE_V2: u32 = 3;
pub const R2SLEIGH_SCOPE_SOLVE_V2: u32 = 4;
pub const R2SLEIGH_SCOPE_EXPLORE_REPLAY_V2: u32 = 5;
pub const R2SLEIGH_SCOPE_SOLVE_REPLAY_V2: u32 = 6;
pub const R2SLEIGH_SCOPE_RUN_SPEC_V2: u32 = 7;
pub const R2SLEIGH_SCOPE_SYMBOL_SCHEMA_V2: u32 = 1;
pub const R2SLEIGH_QUERY_BLOCK_VALUES_V2: u32 = 1;
pub const R2SLEIGH_QUERY_TAINT_SUMMARY_V2: u32 = 2;
pub const R2SLEIGH_QUERY_ANNOTATIONS_V2: u32 = 3;
pub const R2SLEIGH_QUERY_DIRECT_TARGETS_V2: u32 = 4;
pub const R2SLEIGH_QUERY_SYMBOLIC_TARGETS_V2: u32 = 5;
pub const R2SLEIGH_QUERY_RUNTIME_SOURCES_V2: u32 = 6;
pub const R2SLEIGH_QUERY_RECOVERED_VARS_V2: u32 = 7;
pub const R2SLEIGH_QUERY_DATA_REFS_V2: u32 = 8;
pub const R2SLEIGH_PLANNER_QUERY_SCHEMA_V2: u32 = 1;
pub const R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2: u32 = 1;
pub const R2SLEIGH_PLANNER_POST_ANALYSIS_V2: u32 = 2;
pub const R2SLEIGH_PLANNER_AUTO_CALLBACK_V2: u32 = 3;
pub const R2SLEIGH_PLANNER_INTERPROC_SESSION_V2: u32 = 4;
pub const R2SLEIGH_PLANNER_SYMBOLIC_SCOPE_V2: u32 = 5;
pub const R2SLEIGH_PLANNER_RUNTIME_SOURCE_V2: u32 = 6;
pub const R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2: u32 = 7;
pub const R2SLEIGH_PLANNER_TARGET_INPUT_SCHEMA_V2: u32 = 1;
pub const R2SLEIGH_PLANNER_RESULT_SCHEMA_V2: u32 = 1;
pub const R2SLEIGH_MAX_PLANNER_TARGETS_V2: usize = 4_096;
pub const R2SLEIGH_INTERPROC_LINKAGE_UNKNOWN_V2: u32 = 0;
pub const R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2: u32 = 1;
pub const R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2: u32 = 2;
pub const R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2: u32 = 1;
pub const R2SLEIGH_PLANNER_RESULT_REGISTRATION_TARGETS_V2: u32 = 2;
pub const R2SLEIGH_PLANNER_RESULT_RUNTIME_COPY_TARGETS_V2: u32 = 3;
pub const R2SLEIGH_MODE_FAST_V2: u32 = 0;
pub const R2SLEIGH_MODE_BALANCED_V2: u32 = 1;
pub const R2SLEIGH_MODE_FULL_V2: u32 = 2;
pub const R2SLEIGH_TYPE_WRITEBACK_OFF_V2: u32 = 0;
pub const R2SLEIGH_TYPE_WRITEBACK_BALANCED_V2: u32 = 1;
pub const R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE_V2: u32 = 2;
pub const R2SLEIGH_INTERPROC_SESSION_TYPE_ANALYSIS_V2: u32 = 0;
pub const R2SLEIGH_INTERPROC_SESSION_DECOMPILE_V2: u32 = 1;
pub const R2SLEIGH_AUTO_CALLBACK_ANALYZE_FUNCTION_V2: u32 = 0;
pub const R2SLEIGH_AUTO_CALLBACK_RECOVER_VARS_V2: u32 = 1;
pub const R2SLEIGH_AUTO_CALLBACK_DATA_REFS_V2: u32 = 2;
pub const R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_TAINT_V2: u32 = 3;
pub const R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_XREF_V2: u32 = 4;
pub const R2SLEIGH_AUTO_CALLBACK_REASON_ALLOWED_V2: u32 = 0;
pub const R2SLEIGH_AUTO_CALLBACK_REASON_MODE_NOT_FULL_V2: u32 = 1;
pub const R2SLEIGH_AUTO_CALLBACK_REASON_TOO_MANY_BLOCKS_V2: u32 = 2;
pub const R2SLEIGH_AUTO_CALLBACK_REASON_TOO_LARGE_V2: u32 = 3;
pub const R2SLEIGH_AUTO_CALLBACK_REASON_TOO_COSTLY_V2: u32 = 4;
pub const R2SLEIGH_SYMBOLIC_SCOPE_REASON_ALLOWED_V2: u32 = 0;
pub const R2SLEIGH_SYMBOLIC_SCOPE_REASON_SCOPE_FULL_V2: u32 = 1;
pub const R2SLEIGH_SYMBOLIC_SCOPE_REASON_INTERPROC_DISABLED_V2: u32 = 2;
pub const R2SLEIGH_SYMBOLIC_SCOPE_REASON_TARGET_TERMINAL_V2: u32 = 3;
pub const R2SLEIGH_RUNTIME_SOURCE_REASON_ALLOWED_V2: u32 = 0;
pub const R2SLEIGH_RUNTIME_SOURCE_REASON_SCOPE_FULL_V2: u32 = 1;
pub const R2SLEIGH_RUNTIME_SOURCE_REASON_EMPTY_SOURCE_V2: u32 = 2;
#[allow(dead_code)] // Exported for the C-side pre-lift byte budget.
pub const R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2: usize = 16 << 20;
pub const R2SLEIGH_MAX_AGGREGATE_BLOCKS_V2: usize = 1_024;
pub const R2SLEIGH_MAX_AGGREGATE_OPS_V2: usize = 4_096;
pub const R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2: usize = 4_096;
pub const R2SLEIGH_MAX_SCOPE_SYMBOLS_V2: usize = 4_096;
pub const R2SLEIGH_MAX_CONTEXT_ITEMS_V2: usize = 65_536;
pub const R2SLEIGH_MAX_NESTED_ITEMS_V2: usize = 262_144;
pub const R2SLEIGH_MAX_STRING_BYTES_V2: usize = 1 << 20;
pub const R2SLEIGH_MAX_AGGREGATE_STRING_BYTES_V2: usize = 4 << 20;
pub const R2SLEIGH_MAX_JSON_BYTES_V2: usize = 16 << 20;
pub const R2SLEIGH_MAX_AGGREGATE_JSON_BYTES_V2: usize = 16 << 20;

const REQUEST_FLAG_TEST_PANIC: u32 = 1 << 31;
const MAX_RESPONSE_BYTES: usize = 64 << 20;
const MAX_INTERPROC_ITERATIONS: usize = 4_096;
// ABI argument lists are expected to be small; cap caller hints before use.
const MAX_ABI_ARGUMENTS: usize = 256;

/// Borrowed bytes. Its producing callback defines the lifetime: response views
/// survive until response_free, session errors until the next session operation,
/// lift-context views until the next context operation, lift-last-error views
/// until the next lift callback on the current thread, and owned-byte views until
/// owned_bytes_free.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighByteViewV2 {
    pub data: *const u8,
    pub len: usize,
}

impl Default for R2SleighByteViewV2 {
    fn default() -> Self {
        Self {
            data: ptr::null(),
            len: 0,
        }
    }
}

#[repr(C)]
pub struct R2SleighSessionConfigV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub required_capabilities: u64,
}

/// Versioned request envelope. `payload` points to one native
/// R2SleighEngineRequestPayloadV2 whose interpretation is selected by `kind`;
/// it is borrowed only for the duration of execute.
#[repr(C)]
pub struct R2SleighRequestV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub kind: u32,
    pub flags: u32,
    pub payload: *const c_void,
    pub payload_size: usize,
}

/// Length-tagged UTF-8 source string.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighStringViewV2 {
    pub data: *const u8,
    pub len: usize,
}

/// Borrowed opaque radare2 ABI 138 snapshot plus its immutable accessor table.
/// Both pointers are valid only for the duration of one synchronous `execute`
/// callback. Rust deep-copies the source before returning to the caller.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct R2SleighRadareSnapshotInputV2 {
    pub struct_size: u32,
    pub abi_version: u32,
    pub snapshot_schema_version: u32,
    pub accessor_schema_version: u32,
    pub snapshot: *const c_void,
    pub accessors: *const R2SleighRadareAccessorsV2,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct R2SleighRadareSnapshotViewV2 {
    pub schema_version: u32,
    pub struct_size: u32,
    pub capabilities: u64,
    pub function_addr: u64,
    pub function_size: u64,
    pub bits: i32,
    pub endian: u32,
    pub maxstack: i64,
    pub arch_id_length: usize,
    pub cpu_id_length: usize,
    pub function_name_length: usize,
    pub num_base_types: usize,
    pub type_context_hash: u64,
    pub num_call_site_interfaces: usize,
    pub num_stack_slots: usize,
    pub revision_identity: u64,
    pub num_types: usize,
    pub num_aggregates: usize,
    pub num_blocks: usize,
    pub num_external_exits: usize,
    pub total_source_bytes: usize,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareBlockViewV2 {
    pub addr: u64,
    pub size: u64,
    pub num_successors: usize,
    pub switch_addr: u64,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareSuccessorViewV2 {
    pub kind: i32,
    pub target_addr: u64,
    pub case_value: u64,
    pub external: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareRegisterStorageViewV2 {
    pub name_length: usize,
    pub offset: u64,
    pub size: u32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareCarrierProjectionV2 {
    pub kind: i32,
    pub offset_bits: u64,
    pub size_bits: u64,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareParameterViewV2 {
    pub index: u32,
    pub storage: R2SleighRadareRegisterStorageViewV2,
    pub logical_type_id: u32,
    pub carrier: R2SleighRadareCarrierProjectionV2,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareFunctionInterfaceViewV2 {
    pub calling_convention_length: usize,
    pub num_parameters: usize,
    pub return_kind: i32,
    pub return_storage: R2SleighRadareRegisterStorageViewV2,
    pub return_address_storage: R2SleighRadareRegisterStorageViewV2,
    pub stack_pointer_storage: R2SleighRadareRegisterStorageViewV2,
    pub variadic: u8,
    pub noreturn: u8,
    pub stack_resources_complete: u8,
    pub stack_slot_roles_complete: u8,
    pub complete: u8,
    pub return_type_id: u32,
    pub return_carrier: R2SleighRadareCarrierProjectionV2,
    pub logical_types_complete: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareCallSiteViewV2 {
    pub instruction_addr: u64,
    pub target_addr: u64,
    pub calling_convention_length: usize,
    pub num_arguments: usize,
    pub result_kind: i32,
    pub result_storage: R2SleighRadareRegisterStorageViewV2,
    pub variadic: u8,
    pub noreturn: u8,
    pub complete: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareTypeGraphViewV2 {
    pub num_types: usize,
    pub num_aggregates: usize,
    pub complete: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareTypeViewV2 {
    pub id: u32,
    pub kind: i32,
    pub size_bits: u64,
    pub align_bits: u64,
    pub target_type_id: u32,
    pub aggregate_id: u32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareAggregateViewV2 {
    pub id: u32,
    pub type_id: u32,
    pub size_bits: u64,
    pub align_bits: u64,
    pub name_length: usize,
    pub num_members: usize,
    pub complete: u8,
    pub c_layout_compatible: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareAggregateMemberViewV2 {
    pub member_id: u32,
    pub type_id: u32,
    pub offset_bits: u64,
    pub size_bits: u64,
    pub count: usize,
    pub name_length: usize,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct R2SleighRadareStackSlotViewV2 {
    pub name_length: usize,
    pub type_length: usize,
    pub base: i32,
    pub base_name_length: usize,
    pub base_offset: u64,
    pub base_size: u32,
    pub offset: i64,
    pub size: u32,
    pub offset_valid: u8,
    pub role: i32,
    pub arg_index: i32,
    pub arg_name_length: usize,
    pub home_reg_length: usize,
    pub home_reg_offset: u64,
    pub home_reg_size: u32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct R2SleighRadareReturnMechanismViewV2 {
    pub kind: i32,
    pub stack_offset: i64,
    pub slot_size_bytes: u32,
    pub stack_pointer_delta_bytes: u32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct R2SleighRadareAccessorsV2 {
    pub struct_size: u32,
    pub abi_version: u32,
    pub snapshot_schema_version: u32,
    pub accessor_schema_version: u32,
    pub snapshot_view:
        Option<unsafe extern "C" fn(*const c_void, *mut R2SleighRadareSnapshotViewV2) -> u8>,
    pub arch_id: Option<unsafe extern "C" fn(*const c_void, *mut u8, usize) -> u8>,
    pub cpu_id: Option<unsafe extern "C" fn(*const c_void, *mut u8, usize) -> u8>,
    pub function_name: Option<unsafe extern "C" fn(*const c_void, *mut u8, usize) -> u8>,
    pub interface_view: Option<
        unsafe extern "C" fn(*const c_void, *mut R2SleighRadareFunctionInterfaceViewV2) -> u8,
    >,
    pub interface_calling_convention:
        Option<unsafe extern "C" fn(*const c_void, *mut u8, usize) -> u8>,
    pub interface_storage_name:
        Option<unsafe extern "C" fn(*const c_void, i32, *mut u8, usize) -> u8>,
    pub parameter_view: Option<
        unsafe extern "C" fn(*const c_void, usize, *mut R2SleighRadareParameterViewV2) -> u8,
    >,
    pub parameter_storage_name:
        Option<unsafe extern "C" fn(*const c_void, usize, *mut u8, usize) -> u8>,
    pub stack_slot_view: Option<
        unsafe extern "C" fn(*const c_void, usize, *mut R2SleighRadareStackSlotViewV2) -> u8,
    >,
    pub stack_slot_string:
        Option<unsafe extern "C" fn(*const c_void, usize, i32, *mut u8, usize) -> u8>,
    pub call_site_view:
        Option<unsafe extern "C" fn(*const c_void, usize, *mut R2SleighRadareCallSiteViewV2) -> u8>,
    pub call_site_calling_convention:
        Option<unsafe extern "C" fn(*const c_void, usize, *mut u8, usize) -> u8>,
    pub call_site_result_storage_name:
        Option<unsafe extern "C" fn(*const c_void, usize, *mut u8, usize) -> u8>,
    pub call_argument_view: Option<
        unsafe extern "C" fn(*const c_void, usize, usize, *mut R2SleighRadareParameterViewV2) -> u8,
    >,
    pub call_argument_storage_name:
        Option<unsafe extern "C" fn(*const c_void, usize, usize, *mut u8, usize) -> u8>,
    pub type_graph_view:
        Option<unsafe extern "C" fn(*const c_void, *mut R2SleighRadareTypeGraphViewV2) -> u8>,
    pub type_view:
        Option<unsafe extern "C" fn(*const c_void, usize, *mut R2SleighRadareTypeViewV2) -> u8>,
    pub aggregate_view: Option<
        unsafe extern "C" fn(*const c_void, usize, *mut R2SleighRadareAggregateViewV2) -> u8,
    >,
    pub aggregate_name: Option<unsafe extern "C" fn(*const c_void, usize, *mut u8, usize) -> u8>,
    pub aggregate_member_view: Option<
        unsafe extern "C" fn(
            *const c_void,
            usize,
            usize,
            *mut R2SleighRadareAggregateMemberViewV2,
        ) -> u8,
    >,
    pub aggregate_member_name:
        Option<unsafe extern "C" fn(*const c_void, usize, usize, *mut u8, usize) -> u8>,
    pub block_view:
        Option<unsafe extern "C" fn(*const c_void, usize, *mut R2SleighRadareBlockViewV2) -> u8>,
    pub block_bytes:
        Option<unsafe extern "C" fn(*const c_void, usize, usize, *mut u8, usize) -> u8>,
    pub successor_view: Option<
        unsafe extern "C" fn(*const c_void, usize, usize, *mut R2SleighRadareSuccessorViewV2) -> u8,
    >,
    pub external_exit: Option<unsafe extern "C" fn(*const c_void, usize, *mut u64) -> u8>,
    pub return_mechanism_view:
        Option<unsafe extern "C" fn(*const c_void, *mut R2SleighRadareReturnMechanismViewV2) -> u8>,
}

macro_rules! assert_wire_layout {
    ($wire:ty, $source:ty) => {
        const _: [(); size_of::<$wire>()] = [(); size_of::<$source>()];
        const _: [(); align_of::<$wire>()] = [(); align_of::<$source>()];
    };
}

assert_wire_layout!(
    R2SleighRadareSnapshotInputV2,
    r2source::RadareAbi138SnapshotInput
);
assert_wire_layout!(
    R2SleighRadareSnapshotViewV2,
    r2source::RadareAbi138SnapshotView
);
assert_wire_layout!(R2SleighRadareBlockViewV2, r2source::RadareAbi138BlockView);
assert_wire_layout!(
    R2SleighRadareSuccessorViewV2,
    r2source::RadareAbi138SuccessorView
);
assert_wire_layout!(
    R2SleighRadareRegisterStorageViewV2,
    r2source::RadareAbi138RegisterStorageView
);
assert_wire_layout!(
    R2SleighRadareCarrierProjectionV2,
    r2source::RadareAbi138CarrierProjection
);
assert_wire_layout!(
    R2SleighRadareParameterViewV2,
    r2source::RadareAbi138ParameterView
);
assert_wire_layout!(
    R2SleighRadareFunctionInterfaceViewV2,
    r2source::RadareAbi138FunctionInterfaceView
);
assert_wire_layout!(
    R2SleighRadareCallSiteViewV2,
    r2source::RadareAbi138CallSiteView
);
assert_wire_layout!(
    R2SleighRadareTypeGraphViewV2,
    r2source::RadareAbi138TypeGraphView
);
assert_wire_layout!(R2SleighRadareTypeViewV2, r2source::RadareAbi138TypeView);
assert_wire_layout!(
    R2SleighRadareAggregateViewV2,
    r2source::RadareAbi138AggregateView
);
assert_wire_layout!(
    R2SleighRadareAggregateMemberViewV2,
    r2source::RadareAbi138AggregateMemberView
);
assert_wire_layout!(
    R2SleighRadareStackSlotViewV2,
    r2source::RadareAbi138StackSlotView
);
assert_wire_layout!(
    R2SleighRadareReturnMechanismViewV2,
    r2source::RadareAbi138ReturnMechanismView
);
assert_wire_layout!(R2SleighRadareAccessorsV2, r2source::RadareAbi138Accessors);
const _: [(); R2SLEIGH_RADARE_ABI_V2 as usize] = [(); r2source::RADARE_ABI_VERSION as usize];
const _: [(); R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2 as usize] =
    [(); r2source::RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION as usize];
const _: [(); R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2 as usize] =
    [(); r2source::RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION as usize];

/// Typed external signature parameter in the native request graph.
#[repr(C)]
pub struct R2SleighContextParam {
    pub name: *const c_char,
    pub type_name: *const c_char,
    pub cc_reg: *const c_char,
}

/// Typed register or stack variable in the native request graph.
#[repr(C)]
pub struct R2SleighContextVar {
    pub kind: u32,
    pub name: *const c_char,
    pub type_name: *const c_char,
    pub reg: *const c_char,
    pub base: *const c_char,
    pub offset: i64,
    pub has_offset: i32,
    pub role: u32,
    pub param_index: i64,
    pub param_name: *const c_char,
    pub source_reg: *const c_char,
    pub is_arg: i32,
}

#[repr(C)]
pub struct R2SleighContextBaseMember {
    pub name: *const c_char,
    pub type_name: *const c_char,
    pub offset: u64,
    pub size_bits: u64,
    pub has_size_bits: i32,
}

#[repr(C)]
pub struct R2SleighContextEnumVariant {
    pub name: *const c_char,
    pub value: i64,
}

#[repr(C)]
pub struct R2SleighContextBaseType {
    pub kind: u32,
    pub name: *const c_char,
    pub type_name: *const c_char,
    pub size_bits: u64,
    pub has_size_bits: i32,
    pub members: *const R2SleighContextBaseMember,
    pub num_members: usize,
    pub variants: *const R2SleighContextEnumVariant,
    pub num_variants: usize,
}

#[repr(C)]
pub struct R2SleighContextCallee {
    pub call_addr: u64,
    pub addr: u64,
    pub name: *const c_char,
    pub linkage: u32,
    pub signature_name: *const c_char,
    pub signature_ret_type: *const c_char,
    pub signature_callconv: *const c_char,
    pub signature_noreturn: i32,
    pub signature_params: *const R2SleighContextParam,
    pub num_signature_params: usize,
}

/// Immutable typed function context. Every pointer is borrowed only for the
/// duration of `execute` and validated before conversion to owned engine data.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighFunctionContext {
    pub schema_version: u32,
    pub dirty_epoch: u64,
    pub context_hash: u64,
    pub type_dirty_epoch: u64,
    pub external_context_json: *const c_char,
    pub signature_name: *const c_char,
    pub signature_ret_type: *const c_char,
    pub signature_callconv: *const c_char,
    pub signature_noreturn: i32,
    pub params: *const R2SleighContextParam,
    pub num_params: usize,
    pub vars: *const R2SleighContextVar,
    pub num_vars: usize,
    pub base_types: *const R2SleighContextBaseType,
    pub num_base_types: usize,
    pub callees: *const R2SleighContextCallee,
    pub num_callees: usize,
    pub assumptions_json: *const c_char,
}

#[repr(C)]
pub struct R2SleighInterprocSeed {
    pub id: u64,
    pub name: *const c_char,
    pub arg_count_hint: usize,
    pub has_arg_count_hint: i32,
    pub linkage: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighInterprocScope {
    pub schema_version: u32,
    pub functions: *const R2ILFunctionBlocks,
    pub num_functions: usize,
    pub seeds: *const R2SleighInterprocSeed,
    pub num_seeds: usize,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighInterprocSessionPlan {
    pub include_type_interproc_scope: i32,
    pub include_root_symbolic_scope: i32,
    pub interproc_iter: usize,
    pub interproc_max_iters: usize,
    pub interproc_converged: i32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighAnalysisPolicyV2 {
    pub mode: u32,
    pub type_writeback_mode: u32,
    pub type_interproc_max_iters: i32,
    pub type_max_blocks: i32,
    pub type_global_max_links: i32,
    pub type_max_decls: i32,
    pub type_max_mutations: i32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighPostAnalysisPlanV2 {
    pub mode: u32,
    pub type_writeback_mode: u32,
    pub type_interproc_max_iters: i32,
    pub type_max_blocks: i32,
    pub type_global_max_links: i32,
    pub type_max_decls: i32,
    pub type_max_mutations: i32,
    pub function_count: usize,
    pub post_budget_us: u64,
    pub xref_enabled: i32,
    pub taint_enabled: i32,
    pub sigwrite_enabled: i32,
    pub type_writeback_enabled: i32,
    pub semantic_comments_enabled: i32,
    pub sigverify_enabled: i32,
    pub balanced_focus_only: i32,
    pub taint_focus_only: i32,
    pub sigwrite_focus_only: i32,
    pub type_writeback_focus_only: i32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighAutoCallbackPlanV2 {
    pub allowed: i32,
    pub kind: u32,
    pub reason: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighSymbolicScopeFunctionPlanV2 {
    pub append_function: i32,
    pub expand_targets: i32,
    pub reason: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighRuntimeMaterializedSourcePlanV2 {
    pub append_source: i32,
    pub capped_size: u64,
    pub slot_bytes: u64,
    pub reason: u32,
}

/// One exact, independently versioned interprocedural target observation.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighPlannerTargetInputV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub schema_version: u32,
    pub direct_target: u64,
    pub name: R2SleighStringViewV2,
    pub linkage: u32,
    pub resolved_target: u64,
    pub has_resolved_target: u32,
    pub target_materialized: u32,
    pub has_target_metrics: u32,
    pub target_basic_block_count: u32,
    pub target_cost: u32,
}

/// Opaque registry-owned planner result. `planner_result_free` is the only
/// valid deallocator.
pub struct R2SleighPlannerResultV2 {
    queued_targets: Vec<u64>,
    registration_targets: Vec<u64>,
    runtime_copy_targets: Vec<u64>,
}

/// Pointer-free counts for one registry-owned planner result.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighPlannerResultViewV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub schema_version: u32,
    pub queued_target_count: usize,
    pub registration_target_count: usize,
    pub runtime_copy_target_count: usize,
}

/// Versioned planner query. The selected `kind` determines which input fields
/// are read; target arrays are copied and validated during the call.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighPlannerQueryRequestV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub schema_version: u32,
    pub kind: u32,
    pub depth: u32,
    pub purpose: u32,
    pub callback_kind: u32,
    pub root_function: u32,
    pub target_hint_function: u32,
    pub current_scope_count: usize,
    pub function_count: usize,
    pub basic_block_count: usize,
    pub cost: u32,
    pub linear_size: u64,
    pub addr: u64,
    pub size: u64,
    pub interproc: R2SleighInterprocSessionPlan,
    pub targets: *const R2SleighPlannerTargetInputV2,
    pub num_targets: usize,
}

/// Versioned planner response. Only the member selected by `kind` is authoritative.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighPlannerQueryResponseV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub schema_version: u32,
    pub kind: u32,
    pub analysis_policy: R2SleighAnalysisPolicyV2,
    pub post_analysis: R2SleighPostAnalysisPlanV2,
    pub auto_callback: R2SleighAutoCallbackPlanV2,
    pub interproc_session: R2SleighInterprocSessionPlan,
    pub symbolic_scope: R2SleighSymbolicScopeFunctionPlanV2,
    pub runtime_source: R2SleighRuntimeMaterializedSourcePlanV2,
    pub result: *mut R2SleighPlannerResultV2,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighLiftQuality {
    pub expected_blocks: usize,
    pub lifted_blocks: usize,
    pub read_failures: usize,
    pub invalid_blocks: usize,
    pub null_lift_failures: usize,
    pub truncated_blocks: usize,
}

/// One exact full-width register identity supplied by radare2's immutable
/// source snapshot. Name, byte offset, and size are all cross-checked against
/// ArchSpec before use.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighSourceRegisterV2 {
    pub name: R2SleighStringViewV2,
    pub offset: u64,
    pub size: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighSourceParameterV2 {
    pub index: u32,
    pub storage: R2SleighSourceRegisterV2,
}

/// Projection of one logical value into its full-width ABI carrier.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighSourceCarrierProjectionV2 {
    pub kind: u32,
    pub offset_bits: u64,
    pub size_bits: u64,
}

/// Logical type and carrier binding for one source parameter ordinal.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct R2SleighSourceParameterTypeV2 {
    pub index: u32,
    pub type_id: u32,
    pub carrier: R2SleighSourceCarrierProjectionV2,
}

/// One structural logical type. IDs are exact indexes into the source type array.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct R2SleighSourceTypeV2 {
    pub id: u32,
    pub kind: u32,
    pub size_bits: u64,
    pub align_bits: u64,
    pub target_type_id: u32,
    pub aggregate_id: u32,
}

/// One exact aggregate member. `name` is presentation-only; member_id is authority.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighSourceAggregateMemberV2 {
    pub member_id: u32,
    pub type_id: u32,
    pub offset_bits: u64,
    pub size_bits: u64,
    pub count: usize,
    pub name: R2SleighStringViewV2,
}

/// One complete natural-layout aggregate reachable from the function signature.
#[repr(C)]
pub struct R2SleighSourceAggregateLayoutV2 {
    pub id: u32,
    pub type_id: u32,
    pub size_bits: u64,
    pub align_bits: u64,
    pub name: R2SleighStringViewV2,
    pub members: *const R2SleighSourceAggregateMemberV2,
    pub num_members: usize,
    pub complete: u32,
    pub c_layout_compatible: u32,
}

/// One exactly sized stack resource. `base` identifies the source stack/frame
/// register and is canonicalized against ArchSpec before `offset` is used.
/// `role` is exactly Local or parameter Home. Only a Home's `parameter_index`
/// and canonical `home_storage` offset/size carry authority, and they must match
/// that interface parameter. The Home register name is validated presentation
/// data and never participates in role proof.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighSourceStackSlotV2 {
    pub base_kind: u32,
    pub base: R2SleighSourceRegisterV2,
    pub offset: i64,
    pub size: u32,
    pub role: u32,
    pub parameter_index: u32,
    pub home_storage: R2SleighSourceRegisterV2,
}

/// Exact name-independent lifted storage identity.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighSourceStorageV2 {
    pub space: u32,
    pub custom_space: u32,
    pub offset: u64,
    pub size: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighSourceCallArgumentV2 {
    pub index: u32,
    pub storage: R2SleighSourceRegisterV2,
}

/// One exact raw callsite mapped onto one canonical lifted call operation.
#[repr(C)]
pub struct R2SleighSourceCallSiteInterfaceV2 {
    pub schema_version: u32,
    pub struct_size: u32,
    pub revision_identity: u64,
    pub caller_function_addr: u64,
    pub raw_instruction_addr: u64,
    pub raw_target_addr: u64,
    pub block_addr: u64,
    pub op_index: usize,
    pub target: R2SleighSourceStorageV2,
    pub calling_convention: R2SleighStringViewV2,
    pub arguments: *const R2SleighSourceCallArgumentV2,
    pub num_arguments: usize,
    pub result_kind: u32,
    pub result_storage: R2SleighSourceRegisterV2,
    pub variadic: u32,
    pub noreturn: u32,
    pub complete: u32,
}

/// Complete exact function interface for one immutable source revision.
#[repr(C)]
pub struct R2SleighSourceFunctionInterfaceV2 {
    pub schema_version: u32,
    pub struct_size: u32,
    pub revision_identity: u64,
    pub function_addr: u64,
    pub calling_convention: R2SleighStringViewV2,
    pub parameters: *const R2SleighSourceParameterV2,
    pub num_parameters: usize,
    pub stack_slots: *const R2SleighSourceStackSlotV2,
    pub num_stack_slots: usize,
    pub return_kind: u32,
    pub return_storage: R2SleighSourceRegisterV2,
    pub variadic: u32,
    pub noreturn: u32,
    pub stack_resources_complete: u32,
    pub complete: u32,
    pub call_sites: *const R2SleighSourceCallSiteInterfaceV2,
    pub num_call_sites: usize,
    /// True only when the V2 array contains every callsite represented by the
    /// immutable source snapshot; semantic completeness remains per callsite.
    pub call_sites_complete: u32,
    pub parameter_types: *const R2SleighSourceParameterTypeV2,
    pub num_parameter_types: usize,
    pub return_type_id: u32,
    pub return_carrier: R2SleighSourceCarrierProjectionV2,
    pub types: *const R2SleighSourceTypeV2,
    pub num_types: usize,
    pub aggregates: *const R2SleighSourceAggregateLayoutV2,
    pub num_aggregates: usize,
    pub exact_types_complete: u32,
    pub stack_slot_roles_complete: u32,
    /// Exact name-independent register consumed by the lifted return.
    pub return_address_storage: R2SleighSourceStorageV2,
    /// Exact name-independent register carrying the architectural stack pointer.
    pub stack_pointer_storage: R2SleighSourceStorageV2,
}

/// Native engine request graph shared by decompile and type-function requests.
/// `analysis_depth` is consumed only by type-function requests. `timeout_us`
/// combines with the session-owned cancellation token; request flags remain
/// reserved and V2 rejects every nonzero production flag today.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighEngineRequestPayloadV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub ctx: *const R2ILContext,
    pub blocks: *const *const R2ILBlock,
    pub num_blocks: usize,
    pub function_addr: u64,
    pub function_name: *const c_char,
    pub function_context: R2SleighFunctionContext,
    pub lift_quality: R2SleighLiftQuality,
    pub interproc_scope: R2SleighInterprocScope,
    pub interproc_plan: R2SleighInterprocSessionPlan,
    pub analysis_depth: u32,
    /// Relative request deadline. Zero disables the deadline.
    pub timeout_us: u64,
    /// Opaque certifying source. Null keeps this request analysis-only.
    pub radare_snapshot: *const R2SleighRadareSnapshotInputV2,
    /// Detached interface metadata is advisory and never grants certification.
    pub source_interface: *const R2SleighSourceFunctionInterfaceV2,
}

/// One entry in the stable eleven-phase engine timing inventory.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighPhaseTimingV2 {
    pub phase: u32,
    pub status: u32,
    pub elapsed_us: u64,
}

/// Borrowed response metadata. Every pointed-to byte and timing entry remains
/// valid until `response_free` is called for the owning response. Schema 2
/// exposes semantic-kernel render diagnostics as stable structured JSON.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighResponseInfoV2 {
    pub schema_version: u32,
    pub struct_size: u32,
    pub request_kind: u32,
    pub outcome: u32,
    pub phase_timings: *const R2SleighPhaseTimingV2,
    pub num_phase_timings: usize,
    pub ffi_conversion_elapsed_us: u64,
    pub diagnostics_json: R2SleighByteViewV2,
}

/// Opaque registry-owned session handle. The caller owns the obligation to
/// release the handle exactly once, after every concurrent session operation
/// has finished. `session_cancel` may run concurrently with execute;
/// `session_reset_cancellation` is valid only between execute calls.
pub struct R2SleighSessionV2 {
    error: Mutex<Option<CString>>,
    cancellation: Mutex<r2engine::EngineCancellationToken>,
}

/// Opaque registry-owned response handle. The caller owns the obligation to
/// release the handle exactly once with response_free. response_free must not
/// race response_bytes, response_info, or use of their borrowed views.
pub struct R2SleighResponseV2 {
    bytes: CString,
    diagnostics: CString,
    phase_timings: [R2SleighPhaseTimingV2; R2SLEIGH_PHASE_COUNT_V2],
    request_kind: u32,
    outcome: u32,
    ffi_conversion_elapsed_us: u64,
}

/// Opaque Rust-owned bytes. `owned_bytes_view` borrows its contents and
/// `owned_bytes_free` is the only valid deallocator.
pub struct R2SleighOwnedBytesV2 {
    bytes: CString,
}

/// Opaque owner of one tagged structured analysis result.
pub struct R2SleighAnalysisResultV2 {
    kind: u32,
    raw: *mut c_void,
}

impl Drop for R2SleighAnalysisResultV2 {
    fn drop(&mut self) {
        unsafe { free_analysis_result_payload(self) };
        self.raw = ptr::null_mut();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LiftHandleKind {
    Context,
    Block,
    OwnedBytes,
    AnalysisResult,
    PlannerResult,
}

struct LiftHandleEntry {
    kind: LiftHandleKind,
    generation: u64,
    owner: u64,
    payload: usize,
    creator_thread: ThreadId,
}

struct LiftHandleRegistry {
    next_generation: u64,
    handles: BTreeMap<usize, LiftHandleEntry>,
}

enum EngineHandlePayload {
    Session(Arc<R2SleighSessionV2>),
    Response(Arc<R2SleighResponseV2>),
}

struct EngineHandleRegistry {
    next_generation: u64,
    handles: BTreeMap<usize, EngineHandlePayload>,
}

impl Default for EngineHandleRegistry {
    fn default() -> Self {
        Self {
            next_generation: 1,
            handles: BTreeMap::new(),
        }
    }
}

impl Default for LiftHandleRegistry {
    fn default() -> Self {
        Self {
            next_generation: 1,
            handles: BTreeMap::new(),
        }
    }
}

thread_local! {
    static LIFT_LAST_ERROR: RefCell<Option<CString>> = const { RefCell::new(None) };
}

/// One immutable switch case copied into a lifted block.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighSwitchCaseV2 {
    pub value: u64,
    pub target: u64,
}

/// Exact identity of one direct call in a lifted block.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighDirectCallIdentityV2 {
    pub op_index: usize,
    pub target_space: u32,
    pub target_custom_space: u32,
    pub target_offset: u64,
    pub target_size: u32,
}

/// One bounded text-analysis request over registry-owned lift handles.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighAnalysisRenderRequestV2 {
    pub kind: u32,
    pub context: *const R2ILContext,
    pub blocks: *const *const R2ILBlock,
    pub num_blocks: usize,
    pub op_index: usize,
    pub argument: R2SleighStringViewV2,
}

/// One explicitly linked symbol in an immutable per-scope request snapshot.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighScopeSymbolV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub schema_version: u32,
    pub addr: u64,
    pub name: R2SleighStringViewV2,
    pub linkage: u32,
}

/// One bounded symbolic request over registry-owned scoped lift handles.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighScopeRenderRequestV2 {
    pub kind: u32,
    pub context: *const R2ILContext,
    pub functions: *const R2ILFunctionBlocks,
    pub num_functions: usize,
    pub entry_addr: u64,
    pub target_addr: u64,
    pub replay_seed: *const c_void,
    pub argument: R2SleighStringViewV2,
    pub external_context: R2SleighStringViewV2,
    pub symbols: *const R2SleighScopeSymbolV2,
    pub num_symbols: usize,
    pub merge_states: u32,
}

/// One bounded structured-analysis request over registry-owned lift handles.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighAnalysisQueryRequestV2 {
    pub kind: u32,
    pub context: *const R2ILContext,
    pub blocks: *const *const R2ILBlock,
    pub num_blocks: usize,
    pub function_addr: u64,
    pub function_name: R2SleighStringViewV2,
    pub input_values: *const u64,
    pub num_input_values: usize,
}

/// Borrowed arrays owned by one `R2SleighAnalysisResultV2`.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct R2SleighAnalysisResultViewV2 {
    pub kind: u32,
    pub primary: *const c_void,
    pub primary_count: usize,
    pub secondary: *const c_void,
    pub secondary_count: usize,
    pub tertiary: *const c_void,
    pub tertiary_count: usize,
    pub quaternary: *const c_void,
    pub quaternary_count: usize,
}

/// Stable V2 function table. Every callback contains its own unwind barrier.
#[repr(C)]
pub struct R2SleighApiV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub capabilities: u64,
    pub radare_abi_version: u32,
    pub session_config_size: u32,
    pub request_size: u32,
    pub engine_request_payload_size: u32,
    pub function_context_size: u32,
    pub context_param_size: u32,
    pub context_var_size: u32,
    pub context_base_member_size: u32,
    pub context_enum_variant_size: u32,
    pub context_base_type_size: u32,
    pub context_callee_size: u32,
    pub lift_quality_size: u32,
    pub interproc_seed_size: u32,
    pub interproc_scope_size: u32,
    pub interproc_plan_size: u32,
    pub source_function_interface_size: u32,
    pub source_parameter_size: u32,
    pub source_parameter_type_size: u32,
    pub source_carrier_projection_size: u32,
    pub source_type_size: u32,
    pub source_aggregate_member_size: u32,
    pub source_aggregate_layout_size: u32,
    pub source_register_size: u32,
    pub source_stack_slot_size: u32,
    pub source_storage_size: u32,
    pub source_call_argument_size: u32,
    pub source_call_site_interface_size: u32,
    pub byte_view_size: u32,
    pub string_view_size: u32,
    pub phase_timing_size: u32,
    pub response_info_size: u32,
    pub switch_case_size: u32,
    pub direct_call_identity_size: u32,
    pub analysis_render_request_size: u32,
    pub scope_render_request_size: u32,
    pub scope_symbol_size: u32,
    pub analysis_query_request_size: u32,
    pub analysis_result_view_size: u32,
    pub planner_query_request_size: u32,
    pub planner_query_response_size: u32,
    pub planner_target_input_size: u32,
    pub planner_result_view_size: u32,
    pub radare_snapshot_input_size: u32,
    pub radare_accessors_size: u32,
    pub session_create:
        extern "C" fn(*const R2SleighSessionConfigV2, *mut *mut R2SleighSessionV2) -> u32,
    pub session_free: extern "C" fn(*mut R2SleighSessionV2) -> u32,
    pub session_cancel: extern "C" fn(*const R2SleighSessionV2) -> u32,
    pub session_reset_cancellation: extern "C" fn(*const R2SleighSessionV2) -> u32,
    /// # Safety
    ///
    /// Every borrowed request pointer, opaque source handle, and callback table
    /// must remain valid and immutable for the full synchronous call.
    pub execute: unsafe extern "C" fn(
        *mut R2SleighSessionV2,
        *const R2SleighRequestV2,
        *mut *mut R2SleighResponseV2,
    ) -> u32,
    pub response_bytes: extern "C" fn(*const R2SleighResponseV2, *mut R2SleighByteViewV2) -> u32,
    pub response_info: extern "C" fn(*const R2SleighResponseV2, *mut R2SleighResponseInfoV2) -> u32,
    pub response_free: extern "C" fn(*mut R2SleighResponseV2) -> u32,
    pub session_error: extern "C" fn(*const R2SleighSessionV2, *mut R2SleighByteViewV2) -> u32,
    pub lift_context_create: extern "C" fn(R2SleighStringViewV2, *mut *mut R2ILContext) -> u32,
    pub lift_context_free: extern "C" fn(*mut R2ILContext) -> u32,
    pub lift_context_is_loaded: extern "C" fn(*const R2ILContext, *mut u32) -> u32,
    pub lift_context_arch_name: extern "C" fn(*const R2ILContext, *mut R2SleighByteViewV2) -> u32,
    pub lift_context_error: extern "C" fn(*const R2ILContext, *mut R2SleighByteViewV2) -> u32,
    pub lift_last_error: extern "C" fn(*mut R2SleighByteViewV2) -> u32,
    pub lift_context_reg_profile:
        extern "C" fn(*const R2ILContext, *mut *mut R2SleighOwnedBytesV2) -> u32,
    pub lift_instruction:
        extern "C" fn(*mut R2ILContext, R2SleighByteViewV2, u64, *mut *mut R2ILBlock) -> u32,
    pub lift_block:
        extern "C" fn(*mut R2ILContext, R2SleighByteViewV2, u64, u32, *mut *mut R2ILBlock) -> u32,
    pub lift_context_set_semantic_metadata: extern "C" fn(*mut R2ILContext, u32) -> u32,
    pub lift_block_free: extern "C" fn(*mut R2ILBlock) -> u32,
    pub lift_block_validate: extern "C" fn(*mut R2ILContext, *const R2ILBlock) -> u32,
    pub lift_block_set_switch_info: extern "C" fn(
        *mut R2ILBlock,
        u64,
        u64,
        u64,
        u64,
        u32,
        *const R2SleighSwitchCaseV2,
        usize,
    ) -> u32,
    pub lift_block_op_count: extern "C" fn(*const R2ILBlock, *mut usize) -> u32,
    pub lift_block_direct_call_identity: extern "C" fn(
        *const R2ILBlock,
        u64,
        u64,
        *mut u32,
        *mut R2SleighDirectCallIdentityV2,
    ) -> u32,
    pub lift_block_size: extern "C" fn(*const R2ILBlock, *mut u32) -> u32,
    pub lift_block_addr: extern "C" fn(*const R2ILBlock, *mut u64) -> u32,
    pub lift_block_mnemonic: extern "C" fn(
        *const R2ILContext,
        R2SleighByteViewV2,
        u64,
        *mut *mut R2SleighOwnedBytesV2,
    ) -> u32,
    pub lift_block_type: extern "C" fn(*const R2ILBlock, *mut u32) -> u32,
    pub lift_block_jump: extern "C" fn(*const R2ILBlock, *mut u64) -> u32,
    pub lift_block_fail: extern "C" fn(*const R2ILBlock, *mut u64) -> u32,
    pub owned_bytes_view:
        extern "C" fn(*const R2SleighOwnedBytesV2, *mut R2SleighByteViewV2) -> u32,
    pub owned_bytes_free: extern "C" fn(*mut R2SleighOwnedBytesV2) -> u32,
    pub analysis_render: extern "C" fn(
        *const R2SleighAnalysisRenderRequestV2,
        *mut *mut R2SleighOwnedBytesV2,
    ) -> u32,
    pub scope_render:
        extern "C" fn(*const R2SleighScopeRenderRequestV2, *mut *mut R2SleighOwnedBytesV2) -> u32,
    pub analysis_query: extern "C" fn(
        *const R2SleighAnalysisQueryRequestV2,
        *mut *mut R2SleighAnalysisResultV2,
    ) -> u32,
    pub analysis_result_view:
        extern "C" fn(*const R2SleighAnalysisResultV2, *mut R2SleighAnalysisResultViewV2) -> u32,
    pub analysis_result_free: extern "C" fn(*mut R2SleighAnalysisResultV2) -> u32,
    pub engine_cache_reset: extern "C" fn() -> u32,
    pub planner_query: extern "C" fn(
        *const R2SleighPlannerQueryRequestV2,
        *mut R2SleighPlannerQueryResponseV2,
    ) -> u32,
    pub planner_result_view:
        extern "C" fn(*const R2SleighPlannerResultV2, *mut R2SleighPlannerResultViewV2) -> u32,
    pub planner_result_copy:
        extern "C" fn(*const R2SleighPlannerResultV2, u32, *mut u64, usize, *mut usize) -> u32,
    pub planner_result_free: extern "C" fn(*mut R2SleighPlannerResultV2) -> u32,
}

#[derive(Debug)]
struct BoundaryError {
    status: u32,
    message: String,
}

impl BoundaryError {
    fn invalid(message: impl Into<String>) -> Self {
        Self {
            status: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2,
            message: message.into(),
        }
    }

    fn abi(message: impl Into<String>) -> Self {
        Self {
            status: R2SLEIGH_STATUS_ABI_MISMATCH_V2,
            message: message.into(),
        }
    }

    fn unsupported(message: impl Into<String>) -> Self {
        Self {
            status: R2SLEIGH_STATUS_UNSUPPORTED_V2,
            message: message.into(),
        }
    }

    fn limit(message: impl Into<String>) -> Self {
        Self {
            status: R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2,
            message: message.into(),
        }
    }

    fn engine(message: impl Into<String>) -> Self {
        Self {
            status: R2SLEIGH_STATUS_ENGINE_ERROR_V2,
            message: message.into(),
        }
    }
}

fn u32_size<T>() -> u32 {
    u32::try_from(size_of::<T>()).expect("FFI object size fits u32")
}

fn set_session_error(session: &R2SleighSessionV2, message: &str) {
    if let Ok(mut error) = session.error.lock() {
        *error = CString::new(message).ok();
    }
}

fn clear_session_error(session: &R2SleighSessionV2) {
    if let Ok(mut error) = session.error.lock() {
        *error = None;
    }
}

fn valid_object_ptr<T>(value: *const T, label: &str) -> Result<(), BoundaryError> {
    if value.is_null() {
        return Err(BoundaryError::invalid(format!("{label} is null")));
    }
    if !(value as usize).is_multiple_of(align_of::<T>()) {
        return Err(BoundaryError::invalid(format!("{label} is misaligned")));
    }
    Ok(())
}

fn valid_output_ptr<T>(value: *mut T, label: &str) -> Result<(), BoundaryError> {
    valid_object_ptr(value.cast_const(), label)
}

fn registered_session(
    handle: *const R2SleighSessionV2,
) -> Result<Arc<R2SleighSessionV2>, BoundaryError> {
    let key = engine_handle_key(handle, "session")?;
    lock_engine_registry().session(key)
}

fn registered_response(
    handle: *const R2SleighResponseV2,
) -> Result<Arc<R2SleighResponseV2>, BoundaryError> {
    let key = engine_handle_key(handle, "response")?;
    lock_engine_registry().response(key)
}

fn retire_session(handle: *mut R2SleighSessionV2) -> Result<(), BoundaryError> {
    let key = engine_handle_key(handle, "session")?;
    lock_engine_registry().retire_session(key)
}

fn retire_response(handle: *mut R2SleighResponseV2) -> Result<(), BoundaryError> {
    let key = engine_handle_key(handle, "response")?;
    lock_engine_registry().retire_response(key)
}

fn engine_registry() -> &'static Mutex<EngineHandleRegistry> {
    static REGISTRY: OnceLock<Mutex<EngineHandleRegistry>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(EngineHandleRegistry::default()))
}

fn lock_engine_registry() -> MutexGuard<'static, EngineHandleRegistry> {
    engine_registry()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn engine_handle_key<T>(handle: *const T, label: &str) -> Result<usize, BoundaryError> {
    if handle.is_null() {
        return Err(BoundaryError::invalid(format!("{label} is null")));
    }
    let key = handle as usize;
    if !key.is_multiple_of(align_of::<T>()) {
        return Err(BoundaryError::invalid(format!("{label} is misaligned")));
    }
    Ok(key)
}

fn opaque_handle_stride() -> usize {
    align_of::<R2SleighSessionV2>()
        .max(align_of::<R2SleighResponseV2>())
        .max(align_of::<R2ILContext>())
        .max(align_of::<R2ILBlock>())
        .max(align_of::<R2SleighOwnedBytesV2>())
        .max(align_of::<R2SleighAnalysisResultV2>())
        .max(align_of::<R2SleighPlannerResultV2>())
        .max(2)
}

fn lift_registry() -> &'static Mutex<LiftHandleRegistry> {
    static REGISTRY: OnceLock<Mutex<LiftHandleRegistry>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(LiftHandleRegistry::default()))
}

fn lock_lift_registry() -> MutexGuard<'static, LiftHandleRegistry> {
    lift_registry()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn lift_handle_key<T>(handle: *const T, label: &str) -> Result<usize, BoundaryError> {
    if handle.is_null() {
        return Err(BoundaryError::invalid(format!("{label} is null")));
    }
    let key = handle as usize;
    if !key.is_multiple_of(align_of::<T>()) {
        return Err(BoundaryError::invalid(format!("{label} is misaligned")));
    }
    Ok(key)
}

impl LiftHandleRegistry {
    fn allocate_generation(&mut self) -> Result<u64, BoundaryError> {
        let generation = self.next_generation;
        self.next_generation = self
            .next_generation
            .checked_add(1)
            .ok_or_else(|| BoundaryError::limit("lift handle generation exhausted"))?;
        Ok(generation)
    }

    fn handle_key<T>(&self, generation: u64) -> Result<usize, BoundaryError> {
        let stride = opaque_handle_stride();
        let generation = usize::try_from(generation)
            .map_err(|_| BoundaryError::limit("lift handle token space exhausted"))?;
        let generation = generation
            .checked_mul(2)
            .ok_or_else(|| BoundaryError::limit("lift handle token space exhausted"))?;
        let key = generation
            .checked_mul(stride)
            .ok_or_else(|| BoundaryError::limit("lift handle token space exhausted"))?;
        if key == 0 || !key.is_multiple_of(align_of::<T>()) {
            return Err(BoundaryError::engine("invalid generated lift handle token"));
        }
        Ok(key)
    }

    fn insert_context(
        &mut self,
        context: Box<R2ILContext>,
    ) -> Result<*mut R2ILContext, BoundaryError> {
        let generation = self.allocate_generation()?;
        let key = self.handle_key::<R2ILContext>(generation)?;
        if self.handles.contains_key(&key) {
            return Err(BoundaryError::engine("lift context handle collision"));
        }
        let payload = Box::into_raw(context) as usize;
        self.handles.insert(
            key,
            LiftHandleEntry {
                kind: LiftHandleKind::Context,
                generation,
                owner: generation,
                payload,
                creator_thread: thread::current().id(),
            },
        );
        Ok(key as *mut R2ILContext)
    }

    fn insert_block(
        &mut self,
        owner: u64,
        block: Box<R2ILBlock>,
    ) -> Result<*mut R2ILBlock, BoundaryError> {
        let generation = self.allocate_generation()?;
        let key = self.handle_key::<R2ILBlock>(generation)?;
        if self.handles.contains_key(&key) {
            return Err(BoundaryError::engine("lift block handle collision"));
        }
        let payload = Box::into_raw(block) as usize;
        self.handles.insert(
            key,
            LiftHandleEntry {
                kind: LiftHandleKind::Block,
                generation,
                owner,
                payload,
                creator_thread: thread::current().id(),
            },
        );
        Ok(key as *mut R2ILBlock)
    }

    fn insert_owned_bytes(
        &mut self,
        owner: u64,
        bytes: R2SleighOwnedBytesV2,
    ) -> Result<*mut R2SleighOwnedBytesV2, BoundaryError> {
        let bytes = Box::new(bytes);
        let generation = self.allocate_generation()?;
        let key = self.handle_key::<R2SleighOwnedBytesV2>(generation)?;
        if self.handles.contains_key(&key) {
            return Err(BoundaryError::engine("owned-byte handle collision"));
        }
        let payload = Box::into_raw(bytes) as usize;
        self.handles.insert(
            key,
            LiftHandleEntry {
                kind: LiftHandleKind::OwnedBytes,
                generation,
                owner,
                payload,
                creator_thread: thread::current().id(),
            },
        );
        Ok(key as *mut R2SleighOwnedBytesV2)
    }

    fn insert_analysis_result(
        &mut self,
        owner: u64,
        result: R2SleighAnalysisResultV2,
    ) -> Result<*mut R2SleighAnalysisResultV2, BoundaryError> {
        let result = Box::new(result);
        let generation = self.allocate_generation()?;
        let key = self.handle_key::<R2SleighAnalysisResultV2>(generation)?;
        if self.handles.contains_key(&key) {
            return Err(BoundaryError::engine("analysis-result handle collision"));
        }
        let payload = Box::into_raw(result) as usize;
        self.handles.insert(
            key,
            LiftHandleEntry {
                kind: LiftHandleKind::AnalysisResult,
                generation,
                owner,
                payload,
                creator_thread: thread::current().id(),
            },
        );
        Ok(key as *mut R2SleighAnalysisResultV2)
    }

    fn insert_planner_result(
        &mut self,
        result: R2SleighPlannerResultV2,
    ) -> Result<*mut R2SleighPlannerResultV2, BoundaryError> {
        let generation = self.allocate_generation()?;
        let key = self.handle_key::<R2SleighPlannerResultV2>(generation)?;
        if self.handles.contains_key(&key) {
            return Err(BoundaryError::engine("planner-result handle collision"));
        }
        let payload = Box::into_raw(Box::new(result)) as usize;
        self.handles.insert(
            key,
            LiftHandleEntry {
                kind: LiftHandleKind::PlannerResult,
                generation,
                owner: 0,
                payload,
                creator_thread: thread::current().id(),
            },
        );
        Ok(key as *mut R2SleighPlannerResultV2)
    }

    fn entry(
        &self,
        key: usize,
        kind: LiftHandleKind,
        label: &str,
    ) -> Result<&LiftHandleEntry, BoundaryError> {
        let entry = self
            .handles
            .get(&key)
            .ok_or_else(|| BoundaryError::invalid(format!("{label} is unknown or stale")))?;
        if entry.kind != kind {
            return Err(BoundaryError::invalid(format!(
                "{label} has the wrong handle kind or generation"
            )));
        }
        if entry.creator_thread != thread::current().id() {
            return Err(BoundaryError::invalid(format!(
                "{label} belongs to a different thread"
            )));
        }
        Ok(entry)
    }

    fn entry_mut(
        &mut self,
        key: usize,
        kind: LiftHandleKind,
        label: &str,
    ) -> Result<&mut LiftHandleEntry, BoundaryError> {
        let entry = self
            .handles
            .get_mut(&key)
            .ok_or_else(|| BoundaryError::invalid(format!("{label} is unknown or stale")))?;
        if entry.kind != kind {
            return Err(BoundaryError::invalid(format!(
                "{label} has the wrong handle kind or generation"
            )));
        }
        if entry.creator_thread != thread::current().id() {
            return Err(BoundaryError::invalid(format!(
                "{label} belongs to a different thread"
            )));
        }
        Ok(entry)
    }

    fn payload<T>(
        &self,
        key: usize,
        kind: LiftHandleKind,
        label: &str,
    ) -> Result<*mut T, BoundaryError> {
        let entry = self.entry(key, kind, label)?;
        Ok(entry.payload as *mut T)
    }

    fn owner_for_key(&self, key: usize) -> Option<u64> {
        self.handles.get(&key).map(|entry| entry.owner)
    }

    fn retire(
        &mut self,
        key: usize,
        kind: LiftHandleKind,
        label: &str,
    ) -> Result<(), BoundaryError> {
        self.entry(key, kind, label)?;
        let entry = self
            .handles
            .remove(&key)
            .expect("validated lift handle remains registered");
        unsafe {
            match entry.kind {
                LiftHandleKind::Context => drop(Box::from_raw(entry.payload as *mut R2ILContext)),
                LiftHandleKind::Block => drop(Box::from_raw(entry.payload as *mut R2ILBlock)),
                LiftHandleKind::OwnedBytes => {
                    drop(Box::from_raw(entry.payload as *mut R2SleighOwnedBytesV2))
                }
                LiftHandleKind::AnalysisResult => {
                    drop(Box::from_raw(
                        entry.payload as *mut R2SleighAnalysisResultV2,
                    ));
                }
                LiftHandleKind::PlannerResult => {
                    drop(Box::from_raw(entry.payload as *mut R2SleighPlannerResultV2));
                }
            }
        }
        Ok(())
    }

    fn record_error(&mut self, key: Option<usize>, message: &str) {
        let Some(owner) = key.and_then(|key| self.owner_for_key(key)) else {
            return;
        };
        if let Some((key, _)) = self
            .handles
            .iter()
            .find(|(_, entry)| entry.kind == LiftHandleKind::Context && entry.generation == owner)
        {
            let payload = self.handles[key].payload as *mut R2ILContext;
            unsafe { (&mut *payload).set_error(message) };
        }
    }
}

impl EngineHandleRegistry {
    fn allocate_generation(&mut self) -> Result<u64, BoundaryError> {
        let generation = self.next_generation;
        self.next_generation = self
            .next_generation
            .checked_add(1)
            .ok_or_else(|| BoundaryError::limit("engine handle generation exhausted"))?;
        Ok(generation)
    }

    fn handle_key<T>(&self, generation: u64) -> Result<usize, BoundaryError> {
        let generation = usize::try_from(generation)
            .map_err(|_| BoundaryError::limit("engine handle token space exhausted"))?;
        let slot = generation
            .checked_mul(2)
            .and_then(|value| value.checked_add(1))
            .ok_or_else(|| BoundaryError::limit("engine handle token space exhausted"))?;
        let key = slot
            .checked_mul(opaque_handle_stride())
            .ok_or_else(|| BoundaryError::limit("engine handle token space exhausted"))?;
        if key == 0 || !key.is_multiple_of(align_of::<T>()) {
            return Err(BoundaryError::engine(
                "invalid generated engine handle token",
            ));
        }
        Ok(key)
    }

    fn insert_session(
        &mut self,
        session: Arc<R2SleighSessionV2>,
    ) -> Result<*mut R2SleighSessionV2, BoundaryError> {
        let generation = self.allocate_generation()?;
        let key = self.handle_key::<R2SleighSessionV2>(generation)?;
        if self.handles.contains_key(&key) {
            return Err(BoundaryError::engine("session handle collision"));
        }
        self.handles
            .insert(key, EngineHandlePayload::Session(session));
        Ok(key as *mut R2SleighSessionV2)
    }

    fn insert_response(
        &mut self,
        response: Arc<R2SleighResponseV2>,
    ) -> Result<*mut R2SleighResponseV2, BoundaryError> {
        let generation = self.allocate_generation()?;
        let key = self.handle_key::<R2SleighResponseV2>(generation)?;
        if self.handles.contains_key(&key) {
            return Err(BoundaryError::engine("response handle collision"));
        }
        self.handles
            .insert(key, EngineHandlePayload::Response(response));
        Ok(key as *mut R2SleighResponseV2)
    }

    fn session(&self, key: usize) -> Result<Arc<R2SleighSessionV2>, BoundaryError> {
        let payload = self
            .handles
            .get(&key)
            .ok_or_else(|| BoundaryError::invalid("session is unknown or stale"))?;
        match payload {
            EngineHandlePayload::Session(session) => Ok(Arc::clone(session)),
            EngineHandlePayload::Response(_) => Err(BoundaryError::invalid(
                "session has the wrong handle kind or generation",
            )),
        }
    }

    fn response(&self, key: usize) -> Result<Arc<R2SleighResponseV2>, BoundaryError> {
        let payload = self
            .handles
            .get(&key)
            .ok_or_else(|| BoundaryError::invalid("response is unknown or stale"))?;
        match payload {
            EngineHandlePayload::Response(response) => Ok(Arc::clone(response)),
            EngineHandlePayload::Session(_) => Err(BoundaryError::invalid(
                "response has the wrong handle kind or generation",
            )),
        }
    }

    fn retire_session(&mut self, key: usize) -> Result<(), BoundaryError> {
        match self.handles.get(&key) {
            Some(EngineHandlePayload::Session(_)) => {}
            Some(EngineHandlePayload::Response(_)) => {
                return Err(BoundaryError::invalid(
                    "session has the wrong handle kind or generation",
                ));
            }
            None => return Err(BoundaryError::invalid("session is unknown or stale")),
        }
        self.handles.remove(&key);
        Ok(())
    }

    fn retire_response(&mut self, key: usize) -> Result<(), BoundaryError> {
        match self.handles.get(&key) {
            Some(EngineHandlePayload::Response(_)) => {}
            Some(EngineHandlePayload::Session(_)) => {
                return Err(BoundaryError::invalid(
                    "response has the wrong handle kind or generation",
                ));
            }
            None => return Err(BoundaryError::invalid("response is unknown or stale")),
        }
        self.handles.remove(&key);
        Ok(())
    }
}

unsafe fn free_analysis_result_payload(result: &R2SleighAnalysisResultV2) {
    match result.kind {
        R2SLEIGH_QUERY_BLOCK_VALUES_V2 => super::r2il_block_values_free(result.raw.cast()),
        R2SLEIGH_QUERY_TAINT_SUMMARY_V2 => {
            super::analysis::taint::r2taint_function_summary_free(result.raw.cast())
        }
        R2SLEIGH_QUERY_ANNOTATIONS_V2 => super::r2sleigh_annotations_free(result.raw.cast()),
        R2SLEIGH_QUERY_DIRECT_TARGETS_V2 | R2SLEIGH_QUERY_SYMBOLIC_TARGETS_V2 => {
            super::r2sleigh_u64_array_free(result.raw.cast())
        }
        R2SLEIGH_QUERY_RUNTIME_SOURCES_V2 => {
            super::r2sleigh_runtime_sources_free(result.raw.cast())
        }
        R2SLEIGH_QUERY_RECOVERED_VARS_V2 => {
            super::types::r2sleigh_recovered_vars_free(result.raw.cast())
        }
        R2SLEIGH_QUERY_DATA_REFS_V2 => super::types::r2sleigh_data_refs_free(result.raw.cast()),
        _ => {}
    }
}

fn lift_boundary_for<T>(
    handle: *const T,
    operation: impl FnOnce() -> Result<(), BoundaryError>,
) -> u32 {
    let key = (!handle.is_null()).then_some(handle as usize);
    LIFT_LAST_ERROR.with(|error| *error.borrow_mut() = None);
    match catch_unwind(AssertUnwindSafe(operation)) {
        Ok(Ok(())) => R2SLEIGH_STATUS_OK_V2,
        Ok(Err(error)) => {
            LIFT_LAST_ERROR
                .with(|slot| *slot.borrow_mut() = CString::new(error.message.as_str()).ok());
            lock_lift_registry().record_error(key, &error.message);
            error.status
        }
        Err(_) => {
            LIFT_LAST_ERROR
                .with(|slot| *slot.borrow_mut() = CString::new("panic in lift-core callback").ok());
            lock_lift_registry().record_error(key, "panic in lift-core callback");
            R2SLEIGH_STATUS_PANIC_V2
        }
    }
}

fn lift_boundary(operation: impl FnOnce() -> Result<(), BoundaryError>) -> u32 {
    lift_boundary_for(ptr::null::<c_void>(), operation)
}

#[derive(Default)]
struct ValidationBudget {
    blocks: usize,
    ops: usize,
    context_items: usize,
    nested_items: usize,
    string_bytes: usize,
    json_bytes: usize,
}

impl ValidationBudget {
    fn charge(
        current: &mut usize,
        amount: usize,
        cap: usize,
        label: &str,
    ) -> Result<(), BoundaryError> {
        *current = current
            .checked_add(amount)
            .ok_or_else(|| BoundaryError::limit(format!("aggregate {label} count overflow")))?;
        if *current > cap {
            return Err(BoundaryError::limit(format!(
                "aggregate {label} exceeds cap ({cap})"
            )));
        }
        Ok(())
    }

    fn charge_blocks(&mut self, blocks: usize, label: &str) -> Result<(), BoundaryError> {
        Self::charge(
            &mut self.blocks,
            blocks,
            R2SLEIGH_MAX_AGGREGATE_BLOCKS_V2,
            label,
        )
    }

    fn charge_ops(&mut self, ops: usize, label: &str) -> Result<(), BoundaryError> {
        Self::charge(&mut self.ops, ops, R2SLEIGH_MAX_AGGREGATE_OPS_V2, label)
    }

    fn charge_context_items(&mut self, items: usize, label: &str) -> Result<(), BoundaryError> {
        Self::charge(
            &mut self.context_items,
            items,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            label,
        )
    }

    fn charge_nested_items(&mut self, items: usize, label: &str) -> Result<(), BoundaryError> {
        Self::charge(
            &mut self.nested_items,
            items,
            R2SLEIGH_MAX_NESTED_ITEMS_V2,
            label,
        )
    }

    fn charge_string_bytes(&mut self, bytes: usize, label: &str) -> Result<(), BoundaryError> {
        Self::charge(
            &mut self.string_bytes,
            bytes,
            R2SLEIGH_MAX_AGGREGATE_STRING_BYTES_V2,
            label,
        )
    }

    fn charge_json_bytes(&mut self, bytes: usize, label: &str) -> Result<(), BoundaryError> {
        Self::charge(
            &mut self.json_bytes,
            bytes,
            R2SLEIGH_MAX_AGGREGATE_JSON_BYTES_V2,
            label,
        )
    }
}

unsafe fn checked_slice<'a, T>(
    data: *const T,
    count: usize,
    cap: usize,
    label: &str,
) -> Result<&'a [T], BoundaryError> {
    if count > cap || count > isize::MAX as usize / size_of::<T>().max(1) {
        return Err(BoundaryError::limit(format!("{label} count exceeds cap")));
    }
    if count == 0 {
        return Ok(&[]);
    }
    valid_object_ptr(data, label)?;
    Ok(unsafe { slice::from_raw_parts(data, count) })
}

unsafe fn bounded_cstr<'a>(
    data: *const i8,
    cap: usize,
    label: &str,
    budget: &mut ValidationBudget,
    json: bool,
) -> Result<Option<&'a str>, BoundaryError> {
    if data.is_null() {
        return Ok(None);
    }
    let mut len = 0usize;
    while len <= cap {
        if unsafe { *data.add(len) } == 0 {
            break;
        }
        len += 1;
    }
    if len > cap {
        return Err(BoundaryError::limit(format!(
            "{label} is not terminated within its byte cap"
        )));
    }
    if json {
        budget.charge_json_bytes(len, label)?;
    } else {
        budget.charge_string_bytes(len, label)?;
    }
    let bytes = unsafe { slice::from_raw_parts(data.cast::<u8>(), len) };
    str::from_utf8(bytes)
        .map(Some)
        .map_err(|_| BoundaryError::invalid(format!("{label} is not UTF-8")))
}

unsafe fn string_view<'a>(
    view: R2SleighStringViewV2,
    cap: usize,
    label: &str,
    budget: &mut ValidationBudget,
) -> Result<&'a str, BoundaryError> {
    let bytes = unsafe { checked_slice(view.data, view.len, cap, label)? };
    budget.charge_string_bytes(bytes.len(), label)?;
    str::from_utf8(bytes).map_err(|_| BoundaryError::invalid(format!("{label} is not UTF-8")))
}

unsafe fn validate_context_param(
    param: &R2SleighContextParam,
    label: &str,
    budget: &mut ValidationBudget,
) -> Result<(), BoundaryError> {
    unsafe {
        bounded_cstr(
            param.name,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            &format!("{label}.name"),
            budget,
            false,
        )?;
        bounded_cstr(
            param.type_name,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            &format!("{label}.type_name"),
            budget,
            false,
        )?;
        bounded_cstr(
            param.cc_reg,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            &format!("{label}.cc_reg"),
            budget,
            false,
        )?;
    }
    Ok(())
}

unsafe fn validate_context_var(
    var: &R2SleighContextVar,
    label: &str,
    budget: &mut ValidationBudget,
) -> Result<(), BoundaryError> {
    if !matches!(var.has_offset, 0 | 1) || !matches!(var.is_arg, 0 | 1) {
        return Err(BoundaryError::invalid(format!(
            "{label} contains a non-boolean flag"
        )));
    }
    let strings = [
        (var.name, "name"),
        (var.type_name, "type_name"),
        (var.reg, "reg"),
        (var.base, "base"),
        (var.param_name, "param_name"),
        (var.source_reg, "source_reg"),
    ];
    for (data, field) in strings {
        unsafe {
            bounded_cstr(
                data,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("{label}.{field}"),
                budget,
                false,
            )?
        };
    }
    Ok(())
}

unsafe fn validate_base_type(
    base_type: &R2SleighContextBaseType,
    label: &str,
    budget: &mut ValidationBudget,
) -> Result<(), BoundaryError> {
    if !matches!(base_type.has_size_bits, 0 | 1) {
        return Err(BoundaryError::invalid(format!(
            "{label}.has_size_bits is not boolean"
        )));
    }
    unsafe {
        bounded_cstr(
            base_type.name,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            &format!("{label}.name"),
            budget,
            false,
        )?;
        bounded_cstr(
            base_type.type_name,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            &format!("{label}.type_name"),
            budget,
            false,
        )?;
    }
    let members = unsafe {
        checked_slice(
            base_type.members,
            base_type.num_members,
            R2SLEIGH_MAX_NESTED_ITEMS_V2,
            &format!("{label}.members"),
        )?
    };
    let variants = unsafe {
        checked_slice(
            base_type.variants,
            base_type.num_variants,
            R2SLEIGH_MAX_NESTED_ITEMS_V2,
            &format!("{label}.variants"),
        )?
    };
    let nested_items = members
        .len()
        .checked_add(variants.len())
        .ok_or_else(|| BoundaryError::limit("nested type item count overflow"))?;
    budget.charge_nested_items(nested_items, "nested type items")?;
    for (index, member) in members.iter().enumerate() {
        if !matches!(member.has_size_bits, 0 | 1) {
            return Err(BoundaryError::invalid(format!(
                "{label}.members[{index}].has_size_bits is not boolean"
            )));
        }
        unsafe {
            bounded_cstr(
                member.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("{label}.members[{index}].name"),
                budget,
                false,
            )?;
            bounded_cstr(
                member.type_name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("{label}.members[{index}].type_name"),
                budget,
                false,
            )?;
        }
    }
    for (index, variant) in variants.iter().enumerate() {
        unsafe {
            bounded_cstr(
                variant.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("{label}.variants[{index}].name"),
                budget,
                false,
            )?;
        }
    }
    Ok(())
}

unsafe fn validate_callee(
    callee: &R2SleighContextCallee,
    label: &str,
    budget: &mut ValidationBudget,
) -> Result<(), BoundaryError> {
    if !matches!(callee.signature_noreturn, 0 | 1) {
        return Err(BoundaryError::invalid(format!(
            "{label}.signature_noreturn is not boolean"
        )));
    }
    let strings = [
        (callee.name, "name"),
        (callee.signature_name, "signature_name"),
        (callee.signature_ret_type, "signature_ret_type"),
        (callee.signature_callconv, "signature_callconv"),
    ];
    for (data, field) in strings {
        unsafe {
            bounded_cstr(
                data,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("{label}.{field}"),
                budget,
                false,
            )?
        };
    }
    let params = unsafe {
        checked_slice(
            callee.signature_params,
            callee.num_signature_params,
            R2SLEIGH_MAX_NESTED_ITEMS_V2,
            &format!("{label}.signature_params"),
        )?
    };
    budget.charge_nested_items(params.len(), "nested callee parameters")?;
    for (index, param) in params.iter().enumerate() {
        unsafe { validate_context_param(param, &format!("{label}.params[{index}]"), budget)? };
    }
    Ok(())
}

unsafe fn validate_function_context(
    context: &R2SleighFunctionContext,
    budget: &mut ValidationBudget,
) -> Result<(), BoundaryError> {
    if context.schema_version != R2SLEIGH_FUNCTION_CONTEXT_SCHEMA_V2 {
        return Err(BoundaryError::abi(
            "function context schema version mismatch",
        ));
    }
    if !matches!(context.signature_noreturn, 0 | 1) {
        return Err(BoundaryError::invalid(
            "function_context.signature_noreturn is not boolean",
        ));
    }
    let strings = [
        (
            context.external_context_json,
            R2SLEIGH_MAX_JSON_BYTES_V2,
            "external_context_json",
        ),
        (
            context.signature_name,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            "signature_name",
        ),
        (
            context.signature_ret_type,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            "signature_ret_type",
        ),
        (
            context.signature_callconv,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            "signature_callconv",
        ),
        (
            context.assumptions_json,
            R2SLEIGH_MAX_JSON_BYTES_V2,
            "assumptions_json",
        ),
    ];
    for (data, cap, label) in strings {
        let json = label.ends_with("_json");
        unsafe { bounded_cstr(data, cap, label, budget, json)? };
    }
    let params = unsafe {
        checked_slice(
            context.params,
            context.num_params,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "function_context.params",
        )?
    };
    let vars = unsafe {
        checked_slice(
            context.vars,
            context.num_vars,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "function_context.vars",
        )?
    };
    let base_types = unsafe {
        checked_slice(
            context.base_types,
            context.num_base_types,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "function_context.base_types",
        )?
    };
    let callees = unsafe {
        checked_slice(
            context.callees,
            context.num_callees,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "function_context.callees",
        )?
    };
    let context_items = params
        .len()
        .checked_add(vars.len())
        .and_then(|count| count.checked_add(base_types.len()))
        .and_then(|count| count.checked_add(callees.len()))
        .ok_or_else(|| BoundaryError::limit("function context item count overflow"))?;
    budget.charge_context_items(context_items, "function context items")?;
    for (index, param) in params.iter().enumerate() {
        unsafe { validate_context_param(param, &format!("params[{index}]"), budget)? };
    }
    for (index, var) in vars.iter().enumerate() {
        unsafe { validate_context_var(var, &format!("vars[{index}]"), budget)? };
    }
    for (index, base_type) in base_types.iter().enumerate() {
        unsafe { validate_base_type(base_type, &format!("base_types[{index}]"), budget)? };
    }
    for (index, callee) in callees.iter().enumerate() {
        unsafe { validate_callee(callee, &format!("callees[{index}]"), budget)? };
    }
    Ok(())
}

unsafe fn validate_blocks(
    blocks: *const *const R2ILBlock,
    count: usize,
    max_blocks: usize,
    max_ops: usize,
    label: &str,
    budget: &mut ValidationBudget,
) -> Result<(), BoundaryError> {
    let blocks = unsafe { checked_slice(blocks, count, max_blocks, label)? };
    budget.charge_blocks(blocks.len(), label)?;
    let mut function_ops = 0usize;
    for (index, block) in blocks.iter().enumerate() {
        valid_object_ptr(*block, &format!("{label}[{index}]"))?;
        let block_ops = unsafe { (**block).ops.len() };
        function_ops = function_ops
            .checked_add(block_ops)
            .ok_or_else(|| BoundaryError::limit(format!("{label} operation count overflow")))?;
        if function_ops > max_ops {
            return Err(BoundaryError::limit(format!(
                "{label} operation count exceeds per-function cap ({max_ops})"
            )));
        }
    }
    budget.charge_ops(function_ops, label)?;
    Ok(())
}

unsafe fn validate_interproc_scope(
    scope: &R2SleighInterprocScope,
    budget: &mut ValidationBudget,
) -> Result<(), BoundaryError> {
    if scope.schema_version != R2SLEIGH_INTERPROC_SCOPE_SCHEMA_V2 {
        return Err(BoundaryError::abi(
            "interprocedural scope schema version mismatch",
        ));
    }
    let functions = unsafe {
        checked_slice(
            scope.functions,
            scope.num_functions,
            R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2,
            "interproc_scope.functions",
        )?
    };
    let seeds = unsafe {
        checked_slice(
            scope.seeds,
            scope.num_seeds,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "interproc_scope.seeds",
        )?
    };
    budget.charge_context_items(
        functions
            .len()
            .checked_add(seeds.len())
            .ok_or_else(|| BoundaryError::limit("interproc item count overflow"))?,
        "interproc functions and seeds",
    )?;
    for (index, function) in functions.iter().enumerate() {
        unsafe {
            bounded_cstr(
                function.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("interproc_scope.functions[{index}].name"),
                budget,
                false,
            )?;
            validate_blocks(
                function.blocks,
                function.num_blocks,
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                R2SLEIGH_MAX_FUNCTION_OPS_V2,
                &format!("interproc_scope.functions[{index}].blocks"),
                budget,
            )?;
        }
    }
    for (index, seed) in seeds.iter().enumerate() {
        let label = format!("interproc_scope.seeds[{index}]");
        unsafe {
            bounded_cstr(
                seed.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("{label}.name"),
                budget,
                false,
            )?;
        }
        if !matches!(seed.has_arg_count_hint, 0 | 1) {
            return Err(BoundaryError::invalid(format!(
                "{label}.has_arg_count_hint is not boolean"
            )));
        }
        if seed.has_arg_count_hint == 1 && seed.arg_count_hint > MAX_ABI_ARGUMENTS {
            return Err(BoundaryError::limit(format!(
                "{label}.arg_count_hint exceeds ABI argument cap"
            )));
        }
    }
    Ok(())
}

fn validate_interproc_plan(plan: R2SleighInterprocSessionPlan) -> Result<(), BoundaryError> {
    if !matches!(plan.include_type_interproc_scope, 0 | 1)
        || !matches!(plan.include_root_symbolic_scope, 0 | 1)
        || !matches!(plan.interproc_converged, 0 | 1)
    {
        return Err(BoundaryError::invalid(
            "interprocedural plan contains a non-boolean flag",
        ));
    }
    if plan.interproc_iter > MAX_INTERPROC_ITERATIONS
        || plan.interproc_max_iters > MAX_INTERPROC_ITERATIONS
    {
        return Err(BoundaryError::limit(
            "interprocedural iteration count exceeds cap",
        ));
    }
    Ok(())
}

unsafe fn validate_native_input(
    input: &R2SleighEngineRequestPayloadV2,
    kind: u32,
    budget: &mut ValidationBudget,
) -> Result<(), BoundaryError> {
    let label = match kind {
        R2SLEIGH_REQUEST_DECOMPILE_V2 => "decompile",
        R2SLEIGH_REQUEST_TYPE_FUNCTION_V2 => "type_function",
        _ => return Err(BoundaryError::unsupported("unsupported request kind")),
    };
    if kind == R2SLEIGH_REQUEST_DECOMPILE_V2 && input.analysis_depth != 0 {
        return Err(BoundaryError::invalid(
            "decompile request must leave analysis_depth zero",
        ));
    }
    valid_object_ptr(input.ctx, &format!("{label}.ctx"))?;
    unsafe {
        validate_blocks(
            input.blocks,
            input.num_blocks,
            R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
            R2SLEIGH_MAX_FUNCTION_OPS_V2,
            &format!("{label}.blocks"),
            budget,
        )?;
        bounded_cstr(
            input.function_name,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            &format!("{label}.function_name"),
            budget,
            false,
        )?;
        validate_function_context(&input.function_context, budget)?;
        validate_interproc_scope(&input.interproc_scope, budget)?;
    }
    validate_interproc_plan(input.interproc_plan)
}

fn validate_register_against_arch(
    arch: &r2il::ArchSpec,
    name: &str,
    source_offset: u64,
    size: u32,
) -> Result<r2ssa::CanonicalStorageId, BoundaryError> {
    if name.is_empty() || size == 0 || source_offset.checked_add(u64::from(size)).is_none() {
        return Err(BoundaryError::invalid("invalid exact register storage"));
    }
    let mut matches = arch
        .registers
        .iter()
        .filter(|register| register.name.eq_ignore_ascii_case(name));
    let Some(register) = matches.next() else {
        return Err(BoundaryError::invalid(format!(
            "source register {name} does not uniquely match ArchSpec name/size"
        )));
    };
    if matches.next().is_some() || register.offset != source_offset || register.size != size {
        return Err(BoundaryError::invalid(format!(
            "source register {name} does not uniquely match ArchSpec coordinates"
        )));
    }
    Ok(r2ssa::CanonicalStorageId {
        space: r2ssa::CanonicalStorageSpace::Register,
        offset: register.offset,
        size: register.size,
    })
}

fn validate_full_width_register_storage_against_arch(
    arch: &r2il::ArchSpec,
    source: R2SleighSourceStorageV2,
    label: &str,
) -> Result<r2ssa::CanonicalStorageId, BoundaryError> {
    if source.space != R2SLEIGH_SOURCE_STORAGE_REGISTER_V2
        || source.custom_space != 0
        || source.size == 0
        || source.offset.checked_add(u64::from(source.size)).is_none()
        || source.size != r2il::effective_arch_address_size(arch)
    {
        return Err(BoundaryError::invalid(format!(
            "{label} is not a full-width canonical register storage"
        )));
    }
    let exact_coordinate = arch.registers.iter().any(|register| {
        register.parent.is_none()
            && register.offset == source.offset
            && register.size == source.size
    });
    if !exact_coordinate {
        return Err(BoundaryError::invalid(format!(
            "{label} does not match a full-width ArchSpec register coordinate: offset={} size={}",
            source.offset, source.size
        )));
    }
    Ok(r2ssa::CanonicalStorageId {
        space: r2ssa::CanonicalStorageSpace::Register,
        offset: source.offset,
        size: source.size,
    })
}

fn canonical_storage_ranges_overlap(
    left: r2ssa::CanonicalStorageId,
    right: r2ssa::CanonicalStorageId,
) -> bool {
    if left.space != right.space {
        return false;
    }
    let Some(left_end) = left.offset.checked_add(u64::from(left.size)) else {
        return true;
    };
    let Some(right_end) = right.offset.checked_add(u64::from(right.size)) else {
        return true;
    };
    left.offset < right_end && right.offset < left_end
}

fn exact_full_width_arch_register(
    arch: &r2il::ArchSpec,
    name: &str,
) -> Option<r2ssa::CanonicalStorageId> {
    let mut matches = arch
        .registers
        .iter()
        .filter(|register| register.name.eq_ignore_ascii_case(name));
    let register = matches.next()?;
    if matches.next().is_some()
        || register.parent.is_some()
        || register.size != r2il::effective_arch_address_size(arch)
    {
        return None;
    }
    Some(r2ssa::CanonicalStorageId {
        space: r2ssa::CanonicalStorageSpace::Register,
        offset: register.offset,
        size: register.size,
    })
}

fn project_semantic_calling_convention(
    physical: &str,
    arch: &r2il::ArchSpec,
    parameters: &[r2ssa::CanonicalStorageId],
    result: Option<r2ssa::CanonicalStorageId>,
) -> String {
    let arch_name = arch.name.to_ascii_lowercase();
    if physical.eq_ignore_ascii_case("amd64")
        && matches!(arch_name.as_str(), "x86-64" | "x86_64" | "x64" | "amd64")
        && r2il::effective_arch_address_size(arch) == 8
        && parameters.len() <= 6
    {
        let expected = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
            .into_iter()
            .take(parameters.len())
            .map(|name| exact_full_width_arch_register(arch, name))
            .collect::<Option<Vec<_>>>();
        let return_storage = exact_full_width_arch_register(arch, "rax");
        if expected.as_deref() == Some(parameters)
            && return_storage.is_some()
            && result == return_storage
        {
            return "sysv_amd64".to_owned();
        }
    }
    if !physical.eq_ignore_ascii_case("arm64")
        || !matches!(arch_name.as_str(), "aarch64" | "arm64")
        || r2il::effective_arch_address_size(arch) != 8
    {
        return physical.to_owned();
    }
    let Some(x0) = exact_full_width_arch_register(arch, "x0") else {
        return physical.to_owned();
    };
    let Some(x1) = exact_full_width_arch_register(arch, "x1") else {
        return physical.to_owned();
    };
    if parameters == [x0, x1] && result == Some(x0) {
        "aapcs64".to_owned()
    } else {
        physical.to_owned()
    }
}

fn validate_stack_base_against_arch(
    arch: &r2il::ArchSpec,
    base_kind: u32,
    name: &str,
    source_offset: u64,
    size: u32,
) -> Result<(r2ssa::StackAddressBase, r2ssa::CanonicalStorageId), BoundaryError> {
    let storage = validate_register_against_arch(arch, name, source_offset, size)?;
    if storage.size != r2il::effective_arch_address_size(arch) {
        return Err(BoundaryError::invalid(
            "source stack resource base is not a full-width ArchSpec register",
        ));
    }
    let base = match base_kind {
        R2SLEIGH_SOURCE_STACK_BASE_BP_V2 => r2ssa::StackAddressBase::FramePointer,
        R2SLEIGH_SOURCE_STACK_BASE_SP_V2 => r2ssa::StackAddressBase::StackPointer,
        _ => {
            return Err(BoundaryError::invalid(
                "source stack resource has unknown base kind",
            ));
        }
    };
    Ok((base, storage))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OwnedSourceTypeKind {
    SignedInteger,
    UnsignedInteger,
    Pointer,
    Struct,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OwnedSourceCarrierKind {
    Full,
    LowBits,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OwnedSourceCarrierProjection {
    kind: OwnedSourceCarrierKind,
    offset_bits: u64,
    size_bits: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedSourceParameterType {
    index: u32,
    type_id: u32,
    carrier: OwnedSourceCarrierProjection,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedSourceType {
    id: u32,
    kind: OwnedSourceTypeKind,
    size_bits: u64,
    align_bits: u64,
    target_type_id: Option<u32>,
    aggregate_id: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedSourceAggregateMember {
    member_id: u32,
    type_id: u32,
    offset_bits: u64,
    size_bits: u64,
    name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedSourceAggregateLayout {
    id: u32,
    type_id: u32,
    size_bits: u64,
    align_bits: u64,
    name: String,
    members: Vec<OwnedSourceAggregateMember>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OwnedSourceTypeGraph {
    parameter_types: Vec<OwnedSourceParameterType>,
    return_type_id: Option<u32>,
    return_carrier: Option<OwnedSourceCarrierProjection>,
    types: Vec<OwnedSourceType>,
    aggregates: Vec<OwnedSourceAggregateLayout>,
}

impl OwnedSourceTypeGraph {
    fn into_source_contract(
        self,
    ) -> Result<
        (
            Vec<r2ssa::SourceLogicalValue>,
            Option<r2ssa::SourceLogicalValue>,
            r2ssa::SourceTypeGraph,
        ),
        BoundaryError,
    > {
        let parameter_logical_values = self
            .parameter_types
            .into_iter()
            .map(|value| {
                let kind = match value.carrier.kind {
                    OwnedSourceCarrierKind::Full => r2ssa::SourceCarrierKind::Full,
                    OwnedSourceCarrierKind::LowBits => r2ssa::SourceCarrierKind::LowBits,
                };
                r2ssa::SourceLogicalValue::new(
                    value.type_id,
                    r2ssa::SourceCarrierProjection::new(
                        kind,
                        value.carrier.offset_bits,
                        value.carrier.size_bits,
                    ),
                )
            })
            .collect::<Vec<_>>();
        let return_logical_value = match (self.return_type_id, self.return_carrier) {
            (None, None) => None,
            (Some(type_id), Some(carrier)) => {
                let kind = match carrier.kind {
                    OwnedSourceCarrierKind::Full => r2ssa::SourceCarrierKind::Full,
                    OwnedSourceCarrierKind::LowBits => r2ssa::SourceCarrierKind::LowBits,
                };
                Some(r2ssa::SourceLogicalValue::new(
                    type_id,
                    r2ssa::SourceCarrierProjection::new(
                        kind,
                        carrier.offset_bits,
                        carrier.size_bits,
                    ),
                ))
            }
            _ => {
                return Err(BoundaryError::invalid(
                    "validated source return type and carrier are inconsistent",
                ));
            }
        };
        let source_types = self
            .types
            .into_iter()
            .map(|source_type| {
                let kind = match source_type.kind {
                    OwnedSourceTypeKind::SignedInteger => r2ssa::SourceTypeKind::SignedInteger,
                    OwnedSourceTypeKind::UnsignedInteger => r2ssa::SourceTypeKind::UnsignedInteger,
                    OwnedSourceTypeKind::Pointer => r2ssa::SourceTypeKind::Pointer {
                        target_type_id: source_type.target_type_id.ok_or_else(|| {
                            BoundaryError::invalid("validated source pointer is missing its target")
                        })?,
                    },
                    OwnedSourceTypeKind::Struct => r2ssa::SourceTypeKind::Struct {
                        aggregate_id: source_type.aggregate_id.ok_or_else(|| {
                            BoundaryError::invalid(
                                "validated source struct is missing its aggregate",
                            )
                        })?,
                    },
                };
                Ok(r2ssa::SourceType::new(
                    source_type.id,
                    kind,
                    source_type.size_bits,
                    source_type.align_bits,
                ))
            })
            .collect::<Result<Vec<_>, BoundaryError>>()?;
        let source_aggregates = self.aggregates.into_iter().map(|aggregate| {
            r2ssa::SourceAggregateLayout::new(
                aggregate.id,
                aggregate.type_id,
                aggregate.size_bits,
                aggregate.align_bits,
                aggregate.name,
                aggregate.members.into_iter().map(|member| {
                    r2ssa::SourceAggregateMember::new(
                        member.member_id,
                        member.type_id,
                        member.offset_bits,
                        member.size_bits,
                        member.name,
                    )
                }),
            )
        });
        let type_graph = r2ssa::SourceTypeGraph::new(source_types, source_aggregates)
            .map_err(|error| BoundaryError::invalid(error.to_string()))?;
        Ok((parameter_logical_values, return_logical_value, type_graph))
    }
}

fn source_align_up(value: u64, alignment: u64) -> Option<u64> {
    if alignment == 0 || !alignment.is_power_of_two() {
        return None;
    }
    let mask = alignment - 1;
    value.checked_add(mask).map(|aligned| aligned & !mask)
}

fn source_type_kind(kind: u32) -> Result<OwnedSourceTypeKind, BoundaryError> {
    match kind {
        R2SLEIGH_SOURCE_TYPE_SIGNED_INTEGER_V2 => Ok(OwnedSourceTypeKind::SignedInteger),
        R2SLEIGH_SOURCE_TYPE_UNSIGNED_INTEGER_V2 => Ok(OwnedSourceTypeKind::UnsignedInteger),
        R2SLEIGH_SOURCE_TYPE_POINTER_V2 => Ok(OwnedSourceTypeKind::Pointer),
        R2SLEIGH_SOURCE_TYPE_STRUCT_V2 => Ok(OwnedSourceTypeKind::Struct),
        _ => Err(BoundaryError::invalid(
            "source type graph has unknown type kind",
        )),
    }
}

fn source_carrier_projection(
    carrier: R2SleighSourceCarrierProjectionV2,
    logical_type: &OwnedSourceType,
    storage_size: u32,
    label: &str,
) -> Result<OwnedSourceCarrierProjection, BoundaryError> {
    let carrier_bits = u64::from(storage_size)
        .checked_mul(8)
        .ok_or_else(|| BoundaryError::invalid(format!("{label} carrier width overflows")))?;
    if carrier.offset_bits != 0
        || carrier.size_bits != logical_type.size_bits
        || logical_type.size_bits == 0
        || logical_type.size_bits > carrier_bits
    {
        return Err(BoundaryError::invalid(format!(
            "{label} carrier projection does not match its logical type"
        )));
    }
    let kind = match carrier.kind {
        R2SLEIGH_SOURCE_CARRIER_FULL_V2 if logical_type.size_bits == carrier_bits => {
            OwnedSourceCarrierKind::Full
        }
        R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2
            if logical_type.size_bits < carrier_bits
                && matches!(
                    logical_type.kind,
                    OwnedSourceTypeKind::SignedInteger | OwnedSourceTypeKind::UnsignedInteger
                ) =>
        {
            OwnedSourceCarrierKind::LowBits
        }
        _ => {
            return Err(BoundaryError::invalid(format!(
                "{label} has an invalid full/low-bits carrier contract"
            )));
        }
    };
    Ok(OwnedSourceCarrierProjection {
        kind,
        offset_bits: carrier.offset_bits,
        size_bits: carrier.size_bits,
    })
}

unsafe fn validate_source_type_graph(
    source: &R2SleighSourceFunctionInterfaceV2,
    parameters: &[R2SleighSourceParameterV2],
    budget: &mut ValidationBudget,
) -> Result<Option<OwnedSourceTypeGraph>, BoundaryError> {
    if source.exact_types_complete > 1 {
        return Err(BoundaryError::invalid(
            "source type graph completeness flag is not boolean",
        ));
    }
    if source.exact_types_complete == 0 {
        if source.num_parameter_types != 0
            || !source.parameter_types.is_null()
            || source.return_type_id != R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2
            || source.return_carrier.kind != R2SLEIGH_SOURCE_CARRIER_INVALID_V2
            || source.return_carrier.offset_bits != 0
            || source.return_carrier.size_bits != 0
            || source.num_types != 0
            || !source.types.is_null()
            || source.num_aggregates != 0
            || !source.aggregates.is_null()
        {
            return Err(BoundaryError::invalid(
                "incomplete source type graph contains non-authoritative payload",
            ));
        }
        return Ok(None);
    }
    let parameter_types = unsafe {
        checked_slice(
            source.parameter_types,
            source.num_parameter_types,
            MAX_ABI_ARGUMENTS,
            "source_interface.parameter_types",
        )?
    };
    let types = unsafe {
        checked_slice(
            source.types,
            source.num_types,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "source_interface.types",
        )?
    };
    let aggregates = unsafe {
        checked_slice(
            source.aggregates,
            source.num_aggregates,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "source_interface.aggregates",
        )?
    };
    if parameter_types.len() != parameters.len() || types.is_empty() {
        return Err(BoundaryError::invalid(
            "source type graph does not cover the exact function signature",
        ));
    }
    budget.charge_context_items(
        parameter_types
            .len()
            .checked_add(types.len())
            .and_then(|count| count.checked_add(aggregates.len()))
            .ok_or_else(|| BoundaryError::limit("source type graph item count overflow"))?,
        "source type graph items",
    )?;

    let mut owned_types = Vec::with_capacity(types.len());
    for (position, source_type) in types.iter().enumerate() {
        if usize::try_from(source_type.id) != Ok(position)
            || source_type.size_bits == 0
            || source_type.size_bits % 8 != 0
            || source_type.align_bits == 0
            || source_type.align_bits % 8 != 0
            || !source_type.align_bits.is_power_of_two()
            || source_type.align_bits > source_type.size_bits
        {
            return Err(BoundaryError::invalid(format!(
                "source_interface.types[{position}] has invalid identity, size, or alignment"
            )));
        }
        let kind = source_type_kind(source_type.kind)?;
        let (target_type_id, aggregate_id) = match kind {
            OwnedSourceTypeKind::SignedInteger | OwnedSourceTypeKind::UnsignedInteger => {
                if source_type.target_type_id != R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2
                    || source_type.aggregate_id != R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2
                    || !matches!(source_type.size_bits, 8 | 16 | 32 | 64)
                    || source_type.align_bits != source_type.size_bits
                {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.types[{position}] is not a closed scalar"
                    )));
                }
                (None, None)
            }
            OwnedSourceTypeKind::Pointer => {
                if source_type.target_type_id >= source.num_types as u32
                    || source_type.aggregate_id != R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2
                    || source_type.size_bits != 64
                    || source_type.align_bits != 64
                {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.types[{position}] has an invalid pointer target"
                    )));
                }
                (Some(source_type.target_type_id), None)
            }
            OwnedSourceTypeKind::Struct => {
                if source_type.target_type_id != R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2
                    || source_type.aggregate_id >= source.num_aggregates as u32
                {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.types[{position}] has an invalid aggregate reference"
                    )));
                }
                (None, Some(source_type.aggregate_id))
            }
        };
        owned_types.push(OwnedSourceType {
            id: source_type.id,
            kind,
            size_bits: source_type.size_bits,
            align_bits: source_type.align_bits,
            target_type_id,
            aggregate_id,
        });
    }
    for (position, source_type) in owned_types.iter().enumerate() {
        if let Some(target_id) = source_type.target_type_id
            && !matches!(
                owned_types[target_id as usize].kind,
                OwnedSourceTypeKind::SignedInteger
                    | OwnedSourceTypeKind::UnsignedInteger
                    | OwnedSourceTypeKind::Struct
            )
        {
            return Err(BoundaryError::invalid(format!(
                "source_interface.types[{position}] pointer target is not a supported scalar or struct"
            )));
        }
    }

    let mut owned_aggregates = Vec::with_capacity(aggregates.len());
    for (position, aggregate) in aggregates.iter().enumerate() {
        if usize::try_from(aggregate.id) != Ok(position)
            || aggregate.type_id >= source.num_types as u32
            || aggregate.complete != 1
            || aggregate.c_layout_compatible != 1
        {
            return Err(BoundaryError::invalid(format!(
                "source_interface.aggregates[{position}] is incomplete or has invalid identity"
            )));
        }
        let aggregate_type = &owned_types[aggregate.type_id as usize];
        if aggregate_type.kind != OwnedSourceTypeKind::Struct
            || aggregate_type.aggregate_id != Some(aggregate.id)
            || aggregate.size_bits != aggregate_type.size_bits
            || aggregate.align_bits != aggregate_type.align_bits
        {
            return Err(BoundaryError::invalid(format!(
                "source_interface.aggregates[{position}] disagrees with its struct node"
            )));
        }
        let name = unsafe {
            string_view(
                aggregate.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("source_interface.aggregates[{position}].name"),
                budget,
            )?
        }
        .to_owned();
        let members = unsafe {
            checked_slice(
                aggregate.members,
                aggregate.num_members,
                R2SLEIGH_MAX_NESTED_ITEMS_V2,
                &format!("source_interface.aggregates[{position}].members"),
            )?
        };
        if members.is_empty() {
            return Err(BoundaryError::invalid(format!(
                "source_interface.aggregates[{position}] is an incomplete declaration"
            )));
        }
        budget.charge_nested_items(members.len(), "source aggregate members")?;
        let mut cursor = 0u64;
        let mut maximum_alignment = 0u64;
        let mut owned_members = Vec::with_capacity(members.len());
        for (member_position, member) in members.iter().enumerate() {
            if usize::try_from(member.member_id) != Ok(member_position)
                || member.type_id >= source.num_types as u32
                || member.count != 0
                || member.offset_bits % 8 != 0
                || member.size_bits % 8 != 0
            {
                return Err(BoundaryError::invalid(format!(
                    "source_interface.aggregates[{position}].members[{member_position}] has invalid identity or unsupported shape"
                )));
            }
            let member_type = &owned_types[member.type_id as usize];
            if !matches!(
                member_type.kind,
                OwnedSourceTypeKind::SignedInteger | OwnedSourceTypeKind::UnsignedInteger
            ) || member.size_bits != member_type.size_bits
                || source_align_up(cursor, member_type.align_bits) != Some(member.offset_bits)
            {
                return Err(BoundaryError::invalid(format!(
                    "source_interface.aggregates[{position}].members[{member_position}] violates the sealed natural layout"
                )));
            }
            cursor = member
                .offset_bits
                .checked_add(member.size_bits)
                .ok_or_else(|| BoundaryError::invalid("source aggregate member range overflows"))?;
            maximum_alignment = maximum_alignment.max(member_type.align_bits);
            let member_name = unsafe {
                string_view(
                    member.name,
                    R2SLEIGH_MAX_STRING_BYTES_V2,
                    &format!(
                        "source_interface.aggregates[{position}].members[{member_position}].name"
                    ),
                    budget,
                )?
            }
            .to_owned();
            owned_members.push(OwnedSourceAggregateMember {
                member_id: member.member_id,
                type_id: member.type_id,
                offset_bits: member.offset_bits,
                size_bits: member.size_bits,
                name: member_name,
            });
        }
        if maximum_alignment != aggregate.align_bits
            || source_align_up(cursor, maximum_alignment) != Some(aggregate.size_bits)
        {
            return Err(BoundaryError::invalid(format!(
                "source_interface.aggregates[{position}] size or alignment is not exact"
            )));
        }
        owned_aggregates.push(OwnedSourceAggregateLayout {
            id: aggregate.id,
            type_id: aggregate.type_id,
            size_bits: aggregate.size_bits,
            align_bits: aggregate.align_bits,
            name,
            members: owned_members,
        });
    }
    if owned_types
        .iter()
        .filter(|source_type| source_type.kind == OwnedSourceTypeKind::Struct)
        .count()
        != owned_aggregates.len()
    {
        return Err(BoundaryError::invalid(
            "source type graph has missing or duplicate aggregate layouts",
        ));
    }

    let mut owned_parameter_types = Vec::with_capacity(parameter_types.len());
    let mut reachable = BTreeSet::new();
    for (position, parameter_type) in parameter_types.iter().enumerate() {
        if usize::try_from(parameter_type.index) != Ok(position)
            || parameter_type.type_id >= source.num_types as u32
        {
            return Err(BoundaryError::invalid(format!(
                "source_interface.parameter_types[{position}] has invalid identity"
            )));
        }
        let logical_type = &owned_types[parameter_type.type_id as usize];
        let carrier = source_carrier_projection(
            parameter_type.carrier,
            logical_type,
            parameters[position].storage.size,
            &format!("source_interface.parameter_types[{position}]"),
        )?;
        reachable.insert(parameter_type.type_id);
        owned_parameter_types.push(OwnedSourceParameterType {
            index: parameter_type.index,
            type_id: parameter_type.type_id,
            carrier,
        });
    }
    let (return_type_id, return_carrier) = match source.return_kind {
        R2SLEIGH_SOURCE_RETURN_VOID_V2 => {
            if source.return_type_id != R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2
                || source.return_carrier.kind != R2SLEIGH_SOURCE_CARRIER_INVALID_V2
                || source.return_carrier.offset_bits != 0
                || source.return_carrier.size_bits != 0
            {
                return Err(BoundaryError::invalid(
                    "void source return has a logical type or carrier",
                ));
            }
            (None, None)
        }
        R2SLEIGH_SOURCE_RETURN_REGISTER_V2 => {
            if source.return_type_id >= source.num_types as u32 {
                return Err(BoundaryError::invalid(
                    "source return logical type id is invalid",
                ));
            }
            let logical_type = &owned_types[source.return_type_id as usize];
            let carrier = source_carrier_projection(
                source.return_carrier,
                logical_type,
                source.return_storage.size,
                "source_interface.return_carrier",
            )?;
            reachable.insert(source.return_type_id);
            (Some(source.return_type_id), Some(carrier))
        }
        _ => {
            return Err(BoundaryError::invalid(
                "source interface has unknown return kind",
            ));
        }
    };
    let mut worklist: Vec<u32> = reachable.iter().copied().collect();
    while let Some(type_id) = worklist.pop() {
        let source_type = &owned_types[type_id as usize];
        if let Some(target_id) = source_type.target_type_id
            && reachable.insert(target_id)
        {
            worklist.push(target_id);
        }
        if let Some(aggregate_id) = source_type.aggregate_id {
            for member in &owned_aggregates[aggregate_id as usize].members {
                if reachable.insert(member.type_id) {
                    worklist.push(member.type_id);
                }
            }
        }
    }
    if reachable.len() != owned_types.len() {
        return Err(BoundaryError::invalid(
            "source type graph contains unreachable nodes",
        ));
    }
    Ok(Some(OwnedSourceTypeGraph {
        parameter_types: owned_parameter_types,
        return_type_id,
        return_carrier,
        types: owned_types,
        aggregates: owned_aggregates,
    }))
}

unsafe fn source_snapshot(
    source: *const R2SleighSourceFunctionInterfaceV2,
    ctx: *const R2ILContext,
    blocks: *const *const R2ILBlock,
    num_blocks: usize,
    function_addr: u64,
    context_hash: u64,
    budget: &mut ValidationBudget,
) -> Result<Option<Arc<r2engine::EngineSourceSnapshot>>, BoundaryError> {
    if source.is_null() {
        return Ok(None);
    }
    valid_object_ptr(source, "source_interface")?;
    let source = unsafe { &*source };
    if source.schema_version != R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2
        || source.struct_size < u32_size::<R2SleighSourceFunctionInterfaceV2>()
    {
        return Err(BoundaryError::abi(
            "source interface schema or struct size mismatch",
        ));
    }
    if !matches!(source.call_sites_complete, 0 | 1) {
        return Err(BoundaryError::invalid(
            "source callsite completeness flag is not boolean",
        ));
    }
    if source.complete != 1
        || source.stack_resources_complete != 1
        || source.stack_slot_roles_complete != 1
        || source.variadic != 0
        || source.noreturn != 0
    {
        return Err(BoundaryError::invalid(
            "source interface is not a complete supported exact interface",
        ));
    }
    if source.revision_identity == 0
        || context_hash == 0
        || source.revision_identity != context_hash
    {
        return Err(BoundaryError::invalid(
            "source interface revision does not match the immutable function context",
        ));
    }
    if source.function_addr != function_addr {
        return Err(BoundaryError::invalid(
            "source interface function identity does not match the request",
        ));
    }
    let calling_convention = unsafe {
        string_view(
            source.calling_convention,
            R2SLEIGH_MAX_STRING_BYTES_V2,
            "source_interface.calling_convention",
            budget,
        )?
    };
    if calling_convention.trim().is_empty() {
        return Err(BoundaryError::invalid(
            "source interface calling convention is empty",
        ));
    }
    let parameters = unsafe {
        checked_slice(
            source.parameters,
            source.num_parameters,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "source_interface.parameters",
        )?
    };
    let stack_slots = unsafe {
        checked_slice(
            source.stack_slots,
            source.num_stack_slots,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "source_interface.stack_slots",
        )?
    };
    let call_sites = unsafe {
        checked_slice(
            source.call_sites,
            source.num_call_sites,
            R2SLEIGH_MAX_CONTEXT_ITEMS_V2,
            "source_interface.call_sites",
        )?
    };
    let exact_type_graph = unsafe { validate_source_type_graph(source, parameters, budget)? };
    if !call_sites.is_empty() && source.call_sites_complete == 0 {
        return Err(BoundaryError::invalid(
            "source callsite transport is partial and cannot carry authority",
        ));
    }
    budget.charge_context_items(
        parameters
            .len()
            .checked_add(stack_slots.len())
            .and_then(|count| count.checked_add(call_sites.len()))
            .and_then(|count| count.checked_add(2))
            .ok_or_else(|| BoundaryError::limit("source interface item count overflow"))?,
        "source interface items",
    )?;
    let ctx_view = super::context::require_ctx_view(ctx)
        .ok_or_else(|| BoundaryError::invalid("source interface context is unavailable"))?;
    let arch = ctx_view
        .arch
        .ok_or_else(|| BoundaryError::invalid("source interface ArchSpec is unavailable"))?;
    let return_address_storage = validate_full_width_register_storage_against_arch(
        arch,
        source.return_address_storage,
        "source_interface.return_address_storage",
    )?;
    let stack_pointer_storage = validate_full_width_register_storage_against_arch(
        arch,
        source.stack_pointer_storage,
        "source_interface.stack_pointer_storage",
    )?;
    if canonical_storage_ranges_overlap(return_address_storage, stack_pointer_storage) {
        return Err(BoundaryError::invalid(
            "source_interface.stack_pointer_storage overlaps return-address storage",
        ));
    }
    let mut parameter_specs = Vec::with_capacity(parameters.len());
    for (position, parameter) in parameters.iter().enumerate() {
        if usize::try_from(parameter.index) != Ok(position) {
            return Err(BoundaryError::invalid(
                "source parameters are not in exact index order",
            ));
        }
        let name = unsafe {
            string_view(
                parameter.storage.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("source_interface.parameters[{position}].name"),
                budget,
            )?
        };
        let storage = validate_register_against_arch(
            arch,
            name,
            parameter.storage.offset,
            parameter.storage.size,
        )?;
        parameter_specs.push(r2ssa::SourceAbiParameterSpec::new(parameter.index, storage));
    }
    let return_storage = match source.return_kind {
        R2SLEIGH_SOURCE_RETURN_VOID_V2 => None,
        R2SLEIGH_SOURCE_RETURN_REGISTER_V2 => {
            let name = unsafe {
                string_view(
                    source.return_storage.name,
                    R2SLEIGH_MAX_STRING_BYTES_V2,
                    "source_interface.return_storage.name",
                    budget,
                )?
            };
            let storage = validate_register_against_arch(
                arch,
                name,
                source.return_storage.offset,
                source.return_storage.size,
            )?;
            Some(storage)
        }
        _ => {
            return Err(BoundaryError::invalid(
                "source interface has unknown return kind",
            ));
        }
    };
    let return_kind = match return_storage {
        Some(storage) => r2ssa::SourceFunctionReturn::Register { storage },
        None => r2ssa::SourceFunctionReturn::Void,
    };
    let mut stack_slot_specs = Vec::with_capacity(stack_slots.len());
    let mut parameter_homes = BTreeSet::new();
    for (position, slot) in stack_slots.iter().enumerate() {
        let base_name = unsafe {
            string_view(
                slot.base.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("source_interface.stack_slots[{position}].base.name"),
                budget,
            )?
        };
        let (base, canonical_storage) = validate_stack_base_against_arch(
            arch,
            slot.base_kind,
            base_name,
            slot.base.offset,
            slot.base.size,
        )?;
        match base {
            r2ssa::StackAddressBase::StackPointer => {
                if canonical_storage != stack_pointer_storage {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.stack_slots[{position}] SP base does not exactly match stack-pointer storage"
                    )));
                }
            }
            r2ssa::StackAddressBase::FramePointer => {
                if canonical_storage_ranges_overlap(stack_pointer_storage, canonical_storage) {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.stack_pointer_storage overlaps BP base storage at index {position}"
                    )));
                }
            }
        }
        if canonical_storage_ranges_overlap(return_address_storage, canonical_storage) {
            return Err(BoundaryError::invalid(format!(
                "source_interface.return_address_storage overlaps stack base storage at index {position}"
            )));
        }
        if slot.size == 0 || slot.offset.checked_add(i64::from(slot.size)).is_none() {
            return Err(BoundaryError::invalid(format!(
                "source_interface.stack_slots[{position}] has invalid range"
            )));
        }
        let home_name = unsafe {
            string_view(
                slot.home_storage.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("source_interface.stack_slots[{position}].home_storage.name"),
                budget,
            )?
        };
        let spec = match slot.role {
            R2SLEIGH_SOURCE_STACK_ROLE_LOCAL_V2 => {
                if slot.parameter_index != R2SLEIGH_SOURCE_PARAMETER_INDEX_INVALID_V2
                    || !home_name.is_empty()
                    || slot.home_storage.offset != 0
                    || slot.home_storage.size != 0
                {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.stack_slots[{position}] local carries parameter-home authority"
                    )));
                }
                r2ssa::SourceStackSlotSpec::new_local(
                    base,
                    canonical_storage,
                    slot.offset,
                    slot.size,
                )
            }
            R2SLEIGH_SOURCE_STACK_ROLE_PARAMETER_HOME_V2 => {
                let parameter_index = usize::try_from(slot.parameter_index).map_err(|_| {
                    BoundaryError::invalid(format!(
                        "source_interface.stack_slots[{position}] has invalid parameter index"
                    ))
                })?;
                if slot.home_storage.size == 0
                    || slot
                        .home_storage
                        .offset
                        .checked_add(u64::from(slot.home_storage.size))
                        .is_none()
                {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.stack_slots[{position}] has invalid parameter-home storage"
                    )));
                }
                let Some((wire_parameter, parameter_spec)) = parameters
                    .get(parameter_index)
                    .zip(parameter_specs.get(parameter_index))
                else {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.stack_slots[{position}] has invalid parameter index"
                    )));
                };
                let home_storage = validate_register_against_arch(
                    arch,
                    home_name,
                    slot.home_storage.offset,
                    slot.home_storage.size,
                )?;
                if wire_parameter.storage.offset != slot.home_storage.offset
                    || wire_parameter.storage.size != slot.home_storage.size
                    || home_storage != parameter_spec.storage()
                    || !parameter_homes.insert(slot.parameter_index)
                {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.stack_slots[{position}] does not exactly match one parameter home"
                    )));
                }
                if canonical_storage_ranges_overlap(return_address_storage, home_storage) {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.return_address_storage overlaps parameter-home storage at index {position}"
                    )));
                }
                if canonical_storage_ranges_overlap(stack_pointer_storage, home_storage) {
                    return Err(BoundaryError::invalid(format!(
                        "source_interface.stack_pointer_storage overlaps parameter-home storage at index {position}"
                    )));
                }
                r2ssa::SourceStackSlotSpec::new_parameter_home(
                    base,
                    canonical_storage,
                    slot.offset,
                    slot.size,
                    slot.parameter_index,
                    parameter_spec.storage(),
                )
            }
            _ => {
                return Err(BoundaryError::invalid(format!(
                    "source_interface.stack_slots[{position}] has unsupported role"
                )));
            }
        };
        stack_slot_specs.push(spec);
    }
    if parameter_specs.iter().any(|parameter| {
        canonical_storage_ranges_overlap(return_address_storage, parameter.storage())
    }) {
        return Err(BoundaryError::invalid(
            "source_interface.return_address_storage overlaps parameter storage",
        ));
    }
    if parameter_specs.iter().any(|parameter| {
        canonical_storage_ranges_overlap(stack_pointer_storage, parameter.storage())
    }) {
        return Err(BoundaryError::invalid(
            "source_interface.stack_pointer_storage overlaps parameter storage",
        ));
    }
    if return_storage
        .is_some_and(|storage| canonical_storage_ranges_overlap(return_address_storage, storage))
    {
        return Err(BoundaryError::invalid(
            "source_interface.return_address_storage overlaps non-void return storage",
        ));
    }
    if return_storage
        .is_some_and(|storage| canonical_storage_ranges_overlap(stack_pointer_storage, storage))
    {
        return Err(BoundaryError::invalid(
            "source_interface.stack_pointer_storage overlaps non-void return storage",
        ));
    }
    stack_slot_specs.sort_by_key(|slot| (slot.base(), slot.offset(), slot.size_bytes()));
    let lifted_blocks = unsafe {
        checked_slice(
            blocks,
            num_blocks,
            R2SLEIGH_MAX_AGGREGATE_BLOCKS_V2,
            "source_interface.lifted_blocks",
        )?
    };
    let mut call_site_specs = Vec::with_capacity(call_sites.len());
    let mut raw_locations = BTreeSet::new();
    for (position, call) in call_sites.iter().enumerate() {
        if call.schema_version != R2SLEIGH_SOURCE_CALL_SITE_SCHEMA_V2
            || call.struct_size < u32_size::<R2SleighSourceCallSiteInterfaceV2>()
        {
            return Err(BoundaryError::abi(format!(
                "source_interface.call_sites[{position}] schema or struct size mismatch"
            )));
        }
        if call.revision_identity == 0
            || call.revision_identity != source.revision_identity
            || call.caller_function_addr != function_addr
        {
            return Err(BoundaryError::invalid(format!(
                "source_interface.call_sites[{position}] has stale or cross-function identity"
            )));
        }
        if !matches!(call.complete, 0 | 1)
            || !matches!(call.variadic, 0 | 1)
            || !matches!(call.noreturn, 0 | 1)
        {
            return Err(BoundaryError::invalid(format!(
                "source_interface.call_sites[{position}] contains a non-boolean flag"
            )));
        }
        if !raw_locations.insert((call.raw_instruction_addr, call.raw_target_addr)) {
            return Err(BoundaryError::invalid(
                "source callsite raw identity is duplicated or ambiguous",
            ));
        }
        let target = source_storage(call.target)?;
        validate_lifted_call_site(lifted_blocks, call, target, position)?;
        let callconv = unsafe {
            string_view(
                call.calling_convention,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("source_interface.call_sites[{position}].calling_convention"),
                budget,
            )?
        };
        if callconv.trim().is_empty() {
            return Err(BoundaryError::invalid(format!(
                "source_interface.call_sites[{position}] calling convention is empty"
            )));
        }
        let arguments = unsafe {
            checked_slice(
                call.arguments,
                call.num_arguments,
                MAX_ABI_ARGUMENTS,
                &format!("source_interface.call_sites[{position}].arguments"),
            )?
        };
        budget.charge_context_items(arguments.len(), "source callsite arguments")?;
        let mut argument_specs = Vec::with_capacity(arguments.len());
        for (argument_position, argument) in arguments.iter().enumerate() {
            if usize::try_from(argument.index) != Ok(argument_position) {
                return Err(BoundaryError::invalid(format!(
                    "source_interface.call_sites[{position}] arguments are not in exact order"
                )));
            }
            let name = unsafe {
                string_view(
                    argument.storage.name,
                    R2SLEIGH_MAX_STRING_BYTES_V2,
                    &format!(
                        "source_interface.call_sites[{position}].arguments[{argument_position}].name"
                    ),
                    budget,
                )?
            };
            let storage = validate_register_against_arch(
                arch,
                name,
                argument.storage.offset,
                argument.storage.size,
            )?;
            argument_specs.push(r2ssa::SourceCallArgumentSpec::new(argument.index, storage));
        }
        let result = match call.result_kind {
            R2SLEIGH_SOURCE_RETURN_VOID_V2 => r2ssa::SourceCallResult::Void,
            R2SLEIGH_SOURCE_RETURN_REGISTER_V2 => {
                let name = unsafe {
                    string_view(
                        call.result_storage.name,
                        R2SLEIGH_MAX_STRING_BYTES_V2,
                        &format!("source_interface.call_sites[{position}].result_storage.name"),
                        budget,
                    )?
                };
                let storage = validate_register_against_arch(
                    arch,
                    name,
                    call.result_storage.offset,
                    call.result_storage.size,
                )?;
                r2ssa::SourceCallResult::Register { storage }
            }
            _ => {
                return Err(BoundaryError::invalid(format!(
                    "source_interface.call_sites[{position}] has unknown result kind"
                )));
            }
        };
        let argument_storages = argument_specs
            .iter()
            .map(|argument| argument.storage())
            .collect::<Vec<_>>();
        let result_storage = match result {
            r2ssa::SourceCallResult::Void => None,
            r2ssa::SourceCallResult::Register { storage } => Some(storage),
        };
        let semantic_callconv =
            project_semantic_calling_convention(callconv, arch, &argument_storages, result_storage);
        let interface = r2ssa::SourceCallSiteInterface::new(
            source.revision_identity.to_le_bytes().to_vec(),
            r2ssa::SourceCallSiteIdentity::new(call.block_addr, call.op_index, target),
            call.complete != 0,
            semantic_callconv,
            argument_specs,
            call.variadic != 0,
            call.noreturn != 0,
            result,
        )
        .map_err(|error| BoundaryError::invalid(error.to_string()))?;
        call_site_specs.push(interface);
    }
    let revision = source.revision_identity.to_le_bytes().to_vec();
    let (parameter_logical_values, return_logical_value, type_graph) = exact_type_graph
        .map(OwnedSourceTypeGraph::into_source_contract)
        .transpose()?
        .map_or_else(
            || (Vec::new(), None, None),
            |(parameters, return_value, graph)| (parameters, return_value, Some(graph)),
        );
    let parameter_storages = parameter_specs
        .iter()
        .map(|parameter| parameter.storage())
        .collect::<Vec<_>>();
    let return_storage = match return_kind {
        r2ssa::SourceFunctionReturn::Void => None,
        r2ssa::SourceFunctionReturn::Register { storage } => Some(storage),
    };
    let semantic_calling_convention = project_semantic_calling_convention(
        calling_convention,
        arch,
        &parameter_storages,
        return_storage,
    );
    let function_interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
        revision.clone(),
        semantic_calling_convention,
        parameter_specs,
        return_kind,
        stack_slot_specs,
        parameter_logical_values,
        return_logical_value,
        type_graph,
    )
    .and_then(|interface| interface.with_return_address_storage(return_address_storage))
    .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer_storage))
    .map_err(|error| BoundaryError::invalid(error.to_string()))?;
    r2engine::EngineSourceSnapshot::new(revision, Some(function_interface), call_site_specs)
        .map(Arc::new)
        .map(Some)
        .map_err(|error| BoundaryError::invalid(error.to_string()))
}

fn source_storage(
    storage: R2SleighSourceStorageV2,
) -> Result<r2ssa::CanonicalStorageId, BoundaryError> {
    let space = match storage.space {
        R2SLEIGH_SOURCE_STORAGE_RAM_V2 => r2ssa::CanonicalStorageSpace::Ram,
        R2SLEIGH_SOURCE_STORAGE_REGISTER_V2 => r2ssa::CanonicalStorageSpace::Register,
        R2SLEIGH_SOURCE_STORAGE_UNIQUE_V2 => r2ssa::CanonicalStorageSpace::Unique,
        R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2 => r2ssa::CanonicalStorageSpace::Constant,
        R2SLEIGH_SOURCE_STORAGE_CUSTOM_V2 => {
            r2ssa::CanonicalStorageSpace::Custom(storage.custom_space)
        }
        _ => {
            return Err(BoundaryError::invalid(
                "source callsite target has unknown space",
            ));
        }
    };
    if storage.size == 0
        || storage
            .offset
            .checked_add(u64::from(storage.size))
            .is_none()
    {
        return Err(BoundaryError::invalid(
            "source callsite target storage has invalid range",
        ));
    }
    Ok(r2ssa::CanonicalStorageId {
        space,
        offset: storage.offset,
        size: storage.size,
    })
}

fn validate_lifted_call_site(
    blocks: &[*const R2ILBlock],
    call: &R2SleighSourceCallSiteInterfaceV2,
    target: r2ssa::CanonicalStorageId,
    position: usize,
) -> Result<(), BoundaryError> {
    if !matches!(target.space, r2ssa::CanonicalStorageSpace::Constant)
        || target.offset != call.raw_target_addr
    {
        return Err(BoundaryError::invalid(format!(
            "source_interface.call_sites[{position}] is not an exact direct target"
        )));
    }
    let mut raw_matches = 0usize;
    let mut exact_match = false;
    for block in blocks {
        valid_object_ptr(*block, "source_interface.lifted_block")?;
        let block = unsafe { &**block };
        for (op_index, op) in block.ops.iter().enumerate() {
            if !matches!(op, r2il::R2ILOp::Call { .. })
                || block
                    .op_metadata(op_index)
                    .and_then(|metadata| metadata.instruction_addr)
                    != Some(call.raw_instruction_addr)
            {
                continue;
            }
            raw_matches = raw_matches
                .checked_add(1)
                .ok_or_else(|| BoundaryError::limit("source callsite match count overflow"))?;
            if block.addr == call.block_addr
                && op_index == call.op_index
                && matches!(op, r2il::R2ILOp::Call { target: lifted }
                    if r2ssa::CanonicalStorageId::from_varnode(lifted) == target)
            {
                exact_match = true;
            }
        }
    }
    if raw_matches != 1 || !exact_match {
        return Err(BoundaryError::invalid(format!(
            "source_interface.call_sites[{position}] has missing or ambiguous lifted identity"
        )));
    }
    Ok(())
}

#[derive(Debug)]
struct ExecutedRequest {
    output: super::EngineV2Output,
    request_kind: u32,
    ffi_conversion_elapsed_us: u64,
}

fn elapsed_us(started: Instant) -> u64 {
    started.elapsed().as_micros().min(u128::from(u64::MAX)) as u64
}

fn validate_opaque_snapshot_envelope(
    payload: &R2SleighEngineRequestPayloadV2,
) -> Result<(), BoundaryError> {
    let context = payload.function_context;
    let scope = payload.interproc_scope;
    if !payload.ctx.is_null()
        || !payload.blocks.is_null()
        || payload.num_blocks != 0
        || payload.function_addr != 0
        || !payload.function_name.is_null()
        || context.schema_version != 0
        || context.dirty_epoch != 0
        || context.context_hash != 0
        || context.type_dirty_epoch != 0
        || !context.external_context_json.is_null()
        || !context.signature_name.is_null()
        || !context.signature_ret_type.is_null()
        || !context.signature_callconv.is_null()
        || context.signature_noreturn != 0
        || !context.params.is_null()
        || context.num_params != 0
        || !context.vars.is_null()
        || context.num_vars != 0
        || !context.base_types.is_null()
        || context.num_base_types != 0
        || !context.callees.is_null()
        || context.num_callees != 0
        || !context.assumptions_json.is_null()
        || payload.lift_quality != R2SleighLiftQuality::default()
        || scope.schema_version != 0
        || !scope.functions.is_null()
        || scope.num_functions != 0
        || !scope.seeds.is_null()
        || scope.num_seeds != 0
        || payload.interproc_plan != R2SleighInterprocSessionPlan::default()
        || payload.analysis_depth != 0
        || !payload.source_interface.is_null()
    {
        return Err(BoundaryError::invalid(
            "opaque snapshot request contains detached or inactive authority fields",
        ));
    }
    Ok(())
}

unsafe fn capture_trusted_ssa(
    input: *const R2SleighRadareSnapshotInputV2,
    execution: &r2engine::EngineExecutionControl,
) -> Result<Arc<r2ssa::TrustedSsaArtifact>, BoundaryError> {
    let ssa_control = execution.ssa_execution_control();
    r2ssa::SsaWorkControl::poll(&ssa_control)
        .map_err(|error| BoundaryError::engine(format!("trusted ingress stopped: {error}")))?;
    valid_object_ptr(input, "engine payload radare snapshot")?;
    // The local wire declarations are compile-time size/alignment checked
    // against r2source above and preserve the exact repr(C) field order.
    let source_input = unsafe { &*input.cast::<r2source::RadareAbi138SnapshotInput>() };
    let source = unsafe { r2source::capture_radare_abi138(source_input) }.map_err(|error| {
        use r2source::RadareAbi138CaptureError as CaptureError;
        match error {
            CaptureError::InvalidInputSize
            | CaptureError::UnsupportedVersion
            | CaptureError::InvalidAccessorSize => {
                BoundaryError::abi(format!("opaque source snapshot refused: {error}"))
            }
            CaptureError::BudgetExceeded => {
                BoundaryError::limit(format!("opaque source snapshot refused: {error}"))
            }
            _ => BoundaryError::invalid(format!("opaque source snapshot refused: {error}")),
        }
    })?;
    r2ssa::SsaWorkControl::poll(&ssa_control).map_err(|error| {
        BoundaryError::engine(format!(
            "trusted ingress stopped after source capture: {error}"
        ))
    })?;
    let lifted = r2sleigh_lift::Disassembler::lift_owned_function(source)
        .map_err(|error| BoundaryError::unsupported(format!("trusted lift refused: {error}")))?;
    r2ssa::SsaWorkControl::poll(&ssa_control).map_err(|error| {
        BoundaryError::engine(format!("trusted ingress stopped after lift: {error}"))
    })?;
    let trusted =
        r2ssa::TrustedSsaArtifact::prepare_with_control(lifted, &ssa_control).map_err(|error| {
            BoundaryError::engine(format!("trusted SSA preparation failed: {error}"))
        })?;
    Ok(Arc::new(trusted))
}

unsafe fn execute_request(
    request: &R2SleighRequestV2,
    cancellation: r2engine::EngineCancellationToken,
) -> Result<ExecutedRequest, BoundaryError> {
    let ffi_started = Instant::now();
    if request.abi_version != R2SLEIGH_ABI_V2
        || request.struct_size != u32_size::<R2SleighRequestV2>()
    {
        return Err(BoundaryError::abi(
            "request ABI version or struct size mismatch",
        ));
    }
    let allowed_flags = if cfg!(test) {
        REQUEST_FLAG_TEST_PANIC
    } else {
        0
    };
    if request.flags & !allowed_flags != 0 {
        return Err(BoundaryError::unsupported("unsupported request flags"));
    }
    if cfg!(test) && request.flags & REQUEST_FLAG_TEST_PANIC != 0 {
        panic!("test-only V2 boundary panic");
    }
    if request.payload_size != size_of::<R2SleighEngineRequestPayloadV2>() {
        return Err(BoundaryError::abi("engine request payload size mismatch"));
    }
    valid_object_ptr(
        request.payload.cast::<R2SleighEngineRequestPayloadV2>(),
        "request.payload",
    )?;
    let payload = unsafe { &*request.payload.cast::<R2SleighEngineRequestPayloadV2>() };
    if payload.abi_version != R2SLEIGH_ABI_V2
        || payload.struct_size != u32_size::<R2SleighEngineRequestPayloadV2>()
    {
        return Err(BoundaryError::abi(
            "engine payload ABI version or struct size mismatch",
        ));
    }
    if !payload.radare_snapshot.is_null() {
        if !matches!(
            request.kind,
            R2SLEIGH_REQUEST_DECOMPILE_V2 | R2SLEIGH_REQUEST_TYPE_FUNCTION_V2
        ) {
            return Err(BoundaryError::unsupported("unsupported request kind"));
        }
        validate_opaque_snapshot_envelope(payload)?;
        let deadline = (payload.timeout_us != 0).then(|| {
            Instant::now()
                .checked_add(Duration::from_micros(payload.timeout_us))
                .unwrap_or_else(Instant::now)
        });
        let execution = r2engine::EngineExecutionControl::new(cancellation, deadline);
        let trusted = unsafe { capture_trusted_ssa(payload.radare_snapshot, &execution) }?;
        let ffi_conversion_elapsed_us = elapsed_us(ffi_started);
        let output = match request.kind {
            R2SLEIGH_REQUEST_DECOMPILE_V2 => {
                super::r2sleigh_engine_decompile_trusted_output(payload, trusted, execution)
                    .ok_or_else(|| BoundaryError::engine("decompile engine refused the request"))?
            }
            R2SLEIGH_REQUEST_TYPE_FUNCTION_V2 => {
                super::r2sleigh_engine_type_function_trusted_output(payload, trusted, execution)
                    .ok_or_else(|| BoundaryError::engine("type engine refused the request"))?
            }
            _ => return Err(BoundaryError::unsupported("unsupported request kind")),
        };
        return Ok(ExecutedRequest {
            output,
            request_kind: request.kind,
            ffi_conversion_elapsed_us,
        });
    }
    let root_block_handles = unsafe {
        checked_slice(
            payload.blocks,
            payload.num_blocks,
            R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
            "engine payload blocks",
        )?
    };
    let scope_function_handles = unsafe {
        checked_slice(
            payload.interproc_scope.functions,
            payload.interproc_scope.num_functions,
            R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2,
            "engine payload scope functions",
        )?
    };
    let mut scope_block_handles = Vec::with_capacity(scope_function_handles.len());
    for (index, function) in scope_function_handles.iter().enumerate() {
        scope_block_handles.push(unsafe {
            checked_slice(
                function.blocks,
                function.num_blocks,
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                &format!("engine payload scope functions[{index}] blocks"),
            )?
        });
    }

    // Keep the registry locked for the full synchronous request. This pins
    // every resolved allocation and prevents concurrent consume-on-free.
    let registry = lock_lift_registry();
    let context_key = lift_handle_key(payload.ctx, "engine payload lift context")?;
    let context_entry = registry.entry(
        context_key,
        LiftHandleKind::Context,
        "engine payload lift context",
    )?;
    let owner = context_entry.generation;
    let context = context_entry.payload as *const R2ILContext;
    let resolve_block = |handle: *const R2ILBlock, label: &str| {
        let key = lift_handle_key(handle, label)?;
        let entry = registry.entry(key, LiftHandleKind::Block, label)?;
        if entry.owner != owner {
            return Err(BoundaryError::invalid(format!(
                "{label} belongs to a different lift context"
            )));
        }
        Ok(entry.payload as *const R2ILBlock)
    };
    let mut root_blocks = Vec::with_capacity(root_block_handles.len());
    for (index, block) in root_block_handles.iter().enumerate() {
        root_blocks.push(resolve_block(
            *block,
            &format!("engine payload blocks[{index}]"),
        )?);
    }
    let mut scoped_blocks = Vec::with_capacity(scope_block_handles.len());
    for (function_index, blocks) in scope_block_handles.iter().enumerate() {
        let mut resolved = Vec::with_capacity(blocks.len());
        for (block_index, block) in blocks.iter().enumerate() {
            resolved.push(resolve_block(
                *block,
                &format!("engine payload scope functions[{function_index}] blocks[{block_index}]"),
            )?);
        }
        scoped_blocks.push(resolved);
    }
    let mut scoped_functions = Vec::with_capacity(scope_function_handles.len());
    for (index, function) in scope_function_handles.iter().enumerate() {
        scoped_functions.push(R2ILFunctionBlocks {
            entry_addr: function.entry_addr,
            name: function.name,
            blocks: scoped_blocks[index].as_ptr(),
            num_blocks: scoped_blocks[index].len(),
            provenance: function.provenance,
        });
    }
    let mut resolved_payload = *payload;
    resolved_payload.ctx = context;
    resolved_payload.blocks = root_blocks.as_ptr();
    resolved_payload.num_blocks = root_blocks.len();
    resolved_payload.interproc_scope.functions = scoped_functions.as_ptr();
    resolved_payload.interproc_scope.num_functions = scoped_functions.len();
    let payload = &resolved_payload;

    let deadline = (payload.timeout_us != 0).then(|| {
        Instant::now()
            .checked_add(Duration::from_micros(payload.timeout_us))
            .unwrap_or_else(Instant::now)
    });
    let execution = r2engine::EngineExecutionControl::new(cancellation, deadline);
    let mut budget = ValidationBudget::default();
    unsafe { validate_native_input(payload, request.kind, &mut budget)? };
    let source = unsafe {
        source_snapshot(
            payload.source_interface,
            payload.ctx,
            payload.blocks,
            payload.num_blocks,
            payload.function_addr,
            payload.function_context.context_hash,
            &mut budget,
        )?
    };
    let ffi_conversion_elapsed_us = elapsed_us(ffi_started);
    let output = match request.kind {
        R2SLEIGH_REQUEST_DECOMPILE_V2 => {
            super::r2sleigh_engine_decompile_function_output_with_source(payload, source, execution)
                .ok_or_else(|| BoundaryError::engine("decompile engine refused the request"))?
        }
        R2SLEIGH_REQUEST_TYPE_FUNCTION_V2 => {
            super::r2sleigh_engine_type_function_json_output_with_source(payload, source, execution)
                .ok_or_else(|| BoundaryError::engine("type engine refused the request"))?
        }
        _ => return Err(BoundaryError::unsupported("unsupported request kind")),
    };
    Ok(ExecutedRequest {
        output,
        request_kind: request.kind,
        ffi_conversion_elapsed_us,
    })
}

extern "C" fn session_create(
    config: *const R2SleighSessionConfigV2,
    output: *mut *mut R2SleighSessionV2,
) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        if output.is_null()
            || !(output as usize).is_multiple_of(align_of::<*mut R2SleighSessionV2>())
        {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        }
        unsafe { *output = ptr::null_mut() };
        if valid_object_ptr(config, "session config").is_err() {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        }
        let config = unsafe { &*config };
        if config.abi_version != R2SLEIGH_ABI_V2
            || config.struct_size != u32_size::<R2SleighSessionConfigV2>()
        {
            return R2SLEIGH_STATUS_ABI_MISMATCH_V2;
        }
        if config.required_capabilities & !R2SLEIGH_CAPABILITIES_V2 != 0 {
            return R2SLEIGH_STATUS_UNSUPPORTED_V2;
        }
        let session = Arc::new(R2SleighSessionV2 {
            error: Mutex::new(None),
            cancellation: Mutex::new(r2engine::EngineCancellationToken::default()),
        });
        match lock_engine_registry().insert_session(session) {
            Ok(session) => {
                unsafe { *output = session };
                R2SLEIGH_STATUS_OK_V2
            }
            Err(error) => error.status,
        }
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

extern "C" fn session_cancel(session: *const R2SleighSessionV2) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        let Ok(session) = registered_session(session) else {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        };
        let Ok(cancellation) = session.cancellation.lock() else {
            return R2SLEIGH_STATUS_ENGINE_ERROR_V2;
        };
        cancellation.cancel();
        R2SLEIGH_STATUS_OK_V2
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

extern "C" fn session_reset_cancellation(session: *const R2SleighSessionV2) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        let Ok(session) = registered_session(session) else {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        };
        let Ok(mut cancellation) = session.cancellation.lock() else {
            return R2SLEIGH_STATUS_ENGINE_ERROR_V2;
        };
        *cancellation = r2engine::EngineCancellationToken::default();
        R2SLEIGH_STATUS_OK_V2
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

extern "C" fn session_free(session: *mut R2SleighSessionV2) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        retire_session(session)
            .map(|_| R2SLEIGH_STATUS_OK_V2)
            .unwrap_or(R2SLEIGH_STATUS_INVALID_ARGUMENT_V2)
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

fn engine_phase_id(phase: r2engine::EnginePhase) -> u32 {
    match phase {
        r2engine::EnginePhase::SnapshotContext => R2SLEIGH_PHASE_SNAPSHOT_CONTEXT_V2,
        r2engine::EnginePhase::LiftNormalize => R2SLEIGH_PHASE_LIFT_NORMALIZE_V2,
        r2engine::EnginePhase::Ssa => R2SLEIGH_PHASE_SSA_V2,
        r2engine::EnginePhase::Obligations => R2SLEIGH_PHASE_OBLIGATIONS_V2,
        r2engine::EnginePhase::Symbolic => R2SLEIGH_PHASE_SYMBOLIC_V2,
        r2engine::EnginePhase::Types => R2SLEIGH_PHASE_TYPES_V2,
        r2engine::EnginePhase::Certification => R2SLEIGH_PHASE_CERTIFICATION_V2,
        r2engine::EnginePhase::Structuring => R2SLEIGH_PHASE_STRUCTURING_V2,
        r2engine::EnginePhase::Normalization => R2SLEIGH_PHASE_NORMALIZATION_V2,
        r2engine::EnginePhase::Rendering => R2SLEIGH_PHASE_RENDERING_V2,
        r2engine::EnginePhase::FfiConversion => R2SLEIGH_PHASE_FFI_CONVERSION_V2,
    }
}

fn engine_phase_status(status: r2engine::EnginePhaseStatus) -> u32 {
    match status {
        r2engine::EnginePhaseStatus::NotExecuted => R2SLEIGH_PHASE_STATUS_NOT_EXECUTED_V2,
        r2engine::EnginePhaseStatus::Executed => R2SLEIGH_PHASE_STATUS_EXECUTED_V2,
        r2engine::EnginePhaseStatus::Folded => R2SLEIGH_PHASE_STATUS_FOLDED_V2,
        r2engine::EnginePhaseStatus::Reused => R2SLEIGH_PHASE_STATUS_REUSED_V2,
        r2engine::EnginePhaseStatus::Refused => R2SLEIGH_PHASE_STATUS_REFUSED_V2,
    }
}

fn response_phase_timings(
    metrics: &r2engine::EngineMetrics,
) -> [R2SleighPhaseTimingV2; R2SLEIGH_PHASE_COUNT_V2] {
    let mut output = std::array::from_fn(|phase| R2SleighPhaseTimingV2 {
        phase: phase as u32,
        status: R2SLEIGH_PHASE_STATUS_NOT_EXECUTED_V2,
        elapsed_us: 0,
    });
    for timing in &metrics.phase_timings {
        let phase = engine_phase_id(timing.phase);
        if let Some(slot) = output.get_mut(phase as usize) {
            *slot = R2SleighPhaseTimingV2 {
                phase,
                status: engine_phase_status(timing.status),
                elapsed_us: timing.elapsed_us,
            };
        }
    }
    output
}

fn engine_plan_name(plan: r2engine::EnginePlan) -> &'static str {
    match plan {
        r2engine::EnginePlan::FastLocal => "fast_local",
        r2engine::EnginePlan::PreparedOnly => "prepared_only",
        r2engine::EnginePlan::BoundedType => "bounded_type",
        r2engine::EnginePlan::SemanticSummary => "semantic_summary",
        r2engine::EnginePlan::SemanticStructured => "semantic_structured",
        r2engine::EnginePlan::ReplayValidated => "replay_validated",
        r2engine::EnginePlan::RefuseWithEvidence => "refuse_with_evidence",
    }
}

fn engine_semantic_kernel_region_name(
    region: r2engine::EngineSemanticKernelRegion,
) -> &'static str {
    match region {
        r2engine::EngineSemanticKernelRegion::TerminalReturnBlock => "terminal_return_block",
        r2engine::EngineSemanticKernelRegion::AggregateMemberTerminalReturnFunction => {
            "aggregate_member_terminal_return_function"
        }
        r2engine::EngineSemanticKernelRegion::PlainRamMemoryTerminalReturnFunction => {
            "plain_ram_memory_terminal_return_function"
        }
        r2engine::EngineSemanticKernelRegion::DirectCallTerminalReturnFunction => {
            "direct_call_terminal_return_function"
        }
        r2engine::EngineSemanticKernelRegion::ConditionalTerminalReturnFunction => {
            "conditional_terminal_return_function"
        }
        r2engine::EngineSemanticKernelRegion::SwitchTerminalReturnFunction => {
            "switch_terminal_return_function"
        }
        r2engine::EngineSemanticKernelRegion::CarrierFreeLoopTerminalReturnFunction => {
            "carrier_free_loop_terminal_return_function"
        }
    }
}

fn engine_semantic_kernel_region_schema(region: r2engine::EngineSemanticKernelRegion) -> u32 {
    region.current_schema_version()
}

fn response_semantic_kernel_render_json(
    render: &r2engine::EngineSemanticKernelRender,
) -> Result<serde_json::Value, BoundaryError> {
    let region_name = engine_semantic_kernel_region_name(render.region);
    let expected_schema = engine_semantic_kernel_region_schema(render.region);
    if render.region_schema_version != expected_schema {
        return Err(BoundaryError::unsupported(format!(
            "unsupported semantic-kernel region schema version {} for {region_name}; expected {expected_schema}",
            render.region_schema_version,
        )));
    }
    Ok(serde_json::json!({
        "region_id": format!("{region_name}_v{}", render.region_schema_version),
        "region_schema_version": render.region_schema_version,
        "exact_obligation_closure": render.exact_obligation_closure,
    }))
}

fn response_diagnostics_json(
    diagnostics: &r2engine::EngineDiagnostics,
) -> Result<String, BoundaryError> {
    let semantic_kernel_render = diagnostics
        .semantic_kernel_render
        .as_ref()
        .map(response_semantic_kernel_render_json)
        .transpose()?;
    Ok(serde_json::json!({
        "plan": diagnostics.plan.map(engine_plan_name),
        "route_reason": diagnostics.route_reason.as_deref(),
        "warnings": &diagnostics.warnings,
        "refusal": diagnostics.refusal.as_deref(),
        "semantic_kernel_render": semantic_kernel_render,
        "proof_coverage": diagnostics
            .proof_coverage
            .as_ref()
            .map(|value| format!("{value:?}")),
        "render_permission": diagnostics
            .render_permission
            .as_ref()
            .map(|value| format!("{value:?}")),
    })
    .to_string())
}

fn response_outcome(diagnostics: &r2engine::EngineDiagnostics) -> u32 {
    if diagnostics.refusal.is_some()
        || matches!(
            diagnostics.plan,
            Some(r2engine::EnginePlan::RefuseWithEvidence)
        )
    {
        R2SLEIGH_OUTCOME_REFUSED_V2
    } else {
        R2SLEIGH_OUTCOME_COMPLETED_V2
    }
}

unsafe extern "C" fn execute(
    session: *mut R2SleighSessionV2,
    request: *const R2SleighRequestV2,
    output: *mut *mut R2SleighResponseV2,
) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        if output.is_null()
            || !(output as usize).is_multiple_of(align_of::<*mut R2SleighResponseV2>())
        {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        }
        unsafe { *output = ptr::null_mut() };
        let Ok(session) = registered_session(session) else {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        };
        let result = catch_unwind(AssertUnwindSafe(|| {
            valid_object_ptr(request, "request")?;
            clear_session_error(&session);
            let cancellation = session
                .cancellation
                .lock()
                .map_err(|_| BoundaryError::engine("session cancellation state is poisoned"))?
                .clone();
            let response = unsafe { execute_request(&*request, cancellation)? };
            let output_conversion_started = Instant::now();
            if response.output.output.len() > MAX_RESPONSE_BYTES {
                return Err(BoundaryError::limit("response exceeds byte cap"));
            }
            let bytes = CString::new(response.output.output)
                .map_err(|_| BoundaryError::engine("engine response contains an interior NUL"))?;
            let diagnostics_json = response_diagnostics_json(&response.output.diagnostics)?;
            if diagnostics_json.len() > MAX_RESPONSE_BYTES {
                return Err(BoundaryError::limit("response diagnostics exceed byte cap"));
            }
            let diagnostics = CString::new(diagnostics_json)
                .map_err(|_| BoundaryError::engine("diagnostics contain an interior NUL"))?;
            let outcome = response_outcome(&response.output.diagnostics);
            let phase_timings = response_phase_timings(&response.output.metrics);
            let mut owned_response = Box::new(R2SleighResponseV2 {
                bytes,
                diagnostics,
                phase_timings,
                request_kind: response.request_kind,
                outcome,
                ffi_conversion_elapsed_us: 0,
            });
            let ffi_conversion_elapsed_us = response
                .ffi_conversion_elapsed_us
                .saturating_add(elapsed_us(output_conversion_started));
            owned_response.ffi_conversion_elapsed_us = ffi_conversion_elapsed_us;
            owned_response.phase_timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2 as usize] =
                R2SleighPhaseTimingV2 {
                    phase: R2SLEIGH_PHASE_FFI_CONVERSION_V2,
                    status: R2SLEIGH_PHASE_STATUS_EXECUTED_V2,
                    elapsed_us: ffi_conversion_elapsed_us,
                };
            let response = lock_engine_registry().insert_response(Arc::from(owned_response))?;
            unsafe { *output = response };
            Ok(())
        }));
        match result {
            Ok(Ok(())) => R2SLEIGH_STATUS_OK_V2,
            Ok(Err(error)) => {
                set_session_error(&session, &error.message);
                error.status
            }
            Err(_) => {
                set_session_error(&session, "panic contained at r2sleigh V2 execute boundary");
                R2SLEIGH_STATUS_PANIC_V2
            }
        }
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

extern "C" fn response_bytes(
    response: *const R2SleighResponseV2,
    output: *mut R2SleighByteViewV2,
) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        if output.is_null() || !(output as usize).is_multiple_of(align_of::<R2SleighByteViewV2>()) {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        }
        unsafe { *output = R2SleighByteViewV2::default() };
        let Ok(response) = registered_response(response) else {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        };
        unsafe {
            *output = R2SleighByteViewV2 {
                data: response.bytes.as_ptr().cast(),
                len: response.bytes.as_bytes().len(),
            }
        };
        R2SLEIGH_STATUS_OK_V2
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

extern "C" fn response_info(
    response: *const R2SleighResponseV2,
    output: *mut R2SleighResponseInfoV2,
) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        if output.is_null()
            || !(output as usize).is_multiple_of(align_of::<R2SleighResponseInfoV2>())
        {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        }
        unsafe { output.write_bytes(0, 1) };
        let Ok(response) = registered_response(response) else {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        };
        unsafe {
            *output = R2SleighResponseInfoV2 {
                schema_version: R2SLEIGH_RESPONSE_INFO_SCHEMA_V2,
                struct_size: u32_size::<R2SleighResponseInfoV2>(),
                request_kind: response.request_kind,
                outcome: response.outcome,
                phase_timings: response.phase_timings.as_ptr(),
                num_phase_timings: response.phase_timings.len(),
                ffi_conversion_elapsed_us: response.ffi_conversion_elapsed_us,
                diagnostics_json: R2SleighByteViewV2 {
                    data: response.diagnostics.as_ptr().cast(),
                    len: response.diagnostics.as_bytes().len(),
                },
            }
        };
        R2SLEIGH_STATUS_OK_V2
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

extern "C" fn response_free(response: *mut R2SleighResponseV2) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        retire_response(response)
            .map(|_| R2SLEIGH_STATUS_OK_V2)
            .unwrap_or(R2SLEIGH_STATUS_INVALID_ARGUMENT_V2)
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

extern "C" fn session_error(
    session: *const R2SleighSessionV2,
    output: *mut R2SleighByteViewV2,
) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        if output.is_null() || !(output as usize).is_multiple_of(align_of::<R2SleighByteViewV2>()) {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        }
        unsafe { *output = R2SleighByteViewV2::default() };
        let Ok(session) = registered_session(session) else {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        };
        let Ok(error) = session.error.lock() else {
            return R2SLEIGH_STATUS_ENGINE_ERROR_V2;
        };
        unsafe {
            *output = error
                .as_ref()
                .map_or_else(R2SleighByteViewV2::default, |error| R2SleighByteViewV2 {
                    data: error.as_ptr().cast(),
                    len: error.as_bytes().len(),
                });
        }
        R2SLEIGH_STATUS_OK_V2
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

fn c_string_view(value: *const c_char) -> R2SleighByteViewV2 {
    if value.is_null() {
        return R2SleighByteViewV2::default();
    }
    let value = unsafe { CStr::from_ptr(value) };
    R2SleighByteViewV2 {
        data: value.as_ptr().cast(),
        len: value.to_bytes().len(),
    }
}

extern "C" fn lift_context_create(
    arch: R2SleighStringViewV2,
    output: *mut *mut R2ILContext,
) -> u32 {
    lift_boundary(|| {
        valid_output_ptr(output, "lift context output")?;
        unsafe { *output = ptr::null_mut() };
        let mut budget = ValidationBudget::default();
        let arch = unsafe {
            string_view(
                arch,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                "lift architecture",
                &mut budget,
            )?
        };
        if arch.is_empty() {
            return Err(BoundaryError::invalid("lift architecture is empty"));
        }
        let arch = CString::new(arch)
            .map_err(|_| BoundaryError::invalid("lift architecture contains NUL"))?;
        let context = super::r2il_arch_init(arch.as_ptr());
        if context.is_null() {
            return Err(BoundaryError::engine("failed to allocate lift context"));
        }
        // Trusted internal constructor result; no caller-supplied pointer is
        // converted before registry insertion.
        let context = unsafe { Box::from_raw(context) };
        let handle = lock_lift_registry().insert_context(context)?;
        unsafe { *output = handle };
        Ok(())
    })
}

extern "C" fn lift_context_free(context: *mut R2ILContext) -> u32 {
    lift_boundary_for(context, || {
        let key = lift_handle_key(context, "lift context")?;
        let mut registry = lock_lift_registry();
        let generation = registry
            .entry(key, LiftHandleKind::Context, "lift context")?
            .generation;
        if registry
            .handles
            .values()
            .any(|entry| entry.owner == generation && entry.generation != generation)
        {
            return Err(BoundaryError::engine(
                "lift context still owns live child handles",
            ));
        }
        registry.retire(key, LiftHandleKind::Context, "lift context")?;
        Ok(())
    })
}

extern "C" fn lift_context_is_loaded(context: *const R2ILContext, output: *mut u32) -> u32 {
    lift_boundary_for(context, || {
        valid_output_ptr(output, "lift loaded output")?;
        unsafe { *output = 0 };
        let key = lift_handle_key(context, "lift context")?;
        let registry = lock_lift_registry();
        let payload =
            registry.payload::<R2ILContext>(key, LiftHandleKind::Context, "lift context")?;
        unsafe { *output = u32::from(super::r2il_is_loaded(payload) != 0) };
        Ok(())
    })
}

extern "C" fn lift_context_arch_name(
    context: *const R2ILContext,
    output: *mut R2SleighByteViewV2,
) -> u32 {
    lift_boundary_for(context, || {
        valid_output_ptr(output, "lift architecture name output")?;
        unsafe { *output = R2SleighByteViewV2::default() };
        let key = lift_handle_key(context, "lift context")?;
        let registry = lock_lift_registry();
        let payload =
            registry.payload::<R2ILContext>(key, LiftHandleKind::Context, "lift context")?;
        let value = super::r2il_arch_name(payload);
        if value.is_null() {
            return Err(BoundaryError::engine(
                "lift context has no loaded architecture",
            ));
        }
        unsafe { *output = c_string_view(value) };
        Ok(())
    })
}

extern "C" fn lift_context_error(
    context: *const R2ILContext,
    output: *mut R2SleighByteViewV2,
) -> u32 {
    lift_boundary_for(context, || {
        valid_output_ptr(output, "lift error output")?;
        unsafe { *output = R2SleighByteViewV2::default() };
        let key = lift_handle_key(context, "lift context")?;
        let registry = lock_lift_registry();
        let payload =
            registry.payload::<R2ILContext>(key, LiftHandleKind::Context, "lift context")?;
        unsafe { *output = c_string_view(super::r2il_error(payload)) };
        Ok(())
    })
}

extern "C" fn lift_last_error(output: *mut R2SleighByteViewV2) -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        if valid_output_ptr(output, "lift last error output").is_err() {
            return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
        }
        unsafe { *output = R2SleighByteViewV2::default() };
        LIFT_LAST_ERROR.with(|error| {
            if let Some(error) = error.borrow().as_ref() {
                unsafe {
                    *output = R2SleighByteViewV2 {
                        data: error.as_ptr().cast(),
                        len: error.as_bytes().len(),
                    }
                };
            }
        });
        R2SLEIGH_STATUS_OK_V2
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

extern "C" fn lift_context_reg_profile(
    context: *const R2ILContext,
    output: *mut *mut R2SleighOwnedBytesV2,
) -> u32 {
    lift_boundary_for(context, || {
        valid_output_ptr(output, "register profile output")?;
        unsafe { *output = ptr::null_mut() };
        let key = lift_handle_key(context, "lift context")?;
        let mut registry = lock_lift_registry();
        let entry = registry.entry(key, LiftHandleKind::Context, "lift context")?;
        let owner = entry.generation;
        let payload = entry.payload as *const R2ILContext;
        let bytes = super::r2il_get_reg_profile(payload);
        if bytes.is_null() {
            return Err(BoundaryError::engine(
                "lift context has no register profile",
            ));
        }
        let bytes = unsafe { CString::from_raw(bytes) };
        let handle = registry.insert_owned_bytes(owner, R2SleighOwnedBytesV2 { bytes })?;
        unsafe { *output = handle };
        Ok(())
    })
}

unsafe fn lift_input_bytes<'a>(
    bytes: R2SleighByteViewV2,
    label: &str,
) -> Result<&'a [u8], BoundaryError> {
    let bytes = unsafe {
        checked_slice(
            bytes.data,
            bytes.len,
            R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2,
            label,
        )?
    };
    if bytes.is_empty() {
        return Err(BoundaryError::invalid(format!("{label} is empty")));
    }
    Ok(bytes)
}

extern "C" fn lift_instruction(
    context: *mut R2ILContext,
    bytes: R2SleighByteViewV2,
    addr: u64,
    output: *mut *mut R2ILBlock,
) -> u32 {
    lift_boundary_for(context, || {
        valid_output_ptr(output, "lifted instruction output")?;
        unsafe { *output = ptr::null_mut() };
        let key = lift_handle_key(context, "lift context")?;
        let bytes = unsafe { lift_input_bytes(bytes, "instruction bytes")? };
        let mut registry = lock_lift_registry();
        let entry = registry.entry(key, LiftHandleKind::Context, "lift context")?;
        let owner = entry.generation;
        let payload = entry.payload as *mut R2ILContext;
        let block = super::r2il_lift(payload, bytes.as_ptr(), bytes.len(), addr);
        if block.is_null() {
            return Err(BoundaryError::engine("instruction lift failed"));
        }
        // Trusted internal lift result, reclaimed before exposing its
        // registry-proved opaque handle.
        let block = unsafe { Box::from_raw(block) };
        let handle = registry.insert_block(owner, block)?;
        unsafe { *output = handle };
        Ok(())
    })
}

extern "C" fn lift_block(
    context: *mut R2ILContext,
    bytes: R2SleighByteViewV2,
    addr: u64,
    block_size: u32,
    output: *mut *mut R2ILBlock,
) -> u32 {
    lift_boundary_for(context, || {
        valid_output_ptr(output, "lifted block output")?;
        unsafe { *output = ptr::null_mut() };
        let key = lift_handle_key(context, "lift context")?;
        let bytes = unsafe { lift_input_bytes(bytes, "basic block bytes")? };
        if block_size == 0 || block_size as usize > bytes.len() {
            return Err(BoundaryError::invalid(
                "basic block size is zero or exceeds its byte view",
            ));
        }
        let mut registry = lock_lift_registry();
        let entry = registry.entry(key, LiftHandleKind::Context, "lift context")?;
        let owner = entry.generation;
        let payload = entry.payload as *mut R2ILContext;
        let block = super::r2il_lift_block(payload, bytes.as_ptr(), bytes.len(), addr, block_size);
        if block.is_null() {
            return Err(BoundaryError::engine("basic block lift failed"));
        }
        // Trusted internal lift result, reclaimed before exposing its
        // registry-proved opaque handle.
        let block = unsafe { Box::from_raw(block) };
        let handle = registry.insert_block(owner, block)?;
        unsafe { *output = handle };
        Ok(())
    })
}

extern "C" fn lift_context_set_semantic_metadata(context: *mut R2ILContext, enabled: u32) -> u32 {
    lift_boundary_for(context, || {
        let key = lift_handle_key(context, "lift context")?;
        if !matches!(enabled, 0 | 1) {
            return Err(BoundaryError::invalid(
                "semantic metadata flag is not boolean",
            ));
        }
        let mut registry = lock_lift_registry();
        let payload = registry
            .entry_mut(key, LiftHandleKind::Context, "lift context")?
            .payload as *mut R2ILContext;
        super::r2il_set_semantic_metadata_enabled(payload, enabled != 0);
        Ok(())
    })
}

extern "C" fn lift_block_free(block: *mut R2ILBlock) -> u32 {
    lift_boundary_for(block, || {
        let key = lift_handle_key(block, "lifted block")?;
        let mut registry = lock_lift_registry();
        registry.retire(key, LiftHandleKind::Block, "lifted block")?;
        Ok(())
    })
}

extern "C" fn lift_block_validate(context: *mut R2ILContext, block: *const R2ILBlock) -> u32 {
    lift_boundary_for(context, || {
        let context_key = lift_handle_key(context, "lift context")?;
        let block_key = lift_handle_key(block, "lifted block")?;
        let mut registry = lock_lift_registry();
        let context_owner = registry
            .entry_mut(context_key, LiftHandleKind::Context, "lift context")?
            .generation;
        let block_entry = registry.entry(block_key, LiftHandleKind::Block, "lifted block")?;
        if block_entry.owner != context_owner {
            return Err(BoundaryError::invalid(
                "lifted block belongs to a different lift context",
            ));
        }
        let context_payload = registry
            .entry(context_key, LiftHandleKind::Context, "lift context")?
            .payload as *mut R2ILContext;
        let block_payload = block_entry.payload as *const R2ILBlock;
        if super::r2il_block_validate(context_payload, block_payload) == 0 {
            return Err(BoundaryError::engine("lifted block validation failed"));
        }
        Ok(())
    })
}

extern "C" fn lift_block_set_switch_info(
    block: *mut R2ILBlock,
    switch_addr: u64,
    min_val: u64,
    max_val: u64,
    default_target: u64,
    has_default: u32,
    cases: *const R2SleighSwitchCaseV2,
    case_count: usize,
) -> u32 {
    lift_boundary_for(block, || {
        let key = lift_handle_key(block, "lifted block")?;
        if !matches!(has_default, 0 | 1) {
            return Err(BoundaryError::invalid("switch default flag is not boolean"));
        }
        let cases = unsafe {
            checked_slice(
                cases,
                case_count,
                R2SLEIGH_MAX_SWITCH_CASES_V2,
                "switch cases",
            )?
        };
        if cases.is_empty() {
            return Err(BoundaryError::invalid("switch cases are empty"));
        }
        let mut registry = lock_lift_registry();
        let payload = registry
            .entry_mut(key, LiftHandleKind::Block, "lifted block")?
            .payload as *mut R2ILBlock;
        if super::r2il_block_set_switch_info(
            payload,
            switch_addr,
            min_val,
            max_val,
            default_target,
            has_default as i32,
            cases.as_ptr(),
            cases.len(),
        ) == 0
        {
            return Err(BoundaryError::invalid("switch metadata was rejected"));
        }
        Ok(())
    })
}

extern "C" fn lift_block_op_count(block: *const R2ILBlock, output: *mut usize) -> u32 {
    lift_boundary_for(block, || {
        valid_output_ptr(output, "block operation count output")?;
        unsafe { *output = 0 };
        let key = lift_handle_key(block, "lifted block")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2ILBlock>(key, LiftHandleKind::Block, "lifted block")?;
        unsafe { *output = super::r2il_block_op_count(payload) };
        Ok(())
    })
}

extern "C" fn lift_block_direct_call_identity(
    block: *const R2ILBlock,
    raw_instruction_addr: u64,
    raw_target_addr: u64,
    found: *mut u32,
    output: *mut R2SleighDirectCallIdentityV2,
) -> u32 {
    lift_boundary_for(block, || {
        valid_output_ptr(found, "direct call found output")?;
        valid_output_ptr(output, "direct call identity output")?;
        unsafe {
            *found = 0;
            *output = R2SleighDirectCallIdentityV2::default();
        }
        let key = lift_handle_key(block, "lifted block")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2ILBlock>(key, LiftHandleKind::Block, "lifted block")?;
        match super::r2il_block_direct_call_identity(
            payload,
            raw_instruction_addr,
            raw_target_addr,
            output,
        ) {
            1 => unsafe { *found = 1 },
            0 => {}
            _ => return Err(BoundaryError::engine("direct call identity is ambiguous")),
        }
        Ok(())
    })
}

extern "C" fn lift_block_size(block: *const R2ILBlock, output: *mut u32) -> u32 {
    lift_boundary_for(block, || {
        valid_output_ptr(output, "block size output")?;
        unsafe { *output = 0 };
        let key = lift_handle_key(block, "lifted block")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2ILBlock>(key, LiftHandleKind::Block, "lifted block")?;
        unsafe { *output = super::r2il_block_size(payload) };
        Ok(())
    })
}

extern "C" fn lift_block_addr(block: *const R2ILBlock, output: *mut u64) -> u32 {
    lift_boundary_for(block, || {
        valid_output_ptr(output, "block address output")?;
        unsafe { *output = 0 };
        let key = lift_handle_key(block, "lifted block")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2ILBlock>(key, LiftHandleKind::Block, "lifted block")?;
        unsafe { *output = super::r2il_block_addr(payload) };
        Ok(())
    })
}

extern "C" fn lift_block_mnemonic(
    context: *const R2ILContext,
    bytes: R2SleighByteViewV2,
    addr: u64,
    output: *mut *mut R2SleighOwnedBytesV2,
) -> u32 {
    lift_boundary_for(context, || {
        valid_output_ptr(output, "block mnemonic output")?;
        unsafe { *output = ptr::null_mut() };
        let key = lift_handle_key(context, "lift context")?;
        let bytes = unsafe { lift_input_bytes(bytes, "mnemonic bytes")? };
        let mut registry = lock_lift_registry();
        let entry = registry.entry(key, LiftHandleKind::Context, "lift context")?;
        let owner = entry.generation;
        let payload = entry.payload as *const R2ILContext;
        let mnemonic = super::r2il_block_mnemonic(payload, bytes.as_ptr(), bytes.len(), addr);
        if mnemonic.is_null() {
            return Err(BoundaryError::engine("instruction disassembly failed"));
        }
        let bytes = unsafe { CString::from_raw(mnemonic) };
        let handle = registry.insert_owned_bytes(owner, R2SleighOwnedBytesV2 { bytes })?;
        unsafe { *output = handle };
        Ok(())
    })
}

extern "C" fn lift_block_type(block: *const R2ILBlock, output: *mut u32) -> u32 {
    lift_boundary_for(block, || {
        valid_output_ptr(output, "block type output")?;
        unsafe { *output = 0 };
        let key = lift_handle_key(block, "lifted block")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2ILBlock>(key, LiftHandleKind::Block, "lifted block")?;
        unsafe { *output = super::r2il_block_type(payload) };
        Ok(())
    })
}

extern "C" fn lift_block_jump(block: *const R2ILBlock, output: *mut u64) -> u32 {
    lift_boundary_for(block, || {
        valid_output_ptr(output, "block jump output")?;
        unsafe { *output = 0 };
        let key = lift_handle_key(block, "lifted block")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2ILBlock>(key, LiftHandleKind::Block, "lifted block")?;
        unsafe { *output = super::r2il_block_jump(payload) };
        Ok(())
    })
}

extern "C" fn lift_block_fail(block: *const R2ILBlock, output: *mut u64) -> u32 {
    lift_boundary_for(block, || {
        valid_output_ptr(output, "block fail output")?;
        unsafe { *output = 0 };
        let key = lift_handle_key(block, "lifted block")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2ILBlock>(key, LiftHandleKind::Block, "lifted block")?;
        unsafe { *output = super::r2il_block_fail(payload) };
        Ok(())
    })
}

extern "C" fn owned_bytes_view(
    bytes: *const R2SleighOwnedBytesV2,
    output: *mut R2SleighByteViewV2,
) -> u32 {
    lift_boundary_for(bytes, || {
        valid_output_ptr(output, "owned bytes view output")?;
        unsafe { *output = R2SleighByteViewV2::default() };
        let key = lift_handle_key(bytes, "owned bytes")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2SleighOwnedBytesV2>(
            key,
            LiftHandleKind::OwnedBytes,
            "owned bytes",
        )?;
        let bytes = unsafe { &*payload };
        unsafe {
            *output = R2SleighByteViewV2 {
                data: bytes.bytes.as_ptr().cast(),
                len: bytes.bytes.as_bytes().len(),
            }
        };
        Ok(())
    })
}

extern "C" fn owned_bytes_free(bytes: *mut R2SleighOwnedBytesV2) -> u32 {
    lift_boundary_for(bytes, || {
        let key = lift_handle_key(bytes, "owned bytes")?;
        let mut registry = lock_lift_registry();
        registry.retire(key, LiftHandleKind::OwnedBytes, "owned bytes")?;
        Ok(())
    })
}

extern "C" fn analysis_render(
    request: *const R2SleighAnalysisRenderRequestV2,
    output: *mut *mut R2SleighOwnedBytesV2,
) -> u32 {
    lift_boundary(|| {
        valid_output_ptr(output, "analysis render output")?;
        unsafe { *output = ptr::null_mut() };
        valid_object_ptr(request, "analysis render request")?;
        let request = unsafe { &*request };
        let mut budget = ValidationBudget::default();
        let argument = unsafe {
            string_view(
                request.argument,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                "analysis render argument",
                &mut budget,
            )?
        };
        let argument = CString::new(argument)
            .map_err(|_| BoundaryError::invalid("analysis render argument contains NUL"))?;

        if request.kind == R2SLEIGH_ANALYSIS_ENGINE_CACHE_STATS_V2 {
            if !request.context.is_null() || request.num_blocks != 0 {
                return Err(BoundaryError::invalid(
                    "cache-stats render does not accept lift handles",
                ));
            }
            let raw = super::types::r2sleigh_engine_cache_stats_json();
            if raw.is_null() {
                return Err(BoundaryError::engine("cache-stats render failed"));
            }
            let bytes = unsafe { CString::from_raw(raw) };
            let handle =
                lock_lift_registry().insert_owned_bytes(0, R2SleighOwnedBytesV2 { bytes })?;
            unsafe { *output = handle };
            return Ok(());
        }

        let block_handles = unsafe {
            checked_slice(
                request.blocks,
                request.num_blocks,
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                "analysis render blocks",
            )?
        };
        if block_handles.is_empty() {
            return Err(BoundaryError::invalid("analysis render blocks are empty"));
        }
        let context_key = lift_handle_key(request.context, "analysis render context")?;
        let mut registry = lock_lift_registry();
        let context_entry = registry.entry(
            context_key,
            LiftHandleKind::Context,
            "analysis render context",
        )?;
        let owner = context_entry.generation;
        let context = context_entry.payload as *const R2ILContext;
        let mut blocks = Vec::with_capacity(block_handles.len());
        for (index, handle) in block_handles.iter().enumerate() {
            let key = lift_handle_key(*handle, &format!("analysis render blocks[{index}]"))?;
            let entry = registry.entry(
                key,
                LiftHandleKind::Block,
                &format!("analysis render blocks[{index}]"),
            )?;
            if entry.owner != owner {
                return Err(BoundaryError::invalid(format!(
                    "analysis render blocks[{index}] belongs to a different lift context"
                )));
            }
            blocks.push(entry.payload as *const R2ILBlock);
        }
        let block = blocks[0];
        let raw: *mut c_char = match request.kind {
            R2SLEIGH_ANALYSIS_BLOCK_ESIL_V2 if blocks.len() == 1 => {
                super::r2il_block_to_esil(context, block)
            }
            R2SLEIGH_ANALYSIS_BLOCK_OP_JSON_V2 if blocks.len() == 1 => {
                super::r2il_block_op_json_named(context, block, request.op_index)
            }
            R2SLEIGH_ANALYSIS_BLOCK_REGS_READ_V2 if blocks.len() == 1 => {
                super::r2il_block_regs_read(context, block)
            }
            R2SLEIGH_ANALYSIS_BLOCK_REGS_WRITE_V2 if blocks.len() == 1 => {
                super::r2il_block_regs_write(context, block)
            }
            R2SLEIGH_ANALYSIS_BLOCK_MEMORY_V2 if blocks.len() == 1 => {
                super::r2il_block_mem_access(context, block)
            }
            R2SLEIGH_ANALYSIS_BLOCK_VARNODES_V2 if blocks.len() == 1 => {
                super::r2il_block_varnodes(context, block)
            }
            R2SLEIGH_ANALYSIS_BLOCK_SSA_V2 if blocks.len() == 1 => {
                super::analysis::ssa::r2il_block_to_ssa_json(context, block)
            }
            R2SLEIGH_ANALYSIS_BLOCK_DEFUSE_V2 if blocks.len() == 1 => {
                super::analysis::ssa::r2il_block_defuse_json(context, block)
            }
            R2SLEIGH_ANALYSIS_FUNCTION_SSA_V2 => {
                super::analysis::ssa::r2ssa_function_json(context, blocks.as_ptr(), blocks.len())
            }
            R2SLEIGH_ANALYSIS_FUNCTION_SSA_OPT_V2 => super::analysis::ssa::r2ssa_function_opt_json(
                context,
                blocks.as_ptr(),
                blocks.len(),
            ),
            R2SLEIGH_ANALYSIS_FUNCTION_DEFUSE_V2 => {
                super::analysis::ssa::r2ssa_defuse_function_json(
                    context,
                    blocks.as_ptr(),
                    blocks.len(),
                )
            }
            R2SLEIGH_ANALYSIS_FUNCTION_DOMTREE_V2 => {
                super::analysis::ssa::r2ssa_domtree_json(context, blocks.as_ptr(), blocks.len())
            }
            R2SLEIGH_ANALYSIS_FUNCTION_SLICE_V2 => super::analysis::ssa::r2ssa_backward_slice_json(
                context,
                blocks.as_ptr(),
                blocks.len(),
                argument.as_ptr(),
            ),
            R2SLEIGH_ANALYSIS_FUNCTION_TAINT_V2 => super::analysis::taint::r2taint_function_json(
                context,
                blocks.as_ptr(),
                blocks.len(),
            ),
            R2SLEIGH_ANALYSIS_FUNCTION_CFG_ASCII_V2 => {
                super::analysis::cfg::r2cfg_function_ascii(context, blocks.as_ptr(), blocks.len())
            }
            R2SLEIGH_ANALYSIS_FUNCTION_CFG_JSON_V2 => {
                super::analysis::cfg::r2cfg_function_json(context, blocks.as_ptr(), blocks.len())
            }
            kind if matches!(
                kind,
                R2SLEIGH_ANALYSIS_BLOCK_ESIL_V2
                    | R2SLEIGH_ANALYSIS_BLOCK_OP_JSON_V2
                    | R2SLEIGH_ANALYSIS_BLOCK_REGS_READ_V2
                    | R2SLEIGH_ANALYSIS_BLOCK_REGS_WRITE_V2
                    | R2SLEIGH_ANALYSIS_BLOCK_MEMORY_V2
                    | R2SLEIGH_ANALYSIS_BLOCK_VARNODES_V2
                    | R2SLEIGH_ANALYSIS_BLOCK_SSA_V2
                    | R2SLEIGH_ANALYSIS_BLOCK_DEFUSE_V2
            ) =>
            {
                return Err(BoundaryError::invalid(
                    "block render requires exactly one block",
                ));
            }
            _ => return Err(BoundaryError::unsupported("unknown analysis render kind")),
        };
        if raw.is_null() {
            return Err(BoundaryError::engine("analysis render failed"));
        }
        let bytes = unsafe { CString::from_raw(raw) };
        let handle = registry.insert_owned_bytes(owner, R2SleighOwnedBytesV2 { bytes })?;
        unsafe { *output = handle };
        Ok(())
    })
}

unsafe fn scope_request_snapshot(
    request: &R2SleighScopeRenderRequestV2,
) -> Result<super::analysis::sym::SymScopeRequestSnapshot, BoundaryError> {
    let merge_states = match request.merge_states {
        0 => false,
        1 => true,
        _ => {
            return Err(BoundaryError::invalid(
                "scope render merge_states is not boolean",
            ));
        }
    };
    if request.symbols.is_null() != (request.num_symbols == 0) {
        return Err(BoundaryError::invalid(
            "scope render symbols pointer/count are not canonical",
        ));
    }
    let symbols = unsafe {
        checked_slice(
            request.symbols,
            request.num_symbols,
            R2SLEIGH_MAX_SCOPE_SYMBOLS_V2,
            "scope render symbols",
        )?
    };
    let mut budget = ValidationBudget::default();
    let mut copied = Vec::with_capacity(symbols.len());
    for (index, symbol) in symbols.iter().enumerate() {
        let label = format!("scope render symbols[{index}]");
        if symbol.abi_version != R2SLEIGH_ABI_V2
            || symbol.struct_size != u32_size::<R2SleighScopeSymbolV2>()
            || symbol.schema_version != R2SLEIGH_SCOPE_SYMBOL_SCHEMA_V2
        {
            return Err(BoundaryError::abi(format!(
                "{label} has an incompatible envelope"
            )));
        }
        let linkage = match symbol.linkage {
            R2SLEIGH_INTERPROC_LINKAGE_UNKNOWN_V2 => r2ssa::FunctionSemanticLinkage::Unknown,
            R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2 => r2ssa::FunctionSemanticLinkage::Internal,
            R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2 => r2ssa::FunctionSemanticLinkage::Imported,
            _ => {
                return Err(BoundaryError::invalid(format!(
                    "{label}.linkage is invalid"
                )));
            }
        };
        let name = unsafe {
            string_view(
                symbol.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("{label}.name"),
                &mut budget,
            )?
        };
        if name.is_empty() {
            return Err(BoundaryError::invalid(format!("{label}.name is empty")));
        }
        if name.as_bytes().contains(&0) {
            return Err(BoundaryError::invalid(format!("{label}.name contains NUL")));
        }
        copied.push(r2sym::FunctionSymbol {
            addr: symbol.addr,
            name: name.to_string(),
            linkage,
        });
    }
    let symbols = r2sym::FunctionSymbolSnapshot::try_from_symbols(copied).map_err(|err| {
        BoundaryError::invalid(format!("scope render symbol snapshot is invalid: {err:?}"))
    })?;
    Ok(super::analysis::sym::SymScopeRequestSnapshot::new(
        symbols,
        merge_states,
    ))
}

extern "C" fn scope_render(
    request: *const R2SleighScopeRenderRequestV2,
    output: *mut *mut R2SleighOwnedBytesV2,
) -> u32 {
    lift_boundary(|| {
        valid_output_ptr(output, "scope render output")?;
        unsafe { *output = ptr::null_mut() };
        valid_object_ptr(request, "scope render request")?;
        let request = unsafe { &*request };
        let functions = unsafe {
            checked_slice(
                request.functions,
                request.num_functions,
                R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2,
                "scope render functions",
            )?
        };
        if functions.is_empty() {
            return Err(BoundaryError::invalid("scope render functions are empty"));
        }
        let mut budget = ValidationBudget::default();
        let argument = unsafe {
            string_view(
                request.argument,
                R2SLEIGH_MAX_JSON_BYTES_V2,
                "scope render argument",
                &mut budget,
            )?
        };
        let external_context = unsafe {
            string_view(
                request.external_context,
                R2SLEIGH_MAX_JSON_BYTES_V2,
                "scope render external context",
                &mut budget,
            )?
        };
        let argument = CString::new(argument)
            .map_err(|_| BoundaryError::invalid("scope render argument contains NUL"))?;
        let external_context = CString::new(external_context)
            .map_err(|_| BoundaryError::invalid("scope render external context contains NUL"))?;
        let request_snapshot = unsafe { scope_request_snapshot(request)? };
        let argument_ptr = (!request.argument.data.is_null()).then_some(argument.as_ptr());
        let external_ptr =
            (!request.external_context.data.is_null()).then_some(external_context.as_ptr());

        let context_key = lift_handle_key(request.context, "scope render context")?;
        let mut registry = lock_lift_registry();
        let context_entry =
            registry.entry(context_key, LiftHandleKind::Context, "scope render context")?;
        let owner = context_entry.generation;
        let context = context_entry.payload as *const R2ILContext;
        let mut scoped_blocks = Vec::with_capacity(functions.len());
        for (function_index, function) in functions.iter().enumerate() {
            let handles = unsafe {
                checked_slice(
                    function.blocks,
                    function.num_blocks,
                    R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                    &format!("scope render functions[{function_index}] blocks"),
                )?
            };
            let mut resolved = Vec::with_capacity(handles.len());
            for (block_index, handle) in handles.iter().enumerate() {
                let label =
                    format!("scope render functions[{function_index}] blocks[{block_index}]");
                let key = lift_handle_key(*handle, &label)?;
                let entry = registry.entry(key, LiftHandleKind::Block, &label)?;
                if entry.owner != owner {
                    return Err(BoundaryError::invalid(format!(
                        "{label} belongs to a different lift context"
                    )));
                }
                resolved.push(entry.payload as *const R2ILBlock);
            }
            scoped_blocks.push(resolved);
        }
        let mut resolved_functions = Vec::with_capacity(functions.len());
        for (index, function) in functions.iter().enumerate() {
            resolved_functions.push(R2ILFunctionBlocks {
                entry_addr: function.entry_addr,
                name: function.name,
                blocks: scoped_blocks[index].as_ptr(),
                num_blocks: scoped_blocks[index].len(),
                provenance: function.provenance,
            });
        }
        let functions_ptr = resolved_functions.as_ptr();
        let functions_len = resolved_functions.len();
        let external_ptr = external_ptr.unwrap_or(ptr::null());
        let raw = match request.kind {
            R2SLEIGH_SCOPE_FUNCTION_V2 => super::analysis::sym::r2sym_function_scope(
                context,
                functions_ptr,
                functions_len,
                request.entry_addr,
                external_ptr,
                &request_snapshot,
            ),
            R2SLEIGH_SCOPE_PATHS_V2 => super::analysis::sym::r2sym_paths_scope(
                context,
                functions_ptr,
                functions_len,
                request.entry_addr,
                external_ptr,
                &request_snapshot,
            ),
            R2SLEIGH_SCOPE_EXPLORE_V2 => super::analysis::sym::r2sym_explore_to_scope(
                context,
                functions_ptr,
                functions_len,
                request.entry_addr,
                request.target_addr,
                external_ptr,
                &request_snapshot,
            ),
            R2SLEIGH_SCOPE_SOLVE_V2 => super::analysis::sym::r2sym_solve_to_scope(
                context,
                functions_ptr,
                functions_len,
                request.entry_addr,
                request.target_addr,
                external_ptr,
                &request_snapshot,
            ),
            R2SLEIGH_SCOPE_EXPLORE_REPLAY_V2 => {
                super::analysis::sym::r2sym_explore_to_replay_scope(
                    context,
                    functions_ptr,
                    functions_len,
                    request.entry_addr,
                    request.target_addr,
                    request.replay_seed.cast(),
                    external_ptr,
                    &request_snapshot,
                )
            }
            R2SLEIGH_SCOPE_SOLVE_REPLAY_V2 => super::analysis::sym::r2sym_solve_to_replay_scope(
                context,
                functions_ptr,
                functions_len,
                request.entry_addr,
                request.target_addr,
                request.replay_seed.cast(),
                external_ptr,
                &request_snapshot,
            ),
            R2SLEIGH_SCOPE_RUN_SPEC_V2 => super::analysis::sym::r2sym_run_spec_json_scope(
                context,
                functions_ptr,
                functions_len,
                request.entry_addr,
                argument_ptr.unwrap_or(ptr::null()),
                external_ptr,
                &request_snapshot,
            ),
            _ => return Err(BoundaryError::unsupported("unknown scope render kind")),
        };
        if raw.is_null() {
            return Err(BoundaryError::engine("scope render failed"));
        }
        let bytes = unsafe { CString::from_raw(raw) };
        let handle = registry.insert_owned_bytes(owner, R2SleighOwnedBytesV2 { bytes })?;
        unsafe { *output = handle };
        Ok(())
    })
}

extern "C" fn analysis_query(
    request: *const R2SleighAnalysisQueryRequestV2,
    output: *mut *mut R2SleighAnalysisResultV2,
) -> u32 {
    lift_boundary(|| {
        valid_output_ptr(output, "analysis query output")?;
        unsafe { *output = ptr::null_mut() };
        valid_object_ptr(request, "analysis query request")?;
        let request = unsafe { &*request };
        let block_handles = unsafe {
            checked_slice(
                request.blocks,
                request.num_blocks,
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                "analysis query blocks",
            )?
        };
        if block_handles.is_empty() {
            return Err(BoundaryError::invalid("analysis query blocks are empty"));
        }
        let input_values = unsafe {
            checked_slice(
                request.input_values,
                request.num_input_values,
                R2SLEIGH_MAX_NESTED_ITEMS_V2,
                "analysis query input values",
            )?
        };
        let mut budget = ValidationBudget::default();
        let function_name = unsafe {
            string_view(
                request.function_name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                "analysis query function name",
                &mut budget,
            )?
        };
        let function_name = CString::new(function_name)
            .map_err(|_| BoundaryError::invalid("analysis query function name contains NUL"))?;
        let context_key = lift_handle_key(request.context, "analysis query context")?;
        let mut registry = lock_lift_registry();
        let context_entry = registry.entry(
            context_key,
            LiftHandleKind::Context,
            "analysis query context",
        )?;
        let owner = context_entry.generation;
        let context = context_entry.payload as *const R2ILContext;
        let mut blocks = Vec::with_capacity(block_handles.len());
        for (index, handle) in block_handles.iter().enumerate() {
            let label = format!("analysis query blocks[{index}]");
            let key = lift_handle_key(*handle, &label)?;
            let entry = registry.entry(key, LiftHandleKind::Block, &label)?;
            if entry.owner != owner {
                return Err(BoundaryError::invalid(format!(
                    "{label} belongs to a different lift context"
                )));
            }
            blocks.push(entry.payload as *const R2ILBlock);
        }
        let raw: *mut c_void = match request.kind {
            R2SLEIGH_QUERY_BLOCK_VALUES_V2 if blocks.len() == 1 => {
                super::r2il_block_values_typed(context, blocks[0]).cast()
            }
            R2SLEIGH_QUERY_BLOCK_VALUES_V2 => {
                return Err(BoundaryError::invalid(
                    "block-values query requires exactly one block",
                ));
            }
            R2SLEIGH_QUERY_TAINT_SUMMARY_V2 => {
                super::analysis::taint::r2taint_function_summary_typed(
                    context,
                    blocks.as_ptr(),
                    blocks.len(),
                )
                .cast()
            }
            R2SLEIGH_QUERY_ANNOTATIONS_V2 => super::r2sleigh_analyze_fcn_annotations_typed(
                context,
                blocks.as_ptr(),
                blocks.len(),
                request.function_addr,
            )
            .cast(),
            R2SLEIGH_QUERY_DIRECT_TARGETS_V2 => super::r2sleigh_get_direct_call_targets_typed(
                context,
                blocks.as_ptr(),
                blocks.len(),
                request.function_addr,
                function_name.as_ptr(),
            )
            .cast(),
            R2SLEIGH_QUERY_SYMBOLIC_TARGETS_V2 => super::r2sleigh_get_symbolic_scope_targets_typed(
                context,
                blocks.as_ptr(),
                blocks.len(),
                request.function_addr,
                function_name.as_ptr(),
                input_values.as_ptr(),
                input_values.len(),
            )
            .cast(),
            R2SLEIGH_QUERY_RUNTIME_SOURCES_V2 => {
                super::r2sleigh_get_runtime_materialized_sources_typed(
                    context,
                    blocks.as_ptr(),
                    blocks.len(),
                    request.function_addr,
                    function_name.as_ptr(),
                    input_values.as_ptr(),
                    input_values.len(),
                )
                .cast()
            }
            R2SLEIGH_QUERY_RECOVERED_VARS_V2 => super::types::r2sleigh_recover_vars_typed(
                context,
                blocks.as_ptr(),
                blocks.len(),
                request.function_addr,
            )
            .cast(),
            R2SLEIGH_QUERY_DATA_REFS_V2 => super::types::r2sleigh_data_refs_typed(
                context,
                blocks.as_ptr(),
                blocks.len(),
                request.function_addr,
            )
            .cast(),
            _ => return Err(BoundaryError::unsupported("unknown analysis query kind")),
        };
        if raw.is_null() {
            return Err(BoundaryError::engine("analysis query failed"));
        }
        let handle = registry.insert_analysis_result(
            owner,
            R2SleighAnalysisResultV2 {
                kind: request.kind,
                raw,
            },
        )?;
        unsafe { *output = handle };
        Ok(())
    })
}

extern "C" fn analysis_result_view(
    result: *const R2SleighAnalysisResultV2,
    output: *mut R2SleighAnalysisResultViewV2,
) -> u32 {
    lift_boundary_for(result, || {
        valid_output_ptr(output, "analysis result view output")?;
        unsafe { *output = R2SleighAnalysisResultViewV2::default() };
        let key = lift_handle_key(result, "analysis result")?;
        let registry = lock_lift_registry();
        let payload = registry.payload::<R2SleighAnalysisResultV2>(
            key,
            LiftHandleKind::AnalysisResult,
            "analysis result",
        )?;
        let result = unsafe { &*payload };
        let mut view = R2SleighAnalysisResultViewV2 {
            kind: result.kind,
            ..R2SleighAnalysisResultViewV2::default()
        };
        match result.kind {
            R2SLEIGH_QUERY_BLOCK_VALUES_V2 => {
                view.primary =
                    super::r2il_block_values_memory(result.raw.cast(), &mut view.primary_count)
                        .cast();
                view.secondary = super::r2il_block_values_immediates(
                    result.raw.cast(),
                    &mut view.secondary_count,
                )
                .cast();
                view.tertiary =
                    super::r2il_block_values_reg_reads(result.raw.cast(), &mut view.tertiary_count)
                        .cast();
                view.quaternary = super::r2il_block_values_reg_writes(
                    result.raw.cast(),
                    &mut view.quaternary_count,
                )
                .cast();
            }
            R2SLEIGH_QUERY_TAINT_SUMMARY_V2 => {
                view.primary = super::analysis::taint::r2taint_function_summary_sources(
                    result.raw.cast(),
                    &mut view.primary_count,
                )
                .cast();
                view.secondary = super::analysis::taint::r2taint_function_summary_sink_hits(
                    result.raw.cast(),
                    &mut view.secondary_count,
                )
                .cast();
            }
            R2SLEIGH_QUERY_ANNOTATIONS_V2 => {
                view.primary =
                    super::r2sleigh_annotations_items(result.raw.cast(), &mut view.primary_count)
                        .cast();
            }
            R2SLEIGH_QUERY_DIRECT_TARGETS_V2 | R2SLEIGH_QUERY_SYMBOLIC_TARGETS_V2 => {
                view.primary =
                    super::r2sleigh_u64_array_items(result.raw.cast(), &mut view.primary_count)
                        .cast();
            }
            R2SLEIGH_QUERY_RUNTIME_SOURCES_V2 => {
                view.primary = super::r2sleigh_runtime_sources_items(
                    result.raw.cast(),
                    &mut view.primary_count,
                )
                .cast();
            }
            R2SLEIGH_QUERY_RECOVERED_VARS_V2 => {
                view.primary = super::types::r2sleigh_recovered_vars_items(
                    result.raw.cast(),
                    &mut view.primary_count,
                )
                .cast();
            }
            R2SLEIGH_QUERY_DATA_REFS_V2 => {
                view.primary = super::types::r2sleigh_data_refs_items(
                    result.raw.cast(),
                    &mut view.primary_count,
                )
                .cast();
            }
            _ => return Err(BoundaryError::engine("analysis result has an unknown kind")),
        }
        unsafe { *output = view };
        Ok(())
    })
}

extern "C" fn analysis_result_free(result: *mut R2SleighAnalysisResultV2) -> u32 {
    lift_boundary_for(result, || {
        let key = lift_handle_key(result, "analysis result")?;
        lock_lift_registry().retire(key, LiftHandleKind::AnalysisResult, "analysis result")
    })
}

extern "C" fn engine_cache_reset() -> u32 {
    catch_unwind(AssertUnwindSafe(|| {
        super::types::r2sleigh_engine_cache_stats_reset();
        R2SLEIGH_STATUS_OK_V2
    }))
    .unwrap_or(R2SLEIGH_STATUS_PANIC_V2)
}

fn planner_mode(mode: r2engine::EngineAnalysisMode) -> u32 {
    match mode {
        r2engine::EngineAnalysisMode::Fast => R2SLEIGH_MODE_FAST_V2,
        r2engine::EngineAnalysisMode::Balanced => R2SLEIGH_MODE_BALANCED_V2,
        r2engine::EngineAnalysisMode::Full => R2SLEIGH_MODE_FULL_V2,
    }
}

fn planner_type_writeback_mode(mode: r2engine::EngineTypeWritebackMode) -> u32 {
    match mode {
        r2engine::EngineTypeWritebackMode::Off => R2SLEIGH_TYPE_WRITEBACK_OFF_V2,
        r2engine::EngineTypeWritebackMode::Balanced => R2SLEIGH_TYPE_WRITEBACK_BALANCED_V2,
        r2engine::EngineTypeWritebackMode::Aggressive => R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE_V2,
    }
}

fn planner_usize_to_i32(value: usize) -> i32 {
    value.min(i32::MAX as usize) as i32
}

fn planner_bool(value: bool) -> i32 {
    if value { 1 } else { 0 }
}

fn planner_analysis_policy(policy: r2engine::EngineAnalysisPolicy) -> R2SleighAnalysisPolicyV2 {
    R2SleighAnalysisPolicyV2 {
        mode: planner_mode(policy.mode),
        type_writeback_mode: planner_type_writeback_mode(policy.type_writeback_mode),
        type_interproc_max_iters: planner_usize_to_i32(policy.type_interproc_max_iters),
        type_max_blocks: planner_usize_to_i32(policy.type_max_blocks),
        type_global_max_links: planner_usize_to_i32(policy.type_global_max_links),
        type_max_decls: planner_usize_to_i32(policy.type_max_decls),
        type_max_mutations: planner_usize_to_i32(policy.type_max_mutations),
    }
}

fn planner_post_analysis(plan: r2engine::EnginePostAnalysisPlan) -> R2SleighPostAnalysisPlanV2 {
    let policy = planner_analysis_policy(plan.policy);
    R2SleighPostAnalysisPlanV2 {
        mode: policy.mode,
        type_writeback_mode: policy.type_writeback_mode,
        type_interproc_max_iters: policy.type_interproc_max_iters,
        type_max_blocks: policy.type_max_blocks,
        type_global_max_links: policy.type_global_max_links,
        type_max_decls: policy.type_max_decls,
        type_max_mutations: policy.type_max_mutations,
        function_count: plan.function_count,
        post_budget_us: plan.post_budget_us,
        xref_enabled: planner_bool(plan.xref_enabled),
        taint_enabled: planner_bool(plan.taint_enabled),
        sigwrite_enabled: planner_bool(plan.signature_writeback_enabled),
        type_writeback_enabled: planner_bool(plan.type_writeback_enabled),
        semantic_comments_enabled: planner_bool(plan.semantic_comments_enabled),
        sigverify_enabled: planner_bool(plan.signature_verify_enabled),
        balanced_focus_only: planner_bool(plan.balanced_focus_only),
        taint_focus_only: planner_bool(plan.taint_focus_only),
        sigwrite_focus_only: planner_bool(plan.signature_writeback_focus_only),
        type_writeback_focus_only: planner_bool(plan.type_writeback_focus_only),
    }
}

fn planner_auto_callback_kind(raw: u32) -> Option<r2engine::EngineAutoCallbackKind> {
    match raw {
        R2SLEIGH_AUTO_CALLBACK_ANALYZE_FUNCTION_V2 => {
            Some(r2engine::EngineAutoCallbackKind::AnalyzeFunction)
        }
        R2SLEIGH_AUTO_CALLBACK_RECOVER_VARS_V2 => {
            Some(r2engine::EngineAutoCallbackKind::RecoverVars)
        }
        R2SLEIGH_AUTO_CALLBACK_DATA_REFS_V2 => Some(r2engine::EngineAutoCallbackKind::DataRefs),
        R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_TAINT_V2 => {
            Some(r2engine::EngineAutoCallbackKind::PostAnalysisTaint)
        }
        R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_XREF_V2 => {
            Some(r2engine::EngineAutoCallbackKind::PostAnalysisXref)
        }
        _ => None,
    }
}

fn planner_auto_callback_kind_value(kind: r2engine::EngineAutoCallbackKind) -> u32 {
    match kind {
        r2engine::EngineAutoCallbackKind::AnalyzeFunction => {
            R2SLEIGH_AUTO_CALLBACK_ANALYZE_FUNCTION_V2
        }
        r2engine::EngineAutoCallbackKind::RecoverVars => R2SLEIGH_AUTO_CALLBACK_RECOVER_VARS_V2,
        r2engine::EngineAutoCallbackKind::DataRefs => R2SLEIGH_AUTO_CALLBACK_DATA_REFS_V2,
        r2engine::EngineAutoCallbackKind::PostAnalysisTaint => {
            R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_TAINT_V2
        }
        r2engine::EngineAutoCallbackKind::PostAnalysisXref => {
            R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_XREF_V2
        }
    }
}

fn planner_auto_callback_reason(reason: r2engine::EngineAutoCallbackRefusalReason) -> u32 {
    match reason {
        r2engine::EngineAutoCallbackRefusalReason::Allowed => {
            R2SLEIGH_AUTO_CALLBACK_REASON_ALLOWED_V2
        }
        r2engine::EngineAutoCallbackRefusalReason::ModeNotFull => {
            R2SLEIGH_AUTO_CALLBACK_REASON_MODE_NOT_FULL_V2
        }
        r2engine::EngineAutoCallbackRefusalReason::TooManyBlocks => {
            R2SLEIGH_AUTO_CALLBACK_REASON_TOO_MANY_BLOCKS_V2
        }
        r2engine::EngineAutoCallbackRefusalReason::TooLarge => {
            R2SLEIGH_AUTO_CALLBACK_REASON_TOO_LARGE_V2
        }
        r2engine::EngineAutoCallbackRefusalReason::TooCostly => {
            R2SLEIGH_AUTO_CALLBACK_REASON_TOO_COSTLY_V2
        }
    }
}

fn planner_auto_callback(plan: r2engine::EngineAutoCallbackPlan) -> R2SleighAutoCallbackPlanV2 {
    R2SleighAutoCallbackPlanV2 {
        allowed: planner_bool(plan.allowed),
        kind: planner_auto_callback_kind_value(plan.kind),
        reason: planner_auto_callback_reason(plan.reason),
    }
}

fn planner_interproc_purpose(raw: u32) -> Option<r2engine::EngineInterprocSessionPurpose> {
    match raw {
        R2SLEIGH_INTERPROC_SESSION_TYPE_ANALYSIS_V2 => {
            Some(r2engine::EngineInterprocSessionPurpose::TypeAnalysis)
        }
        R2SLEIGH_INTERPROC_SESSION_DECOMPILE_V2 => {
            Some(r2engine::EngineInterprocSessionPurpose::Decompile)
        }
        _ => None,
    }
}

fn planner_interproc_plan(
    plan: r2engine::EngineInterprocSessionPlan,
) -> R2SleighInterprocSessionPlan {
    R2SleighInterprocSessionPlan {
        include_type_interproc_scope: planner_bool(plan.include_type_interproc_scope),
        include_root_symbolic_scope: planner_bool(plan.include_root_symbolic_scope),
        interproc_iter: plan.interproc_iter,
        interproc_max_iters: plan.interproc_max_iters,
        interproc_converged: planner_bool(plan.interproc_converged),
    }
}

fn planner_input_bool(raw: i32) -> Option<bool> {
    match raw {
        0 => Some(false),
        1 => Some(true),
        _ => None,
    }
}

fn planner_interproc_input(
    plan: R2SleighInterprocSessionPlan,
) -> Option<r2engine::EngineInterprocSessionPlan> {
    Some(r2engine::EngineInterprocSessionPlan {
        include_type_interproc_scope: planner_input_bool(plan.include_type_interproc_scope)?,
        include_root_symbolic_scope: planner_input_bool(plan.include_root_symbolic_scope)?,
        interproc_iter: plan.interproc_iter,
        interproc_max_iters: plan.interproc_max_iters,
        interproc_converged: planner_input_bool(plan.interproc_converged)?,
    })
}

fn planner_symbolic_scope_reason(reason: r2engine::EngineSymbolicScopeFunctionReason) -> u32 {
    match reason {
        r2engine::EngineSymbolicScopeFunctionReason::Allowed => {
            R2SLEIGH_SYMBOLIC_SCOPE_REASON_ALLOWED_V2
        }
        r2engine::EngineSymbolicScopeFunctionReason::ScopeFull => {
            R2SLEIGH_SYMBOLIC_SCOPE_REASON_SCOPE_FULL_V2
        }
        r2engine::EngineSymbolicScopeFunctionReason::InterprocDisabled => {
            R2SLEIGH_SYMBOLIC_SCOPE_REASON_INTERPROC_DISABLED_V2
        }
        r2engine::EngineSymbolicScopeFunctionReason::TargetTerminal => {
            R2SLEIGH_SYMBOLIC_SCOPE_REASON_TARGET_TERMINAL_V2
        }
    }
}

fn planner_symbolic_scope(
    plan: r2engine::EngineSymbolicScopeFunctionPlan,
) -> R2SleighSymbolicScopeFunctionPlanV2 {
    R2SleighSymbolicScopeFunctionPlanV2 {
        append_function: planner_bool(plan.append_function),
        expand_targets: planner_bool(plan.expand_targets),
        reason: planner_symbolic_scope_reason(plan.reason),
    }
}

fn planner_runtime_source_reason(reason: r2engine::EngineRuntimeMaterializedSourceReason) -> u32 {
    match reason {
        r2engine::EngineRuntimeMaterializedSourceReason::Allowed => {
            R2SLEIGH_RUNTIME_SOURCE_REASON_ALLOWED_V2
        }
        r2engine::EngineRuntimeMaterializedSourceReason::ScopeFull => {
            R2SLEIGH_RUNTIME_SOURCE_REASON_SCOPE_FULL_V2
        }
        r2engine::EngineRuntimeMaterializedSourceReason::EmptySource => {
            R2SLEIGH_RUNTIME_SOURCE_REASON_EMPTY_SOURCE_V2
        }
    }
}

fn planner_runtime_source(
    plan: r2engine::EngineRuntimeMaterializedSourcePlan,
) -> R2SleighRuntimeMaterializedSourcePlanV2 {
    R2SleighRuntimeMaterializedSourcePlanV2 {
        append_source: planner_bool(plan.append_source),
        capped_size: plan.capped_size,
        slot_bytes: plan.slot_bytes,
        reason: planner_runtime_source_reason(plan.reason),
    }
}

fn planner_interproc_input_is_zero(plan: R2SleighInterprocSessionPlan) -> bool {
    plan == R2SleighInterprocSessionPlan::default()
}

fn planner_query_inactive_fields_are_zero(request: &R2SleighPlannerQueryRequestV2) -> bool {
    let no_depth = request.depth == 0;
    let no_purpose = request.purpose == 0;
    let no_callback = request.callback_kind == 0;
    let no_scope_flags = request.root_function == 0 && request.target_hint_function == 0;
    let no_scope_count = request.current_scope_count == 0;
    let no_function_count = request.function_count == 0;
    let no_metrics = request.basic_block_count == 0 && request.cost == 0;
    let no_linear_size = request.linear_size == 0;
    let no_source = request.addr == 0 && request.size == 0;
    let no_interproc = planner_interproc_input_is_zero(request.interproc);
    let no_targets = request.targets.is_null() && request.num_targets == 0;

    match request.kind {
        R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2 => {
            no_purpose
                && no_callback
                && no_scope_flags
                && no_scope_count
                && no_function_count
                && no_metrics
                && no_linear_size
                && no_source
                && no_interproc
                && no_targets
        }
        R2SLEIGH_PLANNER_POST_ANALYSIS_V2 => {
            no_purpose
                && no_callback
                && no_scope_flags
                && no_scope_count
                && no_metrics
                && no_linear_size
                && no_source
                && no_interproc
                && no_targets
        }
        R2SLEIGH_PLANNER_AUTO_CALLBACK_V2 => {
            no_purpose
                && no_scope_flags
                && no_scope_count
                && no_function_count
                && no_source
                && no_interproc
                && no_targets
        }
        R2SLEIGH_PLANNER_INTERPROC_SESSION_V2 => {
            no_callback
                && no_scope_flags
                && no_scope_count
                && no_function_count
                && no_linear_size
                && no_source
                && no_interproc
                && no_targets
        }
        R2SLEIGH_PLANNER_SYMBOLIC_SCOPE_V2 => {
            no_depth
                && no_purpose
                && no_callback
                && no_function_count
                && no_metrics
                && no_linear_size
                && no_source
                && no_targets
        }
        R2SLEIGH_PLANNER_RUNTIME_SOURCE_V2 => {
            no_depth
                && no_purpose
                && no_callback
                && no_scope_flags
                && no_function_count
                && no_metrics
                && no_linear_size
                && no_interproc
                && no_targets
        }
        R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2 => {
            no_depth
                && no_purpose
                && no_callback
                && no_scope_flags
                && no_scope_count
                && no_function_count
                && no_metrics
                && no_linear_size
                && no_source
                && no_interproc
        }
        _ => false,
    }
}

unsafe fn planner_target_inputs(
    request: &R2SleighPlannerQueryRequestV2,
) -> Result<Vec<r2engine::EngineInterprocTargetInput>, BoundaryError> {
    let inputs = unsafe {
        checked_slice(
            request.targets,
            request.num_targets,
            R2SLEIGH_MAX_PLANNER_TARGETS_V2,
            "planner targets",
        )?
    };
    let mut budget = ValidationBudget::default();
    let mut copied = Vec::with_capacity(inputs.len());
    for (index, input) in inputs.iter().enumerate() {
        let label = format!("planner targets[{index}]");
        if input.abi_version != R2SLEIGH_ABI_V2
            || input.struct_size != u32_size::<R2SleighPlannerTargetInputV2>()
            || input.schema_version != R2SLEIGH_PLANNER_TARGET_INPUT_SCHEMA_V2
        {
            return Err(BoundaryError::abi(format!(
                "{label} has an incompatible envelope"
            )));
        }
        let linkage = match input.linkage {
            R2SLEIGH_INTERPROC_LINKAGE_UNKNOWN_V2 => r2ssa::FunctionSemanticLinkage::Unknown,
            R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2 => r2ssa::FunctionSemanticLinkage::Internal,
            R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2 => r2ssa::FunctionSemanticLinkage::Imported,
            _ => {
                return Err(BoundaryError::invalid(format!(
                    "{label}.linkage is invalid"
                )));
            }
        };
        let has_resolved_target = match input.has_resolved_target {
            0 => false,
            1 => true,
            _ => {
                return Err(BoundaryError::invalid(format!(
                    "{label}.has_resolved_target is not boolean"
                )));
            }
        };
        let target_materialized = match input.target_materialized {
            0 => false,
            1 => true,
            _ => {
                return Err(BoundaryError::invalid(format!(
                    "{label}.target_materialized is not boolean"
                )));
            }
        };
        let has_target_metrics = match input.has_target_metrics {
            0 => false,
            1 => true,
            _ => {
                return Err(BoundaryError::invalid(format!(
                    "{label}.has_target_metrics is not boolean"
                )));
            }
        };
        if !has_resolved_target && input.resolved_target != 0 {
            return Err(BoundaryError::invalid(format!(
                "{label}.resolved_target must be zero when absent"
            )));
        }
        if target_materialized && !has_resolved_target {
            return Err(BoundaryError::invalid(format!(
                "{label} cannot be materialized without a resolved target"
            )));
        }
        if !has_target_metrics && (input.target_basic_block_count != 0 || input.target_cost != 0) {
            return Err(BoundaryError::invalid(format!(
                "{label} metrics must be zero when absent"
            )));
        }
        if has_target_metrics && !target_materialized {
            return Err(BoundaryError::invalid(format!(
                "{label} cannot have metrics without a materialized target"
            )));
        }
        let name = unsafe {
            string_view(
                input.name,
                R2SLEIGH_MAX_STRING_BYTES_V2,
                &format!("{label}.name"),
                &mut budget,
            )?
        }
        .trim();
        copied.push(r2engine::EngineInterprocTargetInput {
            direct_target: input.direct_target,
            name: (!name.is_empty()).then(|| name.to_string()),
            linkage,
            semantic_summary: None,
            resolved_target: has_resolved_target.then_some(input.resolved_target),
            target_materialized,
            target_metrics: has_target_metrics.then_some(r2engine::EngineInterprocTargetMetrics {
                basic_block_count: input.target_basic_block_count,
                cost: input.target_cost,
            }),
        });
    }
    Ok(copied)
}

fn planner_query_impl(
    request: &R2SleighPlannerQueryRequestV2,
) -> Result<R2SleighPlannerQueryResponseV2, BoundaryError> {
    if !planner_query_inactive_fields_are_zero(request) {
        return Err(BoundaryError::invalid(
            "planner query contains nonzero inactive fields",
        ));
    }
    let mut response = R2SleighPlannerQueryResponseV2 {
        abi_version: R2SLEIGH_ABI_V2,
        struct_size: u32_size::<R2SleighPlannerQueryResponseV2>(),
        schema_version: R2SLEIGH_PLANNER_QUERY_SCHEMA_V2,
        kind: request.kind,
        ..R2SleighPlannerQueryResponseV2::default()
    };
    match request.kind {
        R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2 => {
            response.analysis_policy =
                planner_analysis_policy(r2engine::analysis_policy_for_radare2_depth(request.depth));
        }
        R2SLEIGH_PLANNER_POST_ANALYSIS_V2 => {
            response.post_analysis =
                planner_post_analysis(r2engine::post_analysis_plan_for_radare2_depth(
                    request.depth,
                    request.function_count,
                ));
        }
        R2SLEIGH_PLANNER_AUTO_CALLBACK_V2 => {
            let kind = planner_auto_callback_kind(request.callback_kind)
                .ok_or_else(|| BoundaryError::invalid("planner callback kind is invalid"))?;
            response.auto_callback =
                planner_auto_callback(r2engine::auto_callback_plan_for_radare2_depth(
                    request.depth,
                    kind,
                    r2engine::EngineAutoCallbackMetrics {
                        basic_block_count: u32::try_from(request.basic_block_count)
                            .unwrap_or(u32::MAX),
                        cost: request.cost,
                        linear_size: request.linear_size,
                    },
                ));
        }
        R2SLEIGH_PLANNER_INTERPROC_SESSION_V2 => {
            let purpose = planner_interproc_purpose(request.purpose)
                .ok_or_else(|| BoundaryError::invalid("planner purpose is invalid"))?;
            response.interproc_session = planner_interproc_plan(r2engine::interproc_session_plan(
                r2engine::analysis_policy_for_radare2_depth(request.depth),
                purpose,
                Some(r2engine::EngineInterprocTargetMetrics {
                    basic_block_count: u32::try_from(request.basic_block_count).unwrap_or(u32::MAX),
                    cost: request.cost,
                }),
            ));
        }
        R2SLEIGH_PLANNER_SYMBOLIC_SCOPE_V2 => {
            let root_function = match request.root_function {
                0 => false,
                1 => true,
                _ => return Err(BoundaryError::invalid("root_function is not boolean")),
            };
            let target_hint_function = match request.target_hint_function {
                0 => false,
                1 => true,
                _ => {
                    return Err(BoundaryError::invalid(
                        "target_hint_function is not boolean",
                    ));
                }
            };
            let interproc = planner_interproc_input(request.interproc)
                .ok_or_else(|| BoundaryError::invalid("interproc planner input is invalid"))?;
            response.symbolic_scope =
                planner_symbolic_scope(r2engine::symbolic_scope_function_plan(
                    r2engine::EngineSymbolicScopeFunctionInput {
                        current_scope_count: request.current_scope_count,
                        root_function,
                        target_hint_function,
                        interproc,
                    },
                ));
        }
        R2SLEIGH_PLANNER_RUNTIME_SOURCE_V2 => {
            response.runtime_source =
                planner_runtime_source(r2engine::runtime_materialized_source_plan(
                    request.current_scope_count,
                    request.addr,
                    request.size,
                ));
        }
        R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2 => {
            let inputs = unsafe { planner_target_inputs(request)? };
            let plan = r2engine::interproc_scope_target_plan(inputs);
            response.result =
                lock_lift_registry().insert_planner_result(R2SleighPlannerResultV2 {
                    queued_targets: plan.queued_targets,
                    registration_targets: plan.registration_targets,
                    runtime_copy_targets: plan.runtime_copy_targets,
                })?;
        }
        _ => return Err(BoundaryError::invalid("planner query kind is invalid")),
    }
    Ok(response)
}

extern "C" fn planner_query(
    request: *const R2SleighPlannerQueryRequestV2,
    output: *mut R2SleighPlannerQueryResponseV2,
) -> u32 {
    lift_boundary(|| {
        valid_output_ptr(output, "planner query output")?;
        unsafe { *output = R2SleighPlannerQueryResponseV2::default() };
        valid_object_ptr(request, "planner query request")?;
        let request = unsafe { &*request };
        if request.abi_version != R2SLEIGH_ABI_V2
            || request.struct_size != u32_size::<R2SleighPlannerQueryRequestV2>()
            || request.schema_version != R2SLEIGH_PLANNER_QUERY_SCHEMA_V2
        {
            return Err(BoundaryError::abi(
                "planner query request has an incompatible envelope",
            ));
        }
        let response = planner_query_impl(request)?;
        unsafe { *output = response };
        Ok(())
    })
}

extern "C" fn planner_result_view(
    result: *const R2SleighPlannerResultV2,
    output: *mut R2SleighPlannerResultViewV2,
) -> u32 {
    lift_boundary_for(result, || {
        valid_output_ptr(output, "planner result view output")?;
        unsafe { *output = R2SleighPlannerResultViewV2::default() };
        let payload = lock_lift_registry().payload::<R2SleighPlannerResultV2>(
            result as usize,
            LiftHandleKind::PlannerResult,
            "planner result",
        )?;
        let result = unsafe { &*payload };
        unsafe {
            *output = R2SleighPlannerResultViewV2 {
                abi_version: R2SLEIGH_ABI_V2,
                struct_size: u32_size::<R2SleighPlannerResultViewV2>(),
                schema_version: R2SLEIGH_PLANNER_RESULT_SCHEMA_V2,
                queued_target_count: result.queued_targets.len(),
                registration_target_count: result.registration_targets.len(),
                runtime_copy_target_count: result.runtime_copy_targets.len(),
            };
        }
        Ok(())
    })
}

extern "C" fn planner_result_copy(
    result: *const R2SleighPlannerResultV2,
    selector: u32,
    output: *mut u64,
    capacity: usize,
    output_count: *mut usize,
) -> u32 {
    lift_boundary_for(result, || {
        valid_output_ptr(output_count, "planner result copy count")?;
        unsafe { *output_count = 0 };
        let payload = lock_lift_registry().payload::<R2SleighPlannerResultV2>(
            result as usize,
            LiftHandleKind::PlannerResult,
            "planner result",
        )?;
        let result = unsafe { &*payload };
        let values = match selector {
            R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2 => &result.queued_targets,
            R2SLEIGH_PLANNER_RESULT_REGISTRATION_TARGETS_V2 => &result.registration_targets,
            R2SLEIGH_PLANNER_RESULT_RUNTIME_COPY_TARGETS_V2 => &result.runtime_copy_targets,
            _ => return Err(BoundaryError::invalid("planner result selector is invalid")),
        };
        unsafe { *output_count = values.len() };
        if capacity < values.len() {
            return Err(BoundaryError::limit(
                "planner result output capacity is too small",
            ));
        }
        if !values.is_empty() {
            valid_output_ptr(output, "planner result copy output")?;
            unsafe { ptr::copy_nonoverlapping(values.as_ptr(), output, values.len()) };
        }
        Ok(())
    })
}

extern "C" fn planner_result_free(result: *mut R2SleighPlannerResultV2) -> u32 {
    lift_boundary_for(result, || {
        lock_lift_registry().retire(
            result as usize,
            LiftHandleKind::PlannerResult,
            "planner result",
        )
    })
}

static API_V2: R2SleighApiV2 = R2SleighApiV2 {
    abi_version: R2SLEIGH_ABI_V2,
    struct_size: size_of::<R2SleighApiV2>() as u32,
    capabilities: R2SLEIGH_CAPABILITIES_V2,
    radare_abi_version: R2SLEIGH_RADARE_ABI_V2,
    session_config_size: size_of::<R2SleighSessionConfigV2>() as u32,
    request_size: size_of::<R2SleighRequestV2>() as u32,
    engine_request_payload_size: size_of::<R2SleighEngineRequestPayloadV2>() as u32,
    function_context_size: size_of::<R2SleighFunctionContext>() as u32,
    context_param_size: size_of::<R2SleighContextParam>() as u32,
    context_var_size: size_of::<R2SleighContextVar>() as u32,
    context_base_member_size: size_of::<R2SleighContextBaseMember>() as u32,
    context_enum_variant_size: size_of::<R2SleighContextEnumVariant>() as u32,
    context_base_type_size: size_of::<R2SleighContextBaseType>() as u32,
    context_callee_size: size_of::<R2SleighContextCallee>() as u32,
    lift_quality_size: size_of::<R2SleighLiftQuality>() as u32,
    interproc_seed_size: size_of::<R2SleighInterprocSeed>() as u32,
    interproc_scope_size: size_of::<R2SleighInterprocScope>() as u32,
    interproc_plan_size: size_of::<R2SleighInterprocSessionPlan>() as u32,
    source_function_interface_size: size_of::<R2SleighSourceFunctionInterfaceV2>() as u32,
    source_parameter_size: size_of::<R2SleighSourceParameterV2>() as u32,
    source_parameter_type_size: size_of::<R2SleighSourceParameterTypeV2>() as u32,
    source_carrier_projection_size: size_of::<R2SleighSourceCarrierProjectionV2>() as u32,
    source_type_size: size_of::<R2SleighSourceTypeV2>() as u32,
    source_aggregate_member_size: size_of::<R2SleighSourceAggregateMemberV2>() as u32,
    source_aggregate_layout_size: size_of::<R2SleighSourceAggregateLayoutV2>() as u32,
    source_register_size: size_of::<R2SleighSourceRegisterV2>() as u32,
    source_stack_slot_size: size_of::<R2SleighSourceStackSlotV2>() as u32,
    source_storage_size: size_of::<R2SleighSourceStorageV2>() as u32,
    source_call_argument_size: size_of::<R2SleighSourceCallArgumentV2>() as u32,
    source_call_site_interface_size: size_of::<R2SleighSourceCallSiteInterfaceV2>() as u32,
    byte_view_size: size_of::<R2SleighByteViewV2>() as u32,
    string_view_size: size_of::<R2SleighStringViewV2>() as u32,
    phase_timing_size: size_of::<R2SleighPhaseTimingV2>() as u32,
    response_info_size: size_of::<R2SleighResponseInfoV2>() as u32,
    switch_case_size: size_of::<R2SleighSwitchCaseV2>() as u32,
    direct_call_identity_size: size_of::<R2SleighDirectCallIdentityV2>() as u32,
    analysis_render_request_size: size_of::<R2SleighAnalysisRenderRequestV2>() as u32,
    scope_render_request_size: size_of::<R2SleighScopeRenderRequestV2>() as u32,
    scope_symbol_size: size_of::<R2SleighScopeSymbolV2>() as u32,
    analysis_query_request_size: size_of::<R2SleighAnalysisQueryRequestV2>() as u32,
    analysis_result_view_size: size_of::<R2SleighAnalysisResultViewV2>() as u32,
    planner_query_request_size: size_of::<R2SleighPlannerQueryRequestV2>() as u32,
    planner_query_response_size: size_of::<R2SleighPlannerQueryResponseV2>() as u32,
    planner_target_input_size: size_of::<R2SleighPlannerTargetInputV2>() as u32,
    planner_result_view_size: size_of::<R2SleighPlannerResultViewV2>() as u32,
    radare_snapshot_input_size: size_of::<R2SleighRadareSnapshotInputV2>() as u32,
    radare_accessors_size: size_of::<R2SleighRadareAccessorsV2>() as u32,
    session_create,
    session_free,
    session_cancel,
    session_reset_cancellation,
    execute,
    response_bytes,
    response_info,
    response_free,
    session_error,
    lift_context_create,
    lift_context_free,
    lift_context_is_loaded,
    lift_context_arch_name,
    lift_context_error,
    lift_last_error,
    lift_context_reg_profile,
    lift_instruction,
    lift_block,
    lift_context_set_semantic_metadata,
    lift_block_free,
    lift_block_validate,
    lift_block_set_switch_info,
    lift_block_op_count,
    lift_block_direct_call_identity,
    lift_block_size,
    lift_block_addr,
    lift_block_mnemonic,
    lift_block_type,
    lift_block_jump,
    lift_block_fail,
    owned_bytes_view,
    owned_bytes_free,
    analysis_render,
    scope_render,
    analysis_query,
    analysis_result_view,
    analysis_result_free,
    engine_cache_reset,
    planner_query,
    planner_result_view,
    planner_result_copy,
    planner_result_free,
};

/// Return the immutable V2 API table. The table and all callback addresses are
/// process-lifetime borrows and must not be freed.
#[unsafe(no_mangle)]
pub extern "C" fn r2sleigh_api_v2() -> *const R2SleighApiV2 {
    catch_unwind(AssertUnwindSafe(|| &API_V2 as *const R2SleighApiV2)).unwrap_or(ptr::null())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config() -> R2SleighSessionConfigV2 {
        R2SleighSessionConfigV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighSessionConfigV2>(),
            required_capabilities: R2SLEIGH_CAP_DECOMPILE_V2,
        }
    }

    fn planner_request(kind: u32) -> R2SleighPlannerQueryRequestV2 {
        R2SleighPlannerQueryRequestV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighPlannerQueryRequestV2>(),
            schema_version: R2SLEIGH_PLANNER_QUERY_SCHEMA_V2,
            kind,
            ..R2SleighPlannerQueryRequestV2::default()
        }
    }

    fn planner_query_for(
        request: &R2SleighPlannerQueryRequestV2,
    ) -> (u32, R2SleighPlannerQueryResponseV2) {
        let mut response = R2SleighPlannerQueryResponseV2::default();
        let status = (API_V2.planner_query)(request, &mut response);
        (status, response)
    }

    fn scope_symbol(addr: u64, name: &[u8], linkage: u32) -> R2SleighScopeSymbolV2 {
        R2SleighScopeSymbolV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighScopeSymbolV2>(),
            schema_version: R2SLEIGH_SCOPE_SYMBOL_SCHEMA_V2,
            addr,
            name: R2SleighStringViewV2 {
                data: name.as_ptr(),
                len: name.len(),
            },
            linkage,
        }
    }

    fn scope_snapshot_request(
        symbols: &[R2SleighScopeSymbolV2],
        merge_states: u32,
    ) -> R2SleighScopeRenderRequestV2 {
        R2SleighScopeRenderRequestV2 {
            kind: R2SLEIGH_SCOPE_FUNCTION_V2,
            context: ptr::null(),
            functions: ptr::null(),
            num_functions: 0,
            entry_addr: 0,
            target_addr: 0,
            replay_seed: ptr::null(),
            argument: R2SleighStringViewV2::default(),
            external_context: R2SleighStringViewV2::default(),
            symbols: if symbols.is_empty() {
                ptr::null()
            } else {
                symbols.as_ptr()
            },
            num_symbols: symbols.len(),
            merge_states,
        }
    }

    #[test]
    fn scope_symbol_snapshot_is_owned_and_imported_linkage_is_the_only_name_authority() {
        let mut internal_name = b"memcpy".to_vec();
        let mut imported_name = b"malloc".to_vec();
        let symbols = [
            scope_symbol(
                0x4000,
                &internal_name,
                R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2,
            ),
            scope_symbol(
                0x5000,
                &imported_name,
                R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2,
            ),
        ];
        let request = scope_snapshot_request(&symbols, 1);
        let snapshot = unsafe { scope_request_snapshot(&request) }.expect("valid snapshot");
        internal_name.fill(b'x');
        imported_name.fill(b'y');

        assert!(snapshot.merge_states());
        assert_eq!(snapshot.symbols().len(), 2);
        assert!(!snapshot.symbols().imported_names().contains_key(&0x4000));
        assert_eq!(
            snapshot
                .symbols()
                .imported_names()
                .get(&0x5000)
                .map(String::as_str),
            Some("malloc")
        );
    }

    #[test]
    fn scope_symbol_snapshot_rejects_envelopes_names_linkage_and_conflicts() {
        let valid = scope_symbol(0x4000, b"local", R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2);
        for symbol in [
            R2SleighScopeSymbolV2 {
                struct_size: valid.struct_size - 1,
                ..valid
            },
            R2SleighScopeSymbolV2 {
                linkage: u32::MAX,
                ..valid
            },
            scope_symbol(0x4000, b"", R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2),
            scope_symbol(0x4000, b"bad\0name", R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2),
            scope_symbol(0x4000, &[0xff], R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2),
        ] {
            assert!(
                unsafe { scope_request_snapshot(&scope_snapshot_request(&[symbol], 0)) }.is_err()
            );
        }

        let conflicting = [
            valid,
            R2SleighScopeSymbolV2 {
                linkage: R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2,
                ..valid
            },
        ];
        assert!(
            unsafe { scope_request_snapshot(&scope_snapshot_request(&conflicting, 0)) }.is_err()
        );
        let duplicate = [valid, valid];
        assert_eq!(
            unsafe { scope_request_snapshot(&scope_snapshot_request(&duplicate, 0)) }
                .unwrap()
                .symbols()
                .len(),
            1
        );
        assert!(unsafe { scope_request_snapshot(&scope_snapshot_request(&[], 2)) }.is_err());

        let mut null_nonzero = scope_snapshot_request(&[], 0);
        null_nonzero.num_symbols = 1;
        assert!(unsafe { scope_request_snapshot(&null_nonzero) }.is_err());
        let mut nonnull_zero = scope_snapshot_request(&[], 0);
        nonnull_zero.symbols = &valid;
        assert!(unsafe { scope_request_snapshot(&nonnull_zero) }.is_err());
        let mut over_cap = scope_snapshot_request(&[], 0);
        over_cap.num_symbols = R2SLEIGH_MAX_SCOPE_SYMBOLS_V2 + 1;
        assert!(unsafe { scope_request_snapshot(&over_cap) }.is_err());
        let mut misaligned = scope_snapshot_request(&[], 0);
        misaligned.symbols = 1usize as *const R2SleighScopeSymbolV2;
        misaligned.num_symbols = 1;
        assert!(unsafe { scope_request_snapshot(&misaligned) }.is_err());
    }

    #[test]
    fn scope_symbol_snapshot_enforces_aggregate_budget_and_is_concurrent_request_local() {
        let exact_cap = (0..R2SLEIGH_MAX_SCOPE_SYMBOLS_V2)
            .map(|index| {
                scope_symbol(
                    0x1000 + index as u64,
                    b"x",
                    R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            unsafe { scope_request_snapshot(&scope_snapshot_request(&exact_cap, 0)) }
                .unwrap()
                .symbols()
                .len(),
            R2SLEIGH_MAX_SCOPE_SYMBOLS_V2
        );

        let maximum_name = vec![b'x'; R2SLEIGH_MAX_STRING_BYTES_V2];
        let symbols = (0..5)
            .map(|index| {
                scope_symbol(
                    0x4000 + index,
                    &maximum_name,
                    R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2,
                )
            })
            .collect::<Vec<_>>();
        assert!(unsafe { scope_request_snapshot(&scope_snapshot_request(&symbols, 0)) }.is_err());

        let outcomes = [false, true].map(|merge_states| {
            std::thread::spawn(move || {
                let name = if merge_states { b"malloc" } else { b"memcpy" };
                let symbol = scope_symbol(0x5000, name, R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2);
                let symbols = [symbol];
                let request = scope_snapshot_request(&symbols, u32::from(merge_states));
                let snapshot = unsafe { scope_request_snapshot(&request) }.unwrap();
                (
                    snapshot.merge_states(),
                    snapshot.symbols().imported_names().get(&0x5000).cloned(),
                )
            })
        });
        let [merge_off, merge_on] = outcomes;
        assert_eq!(
            merge_off.join().unwrap(),
            (false, Some("memcpy".to_string()))
        );
        assert_eq!(merge_on.join().unwrap(), (true, Some("malloc".to_string())));
    }

    #[test]
    fn planner_query_table_routes_scalar_engine_plans() {
        assert_ne!(API_V2.capabilities & R2SLEIGH_CAP_PLANNER_QUERY_V2, 0);
        assert_eq!(
            API_V2.planner_query_request_size as usize,
            size_of::<R2SleighPlannerQueryRequestV2>()
        );
        assert_eq!(
            API_V2.planner_query_response_size as usize,
            size_of::<R2SleighPlannerQueryResponseV2>()
        );

        let mut request = planner_request(R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2);
        request.depth = r2engine::RADARE2_ANALYSIS_DEPTH_BASIC;
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(response.kind, request.kind);
        assert_eq!(response.analysis_policy.mode, R2SLEIGH_MODE_FAST_V2);
        assert_eq!(
            response.analysis_policy.type_writeback_mode,
            R2SLEIGH_TYPE_WRITEBACK_OFF_V2
        );

        request = planner_request(R2SLEIGH_PLANNER_POST_ANALYSIS_V2);
        request.function_count = 1;
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(response.post_analysis.mode, R2SLEIGH_MODE_BALANCED_V2);
        assert_eq!(response.post_analysis.function_count, 1);
        assert_eq!(response.post_analysis.xref_enabled, 1);

        request = planner_request(R2SLEIGH_PLANNER_AUTO_CALLBACK_V2);
        request.depth = r2engine::RADARE2_ANALYSIS_DEPTH_AGGRESSIVE;
        request.callback_kind = R2SLEIGH_AUTO_CALLBACK_DATA_REFS_V2;
        request.basic_block_count = r2engine::AUTO_CALLBACK_MAX_BLOCKS as usize;
        request.cost = r2engine::AUTO_CALLBACK_MAX_COST;
        request.linear_size = r2engine::AUTO_CALLBACK_MAX_LINEAR_SIZE;
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(response.auto_callback.allowed, 1);
        assert_eq!(
            response.auto_callback.reason,
            R2SLEIGH_AUTO_CALLBACK_REASON_ALLOWED_V2
        );

        request = planner_request(R2SLEIGH_PLANNER_INTERPROC_SESSION_V2);
        request.purpose = R2SLEIGH_INTERPROC_SESSION_TYPE_ANALYSIS_V2;
        request.basic_block_count = r2engine::ENGINE_INTERPROC_HELPER_MAX_BLOCKS as usize;
        request.cost = r2engine::ENGINE_INTERPROC_HELPER_MAX_COST;
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(response.interproc_session.include_type_interproc_scope, 1);
        assert_eq!(response.interproc_session.interproc_converged, 1);

        request = planner_request(R2SLEIGH_PLANNER_SYMBOLIC_SCOPE_V2);
        request.root_function = 1;
        request.interproc.interproc_converged = 1;
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(response.symbolic_scope.append_function, 1);
        assert_eq!(response.symbolic_scope.expand_targets, 1);
        assert_eq!(
            response.symbolic_scope.reason,
            R2SLEIGH_SYMBOLIC_SCOPE_REASON_ALLOWED_V2
        );

        request = planner_request(R2SLEIGH_PLANNER_RUNTIME_SOURCE_V2);
        request.addr = 0x9000;
        request.size = 0x20;
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(response.runtime_source.append_source, 1);
        assert_eq!(response.runtime_source.capped_size, 0x20);
        assert_eq!(
            response.runtime_source.reason,
            R2SLEIGH_RUNTIME_SOURCE_REASON_ALLOWED_V2
        );
    }

    fn planner_target(
        direct_target: u64,
        name: &'static [u8],
        linkage: u32,
        resolved_target: u64,
    ) -> R2SleighPlannerTargetInputV2 {
        R2SleighPlannerTargetInputV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighPlannerTargetInputV2>(),
            schema_version: R2SLEIGH_PLANNER_TARGET_INPUT_SCHEMA_V2,
            direct_target,
            name: R2SleighStringViewV2 {
                data: name.as_ptr(),
                len: name.len(),
            },
            linkage,
            resolved_target,
            has_resolved_target: 1,
            target_materialized: 1,
            has_target_metrics: 1,
            target_basic_block_count: 1,
            target_cost: 1,
        }
    }

    #[test]
    fn planner_target_result_is_registry_owned_copied_and_thread_affine() {
        let targets = [
            planner_target(
                0x3000,
                b"sym.imp.AddVectoredExceptionHandler",
                R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2,
                0x3000,
            ),
            planner_target(
                0x4000,
                b"sym.local_helper",
                R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2,
                0x4010,
            ),
            planner_target(
                0x5000,
                b"sym.imp.memcpy",
                R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2,
                0x5000,
            ),
        ];
        let mut request = planner_request(R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2);
        request.targets = targets.as_ptr();
        request.num_targets = targets.len();
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert!(!response.result.is_null());

        let mut view = R2SleighPlannerResultViewV2::default();
        assert_eq!(
            (API_V2.planner_result_view)(response.result, &mut view),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(view.queued_target_count, 2);
        assert_eq!(view.registration_target_count, 1);
        assert_eq!(view.runtime_copy_target_count, 1);

        let mut count = 0;
        assert_eq!(
            (API_V2.planner_result_copy)(
                response.result,
                R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2,
                ptr::null_mut(),
                0,
                &mut count,
            ),
            R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2
        );
        assert_eq!(count, 2);

        let mut queued = [0u64; 2];
        assert_eq!(
            (API_V2.planner_result_copy)(
                response.result,
                R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2,
                queued.as_mut_ptr(),
                queued.len(),
                &mut count,
            ),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(count, 2);
        assert_eq!(queued, [0x4000, 0x4010]);
        assert_eq!(
            (API_V2.planner_result_copy)(
                response.result,
                R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2,
                queued.as_mut_ptr(),
                1,
                &mut count,
            ),
            R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2
        );
        assert_eq!(count, 2);

        let handle = response.result as usize;
        assert_eq!(
            std::thread::spawn(move || {
                let mut view = R2SleighPlannerResultViewV2::default();
                (API_V2.planner_result_view)(handle as *const _, &mut view)
            })
            .join()
            .expect("planner thread"),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(
            std::thread::spawn(move || {
                (API_V2.planner_result_free)(handle as *mut R2SleighPlannerResultV2)
            })
            .join()
            .expect("planner free thread"),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(
            (API_V2.planner_result_view)(response.result, &mut view),
            R2SLEIGH_STATUS_OK_V2,
            "wrong-thread free refusal must retain the owner"
        );
        assert_eq!(
            (API_V2.planner_result_free)(response.result),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(
            (API_V2.planner_result_view)(response.result, &mut view),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(
            (API_V2.planner_result_free)(response.result),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2,
            "double free must remain stale"
        );
    }

    #[test]
    fn planner_result_copy_validates_selector_count_and_empty_output() {
        let request = planner_request(R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2);
        let (status, empty) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert!(!empty.result.is_null());
        let mut count = usize::MAX;
        assert_eq!(
            (API_V2.planner_result_copy)(
                empty.result,
                R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2,
                ptr::null_mut(),
                0,
                &mut count,
            ),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(count, 0);
        count = usize::MAX;
        assert_eq!(
            (API_V2.planner_result_copy)(empty.result, u32::MAX, ptr::null_mut(), 0, &mut count,),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(count, 0);
        assert_eq!(
            (API_V2.planner_result_copy)(
                empty.result,
                R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2,
                ptr::null_mut(),
                0,
                ptr::null_mut(),
            ),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );

        let wrong_kind = lock_lift_registry()
            .insert_owned_bytes(
                0,
                R2SleighOwnedBytesV2 {
                    bytes: CString::new("planner wrong kind").unwrap(),
                },
            )
            .expect("registered wrong-kind handle");
        let mut view = R2SleighPlannerResultViewV2::default();
        let mut count = usize::MAX;
        assert_eq!(
            (API_V2.planner_result_view)(wrong_kind.cast(), &mut view),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(
            (API_V2.planner_result_copy)(
                wrong_kind.cast(),
                R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2,
                ptr::null_mut(),
                0,
                &mut count,
            ),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(count, 0);
        assert_eq!(
            (API_V2.planner_result_free)(wrong_kind.cast()),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(
            (API_V2.owned_bytes_free)(wrong_kind),
            R2SLEIGH_STATUS_OK_V2,
            "wrong-kind refusal must retain the true owner"
        );
        assert_eq!(
            (API_V2.planner_result_free)(empty.result),
            R2SLEIGH_STATUS_OK_V2
        );
    }

    #[test]
    fn planner_target_ingress_rejects_bad_envelopes_utf8_and_exact_tags() {
        fn query_target(target: &R2SleighPlannerTargetInputV2) -> u32 {
            let mut request = planner_request(R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2);
            request.targets = target;
            request.num_targets = 1;
            planner_query_for(&request).0
        }

        let mut target = planner_target(
            0x4000,
            b"local",
            R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2,
            0x4000,
        );
        for invalid in [2, u32::MAX] {
            target.target_materialized = invalid;
            assert_eq!(query_target(&target), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        }
        target.target_materialized = 1;
        target.linkage = u32::MAX;
        assert_eq!(query_target(&target), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        target.linkage = R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2;
        target.struct_size -= 1;
        assert_eq!(query_target(&target), R2SLEIGH_STATUS_ABI_MISMATCH_V2);
        target.struct_size = u32_size::<R2SleighPlannerTargetInputV2>();
        let invalid_utf8 = [0xff];
        target.name = R2SleighStringViewV2 {
            data: invalid_utf8.as_ptr(),
            len: invalid_utf8.len(),
        };
        assert_eq!(query_target(&target), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        let mut request = planner_request(R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2);
        request.targets = ptr::null();
        request.num_targets = 1;
        assert_eq!(
            planner_query_for(&request).0,
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        request.num_targets = R2SLEIGH_MAX_PLANNER_TARGETS_V2 + 1;
        assert_eq!(
            planner_query_for(&request).0,
            R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2
        );

        let exact_cap_target =
            planner_target(0x4000, b"", R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2, 0x4000);
        let exact_cap_targets = vec![exact_cap_target; R2SLEIGH_MAX_PLANNER_TARGETS_V2];
        request.targets = exact_cap_targets.as_ptr();
        request.num_targets = exact_cap_targets.len();
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(
            (API_V2.planner_result_free)(response.result),
            R2SLEIGH_STATUS_OK_V2
        );

        let maximum_name = vec![b'x'; R2SLEIGH_MAX_STRING_BYTES_V2];
        let mut aggregate_targets = vec![exact_cap_target; 5];
        for target in &mut aggregate_targets {
            target.name = R2SleighStringViewV2 {
                data: maximum_name.as_ptr(),
                len: maximum_name.len(),
            };
        }
        request.targets = aggregate_targets.as_ptr();
        request.num_targets = aggregate_targets.len();
        assert_eq!(
            planner_query_for(&request).0,
            R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2,
            "aggregate target-name bytes must remain bounded"
        );
    }

    #[test]
    fn planner_target_ingress_rejects_invalid_boolean_and_dependency_matrix() {
        fn query_target(target: &R2SleighPlannerTargetInputV2) -> u32 {
            let mut request = planner_request(R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2);
            request.targets = target;
            request.num_targets = 1;
            planner_query_for(&request).0
        }

        let valid = planner_target(
            0x4000,
            b"local",
            R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2,
            0x4010,
        );
        for invalid in [2, u32::MAX] {
            for target in [
                R2SleighPlannerTargetInputV2 {
                    has_resolved_target: invalid,
                    ..valid
                },
                R2SleighPlannerTargetInputV2 {
                    target_materialized: invalid,
                    ..valid
                },
                R2SleighPlannerTargetInputV2 {
                    has_target_metrics: invalid,
                    ..valid
                },
            ] {
                assert_eq!(query_target(&target), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
            }
        }

        for target in [
            R2SleighPlannerTargetInputV2 {
                has_resolved_target: 0,
                ..valid
            },
            R2SleighPlannerTargetInputV2 {
                has_resolved_target: 0,
                resolved_target: 0,
                ..valid
            },
            R2SleighPlannerTargetInputV2 {
                has_target_metrics: 0,
                ..valid
            },
            R2SleighPlannerTargetInputV2 {
                target_materialized: 0,
                ..valid
            },
        ] {
            assert_eq!(query_target(&target), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        }

        let absent = R2SleighPlannerTargetInputV2 {
            resolved_target: 0,
            has_resolved_target: 0,
            target_materialized: 0,
            has_target_metrics: 0,
            target_basic_block_count: 0,
            target_cost: 0,
            ..valid
        };
        let mut request = planner_request(R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2);
        request.targets = &absent;
        request.num_targets = 1;
        let (status, response) = planner_query_for(&request);
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(
            (API_V2.planner_result_free)(response.result),
            R2SLEIGH_STATUS_OK_V2
        );
    }

    #[test]
    fn planner_query_rejects_bad_tags_kinds_enums_and_booleans() {
        let mut response = R2SleighPlannerQueryResponseV2::default();
        assert_eq!(
            (API_V2.planner_query)(ptr::null(), &mut response),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        let request = planner_request(R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2);
        assert_eq!(
            (API_V2.planner_query)(&request, ptr::null_mut()),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );

        for request in [
            R2SleighPlannerQueryRequestV2 {
                abi_version: R2SLEIGH_ABI_V2 + 1,
                ..request
            },
            R2SleighPlannerQueryRequestV2 {
                struct_size: request.struct_size - 1,
                ..request
            },
            R2SleighPlannerQueryRequestV2 {
                schema_version: R2SLEIGH_PLANNER_QUERY_SCHEMA_V2 + 1,
                ..request
            },
        ] {
            let (status, response) = planner_query_for(&request);
            assert_eq!(status, R2SLEIGH_STATUS_ABI_MISMATCH_V2);
            assert_eq!(response, R2SleighPlannerQueryResponseV2::default());
        }

        let invalid = [
            R2SleighPlannerQueryRequestV2 {
                kind: u32::MAX,
                ..request
            },
            R2SleighPlannerQueryRequestV2 {
                kind: R2SLEIGH_PLANNER_AUTO_CALLBACK_V2,
                callback_kind: u32::MAX,
                ..request
            },
            R2SleighPlannerQueryRequestV2 {
                kind: R2SLEIGH_PLANNER_INTERPROC_SESSION_V2,
                purpose: u32::MAX,
                ..request
            },
            R2SleighPlannerQueryRequestV2 {
                kind: R2SLEIGH_PLANNER_SYMBOLIC_SCOPE_V2,
                root_function: 2,
                ..request
            },
            R2SleighPlannerQueryRequestV2 {
                kind: R2SLEIGH_PLANNER_SYMBOLIC_SCOPE_V2,
                interproc: R2SleighInterprocSessionPlan {
                    interproc_converged: 2,
                    ..R2SleighInterprocSessionPlan::default()
                },
                ..request
            },
        ];
        for request in invalid {
            let (status, response) = planner_query_for(&request);
            assert_eq!(status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
            assert_eq!(response, R2SleighPlannerQueryResponseV2::default());
        }
    }

    #[test]
    fn planner_query_rejects_nonzero_inactive_fields_for_every_kind() {
        let target = planner_target(
            0x4000,
            b"local",
            R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2,
            0x4000,
        );
        let invalid = [
            R2SleighPlannerQueryRequestV2 {
                purpose: 1,
                ..planner_request(R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                targets: &target,
                ..planner_request(R2SLEIGH_PLANNER_POST_ANALYSIS_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                function_count: 1,
                callback_kind: R2SLEIGH_AUTO_CALLBACK_ANALYZE_FUNCTION_V2,
                ..planner_request(R2SLEIGH_PLANNER_AUTO_CALLBACK_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                purpose: R2SLEIGH_INTERPROC_SESSION_TYPE_ANALYSIS_V2,
                linear_size: 1,
                ..planner_request(R2SLEIGH_PLANNER_INTERPROC_SESSION_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                depth: 1,
                ..planner_request(R2SLEIGH_PLANNER_SYMBOLIC_SCOPE_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                interproc: R2SleighInterprocSessionPlan {
                    interproc_iter: 1,
                    ..R2SleighInterprocSessionPlan::default()
                },
                ..planner_request(R2SLEIGH_PLANNER_RUNTIME_SOURCE_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                addr: 1,
                ..planner_request(R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2)
            },
        ];
        for request in invalid {
            let (status, response) = planner_query_for(&request);
            assert_eq!(status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
            assert_eq!(response, R2SleighPlannerQueryResponseV2::default());
        }
    }

    #[test]
    #[cfg(feature = "x86")]
    fn lift_core_table_round_trip_owns_strings_and_handles() {
        let api = &API_V2;
        assert_ne!(api.capabilities & R2SLEIGH_CAP_LIFT_CORE_V2, 0);
        assert_eq!(api.struct_size as usize, size_of::<R2SleighApiV2>());
        assert_eq!(
            api.string_view_size as usize,
            size_of::<R2SleighStringViewV2>()
        );
        assert_eq!(
            api.switch_case_size as usize,
            size_of::<R2SleighSwitchCaseV2>()
        );
        assert_eq!(
            api.direct_call_identity_size as usize,
            size_of::<R2SleighDirectCallIdentityV2>()
        );

        let arch = b"x86-64";
        let mut context = ptr::null_mut();
        assert_eq!(
            (api.lift_context_create)(
                R2SleighStringViewV2 {
                    data: arch.as_ptr(),
                    len: arch.len(),
                },
                &mut context,
            ),
            R2SLEIGH_STATUS_OK_V2
        );
        assert!(!context.is_null());
        let context_token = context as usize;

        let mut loaded = 0;
        assert_eq!(
            (api.lift_context_is_loaded)(context, &mut loaded),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(loaded, 1);

        let mut arch_name = R2SleighByteViewV2::default();
        assert_eq!(
            (api.lift_context_arch_name)(context, &mut arch_name),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(
            unsafe { slice::from_raw_parts(arch_name.data, arch_name.len) },
            arch
        );

        let mut profile = ptr::null_mut();
        assert_eq!(
            (api.lift_context_reg_profile)(context, &mut profile),
            R2SLEIGH_STATUS_OK_V2
        );
        assert!(!profile.is_null());
        let mut profile_view = R2SleighByteViewV2::default();
        assert_eq!(
            (api.owned_bytes_view)(profile, &mut profile_view),
            R2SLEIGH_STATUS_OK_V2
        );
        let profile_copy =
            unsafe { slice::from_raw_parts(profile_view.data, profile_view.len).to_vec() };
        assert!(profile_copy.windows(4).any(|window| window == b"=PC\t"));
        assert_eq!((api.owned_bytes_free)(profile), R2SLEIGH_STATUS_OK_V2);

        let bytes = [0x31, 0xc0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let byte_view = R2SleighByteViewV2 {
            data: bytes.as_ptr(),
            len: bytes.len(),
        };
        let mut block = ptr::null_mut();
        assert_eq!(
            (api.lift_instruction)(context, byte_view, 0x1000, &mut block),
            R2SLEIGH_STATUS_OK_V2
        );
        assert!(!block.is_null());
        assert_eq!(
            (api.lift_block_validate)(context, block),
            R2SLEIGH_STATUS_OK_V2
        );
        let mut addr = 0;
        let mut size = 0;
        let mut op_count = 0;
        assert_eq!(
            (api.lift_block_addr)(block, &mut addr),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(
            (api.lift_block_size)(block, &mut size),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(
            (api.lift_block_op_count)(block, &mut op_count),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(addr, 0x1000);
        assert!(size > 0);
        assert!(op_count > 0);

        let block_handles = [block as *const R2ILBlock];
        let render_request = R2SleighAnalysisRenderRequestV2 {
            kind: R2SLEIGH_ANALYSIS_BLOCK_ESIL_V2,
            context,
            blocks: block_handles.as_ptr(),
            num_blocks: block_handles.len(),
            op_index: 0,
            argument: R2SleighStringViewV2::default(),
        };
        let mut rendered = ptr::null_mut();
        assert_eq!(
            (api.analysis_render)(&render_request, &mut rendered),
            R2SLEIGH_STATUS_OK_V2
        );
        let mut rendered_view = R2SleighByteViewV2::default();
        assert_eq!(
            (api.owned_bytes_view)(rendered, &mut rendered_view),
            R2SLEIGH_STATUS_OK_V2
        );
        assert!(rendered_view.len > 0);

        let query_request = R2SleighAnalysisQueryRequestV2 {
            kind: R2SLEIGH_QUERY_BLOCK_VALUES_V2,
            context,
            blocks: block_handles.as_ptr(),
            num_blocks: block_handles.len(),
            function_addr: 0,
            function_name: R2SleighStringViewV2::default(),
            input_values: ptr::null(),
            num_input_values: 0,
        };
        let mut analysis_result = ptr::null_mut();
        assert_eq!(
            (api.analysis_query)(&query_request, &mut analysis_result),
            R2SLEIGH_STATUS_OK_V2
        );
        let mut analysis_view = R2SleighAnalysisResultViewV2::default();
        assert_eq!(
            (api.analysis_result_view)(analysis_result, &mut analysis_view),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(analysis_view.kind, R2SLEIGH_QUERY_BLOCK_VALUES_V2);
        assert_eq!(
            (api.analysis_result_free)(analysis_result),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(
            (api.analysis_result_view)(analysis_result, &mut analysis_view),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!((api.owned_bytes_free)(rendered), R2SLEIGH_STATUS_OK_V2);

        let mut mnemonic = ptr::null_mut();
        assert_eq!(
            (api.lift_block_mnemonic)(context, byte_view, 0x1000, &mut mnemonic),
            R2SLEIGH_STATUS_OK_V2
        );
        let mut mnemonic_view = R2SleighByteViewV2::default();
        assert_eq!(
            (api.owned_bytes_view)(mnemonic, &mut mnemonic_view),
            R2SLEIGH_STATUS_OK_V2
        );
        assert!(mnemonic_view.len > 0);
        assert_eq!((api.owned_bytes_free)(mnemonic), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(
            (api.lift_context_free)(context),
            R2SLEIGH_STATUS_ENGINE_ERROR_V2,
            "context consumption must reject live child handles"
        );
        let mut context_error = R2SleighByteViewV2::default();
        assert_eq!(
            (api.lift_context_error)(context, &mut context_error),
            R2SLEIGH_STATUS_OK_V2
        );
        let context_error = unsafe { slice::from_raw_parts(context_error.data, context_error.len) };
        assert!(String::from_utf8_lossy(context_error).contains("live child handles"));

        let one_case = [R2SleighSwitchCaseV2 {
            value: 0,
            target: 0x1000,
        }];
        assert_eq!(
            (api.lift_block_set_switch_info)(
                block,
                0x1000,
                0,
                0,
                0,
                2,
                one_case.as_ptr(),
                one_case.len(),
            ),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        let mut block_error = R2SleighByteViewV2::default();
        assert_eq!(
            (api.lift_context_error)(context, &mut block_error),
            R2SLEIGH_STATUS_OK_V2
        );
        let block_error = unsafe { slice::from_raw_parts(block_error.data, block_error.len) };
        assert!(String::from_utf8_lossy(block_error).contains("switch default flag"));
        assert_eq!((api.lift_block_free)(block), R2SLEIGH_STATUS_OK_V2);
        assert_eq!((api.lift_context_free)(context), R2SLEIGH_STATUS_OK_V2);

        let mut next_context = ptr::null_mut();
        assert_eq!(
            (api.lift_context_create)(
                R2SleighStringViewV2 {
                    data: arch.as_ptr(),
                    len: arch.len(),
                },
                &mut next_context,
            ),
            R2SLEIGH_STATUS_OK_V2
        );
        assert!(next_context as usize > context_token);
        assert_eq!(
            (api.lift_context_is_loaded)(context, &mut loaded),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2,
            "retired token must remain stale after later allocation"
        );
        assert_eq!((api.lift_context_free)(next_context), R2SLEIGH_STATUS_OK_V2);
    }

    #[test]
    fn lift_core_rejects_malformed_pointers_and_byte_views() {
        let api = &API_V2;
        let arch = b"x86-64";
        let arch_view = R2SleighStringViewV2 {
            data: arch.as_ptr(),
            len: arch.len(),
        };
        assert_eq!(
            (api.lift_context_create)(arch_view, ptr::null_mut()),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(
            (api.lift_context_create)(arch_view, 1usize as *mut *mut R2ILContext),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        let mut block = ptr::null_mut();
        assert_eq!(
            (api.lift_instruction)(
                ptr::null_mut(),
                R2SleighByteViewV2 {
                    data: ptr::null(),
                    len: 1,
                },
                0,
                &mut block,
            ),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert!(block.is_null());
        assert_eq!(
            (api.lift_instruction)(
                align_of::<R2ILContext>() as *mut R2ILContext,
                R2SleighByteViewV2 {
                    data: ptr::null(),
                    len: R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2 + 1,
                },
                0,
                &mut block,
            ),
            R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2
        );
        assert_eq!(
            (api.lift_block_op_count)(ptr::null(), 1usize as *mut usize),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        let mut unknown_size = 0;
        assert_eq!(
            (api.lift_block_size)(
                (align_of::<R2ILBlock>() * 128) as *const R2ILBlock,
                &mut unknown_size,
            ),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2,
            "an aligned fake handle must fail registry ownership proof"
        );
        let owned = lock_lift_registry()
            .insert_owned_bytes(
                0,
                R2SleighOwnedBytesV2 {
                    bytes: CString::new("wrong kind").unwrap(),
                },
            )
            .expect("registered owned bytes");
        let mut size = 0;
        assert_eq!(
            (api.lift_block_size)(owned.cast(), &mut size),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!((api.owned_bytes_free)(owned), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(
            (api.owned_bytes_free)(owned),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        let mut error = R2SleighByteViewV2::default();
        assert_eq!((api.lift_last_error)(&mut error), R2SLEIGH_STATUS_OK_V2);
        let error = unsafe { slice::from_raw_parts(error.data, error.len) };
        assert!(String::from_utf8_lossy(error).contains("stale"));

        let cases = [R2SleighSwitchCaseV2::default()];
        assert_eq!(
            (api.lift_block_set_switch_info)(
                align_of::<R2ILBlock>() as *mut R2ILBlock,
                0,
                0,
                0,
                0,
                0,
                cases.as_ptr(),
                R2SLEIGH_MAX_SWITCH_CASES_V2 + 1,
            ),
            R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2
        );
        assert_eq!(
            (api.owned_bytes_free)(ptr::null_mut()),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
    }

    #[test]
    #[cfg(feature = "x86")]
    fn lift_core_rejects_cross_context_blocks() {
        let api = &API_V2;
        let arch_bytes = b"x86-64";
        let arch = R2SleighStringViewV2 {
            data: arch_bytes.as_ptr(),
            len: arch_bytes.len(),
        };
        let mut first = ptr::null_mut();
        let mut second = ptr::null_mut();
        assert_eq!(
            (api.lift_context_create)(arch, &mut first),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(
            (api.lift_context_create)(arch, &mut second),
            R2SLEIGH_STATUS_OK_V2
        );
        let bytes = [0x31, 0xc0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let mut block = ptr::null_mut();
        assert_eq!(
            (api.lift_instruction)(
                first,
                R2SleighByteViewV2 {
                    data: bytes.as_ptr(),
                    len: bytes.len(),
                },
                0x1000,
                &mut block,
            ),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(
            (api.lift_block_validate)(second, block),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!((api.lift_block_free)(block), R2SLEIGH_STATUS_OK_V2);
        assert_eq!((api.lift_context_free)(first), R2SLEIGH_STATUS_OK_V2);
        assert_eq!((api.lift_context_free)(second), R2SLEIGH_STATUS_OK_V2);
    }

    #[test]
    fn lift_core_boundary_contains_panics() {
        assert_eq!(
            lift_boundary(|| -> Result<(), BoundaryError> {
                panic!("lift-core boundary test panic")
            }),
            R2SLEIGH_STATUS_PANIC_V2
        );
    }

    fn assert_semantic_kernel_render_diagnostics(
        region: r2engine::EngineSemanticKernelRegion,
        expected_region_name: &str,
        expected_schema_version: u32,
    ) {
        assert_eq!(
            engine_semantic_kernel_region_schema(region),
            expected_schema_version
        );
        let diagnostics = r2engine::EngineDiagnostics {
            semantic_kernel_render: Some(r2engine::EngineSemanticKernelRender {
                region,
                region_schema_version: expected_schema_version,
                exact_obligation_closure: true,
            }),
            ..Default::default()
        };
        let encoded = response_diagnostics_json(&diagnostics).expect("supported diagnostics");
        let decoded: serde_json::Value = serde_json::from_str(&encoded).expect("diagnostics JSON");
        assert_eq!(
            decoded["semantic_kernel_render"],
            serde_json::json!({
                "region_id": format!("{expected_region_name}_v{expected_schema_version}"),
                "region_schema_version": expected_schema_version,
                "exact_obligation_closure": true,
            })
        );
    }

    #[test]
    fn aggregate_semantic_kernel_diagnostics_are_stable_json() {
        assert_semantic_kernel_render_diagnostics(
            r2engine::EngineSemanticKernelRegion::AggregateMemberTerminalReturnFunction,
            "aggregate_member_terminal_return_function",
            3,
        );
    }

    #[test]
    fn generic_semantic_kernel_diagnostics_are_stable_json() {
        assert_semantic_kernel_render_diagnostics(
            r2engine::EngineSemanticKernelRegion::TerminalReturnBlock,
            "terminal_return_block",
            3,
        );
    }

    #[test]
    fn every_current_semantic_kernel_region_has_a_stable_identifier() {
        let regions = [
            (
                r2engine::EngineSemanticKernelRegion::TerminalReturnBlock,
                "terminal_return_block",
                3,
            ),
            (
                r2engine::EngineSemanticKernelRegion::AggregateMemberTerminalReturnFunction,
                "aggregate_member_terminal_return_function",
                3,
            ),
            (
                r2engine::EngineSemanticKernelRegion::PlainRamMemoryTerminalReturnFunction,
                "plain_ram_memory_terminal_return_function",
                3,
            ),
            (
                r2engine::EngineSemanticKernelRegion::DirectCallTerminalReturnFunction,
                "direct_call_terminal_return_function",
                3,
            ),
            (
                r2engine::EngineSemanticKernelRegion::ConditionalTerminalReturnFunction,
                "conditional_terminal_return_function",
                3,
            ),
            (
                r2engine::EngineSemanticKernelRegion::SwitchTerminalReturnFunction,
                "switch_terminal_return_function",
                3,
            ),
            (
                r2engine::EngineSemanticKernelRegion::CarrierFreeLoopTerminalReturnFunction,
                "carrier_free_loop_terminal_return_function",
                3,
            ),
        ];
        for (region, expected, expected_schema_version) in regions {
            assert_eq!(engine_semantic_kernel_region_name(region), expected);
            assert_semantic_kernel_render_diagnostics(region, expected, expected_schema_version);
        }
    }

    #[test]
    fn future_semantic_kernel_region_schema_is_refused() {
        let region = r2engine::EngineSemanticKernelRegion::TerminalReturnBlock;
        let expected_schema = engine_semantic_kernel_region_schema(region);
        let future_schema = expected_schema.checked_add(1).expect("future schema");
        let diagnostics = r2engine::EngineDiagnostics {
            semantic_kernel_render: Some(r2engine::EngineSemanticKernelRender {
                region,
                region_schema_version: future_schema,
                exact_obligation_closure: true,
            }),
            ..Default::default()
        };
        let error = response_diagnostics_json(&diagnostics).expect_err("future schema refusal");
        assert_eq!(error.status, R2SLEIGH_STATUS_UNSUPPORTED_V2);
        assert_eq!(
            error.message,
            format!(
                "unsupported semantic-kernel region schema version {future_schema} for terminal_return_block; expected {expected_schema}"
            )
        );
    }

    fn native_function_context(external_context: &CString) -> R2SleighFunctionContext {
        R2SleighFunctionContext {
            schema_version: R2SLEIGH_FUNCTION_CONTEXT_SCHEMA_V2,
            dirty_epoch: 0,
            context_hash: 0,
            type_dirty_epoch: 0,
            external_context_json: external_context.as_ptr(),
            signature_name: ptr::null(),
            signature_ret_type: ptr::null(),
            signature_callconv: ptr::null(),
            signature_noreturn: 0,
            params: ptr::null(),
            num_params: 0,
            vars: ptr::null(),
            num_vars: 0,
            base_types: ptr::null(),
            num_base_types: 0,
            callees: ptr::null(),
            num_callees: 0,
            assumptions_json: ptr::null(),
        }
    }

    fn native_decompile_payload(
        ctx: *const R2ILContext,
        blocks: &[*const R2ILBlock],
        function_name: &CString,
        external_context: &CString,
        timeout_us: u64,
    ) -> R2SleighEngineRequestPayloadV2 {
        R2SleighEngineRequestPayloadV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighEngineRequestPayloadV2>(),
            ctx,
            blocks: blocks.as_ptr(),
            num_blocks: blocks.len(),
            function_addr: 0x401000,
            function_name: function_name.as_ptr(),
            function_context: native_function_context(external_context),
            lift_quality: R2SleighLiftQuality {
                expected_blocks: blocks.len(),
                lifted_blocks: blocks.len(),
                read_failures: 0,
                invalid_blocks: 0,
                null_lift_failures: 0,
                truncated_blocks: 0,
            },
            interproc_scope: R2SleighInterprocScope {
                schema_version: R2SLEIGH_INTERPROC_SCOPE_SCHEMA_V2,
                functions: ptr::null(),
                num_functions: 0,
                seeds: ptr::null(),
                num_seeds: 0,
            },
            interproc_plan: R2SleighInterprocSessionPlan {
                include_type_interproc_scope: 0,
                include_root_symbolic_scope: 0,
                interproc_iter: 0,
                interproc_max_iters: 1,
                interproc_converged: 0,
            },
            analysis_depth: 0,
            timeout_us,
            radare_snapshot: ptr::null(),
            source_interface: ptr::null(),
        }
    }

    fn native_request(payload: &R2SleighEngineRequestPayloadV2) -> R2SleighRequestV2 {
        R2SleighRequestV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighRequestV2>(),
            kind: R2SLEIGH_REQUEST_DECOMPILE_V2,
            flags: 0,
            payload: (payload as *const R2SleighEngineRequestPayloadV2).cast(),
            payload_size: size_of::<R2SleighEngineRequestPayloadV2>(),
        }
    }

    fn response_text(response: *const R2SleighResponseV2) -> String {
        let mut bytes = R2SleighByteViewV2::default();
        assert_eq!(response_bytes(response, &mut bytes), R2SLEIGH_STATUS_OK_V2);
        String::from_utf8(unsafe { slice::from_raw_parts(bytes.data, bytes.len) }.to_vec())
            .expect("response UTF-8")
    }

    #[cfg(feature = "x86")]
    fn x86_return_fixture() -> (*mut R2ILContext, *mut R2ILBlock) {
        let (arch, disasm) =
            super::super::create_disassembler_for_arch("x86-64").expect("x86-64 disassembler");
        let block = disasm
            .lift_block(&[0xc3], 0x401000, 1)
            .expect("lift return block");
        let mut registry = lock_lift_registry();
        let context = registry
            .insert_context(Box::new(R2ILContext::with_arch_and_disasm(arch, disasm)))
            .expect("registered x86 context");
        let owner = registry
            .entry(context as usize, LiftHandleKind::Context, "x86 context")
            .expect("registered context entry")
            .generation;
        let block = registry
            .insert_block(owner, Box::new(block))
            .expect("registered return block");
        (context, block)
    }

    fn validate_seed_hint(
        arg_count_hint: usize,
        has_arg_count_hint: i32,
    ) -> Result<(), BoundaryError> {
        let name = b"callee\0";
        let seed = super::super::R2SleighInterprocSeed {
            id: 1,
            name: name.as_ptr().cast(),
            arg_count_hint,
            has_arg_count_hint,
            linkage: 0,
        };
        let scope = R2SleighInterprocScope {
            schema_version: R2SLEIGH_INTERPROC_SCOPE_SCHEMA_V2,
            functions: ptr::null(),
            num_functions: 0,
            seeds: &seed,
            num_seeds: 1,
        };
        unsafe { validate_interproc_scope(&scope, &mut ValidationBudget::default()) }
    }

    unsafe fn source_snapshot_with_new_budget(
        source: *const R2SleighSourceFunctionInterfaceV2,
        ctx: *const R2ILContext,
        blocks: &[*const R2ILBlock],
        function_addr: u64,
        context_hash: u64,
    ) -> Result<Option<Arc<r2engine::EngineSourceSnapshot>>, BoundaryError> {
        unsafe {
            source_snapshot(
                source,
                ctx,
                blocks.as_ptr(),
                blocks.len(),
                function_addr,
                context_hash,
                &mut ValidationBudget::default(),
            )
        }
    }

    fn wire_register_storage(offset: u64, size: u32) -> R2SleighSourceStorageV2 {
        R2SleighSourceStorageV2 {
            space: R2SLEIGH_SOURCE_STORAGE_REGISTER_V2,
            custom_space: 0,
            offset,
            size,
        }
    }

    fn void_source_interface(
        calling_convention: &[u8],
        stack_slots: &[R2SleighSourceStackSlotV2],
        return_address_storage: R2SleighSourceStorageV2,
        stack_pointer_storage: R2SleighSourceStorageV2,
    ) -> R2SleighSourceFunctionInterfaceV2 {
        R2SleighSourceFunctionInterfaceV2 {
            schema_version: R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2,
            struct_size: u32_size::<R2SleighSourceFunctionInterfaceV2>(),
            revision_identity: 1,
            function_addr: 0x401000,
            calling_convention: R2SleighStringViewV2 {
                data: calling_convention.as_ptr(),
                len: calling_convention.len(),
            },
            parameters: ptr::null(),
            num_parameters: 0,
            stack_slots: stack_slots.as_ptr(),
            num_stack_slots: stack_slots.len(),
            return_kind: R2SLEIGH_SOURCE_RETURN_VOID_V2,
            return_storage: R2SleighSourceRegisterV2 {
                name: R2SleighStringViewV2 {
                    data: ptr::null(),
                    len: 0,
                },
                offset: 0,
                size: 0,
            },
            variadic: 0,
            noreturn: 0,
            stack_resources_complete: 1,
            complete: 1,
            call_sites: ptr::null(),
            num_call_sites: 0,
            call_sites_complete: 0,
            parameter_types: ptr::null(),
            num_parameter_types: 0,
            return_type_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
            return_carrier: R2SleighSourceCarrierProjectionV2::default(),
            types: ptr::null(),
            num_types: 0,
            aggregates: ptr::null(),
            num_aggregates: 0,
            exact_types_complete: 0,
            stack_slot_roles_complete: 1,
            return_address_storage,
            stack_pointer_storage,
        }
    }

    #[test]
    fn exact_source_type_graph_is_owned_and_rejects_malformed_wire_data() {
        let member_names: [&[u8]; 14] = [
            b"first",
            b"second",
            b"third",
            b"fourth",
            b"fifth",
            b"sixth",
            b"seventh",
            b"eighth",
            b"ninth",
            b"tenth",
            b"eleventh",
            b"twelfth",
            b"thirteenth",
            b"fourteenth",
        ];
        let mut members: [R2SleighSourceAggregateMemberV2; 14] =
            std::array::from_fn(|index| R2SleighSourceAggregateMemberV2 {
                member_id: index as u32,
                type_id: 1,
                offset_bits: index as u64 * 32,
                size_bits: 32,
                count: 0,
                name: R2SleighStringViewV2 {
                    data: member_names[index].as_ptr(),
                    len: member_names[index].len(),
                },
            });
        let aggregate_name = b"DemoStruct";
        let aggregates = [R2SleighSourceAggregateLayoutV2 {
            id: 0,
            type_id: 0,
            size_bits: 56 * 8,
            align_bits: 32,
            name: R2SleighStringViewV2 {
                data: aggregate_name.as_ptr(),
                len: aggregate_name.len(),
            },
            members: members.as_ptr(),
            num_members: members.len(),
            complete: 1,
            c_layout_compatible: 1,
        }];
        let mut types = [
            R2SleighSourceTypeV2 {
                id: 0,
                kind: R2SLEIGH_SOURCE_TYPE_STRUCT_V2,
                size_bits: 56 * 8,
                align_bits: 32,
                target_type_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
                aggregate_id: 0,
            },
            R2SleighSourceTypeV2 {
                id: 1,
                kind: R2SLEIGH_SOURCE_TYPE_SIGNED_INTEGER_V2,
                size_bits: 32,
                align_bits: 32,
                target_type_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
                aggregate_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
            },
            R2SleighSourceTypeV2 {
                id: 2,
                kind: R2SLEIGH_SOURCE_TYPE_POINTER_V2,
                size_bits: 64,
                align_bits: 64,
                target_type_id: 0,
                aggregate_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
            },
        ];
        let mut parameter_types = [
            R2SleighSourceParameterTypeV2 {
                index: 0,
                type_id: 2,
                carrier: R2SleighSourceCarrierProjectionV2 {
                    kind: R2SLEIGH_SOURCE_CARRIER_FULL_V2,
                    offset_bits: 0,
                    size_bits: 64,
                },
            },
            R2SleighSourceParameterTypeV2 {
                index: 1,
                type_id: 1,
                carrier: R2SleighSourceCarrierProjectionV2 {
                    kind: R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2,
                    offset_bits: 0,
                    size_bits: 32,
                },
            },
            R2SleighSourceParameterTypeV2 {
                index: 2,
                type_id: 1,
                carrier: R2SleighSourceCarrierProjectionV2 {
                    kind: R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2,
                    offset_bits: 0,
                    size_bits: 32,
                },
            },
        ];
        let parameters = [
            R2SleighSourceParameterV2 {
                index: 0,
                storage: R2SleighSourceRegisterV2 {
                    name: R2SleighStringViewV2::default(),
                    offset: 0,
                    size: 8,
                },
            },
            R2SleighSourceParameterV2 {
                index: 1,
                storage: R2SleighSourceRegisterV2 {
                    name: R2SleighStringViewV2::default(),
                    offset: 8,
                    size: 8,
                },
            },
            R2SleighSourceParameterV2 {
                index: 2,
                storage: R2SleighSourceRegisterV2 {
                    name: R2SleighStringViewV2::default(),
                    offset: 16,
                    size: 8,
                },
            },
        ];
        let mut source = void_source_interface(
            b"sysv",
            &[],
            wire_register_storage(0, 8),
            wire_register_storage(24, 8),
        );
        source.parameters = parameters.as_ptr();
        source.num_parameters = parameters.len();
        source.return_kind = R2SLEIGH_SOURCE_RETURN_REGISTER_V2;
        source.return_storage.size = 8;
        source.parameter_types = parameter_types.as_ptr();
        source.num_parameter_types = parameter_types.len();
        source.return_type_id = 1;
        source.return_carrier = R2SleighSourceCarrierProjectionV2 {
            kind: R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2,
            offset_bits: 0,
            size_bits: 32,
        };
        source.types = types.as_ptr();
        source.num_types = types.len();
        source.aggregates = aggregates.as_ptr();
        source.num_aggregates = aggregates.len();
        source.exact_types_complete = 1;

        let owned = unsafe {
            validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
        }
        .expect("valid exact type graph")
        .expect("authoritative type graph");
        assert_eq!(owned.types.len(), 3);
        assert_eq!(owned.parameter_types[0].type_id, 2);
        assert_eq!(owned.return_type_id, Some(1));
        assert_eq!(owned.aggregates[0].size_bits, 56 * 8);
        assert_eq!(owned.aggregates[0].members[2].offset_bits, 8 * 8);
        assert_eq!(owned.aggregates[0].members[13].offset_bits, 52 * 8);
        assert_eq!(owned.aggregates[0].members[13].name, "fourteenth");

        types[2].id = 9;
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err()
        );
        types[2].id = 2;

        types[1].align_bits = 16;
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err()
        );
        types[1].align_bits = 32;

        types[2].size_bits = 32;
        types[2].align_bits = 32;
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err()
        );
        types[2].size_bits = 64;
        types[2].align_bits = 64;
        assert_eq!((types[2].size_bits, types[2].align_bits), (64, 64));

        members[13].offset_bits = 48 * 8;
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err()
        );
        members[13].offset_bits = 52 * 8;
        assert_eq!(members[13].offset_bits, 52 * 8);

        parameter_types[1].carrier.kind = R2SLEIGH_SOURCE_CARRIER_FULL_V2;
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err()
        );
        parameter_types[1].carrier.kind = R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2;
        assert_eq!(
            parameter_types[1].carrier.kind,
            R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2
        );

        let types_ptr = source.types;
        source.types = ptr::null();
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err()
        );
        source.types = types_ptr;

        let type_count = source.num_types;
        source.num_types = R2SLEIGH_MAX_CONTEXT_ITEMS_V2 + 1;
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err()
        );
        source.num_types = type_count;

        source.exact_types_complete = 0;
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err()
        );
    }

    #[test]
    fn exact_scalar_pointer_type_graph_is_owned_and_rejects_pointer_pointees() {
        let mut types = [
            R2SleighSourceTypeV2 {
                id: 0,
                kind: R2SLEIGH_SOURCE_TYPE_UNSIGNED_INTEGER_V2,
                size_bits: 8,
                align_bits: 8,
                target_type_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
                aggregate_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
            },
            R2SleighSourceTypeV2 {
                id: 1,
                kind: R2SLEIGH_SOURCE_TYPE_POINTER_V2,
                size_bits: 64,
                align_bits: 64,
                target_type_id: 0,
                aggregate_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
            },
            R2SleighSourceTypeV2 {
                id: 2,
                kind: R2SLEIGH_SOURCE_TYPE_UNSIGNED_INTEGER_V2,
                size_bits: 64,
                align_bits: 64,
                target_type_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
                aggregate_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
            },
        ];
        let parameter_types = [
            R2SleighSourceParameterTypeV2 {
                index: 0,
                type_id: 1,
                carrier: R2SleighSourceCarrierProjectionV2 {
                    kind: R2SLEIGH_SOURCE_CARRIER_FULL_V2,
                    offset_bits: 0,
                    size_bits: 64,
                },
            },
            R2SleighSourceParameterTypeV2 {
                index: 1,
                type_id: 2,
                carrier: R2SleighSourceCarrierProjectionV2 {
                    kind: R2SLEIGH_SOURCE_CARRIER_FULL_V2,
                    offset_bits: 0,
                    size_bits: 64,
                },
            },
        ];
        let parameters = [
            R2SleighSourceParameterV2 {
                index: 0,
                storage: R2SleighSourceRegisterV2 {
                    name: R2SleighStringViewV2::default(),
                    offset: 0,
                    size: 8,
                },
            },
            R2SleighSourceParameterV2 {
                index: 1,
                storage: R2SleighSourceRegisterV2 {
                    name: R2SleighStringViewV2::default(),
                    offset: 8,
                    size: 8,
                },
            },
        ];
        let mut source = void_source_interface(
            b"aapcs64",
            &[],
            wire_register_storage(0, 8),
            wire_register_storage(24, 8),
        );
        source.parameters = parameters.as_ptr();
        source.num_parameters = parameters.len();
        source.return_kind = R2SLEIGH_SOURCE_RETURN_REGISTER_V2;
        source.return_storage.size = 8;
        source.parameter_types = parameter_types.as_ptr();
        source.num_parameter_types = parameter_types.len();
        source.return_type_id = 2;
        source.return_carrier = R2SleighSourceCarrierProjectionV2 {
            kind: R2SLEIGH_SOURCE_CARRIER_FULL_V2,
            offset_bits: 0,
            size_bits: 64,
        };
        source.types = types.as_ptr();
        source.num_types = types.len();
        source.exact_types_complete = 1;

        let owned = unsafe {
            validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
        }
        .expect("valid exact scalar-pointer graph")
        .expect("authoritative scalar-pointer graph");
        assert_eq!(owned.types.len(), 3);
        assert_eq!(owned.parameter_types[0].type_id, 1);
        assert_eq!(owned.types[1].target_type_id, Some(0));
        assert_eq!(owned.types[0].kind, OwnedSourceTypeKind::UnsignedInteger);
        assert!(owned.aggregates.is_empty());

        types[1].target_type_id = 1;
        assert_eq!(types[1].target_type_id, 1);
        assert!(
            unsafe {
                validate_source_type_graph(&source, &parameters, &mut ValidationBudget::default())
            }
            .is_err(),
            "pointer-to-pointer graphs remain outside the exact v1 subset"
        );
    }

    #[test]
    fn wrong_session_version_is_rejected_without_allocating() {
        let mut config = config();
        config.abi_version += 1;
        let mut session = ptr::null_mut();
        assert_eq!(
            session_create(&config, &mut session),
            R2SLEIGH_STATUS_ABI_MISMATCH_V2
        );
        assert!(session.is_null());
    }

    #[test]
    fn wrong_request_version_is_rejected_with_borrowed_error() {
        let mut session = ptr::null_mut();
        assert_eq!(
            session_create(&config(), &mut session),
            R2SLEIGH_STATUS_OK_V2
        );
        let request = R2SleighRequestV2 {
            abi_version: R2SLEIGH_ABI_V2 + 1,
            struct_size: u32_size::<R2SleighRequestV2>(),
            kind: R2SLEIGH_REQUEST_DECOMPILE_V2,
            flags: 0,
            payload: ptr::null(),
            payload_size: 0,
        };
        let mut response = ptr::null_mut();
        assert_eq!(
            unsafe { execute(session, &request, &mut response) },
            R2SLEIGH_STATUS_ABI_MISMATCH_V2
        );
        assert!(response.is_null());
        let mut error = R2SleighByteViewV2::default();
        assert_eq!(session_error(session, &mut error), R2SLEIGH_STATUS_OK_V2);
        assert!(!error.data.is_null());
        assert_eq!(session_free(session), R2SLEIGH_STATUS_OK_V2);
    }

    #[cfg(feature = "x86")]
    #[test]
    fn session_cancel_and_reset_are_one_request_execution_controls() {
        let (ctx, block) = x86_return_fixture();
        let blocks = [block as *const R2ILBlock];
        let function_name = CString::new("sym.cancel_transport").unwrap();
        let external_context = CString::new("{}").unwrap();
        let payload = native_decompile_payload(ctx, &blocks, &function_name, &external_context, 0);
        let request = native_request(&payload);
        let mut session = ptr::null_mut();
        assert_eq!(
            session_create(&config(), &mut session),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(session_cancel(session), R2SLEIGH_STATUS_OK_V2);

        let mut response = ptr::null_mut();
        assert_eq!(
            unsafe { execute(session, &request, &mut response) },
            R2SLEIGH_STATUS_OK_V2
        );
        assert!(!response.is_null());
        let mut info = unsafe { std::mem::zeroed::<R2SleighResponseInfoV2>() };
        assert_eq!(response_info(response, &mut info), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(info.outcome, R2SLEIGH_OUTCOME_REFUSED_V2);
        let timings = unsafe { slice::from_raw_parts(info.phase_timings, info.num_phase_timings) };
        assert_eq!(timings.len(), R2SLEIGH_PHASE_COUNT_V2);
        assert_eq!(
            timings[R2SLEIGH_PHASE_SNAPSHOT_CONTEXT_V2 as usize].status,
            R2SLEIGH_PHASE_STATUS_REFUSED_V2
        );
        assert_eq!(
            timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2 as usize].status,
            R2SLEIGH_PHASE_STATUS_EXECUTED_V2
        );
        assert_eq!(
            timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2 as usize].elapsed_us,
            info.ffi_conversion_elapsed_us
        );
        let cancelled = response_text(response);
        assert!(cancelled.contains("cancelled before snapshot_context"));
        assert!(!cancelled.contains("return;"), "{cancelled}");
        assert_eq!(response_free(response), R2SLEIGH_STATUS_OK_V2);

        assert_eq!(session_reset_cancellation(session), R2SLEIGH_STATUS_OK_V2);
        response = ptr::null_mut();
        assert_eq!(
            unsafe { execute(session, &request, &mut response) },
            R2SLEIGH_STATUS_OK_V2
        );
        assert_eq!(response_info(response, &mut info), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(info.outcome, R2SLEIGH_OUTCOME_REFUSED_V2);
        let reset = response_text(response);
        assert!(
            !reset.contains("cancelled before snapshot_context"),
            "reset must clear the one-request cancellation even when the mutable lift is refused by the genuine-lift certification gate: {reset}"
        );
        assert_eq!(response_free(response), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(session_free(session), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(lift_block_free(block), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(lift_context_free(ctx), R2SLEIGH_STATUS_OK_V2);
    }

    #[cfg(feature = "x86")]
    #[test]
    fn expired_native_timeout_refuses_without_partial_c() {
        let (ctx, block) = x86_return_fixture();
        let blocks = [block as *const R2ILBlock];
        let function_name = CString::new("sym.timeout_transport").unwrap();
        let external_context =
            CString::new(format!("{{\"padding\":\"{}\"}}", "x".repeat(256 * 1024))).unwrap();
        let payload = native_decompile_payload(ctx, &blocks, &function_name, &external_context, 1);
        let request = native_request(&payload);
        let mut session = ptr::null_mut();
        assert_eq!(
            session_create(&config(), &mut session),
            R2SLEIGH_STATUS_OK_V2
        );

        let mut response = ptr::null_mut();
        assert_eq!(
            unsafe { execute(session, &request, &mut response) },
            R2SLEIGH_STATUS_OK_V2
        );
        assert!(!response.is_null());
        let mut info = unsafe { std::mem::zeroed::<R2SleighResponseInfoV2>() };
        assert_eq!(response_info(response, &mut info), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(info.outcome, R2SLEIGH_OUTCOME_REFUSED_V2);
        let refused = response_text(response);
        assert!(refused.contains("deadline exceeded before snapshot_context"));
        assert!(!refused.contains("return;"), "{refused}");
        assert_eq!(response_free(response), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(session_free(session), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(lift_block_free(block), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(lift_context_free(ctx), R2SLEIGH_STATUS_OK_V2);
    }

    #[test]
    fn null_output_and_count_cap_are_rejected_before_slice_creation() {
        assert_eq!(
            session_create(&config(), ptr::null_mut()),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        let error = unsafe {
            checked_slice::<*const R2ILBlock>(
                ptr::null(),
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2 + 1,
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                "blocks",
            )
            .expect_err("count cap")
        };
        assert_eq!(error.status, R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2);
    }

    #[test]
    fn invalid_owners_clear_all_caller_owned_outputs() {
        let mut response = ptr::dangling_mut::<R2SleighResponseV2>();
        assert_eq!(
            unsafe { execute(ptr::null_mut(), ptr::null(), &mut response) },
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert!(response.is_null());

        let mut bytes = R2SleighByteViewV2 {
            data: ptr::dangling(),
            len: usize::MAX,
        };
        assert_eq!(
            response_bytes(ptr::null(), &mut bytes),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert!(bytes.data.is_null());
        assert_eq!(bytes.len, 0);

        let mut info = R2SleighResponseInfoV2 {
            schema_version: u32::MAX,
            struct_size: u32::MAX,
            request_kind: u32::MAX,
            outcome: u32::MAX,
            phase_timings: ptr::dangling(),
            num_phase_timings: usize::MAX,
            ffi_conversion_elapsed_us: u64::MAX,
            diagnostics_json: R2SleighByteViewV2 {
                data: ptr::dangling(),
                len: usize::MAX,
            },
        };
        assert_eq!(
            response_info(ptr::null(), &mut info),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(info.schema_version, 0);
        assert!(info.phase_timings.is_null());
        assert!(info.diagnostics_json.data.is_null());

        bytes = R2SleighByteViewV2 {
            data: ptr::dangling(),
            len: usize::MAX,
        };
        assert_eq!(
            session_error(ptr::null(), &mut bytes),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert!(bytes.data.is_null());
        assert_eq!(bytes.len, 0);
    }

    #[test]
    fn block_depth_gate_accepts_cap_and_rejects_next_count() {
        let block = R2ILBlock::new(0x1000, 1);
        let blocks = [&block as *const R2ILBlock; R2SLEIGH_MAX_FUNCTION_BLOCKS_V2];
        unsafe {
            validate_blocks(
                blocks.as_ptr(),
                blocks.len(),
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                R2SLEIGH_MAX_FUNCTION_OPS_V2,
                "blocks at cap",
                &mut ValidationBudget::default(),
            )
            .expect("block cap is accepted");
        }
        let error = unsafe {
            validate_blocks(
                ptr::null(),
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2 + 1,
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                R2SLEIGH_MAX_FUNCTION_OPS_V2,
                "blocks above cap",
                &mut ValidationBudget::default(),
            )
            .expect_err("block count above cap")
        };
        assert_eq!(error.status, R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2);
    }

    #[test]
    fn operation_gate_refuses_before_engine_conversion() {
        let mut block = R2ILBlock::new(0x1000, 1);
        let op = r2il::R2ILOp::Copy {
            dst: r2il::Varnode::unique(0, 8),
            src: r2il::Varnode::constant(0, 8),
        };
        block.ops.resize(R2SLEIGH_MAX_FUNCTION_OPS_V2 + 1, op);
        let blocks = [&block as *const R2ILBlock];
        let error = unsafe {
            validate_blocks(
                blocks.as_ptr(),
                blocks.len(),
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                R2SLEIGH_MAX_FUNCTION_OPS_V2,
                "decompile.blocks",
                &mut ValidationBudget::default(),
            )
            .expect_err("operation count above cap")
        };
        assert_eq!(error.status, R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2);
        assert!(error.message.contains("per-function cap (512)"));
    }

    #[test]
    fn request_wide_operation_budget_is_aggregate_and_checked() {
        let mut full = R2ILBlock::new(0x1000, 1);
        let op = r2il::R2ILOp::Copy {
            dst: r2il::Varnode::unique(0, 8),
            src: r2il::Varnode::constant(0, 8),
        };
        full.ops.resize(R2SLEIGH_MAX_FUNCTION_OPS_V2, op.clone());
        let mut one = R2ILBlock::new(0x2000, 1);
        one.ops.push(op);
        let full_blocks = [&full as *const R2ILBlock];
        let one_block = [&one as *const R2ILBlock];
        let mut budget = ValidationBudget::default();
        for index in 0..(R2SLEIGH_MAX_AGGREGATE_OPS_V2 / R2SLEIGH_MAX_FUNCTION_OPS_V2) {
            unsafe {
                validate_blocks(
                    full_blocks.as_ptr(),
                    full_blocks.len(),
                    R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                    R2SLEIGH_MAX_FUNCTION_OPS_V2,
                    &format!("scope[{index}]"),
                    &mut budget,
                )
                .expect("aggregate operation budget through the cap");
            }
        }
        let error = unsafe {
            validate_blocks(
                one_block.as_ptr(),
                one_block.len(),
                R2SLEIGH_MAX_FUNCTION_BLOCKS_V2,
                R2SLEIGH_MAX_FUNCTION_OPS_V2,
                "scope[overflow]",
                &mut budget,
            )
            .expect_err("aggregate operation count above cap")
        };
        assert_eq!(error.status, R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2);
        assert!(
            error
                .message
                .contains("aggregate scope[overflow] exceeds cap (4096)")
        );
    }

    #[test]
    fn aggregate_string_budget_rejects_reused_large_borrows() {
        let mut bytes = vec![b'x'; R2SLEIGH_MAX_STRING_BYTES_V2];
        bytes.push(0);
        let parameter = R2SleighContextParam {
            name: bytes.as_ptr().cast(),
            type_name: ptr::null(),
            cc_reg: ptr::null(),
        };
        let mut budget = ValidationBudget::default();
        for index in 0..(R2SLEIGH_MAX_AGGREGATE_STRING_BYTES_V2 / R2SLEIGH_MAX_STRING_BYTES_V2) {
            unsafe {
                validate_context_param(&parameter, &format!("params[{index}]"), &mut budget)
                    .expect("aggregate string bytes through the cap");
            }
        }
        let error = unsafe {
            validate_context_param(&parameter, "params[overflow]", &mut budget)
                .expect_err("aggregate strings above cap")
        };
        assert_eq!(error.status, R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2);
        assert!(
            error
                .message
                .contains("aggregate params[overflow].name exceeds cap")
        );
    }

    #[test]
    fn oversized_request_is_rejected_before_context_or_engine_dereference() {
        let payload = R2SleighEngineRequestPayloadV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighEngineRequestPayloadV2>(),
            ctx: std::ptr::NonNull::<R2ILContext>::dangling().as_ptr(),
            blocks: ptr::null(),
            num_blocks: R2SLEIGH_MAX_FUNCTION_BLOCKS_V2 + 1,
            function_addr: 0x401000,
            function_name: ptr::null(),
            function_context: unsafe { std::mem::zeroed() },
            lift_quality: R2SleighLiftQuality::default(),
            interproc_scope: unsafe { std::mem::zeroed() },
            interproc_plan: R2SleighInterprocSessionPlan {
                include_type_interproc_scope: 0,
                include_root_symbolic_scope: 0,
                interproc_iter: 0,
                interproc_max_iters: 0,
                interproc_converged: 1,
            },
            analysis_depth: 0,
            timeout_us: 0,
            radare_snapshot: ptr::null(),
            source_interface: ptr::null(),
        };
        let request = R2SleighRequestV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighRequestV2>(),
            kind: R2SLEIGH_REQUEST_DECOMPILE_V2,
            flags: 0,
            payload: (&payload as *const R2SleighEngineRequestPayloadV2).cast(),
            payload_size: size_of::<R2SleighEngineRequestPayloadV2>(),
        };
        let error =
            unsafe { execute_request(&request, r2engine::EngineCancellationToken::default()) }
                .expect_err("oversized root CFG");
        assert_eq!(error.status, R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2);
        assert!(error.message.ends_with("blocks count exceeds cap"));
    }

    fn opaque_request(payload: &R2SleighEngineRequestPayloadV2) -> R2SleighRequestV2 {
        R2SleighRequestV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighRequestV2>(),
            kind: R2SLEIGH_REQUEST_DECOMPILE_V2,
            flags: 0,
            payload: (payload as *const R2SleighEngineRequestPayloadV2).cast(),
            payload_size: size_of::<R2SleighEngineRequestPayloadV2>(),
        }
    }

    fn opaque_payload(source: &R2SleighRadareSnapshotInputV2) -> R2SleighEngineRequestPayloadV2 {
        // Zero is the canonical inactive representation for every detached
        // request field in the opaque source route.
        let mut payload = unsafe { std::mem::zeroed::<R2SleighEngineRequestPayloadV2>() };
        payload.abi_version = R2SLEIGH_ABI_V2;
        payload.struct_size = u32_size::<R2SleighEngineRequestPayloadV2>();
        payload.radare_snapshot = source;
        payload
    }

    #[test]
    fn opaque_source_rejects_stale_schema_before_foreign_access() {
        let source = R2SleighRadareSnapshotInputV2 {
            struct_size: u32_size::<R2SleighRadareSnapshotInputV2>(),
            abi_version: R2SLEIGH_RADARE_ABI_V2,
            snapshot_schema_version: R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2 - 1,
            accessor_schema_version: R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2,
            snapshot: ptr::null(),
            accessors: ptr::null(),
        };
        let payload = opaque_payload(&source);
        let error = unsafe {
            execute_request(
                &opaque_request(&payload),
                r2engine::EngineCancellationToken::default(),
            )
        }
        .expect_err("stale source schema");
        assert_eq!(error.status, R2SLEIGH_STATUS_ABI_MISMATCH_V2);
    }

    #[test]
    fn opaque_source_rejects_null_handles_and_detached_authority() {
        let source = R2SleighRadareSnapshotInputV2 {
            struct_size: u32_size::<R2SleighRadareSnapshotInputV2>(),
            abi_version: R2SLEIGH_RADARE_ABI_V2,
            snapshot_schema_version: R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2,
            accessor_schema_version: R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2,
            snapshot: ptr::null(),
            accessors: ptr::null(),
        };
        let payload = opaque_payload(&source);
        let error = unsafe {
            execute_request(
                &opaque_request(&payload),
                r2engine::EngineCancellationToken::default(),
            )
        }
        .expect_err("null opaque source handles");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let mut payload = opaque_payload(&source);
        payload.function_addr = 0x401000;
        let error = unsafe {
            execute_request(
                &opaque_request(&payload),
                r2engine::EngineCancellationToken::default(),
            )
        }
        .expect_err("detached identity beside opaque authority");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("detached or inactive authority"));
    }

    #[test]
    fn opaque_source_honors_cancellation_before_foreign_access() {
        let source = R2SleighRadareSnapshotInputV2 {
            struct_size: u32_size::<R2SleighRadareSnapshotInputV2>(),
            abi_version: R2SLEIGH_RADARE_ABI_V2,
            snapshot_schema_version: R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2,
            accessor_schema_version: R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2,
            snapshot: std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
            accessors: std::ptr::NonNull::<R2SleighRadareAccessorsV2>::dangling().as_ptr(),
        };
        let payload = opaque_payload(&source);
        let cancellation = r2engine::EngineCancellationToken::default();
        cancellation.cancel();
        let error = unsafe { execute_request(&opaque_request(&payload), cancellation) }
            .expect_err("cancelled opaque ingress");
        assert_eq!(error.status, R2SLEIGH_STATUS_ENGINE_ERROR_V2);
        assert!(error.message.contains("trusted ingress stopped"));
    }

    #[test]
    fn interproc_seed_arg_count_hint_requires_boolean_presence() {
        let error = validate_seed_hint(1, 2).expect_err("non-boolean seed hint presence");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
    }

    #[test]
    fn nested_native_schemas_are_enforced_before_conversion() {
        let external_context = CString::new("{}").unwrap();
        let mut context = native_function_context(&external_context);
        context.schema_version = R2SLEIGH_FUNCTION_CONTEXT_SCHEMA_V2 + 1;
        let error =
            unsafe { validate_function_context(&context, &mut ValidationBudget::default()) }
                .expect_err("future function-context schema");
        assert_eq!(error.status, R2SLEIGH_STATUS_ABI_MISMATCH_V2);

        let scope = R2SleighInterprocScope {
            schema_version: R2SLEIGH_INTERPROC_SCOPE_SCHEMA_V2 + 1,
            functions: ptr::null(),
            num_functions: 0,
            seeds: ptr::null(),
            num_seeds: 0,
        };
        let error = unsafe { validate_interproc_scope(&scope, &mut ValidationBudget::default()) }
            .expect_err("future interprocedural-scope schema");
        assert_eq!(error.status, R2SLEIGH_STATUS_ABI_MISMATCH_V2);
    }

    #[test]
    fn nested_native_boolean_fields_reject_noncanonical_values() {
        let mut var = R2SleighContextVar {
            kind: 0,
            name: ptr::null(),
            type_name: ptr::null(),
            reg: ptr::null(),
            base: ptr::null(),
            offset: 0,
            has_offset: 2,
            role: 0,
            param_index: -1,
            param_name: ptr::null(),
            source_reg: ptr::null(),
            is_arg: 0,
        };
        let error = unsafe { validate_context_var(&var, "var", &mut ValidationBudget::default()) }
            .expect_err("non-boolean variable offset presence");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        var.has_offset = 0;
        var.is_arg = -1;
        let error = unsafe { validate_context_var(&var, "var", &mut ValidationBudget::default()) }
            .expect_err("non-boolean variable argument flag");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let member = R2SleighContextBaseMember {
            name: ptr::null(),
            type_name: ptr::null(),
            offset: 0,
            size_bits: 0,
            has_size_bits: 2,
        };
        let mut base_type = R2SleighContextBaseType {
            kind: 0,
            name: ptr::null(),
            type_name: ptr::null(),
            size_bits: 0,
            has_size_bits: 0,
            members: &member,
            num_members: 1,
            variants: ptr::null(),
            num_variants: 0,
        };
        let error = unsafe {
            validate_base_type(&base_type, "base_type", &mut ValidationBudget::default())
        }
        .expect_err("non-boolean member size presence");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        base_type.has_size_bits = 2;
        let error = unsafe {
            validate_base_type(&base_type, "base_type", &mut ValidationBudget::default())
        }
        .expect_err("non-boolean base-type size presence");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let callee = R2SleighContextCallee {
            call_addr: 0,
            addr: 0,
            name: ptr::null(),
            linkage: 0,
            signature_name: ptr::null(),
            signature_ret_type: ptr::null(),
            signature_callconv: ptr::null(),
            signature_noreturn: 2,
            signature_params: ptr::null(),
            num_signature_params: 0,
        };
        let error = unsafe { validate_callee(&callee, "callee", &mut ValidationBudget::default()) }
            .expect_err("non-boolean callee noreturn");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let external_context = CString::new("{}").unwrap();
        let mut context = native_function_context(&external_context);
        context.signature_noreturn = 2;
        let error =
            unsafe { validate_function_context(&context, &mut ValidationBudget::default()) }
                .expect_err("non-boolean function noreturn");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
    }

    #[test]
    fn interproc_seed_arg_count_hint_is_bounded_before_engine_use() {
        validate_seed_hint(MAX_ABI_ARGUMENTS, 1).expect("ABI argument cap is accepted");

        let error =
            validate_seed_hint(MAX_ABI_ARGUMENTS + 1, 1).expect_err("ABI argument count above cap");
        assert_eq!(error.status, R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2);

        let error = validate_seed_hint(usize::MAX, 1).expect_err("huge ABI argument count");
        assert_eq!(error.status, R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2);

        validate_seed_hint(usize::MAX, 0).expect("absent argument hint has no arity");
    }

    #[test]
    fn execute_contains_panics_and_preserves_borrowed_error() {
        let mut session = ptr::null_mut();
        assert_eq!(
            session_create(&config(), &mut session),
            R2SLEIGH_STATUS_OK_V2
        );
        let request = R2SleighRequestV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighRequestV2>(),
            kind: R2SLEIGH_REQUEST_DECOMPILE_V2,
            flags: REQUEST_FLAG_TEST_PANIC,
            payload: ptr::null(),
            payload_size: 0,
        };
        let mut response = ptr::null_mut();
        assert_eq!(
            unsafe { execute(session, &request, &mut response) },
            R2SLEIGH_STATUS_PANIC_V2
        );
        assert!(response.is_null());
        let mut first = R2SleighByteViewV2::default();
        let mut second = R2SleighByteViewV2::default();
        assert_eq!(session_error(session, &mut first), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(session_error(session, &mut second), R2SLEIGH_STATUS_OK_V2);
        assert!(!first.data.is_null());
        assert_eq!(first.data, second.data);
        assert_eq!(first.len, second.len);
        assert_eq!(session_free(session), R2SLEIGH_STATUS_OK_V2);
    }

    #[test]
    fn response_ownership_and_views_are_stable_until_free() {
        let mut phase_timings = std::array::from_fn(|phase| R2SleighPhaseTimingV2 {
            phase: phase as u32,
            status: R2SLEIGH_PHASE_STATUS_NOT_EXECUTED_V2,
            elapsed_us: 0,
        });
        phase_timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2 as usize] = R2SleighPhaseTimingV2 {
            phase: R2SLEIGH_PHASE_FFI_CONVERSION_V2,
            status: R2SLEIGH_PHASE_STATUS_EXECUTED_V2,
            elapsed_us: 7,
        };
        let response = lock_engine_registry()
            .insert_response(Arc::new(R2SleighResponseV2 {
                bytes: CString::new("owned response").unwrap(),
                diagnostics: CString::new("{\"warnings\":[]}").unwrap(),
                phase_timings,
                request_kind: R2SLEIGH_REQUEST_DECOMPILE_V2,
                outcome: R2SLEIGH_OUTCOME_COMPLETED_V2,
                ffi_conversion_elapsed_us: 7,
            }))
            .expect("registered response");
        let forged = 0x1000usize as *mut R2SleighResponseV2;
        let mut forged_bytes = R2SleighByteViewV2 {
            data: ptr::dangling(),
            len: usize::MAX,
        };
        assert_eq!(
            response_bytes(forged, &mut forged_bytes),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert!(forged_bytes.data.is_null());
        assert_eq!(forged_bytes.len, 0);
        assert_eq!(response_free(forged), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert_eq!(
            session_free(response.cast::<R2SleighSessionV2>()),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2,
            "reverse wrong-kind free must preserve the response owner"
        );
        let mut first = R2SleighByteViewV2::default();
        let mut second = R2SleighByteViewV2::default();
        assert_eq!(response_bytes(response, &mut first), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(response_bytes(response, &mut second), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(first.data, second.data);
        assert_eq!(first.len, "owned response".len());
        let bytes = unsafe { slice::from_raw_parts(first.data, first.len) };
        assert_eq!(bytes, b"owned response");
        let mut info = unsafe { std::mem::zeroed::<R2SleighResponseInfoV2>() };
        assert_eq!(response_info(response, &mut info), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(R2SLEIGH_RESPONSE_INFO_SCHEMA_V2, 2);
        assert_eq!(info.schema_version, R2SLEIGH_RESPONSE_INFO_SCHEMA_V2);
        assert_eq!(info.num_phase_timings, R2SLEIGH_PHASE_COUNT_V2);
        assert_eq!(info.ffi_conversion_elapsed_us, 7);
        assert!(!info.phase_timings.is_null());
        assert!(!info.diagnostics_json.data.is_null());
        let timings = unsafe { slice::from_raw_parts(info.phase_timings, info.num_phase_timings) };
        assert_eq!(
            timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2 as usize].elapsed_us,
            info.ffi_conversion_elapsed_us
        );
        assert_eq!(response_free(response), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(response_free(response), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert_eq!(
            response_bytes(response, &mut first),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert!(first.data.is_null());
        assert_eq!(first.len, 0);
        let mut stale_info = unsafe { std::mem::zeroed::<R2SleighResponseInfoV2>() };
        stale_info.schema_version = u32::MAX;
        stale_info.phase_timings = ptr::dangling();
        assert_eq!(
            response_info(response, &mut stale_info),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert_eq!(stale_info.schema_version, 0);
        assert!(stale_info.phase_timings.is_null());
    }

    #[test]
    fn session_tokens_reject_forgery_cross_kind_stale_and_double_free() {
        let mut session = ptr::null_mut();
        assert_eq!(
            session_create(&config(), &mut session),
            R2SLEIGH_STATUS_OK_V2
        );
        let forged = 0x1000usize as *mut R2SleighSessionV2;
        assert_eq!(session_cancel(forged), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert_eq!(session_free(forged), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        assert_eq!(
            response_free(session.cast::<R2SleighResponseV2>()),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2,
            "wrong-kind free must preserve the real session owner"
        );
        assert_eq!(session_cancel(session), R2SLEIGH_STATUS_OK_V2);

        let retained =
            registered_session(session).expect("active call retains the session allocation");
        assert_eq!(session_free(session), R2SLEIGH_STATUS_OK_V2);
        assert_eq!(session_free(session), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert_eq!(session_cancel(session), R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert_eq!(
            session_reset_cancellation(session),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        let mut error = R2SleighByteViewV2 {
            data: ptr::dangling(),
            len: usize::MAX,
        };
        assert_eq!(
            session_error(session, &mut error),
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert!(error.data.is_null());
        assert_eq!(error.len, 0);
        let mut response = ptr::dangling_mut::<R2SleighResponseV2>();
        assert_eq!(
            unsafe { execute(session, ptr::null(), &mut response) },
            R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
        );
        assert!(response.is_null());
        retained
            .cancellation
            .lock()
            .expect("retained cancellation")
            .cancel();

        let mut replacement = ptr::null_mut();
        assert_eq!(
            session_create(&config(), &mut replacement),
            R2SLEIGH_STATUS_OK_V2
        );
        assert_ne!(session, replacement, "retired tokens are never reused");
        assert_eq!(session_free(replacement), R2SLEIGH_STATUS_OK_V2);
    }

    #[test]
    fn session_cancel_is_valid_from_another_thread() {
        let mut session = ptr::null_mut();
        assert_eq!(
            session_create(&config(), &mut session),
            R2SLEIGH_STATUS_OK_V2
        );
        let token = session as usize;
        let status = std::thread::spawn(move || session_cancel(token as *const R2SleighSessionV2))
            .join()
            .expect("cross-thread cancel does not panic");
        assert_eq!(status, R2SLEIGH_STATUS_OK_V2);
        assert_eq!(session_free(session), R2SLEIGH_STATUS_OK_V2);
    }

    #[test]
    fn session_cancel_does_not_wait_for_pinned_lift_handles() {
        let mut session = ptr::null_mut();
        assert_eq!(
            session_create(&config(), &mut session),
            R2SLEIGH_STATUS_OK_V2
        );
        let pinned_lift_handles = lock_lift_registry();
        let token = session as usize;
        let (sender, receiver) = std::sync::mpsc::channel();
        let cancel = std::thread::spawn(move || {
            sender
                .send(session_cancel(token as *const R2SleighSessionV2))
                .expect("cancellation status receiver remains live");
        });
        assert_eq!(
            receiver
                .recv_timeout(Duration::from_secs(1))
                .expect("session cancellation must not share the pinned lift registry"),
            R2SLEIGH_STATUS_OK_V2
        );
        drop(pinned_lift_handles);
        cancel.join().expect("cross-thread cancel does not panic");
        assert_eq!(session_free(session), R2SLEIGH_STATUS_OK_V2);
    }

    #[test]
    fn radare_return_mechanism_wire_layout_matches_source_append() {
        assert_eq!(
            size_of::<R2SleighRadareReturnMechanismViewV2>(),
            size_of::<r2source::RadareAbi138ReturnMechanismView>()
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareReturnMechanismViewV2, kind),
            std::mem::offset_of!(r2source::RadareAbi138ReturnMechanismView, kind)
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareReturnMechanismViewV2, stack_offset),
            std::mem::offset_of!(r2source::RadareAbi138ReturnMechanismView, stack_offset)
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareReturnMechanismViewV2, slot_size_bytes),
            std::mem::offset_of!(r2source::RadareAbi138ReturnMechanismView, slot_size_bytes)
        );
        assert_eq!(
            std::mem::offset_of!(
                R2SleighRadareReturnMechanismViewV2,
                stack_pointer_delta_bytes
            ),
            std::mem::offset_of!(
                r2source::RadareAbi138ReturnMechanismView,
                stack_pointer_delta_bytes
            )
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareAccessorsV2, return_mechanism_view),
            std::mem::offset_of!(r2source::RadareAbi138Accessors, return_mechanism_view)
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareAccessorsV2, return_mechanism_view),
            std::mem::offset_of!(R2SleighRadareAccessorsV2, external_exit)
                + size_of::<Option<unsafe extern "C" fn(*const c_void, usize, *mut u64) -> u8>>()
        );
    }

    #[test]
    fn api_table_reports_rust_layouts() {
        let api = unsafe { &*r2sleigh_api_v2() };
        assert_eq!(api.abi_version, R2SLEIGH_ABI_V2);
        assert_eq!(api.radare_abi_version, R2SLEIGH_RADARE_ABI_V2);
        assert_eq!(R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2, 8);
        assert_eq!(R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2, 2);
        assert_eq!(api.struct_size as usize, size_of::<R2SleighApiV2>());
        assert_eq!(api.request_size as usize, size_of::<R2SleighRequestV2>());
        assert_eq!(
            api.engine_request_payload_size as usize,
            size_of::<R2SleighEngineRequestPayloadV2>()
        );
        assert_eq!(
            api.function_context_size as usize,
            size_of::<R2SleighFunctionContext>()
        );
        assert_eq!(
            api.context_param_size as usize,
            size_of::<R2SleighContextParam>()
        );
        assert_eq!(
            api.context_var_size as usize,
            size_of::<R2SleighContextVar>()
        );
        assert_eq!(
            api.context_base_member_size as usize,
            size_of::<R2SleighContextBaseMember>()
        );
        assert_eq!(
            api.context_enum_variant_size as usize,
            size_of::<R2SleighContextEnumVariant>()
        );
        assert_eq!(
            api.context_base_type_size as usize,
            size_of::<R2SleighContextBaseType>()
        );
        assert_eq!(
            api.context_callee_size as usize,
            size_of::<R2SleighContextCallee>()
        );
        assert_eq!(
            api.lift_quality_size as usize,
            size_of::<R2SleighLiftQuality>()
        );
        assert_eq!(
            api.interproc_seed_size as usize,
            size_of::<R2SleighInterprocSeed>()
        );
        assert_eq!(
            api.interproc_scope_size as usize,
            size_of::<R2SleighInterprocScope>()
        );
        assert_eq!(
            api.interproc_plan_size as usize,
            size_of::<R2SleighInterprocSessionPlan>()
        );
        assert_eq!(
            api.source_function_interface_size as usize,
            size_of::<R2SleighSourceFunctionInterfaceV2>()
        );
        assert_eq!(
            api.source_parameter_type_size as usize,
            size_of::<R2SleighSourceParameterTypeV2>()
        );
        assert_eq!(
            api.source_carrier_projection_size as usize,
            size_of::<R2SleighSourceCarrierProjectionV2>()
        );
        assert_eq!(
            api.source_type_size as usize,
            size_of::<R2SleighSourceTypeV2>()
        );
        assert_eq!(
            api.source_aggregate_member_size as usize,
            size_of::<R2SleighSourceAggregateMemberV2>()
        );
        assert_eq!(
            api.source_aggregate_layout_size as usize,
            size_of::<R2SleighSourceAggregateLayoutV2>()
        );
        assert_eq!(
            api.source_stack_slot_size as usize,
            size_of::<R2SleighSourceStackSlotV2>()
        );
        assert_eq!(
            api.source_storage_size as usize,
            size_of::<R2SleighSourceStorageV2>()
        );
        assert_eq!(
            api.source_call_argument_size as usize,
            size_of::<R2SleighSourceCallArgumentV2>()
        );
        assert_eq!(
            api.source_call_site_interface_size as usize,
            size_of::<R2SleighSourceCallSiteInterfaceV2>()
        );
        assert_eq!(
            api.phase_timing_size as usize,
            size_of::<R2SleighPhaseTimingV2>()
        );
        assert_eq!(
            api.response_info_size as usize,
            size_of::<R2SleighResponseInfoV2>()
        );
        assert_eq!(
            api.analysis_render_request_size as usize,
            size_of::<R2SleighAnalysisRenderRequestV2>()
        );
        assert_eq!(
            api.scope_render_request_size as usize,
            size_of::<R2SleighScopeRenderRequestV2>()
        );
        assert_eq!(
            api.scope_symbol_size as usize,
            size_of::<R2SleighScopeSymbolV2>()
        );
        assert_eq!(
            api.analysis_query_request_size as usize,
            size_of::<R2SleighAnalysisQueryRequestV2>()
        );
        assert_eq!(
            api.analysis_result_view_size as usize,
            size_of::<R2SleighAnalysisResultViewV2>()
        );
        assert_eq!(
            api.radare_snapshot_input_size as usize,
            size_of::<R2SleighRadareSnapshotInputV2>()
        );
        assert_eq!(
            api.radare_accessors_size as usize,
            size_of::<R2SleighRadareAccessorsV2>()
        );
    }

    #[test]
    fn exact_source_interface_uses_le_revision_and_arch_register_identity() {
        let (arch, disasm) =
            super::super::create_disassembler_for_arch("x86-64").expect("x86-64 disassembler");
        let parameter_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rdi"))
            .expect("rdi register")
            .clone();
        let return_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rax"))
            .expect("rax register")
            .clone();
        let frame_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rbp"))
            .expect("rbp register")
            .clone();
        let stack_pointer_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rsp"))
            .expect("rsp register")
            .clone();
        let return_address_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rip"))
            .expect("rip register")
            .clone();
        let return_address_storage =
            wire_register_storage(return_address_register.offset, return_address_register.size);
        let stack_pointer_storage =
            wire_register_storage(stack_pointer_register.offset, stack_pointer_register.size);
        let parameter_name = parameter_register.name.as_bytes().to_vec();
        let return_name = return_register.name.as_bytes().to_vec();
        let frame_name = frame_register.name.as_bytes().to_vec();
        let stack_pointer_name = stack_pointer_register.name.as_bytes().to_vec();
        let source_frame_offset = frame_register.offset;
        let (base, canonical_frame_storage) = validate_stack_base_against_arch(
            &arch,
            R2SLEIGH_SOURCE_STACK_BASE_BP_V2,
            &frame_register.name,
            source_frame_offset,
            frame_register.size,
        )
        .expect("canonical frame register");
        assert_eq!(base, r2ssa::StackAddressBase::FramePointer);
        assert_eq!(canonical_frame_storage.offset, frame_register.offset);
        let error = validate_stack_base_against_arch(
            &arch,
            R2SLEIGH_SOURCE_STACK_BASE_BP_V2,
            &frame_register.name,
            frame_register.offset + 1,
            frame_register.size,
        )
        .expect_err("mismatched source frame coordinate");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        let ctx = Box::new(R2ILContext::with_arch_and_disasm(arch, disasm));
        let calling_convention = b"sysv";
        let source_parameter_offset = parameter_register.offset;
        let source_return_offset = return_register.offset;
        let parameters = [R2SleighSourceParameterV2 {
            index: 0,
            storage: R2SleighSourceRegisterV2 {
                name: R2SleighStringViewV2 {
                    data: parameter_name.as_ptr(),
                    len: parameter_name.len(),
                },
                offset: source_parameter_offset,
                size: parameter_register.size,
            },
        }];
        let mut stack_slots = [R2SleighSourceStackSlotV2 {
            base_kind: R2SLEIGH_SOURCE_STACK_BASE_BP_V2,
            base: R2SleighSourceRegisterV2 {
                name: R2SleighStringViewV2 {
                    data: frame_name.as_ptr(),
                    len: frame_name.len(),
                },
                offset: source_frame_offset,
                size: frame_register.size,
            },
            offset: -16,
            size: 8,
            role: R2SLEIGH_SOURCE_STACK_ROLE_PARAMETER_HOME_V2,
            parameter_index: 0,
            home_storage: R2SleighSourceRegisterV2 {
                name: R2SleighStringViewV2 {
                    data: parameter_name.as_ptr(),
                    len: parameter_name.len(),
                },
                offset: source_parameter_offset,
                size: parameter_register.size,
            },
        }];
        let mut source = R2SleighSourceFunctionInterfaceV2 {
            schema_version: R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2,
            struct_size: u32_size::<R2SleighSourceFunctionInterfaceV2>(),
            revision_identity: 0x0102_0304_0506_0708,
            function_addr: 0x401000,
            calling_convention: R2SleighStringViewV2 {
                data: calling_convention.as_ptr(),
                len: calling_convention.len(),
            },
            parameters: parameters.as_ptr(),
            num_parameters: parameters.len(),
            stack_slots: stack_slots.as_ptr(),
            num_stack_slots: stack_slots.len(),
            return_kind: R2SLEIGH_SOURCE_RETURN_REGISTER_V2,
            return_storage: R2SleighSourceRegisterV2 {
                name: R2SleighStringViewV2 {
                    data: return_name.as_ptr(),
                    len: return_name.len(),
                },
                offset: source_return_offset,
                size: return_register.size,
            },
            variadic: 0,
            noreturn: 0,
            stack_resources_complete: 1,
            complete: 1,
            call_sites: ptr::null(),
            num_call_sites: 0,
            call_sites_complete: 0,
            parameter_types: ptr::null(),
            num_parameter_types: 0,
            return_type_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
            return_carrier: R2SleighSourceCarrierProjectionV2::default(),
            types: ptr::null(),
            num_types: 0,
            aggregates: ptr::null(),
            num_aggregates: 0,
            exact_types_complete: 0,
            stack_slot_roles_complete: 1,
            return_address_storage,
            stack_pointer_storage,
        };

        source.schema_version = R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2 - 1;
        assert_eq!(
            unsafe {
                source_snapshot_with_new_budget(
                    &source,
                    &*ctx,
                    &[],
                    0x401000,
                    0x0102_0304_0506_0708,
                )
            }
            .expect_err("schema 6 source interface must not retain a compatibility path")
            .status,
            R2SLEIGH_STATUS_ABI_MISMATCH_V2
        );
        source.schema_version = R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2;
        source.struct_size = u32_size::<R2SleighSourceFunctionInterfaceV2>() + 16;
        assert!(
            unsafe {
                source_snapshot_with_new_budget(
                    &source,
                    &*ctx,
                    &[],
                    0x401000,
                    0x0102_0304_0506_0708,
                )
            }
            .is_ok(),
            "a future source struct tail must be accepted"
        );
        source.struct_size = u32_size::<R2SleighSourceFunctionInterfaceV2>() - 1;
        assert_eq!(
            unsafe {
                source_snapshot_with_new_budget(
                    &source,
                    &*ctx,
                    &[],
                    0x401000,
                    0x0102_0304_0506_0708,
                )
            }
            .expect_err("a truncated source struct must fail")
            .status,
            R2SLEIGH_STATUS_ABI_MISMATCH_V2
        );
        source.struct_size = u32_size::<R2SleighSourceFunctionInterfaceV2>();

        let snapshot = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect("valid source payload")
        .expect("exact source snapshot");
        assert_eq!(
            snapshot.revision_identity(),
            &0x0102_0304_0506_0708u64.to_le_bytes()
        );
        let interface = snapshot.function_interface().expect("function interface");
        assert_eq!(interface.parameters().len(), 1);
        assert_eq!(
            interface.parameters()[0].storage().offset,
            parameter_register.offset
        );
        assert!(matches!(
            interface.return_kind(),
            r2ssa::SourceFunctionReturn::Register { storage }
                if storage.offset == return_register.offset
        ));
        assert_eq!(
            interface.return_address_storage(),
            Some(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: return_address_register.offset,
                size: return_address_register.size,
            })
        );
        assert_eq!(
            interface.stack_pointer_storage(),
            Some(r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: stack_pointer_register.offset,
                size: stack_pointer_register.size,
            })
        );
        assert_eq!(interface.stack_slots().len(), 1);
        assert!(interface.stack_slot_roles_complete());
        assert_eq!(
            interface.stack_slots()[0],
            r2ssa::SourceStackSlotSpec::new_parameter_home(
                r2ssa::StackAddressBase::FramePointer,
                canonical_frame_storage,
                -16,
                8,
                0,
                r2ssa::CanonicalStorageId {
                    space: r2ssa::CanonicalStorageSpace::Register,
                    offset: parameter_register.offset,
                    size: parameter_register.size,
                },
            )
        );
        assert!(snapshot.call_site_interfaces().is_empty());

        source.return_address_storage.size = return_address_register.size / 2;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("partial-width return-address storage must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        source.return_address_storage = return_address_storage;

        source.stack_pointer_storage.size = stack_pointer_register.size / 2;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("partial-width stack-pointer storage must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        source.stack_pointer_storage = stack_pointer_storage;

        source.stack_pointer_storage = return_address_storage;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("stack pointer overlapping return-address storage must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        source.stack_pointer_storage = stack_pointer_storage;

        source.stack_pointer_storage =
            wire_register_storage(parameter_register.offset, parameter_register.size);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("stack pointer overlapping a parameter home must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("overlaps parameter-home storage"));
        source.stack_pointer_storage = stack_pointer_storage;

        source.stack_pointer_storage =
            wire_register_storage(return_register.offset, return_register.size);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("stack pointer overlapping a non-void return must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("overlaps non-void return storage"));
        source.stack_pointer_storage = stack_pointer_storage;

        source.stack_pointer_storage =
            wire_register_storage(frame_register.offset, frame_register.size);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("stack pointer overlapping a BP base must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("overlaps BP base storage"));
        source.stack_pointer_storage = stack_pointer_storage;

        stack_slots[0].base_kind = R2SLEIGH_SOURCE_STACK_BASE_SP_V2;
        stack_slots[0].base.name = R2SleighStringViewV2 {
            data: stack_pointer_name.as_ptr(),
            len: stack_pointer_name.len(),
        };
        stack_slots[0].base.offset = stack_pointer_register.offset;
        stack_slots[0].base.size = stack_pointer_register.size;
        unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect("SP stack base exactly equal to the stack-pointer carrier")
        .expect("exact SP source snapshot");
        stack_slots[0].base.name = R2SleighStringViewV2 {
            data: frame_name.as_ptr(),
            len: frame_name.len(),
        };
        stack_slots[0].base.offset = frame_register.offset;
        stack_slots[0].base.size = frame_register.size;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("SP stack base mismatching the stack-pointer carrier must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(
            error
                .message
                .contains("does not exactly match stack-pointer storage")
        );
        stack_slots[0].base_kind = R2SLEIGH_SOURCE_STACK_BASE_BP_V2;
        source.stack_pointer_storage = stack_pointer_storage;

        source.stack_slots = ptr::null();
        source.num_stack_slots = 0;
        source.return_address_storage =
            wire_register_storage(parameter_register.offset, parameter_register.size);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("return-address overlap with a parameter must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("overlaps parameter storage"));
        source.return_address_storage = return_address_storage;
        source.stack_pointer_storage =
            wire_register_storage(parameter_register.offset, parameter_register.size);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("stack-pointer overlap with a parameter must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("overlaps parameter storage"));
        source.stack_pointer_storage = stack_pointer_storage;

        source.stack_slots = stack_slots.as_ptr();
        source.num_stack_slots = stack_slots.len();
        source.return_address_storage =
            wire_register_storage(return_register.offset, return_register.size);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("return-address overlap with a non-void return must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("overlaps non-void return storage"));

        source.return_address_storage =
            wire_register_storage(frame_register.offset, frame_register.size);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("return-address overlap with a stack base must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("overlaps stack base storage"));

        source.return_address_storage =
            wire_register_storage(parameter_register.offset, parameter_register.size);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("return-address overlap with a parameter home must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert!(error.message.contains("overlaps parameter-home storage"));
        source.return_address_storage = return_address_storage;

        stack_slots[0].home_storage.size = 0;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("zero parameter-home storage must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        stack_slots[0].home_storage.size = parameter_register.size;
        stack_slots[0].parameter_index = 1;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("out-of-range parameter-home index must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        stack_slots[0].parameter_index = 0;
        stack_slots[0].home_storage.offset = source_return_offset;
        stack_slots[0].home_storage.size = return_register.size;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("mismatched parameter-home storage must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        stack_slots[0].home_storage.offset = source_parameter_offset;
        stack_slots[0].home_storage.name = R2SleighStringViewV2 {
            data: return_name.as_ptr(),
            len: return_name.len(),
        };
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("mismatched parameter-home register name must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        stack_slots[0].home_storage.name = R2SleighStringViewV2 {
            data: parameter_name.as_ptr(),
            len: parameter_name.len(),
        };
        let mut second_home = stack_slots[0];
        second_home.offset = -32;
        let duplicate_homes = [stack_slots[0], second_home];
        source.stack_slots = duplicate_homes.as_ptr();
        source.num_stack_slots = duplicate_homes.len();
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 0x0102_0304_0506_0708)
        }
        .expect_err("duplicate homes for one parameter must fail closed");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
    }

    #[test]
    fn exact_source_stack_slots_use_explicit_role_and_fail_closed_on_invalid_inputs() {
        let (arch, disasm) =
            super::super::create_disassembler_for_arch("x86-64").expect("x86-64 disassembler");
        let frame_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rbp"))
            .expect("rbp register")
            .clone();
        let return_address_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rip"))
            .expect("rip register")
            .clone();
        let stack_pointer_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rsp"))
            .expect("rsp register")
            .clone();
        let return_address_storage =
            wire_register_storage(return_address_register.offset, return_address_register.size);
        let stack_pointer_storage =
            wire_register_storage(stack_pointer_register.offset, stack_pointer_register.size);
        let frame_name = frame_register.name.as_bytes().to_vec();
        let mut arm_arch = r2il::ArchSpec::new("arm-stack-base-test");
        arm_arch.addr_size = 4;
        arm_arch.add_register(r2il::RegisterDef::new("r13", 52, 4));
        let (base_kind, storage) = validate_stack_base_against_arch(
            &arm_arch,
            R2SLEIGH_SOURCE_STACK_BASE_SP_V2,
            "r13",
            52,
            4,
        )
        .expect("explicit stack role accepts ARM r13 without a spelling whitelist");
        assert_eq!(base_kind, r2ssa::StackAddressBase::StackPointer);
        assert_eq!(storage.offset, 52);
        let error = validate_stack_base_against_arch(&arm_arch, 0, "r13", 52, 4)
            .expect_err("unknown explicit stack role");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        let error = validate_stack_base_against_arch(
            &arch,
            R2SLEIGH_SOURCE_STACK_BASE_BP_V2,
            &frame_register.name,
            0,
            frame_register.size + 1,
        )
        .expect_err("stack base size mismatch");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let ctx = Box::new(R2ILContext::with_arch_and_disasm(arch, disasm));
        let base = R2SleighSourceRegisterV2 {
            name: R2SleighStringViewV2 {
                data: frame_name.as_ptr(),
                len: frame_name.len(),
            },
            offset: 0x7777_0000,
            size: frame_register.size,
        };
        let overlapping = [
            R2SleighSourceStackSlotV2 {
                base_kind: R2SLEIGH_SOURCE_STACK_BASE_BP_V2,
                base,
                offset: -16,
                size: 8,
                role: R2SLEIGH_SOURCE_STACK_ROLE_LOCAL_V2,
                parameter_index: R2SLEIGH_SOURCE_PARAMETER_INDEX_INVALID_V2,
                home_storage: R2SleighSourceRegisterV2 {
                    name: R2SleighStringViewV2 {
                        data: ptr::null(),
                        len: 0,
                    },
                    offset: 0,
                    size: 0,
                },
            },
            R2SleighSourceStackSlotV2 {
                base_kind: R2SLEIGH_SOURCE_STACK_BASE_BP_V2,
                base,
                offset: -12,
                size: 8,
                role: R2SLEIGH_SOURCE_STACK_ROLE_LOCAL_V2,
                parameter_index: R2SLEIGH_SOURCE_PARAMETER_INDEX_INVALID_V2,
                home_storage: R2SleighSourceRegisterV2 {
                    name: R2SleighStringViewV2 {
                        data: ptr::null(),
                        len: 0,
                    },
                    offset: 0,
                    size: 0,
                },
            },
        ];
        let source = void_source_interface(
            b"sysv",
            &overlapping,
            return_address_storage,
            stack_pointer_storage,
        );
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("overlapping source stack slots");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let duplicate = [overlapping[0], overlapping[0]];
        let source = void_source_interface(
            b"sysv",
            &duplicate,
            return_address_storage,
            stack_pointer_storage,
        );
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("duplicate source stack slots");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let exact = [overlapping[0]];
        let mut source = void_source_interface(
            b"sysv",
            &exact,
            return_address_storage,
            stack_pointer_storage,
        );
        source.stack_resources_complete = 0;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("incomplete source stack resource set");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        source.stack_resources_complete = 2;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("non-boolean source stack resource completeness");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        source.stack_resources_complete = 1;
        source.stack_slot_roles_complete = 0;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("incomplete source stack-slot roles");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        source.stack_slot_roles_complete = 1;
        source.call_sites_complete = 2;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("non-boolean source callsite completeness");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        source.call_sites_complete = 0;
        let mut malformed_local = exact[0];
        malformed_local.parameter_index = 0;
        source.stack_slots = &malformed_local;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("local carrying parameter-home authority");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        malformed_local.parameter_index = R2SLEIGH_SOURCE_PARAMETER_INDEX_INVALID_V2;
        malformed_local.home_storage.name = R2SleighStringViewV2 {
            data: frame_name.as_ptr(),
            len: frame_name.len(),
        };
        source.stack_slots = &malformed_local;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("local carrying a nonempty home register name");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        malformed_local.home_storage.name = R2SleighStringViewV2 {
            data: ptr::null(),
            len: 0,
        };
        malformed_local.home_storage.offset = frame_register.offset;
        malformed_local.home_storage.size = frame_register.size;
        source.stack_slots = &malformed_local;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("local carrying nonzero home storage");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let mut malformed_home_name = exact[0];
        malformed_home_name.home_storage.name = R2SleighStringViewV2 {
            data: ptr::null(),
            len: 1,
        };
        source.stack_slots = &malformed_home_name;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("cosmetic home name still rejects a null/nonzero pointer-length pair");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let mut zero_home = exact[0];
        zero_home.role = R2SLEIGH_SOURCE_STACK_ROLE_PARAMETER_HOME_V2;
        zero_home.parameter_index = 0;
        source.stack_slots = &zero_home;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("home with zero canonical storage");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
    }

    #[test]
    fn exact_source_interface_rejects_zero_stale_and_cross_function_identity() {
        let (arch, disasm) =
            super::super::create_disassembler_for_arch("x86-64").expect("x86-64 disassembler");
        let return_address_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rip"))
            .expect("rip register")
            .clone();
        let stack_pointer_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rsp"))
            .expect("rsp register")
            .clone();
        let return_address_storage =
            wire_register_storage(return_address_register.offset, return_address_register.size);
        let stack_pointer_storage =
            wire_register_storage(stack_pointer_register.offset, stack_pointer_register.size);
        let ctx = Box::new(R2ILContext::with_arch_and_disasm(arch, disasm));
        let mut source =
            void_source_interface(b"sysv", &[], return_address_storage, stack_pointer_storage);

        source.revision_identity = 0;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 1) }
            .expect_err("zero source revision");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        source.revision_identity = 1;
        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401000, 2) }
            .expect_err("stale source revision");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let error = unsafe { source_snapshot_with_new_budget(&source, &*ctx, &[], 0x401008, 1) }
            .expect_err("cross-function source identity");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
    }

    #[test]
    fn exact_v2_synthetic_callsite_stays_residual_and_rejects_bad_identity() {
        let mut arch = r2il::ArchSpec::new("v2-direct-call-return-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(r2il::Endianness::Little);
        arch.add_register(r2il::RegisterDef::new("rax", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rdi", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        arch.add_register(r2il::RegisterDef::new("rsp", 24, 8));
        let (_, disasm) = super::super::create_disassembler_for_arch("x86-64")
            .expect("x86-64 disassembler for context view");
        let parameter_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rdi"))
            .expect("rdi register")
            .clone();
        let return_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rax"))
            .expect("rax register")
            .clone();
        let instruction_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rip"))
            .expect("rip register")
            .clone();
        let stack_pointer_register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rsp"))
            .expect("rsp register")
            .clone();
        let engine_arch = arch.clone();
        let ctx = Box::new(R2ILContext::with_arch_and_disasm(arch, disasm));
        let parameter_name = parameter_register.name.as_bytes();
        let return_name = return_register.name.as_bytes();
        let caller_callconv = b"caller-test-abi";
        let callee_callconv = b"callee-test-abi";
        let revision = 0x8899_aabb_ccdd_eeff;
        let raw_call_addr = 0x7502;
        let target_addr = 0x8600;
        let parameters = [R2SleighSourceParameterV2 {
            index: 0,
            storage: R2SleighSourceRegisterV2 {
                name: R2SleighStringViewV2 {
                    data: parameter_name.as_ptr(),
                    len: parameter_name.len(),
                },
                offset: parameter_register.offset,
                size: parameter_register.size,
            },
        }];
        let call_arguments = [R2SleighSourceCallArgumentV2 {
            index: 0,
            storage: parameters[0].storage,
        }];
        let mut call_site = R2SleighSourceCallSiteInterfaceV2 {
            schema_version: R2SLEIGH_SOURCE_CALL_SITE_SCHEMA_V2,
            struct_size: u32_size::<R2SleighSourceCallSiteInterfaceV2>(),
            revision_identity: revision,
            caller_function_addr: 0x7500,
            raw_instruction_addr: raw_call_addr,
            raw_target_addr: target_addr,
            block_addr: 0x7500,
            op_index: 1,
            target: R2SleighSourceStorageV2 {
                space: R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2,
                custom_space: 0,
                offset: target_addr,
                size: 8,
            },
            calling_convention: R2SleighStringViewV2 {
                data: callee_callconv.as_ptr(),
                len: callee_callconv.len(),
            },
            arguments: call_arguments.as_ptr(),
            num_arguments: call_arguments.len(),
            result_kind: R2SLEIGH_SOURCE_RETURN_VOID_V2,
            result_storage: R2SleighSourceRegisterV2 {
                name: R2SleighStringViewV2 {
                    data: ptr::null(),
                    len: 0,
                },
                offset: 0,
                size: 0,
            },
            variadic: 0,
            noreturn: 0,
            complete: 1,
        };
        let mut source = R2SleighSourceFunctionInterfaceV2 {
            schema_version: R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2,
            struct_size: u32_size::<R2SleighSourceFunctionInterfaceV2>(),
            revision_identity: revision,
            function_addr: 0x7500,
            calling_convention: R2SleighStringViewV2 {
                data: caller_callconv.as_ptr(),
                len: caller_callconv.len(),
            },
            parameters: parameters.as_ptr(),
            num_parameters: parameters.len(),
            stack_slots: ptr::null(),
            num_stack_slots: 0,
            return_kind: R2SLEIGH_SOURCE_RETURN_REGISTER_V2,
            return_storage: R2SleighSourceRegisterV2 {
                name: R2SleighStringViewV2 {
                    data: return_name.as_ptr(),
                    len: return_name.len(),
                },
                offset: return_register.offset,
                size: return_register.size,
            },
            variadic: 0,
            noreturn: 0,
            stack_resources_complete: 1,
            complete: 1,
            call_sites: &call_site,
            num_call_sites: 1,
            call_sites_complete: 1,
            parameter_types: ptr::null(),
            num_parameter_types: 0,
            return_type_id: R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
            return_carrier: R2SleighSourceCarrierProjectionV2::default(),
            types: ptr::null(),
            num_types: 0,
            aggregates: ptr::null(),
            num_aggregates: 0,
            exact_types_complete: 0,
            stack_slot_roles_complete: 1,
            return_address_storage: wire_register_storage(
                instruction_register.offset,
                instruction_register.size,
            ),
            stack_pointer_storage: wire_register_storage(
                stack_pointer_register.offset,
                stack_pointer_register.size,
            ),
        };
        let mut call = R2ILBlock::new(0x7500, 4);
        call.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(parameter_register.offset, parameter_register.size),
            src: r2il::Varnode::constant(0x11, parameter_register.size),
        });
        call.push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(target_addr, 8),
        });
        let call_metadata = r2il::OpMetadata {
            instruction_addr: Some(raw_call_addr),
            ..Default::default()
        };
        call.set_op_metadata(1, call_metadata);
        let mut mapped = super::super::R2ILDirectCallIdentity {
            op_index: 0,
            target_space: 0,
            target_custom_space: 0,
            target_offset: 0,
            target_size: 0,
        };
        assert_eq!(
            super::super::r2il_block_direct_call_identity(
                &call,
                raw_call_addr,
                target_addr,
                &mut mapped,
            ),
            1
        );
        assert_eq!(mapped.op_index, 1);
        assert_eq!(mapped.target_space, R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2);
        assert_eq!(mapped.target_offset, target_addr);
        let mut returned = R2ILBlock::new(0x7504, 4);
        returned.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(return_register.offset, return_register.size),
            src: r2il::Varnode::constant(7, return_register.size),
        });
        returned.push(r2il::R2ILOp::Return {
            target: r2il::Varnode::register(instruction_register.offset, instruction_register.size),
        });
        let blocks = vec![call, returned];
        let block_ptrs = blocks
            .iter()
            .map(|block| block as *const R2ILBlock)
            .collect::<Vec<_>>();
        let snapshot = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect("valid exact V2 callsite")
        .expect("V2 source snapshot");
        assert_eq!(snapshot.call_site_interfaces().len(), 1);
        let response = r2engine::EngineSession::new(4).decompile_function_from_input(
            r2engine::EngineFunctionDecompileRequestInput::single_function(
                r2engine::EngineFunctionInput {
                    function_name: "sym.v2_direct_call_return".to_string(),
                    function_addr: 0x7500,
                    blocks: blocks.clone(),
                    arch: Some(engine_arch.clone()),
                    source_snapshot: Some(snapshot),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
                0,
            ),
        );
        assert!(response.diagnostics.semantic_kernel_render.is_none());
        assert!(
            response.output.contains("r2dec residual"),
            "a fabricated call graph cannot grant CertifiedC authority: {}",
            response.output
        );

        call_site.complete = 2;
        source.call_sites = ptr::from_ref(&call_site);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect_err("non-boolean callsite completeness");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        call_site.complete = 1;
        call_site.variadic = 2;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect_err("non-boolean callsite variadic flag");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        call_site.variadic = 0;
        call_site.noreturn = 2;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect_err("non-boolean callsite noreturn flag");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        call_site.noreturn = 0;

        call_site.complete = 0;
        source.call_sites = ptr::from_ref(&call_site);
        let incomplete = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect("structurally valid incomplete callsite")
        .expect("incomplete source snapshot");
        let refused = r2engine::EngineSession::new(4).decompile_function_from_input(
            r2engine::EngineFunctionDecompileRequestInput::single_function(
                r2engine::EngineFunctionInput {
                    function_name: "sym.v2_direct_call_return".to_string(),
                    function_addr: 0x7500,
                    blocks: blocks.clone(),
                    arch: Some(engine_arch.clone()),
                    source_snapshot: Some(incomplete),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
                0,
            ),
        );
        assert!(refused.diagnostics.semantic_kernel_render.is_none());
        call_site.complete = 1;
        call_site.result_kind = R2SLEIGH_SOURCE_RETURN_REGISTER_V2;
        call_site.result_storage = R2SleighSourceRegisterV2 {
            name: R2SleighStringViewV2 {
                data: return_name.as_ptr(),
                len: return_name.len(),
            },
            offset: return_register.offset,
            size: return_register.size,
        };
        source.call_sites = ptr::from_ref(&call_site);
        let nonvoid = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect("structurally valid nonvoid callsite")
        .expect("nonvoid source snapshot");
        assert!(matches!(
            nonvoid.call_site_interfaces()[0].result(),
            r2ssa::SourceCallResult::Register { .. }
        ));
        let refused = r2engine::EngineSession::new(4).decompile_function_from_input(
            r2engine::EngineFunctionDecompileRequestInput::single_function(
                r2engine::EngineFunctionInput {
                    function_name: "sym.v2_direct_call_return".to_string(),
                    function_addr: 0x7500,
                    blocks: blocks.clone(),
                    arch: Some(engine_arch),
                    source_snapshot: Some(nonvoid),
                    semantic_metadata_enabled: true,
                },
                Some(64),
                r2types::ParsedExternalContext::default(),
                0,
            ),
        );
        assert!(
            refused.diagnostics.semantic_kernel_render.is_none(),
            "nonvoid call results remain residual"
        );
        call_site.result_kind = R2SLEIGH_SOURCE_RETURN_VOID_V2;
        call_site.result_storage = R2SleighSourceRegisterV2 {
            name: R2SleighStringViewV2 {
                data: ptr::null(),
                len: 0,
            },
            offset: 0,
            size: 0,
        };

        call_site.revision_identity = revision.wrapping_add(1);
        source.call_sites = ptr::from_ref(&call_site);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect_err("stale callsite revision");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        call_site.revision_identity = revision;
        call_site.caller_function_addr = 0x7510;
        source.call_sites = ptr::from_ref(&call_site);
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect_err("cross-function callsite identity");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        call_site.caller_function_addr = 0x7500;
        source.call_sites = ptr::from_ref(&call_site);

        let mut ambiguous_blocks = blocks.clone();
        ambiguous_blocks[0].push(r2il::R2ILOp::Call {
            target: r2il::Varnode::constant(target_addr, 8),
        });
        let duplicate_metadata = r2il::OpMetadata {
            instruction_addr: Some(raw_call_addr),
            ..Default::default()
        };
        ambiguous_blocks[0].set_op_metadata(2, duplicate_metadata);
        let ambiguous_ptrs = ambiguous_blocks
            .iter()
            .map(|block| block as *const R2ILBlock)
            .collect::<Vec<_>>();
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &ambiguous_ptrs, 0x7500, revision)
        }
        .expect_err("ambiguous lifted callsite mapping");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        source.call_sites_complete = 0;
        let error = unsafe {
            source_snapshot_with_new_budget(&source, &*ctx, &block_ptrs, 0x7500, revision)
        }
        .expect_err("partial callsite transport");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
    }

    #[test]
    fn exact_source_register_rejects_mismatched_name_or_size() {
        let (arch, _) =
            super::super::create_disassembler_for_arch("x86-64").expect("x86-64 disassembler");
        let register = arch
            .registers
            .iter()
            .find(|register| register.name.eq_ignore_ascii_case("rdi"))
            .expect("rdi register");

        let error = validate_register_against_arch(
            &arch,
            "not_an_arch_register",
            register.offset,
            register.size,
        )
        .expect_err("unknown register name");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let error = validate_register_against_arch(
            &arch,
            &register.name,
            register.offset,
            register.size + 1,
        )
        .expect_err("register size mismatch");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let error = validate_register_against_arch(
            &arch,
            &register.name,
            register.offset + 1,
            register.size,
        )
        .expect_err("register offset mismatch");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);

        let error = validate_register_against_arch(&arch, &register.name, u64::MAX, register.size)
            .expect_err("source register coordinate overflow");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
    }

    #[test]
    fn exact_source_register_requires_unique_case_insensitive_name() {
        let mut arch = r2il::ArchSpec::new("duplicate-register-test");
        arch.add_register(r2il::RegisterDef::new("ARG0", 0x10, 8));
        arch.add_register(r2il::RegisterDef::new("arg0", 0x20, 8));

        let error = validate_register_against_arch(&arch, "Arg0", 0x30, 8)
            .expect_err("case-insensitive register identity must be unique");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
    }

    #[test]
    fn return_address_storage_requires_exact_full_width_register_coordinates() {
        let mut arch = r2il::ArchSpec::new("return-address-storage-test");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("pc", 0x20, 8));
        arch.add_register(r2il::RegisterDef::sub("pc_low", 0x20, 4, "pc"));

        let exact = wire_register_storage(0x20, 8);
        assert_eq!(
            validate_full_width_register_storage_against_arch(&arch, exact, "return address")
                .expect("exact return-address coordinate"),
            r2ssa::CanonicalStorageId {
                space: r2ssa::CanonicalStorageSpace::Register,
                offset: 0x20,
                size: 8,
            }
        );

        for malformed in [
            R2SleighSourceStorageV2 {
                space: R2SLEIGH_SOURCE_STORAGE_RAM_V2,
                ..exact
            },
            R2SleighSourceStorageV2 { size: 4, ..exact },
            R2SleighSourceStorageV2 {
                offset: 0x28,
                ..exact
            },
            R2SleighSourceStorageV2 {
                custom_space: 1,
                ..exact
            },
        ] {
            let error = validate_full_width_register_storage_against_arch(
                &arch,
                malformed,
                "return address",
            )
            .expect_err("malformed return-address storage");
            assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        }
    }

    fn exact_aarch64_projection_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(r2il::RegisterDef::new("x0", 0, 8));
        arch.add_register(r2il::RegisterDef::sub("w0", 0, 4, "x0"));
        arch.add_register(r2il::RegisterDef::new("x1", 8, 8));
        arch.add_register(r2il::RegisterDef::sub("w1", 8, 4, "x1"));
        arch.add_register(r2il::RegisterDef::new("x2", 16, 8));
        arch
    }

    fn exact_x86_64_projection_arch() -> r2il::ArchSpec {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.addr_size = 8;
        for (name, offset) in [
            ("rdi", 0),
            ("rsi", 8),
            ("rdx", 16),
            ("rcx", 24),
            ("r8", 32),
            ("r9", 40),
            ("rax", 48),
        ] {
            arch.add_register(r2il::RegisterDef::new(name, offset, 8));
        }
        arch.add_register(r2il::RegisterDef::sub("edi", 0, 4, "rdi"));
        arch.add_register(r2il::RegisterDef::sub("esi", 8, 4, "rsi"));
        arch.add_register(r2il::RegisterDef::sub("eax", 48, 4, "rax"));
        arch
    }

    fn register_storage(offset: u64, size: u32) -> r2ssa::CanonicalStorageId {
        r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    #[test]
    fn physical_arm64_projects_only_the_exact_supported_aapcs64_carriers() {
        let arch = exact_aarch64_projection_arch();
        let x0 = register_storage(0, 8);
        let x1 = register_storage(8, 8);
        assert_eq!(
            project_semantic_calling_convention("arm64", &arch, &[x0, x1], Some(x0)),
            "aapcs64"
        );
        assert_eq!(
            project_semantic_calling_convention("ARM64", &arch, &[x0, x1], Some(x0)),
            "aapcs64"
        );

        let x2 = register_storage(16, 8);
        let w0 = register_storage(0, 4);
        let w1 = register_storage(8, 4);
        for (parameters, result) in [
            (vec![x0, x2], Some(x0)),
            (vec![x1, x0], Some(x0)),
            (vec![w0, w1], Some(x0)),
            (vec![x0, x1], None),
            (vec![x0, x1], Some(x1)),
        ] {
            assert_eq!(
                project_semantic_calling_convention("arm64", &arch, &parameters, result),
                "arm64"
            );
        }

        let mut wrong_arch = arch.clone();
        wrong_arch.name = "arm64-looking".to_owned();
        assert_eq!(
            project_semantic_calling_convention("arm64", &wrong_arch, &[x0, x1], Some(x0)),
            "arm64"
        );
        let mut wrong_width = arch.clone();
        wrong_width.addr_size = 4;
        assert_eq!(
            project_semantic_calling_convention("arm64", &wrong_width, &[x0, x1], Some(x0)),
            "arm64"
        );
        let mut duplicate = arch.clone();
        duplicate.add_register(r2il::RegisterDef::new("X0", 32, 8));
        assert_eq!(
            project_semantic_calling_convention("arm64", &duplicate, &[x0, x1], Some(x0)),
            "arm64"
        );
        let no_register_evidence = r2il::ArchSpec::new("aarch64");
        assert_eq!(
            project_semantic_calling_convention(
                "arm64",
                &no_register_evidence,
                &[x0, x1],
                Some(x0),
            ),
            "arm64"
        );
    }

    #[test]
    fn physical_amd64_projects_only_exact_sysv_integer_carriers() {
        let arch = exact_x86_64_projection_arch();
        let rdi = register_storage(0, 8);
        let rsi = register_storage(8, 8);
        let rdx = register_storage(16, 8);
        let rax = register_storage(48, 8);
        for parameters in [vec![rdi], vec![rdi, rsi], vec![rdi, rsi, rdx]] {
            assert_eq!(
                project_semantic_calling_convention("amd64", &arch, &parameters, Some(rax)),
                "sysv_amd64"
            );
        }
        for (parameters, result) in [
            (vec![rsi], Some(rax)),
            (vec![rsi, rdi], Some(rax)),
            (vec![register_storage(0, 4)], Some(rax)),
            (vec![rdi], None),
            (vec![rdi], Some(rdi)),
        ] {
            assert_eq!(
                project_semantic_calling_convention("amd64", &arch, &parameters, result),
                "amd64"
            );
        }
        let mut duplicate = arch.clone();
        duplicate.add_register(r2il::RegisterDef::new("RDI", 64, 8));
        assert_eq!(
            project_semantic_calling_convention("amd64", &duplicate, &[rdi], Some(rax)),
            "amd64"
        );
        let no_register_evidence = r2il::ArchSpec::new("x86-64");
        assert_eq!(
            project_semantic_calling_convention("amd64", &no_register_evidence, &[rdi], Some(rax),),
            "amd64"
        );
    }
}
