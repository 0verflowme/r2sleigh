//! Versioned, panic-contained production boundary for engine requests.
//!
//! V2 exposes the lift core plus decompilation and function typing. Engine
//! requests require one immutable, versioned radare snapshot.

use super::{R2ILBlock, R2ILContext};
use std::cell::RefCell;
use std::collections::BTreeMap;
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
pub const R2SLEIGH_CAP_RESPONSE_INFO_V2: u64 = 1 << 5;
pub const R2SLEIGH_CAP_EXECUTION_CONTROL_V2: u64 = 1 << 6;
pub const R2SLEIGH_CAP_LIFT_CORE_V2: u64 = 1 << 9;
pub const R2SLEIGH_CAP_PLANNER_QUERY_V2: u64 = 1 << 10;
pub const R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2: u64 = 1 << 11;
pub const R2SLEIGH_CAPABILITIES_V2: u64 = R2SLEIGH_CAP_DECOMPILE_V2
    | R2SLEIGH_CAP_TYPE_FUNCTION_V2
    | R2SLEIGH_CAP_RESPONSE_INFO_V2
    | R2SLEIGH_CAP_EXECUTION_CONTROL_V2
    | R2SLEIGH_CAP_LIFT_CORE_V2
    | R2SLEIGH_CAP_PLANNER_QUERY_V2
    | R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2;
pub const R2SLEIGH_RADARE_ABI_V2: u32 = 138;
pub const R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2: u32 = 10;
pub const R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2: u32 = 4;

pub const R2SLEIGH_STATUS_OK_V2: u32 = 0;
pub const R2SLEIGH_STATUS_INVALID_ARGUMENT_V2: u32 = 1;
pub const R2SLEIGH_STATUS_ABI_MISMATCH_V2: u32 = 2;
pub const R2SLEIGH_STATUS_UNSUPPORTED_V2: u32 = 3;
pub const R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2: u32 = 4;
pub const R2SLEIGH_STATUS_ENGINE_ERROR_V2: u32 = 5;
pub const R2SLEIGH_STATUS_PANIC_V2: u32 = 6;

pub const R2SLEIGH_REQUEST_DECOMPILE_V2: u32 = 1;
pub const R2SLEIGH_REQUEST_TYPE_FUNCTION_V2: u32 = 2;
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
pub const R2SLEIGH_SOURCE_STORAGE_RAM_V2: u32 = 1;
pub const R2SLEIGH_SOURCE_STORAGE_REGISTER_V2: u32 = 2;
pub const R2SLEIGH_SOURCE_STORAGE_UNIQUE_V2: u32 = 3;
pub const R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2: u32 = 4;
pub const R2SLEIGH_SOURCE_STORAGE_CUSTOM_V2: u32 = 5;
pub const R2SLEIGH_MAX_FUNCTION_BLOCKS_V2: usize = 200;
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
pub const R2SLEIGH_QUERY_BLOCK_VALUES_V2: u32 = 1;
pub const R2SLEIGH_QUERY_TAINT_SUMMARY_V2: u32 = 2;
pub const R2SLEIGH_QUERY_ANNOTATIONS_V2: u32 = 3;
pub const R2SLEIGH_QUERY_RECOVERED_VARS_V2: u32 = 7;
pub const R2SLEIGH_QUERY_DATA_REFS_V2: u32 = 8;
pub const R2SLEIGH_DATA_REF_SCHEMA_V2: u32 = 1;
pub const R2SLEIGH_PLANNER_QUERY_SCHEMA_V2: u32 = 1;
pub const R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2: u32 = 1;
pub const R2SLEIGH_PLANNER_POST_ANALYSIS_V2: u32 = 2;
pub const R2SLEIGH_PLANNER_AUTO_CALLBACK_V2: u32 = 3;
pub const R2SLEIGH_MODE_FAST_V2: u32 = 0;
pub const R2SLEIGH_MODE_BALANCED_V2: u32 = 1;
pub const R2SLEIGH_MODE_FULL_V2: u32 = 2;
pub const R2SLEIGH_TYPE_WRITEBACK_OFF_V2: u32 = 0;
pub const R2SLEIGH_TYPE_WRITEBACK_BALANCED_V2: u32 = 1;
pub const R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE_V2: u32 = 2;
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
#[allow(dead_code)] // Exported for the C-side pre-lift byte budget.
pub const R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2: usize = 16 << 20;
pub const R2SLEIGH_MAX_STRING_BYTES_V2: usize = 1 << 20;

const REQUEST_FLAG_TEST_PANIC: u32 = 1 << 31;
const MAX_RESPONSE_BYTES: usize = 64 << 20;

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

/// Versioned request envelope. `payload` points to one opaque-snapshot
/// R2SleighEngineRequestPayloadV2 whose operation is selected by `kind`; it is
/// borrowed only for the duration of execute.
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
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct R2SleighRadareStackAllocationContractViewV2 {
    pub growth: i32,
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
    pub frame_pointer_storage_view:
        Option<unsafe extern "C" fn(*const c_void, *mut R2SleighRadareRegisterStorageViewV2) -> u8>,
    pub stack_allocation_contract_view: Option<
        unsafe extern "C" fn(*const c_void, *mut R2SleighRadareStackAllocationContractViewV2) -> u8,
    >,
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
assert_wire_layout!(
    R2SleighRadareStackAllocationContractViewV2,
    r2source::RadareAbi138StackAllocationContractView
);
assert_wire_layout!(R2SleighRadareAccessorsV2, r2source::RadareAbi138Accessors);
const _: [(); R2SLEIGH_RADARE_ABI_V2 as usize] = [(); r2source::RADARE_ABI_VERSION as usize];
const _: [(); R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2 as usize] =
    [(); r2source::RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION as usize];
const _: [(); R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2 as usize] =
    [(); r2source::RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION as usize];

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

/// Versioned scalar planner query. The selected `kind` determines which input
/// fields are read.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct R2SleighPlannerQueryRequestV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    pub schema_version: u32,
    pub kind: u32,
    pub depth: u32,
    pub callback_kind: u32,
    pub function_count: usize,
    pub basic_block_count: usize,
    pub cost: u32,
    pub linear_size: u64,
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
}

/// Opaque-snapshot engine request shared by decompile and type-function.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighEngineRequestPayloadV2 {
    pub abi_version: u32,
    pub struct_size: u32,
    /// Relative request deadline. Zero disables the deadline.
    pub timeout_us: u64,
    /// Required opaque certifying source.
    pub radare_snapshot: *const R2SleighRadareSnapshotInputV2,
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

/// One bounded structured-analysis request over registry-owned lift handles.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct R2SleighAnalysisQueryRequestV2 {
    pub kind: u32,
    pub context: *const R2ILContext,
    pub blocks: *const *const R2ILBlock,
    pub num_blocks: usize,
    pub function_addr: u64,
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
    pub byte_view_size: u32,
    pub string_view_size: u32,
    pub phase_timing_size: u32,
    pub response_info_size: u32,
    pub switch_case_size: u32,
    pub direct_call_identity_size: u32,
    pub analysis_render_request_size: u32,
    pub analysis_query_request_size: u32,
    pub analysis_result_view_size: u32,
    pub data_ref_size: u32,
    pub data_ref_schema_version: u32,
    pub planner_query_request_size: u32,
    pub planner_query_response_size: u32,
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
}

#[derive(Debug)]
struct BoundaryError {
    status: u32,
    message: String,
}

#[derive(Debug)]
struct ExecutedRequest {
    output: super::EngineV2Output,
    request_kind: u32,
    ffi_conversion_elapsed_us: u64,
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
    string_bytes: usize,
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

    fn charge_string_bytes(&mut self, bytes: usize, label: &str) -> Result<(), BoundaryError> {
        Self::charge(
            &mut self.string_bytes,
            bytes,
            R2SLEIGH_MAX_STRING_BYTES_V2,
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

fn elapsed_us(started: Instant) -> u64 {
    started.elapsed().as_micros().min(u128::from(u64::MAX)) as u64
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
    if payload.radare_snapshot.is_null() {
        return Err(BoundaryError::invalid(
            "engine request requires an opaque radare snapshot",
        ));
    }
    if !matches!(
        request.kind,
        R2SLEIGH_REQUEST_DECOMPILE_V2 | R2SLEIGH_REQUEST_TYPE_FUNCTION_V2
    ) {
        return Err(BoundaryError::unsupported("unsupported request kind"));
    }
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
        _ => unreachable!("request kind validated above"),
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

fn planner_query_inactive_fields_are_zero(request: &R2SleighPlannerQueryRequestV2) -> bool {
    let no_callback = request.callback_kind == 0;
    let no_function_count = request.function_count == 0;
    let no_metrics = request.basic_block_count == 0 && request.cost == 0;
    let no_linear_size = request.linear_size == 0;

    match request.kind {
        R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2 => {
            no_callback && no_function_count && no_metrics && no_linear_size
        }
        R2SLEIGH_PLANNER_POST_ANALYSIS_V2 => no_callback && no_metrics && no_linear_size,
        R2SLEIGH_PLANNER_AUTO_CALLBACK_V2 => no_function_count,
        _ => false,
    }
}

fn planner_query_impl(
    request: &R2SleighPlannerQueryRequestV2,
) -> Result<R2SleighPlannerQueryResponseV2, BoundaryError> {
    if !matches!(
        request.kind,
        R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2
            | R2SLEIGH_PLANNER_POST_ANALYSIS_V2
            | R2SLEIGH_PLANNER_AUTO_CALLBACK_V2
    ) {
        return Err(BoundaryError::invalid("planner query kind is invalid"));
    }
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
        _ => unreachable!("planner query kind validated above"),
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

static API_V2: R2SleighApiV2 = R2SleighApiV2 {
    abi_version: R2SLEIGH_ABI_V2,
    struct_size: size_of::<R2SleighApiV2>() as u32,
    capabilities: R2SLEIGH_CAPABILITIES_V2,
    radare_abi_version: R2SLEIGH_RADARE_ABI_V2,
    session_config_size: size_of::<R2SleighSessionConfigV2>() as u32,
    request_size: size_of::<R2SleighRequestV2>() as u32,
    engine_request_payload_size: size_of::<R2SleighEngineRequestPayloadV2>() as u32,
    byte_view_size: size_of::<R2SleighByteViewV2>() as u32,
    string_view_size: size_of::<R2SleighStringViewV2>() as u32,
    phase_timing_size: size_of::<R2SleighPhaseTimingV2>() as u32,
    response_info_size: size_of::<R2SleighResponseInfoV2>() as u32,
    switch_case_size: size_of::<R2SleighSwitchCaseV2>() as u32,
    direct_call_identity_size: size_of::<R2SleighDirectCallIdentityV2>() as u32,
    analysis_render_request_size: size_of::<R2SleighAnalysisRenderRequestV2>() as u32,
    analysis_query_request_size: size_of::<R2SleighAnalysisQueryRequestV2>() as u32,
    analysis_result_view_size: size_of::<R2SleighAnalysisResultViewV2>() as u32,
    data_ref_size: size_of::<super::types::R2SleighDataRef>() as u32,
    data_ref_schema_version: R2SLEIGH_DATA_REF_SCHEMA_V2,
    planner_query_request_size: size_of::<R2SleighPlannerQueryRequestV2>() as u32,
    planner_query_response_size: size_of::<R2SleighPlannerQueryResponseV2>() as u32,
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
    analysis_query,
    analysis_result_view,
    analysis_result_free,
    engine_cache_reset,
    planner_query,
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
        ];
        for request in invalid {
            let (status, response) = planner_query_for(&request);
            assert_eq!(status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
            assert_eq!(response, R2SleighPlannerQueryResponseV2::default());
        }
    }

    #[test]
    fn planner_query_rejects_deleted_raw_kinds_without_output() {
        for kind in [4, 5, 6, 7] {
            let request = planner_request(kind);
            let (status, response) = planner_query_for(&request);
            assert_eq!(status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
            assert_eq!(response, R2SleighPlannerQueryResponseV2::default());
        }
    }

    #[test]
    fn planner_query_rejects_nonzero_inactive_fields_for_every_kind() {
        let invalid = [
            R2SleighPlannerQueryRequestV2 {
                callback_kind: 1,
                ..planner_request(R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                function_count: 1,
                ..planner_request(R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                basic_block_count: 1,
                ..planner_request(R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                cost: 1,
                ..planner_request(R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                linear_size: 1,
                ..planner_request(R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                callback_kind: 1,
                ..planner_request(R2SLEIGH_PLANNER_POST_ANALYSIS_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                basic_block_count: 1,
                ..planner_request(R2SLEIGH_PLANNER_POST_ANALYSIS_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                cost: 1,
                ..planner_request(R2SLEIGH_PLANNER_POST_ANALYSIS_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                linear_size: 1,
                ..planner_request(R2SLEIGH_PLANNER_POST_ANALYSIS_V2)
            },
            R2SleighPlannerQueryRequestV2 {
                function_count: 1,
                callback_kind: R2SLEIGH_AUTO_CALLBACK_ANALYZE_FUNCTION_V2,
                ..planner_request(R2SLEIGH_PLANNER_AUTO_CALLBACK_V2)
            },
        ];
        for request in invalid {
            let (status, response) = planner_query_for(&request);
            assert_eq!(status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
            assert_eq!(response, R2SleighPlannerQueryResponseV2::default());
        }
    }

    #[test]
    fn direct_call_identity_preserves_constant_space_id() {
        let mut block = R2ILBlock::new(0x401000, 5);
        block.push_with_metadata(
            r2il::R2ILOp::Call {
                target: r2il::Varnode::constant(0x402000, 8),
            },
            Some(r2il::OpMetadata {
                instruction_addr: Some(0x401000),
                ..r2il::OpMetadata::default()
            }),
        );
        let mut identity = R2SleighDirectCallIdentityV2::default();
        assert_eq!(
            super::super::r2il_block_direct_call_identity(
                &block,
                0x401000,
                0x402000,
                &mut identity,
            ),
            1
        );
        assert_eq!(identity.op_index, 0);
        assert_eq!(identity.target_space, R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2);
        assert_eq!(identity.target_custom_space, 0);
        assert_eq!(identity.target_offset, 0x402000);
        assert_eq!(identity.target_size, 8);
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
        for deleted_kind in [4, 5, 6] {
            let deleted_request = R2SleighAnalysisQueryRequestV2 {
                kind: deleted_kind,
                ..query_request
            };
            let mut deleted_result = analysis_result;
            assert_eq!(
                (api.analysis_query)(&deleted_request, &mut deleted_result),
                R2SLEIGH_STATUS_UNSUPPORTED_V2,
                "deleted query ID {deleted_kind} must not alias another query"
            );
            assert!(deleted_result.is_null());
        }
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
            4,
        );
    }

    #[test]
    fn generic_semantic_kernel_diagnostics_are_stable_json() {
        assert_semantic_kernel_render_diagnostics(
            r2engine::EngineSemanticKernelRegion::TerminalReturnBlock,
            "terminal_return_block",
            r2dec::CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
        );
    }

    #[test]
    fn every_current_semantic_kernel_region_has_a_stable_identifier() {
        let regions = [
            (
                r2engine::EngineSemanticKernelRegion::TerminalReturnBlock,
                "terminal_return_block",
                r2dec::CERTIFIED_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            ),
            (
                r2engine::EngineSemanticKernelRegion::AggregateMemberTerminalReturnFunction,
                "aggregate_member_terminal_return_function",
                4,
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
        R2SleighEngineRequestPayloadV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighEngineRequestPayloadV2>(),
            timeout_us: 0,
            radare_snapshot: source,
        }
    }

    #[test]
    fn engine_request_requires_opaque_snapshot_before_access() {
        let payload = R2SleighEngineRequestPayloadV2 {
            abi_version: R2SLEIGH_ABI_V2,
            struct_size: u32_size::<R2SleighEngineRequestPayloadV2>(),
            timeout_us: 0,
            radare_snapshot: ptr::null(),
        };
        let error = unsafe {
            execute_request(
                &opaque_request(&payload),
                r2engine::EngineCancellationToken::default(),
            )
        }
        .expect_err("null opaque snapshot");
        assert_eq!(error.status, R2SLEIGH_STATUS_INVALID_ARGUMENT_V2);
        assert_eq!(
            error.message,
            "engine request requires an opaque radare snapshot"
        );
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
    fn opaque_source_rejects_null_handles() {
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
    fn radare_frame_pointer_wire_layout_matches_source_append() {
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareAccessorsV2, frame_pointer_storage_view),
            std::mem::offset_of!(r2source::RadareAbi138Accessors, frame_pointer_storage_view)
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareAccessorsV2, frame_pointer_storage_view),
            std::mem::offset_of!(R2SleighRadareAccessorsV2, return_mechanism_view)
                + size_of::<
                    Option<
                        unsafe extern "C" fn(
                            *const c_void,
                            *mut R2SleighRadareReturnMechanismViewV2,
                        ) -> u8,
                    >,
                >()
        );
    }

    #[test]
    fn radare_stack_allocation_contract_wire_layout_matches_source_append() {
        assert_eq!(
            size_of::<R2SleighRadareStackAllocationContractViewV2>(),
            size_of::<r2source::RadareAbi138StackAllocationContractView>()
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareStackAllocationContractViewV2, growth),
            std::mem::offset_of!(r2source::RadareAbi138StackAllocationContractView, growth)
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareAccessorsV2, stack_allocation_contract_view),
            std::mem::offset_of!(
                r2source::RadareAbi138Accessors,
                stack_allocation_contract_view
            )
        );
        assert_eq!(
            std::mem::offset_of!(R2SleighRadareAccessorsV2, stack_allocation_contract_view),
            std::mem::offset_of!(R2SleighRadareAccessorsV2, frame_pointer_storage_view)
                + size_of::<
                    Option<
                        unsafe extern "C" fn(
                            *const c_void,
                            *mut R2SleighRadareRegisterStorageViewV2,
                        ) -> u8,
                    >,
                >()
        );
    }

    #[test]
    fn api_table_reports_rust_layouts() {
        let api = unsafe { &*r2sleigh_api_v2() };
        assert_eq!(api.abi_version, R2SLEIGH_ABI_V2);
        assert_eq!(api.radare_abi_version, R2SLEIGH_RADARE_ABI_V2);
        assert_eq!(R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2, 10);
        assert_eq!(R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2, 4);
        assert_eq!(api.struct_size as usize, size_of::<R2SleighApiV2>());
        assert_eq!(api.request_size as usize, size_of::<R2SleighRequestV2>());
        assert_eq!(
            api.engine_request_payload_size as usize,
            size_of::<R2SleighEngineRequestPayloadV2>()
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
            api.analysis_query_request_size as usize,
            size_of::<R2SleighAnalysisQueryRequestV2>()
        );
        assert_eq!(
            api.analysis_result_view_size as usize,
            size_of::<R2SleighAnalysisResultViewV2>()
        );
        assert_eq!(
            api.data_ref_size as usize,
            size_of::<super::super::types::R2SleighDataRef>()
        );
        assert_eq!(api.data_ref_schema_version, R2SLEIGH_DATA_REF_SCHEMA_V2);
        assert_ne!(api.data_ref_size, 0);
        assert_ne!(api.data_ref_schema_version, 0);
        assert_eq!(
            api.radare_snapshot_input_size as usize,
            size_of::<R2SleighRadareSnapshotInputV2>()
        );
        assert_eq!(
            api.radare_accessors_size as usize,
            size_of::<R2SleighRadareAccessorsV2>()
        );
    }
}
