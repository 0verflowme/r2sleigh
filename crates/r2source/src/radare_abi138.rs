//! Audited synchronous ingress for radare2 ABI 139 snapshot schema 12.
//!
//! The wire API contains only opaque handles, scalars, and caller-owned output
//! buffers. It deliberately cannot expose radare2 internals or assemble source
//! authority from detached Rust values.

#![allow(unsafe_code)]

use std::ffi::c_void;
use std::mem::size_of;
use std::sync::Arc;

use super::*;

/// Contract identity for the borrowed radare2 function-snapshot transport.
///
/// This is r2sleigh's own number, not radare2's ABI version. Pinning the
/// transport to `R2_ABIVERSION` broke the plugin on every unrelated radare2 ABI
/// bump even when the snapshot API had not moved; support is instead decided by
/// the snapshot capability flag and by this contract plus the snapshot and
/// accessor schema versions, all of which change only when the transport
/// itself changes.
pub const RADARE_SNAPSHOT_CONTRACT_VERSION: u32 = 1;
pub const RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION: u32 = 14;
pub const RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION: u32 = 5;

pub const RADARE_ENDIAN_LITTLE: u32 = 0x4321;
pub const RADARE_ENDIAN_BIG: u32 = 0x1234;

pub const RADARE_CAP_SIGNATURE: u64 = 1 << 0;
pub const RADARE_CAP_REGISTER_ARGS: u64 = 1 << 1;
pub const RADARE_CAP_STACK_SLOTS: u64 = 1 << 2;
pub const RADARE_CAP_CALLEES: u64 = 1 << 3;
pub const RADARE_CAP_TYPES: u64 = 1 << 4;
pub const RADARE_CAP_ASSUMPTIONS: u64 = 1 << 5;
pub const RADARE_CAP_REVISION: u64 = 1 << 6;
pub const RADARE_CAP_EXACT_FUNCTION_INTERFACE: u64 = 1 << 7;
pub const RADARE_CAP_CALL_SITE_INTERFACES: u64 = 1 << 8;
pub const RADARE_CAP_EXACT_CALL_SITE_INTERFACES: u64 = 1 << 9;
pub const RADARE_CAP_EXACT_FUNCTION_TYPES: u64 = 1 << 10;
pub const RADARE_CAP_EXACT_STACK_SLOT_ROLES: u64 = 1 << 11;
pub const RADARE_CAP_RETURN_ADDRESS_STORAGE: u64 = 1 << 12;
pub const RADARE_CAP_STACK_POINTER_STORAGE: u64 = 1 << 13;
pub const RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE: u64 = 1 << 14;
pub const RADARE_CAP_EXACT_RETURN_MECHANISM: u64 = 1 << 15;
pub const RADARE_CAP_EXACT_FRAME_POINTER_STORAGE: u64 = 1 << 16;
pub const RADARE_CAP_EXACT_STACK_ALLOCATION_CONTRACT: u64 = 1 << 17;

const KNOWN_CAPABILITIES: u64 = (1 << 18) - 1;
const INVALID_U64: u64 = u64::MAX;
const INVALID_TYPE_ID: u32 = u32::MAX;

// These bounds are independent of radare2's collection limits. They cap every
// allocation made while the foreign snapshot is borrowed.
const MAX_STRING_BYTES: usize = 1024 * 1024;
const MAX_TOTAL_STRING_BYTES: usize = 16 * 1024 * 1024;
const MAX_BLOCKS: usize = 65_536;
const MAX_BLOCK_BYTES: usize = 16 * 1024 * 1024;
const MAX_FUNCTION_BYTES: usize = 256 * 1024 * 1024;
const MAX_SUCCESSORS: usize = 262_144;
const MAX_EXTERNAL_EXITS: usize = 262_144;
const MAX_PARAMETERS: usize = 4_096;
const MAX_STACK_SLOTS: usize = 65_536;
const MAX_CALLS: usize = 65_536;
const MAX_TOTAL_CALL_ARGUMENTS: usize = 65_536;
const MAX_TYPES: usize = 131_072;
const MAX_AGGREGATES: usize = 4_096;
const MAX_MEMBERS: usize = 65_536;
const MAX_TOTAL_CAPTURE_BYTES: usize = 512 * 1024 * 1024;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct RadareAbi138SnapshotInput {
    pub struct_size: u32,
    pub abi_version: u32,
    pub snapshot_schema_version: u32,
    pub accessor_schema_version: u32,
    pub snapshot: *const c_void,
    pub accessors: *const RadareAbi138Accessors,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RadareAbi138SnapshotView {
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
pub struct RadareAbi138BlockView {
    pub addr: u64,
    pub size: u64,
    pub num_successors: usize,
    pub switch_addr: u64,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138SuccessorView {
    pub kind: i32,
    pub target_addr: u64,
    pub case_value: u64,
    pub external: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RadareAbi138RegisterStorageView {
    pub name_length: usize,
    pub offset: u64,
    pub size: u32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138CarrierProjection {
    pub kind: i32,
    pub offset_bits: u64,
    pub size_bits: u64,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138ParameterView {
    pub index: u32,
    pub name_length: usize,
    pub storage: RadareAbi138RegisterStorageView,
    pub logical_type_id: u32,
    pub carrier: RadareAbi138CarrierProjection,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138FunctionInterfaceView {
    pub calling_convention_length: usize,
    pub num_parameters: usize,
    pub return_kind: i32,
    pub return_storage: RadareAbi138RegisterStorageView,
    pub return_address_storage: RadareAbi138RegisterStorageView,
    pub stack_pointer_storage: RadareAbi138RegisterStorageView,
    pub variadic: u8,
    pub noreturn: u8,
    pub stack_resources_complete: u8,
    pub stack_slot_roles_complete: u8,
    pub complete: u8,
    pub return_type_id: u32,
    pub return_carrier: RadareAbi138CarrierProjection,
    pub logical_types_complete: u8,
    pub stack_pointer_preserved_across_calls: u8,
    pub frame_pointer_preserved_across_calls: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138CallSiteView {
    pub instruction_addr: u64,
    pub target_addr: u64,
    pub calling_convention_length: usize,
    pub num_arguments: usize,
    pub result_kind: i32,
    pub result_storage: RadareAbi138RegisterStorageView,
    pub variadic: u8,
    pub noreturn: u8,
    pub complete: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138TypeGraphView {
    pub num_types: usize,
    pub num_aggregates: usize,
    pub complete: u8,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138TypeView {
    pub id: u32,
    pub kind: i32,
    pub size_bits: u64,
    pub align_bits: u64,
    pub target_type_id: u32,
    pub aggregate_id: u32,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138AggregateView {
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
pub struct RadareAbi138AggregateMemberView {
    pub member_id: u32,
    pub type_id: u32,
    pub offset_bits: u64,
    pub size_bits: u64,
    pub count: usize,
    pub name_length: usize,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138StackSlotView {
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
pub struct RadareAbi138ReturnMechanismView {
    pub kind: i32,
    pub stack_offset: i64,
    pub slot_size_bytes: u32,
    pub stack_pointer_delta_bytes: u32,
}

/// Source-owned callee stack-allocation direction and exact implicit byte
/// ownership beyond the active SP. `growth` is 1 for lower addresses and 2 for
/// higher addresses; zero is reserved for inactive data.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RadareAbi138StackAllocationContractView {
    pub growth: i32,
    pub implicit_active_sp_bytes: u32,
}

pub type RadareSnapshotViewFn =
    unsafe extern "C" fn(*const c_void, *mut RadareAbi138SnapshotView) -> u8;
pub type RadareStringFn = unsafe extern "C" fn(*const c_void, *mut u8, usize) -> u8;
pub type RadareInterfaceViewFn =
    unsafe extern "C" fn(*const c_void, *mut RadareAbi138FunctionInterfaceView) -> u8;
pub type RadareInterfaceStorageNameFn =
    unsafe extern "C" fn(*const c_void, i32, *mut u8, usize) -> u8;
pub type RadareParameterViewFn =
    unsafe extern "C" fn(*const c_void, usize, *mut RadareAbi138ParameterView) -> u8;
pub type RadareIndexedStringFn = unsafe extern "C" fn(*const c_void, usize, *mut u8, usize) -> u8;
pub type RadareStackSlotViewFn =
    unsafe extern "C" fn(*const c_void, usize, *mut RadareAbi138StackSlotView) -> u8;
pub type RadareStackSlotStringFn =
    unsafe extern "C" fn(*const c_void, usize, i32, *mut u8, usize) -> u8;
pub type RadareCallSiteViewFn =
    unsafe extern "C" fn(*const c_void, usize, *mut RadareAbi138CallSiteView) -> u8;
pub type RadareCallSiteStringFn = unsafe extern "C" fn(*const c_void, usize, *mut u8, usize) -> u8;
pub type RadareCallArgumentViewFn =
    unsafe extern "C" fn(*const c_void, usize, usize, *mut RadareAbi138ParameterView) -> u8;
pub type RadareCallArgumentStorageNameFn =
    unsafe extern "C" fn(*const c_void, usize, usize, *mut u8, usize) -> u8;
pub type RadareTypeGraphViewFn =
    unsafe extern "C" fn(*const c_void, *mut RadareAbi138TypeGraphView) -> u8;
pub type RadareTypeViewFn =
    unsafe extern "C" fn(*const c_void, usize, *mut RadareAbi138TypeView) -> u8;
pub type RadareAggregateViewFn =
    unsafe extern "C" fn(*const c_void, usize, *mut RadareAbi138AggregateView) -> u8;
pub type RadareAggregateMemberViewFn =
    unsafe extern "C" fn(*const c_void, usize, usize, *mut RadareAbi138AggregateMemberView) -> u8;
pub type RadareAggregateMemberNameFn =
    unsafe extern "C" fn(*const c_void, usize, usize, *mut u8, usize) -> u8;
pub type RadareBlockViewFn =
    unsafe extern "C" fn(*const c_void, usize, *mut RadareAbi138BlockView) -> u8;
pub type RadareBlockBytesFn =
    unsafe extern "C" fn(*const c_void, usize, usize, *mut u8, usize) -> u8;
pub type RadareSuccessorViewFn =
    unsafe extern "C" fn(*const c_void, usize, usize, *mut RadareAbi138SuccessorView) -> u8;
pub type RadareExternalExitFn = unsafe extern "C" fn(*const c_void, usize, *mut u64) -> u8;
pub type RadareReturnMechanismViewFn =
    unsafe extern "C" fn(*const c_void, *mut RadareAbi138ReturnMechanismView) -> u8;
pub type RadareFramePointerStorageViewFn =
    unsafe extern "C" fn(*const c_void, *mut RadareAbi138RegisterStorageView) -> u8;
pub type RadareStackAllocationContractViewFn =
    unsafe extern "C" fn(*const c_void, *mut RadareAbi138StackAllocationContractView) -> u8;

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct RadareAbi138Accessors {
    pub struct_size: u32,
    pub abi_version: u32,
    pub snapshot_schema_version: u32,
    pub accessor_schema_version: u32,
    pub snapshot_view: Option<RadareSnapshotViewFn>,
    pub arch_id: Option<RadareStringFn>,
    pub cpu_id: Option<RadareStringFn>,
    pub function_name: Option<RadareStringFn>,
    pub interface_view: Option<RadareInterfaceViewFn>,
    pub interface_calling_convention: Option<RadareStringFn>,
    pub interface_storage_name: Option<RadareInterfaceStorageNameFn>,
    pub parameter_view: Option<RadareParameterViewFn>,
    pub parameter_name: Option<RadareIndexedStringFn>,
    pub parameter_storage_name: Option<RadareIndexedStringFn>,
    pub stack_slot_view: Option<RadareStackSlotViewFn>,
    pub stack_slot_string: Option<RadareStackSlotStringFn>,
    pub call_site_view: Option<RadareCallSiteViewFn>,
    pub call_site_calling_convention: Option<RadareCallSiteStringFn>,
    pub call_site_result_storage_name: Option<RadareCallSiteStringFn>,
    pub call_argument_view: Option<RadareCallArgumentViewFn>,
    pub call_argument_storage_name: Option<RadareCallArgumentStorageNameFn>,
    pub type_graph_view: Option<RadareTypeGraphViewFn>,
    pub type_view: Option<RadareTypeViewFn>,
    pub aggregate_view: Option<RadareAggregateViewFn>,
    pub aggregate_name: Option<RadareIndexedStringFn>,
    pub aggregate_member_view: Option<RadareAggregateMemberViewFn>,
    pub aggregate_member_name: Option<RadareAggregateMemberNameFn>,
    pub block_view: Option<RadareBlockViewFn>,
    pub block_bytes: Option<RadareBlockBytesFn>,
    pub successor_view: Option<RadareSuccessorViewFn>,
    pub external_exit: Option<RadareExternalExitFn>,
    pub return_mechanism_view: Option<RadareReturnMechanismViewFn>,
    pub frame_pointer_storage_view: Option<RadareFramePointerStorageViewFn>,
    pub stack_allocation_contract_view: Option<RadareStackAllocationContractViewFn>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RadareAbi138CaptureError {
    NullInput,
    InvalidInputSize,
    UnsupportedVersion,
    InvalidAccessorSize,
    MissingAccessor(&'static str),
    AccessorFailed(&'static str),
    InvalidBoolean,
    InvalidCapabilities,
    UnsupportedExactCallSites,
    InactivePayload,
    BudgetExceeded,
    InvalidUtf8,
    InvalidString,
    InvalidMachine,
    InvalidRange,
    InvalidAdvisoryCall,
    InvalidEnum,
    InvalidInterface,
    InvalidTypeGraph,
    SnapshotChanged,
    SnapshotValidation(SnapshotValidationError),
}

impl std::fmt::Display for RadareAbi138CaptureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "radare ABI 139 snapshot capture failed: {self:?}")
    }
}

impl std::error::Error for RadareAbi138CaptureError {}

impl From<SnapshotValidationError> for RadareAbi138CaptureError {
    fn from(value: SnapshotValidationError) -> Self {
        Self::SnapshotValidation(value)
    }
}

#[derive(Default)]
struct CaptureBudget {
    strings: usize,
    total: usize,
    successors: usize,
    members: usize,
    call_arguments: usize,
}

impl CaptureBudget {
    fn charge(&mut self, bytes: usize) -> Result<(), RadareAbi138CaptureError> {
        self.total = self
            .total
            .checked_add(bytes)
            .filter(|total| *total <= MAX_TOTAL_CAPTURE_BYTES)
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
        Ok(())
    }

    fn charge_string(&mut self, bytes: usize) -> Result<(), RadareAbi138CaptureError> {
        if bytes > MAX_STRING_BYTES {
            return Err(RadareAbi138CaptureError::BudgetExceeded);
        }
        self.strings = self
            .strings
            .checked_add(bytes)
            .filter(|total| *total <= MAX_TOTAL_STRING_BYTES)
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
        self.charge(bytes.saturating_add(1))
    }
}

fn exact_size<T>() -> Result<u32, RadareAbi138CaptureError> {
    u32::try_from(size_of::<T>()).map_err(|_| RadareAbi138CaptureError::InvalidInputSize)
}

fn wire_bool(value: u8) -> Result<bool, RadareAbi138CaptureError> {
    match value {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(RadareAbi138CaptureError::InvalidBoolean),
    }
}

fn callback_ok(value: u8, name: &'static str) -> Result<(), RadareAbi138CaptureError> {
    match value {
        0 => Err(RadareAbi138CaptureError::AccessorFailed(name)),
        1 => Ok(()),
        _ => Err(RadareAbi138CaptureError::InvalidBoolean),
    }
}

fn required<T: Copy>(
    callback: Option<T>,
    name: &'static str,
) -> Result<T, RadareAbi138CaptureError> {
    callback.ok_or(RadareAbi138CaptureError::MissingAccessor(name))
}

unsafe fn copy_string(
    snapshot: *const c_void,
    callback: RadareStringFn,
    length: usize,
    name: &'static str,
    budget: &mut CaptureBudget,
) -> Result<String, RadareAbi138CaptureError> {
    budget.charge_string(length)?;
    let capacity = length
        .checked_add(1)
        .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
    let mut bytes = vec![0xff; capacity];
    // SAFETY: the caller guarantees callback validity for the borrowed snapshot;
    // this module owns a buffer of the exact advertised capacity.
    callback_ok(
        unsafe { callback(snapshot, bytes.as_mut_ptr(), capacity) },
        name,
    )?;
    if bytes[length] != 0 || bytes[..length].contains(&0) {
        return Err(RadareAbi138CaptureError::InvalidString);
    }
    String::from_utf8(bytes[..length].to_vec()).map_err(|_| RadareAbi138CaptureError::InvalidUtf8)
}

unsafe fn copy_indexed_string(
    snapshot: *const c_void,
    callback: RadareIndexedStringFn,
    index: usize,
    length: usize,
    name: &'static str,
    budget: &mut CaptureBudget,
) -> Result<String, RadareAbi138CaptureError> {
    budget.charge_string(length)?;
    let capacity = length
        .checked_add(1)
        .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
    let mut bytes = vec![0xff; capacity];
    // SAFETY: see `copy_string`; index validity was bounded by the parent view.
    callback_ok(
        unsafe { callback(snapshot, index, bytes.as_mut_ptr(), capacity) },
        name,
    )?;
    if bytes[length] != 0 || bytes[..length].contains(&0) {
        return Err(RadareAbi138CaptureError::InvalidString);
    }
    String::from_utf8(bytes[..length].to_vec()).map_err(|_| RadareAbi138CaptureError::InvalidUtf8)
}

unsafe fn copy_interface_storage_name(
    snapshot: *const c_void,
    callback: RadareInterfaceStorageNameFn,
    kind: i32,
    length: usize,
    budget: &mut CaptureBudget,
) -> Result<String, RadareAbi138CaptureError> {
    budget.charge_string(length)?;
    let capacity = length
        .checked_add(1)
        .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
    let mut bytes = vec![0xff; capacity];
    // SAFETY: callback validity is part of the unsafe API contract.
    callback_ok(
        unsafe { callback(snapshot, kind, bytes.as_mut_ptr(), capacity) },
        "interface_storage_name",
    )?;
    if bytes[length] != 0 || bytes[..length].contains(&0) {
        return Err(RadareAbi138CaptureError::InvalidString);
    }
    String::from_utf8(bytes[..length].to_vec()).map_err(|_| RadareAbi138CaptureError::InvalidUtf8)
}

unsafe fn copy_stack_slot_string(
    snapshot: *const c_void,
    callback: RadareStackSlotStringFn,
    index: usize,
    kind: i32,
    length: usize,
    budget: &mut CaptureBudget,
) -> Result<String, RadareAbi138CaptureError> {
    budget.charge_string(length)?;
    let capacity = length
        .checked_add(1)
        .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
    let mut bytes = vec![0xff; capacity];
    // SAFETY: callback validity is part of the unsafe API contract.
    callback_ok(
        unsafe { callback(snapshot, index, kind, bytes.as_mut_ptr(), capacity) },
        "stack_slot_string",
    )?;
    if bytes[length] != 0 || bytes[..length].contains(&0) {
        return Err(RadareAbi138CaptureError::InvalidString);
    }
    String::from_utf8(bytes[..length].to_vec()).map_err(|_| RadareAbi138CaptureError::InvalidUtf8)
}

unsafe fn copy_call_argument_storage_name(
    snapshot: *const c_void,
    callback: RadareCallArgumentStorageNameFn,
    call_index: usize,
    argument_index: usize,
    length: usize,
    budget: &mut CaptureBudget,
) -> Result<String, RadareAbi138CaptureError> {
    budget.charge_string(length)?;
    let capacity = length
        .checked_add(1)
        .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
    let mut bytes = vec![0xff; capacity];
    // SAFETY: callback validity is part of the unsafe API contract and both
    // indices were bounded by stable parent views.
    callback_ok(
        unsafe {
            callback(
                snapshot,
                call_index,
                argument_index,
                bytes.as_mut_ptr(),
                capacity,
            )
        },
        "call_argument_storage_name",
    )?;
    if bytes[length] != 0 || bytes[..length].contains(&0) {
        return Err(RadareAbi138CaptureError::InvalidString);
    }
    String::from_utf8(bytes[..length].to_vec()).map_err(|_| RadareAbi138CaptureError::InvalidUtf8)
}

fn storage(
    view: RadareAbi138RegisterStorageView,
) -> Result<CanonicalStorageId, RadareAbi138CaptureError> {
    if view.name_length == 0
        || view.size == 0
        || view.offset.checked_add(u64::from(view.size)).is_none()
    {
        return Err(RadareAbi138CaptureError::InvalidInterface);
    }
    Ok(CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset: view.offset,
        size: view.size,
    })
}

fn absent_storage(view: RadareAbi138RegisterStorageView) -> bool {
    view.name_length == 0 && view.offset == 0 && view.size == 0
}

fn logical_value(
    type_id: u32,
    carrier: RadareAbi138CarrierProjection,
) -> Result<SourceLogicalValue, RadareAbi138CaptureError> {
    let kind = match carrier.kind {
        1 => SourceCarrierKind::Full,
        2 => SourceCarrierKind::LowBits,
        _ => return Err(RadareAbi138CaptureError::InvalidEnum),
    };
    Ok(SourceLogicalValue::new(
        type_id,
        SourceCarrierProjection::new(kind, carrier.offset_bits, carrier.size_bits),
    ))
}

unsafe fn read_view(
    snapshot: *const c_void,
    callback: RadareSnapshotViewFn,
) -> Result<RadareAbi138SnapshotView, RadareAbi138CaptureError> {
    let mut view = RadareAbi138SnapshotView::default();
    // SAFETY: callback and snapshot validity are guaranteed by the caller.
    callback_ok(unsafe { callback(snapshot, &mut view) }, "snapshot_view")?;
    Ok(view)
}

fn validate_top(view: &RadareAbi138SnapshotView) -> Result<(), RadareAbi138CaptureError> {
    if view.schema_version != RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION
        || view.struct_size != exact_size::<RadareAbi138SnapshotView>()?
    {
        return Err(RadareAbi138CaptureError::UnsupportedVersion);
    }
    if view.capabilities & !KNOWN_CAPABILITIES != 0
        || view.capabilities & RADARE_CAP_REVISION == 0
        || view.capabilities & RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE == 0
        || view.revision_identity == 0
    {
        return Err(RadareAbi138CaptureError::InvalidCapabilities);
    }
    if view.capabilities & RADARE_CAP_EXACT_CALL_SITE_INTERFACES != 0 {
        return Err(RadareAbi138CaptureError::UnsupportedExactCallSites);
    }
    let exact_interface = view.capabilities & RADARE_CAP_EXACT_FUNCTION_INTERFACE != 0;
    let exact_types = view.capabilities & RADARE_CAP_EXACT_FUNCTION_TYPES != 0;
    let exact_slots = view.capabilities & RADARE_CAP_EXACT_STACK_SLOT_ROLES != 0;
    let exact_return_mechanism = view.capabilities & RADARE_CAP_EXACT_RETURN_MECHANISM != 0;
    let exact_frame_pointer = view.capabilities & RADARE_CAP_EXACT_FRAME_POINTER_STORAGE != 0;
    let exact_stack_allocation =
        view.capabilities & RADARE_CAP_EXACT_STACK_ALLOCATION_CONTRACT != 0;
    if (exact_types || exact_slots) && !exact_interface {
        return Err(RadareAbi138CaptureError::InvalidCapabilities);
    }
    if (exact_slots && view.capabilities & RADARE_CAP_STACK_SLOTS == 0)
        || (exact_types && view.capabilities & RADARE_CAP_TYPES == 0)
        || (exact_stack_allocation
            && (!exact_interface || view.capabilities & RADARE_CAP_STACK_POINTER_STORAGE == 0))
        || (exact_return_mechanism
            && (!exact_interface
                || !exact_slots
                || view.capabilities & RADARE_CAP_RETURN_ADDRESS_STORAGE == 0
                || view.capabilities & RADARE_CAP_STACK_POINTER_STORAGE == 0))
        || (exact_frame_pointer
            && (!exact_interface
                || view.capabilities & RADARE_CAP_RETURN_ADDRESS_STORAGE == 0
                || view.capabilities & RADARE_CAP_STACK_POINTER_STORAGE == 0))
    {
        return Err(RadareAbi138CaptureError::InvalidCapabilities);
    }
    if view.num_stack_slots != 0 && view.capabilities & RADARE_CAP_STACK_SLOTS == 0 {
        return Err(RadareAbi138CaptureError::InactivePayload);
    }
    if (view.num_types != 0 || view.num_aggregates != 0)
        && view.capabilities & RADARE_CAP_TYPES == 0
    {
        return Err(RadareAbi138CaptureError::InactivePayload);
    }
    if view.num_call_site_interfaces != 0
        && view.capabilities & RADARE_CAP_CALL_SITE_INTERFACES == 0
    {
        return Err(RadareAbi138CaptureError::InactivePayload);
    }
    if view.num_base_types != 0 && view.capabilities & RADARE_CAP_TYPES == 0 {
        return Err(RadareAbi138CaptureError::InactivePayload);
    }
    if !matches!(view.bits, 32 | 64)
        || !matches!(view.endian, RADARE_ENDIAN_LITTLE | RADARE_ENDIAN_BIG)
    {
        return Err(RadareAbi138CaptureError::InvalidMachine);
    }
    if view.function_size == 0
        || view.num_blocks == 0
        || view.num_blocks > MAX_BLOCKS
        || view.total_source_bytes == 0
        || view.total_source_bytes > MAX_FUNCTION_BYTES
        || view.num_external_exits > MAX_EXTERNAL_EXITS
        || view.num_stack_slots > MAX_STACK_SLOTS
        || view.num_call_site_interfaces > MAX_CALLS
        || view.num_types > MAX_TYPES
        || view.num_aggregates > MAX_AGGREGATES
        || view.arch_id_length == 0
        || view.cpu_id_length == 0
    {
        return Err(RadareAbi138CaptureError::BudgetExceeded);
    }
    Ok(())
}

unsafe fn capture_type_graph(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    top: &RadareAbi138SnapshotView,
    budget: &mut CaptureBudget,
) -> Result<SourceTypeGraph, RadareAbi138CaptureError> {
    let graph_view_fn = required(accessors.type_graph_view, "type_graph_view")?;
    let type_view_fn = required(accessors.type_view, "type_view")?;
    let aggregate_view_fn = required(accessors.aggregate_view, "aggregate_view")?;
    let aggregate_name_fn = required(accessors.aggregate_name, "aggregate_name")?;
    let member_view_fn = required(accessors.aggregate_member_view, "aggregate_member_view")?;
    let member_name_fn = required(accessors.aggregate_member_name, "aggregate_member_name")?;

    let mut graph_view = RadareAbi138TypeGraphView::default();
    // SAFETY: foreign callback validity is guaranteed by the API caller.
    callback_ok(
        unsafe { graph_view_fn(snapshot, &mut graph_view) },
        "type_graph_view",
    )?;
    if graph_view.num_types != top.num_types
        || graph_view.num_aggregates != top.num_aggregates
        || !wire_bool(graph_view.complete)?
        || graph_view.num_types == 0
    {
        return Err(RadareAbi138CaptureError::InvalidTypeGraph);
    }
    budget.charge(
        graph_view
            .num_types
            .checked_mul(size_of::<SourceType>())
            .and_then(|types| {
                graph_view
                    .num_aggregates
                    .checked_mul(size_of::<SourceAggregateLayout>())
                    .and_then(|aggregates| types.checked_add(aggregates))
            })
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
    )?;

    let mut types = Vec::with_capacity(graph_view.num_types);
    for index in 0..graph_view.num_types {
        let mut view = RadareAbi138TypeView::default();
        // SAFETY: index is bounded by the stable parent view.
        callback_ok(
            unsafe { type_view_fn(snapshot, index, &mut view) },
            "type_view",
        )?;
        if usize::try_from(view.id) != Ok(index) {
            return Err(RadareAbi138CaptureError::InvalidTypeGraph);
        }
        let kind = match view.kind {
            1 if view.target_type_id == INVALID_TYPE_ID && view.aggregate_id == u32::MAX => {
                SourceTypeKind::SignedInteger
            }
            2 if view.target_type_id == INVALID_TYPE_ID && view.aggregate_id == u32::MAX => {
                SourceTypeKind::UnsignedInteger
            }
            3 if view.target_type_id != INVALID_TYPE_ID && view.aggregate_id == u32::MAX => {
                SourceTypeKind::Pointer {
                    target_type_id: view.target_type_id,
                }
            }
            4 if view.target_type_id == INVALID_TYPE_ID && view.aggregate_id != u32::MAX => {
                SourceTypeKind::Struct {
                    aggregate_id: view.aggregate_id,
                }
            }
            _ => return Err(RadareAbi138CaptureError::InvalidEnum),
        };
        types.push(SourceType::new(
            view.id,
            kind,
            view.size_bits,
            view.align_bits,
        ));
    }

    let mut aggregates = Vec::with_capacity(graph_view.num_aggregates);
    for aggregate_index in 0..graph_view.num_aggregates {
        let mut view = RadareAbi138AggregateView::default();
        // SAFETY: aggregate index is bounded by the stable graph view.
        callback_ok(
            unsafe { aggregate_view_fn(snapshot, aggregate_index, &mut view) },
            "aggregate_view",
        )?;
        if usize::try_from(view.id) != Ok(aggregate_index)
            || !wire_bool(view.complete)?
            || !wire_bool(view.c_layout_compatible)?
            || view.num_members == 0
        {
            return Err(RadareAbi138CaptureError::InvalidTypeGraph);
        }
        budget.members = budget
            .members
            .checked_add(view.num_members)
            .filter(|members| *members <= MAX_MEMBERS)
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
        budget.charge(
            view.num_members
                .checked_mul(size_of::<SourceAggregateMember>())
                .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
        )?;
        // SAFETY: callback writes the advertised caller-owned string.
        let name = unsafe {
            copy_indexed_string(
                snapshot,
                aggregate_name_fn,
                aggregate_index,
                view.name_length,
                "aggregate_name",
                budget,
            )
        }?;
        let mut members = Vec::with_capacity(view.num_members);
        for member_index in 0..view.num_members {
            let mut member = RadareAbi138AggregateMemberView::default();
            // SAFETY: both indices are bounded by their stable parent views.
            callback_ok(
                unsafe { member_view_fn(snapshot, aggregate_index, member_index, &mut member) },
                "aggregate_member_view",
            )?;
            if usize::try_from(member.member_id) != Ok(member_index) || member.count != 1 {
                return Err(RadareAbi138CaptureError::InvalidTypeGraph);
            }
            budget.charge_string(member.name_length)?;
            let capacity = member
                .name_length
                .checked_add(1)
                .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
            let mut bytes = vec![0xff; capacity];
            // SAFETY: callback writes the advertised caller-owned string.
            callback_ok(
                unsafe {
                    member_name_fn(
                        snapshot,
                        aggregate_index,
                        member_index,
                        bytes.as_mut_ptr(),
                        capacity,
                    )
                },
                "aggregate_member_name",
            )?;
            if bytes[member.name_length] != 0 || bytes[..member.name_length].contains(&0) {
                return Err(RadareAbi138CaptureError::InvalidString);
            }
            let member_name = String::from_utf8(bytes[..member.name_length].to_vec())
                .map_err(|_| RadareAbi138CaptureError::InvalidUtf8)?;
            members.push(SourceAggregateMember::new(
                member.member_id,
                member.type_id,
                member.offset_bits,
                member.size_bits,
                member_name,
            ));
        }
        aggregates.push(SourceAggregateLayout::new(
            view.id,
            view.type_id,
            view.size_bits,
            view.align_bits,
            name,
            members,
        ));
    }
    SourceTypeGraph::new(types, aggregates).map_err(|_| RadareAbi138CaptureError::InvalidTypeGraph)
}

unsafe fn capture_stack_slots(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    top: &RadareAbi138SnapshotView,
    exact_roles: bool,
    budget: &mut CaptureBudget,
) -> Result<(Vec<SourceStackSlotSpec>, Vec<SourceStackSlotName>), RadareAbi138CaptureError> {
    let view_fn = required(accessors.stack_slot_view, "stack_slot_view")?;
    let string_fn = required(accessors.stack_slot_string, "stack_slot_string")?;
    budget.charge(
        top.num_stack_slots
            .checked_mul(size_of::<SourceStackSlotSpec>())
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
    )?;
    let mut slots = Vec::with_capacity(top.num_stack_slots);
    let mut names = Vec::new();
    for index in 0..top.num_stack_slots {
        let mut view = RadareAbi138StackSlotView::default();
        // SAFETY: index is bounded by the stable top-level view.
        callback_ok(
            unsafe { view_fn(snapshot, index, &mut view) },
            "stack_slot_view",
        )?;
        // only an exact role inventory needs each slot's reach, so keep the rest
        if !wire_bool(view.offset_valid)? || (exact_roles && view.size == 0) {
            return Err(RadareAbi138CaptureError::InvalidInterface);
        }
        // Every owned string is validated; the name is kept because presentation
        // carries it, and the rest have no place in the semantic slot contract.
        let mut slot_name = String::new();
        for (kind, length) in [
            (0, view.name_length),
            (1, view.type_length),
            (2, view.base_name_length),
            (3, view.arg_name_length),
            (4, view.home_reg_length),
        ] {
            // SAFETY: string kind is from the closed schema-12 vocabulary.
            let string = unsafe {
                copy_stack_slot_string(snapshot, string_fn, index, kind, length, budget)
            }?;
            if kind == 0 {
                slot_name = string;
            }
        }
        let base = match view.base {
            0 => StackAddressBase::FramePointer,
            1 => StackAddressBase::StackPointer,
            _ => return Err(RadareAbi138CaptureError::InvalidEnum),
        };
        if !slot_name.is_empty() {
            names.push(SourceStackSlotName::new(base, view.offset, slot_name));
        }
        let base_storage = storage(RadareAbi138RegisterStorageView {
            name_length: view.base_name_length,
            offset: view.base_offset,
            size: view.base_size,
        })?;
        if !exact_roles {
            if !matches!(view.role, 0..=3) {
                return Err(RadareAbi138CaptureError::InvalidEnum);
            }
            if view.arg_index != -1
                || view.arg_name_length != 0
                || view.home_reg_length != 0
                || view.home_reg_offset != 0
                || view.home_reg_size != 0
            {
                return Err(RadareAbi138CaptureError::InactivePayload);
            }
            slots.push(SourceStackSlotSpec::new(
                base,
                base_storage,
                view.offset,
                view.size,
            ));
            continue;
        }
        let slot = match view.role {
            0 if view.arg_index == -1
                && view.arg_name_length == 0
                && view.home_reg_length == 0
                && view.home_reg_offset == 0
                && view.home_reg_size == 0 =>
            {
                SourceStackSlotSpec::new_local(base, base_storage, view.offset, view.size)
            }
            2 if view.arg_index >= 0 && view.home_reg_length != 0 => {
                let parameter_index = u32::try_from(view.arg_index)
                    .map_err(|_| RadareAbi138CaptureError::InvalidInterface)?;
                let home_storage = storage(RadareAbi138RegisterStorageView {
                    name_length: view.home_reg_length,
                    offset: view.home_reg_offset,
                    size: view.home_reg_size,
                })?;
                SourceStackSlotSpec::new_parameter_home(
                    base,
                    base_storage,
                    view.offset,
                    view.size,
                    parameter_index,
                    home_storage,
                )
            }
            _ => return Err(RadareAbi138CaptureError::InvalidEnum),
        };
        slots.push(slot);
    }
    Ok((slots, names))
}

unsafe fn capture_return_mechanism(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    active: bool,
    interface: SourceFunctionInterface,
    address_size_bytes: u32,
) -> Result<SourceFunctionInterface, RadareAbi138CaptureError> {
    if !active {
        return Ok(interface);
    }
    let view_fn = required(accessors.return_mechanism_view, "return_mechanism_view")?;
    let mut first = RadareAbi138ReturnMechanismView::default();
    // SAFETY: callback and snapshot validity are guaranteed by the caller.
    callback_ok(
        unsafe { view_fn(snapshot, &mut first) },
        "return_mechanism_view",
    )?;
    let mut second = RadareAbi138ReturnMechanismView::default();
    // SAFETY: callback and snapshot validity remain live for the second read.
    callback_ok(
        unsafe { view_fn(snapshot, &mut second) },
        "return_mechanism_view",
    )?;
    if first != second {
        return Err(RadareAbi138CaptureError::SnapshotChanged);
    }
    if first.kind != 1 {
        return Err(RadareAbi138CaptureError::InvalidEnum);
    }
    interface
        .with_exact_stacked_return(
            first.stack_offset,
            first.slot_size_bytes,
            first.stack_pointer_delta_bytes,
            address_size_bytes,
        )
        .map_err(|_| RadareAbi138CaptureError::InvalidInterface)
}

unsafe fn capture_frame_pointer_storage(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    active: bool,
    interface: SourceFunctionInterface,
    budget: &mut CaptureBudget,
) -> Result<SourceFunctionInterface, RadareAbi138CaptureError> {
    if !active {
        return Ok(interface);
    }
    let view_fn = required(
        accessors.frame_pointer_storage_view,
        "frame_pointer_storage_view",
    )?;
    let name_fn = required(accessors.interface_storage_name, "interface_storage_name")?;
    let mut first = RadareAbi138RegisterStorageView::default();
    // SAFETY: callback and snapshot validity are guaranteed by the caller.
    callback_ok(
        unsafe { view_fn(snapshot, &mut first) },
        "frame_pointer_storage_view",
    )?;
    // SAFETY: callback writes one owned string of the advertised size.
    let first_name =
        unsafe { copy_interface_storage_name(snapshot, name_fn, 3, first.name_length, budget) }?;
    let mut second = RadareAbi138RegisterStorageView::default();
    // SAFETY: callback and snapshot validity remain live for the second read.
    callback_ok(
        unsafe { view_fn(snapshot, &mut second) },
        "frame_pointer_storage_view",
    )?;
    // SAFETY: the second stable view advertises this owned string length.
    let second_name =
        unsafe { copy_interface_storage_name(snapshot, name_fn, 3, second.name_length, budget) }?;
    if first != second || first_name != second_name {
        return Err(RadareAbi138CaptureError::SnapshotChanged);
    }
    if first_name.is_empty() {
        return Err(RadareAbi138CaptureError::InvalidInterface);
    }
    interface
        .with_frame_pointer_storage(storage(first)?)
        .map_err(|_| RadareAbi138CaptureError::InvalidInterface)
}

unsafe fn capture_stack_allocation_contract(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    active: bool,
    interface: SourceFunctionInterface,
) -> Result<SourceFunctionInterface, RadareAbi138CaptureError> {
    if !active {
        return Ok(interface);
    }
    let view_fn = required(
        accessors.stack_allocation_contract_view,
        "stack_allocation_contract_view",
    )?;
    let mut first = RadareAbi138StackAllocationContractView::default();
    // SAFETY: callback and snapshot validity are guaranteed by the caller.
    callback_ok(
        unsafe { view_fn(snapshot, &mut first) },
        "stack_allocation_contract_view",
    )?;
    let mut second = RadareAbi138StackAllocationContractView::default();
    // SAFETY: callback and snapshot validity remain live for the second read.
    callback_ok(
        unsafe { view_fn(snapshot, &mut second) },
        "stack_allocation_contract_view",
    )?;
    if first != second {
        return Err(RadareAbi138CaptureError::SnapshotChanged);
    }
    let growth = match first.growth {
        1 => SourceStackGrowth::LowerAddresses,
        2 => SourceStackGrowth::HigherAddresses,
        _ => return Err(RadareAbi138CaptureError::InvalidEnum),
    };
    interface
        .with_stack_allocation_contract(
            SourceStackAllocationContract::with_implicit_active_sp_bytes(
                growth,
                first.implicit_active_sp_bytes,
            ),
        )
        .map_err(|_| RadareAbi138CaptureError::InvalidInterface)
}

type CapturedInterface = (
    SourceFunctionInterface,
    Box<[Box<str>]>,
    Box<[SourceStackSlotName]>,
);

/// Read the machine carriers radare2 resolved from its register profile.
///
/// This is independent of the ABI interface on purpose: radare2 advertises the
/// return-address and stack-pointer capabilities from register aliases, which
/// it knows with or without debug information. Capturing them here keeps them
/// reachable for functions whose ABI was never recovered, instead of losing
/// them because the surrounding interface could not be captured.
unsafe fn capture_machine_roles(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    top: &RadareAbi138SnapshotView,
) -> Result<SourceMachineRoles, RadareAbi138CaptureError> {
    let has_return_address = top.capabilities & RADARE_CAP_RETURN_ADDRESS_STORAGE != 0;
    let has_stack_pointer = top.capabilities & RADARE_CAP_STACK_POINTER_STORAGE != 0;
    if !has_return_address && !has_stack_pointer {
        return Ok(SourceMachineRoles::default());
    }
    let view_fn = required(accessors.interface_view, "interface_view")?;
    let mut view = RadareAbi138FunctionInterfaceView::default();
    // SAFETY: callback validity is guaranteed by the caller.
    callback_ok(unsafe { view_fn(snapshot, &mut view) }, "interface_view")?;
    let return_address_storage = if has_return_address {
        Some(storage(view.return_address_storage)?)
    } else if absent_storage(view.return_address_storage) {
        None
    } else {
        return Err(RadareAbi138CaptureError::InactivePayload);
    };
    let stack_pointer_storage = if has_stack_pointer {
        Some(storage(view.stack_pointer_storage)?)
    } else if absent_storage(view.stack_pointer_storage) {
        None
    } else {
        return Err(RadareAbi138CaptureError::InactivePayload);
    };
    SourceMachineRoles::new(return_address_storage, stack_pointer_storage)
        .map_err(|_| RadareAbi138CaptureError::InvalidInterface)
}

unsafe fn capture_interface(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    top: &RadareAbi138SnapshotView,
    revision: &[u8],
    budget: &mut CaptureBudget,
) -> Result<CapturedInterface, RadareAbi138CaptureError> {
    let view_fn = required(accessors.interface_view, "interface_view")?;
    let cc_fn = required(
        accessors.interface_calling_convention,
        "interface_calling_convention",
    )?;
    let storage_name_fn = required(accessors.interface_storage_name, "interface_storage_name")?;
    let parameter_view_fn = required(accessors.parameter_view, "parameter_view")?;
    let parameter_name_fn = required(accessors.parameter_name, "parameter_name")?;
    let parameter_storage_name_fn =
        required(accessors.parameter_storage_name, "parameter_storage_name")?;
    let mut view = RadareAbi138FunctionInterfaceView::default();
    // SAFETY: callback validity is guaranteed by the caller.
    callback_ok(unsafe { view_fn(snapshot, &mut view) }, "interface_view")?;
    let variadic = wire_bool(view.variadic)?;
    let noreturn = wire_bool(view.noreturn)?;
    let stack_resources_complete = wire_bool(view.stack_resources_complete)?;
    let stack_roles_complete = wire_bool(view.stack_slot_roles_complete)?;
    let complete = wire_bool(view.complete)?;
    let logical_types_complete = wire_bool(view.logical_types_complete)?;
    let stack_pointer_preserved = wire_bool(view.stack_pointer_preserved_across_calls)?;
    let frame_pointer_preserved = wire_bool(view.frame_pointer_preserved_across_calls)?;
    let exact_types = top.capabilities & RADARE_CAP_EXACT_FUNCTION_TYPES != 0;
    let exact_slots = top.capabilities & RADARE_CAP_EXACT_STACK_SLOT_ROLES != 0;
    if !complete
        || variadic
        || noreturn
        || (exact_slots && !stack_resources_complete)
        || stack_roles_complete != exact_slots
        || logical_types_complete != exact_types
        || view.num_parameters > MAX_PARAMETERS
    {
        return Err(RadareAbi138CaptureError::InvalidInterface);
    }
    budget.charge(
        view.num_parameters
            .checked_mul(size_of::<SourceAbiParameterSpec>())
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
    )?;
    if exact_types {
        budget.charge(
            view.num_parameters
                .checked_mul(size_of::<SourceLogicalValue>())
                .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
        )?;
    }
    // SAFETY: callback writes an owned string of the advertised size.
    let calling_convention = unsafe {
        copy_string(
            snapshot,
            cc_fn,
            view.calling_convention_length,
            "interface_calling_convention",
            budget,
        )
    }?;
    if calling_convention.trim().is_empty() {
        return Err(RadareAbi138CaptureError::InvalidInterface);
    }

    let mut parameters = Vec::with_capacity(view.num_parameters);
    let mut parameter_names = Vec::with_capacity(view.num_parameters);
    let mut logical_parameters = Vec::with_capacity(view.num_parameters);
    for index in 0..view.num_parameters {
        let mut parameter = RadareAbi138ParameterView::default();
        // SAFETY: parameter index is bounded by the stable interface view.
        callback_ok(
            unsafe { parameter_view_fn(snapshot, index, &mut parameter) },
            "parameter_view",
        )?;
        if usize::try_from(parameter.index) != Ok(index) {
            return Err(RadareAbi138CaptureError::InvalidInterface);
        }
        // SAFETY: callback writes an owned string of the advertised size.
        let parameter_storage_name = unsafe {
            copy_indexed_string(
                snapshot,
                parameter_storage_name_fn,
                index,
                parameter.storage.name_length,
                "parameter_storage_name",
                budget,
            )
        }?;
        if parameter_storage_name.is_empty() {
            return Err(RadareAbi138CaptureError::InvalidInterface);
        }
        // SAFETY: callback writes an owned presentation string of the advertised size.
        let parameter_name = unsafe {
            copy_indexed_string(
                snapshot,
                parameter_name_fn,
                index,
                parameter.name_length,
                "parameter_name",
                budget,
            )
        }?;
        parameter_names.push(parameter_name.into_boxed_str());
        parameters.push(SourceAbiParameterSpec::new(
            parameter.index,
            storage(parameter.storage)?,
        ));
        if exact_types {
            logical_parameters.push(logical_value(parameter.logical_type_id, parameter.carrier)?);
        } else if parameter.logical_type_id != INVALID_TYPE_ID
            || parameter.carrier.kind != 0
            || parameter.carrier.offset_bits != 0
            || parameter.carrier.size_bits != 0
        {
            return Err(RadareAbi138CaptureError::InactivePayload);
        }
    }

    let return_kind = match view.return_kind {
        1 if absent_storage(view.return_storage) => SourceFunctionReturn::Void,
        2 => {
            // SAFETY: callback writes an owned string of the advertised size.
            let name = unsafe {
                copy_interface_storage_name(
                    snapshot,
                    storage_name_fn,
                    0,
                    view.return_storage.name_length,
                    budget,
                )
            }?;
            if name.is_empty() {
                return Err(RadareAbi138CaptureError::InvalidInterface);
            }
            SourceFunctionReturn::Register {
                storage: storage(view.return_storage)?,
            }
        }
        _ => return Err(RadareAbi138CaptureError::InvalidEnum),
    };
    let return_logical = if exact_types {
        match return_kind {
            SourceFunctionReturn::Void => {
                if view.return_type_id != INVALID_TYPE_ID
                    || view.return_carrier.kind != 0
                    || view.return_carrier.offset_bits != 0
                    || view.return_carrier.size_bits != 0
                {
                    return Err(RadareAbi138CaptureError::InvalidInterface);
                }
                None
            }
            SourceFunctionReturn::Register { .. } => {
                Some(logical_value(view.return_type_id, view.return_carrier)?)
            }
        }
    } else {
        if view.return_type_id != INVALID_TYPE_ID
            || view.return_carrier.kind != 0
            || view.return_carrier.offset_bits != 0
            || view.return_carrier.size_bits != 0
        {
            return Err(RadareAbi138CaptureError::InactivePayload);
        }
        None
    };

    // SAFETY: slot accessors are required only when exact slot payload is active.
    let (stack_slots, stack_slot_names) = if top.num_stack_slots != 0 {
        unsafe { capture_stack_slots(snapshot, accessors, top, exact_slots, budget) }?
    } else {
        (Vec::new(), Vec::new())
    };
    // SAFETY: type accessors are required only when exact type payload is active.
    let type_graph = if exact_types {
        Some(unsafe { capture_type_graph(snapshot, accessors, top, budget) }?)
    } else {
        None
    };

    let mut interface = if exact_types && exact_slots {
        SourceFunctionInterface::new_exact_with_logical_types(
            revision,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
            logical_parameters,
            return_logical,
            type_graph,
        )
    } else if exact_types {
        SourceFunctionInterface::new_with_logical_types(
            revision,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
            logical_parameters,
            return_logical,
            type_graph,
        )
    } else if exact_slots {
        SourceFunctionInterface::new_exact(
            revision,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
        )
    } else {
        SourceFunctionInterface::new(
            revision,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
        )
    }
    .map_err(|_| RadareAbi138CaptureError::InvalidInterface)?;

    interface =
        interface.with_preserved_call_carriers(stack_pointer_preserved, frame_pointer_preserved);
    if top.capabilities & RADARE_CAP_RETURN_ADDRESS_STORAGE != 0 {
        // SAFETY: callback writes an owned string of the advertised size.
        let name = unsafe {
            copy_interface_storage_name(
                snapshot,
                storage_name_fn,
                1,
                view.return_address_storage.name_length,
                budget,
            )
        }?;
        if name.is_empty() {
            return Err(RadareAbi138CaptureError::InvalidInterface);
        }
        interface = interface
            .with_return_address_storage(storage(view.return_address_storage)?)
            .map_err(|_| RadareAbi138CaptureError::InvalidInterface)?;
    } else if !absent_storage(view.return_address_storage) {
        return Err(RadareAbi138CaptureError::InactivePayload);
    }
    if top.capabilities & RADARE_CAP_STACK_POINTER_STORAGE != 0 {
        // SAFETY: callback writes an owned string of the advertised size.
        let name = unsafe {
            copy_interface_storage_name(
                snapshot,
                storage_name_fn,
                2,
                view.stack_pointer_storage.name_length,
                budget,
            )
        }?;
        if name.is_empty() {
            return Err(RadareAbi138CaptureError::InvalidInterface);
        }
        interface = interface
            .with_stack_pointer_storage(storage(view.stack_pointer_storage)?)
            .map_err(|_| RadareAbi138CaptureError::InvalidInterface)?;
    } else if !absent_storage(view.stack_pointer_storage) {
        return Err(RadareAbi138CaptureError::InactivePayload);
    }
    // SAFETY: the optional scalar callback is copied from the validated table
    // and read twice while the snapshot borrow remains live.
    let interface = unsafe {
        capture_stack_allocation_contract(
            snapshot,
            accessors,
            top.capabilities & RADARE_CAP_EXACT_STACK_ALLOCATION_CONTRACT != 0,
            interface,
        )
    }?;
    let address_size_bytes = u32::try_from(top.bits)
        .ok()
        .and_then(|bits| bits.checked_div(8))
        .filter(|bytes| *bytes > 0)
        .ok_or(RadareAbi138CaptureError::InvalidMachine)?;
    // SAFETY: the optional scalar callback is copied from the validated table
    // and read twice while the snapshot borrow remains live.
    let interface = unsafe {
        capture_return_mechanism(
            snapshot,
            accessors,
            top.capabilities & RADARE_CAP_EXACT_RETURN_MECHANISM != 0,
            interface,
            address_size_bytes,
        )
    }?;
    // SAFETY: both callbacks are copied from the validated table and all
    // returned bytes are deep-copied while the snapshot borrow remains live.
    let interface = unsafe {
        capture_frame_pointer_storage(
            snapshot,
            accessors,
            top.capabilities & RADARE_CAP_EXACT_FRAME_POINTER_STORAGE != 0,
            interface,
            budget,
        )
    }?;
    Ok((
        interface,
        parameter_names.into_boxed_slice(),
        stack_slot_names.into_boxed_slice(),
    ))
}

unsafe fn capture_image(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    top: &RadareAbi138SnapshotView,
    budget: &mut CaptureBudget,
) -> Result<OwnedFunctionImage, RadareAbi138CaptureError> {
    let block_view_fn = required(accessors.block_view, "block_view")?;
    let block_bytes_fn = required(accessors.block_bytes, "block_bytes")?;
    let successor_view_fn = required(accessors.successor_view, "successor_view")?;
    budget.charge(
        top.num_blocks
            .checked_mul(size_of::<OwnedFunctionBlock>())
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
    )?;
    let mut blocks = Vec::with_capacity(top.num_blocks);
    let mut source_bytes = 0usize;
    for block_index in 0..top.num_blocks {
        let mut view = RadareAbi138BlockView::default();
        // SAFETY: index is bounded by the stable top-level view.
        callback_ok(
            unsafe { block_view_fn(snapshot, block_index, &mut view) },
            "block_view",
        )?;
        let size = usize::try_from(view.size)
            .ok()
            .filter(|size| *size != 0 && *size <= MAX_BLOCK_BYTES)
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
        let block_end = view
            .addr
            .checked_add(view.size)
            .ok_or(RadareAbi138CaptureError::InvalidRange)?;
        source_bytes = source_bytes
            .checked_add(size)
            .filter(|total| *total <= MAX_FUNCTION_BYTES)
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
        budget.charge(size)?;
        let mut bytes = vec![0u8; size];
        // SAFETY: buffer is owned and exactly matches the stable block extent.
        callback_ok(
            unsafe { block_bytes_fn(snapshot, block_index, 0, bytes.as_mut_ptr(), size) },
            "block_bytes",
        )?;
        budget.successors = budget
            .successors
            .checked_add(view.num_successors)
            .filter(|total| *total <= MAX_SUCCESSORS)
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
        budget.charge(
            view.num_successors
                .checked_mul(size_of::<AdvisorySuccessor>())
                .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
        )?;
        let mut successors = Vec::with_capacity(view.num_successors);
        for successor_index in 0..view.num_successors {
            let mut successor = RadareAbi138SuccessorView::default();
            // SAFETY: both indices are bounded by stable parent views.
            callback_ok(
                unsafe {
                    successor_view_fn(snapshot, block_index, successor_index, &mut successor)
                },
                "successor_view",
            )?;
            let external = wire_bool(successor.external)?;
            let (kind, case_value) = match successor.kind {
                0 if successor.case_value == 0 => (AdvisorySuccessorKind::Direct, None),
                1 if successor.case_value == 0 => (AdvisorySuccessorKind::Fallthrough, None),
                2 => (
                    AdvisorySuccessorKind::SwitchCase,
                    Some(successor.case_value),
                ),
                3 if successor.case_value == 0 => (AdvisorySuccessorKind::SwitchDefault, None),
                _ => return Err(RadareAbi138CaptureError::InvalidEnum),
            };
            successors.push(AdvisorySuccessor {
                kind,
                target: successor.target_addr,
                case_value,
                external,
            });
        }
        let switch_instruction = match view.switch_addr {
            INVALID_U64 => None,
            address if address >= view.addr && address < block_end => Some(address),
            _ => return Err(RadareAbi138CaptureError::InvalidRange),
        };
        blocks.push(OwnedFunctionBlock {
            address: view.addr,
            bytes: Arc::from(bytes),
            successors: successors.into_boxed_slice(),
            switch_instruction,
        });
    }
    if source_bytes != top.total_source_bytes {
        return Err(RadareAbi138CaptureError::InvalidRange);
    }
    let first_address = blocks
        .first()
        .map(|block| block.address)
        .ok_or(RadareAbi138CaptureError::InvalidRange)?;
    let last_end = blocks
        .last()
        .and_then(|block| {
            u64::try_from(block.bytes.len())
                .ok()
                .and_then(|size| block.address.checked_add(size))
        })
        .ok_or(RadareAbi138CaptureError::InvalidRange)?;
    if last_end.checked_sub(first_address) != Some(top.function_size) {
        return Err(RadareAbi138CaptureError::InvalidRange);
    }

    let external_exit_fn = if top.num_external_exits == 0 {
        accessors.external_exit
    } else {
        Some(required(accessors.external_exit, "external_exit")?)
    };
    budget.charge(
        top.num_external_exits
            .checked_mul(size_of::<u64>())
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
    )?;
    let mut external_exits = Vec::with_capacity(top.num_external_exits);
    for index in 0..top.num_external_exits {
        let mut target = 0u64;
        // SAFETY: callback is present and index is top-view bounded.
        callback_ok(
            unsafe { external_exit_fn.expect("required above")(snapshot, index, &mut target) },
            "external_exit",
        )?;
        external_exits.push(target);
    }
    Ok(OwnedFunctionImage {
        // The legacy accessor transport predates the string table; the flat
        // snapshot buffer is the path that carries it.
        string_literals: Box::new([]),
        entry_address: top.function_addr,
        blocks: blocks.into_boxed_slice(),
        external_exits: external_exits.into_boxed_slice(),
        total_source_bytes: source_bytes,
    })
}

unsafe fn capture_advisory_calls(
    snapshot: *const c_void,
    accessors: &RadareAbi138Accessors,
    top: &RadareAbi138SnapshotView,
    budget: &mut CaptureBudget,
) -> Result<Box<[AdvisoryCallSite]>, RadareAbi138CaptureError> {
    if top.num_call_site_interfaces == 0 {
        return Ok(Box::new([]));
    }
    let view_fn = required(accessors.call_site_view, "call_site_view")?;
    let calling_convention_fn = required(
        accessors.call_site_calling_convention,
        "call_site_calling_convention",
    )?;
    let result_storage_name_fn = required(
        accessors.call_site_result_storage_name,
        "call_site_result_storage_name",
    )?;
    let argument_view_fn = required(accessors.call_argument_view, "call_argument_view")?;
    let argument_storage_name_fn = required(
        accessors.call_argument_storage_name,
        "call_argument_storage_name",
    )?;
    budget.charge(
        top.num_call_site_interfaces
            .checked_mul(size_of::<AdvisoryCallSite>())
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
    )?;
    let mut calls = Vec::with_capacity(top.num_call_site_interfaces);
    for index in 0..top.num_call_site_interfaces {
        let mut view = RadareAbi138CallSiteView::default();
        // SAFETY: index is bounded by the stable top-level view.
        callback_ok(
            unsafe { view_fn(snapshot, index, &mut view) },
            "call_site_view",
        )?;
        let variadic = wire_bool(view.variadic)?;
        let noreturn = wire_bool(view.noreturn)?;
        let complete = wire_bool(view.complete)?;
        if view.num_arguments > MAX_PARAMETERS
            || view.instruction_addr == INVALID_U64
            || view.target_addr == INVALID_U64
        {
            return Err(RadareAbi138CaptureError::InvalidAdvisoryCall);
        }
        budget.call_arguments = budget
            .call_arguments
            .checked_add(view.num_arguments)
            .filter(|total| *total <= MAX_TOTAL_CALL_ARGUMENTS)
            .ok_or(RadareAbi138CaptureError::BudgetExceeded)?;
        budget.charge(
            view.num_arguments
                .checked_mul(size_of::<RadareAbi138ParameterView>())
                .ok_or(RadareAbi138CaptureError::BudgetExceeded)?,
        )?;
        // SAFETY: call index and advertised string length are top-view bounded.
        let calling_convention = unsafe {
            copy_indexed_string(
                snapshot,
                calling_convention_fn,
                index,
                view.calling_convention_length,
                "call_site_calling_convention",
                budget,
            )
        }?;
        // SAFETY: call index and advertised string length are top-view bounded.
        let result_storage_name = unsafe {
            copy_indexed_string(
                snapshot,
                result_storage_name_fn,
                index,
                view.result_storage.name_length,
                "call_site_result_storage_name",
                budget,
            )
        }?;
        let result = match view.result_kind {
            0 | 1 if absent_storage(view.result_storage) && result_storage_name.is_empty() => {
                SourceCallResult::Void
            }
            2 if !result_storage_name.is_empty() => SourceCallResult::Register {
                storage: storage(view.result_storage)?,
            },
            _ => return Err(RadareAbi138CaptureError::InvalidEnum),
        };
        if complete && calling_convention.trim().is_empty() {
            return Err(RadareAbi138CaptureError::InvalidAdvisoryCall);
        }
        let mut arguments = Vec::with_capacity(view.num_arguments);
        for argument_index in 0..view.num_arguments {
            let mut argument = RadareAbi138ParameterView::default();
            // SAFETY: both indices are bounded by stable parent views.
            callback_ok(
                unsafe { argument_view_fn(snapshot, index, argument_index, &mut argument) },
                "call_argument_view",
            )?;
            if usize::try_from(argument.index) != Ok(argument_index)
                || argument.logical_type_id != INVALID_TYPE_ID
                || argument.carrier.kind != 0
                || argument.carrier.offset_bits != 0
                || argument.carrier.size_bits != 0
            {
                return Err(RadareAbi138CaptureError::InvalidAdvisoryCall);
            }
            // SAFETY: both indices and advertised length are parent-view bounded.
            let storage_name = unsafe {
                copy_call_argument_storage_name(
                    snapshot,
                    argument_storage_name_fn,
                    index,
                    argument_index,
                    argument.storage.name_length,
                    budget,
                )
            }?;
            if storage_name.is_empty() {
                if !absent_storage(argument.storage) {
                    return Err(RadareAbi138CaptureError::InvalidAdvisoryCall);
                }
                // A site whose argument carriers are not all named cannot
                // describe its own arguments, so no prototype is kept for it.
                arguments.clear();
                break;
            }
            arguments.push(SourceCallArgumentSpec::new(
                argument.index,
                storage(argument.storage)?,
            ));
        }
        // Only a site radare2 reported as complete, whose carriers it named in
        // full, describes what the call takes and returns.
        let prototype =
            (complete && arguments.len() == view.num_arguments).then(|| AdvisoryCallPrototype {
                calling_convention: calling_convention.clone(),
                arguments: arguments.into_boxed_slice(),
                variadic,
                noreturn,
                result,
            });
        calls.push(AdvisoryCallSite {
            // The legacy accessor transport predates the name and never
            // carried one; the flat snapshot buffer is the path that does.
            target_name: None,
            instruction_address: view.instruction_addr,
            target_address: view.target_addr,
            prototype,
        });
    }
    Ok(calls.into_boxed_slice())
}

/// Deep-copy one borrowed radare2 ABI 139/schema-12 snapshot synchronously.
///
/// This is the only public source-authority mint. It performs no symbol lookup
/// and retains no foreign pointers.
///
/// # Safety
///
/// `input.snapshot` must remain valid for this call. `input.accessors` must be
/// valid, properly aligned, and immutable while its table value is copied at
/// the start of this call; no foreign reference to the table is retained after
/// that copy. Every non-null callback must obey its declared ABI and may write
/// only within the supplied caller-owned output buffer. The snapshot must not
/// be concurrently mutated; a changed top-level view is detected and rejected,
/// but data races in foreign code cannot be made safe by Rust validation.
pub unsafe fn capture_radare_abi138(
    input: &RadareAbi138SnapshotInput,
) -> Result<OwnedFunctionSnapshot, RadareAbi138CaptureError> {
    if input.struct_size != exact_size::<RadareAbi138SnapshotInput>()? {
        return Err(RadareAbi138CaptureError::InvalidInputSize);
    }
    if input.abi_version != RADARE_SNAPSHOT_CONTRACT_VERSION
        || input.snapshot_schema_version != RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION
        || input.accessor_schema_version != RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION
    {
        return Err(RadareAbi138CaptureError::UnsupportedVersion);
    }
    if input.snapshot.is_null() || input.accessors.is_null() {
        return Err(RadareAbi138CaptureError::NullInput);
    }
    // SAFETY: validity, alignment, and immutability during this one value copy
    // are part of this function's explicit unsafe contract. The foreign table
    // pointer is never dereferenced again.
    let accessors = unsafe { input.accessors.read() };
    if accessors.struct_size != exact_size::<RadareAbi138Accessors>()?
        || accessors.abi_version != RADARE_SNAPSHOT_CONTRACT_VERSION
        || accessors.snapshot_schema_version != RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION
        || accessors.accessor_schema_version != RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION
    {
        return Err(RadareAbi138CaptureError::InvalidAccessorSize);
    }
    let snapshot_view_fn = required(accessors.snapshot_view, "snapshot_view")?;
    // SAFETY: snapshot/table validity is the caller's unsafe obligation.
    let first = unsafe { read_view(input.snapshot, snapshot_view_fn) }?;
    validate_top(&first)?;

    let arch_fn = required(accessors.arch_id, "arch_id")?;
    let cpu_fn = required(accessors.cpu_id, "cpu_id")?;
    let name_fn = required(accessors.function_name, "function_name")?;
    let mut budget = CaptureBudget::default();
    // SAFETY: each accessor writes to an exact caller-owned buffer.
    let arch_id = unsafe {
        copy_string(
            input.snapshot,
            arch_fn,
            first.arch_id_length,
            "arch_id",
            &mut budget,
        )
    }?;
    // SAFETY: each accessor writes to an exact caller-owned buffer.
    let cpu_id = unsafe {
        copy_string(
            input.snapshot,
            cpu_fn,
            first.cpu_id_length,
            "cpu_id",
            &mut budget,
        )
    }?;
    // SAFETY: each accessor writes to an exact caller-owned buffer.
    let function_name = unsafe {
        copy_string(
            input.snapshot,
            name_fn,
            first.function_name_length,
            "function_name",
            &mut budget,
        )
    }?;
    if arch_id.is_empty() || cpu_id.is_empty() {
        return Err(RadareAbi138CaptureError::InvalidMachine);
    }
    let machine = MachineProfile {
        arch_id: arch_id.into_boxed_str(),
        cpu_id: cpu_id.into_boxed_str(),
        bits: u32::try_from(first.bits).map_err(|_| RadareAbi138CaptureError::InvalidMachine)?,
        endianness: match first.endian {
            RADARE_ENDIAN_LITTLE => SourceEndianness::Little,
            RADARE_ENDIAN_BIG => SourceEndianness::Big,
            _ => return Err(RadareAbi138CaptureError::InvalidMachine),
        },
    };
    let revision = first.revision_identity.to_le_bytes();
    // SAFETY: all child accesses are bounded by the first stable top view.
    let image = unsafe { capture_image(input.snapshot, &accessors, &first, &mut budget) }?;
    // SAFETY: advisory call count is bounded by the first stable top view.
    let advisory_calls =
        unsafe { capture_advisory_calls(input.snapshot, &accessors, &first, &mut budget) }?;
    // SAFETY: interface child counts are validated before each access.
    let captured_interface = if first.capabilities & RADARE_CAP_EXACT_FUNCTION_INTERFACE != 0 {
        Some(unsafe {
            capture_interface(input.snapshot, &accessors, &first, &revision, &mut budget)
        }?)
    } else {
        None
    };
    // SAFETY: the interface view is a fixed-size out-parameter read under the
    // same stable top view as every other child access.
    let machine_roles = unsafe { capture_machine_roles(input.snapshot, &accessors, &first) }?;
    let function_interface = captured_interface
        .as_ref()
        .map(|(interface, _, _)| interface.clone());
    let (parameter_names, stack_slot_names) = captured_interface
        .map(|(_, parameter_names, slot_names)| (parameter_names, slot_names))
        .unwrap_or_default();

    // Repeat the source-owned top view after every deep copy. Minting authority
    // is forbidden if any captured count, capability, range, or identity moved.
    // SAFETY: callback/table validity remains live for the duration of the call.
    let second = unsafe { read_view(input.snapshot, snapshot_view_fn) }?;
    if second != first {
        return Err(RadareAbi138CaptureError::SnapshotChanged);
    }
    validate_top(&second)?;

    let captured_fields = CapturedSourceFields {
        bounded_function_image: true,
        function_interface: function_interface.is_some(),
        exact_function_types: first.capabilities & RADARE_CAP_EXACT_FUNCTION_TYPES != 0,
        exact_stack_slot_roles: first.capabilities & RADARE_CAP_EXACT_STACK_SLOT_ROLES != 0,
        return_address_storage: function_interface.is_some()
            && first.capabilities & RADARE_CAP_RETURN_ADDRESS_STORAGE != 0,
        stack_pointer_storage: function_interface.is_some()
            && first.capabilities & RADARE_CAP_STACK_POINTER_STORAGE != 0,
        return_mechanism: function_interface.is_some()
            && first.capabilities & RADARE_CAP_EXACT_RETURN_MECHANISM != 0,
        frame_pointer_storage: function_interface.is_some()
            && first.capabilities & RADARE_CAP_EXACT_FRAME_POINTER_STORAGE != 0,
        stack_allocation_contract: function_interface.is_some()
            && first.capabilities & RADARE_CAP_EXACT_STACK_ALLOCATION_CONTRACT != 0,
    };
    OwnedFunctionSnapshot::from_captured_parts(
        machine,
        FunctionIdentity {
            address: first.function_addr,
        },
        FunctionPresentation {
            display_name: function_name.into_boxed_str(),
            parameter_names,
            stack_slot_names,
            // The direct capture does not read the recovered prototype; the
            // wire transport is the path that carries it.
            signature: None,
            callee_signatures: Box::new([]),
        },
        image,
        advisory_calls,
        Box::from(revision),
        function_interface,
        machine_roles,
        // The accessor transport never carried convention candidates.
        SourceConventionSlots::new("", [], None)
            .map_err(|_| RadareAbi138CaptureError::InvalidMachine)?,
        captured_fields,
        DiagnosticIdentity(first.revision_identity),
    )
    .map_err(Into::into)
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;

    struct ReturnMechanismFixture {
        first: RadareAbi138ReturnMechanismView,
        second: RadareAbi138ReturnMechanismView,
        calls: Cell<usize>,
        status: u8,
    }

    struct FramePointerFixture {
        first: RadareAbi138RegisterStorageView,
        second: RadareAbi138RegisterStorageView,
        first_name: &'static [u8],
        second_name: &'static [u8],
        view_calls: Cell<usize>,
        name_calls: Cell<usize>,
        status: u8,
    }

    struct StackAllocationFixture {
        first: RadareAbi138StackAllocationContractView,
        second: RadareAbi138StackAllocationContractView,
        calls: Cell<usize>,
        status: u8,
    }

    unsafe extern "C" fn return_mechanism_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138ReturnMechanismView,
    ) -> u8 {
        // SAFETY: tests pass exact pointers to live fixture/output values.
        let fixture = unsafe { &*snapshot.cast::<ReturnMechanismFixture>() };
        let call = fixture.calls.get();
        fixture.calls.set(call.saturating_add(1));
        let view = if call == 0 {
            fixture.first
        } else {
            fixture.second
        };
        // SAFETY: the production reader supplies one valid output object.
        unsafe { out.write(view) };
        fixture.status
    }

    unsafe extern "C" fn frame_pointer_storage_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138RegisterStorageView,
    ) -> u8 {
        // SAFETY: tests pass exact pointers to live fixture/output values.
        let fixture = unsafe { &*snapshot.cast::<FramePointerFixture>() };
        let call = fixture.view_calls.get();
        fixture.view_calls.set(call.saturating_add(1));
        let view = if call == 0 {
            fixture.first
        } else {
            fixture.second
        };
        // SAFETY: the production reader supplies one valid output object.
        unsafe { out.write(view) };
        fixture.status
    }

    unsafe extern "C" fn frame_pointer_storage_name(
        snapshot: *const c_void,
        kind: i32,
        out: *mut u8,
        capacity: usize,
    ) -> u8 {
        // SAFETY: tests pass an exact pointer to a live fixture.
        let fixture = unsafe { &*snapshot.cast::<FramePointerFixture>() };
        if kind != 3 {
            return 0;
        }
        let call = fixture.name_calls.get();
        fixture.name_calls.set(call.saturating_add(1));
        let name = if call == 0 {
            fixture.first_name
        } else {
            fixture.second_name
        };
        if capacity != name.len().saturating_add(1) {
            return 0;
        }
        // SAFETY: the production reader supplies exactly `name.len() + 1`
        // writable bytes.
        unsafe {
            std::ptr::copy_nonoverlapping(name.as_ptr(), out, name.len());
            out.add(name.len()).write(0);
        }
        fixture.status
    }

    unsafe extern "C" fn stack_allocation_contract_view(
        snapshot: *const c_void,
        out: *mut RadareAbi138StackAllocationContractView,
    ) -> u8 {
        // SAFETY: tests pass exact pointers to live fixture/output values.
        let fixture = unsafe { &*snapshot.cast::<StackAllocationFixture>() };
        let call = fixture.calls.get();
        fixture.calls.set(call.saturating_add(1));
        let view = if call == 0 {
            fixture.first
        } else {
            fixture.second
        };
        // SAFETY: the production reader supplies one valid output object.
        unsafe { out.write(view) };
        fixture.status
    }

    fn register(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn exact_return_interface() -> SourceFunctionInterface {
        SourceFunctionInterface::new_exact(
            b"return-mechanism-revision".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(register(16)))
        .and_then(|interface| interface.with_stack_pointer_storage(register(24)))
        .expect("exact return interface")
    }

    fn mechanism_accessors(callback: Option<RadareReturnMechanismViewFn>) -> RadareAbi138Accessors {
        RadareAbi138Accessors {
            return_mechanism_view: callback,
            ..RadareAbi138Accessors::default()
        }
    }

    fn frame_pointer_accessors(
        callback: Option<RadareFramePointerStorageViewFn>,
    ) -> RadareAbi138Accessors {
        RadareAbi138Accessors {
            interface_storage_name: Some(frame_pointer_storage_name),
            frame_pointer_storage_view: callback,
            ..RadareAbi138Accessors::default()
        }
    }

    fn stack_allocation_accessors(
        callback: Option<RadareStackAllocationContractViewFn>,
    ) -> RadareAbi138Accessors {
        RadareAbi138Accessors {
            stack_allocation_contract_view: callback,
            ..RadareAbi138Accessors::default()
        }
    }

    fn frame_pointer_view(offset: u64) -> RadareAbi138RegisterStorageView {
        RadareAbi138RegisterStorageView {
            name_length: 3,
            offset,
            size: 8,
        }
    }

    fn stacked_view() -> RadareAbi138ReturnMechanismView {
        RadareAbi138ReturnMechanismView {
            kind: 1,
            stack_offset: 0,
            slot_size_bytes: 8,
            stack_pointer_delta_bytes: 8,
        }
    }

    fn lower_stack_allocation_view() -> RadareAbi138StackAllocationContractView {
        RadareAbi138StackAllocationContractView {
            growth: 1,
            implicit_active_sp_bytes: 128,
        }
    }

    fn valid_top(capabilities: u64) -> RadareAbi138SnapshotView {
        RadareAbi138SnapshotView {
            schema_version: RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
            struct_size: u32::try_from(size_of::<RadareAbi138SnapshotView>())
                .expect("ABI view size fits u32"),
            capabilities,
            function_size: 1,
            bits: 64,
            endian: RADARE_ENDIAN_LITTLE,
            arch_id_length: 3,
            cpu_id_length: 3,
            revision_identity: 1,
            num_blocks: 1,
            total_source_bytes: 1,
            ..RadareAbi138SnapshotView::default()
        }
    }

    fn null_input() -> RadareAbi138SnapshotInput {
        RadareAbi138SnapshotInput {
            struct_size: u32::try_from(size_of::<RadareAbi138SnapshotInput>())
                .expect("ABI input size fits u32"),
            abi_version: RADARE_SNAPSHOT_CONTRACT_VERSION,
            snapshot_schema_version: RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
            accessor_schema_version: RADARE_SNAPSHOT_ACCESSOR_SCHEMA_VERSION,
            snapshot: std::ptr::null(),
            accessors: std::ptr::null(),
        }
    }

    #[test]
    fn malformed_header_is_rejected_before_foreign_access() {
        let mut input = null_input();
        input.struct_size = 0;
        // SAFETY: malformed size is rejected before either null pointer is read.
        assert_eq!(
            unsafe { capture_radare_abi138(&input) },
            Err(RadareAbi138CaptureError::InvalidInputSize)
        );

        let mut input = null_input();
        input.snapshot_schema_version = 10;
        // SAFETY: malformed version is rejected before either null pointer is read.
        assert_eq!(
            unsafe { capture_radare_abi138(&input) },
            Err(RadareAbi138CaptureError::UnsupportedVersion)
        );

        let mut input = null_input();
        input.accessor_schema_version = 1;
        // SAFETY: malformed version is rejected before either null pointer is read.
        assert_eq!(
            unsafe { capture_radare_abi138(&input) },
            Err(RadareAbi138CaptureError::UnsupportedVersion)
        );
    }

    #[test]
    fn null_foreign_handles_are_rejected() {
        let input = null_input();
        // SAFETY: null handles are explicitly accepted as malformed input and
        // rejected before dereference.
        assert_eq!(
            unsafe { capture_radare_abi138(&input) },
            Err(RadareAbi138CaptureError::NullInput)
        );
    }

    #[test]
    fn malformed_accessor_table_is_rejected_after_one_owned_copy() {
        let accessors = RadareAbi138Accessors::default();
        let mut input = null_input();
        input.snapshot = std::ptr::NonNull::<u8>::dangling().as_ptr().cast();
        input.accessors = &accessors;
        // SAFETY: the local accessor table is valid and immutable for the copy;
        // its zero header is rejected before the opaque snapshot is accessed.
        assert_eq!(
            unsafe { capture_radare_abi138(&input) },
            Err(RadareAbi138CaptureError::InvalidAccessorSize)
        );
    }

    #[test]
    fn return_mechanism_layout_is_append_only_and_defaults_inactive() {
        let view = RadareAbi138ReturnMechanismView::default();
        assert_eq!(view.kind, 0);
        assert_eq!(view.stack_offset, 0);
        assert_eq!(view.slot_size_bytes, 0);
        assert_eq!(view.stack_pointer_delta_bytes, 0);
        let accessors = RadareAbi138Accessors::default();
        assert!(accessors.return_mechanism_view.is_none());
        assert_eq!(
            std::mem::offset_of!(RadareAbi138Accessors, return_mechanism_view),
            std::mem::offset_of!(RadareAbi138Accessors, external_exit)
                + size_of::<Option<RadareExternalExitFn>>()
        );
    }

    #[test]
    fn frame_pointer_layout_is_append_only_and_defaults_inactive() {
        let accessors = RadareAbi138Accessors::default();
        assert!(accessors.frame_pointer_storage_view.is_none());
        assert_eq!(
            std::mem::offset_of!(RadareAbi138Accessors, frame_pointer_storage_view),
            std::mem::offset_of!(RadareAbi138Accessors, return_mechanism_view)
                + size_of::<Option<RadareReturnMechanismViewFn>>()
        );
    }

    #[test]
    fn machine_carrier_capabilities_do_not_require_an_exact_interface() {
        // radare2 resolves the return-address and stack-pointer carriers from
        // register aliases, which it knows with or without debug information.
        // Advertising them must therefore not require the exact-interface
        // capability, otherwise every function without an ABI loses its
        // machine carriers as well.
        let machine_only = RADARE_CAP_REVISION
            | RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE
            | RADARE_CAP_RETURN_ADDRESS_STORAGE
            | RADARE_CAP_STACK_POINTER_STORAGE;
        assert_eq!(validate_top(&valid_top(machine_only)), Ok(()));
        assert_eq!(machine_only & RADARE_CAP_EXACT_FUNCTION_INTERFACE, 0);
    }

    #[test]
    fn machine_roles_reject_a_carrier_the_capability_did_not_advertise() {
        assert_eq!(
            SourceMachineRoles::new(
                Some(CanonicalStorageId {
                    space: CanonicalStorageSpace::Register,
                    offset: 0,
                    size: 0,
                }),
                None,
            ),
            Err(SourceMachineRolesError::InvalidRegisterStorage)
        );
        let roles = SourceMachineRoles::new(
            Some(CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: 16,
                size: 8,
            }),
            None,
        )
        .expect("a well formed return address carrier is accepted");
        assert!(!roles.is_empty());
        assert!(roles.stack_pointer_storage().is_none());
    }

    #[test]
    fn frame_pointer_capability_requires_exact_interface_and_return_storages() {
        let dependencies = RADARE_CAP_REVISION
            | RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE
            | RADARE_CAP_EXACT_FUNCTION_INTERFACE
            | RADARE_CAP_RETURN_ADDRESS_STORAGE
            | RADARE_CAP_STACK_POINTER_STORAGE
            | RADARE_CAP_EXACT_FRAME_POINTER_STORAGE;
        assert_eq!(validate_top(&valid_top(dependencies)), Ok(()));
        for dependency in [
            RADARE_CAP_EXACT_FUNCTION_INTERFACE,
            RADARE_CAP_RETURN_ADDRESS_STORAGE,
            RADARE_CAP_STACK_POINTER_STORAGE,
        ] {
            assert_eq!(
                validate_top(&valid_top(dependencies & !dependency)),
                Err(RadareAbi138CaptureError::InvalidCapabilities)
            );
        }
        assert_eq!(dependencies & RADARE_CAP_STACK_SLOTS, 0);
        assert_eq!(dependencies & RADARE_CAP_EXACT_STACK_SLOT_ROLES, 0);
    }

    #[test]
    fn stack_allocation_contract_layout_is_append_only_and_defaults_inactive() {
        let view = RadareAbi138StackAllocationContractView::default();
        assert_eq!(view.growth, 0);
        assert_eq!(view.implicit_active_sp_bytes, 0);
        assert_eq!(
            std::mem::offset_of!(
                RadareAbi138StackAllocationContractView,
                implicit_active_sp_bytes
            ),
            size_of::<i32>()
        );
        assert_eq!(
            size_of::<RadareAbi138StackAllocationContractView>(),
            size_of::<i32>() + size_of::<u32>()
        );
        let accessors = RadareAbi138Accessors::default();
        assert!(accessors.stack_allocation_contract_view.is_none());
        assert_eq!(
            std::mem::offset_of!(RadareAbi138Accessors, stack_allocation_contract_view),
            std::mem::offset_of!(RadareAbi138Accessors, frame_pointer_storage_view)
                + size_of::<Option<RadareFramePointerStorageViewFn>>()
        );
    }

    #[test]
    fn previous_stack_allocation_snapshot_schema_is_rejected() {
        let capabilities = RADARE_CAP_REVISION
            | RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE
            | RADARE_CAP_EXACT_FUNCTION_INTERFACE
            | RADARE_CAP_STACK_POINTER_STORAGE
            | RADARE_CAP_EXACT_STACK_ALLOCATION_CONTRACT;
        let mut top = valid_top(capabilities);
        top.schema_version = 10;
        assert_eq!(
            validate_top(&top),
            Err(RadareAbi138CaptureError::UnsupportedVersion)
        );
    }

    #[test]
    fn stack_allocation_contract_capability_requires_exact_interface_and_sp() {
        let dependencies = RADARE_CAP_REVISION
            | RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE
            | RADARE_CAP_EXACT_FUNCTION_INTERFACE
            | RADARE_CAP_STACK_POINTER_STORAGE
            | RADARE_CAP_EXACT_STACK_ALLOCATION_CONTRACT;
        assert_eq!(validate_top(&valid_top(dependencies)), Ok(()));
        for dependency in [
            RADARE_CAP_EXACT_FUNCTION_INTERFACE,
            RADARE_CAP_STACK_POINTER_STORAGE,
        ] {
            assert_eq!(
                validate_top(&valid_top(dependencies & !dependency)),
                Err(RadareAbi138CaptureError::InvalidCapabilities)
            );
        }
    }

    #[test]
    fn exact_stack_allocation_contract_is_read_twice_and_bound() {
        for implicit_active_sp_bytes in [0, 128, u32::MAX] {
            let view = RadareAbi138StackAllocationContractView {
                growth: 1,
                implicit_active_sp_bytes,
            };
            let fixture = StackAllocationFixture {
                first: view,
                second: view,
                calls: Cell::new(0),
                status: 1,
            };
            let accessors = stack_allocation_accessors(Some(stack_allocation_contract_view));
            // SAFETY: callback receives a live fixture for both synchronous reads.
            let interface = unsafe {
                capture_stack_allocation_contract(
                    (&fixture as *const StackAllocationFixture).cast(),
                    &accessors,
                    true,
                    exact_return_interface(),
                )
            }
            .expect("exact stack allocation contract");
            assert_eq!(fixture.calls.get(), 2);
            assert_eq!(
                interface.stack_allocation_contract(),
                Some(
                    SourceStackAllocationContract::with_implicit_active_sp_bytes(
                        SourceStackGrowth::LowerAddresses,
                        implicit_active_sp_bytes,
                    )
                )
            );
        }
    }

    #[test]
    fn inactive_stack_allocation_contract_never_invokes_accessor() {
        let fixture = StackAllocationFixture {
            first: lower_stack_allocation_view(),
            second: lower_stack_allocation_view(),
            calls: Cell::new(0),
            status: 0,
        };
        let accessors = stack_allocation_accessors(Some(stack_allocation_contract_view));
        // SAFETY: inactive contracts must not invoke a foreign callback.
        let interface = unsafe {
            capture_stack_allocation_contract(
                (&fixture as *const StackAllocationFixture).cast(),
                &accessors,
                false,
                exact_return_interface(),
            )
        }
        .expect("inactive stack allocation contract");
        assert_eq!(fixture.calls.get(), 0);
        assert_eq!(interface.stack_allocation_contract(), None);
    }

    #[test]
    fn stack_allocation_contract_refuses_missing_unknown_failed_and_mutated_payloads() {
        // SAFETY: active missing callback is rejected before snapshot access.
        assert_eq!(
            unsafe {
                capture_stack_allocation_contract(
                    std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
                    &RadareAbi138Accessors::default(),
                    true,
                    exact_return_interface(),
                )
            },
            Err(RadareAbi138CaptureError::MissingAccessor(
                "stack_allocation_contract_view"
            ))
        );

        for (first, second, status, expected) in [
            (
                RadareAbi138StackAllocationContractView {
                    growth: 0,
                    implicit_active_sp_bytes: 0,
                },
                RadareAbi138StackAllocationContractView {
                    growth: 0,
                    implicit_active_sp_bytes: 0,
                },
                1,
                RadareAbi138CaptureError::InvalidEnum,
            ),
            (
                RadareAbi138StackAllocationContractView {
                    growth: 3,
                    implicit_active_sp_bytes: 0,
                },
                RadareAbi138StackAllocationContractView {
                    growth: 3,
                    implicit_active_sp_bytes: 0,
                },
                1,
                RadareAbi138CaptureError::InvalidEnum,
            ),
            (
                lower_stack_allocation_view(),
                lower_stack_allocation_view(),
                0,
                RadareAbi138CaptureError::AccessorFailed("stack_allocation_contract_view"),
            ),
            (
                lower_stack_allocation_view(),
                RadareAbi138StackAllocationContractView {
                    growth: 2,
                    implicit_active_sp_bytes: 128,
                },
                1,
                RadareAbi138CaptureError::SnapshotChanged,
            ),
            (
                lower_stack_allocation_view(),
                RadareAbi138StackAllocationContractView {
                    growth: 1,
                    implicit_active_sp_bytes: 127,
                },
                1,
                RadareAbi138CaptureError::SnapshotChanged,
            ),
        ] {
            let fixture = StackAllocationFixture {
                first,
                second,
                calls: Cell::new(0),
                status,
            };
            let accessors = stack_allocation_accessors(Some(stack_allocation_contract_view));
            // SAFETY: callback receives a live fixture for synchronous reads.
            assert_eq!(
                unsafe {
                    capture_stack_allocation_contract(
                        (&fixture as *const StackAllocationFixture).cast(),
                        &accessors,
                        true,
                        exact_return_interface(),
                    )
                },
                Err(expected)
            );
        }
    }

    #[test]
    fn exact_frame_pointer_is_read_twice_and_bound_without_stack_slots() {
        let fixture = FramePointerFixture {
            first: frame_pointer_view(32),
            second: frame_pointer_view(32),
            first_name: b"rbp",
            second_name: b"rbp",
            view_calls: Cell::new(0),
            name_calls: Cell::new(0),
            status: 1,
        };
        let accessors = frame_pointer_accessors(Some(frame_pointer_storage_view));
        let mut budget = CaptureBudget::default();
        // SAFETY: fixture and callbacks remain live for both synchronous reads.
        let interface = unsafe {
            capture_frame_pointer_storage(
                (&fixture as *const FramePointerFixture).cast(),
                &accessors,
                true,
                exact_return_interface(),
                &mut budget,
            )
        }
        .expect("exact frame pointer");
        assert_eq!(interface.exact_frame_pointer_storage(), Some(register(32)));
        assert_eq!(fixture.view_calls.get(), 2);
        assert_eq!(fixture.name_calls.get(), 2);
    }

    #[test]
    fn inactive_frame_pointer_never_invokes_accessors() {
        let fixture = FramePointerFixture {
            first: frame_pointer_view(32),
            second: frame_pointer_view(32),
            first_name: b"rbp",
            second_name: b"rbp",
            view_calls: Cell::new(0),
            name_calls: Cell::new(0),
            status: 1,
        };
        let accessors = frame_pointer_accessors(Some(frame_pointer_storage_view));
        let mut budget = CaptureBudget::default();
        // SAFETY: inactive capture never invokes either foreign callback.
        let interface = unsafe {
            capture_frame_pointer_storage(
                (&fixture as *const FramePointerFixture).cast(),
                &accessors,
                false,
                exact_return_interface(),
                &mut budget,
            )
        }
        .expect("inactive frame pointer");
        assert_eq!(interface.exact_frame_pointer_storage(), None);
        assert_eq!(fixture.view_calls.get(), 0);
        assert_eq!(fixture.name_calls.get(), 0);
    }

    #[test]
    fn frame_pointer_refuses_view_or_name_mutation() {
        for fixture in [
            FramePointerFixture {
                first: frame_pointer_view(32),
                second: frame_pointer_view(40),
                first_name: b"rbp",
                second_name: b"rbp",
                view_calls: Cell::new(0),
                name_calls: Cell::new(0),
                status: 1,
            },
            FramePointerFixture {
                first: frame_pointer_view(32),
                second: frame_pointer_view(32),
                first_name: b"rbp",
                second_name: b"ebp",
                view_calls: Cell::new(0),
                name_calls: Cell::new(0),
                status: 1,
            },
        ] {
            let accessors = frame_pointer_accessors(Some(frame_pointer_storage_view));
            let mut budget = CaptureBudget::default();
            // SAFETY: fixture and callbacks remain live for both synchronous reads.
            assert_eq!(
                unsafe {
                    capture_frame_pointer_storage(
                        (&fixture as *const FramePointerFixture).cast(),
                        &accessors,
                        true,
                        exact_return_interface(),
                        &mut budget,
                    )
                },
                Err(RadareAbi138CaptureError::SnapshotChanged)
            );
        }
    }

    #[test]
    fn active_frame_pointer_requires_callback_and_checked_geometry() {
        let mut budget = CaptureBudget::default();
        // SAFETY: active capture rejects the absent callback before using the
        // dangling snapshot value.
        assert_eq!(
            unsafe {
                capture_frame_pointer_storage(
                    std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
                    &frame_pointer_accessors(None),
                    true,
                    exact_return_interface(),
                    &mut budget,
                )
            },
            Err(RadareAbi138CaptureError::MissingAccessor(
                "frame_pointer_storage_view"
            ))
        );

        let fixture = FramePointerFixture {
            first: frame_pointer_view(16),
            second: frame_pointer_view(16),
            first_name: b"rip",
            second_name: b"rip",
            view_calls: Cell::new(0),
            name_calls: Cell::new(0),
            status: 1,
        };
        let accessors = frame_pointer_accessors(Some(frame_pointer_storage_view));
        let mut budget = CaptureBudget::default();
        // SAFETY: fixture and callbacks remain live for both synchronous reads.
        assert_eq!(
            unsafe {
                capture_frame_pointer_storage(
                    (&fixture as *const FramePointerFixture).cast(),
                    &accessors,
                    true,
                    exact_return_interface(),
                    &mut budget,
                )
            },
            Err(RadareAbi138CaptureError::InvalidInterface)
        );
    }

    #[test]
    fn return_mechanism_capability_requires_all_exact_dependencies() {
        let dependencies = RADARE_CAP_REVISION
            | RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE
            | RADARE_CAP_EXACT_FUNCTION_INTERFACE
            | RADARE_CAP_STACK_SLOTS
            | RADARE_CAP_EXACT_STACK_SLOT_ROLES
            | RADARE_CAP_RETURN_ADDRESS_STORAGE
            | RADARE_CAP_STACK_POINTER_STORAGE
            | RADARE_CAP_EXACT_RETURN_MECHANISM;
        assert_eq!(validate_top(&valid_top(dependencies)), Ok(()));
        for dependency in [
            RADARE_CAP_EXACT_FUNCTION_INTERFACE,
            RADARE_CAP_STACK_SLOTS,
            RADARE_CAP_EXACT_STACK_SLOT_ROLES,
            RADARE_CAP_RETURN_ADDRESS_STORAGE,
            RADARE_CAP_STACK_POINTER_STORAGE,
        ] {
            assert_eq!(
                validate_top(&valid_top(dependencies & !dependency)),
                Err(RadareAbi138CaptureError::InvalidCapabilities)
            );
        }
        assert_eq!(
            validate_top(&valid_top(dependencies | (1 << 18))),
            Err(RadareAbi138CaptureError::InvalidCapabilities)
        );
    }

    #[test]
    fn exact_return_mechanism_is_read_twice_and_bound() {
        let fixture = ReturnMechanismFixture {
            first: stacked_view(),
            second: stacked_view(),
            calls: Cell::new(0),
            status: 1,
        };
        let accessors = mechanism_accessors(Some(return_mechanism_view));
        // SAFETY: callback receives a live fixture for both synchronous reads.
        let interface = unsafe {
            capture_return_mechanism(
                (&fixture as *const ReturnMechanismFixture).cast(),
                &accessors,
                true,
                exact_return_interface(),
                8,
            )
        }
        .expect("exact stacked return mechanism");
        assert_eq!(fixture.calls.get(), 2);
        assert_eq!(
            interface.return_mechanism(),
            Some(SourceReturnMechanism::Stacked {
                stack_offset: 0,
                slot_size_bytes: 8,
                stack_pointer_delta_bytes: 8,
                address_size_bytes: 8,
            })
        );
    }

    #[test]
    fn inactive_return_mechanism_never_invokes_accessor() {
        let fixture = ReturnMechanismFixture {
            first: stacked_view(),
            second: stacked_view(),
            calls: Cell::new(0),
            status: 0,
        };
        let accessors = mechanism_accessors(Some(return_mechanism_view));
        // SAFETY: inactive ARM/LR-style contracts must not invoke the callback.
        let interface = unsafe {
            capture_return_mechanism(
                (&fixture as *const ReturnMechanismFixture).cast(),
                &accessors,
                false,
                exact_return_interface(),
                8,
            )
        }
        .expect("inactive register-return mechanism");
        assert_eq!(fixture.calls.get(), 0);
        assert_eq!(interface.return_mechanism(), None);
    }

    #[test]
    fn return_mechanism_refuses_missing_unknown_and_failed_payloads() {
        // SAFETY: no callback is invoked for an inactive absent mechanism.
        assert_eq!(
            unsafe {
                capture_return_mechanism(
                    std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
                    &RadareAbi138Accessors::default(),
                    false,
                    exact_return_interface(),
                    8,
                )
            }
            .expect("inactive absent mechanism")
            .return_mechanism(),
            None
        );
        // SAFETY: active missing callback is rejected before snapshot access.
        assert_eq!(
            unsafe {
                capture_return_mechanism(
                    std::ptr::NonNull::<u8>::dangling().as_ptr().cast(),
                    &RadareAbi138Accessors::default(),
                    true,
                    exact_return_interface(),
                    8,
                )
            },
            Err(RadareAbi138CaptureError::MissingAccessor(
                "return_mechanism_view"
            ))
        );

        for (view, status, expected) in [
            (
                RadareAbi138ReturnMechanismView {
                    kind: 2,
                    ..stacked_view()
                },
                1,
                RadareAbi138CaptureError::InvalidEnum,
            ),
            (
                stacked_view(),
                0,
                RadareAbi138CaptureError::AccessorFailed("return_mechanism_view"),
            ),
        ] {
            let fixture = ReturnMechanismFixture {
                first: view,
                second: view,
                calls: Cell::new(0),
                status,
            };
            let accessors = mechanism_accessors(Some(return_mechanism_view));
            // SAFETY: callback receives a live fixture for synchronous reads.
            assert_eq!(
                unsafe {
                    capture_return_mechanism(
                        (&fixture as *const ReturnMechanismFixture).cast(),
                        &accessors,
                        true,
                        exact_return_interface(),
                        8,
                    )
                },
                Err(expected)
            );
        }
    }

    #[test]
    fn return_mechanism_refuses_mutation_and_malformed_geometry() {
        let mutated = ReturnMechanismFixture {
            first: stacked_view(),
            second: RadareAbi138ReturnMechanismView {
                stack_pointer_delta_bytes: 4,
                ..stacked_view()
            },
            calls: Cell::new(0),
            status: 1,
        };
        let accessors = mechanism_accessors(Some(return_mechanism_view));
        // SAFETY: callback receives a live fixture for synchronous reads.
        assert_eq!(
            unsafe {
                capture_return_mechanism(
                    (&mutated as *const ReturnMechanismFixture).cast(),
                    &accessors,
                    true,
                    exact_return_interface(),
                    8,
                )
            },
            Err(RadareAbi138CaptureError::SnapshotChanged)
        );

        for malformed in [
            RadareAbi138ReturnMechanismView {
                stack_offset: 1,
                ..stacked_view()
            },
            RadareAbi138ReturnMechanismView {
                slot_size_bytes: 4,
                ..stacked_view()
            },
            RadareAbi138ReturnMechanismView {
                stack_pointer_delta_bytes: 4,
                ..stacked_view()
            },
        ] {
            let fixture = ReturnMechanismFixture {
                first: malformed,
                second: malformed,
                calls: Cell::new(0),
                status: 1,
            };
            // SAFETY: callback receives a live fixture for synchronous reads.
            assert_eq!(
                unsafe {
                    capture_return_mechanism(
                        (&fixture as *const ReturnMechanismFixture).cast(),
                        &accessors,
                        true,
                        exact_return_interface(),
                        8,
                    )
                },
                Err(RadareAbi138CaptureError::InvalidInterface)
            );
        }
    }

    #[test]
    fn advisory_partial_payload_does_not_claim_exact_interface_authority() {
        let view = RadareAbi138SnapshotView {
            schema_version: RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
            struct_size: u32::try_from(size_of::<RadareAbi138SnapshotView>())
                .expect("ABI view size fits u32"),
            capabilities: RADARE_CAP_TYPES
                | RADARE_CAP_REVISION
                | RADARE_CAP_RETURN_ADDRESS_STORAGE
                | RADARE_CAP_STACK_POINTER_STORAGE
                | RADARE_CAP_OWNED_BOUNDED_FUNCTION_IMAGE,
            function_size: 1,
            bits: 64,
            endian: RADARE_ENDIAN_LITTLE,
            arch_id_length: 3,
            cpu_id_length: 3,
            revision_identity: 1,
            num_types: 1,
            num_blocks: 1,
            total_source_bytes: 1,
            ..RadareAbi138SnapshotView::default()
        };
        assert_eq!(validate_top(&view), Ok(()));
        assert_eq!(view.capabilities & RADARE_CAP_EXACT_FUNCTION_INTERFACE, 0);
        assert_eq!(view.capabilities & RADARE_CAP_EXACT_FUNCTION_TYPES, 0);
    }
}
