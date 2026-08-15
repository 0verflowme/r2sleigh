use libloading::Library;
use std::ffi::c_void;
use std::mem::size_of;
use std::ptr;

pub const STATUS_OK: u32 = 0;
pub const ANALYSIS_BLOCK_ESIL: u32 = 1;
pub const ANALYSIS_BLOCK_MEMORY: u32 = 5;
pub const ANALYSIS_BLOCK_SSA: u32 = 7;
pub const ANALYSIS_BLOCK_DEFUSE: u32 = 8;

#[repr(C)]
#[derive(Clone, Copy)]
struct StringView {
    data: *const u8,
    len: usize,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct ByteView {
    data: *const u8,
    len: usize,
}

#[repr(C)]
struct AnalysisRenderRequest {
    kind: u32,
    context: *const c_void,
    blocks: *const *const c_void,
    num_blocks: usize,
    op_index: usize,
    argument: StringView,
}

type ContextCreate = unsafe extern "C" fn(StringView, *mut *mut c_void) -> u32;
type ContextFree = unsafe extern "C" fn(*mut c_void) -> u32;
type ContextLoaded = unsafe extern "C" fn(*const c_void, *mut u32) -> u32;
type ContextError = unsafe extern "C" fn(*const c_void, *mut ByteView) -> u32;
type ContextMetadata = unsafe extern "C" fn(*mut c_void, u32) -> u32;
type LiftInstruction = unsafe extern "C" fn(*mut c_void, ByteView, u64, *mut *mut c_void) -> u32;
type BlockFree = unsafe extern "C" fn(*mut c_void) -> u32;
type BlockValidate = unsafe extern "C" fn(*mut c_void, *const c_void) -> u32;
type BlockOpCount = unsafe extern "C" fn(*const c_void, *mut usize) -> u32;
type OwnedBytesView = unsafe extern "C" fn(*const c_void, *mut ByteView) -> u32;
type OwnedBytesFree = unsafe extern "C" fn(*mut c_void) -> u32;
type AnalysisRender = unsafe extern "C" fn(*const AnalysisRenderRequest, *mut *mut c_void) -> u32;

#[repr(C)]
struct ApiV2 {
    abi_version: u32,
    struct_size: u32,
    capabilities: u64,
    radare_abi_version: u32,
    session_config_size: u32,
    request_size: u32,
    engine_request_payload_size: u32,
    byte_view_size: u32,
    string_view_size: u32,
    phase_timing_size: u32,
    response_info_size: u32,
    switch_case_size: u32,
    direct_call_identity_size: u32,
    analysis_render_request_size: u32,
    analysis_query_request_size: u32,
    analysis_result_view_size: u32,
    data_ref_size: u32,
    data_ref_schema_version: u32,
    planner_query_request_size: u32,
    planner_query_response_size: u32,
    radare_snapshot_input_size: u32,
    radare_accessors_size: u32,
    session_create: usize,
    session_free: usize,
    session_cancel: usize,
    session_reset_cancellation: usize,
    execute: usize,
    response_bytes: usize,
    response_info: usize,
    response_free: usize,
    session_error: usize,
    lift_context_create: ContextCreate,
    lift_context_free: ContextFree,
    lift_context_is_loaded: ContextLoaded,
    lift_context_arch_name: usize,
    lift_context_error: ContextError,
    lift_last_error: usize,
    lift_context_reg_profile: usize,
    lift_instruction: LiftInstruction,
    lift_block: usize,
    lift_context_set_semantic_metadata: ContextMetadata,
    lift_block_free: BlockFree,
    lift_block_validate: BlockValidate,
    lift_block_set_switch_info: usize,
    lift_block_op_count: BlockOpCount,
    lift_block_direct_call_identity: usize,
    lift_block_size: usize,
    lift_block_addr: usize,
    lift_block_mnemonic: usize,
    lift_block_type: usize,
    lift_block_jump: usize,
    lift_block_fail: usize,
    owned_bytes_view: OwnedBytesView,
    owned_bytes_free: OwnedBytesFree,
    analysis_render: AnalysisRender,
    analysis_query: usize,
    analysis_result_view: usize,
    analysis_result_free: usize,
    engine_cache_reset: usize,
    planner_query: usize,
}

pub struct V2Library {
    _library: Library,
    api: *const ApiV2,
}

impl V2Library {
    pub unsafe fn open(path: &str) -> Self {
        let library = unsafe { Library::new(path) }.expect("load plugin");
        let api_fn: libloading::Symbol<unsafe extern "C" fn() -> *const ApiV2> =
            unsafe { library.get(b"r2sleigh_api_v2") }.expect("load V2 API");
        let api = unsafe { api_fn() };
        assert!(!api.is_null(), "V2 API table is null");
        let table = unsafe { &*api };
        assert_eq!(table.abi_version, 2, "unexpected V2 ABI version");
        assert_eq!(table.struct_size as usize, size_of::<ApiV2>());
        Self {
            _library: library,
            api,
        }
    }

    fn api(&self) -> &ApiV2 {
        unsafe { &*self.api }
    }

    pub fn context(&self, arch: &str) -> Option<Context<'_>> {
        let view = StringView {
            data: arch.as_ptr(),
            len: arch.len(),
        };
        let mut raw = ptr::null_mut();
        let status = unsafe { (self.api().lift_context_create)(view, &mut raw) };
        if status != STATUS_OK || raw.is_null() {
            return None;
        }
        let context = Context { owner: self, raw };
        if !context.is_loaded() {
            return None;
        }
        Some(context)
    }
}

pub struct Context<'a> {
    owner: &'a V2Library,
    raw: *mut c_void,
}

impl Context<'_> {
    pub fn is_loaded(&self) -> bool {
        let mut loaded = 0;
        let status = unsafe { (self.owner.api().lift_context_is_loaded)(self.raw, &mut loaded) };
        status == STATUS_OK && loaded == 1
    }

    pub fn set_semantic_metadata(&self, enabled: bool) {
        assert_eq!(
            unsafe {
                (self.owner.api().lift_context_set_semantic_metadata)(self.raw, enabled as u32)
            },
            STATUS_OK
        );
    }

    pub fn error(&self) -> String {
        let mut view = ByteView::default();
        let status = unsafe { (self.owner.api().lift_context_error)(self.raw, &mut view) };
        if status != STATUS_OK || view.data.is_null() {
            return String::new();
        }
        String::from_utf8_lossy(unsafe { std::slice::from_raw_parts(view.data, view.len) })
            .into_owned()
    }

    pub fn lift<'a>(&'a self, bytes: &[u8], addr: u64) -> Block<'a> {
        let mut raw = ptr::null_mut();
        let status = unsafe {
            (self.owner.api().lift_instruction)(
                self.raw,
                ByteView {
                    data: bytes.as_ptr(),
                    len: bytes.len(),
                },
                addr,
                &mut raw,
            )
        };
        assert_eq!(status, STATUS_OK, "lift failed: {}", self.error());
        assert!(!raw.is_null());
        Block { context: self, raw }
    }
}

impl Drop for Context<'_> {
    fn drop(&mut self) {
        assert_eq!(
            unsafe { (self.owner.api().lift_context_free)(self.raw) },
            STATUS_OK,
            "context free refused"
        );
    }
}

pub struct Block<'a> {
    context: &'a Context<'a>,
    raw: *mut c_void,
}

impl Block<'_> {
    pub fn validate(&self) -> bool {
        unsafe {
            (self.context.owner.api().lift_block_validate)(self.context.raw, self.raw) == STATUS_OK
        }
    }

    pub fn op_count(&self) -> usize {
        let mut count = 0;
        assert_eq!(
            unsafe { (self.context.owner.api().lift_block_op_count)(self.raw, &mut count) },
            STATUS_OK
        );
        count
    }

    pub fn render(&self, kind: u32, op_index: usize) -> String {
        let blocks = [self.raw as *const c_void];
        let request = AnalysisRenderRequest {
            kind,
            context: self.context.raw,
            blocks: blocks.as_ptr(),
            num_blocks: blocks.len(),
            op_index,
            argument: StringView {
                data: ptr::null(),
                len: 0,
            },
        };
        let mut bytes = ptr::null_mut();
        assert_eq!(
            unsafe { (self.context.owner.api().analysis_render)(&request, &mut bytes) },
            STATUS_OK,
            "render failed: {}",
            self.context.error()
        );
        assert!(!bytes.is_null());
        let mut view = ByteView::default();
        assert_eq!(
            unsafe { (self.context.owner.api().owned_bytes_view)(bytes, &mut view) },
            STATUS_OK
        );
        let result =
            String::from_utf8_lossy(unsafe { std::slice::from_raw_parts(view.data, view.len) })
                .into_owned();
        assert_eq!(
            unsafe { (self.context.owner.api().owned_bytes_free)(bytes) },
            STATUS_OK
        );
        result
    }
}

impl Drop for Block<'_> {
    fn drop(&mut self) {
        assert_eq!(
            unsafe { (self.context.owner.api().lift_block_free)(self.raw) },
            STATUS_OK,
            "block free refused"
        );
    }
}
