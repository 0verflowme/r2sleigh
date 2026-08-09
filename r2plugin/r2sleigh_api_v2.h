#ifndef R2SLEIGH_API_V2_H
#define R2SLEIGH_API_V2_H

/* Generated from Rust declarations in src/ffi_v2.rs. Do not edit. */

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
typedef struct R2ILContext R2ILContext;
typedef struct R2ILBlock R2ILBlock;
typedef struct R2ILFunctionBlocks R2ILFunctionBlocks;

#define R2SLEIGH_ABI_V2 2

#define R2SLEIGH_CAP_DECOMPILE_V2 (1 << 0)

#define R2SLEIGH_CAP_TYPE_FUNCTION_V2 (1 << 1)

#define R2SLEIGH_CAP_EXACT_FUNCTION_INTERFACE_V2 (1 << 2)

#define R2SLEIGH_CAP_CALL_SITE_INTERFACES_V2 (1 << 3)

#define R2SLEIGH_CAP_NATIVE_REQUEST_GRAPH_V2 (1 << 4)

#define R2SLEIGH_CAP_RESPONSE_INFO_V2 (1 << 5)

#define R2SLEIGH_CAP_EXECUTION_CONTROL_V2 (1 << 6)

#define R2SLEIGH_CAP_EXACT_TYPE_LAYOUT_V2 (1 << 7)

#define R2SLEIGH_CAP_EXACT_STACK_SLOT_ROLES_V2 (1 << 8)

#define R2SLEIGH_CAPABILITIES_V2 ((((((((R2SLEIGH_CAP_DECOMPILE_V2 | R2SLEIGH_CAP_TYPE_FUNCTION_V2) | R2SLEIGH_CAP_EXACT_FUNCTION_INTERFACE_V2) | R2SLEIGH_CAP_CALL_SITE_INTERFACES_V2) | R2SLEIGH_CAP_NATIVE_REQUEST_GRAPH_V2) | R2SLEIGH_CAP_RESPONSE_INFO_V2) | R2SLEIGH_CAP_EXECUTION_CONTROL_V2) | R2SLEIGH_CAP_EXACT_TYPE_LAYOUT_V2) | R2SLEIGH_CAP_EXACT_STACK_SLOT_ROLES_V2)

#define R2SLEIGH_RADARE_ABI_V2 137

#define R2SLEIGH_STATUS_OK_V2 0

#define R2SLEIGH_STATUS_INVALID_ARGUMENT_V2 1

#define R2SLEIGH_STATUS_ABI_MISMATCH_V2 2

#define R2SLEIGH_STATUS_UNSUPPORTED_V2 3

#define R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2 4

#define R2SLEIGH_STATUS_ENGINE_ERROR_V2 5

#define R2SLEIGH_STATUS_PANIC_V2 6

#define R2SLEIGH_REQUEST_DECOMPILE_V2 1

#define R2SLEIGH_REQUEST_TYPE_FUNCTION_V2 2

#define R2SLEIGH_FUNCTION_CONTEXT_SCHEMA_V2 3

#define R2SLEIGH_INTERPROC_SCOPE_SCHEMA_V2 1

#define R2SLEIGH_RESPONSE_INFO_SCHEMA_V2 2

#define R2SLEIGH_OUTCOME_COMPLETED_V2 0

#define R2SLEIGH_OUTCOME_REFUSED_V2 1

#define R2SLEIGH_PHASE_SNAPSHOT_CONTEXT_V2 0

#define R2SLEIGH_PHASE_LIFT_NORMALIZE_V2 1

#define R2SLEIGH_PHASE_SSA_V2 2

#define R2SLEIGH_PHASE_OBLIGATIONS_V2 3

#define R2SLEIGH_PHASE_SYMBOLIC_V2 4

#define R2SLEIGH_PHASE_TYPES_V2 5

#define R2SLEIGH_PHASE_CERTIFICATION_V2 6

#define R2SLEIGH_PHASE_STRUCTURING_V2 7

#define R2SLEIGH_PHASE_NORMALIZATION_V2 8

#define R2SLEIGH_PHASE_RENDERING_V2 9

#define R2SLEIGH_PHASE_FFI_CONVERSION_V2 10

#define R2SLEIGH_PHASE_COUNT_V2 11

#define R2SLEIGH_PHASE_STATUS_NOT_EXECUTED_V2 0

#define R2SLEIGH_PHASE_STATUS_EXECUTED_V2 1

#define R2SLEIGH_PHASE_STATUS_FOLDED_V2 2

#define R2SLEIGH_PHASE_STATUS_REUSED_V2 3

#define R2SLEIGH_PHASE_STATUS_REFUSED_V2 4

#define R2SLEIGH_SOURCE_RETURN_VOID_V2 1

#define R2SLEIGH_SOURCE_RETURN_REGISTER_V2 2

#define R2SLEIGH_SOURCE_STACK_BASE_BP_V2 1

#define R2SLEIGH_SOURCE_STACK_BASE_SP_V2 2

#define R2SLEIGH_SOURCE_STACK_ROLE_LOCAL_V2 1

#define R2SLEIGH_SOURCE_STACK_ROLE_PARAMETER_HOME_V2 2

#define R2SLEIGH_SOURCE_PARAMETER_INDEX_INVALID_V2 UINT32_MAX

#define R2SLEIGH_SOURCE_STORAGE_RAM_V2 1

#define R2SLEIGH_SOURCE_STORAGE_REGISTER_V2 2

#define R2SLEIGH_SOURCE_STORAGE_UNIQUE_V2 3

#define R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2 4

#define R2SLEIGH_SOURCE_STORAGE_CUSTOM_V2 5

#define R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2 7

#define R2SLEIGH_SOURCE_CALL_SITE_SCHEMA_V2 1

#define R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2 UINT32_MAX

#define R2SLEIGH_SOURCE_TYPE_SIGNED_INTEGER_V2 1

#define R2SLEIGH_SOURCE_TYPE_UNSIGNED_INTEGER_V2 2

#define R2SLEIGH_SOURCE_TYPE_POINTER_V2 3

#define R2SLEIGH_SOURCE_TYPE_STRUCT_V2 4

#define R2SLEIGH_SOURCE_CARRIER_INVALID_V2 0

#define R2SLEIGH_SOURCE_CARRIER_FULL_V2 1

#define R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2 2

#define R2SLEIGH_MAX_FUNCTION_BLOCKS_V2 200

#define R2SLEIGH_MAX_FUNCTION_OPS_V2 512

#define R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2 (16 << 20)

#define R2SLEIGH_MAX_AGGREGATE_BLOCKS_V2 1024

#define R2SLEIGH_MAX_AGGREGATE_OPS_V2 4096

#define R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2 4096

#define R2SLEIGH_MAX_CONTEXT_ITEMS_V2 65536

#define R2SLEIGH_MAX_NESTED_ITEMS_V2 262144

#define R2SLEIGH_MAX_STRING_BYTES_V2 (1 << 20)

#define R2SLEIGH_MAX_AGGREGATE_STRING_BYTES_V2 (4 << 20)

#define R2SLEIGH_MAX_JSON_BYTES_V2 (16 << 20)

#define R2SLEIGH_MAX_AGGREGATE_JSON_BYTES_V2 (16 << 20)

/**
 * Opaque, caller-owned response. response_free is the only valid deallocator.
 */
typedef struct R2SleighResponseV2 R2SleighResponseV2;

/**
 * Opaque, caller-owned session. `session_cancel` may run concurrently with
 * execute; `session_reset_cancellation` is valid only between execute calls.
 * session_free is the only valid deallocator.
 */
typedef struct R2SleighSessionV2 R2SleighSessionV2;

typedef struct R2SleighSessionConfigV2 {
  uint32_t abi_version;
  uint32_t struct_size;
  uint64_t required_capabilities;
} R2SleighSessionConfigV2;

/**
 * Versioned request envelope. `payload` points to one native
 * R2SleighEngineRequestPayloadV2 whose interpretation is selected by `kind`;
 * it is borrowed only for the duration of execute.
 */
typedef struct R2SleighRequestV2 {
  uint32_t abi_version;
  uint32_t struct_size;
  uint32_t kind;
  uint32_t flags;
  const void *payload;
  size_t payload_size;
} R2SleighRequestV2;

/**
 * Borrowed bytes. A response view remains valid until response_free; an error
 * view remains valid until the next operation on that session or session_free.
 */
typedef struct R2SleighByteViewV2 {
  const uint8_t *data;
  size_t len;
} R2SleighByteViewV2;

/**
 * One entry in the stable eleven-phase engine timing inventory.
 */
typedef struct R2SleighPhaseTimingV2 {
  uint32_t phase;
  uint32_t status;
  uint64_t elapsed_us;
} R2SleighPhaseTimingV2;

/**
 * Borrowed response metadata. Every pointed-to byte and timing entry remains
 * valid until `response_free` is called for the owning response. Schema 2
 * exposes semantic-kernel render diagnostics as stable structured JSON.
 */
typedef struct R2SleighResponseInfoV2 {
  uint32_t schema_version;
  uint32_t struct_size;
  uint32_t request_kind;
  uint32_t outcome;
  const struct R2SleighPhaseTimingV2 *phase_timings;
  size_t num_phase_timings;
  uint64_t ffi_conversion_elapsed_us;
  struct R2SleighByteViewV2 diagnostics_json;
} R2SleighResponseInfoV2;

/**
 * Stable V2 function table. Every callback contains its own unwind barrier.
 */
typedef struct R2SleighApiV2 {
  uint32_t abi_version;
  uint32_t struct_size;
  uint64_t capabilities;
  uint32_t radare_abi_version;
  uint32_t session_config_size;
  uint32_t request_size;
  uint32_t engine_request_payload_size;
  uint32_t function_context_size;
  uint32_t context_param_size;
  uint32_t context_var_size;
  uint32_t context_base_member_size;
  uint32_t context_enum_variant_size;
  uint32_t context_base_type_size;
  uint32_t context_callee_size;
  uint32_t lift_quality_size;
  uint32_t interproc_seed_size;
  uint32_t interproc_scope_size;
  uint32_t interproc_plan_size;
  uint32_t source_function_interface_size;
  uint32_t source_parameter_size;
  uint32_t source_parameter_type_size;
  uint32_t source_carrier_projection_size;
  uint32_t source_type_size;
  uint32_t source_aggregate_member_size;
  uint32_t source_aggregate_layout_size;
  uint32_t source_register_size;
  uint32_t source_stack_slot_size;
  uint32_t source_storage_size;
  uint32_t source_call_argument_size;
  uint32_t source_call_site_interface_size;
  uint32_t byte_view_size;
  uint32_t phase_timing_size;
  uint32_t response_info_size;
  uint32_t (*session_create)(const struct R2SleighSessionConfigV2*, struct R2SleighSessionV2**);
  uint32_t (*session_free)(struct R2SleighSessionV2*);
  uint32_t (*session_cancel)(const struct R2SleighSessionV2*);
  uint32_t (*session_reset_cancellation)(const struct R2SleighSessionV2*);
  uint32_t (*execute)(struct R2SleighSessionV2*,
                      const struct R2SleighRequestV2*,
                      struct R2SleighResponseV2**);
  uint32_t (*response_bytes)(const struct R2SleighResponseV2*, struct R2SleighByteViewV2*);
  uint32_t (*response_info)(const struct R2SleighResponseV2*, struct R2SleighResponseInfoV2*);
  uint32_t (*response_free)(struct R2SleighResponseV2*);
  uint32_t (*session_error)(const struct R2SleighSessionV2*, struct R2SleighByteViewV2*);
} R2SleighApiV2;

/**
 * Typed external signature parameter in the native request graph.
 */
typedef struct R2SleighContextParam {
  const char *name;
  const char *type_name;
  const char *cc_reg;
} R2SleighContextParam;

/**
 * Typed register or stack variable in the native request graph.
 */
typedef struct R2SleighContextVar {
  uint32_t kind;
  const char *name;
  const char *type_name;
  const char *reg;
  const char *base;
  int64_t offset;
  int32_t has_offset;
  uint32_t role;
  int64_t param_index;
  const char *param_name;
  const char *source_reg;
  int32_t is_arg;
} R2SleighContextVar;

typedef struct R2SleighContextBaseMember {
  const char *name;
  const char *type_name;
  uint64_t offset;
  uint64_t size_bits;
  int32_t has_size_bits;
} R2SleighContextBaseMember;

typedef struct R2SleighContextEnumVariant {
  const char *name;
  int64_t value;
} R2SleighContextEnumVariant;

typedef struct R2SleighContextBaseType {
  uint32_t kind;
  const char *name;
  const char *type_name;
  uint64_t size_bits;
  int32_t has_size_bits;
  const struct R2SleighContextBaseMember *members;
  size_t num_members;
  const struct R2SleighContextEnumVariant *variants;
  size_t num_variants;
} R2SleighContextBaseType;

typedef struct R2SleighContextCallee {
  uint64_t call_addr;
  uint64_t addr;
  const char *name;
  uint32_t linkage;
  const char *signature_name;
  const char *signature_ret_type;
  const char *signature_callconv;
  int32_t signature_noreturn;
  const struct R2SleighContextParam *signature_params;
  size_t num_signature_params;
} R2SleighContextCallee;

/**
 * Immutable typed function context. Every pointer is borrowed only for the
 * duration of `execute` and validated before conversion to owned engine data.
 */
typedef struct R2SleighFunctionContext {
  uint32_t schema_version;
  uint64_t dirty_epoch;
  uint64_t context_hash;
  uint64_t type_dirty_epoch;
  const char *external_context_json;
  const char *signature_name;
  const char *signature_ret_type;
  const char *signature_callconv;
  int32_t signature_noreturn;
  const struct R2SleighContextParam *params;
  size_t num_params;
  const struct R2SleighContextVar *vars;
  size_t num_vars;
  const struct R2SleighContextBaseType *base_types;
  size_t num_base_types;
  const struct R2SleighContextCallee *callees;
  size_t num_callees;
  const char *assumptions_json;
} R2SleighFunctionContext;

typedef struct R2SleighLiftQuality {
  size_t expected_blocks;
  size_t lifted_blocks;
  size_t read_failures;
  size_t invalid_blocks;
  size_t null_lift_failures;
  size_t truncated_blocks;
} R2SleighLiftQuality;

typedef struct R2SleighInterprocSeed {
  uint64_t id;
  const char *name;
  size_t arg_count_hint;
  int32_t has_arg_count_hint;
  uint32_t linkage;
} R2SleighInterprocSeed;

typedef struct R2SleighInterprocScope {
  uint32_t schema_version;
  const R2ILFunctionBlocks *functions;
  size_t num_functions;
  const struct R2SleighInterprocSeed *seeds;
  size_t num_seeds;
} R2SleighInterprocScope;

typedef struct R2SleighInterprocSessionPlan {
  int32_t include_type_interproc_scope;
  int32_t include_root_symbolic_scope;
  size_t interproc_iter;
  size_t interproc_max_iters;
  int32_t interproc_converged;
} R2SleighInterprocSessionPlan;

/**
 * Length-tagged UTF-8 source string.
 */
typedef struct R2SleighStringViewV2 {
  const uint8_t *data;
  size_t len;
} R2SleighStringViewV2;

/**
 * One exact full-width register identity supplied by radare2's immutable
 * source snapshot. Name, byte offset, and size are all cross-checked against
 * ArchSpec before use.
 */
typedef struct R2SleighSourceRegisterV2 {
  struct R2SleighStringViewV2 name;
  uint64_t offset;
  uint32_t size;
} R2SleighSourceRegisterV2;

typedef struct R2SleighSourceParameterV2 {
  uint32_t index;
  struct R2SleighSourceRegisterV2 storage;
} R2SleighSourceParameterV2;

/**
 * One exactly sized stack resource. `base` identifies the source stack/frame
 * register and is canonicalized against ArchSpec before `offset` is used.
 * `role` is exactly Local or parameter Home. Only a Home's `parameter_index`
 * and canonical `home_storage` offset/size carry authority, and they must match
 * that interface parameter. The Home register name is validated presentation
 * data and never participates in role proof.
 */
typedef struct R2SleighSourceStackSlotV2 {
  uint32_t base_kind;
  struct R2SleighSourceRegisterV2 base;
  int64_t offset;
  uint32_t size;
  uint32_t role;
  uint32_t parameter_index;
  struct R2SleighSourceRegisterV2 home_storage;
} R2SleighSourceStackSlotV2;

/**
 * Exact name-independent lifted storage identity.
 */
typedef struct R2SleighSourceStorageV2 {
  uint32_t space;
  uint32_t custom_space;
  uint64_t offset;
  uint32_t size;
} R2SleighSourceStorageV2;

typedef struct R2SleighSourceCallArgumentV2 {
  uint32_t index;
  struct R2SleighSourceRegisterV2 storage;
} R2SleighSourceCallArgumentV2;

/**
 * One exact raw callsite mapped onto one canonical lifted call operation.
 */
typedef struct R2SleighSourceCallSiteInterfaceV2 {
  uint32_t schema_version;
  uint32_t struct_size;
  uint64_t revision_identity;
  uint64_t caller_function_addr;
  uint64_t raw_instruction_addr;
  uint64_t raw_target_addr;
  uint64_t block_addr;
  size_t op_index;
  struct R2SleighSourceStorageV2 target;
  struct R2SleighStringViewV2 calling_convention;
  const struct R2SleighSourceCallArgumentV2 *arguments;
  size_t num_arguments;
  uint32_t result_kind;
  struct R2SleighSourceRegisterV2 result_storage;
  uint32_t variadic;
  uint32_t noreturn;
  uint32_t complete;
} R2SleighSourceCallSiteInterfaceV2;

/**
 * Projection of one logical value into its full-width ABI carrier.
 */
typedef struct R2SleighSourceCarrierProjectionV2 {
  uint32_t kind;
  uint64_t offset_bits;
  uint64_t size_bits;
} R2SleighSourceCarrierProjectionV2;

/**
 * Logical type and carrier binding for one source parameter ordinal.
 */
typedef struct R2SleighSourceParameterTypeV2 {
  uint32_t index;
  uint32_t type_id;
  struct R2SleighSourceCarrierProjectionV2 carrier;
} R2SleighSourceParameterTypeV2;

/**
 * One structural logical type. IDs are exact indexes into the source type array.
 */
typedef struct R2SleighSourceTypeV2 {
  uint32_t id;
  uint32_t kind;
  uint64_t size_bits;
  uint64_t align_bits;
  uint32_t target_type_id;
  uint32_t aggregate_id;
} R2SleighSourceTypeV2;

/**
 * One exact aggregate member. `name` is presentation-only; member_id is authority.
 */
typedef struct R2SleighSourceAggregateMemberV2 {
  uint32_t member_id;
  uint32_t type_id;
  uint64_t offset_bits;
  uint64_t size_bits;
  size_t count;
  struct R2SleighStringViewV2 name;
} R2SleighSourceAggregateMemberV2;

/**
 * One complete natural-layout aggregate reachable from the function signature.
 */
typedef struct R2SleighSourceAggregateLayoutV2 {
  uint32_t id;
  uint32_t type_id;
  uint64_t size_bits;
  uint64_t align_bits;
  struct R2SleighStringViewV2 name;
  const struct R2SleighSourceAggregateMemberV2 *members;
  size_t num_members;
  uint32_t complete;
  uint32_t c_layout_compatible;
} R2SleighSourceAggregateLayoutV2;

/**
 * Complete exact function interface for one immutable source revision.
 */
typedef struct R2SleighSourceFunctionInterfaceV2 {
  uint32_t schema_version;
  uint32_t struct_size;
  uint64_t revision_identity;
  uint64_t function_addr;
  struct R2SleighStringViewV2 calling_convention;
  const struct R2SleighSourceParameterV2 *parameters;
  size_t num_parameters;
  const struct R2SleighSourceStackSlotV2 *stack_slots;
  size_t num_stack_slots;
  uint32_t return_kind;
  struct R2SleighSourceRegisterV2 return_storage;
  uint32_t variadic;
  uint32_t noreturn;
  uint32_t stack_resources_complete;
  uint32_t complete;
  const struct R2SleighSourceCallSiteInterfaceV2 *call_sites;
  size_t num_call_sites;
  /**
   * True only when the V2 array contains every callsite represented by the
   * immutable source snapshot; semantic completeness remains per callsite.
   */
  uint32_t call_sites_complete;
  const struct R2SleighSourceParameterTypeV2 *parameter_types;
  size_t num_parameter_types;
  uint32_t return_type_id;
  struct R2SleighSourceCarrierProjectionV2 return_carrier;
  const struct R2SleighSourceTypeV2 *types;
  size_t num_types;
  const struct R2SleighSourceAggregateLayoutV2 *aggregates;
  size_t num_aggregates;
  uint32_t exact_types_complete;
  uint32_t stack_slot_roles_complete;
  /**
   * Exact name-independent register consumed by the lifted return.
   */
  struct R2SleighSourceStorageV2 return_address_storage;
  /**
   * Exact name-independent register carrying the architectural stack pointer.
   */
  struct R2SleighSourceStorageV2 stack_pointer_storage;
} R2SleighSourceFunctionInterfaceV2;

/**
 * Native engine request graph shared by decompile and type-function requests.
 * `analysis_depth` is consumed only by type-function requests. `timeout_us`
 * combines with the session-owned cancellation token; request flags remain
 * reserved and V2 rejects every nonzero production flag today.
 */
typedef struct R2SleighEngineRequestPayloadV2 {
  uint32_t abi_version;
  uint32_t struct_size;
  const R2ILContext *ctx;
  const R2ILBlock *const *blocks;
  size_t num_blocks;
  uint64_t function_addr;
  const char *function_name;
  struct R2SleighFunctionContext function_context;
  struct R2SleighLiftQuality lift_quality;
  struct R2SleighInterprocScope interproc_scope;
  struct R2SleighInterprocSessionPlan interproc_plan;
  uint32_t analysis_depth;
  /**
   * Relative request deadline. Zero disables the deadline.
   */
  uint64_t timeout_us;
  const struct R2SleighSourceFunctionInterfaceV2 *source_interface;
} R2SleighEngineRequestPayloadV2;

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * Return the immutable V2 API table. The table and all callback addresses are
 * process-lifetime borrows and must not be freed.
 */
const struct R2SleighApiV2 *r2sleigh_api_v2(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  /* R2SLEIGH_API_V2_H */
