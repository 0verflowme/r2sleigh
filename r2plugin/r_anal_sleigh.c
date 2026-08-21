/* radare2 - LGPL - Copyright 2025 - r2sleigh project */

#include <r_anal.h>
#include <r_core.h>
#include <r_lib.h>
#include <r_version.h>
#include <r_util/r_json.h>
#include <r_util/r_num.h>
#include <r_util/r_str.h>
#include <r_util/r_type.h>
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "r2sleigh_api_v2.h"
#include "snapshot_wire.h"

/* Support is decided by whether radare2 exposes the function-snapshot API, and
 * by nothing else. Pinning a number -- the ABI number or the schema number --
 * says the plugin needs one particular revision when what it needs is one
 * particular capability, and those numbers move for unrelated reasons: the
 * schema last moved for two booleans on a struct no consumer can see, and stood
 * still through three changes to the struct every consumer reads. The guards
 * that actually hold are the linker, which cannot resolve an accessor that is
 * not there, and the wire conformance test, which compares writer against
 * reader byte for byte. */
#ifndef R_ANAL_FUNCTION_SNAPSHOT_API
#error "r2sleigh requires a radare2 exposing the immutable function-snapshot API"
#endif


/* Remaining direct value declarations for the Rust library. */
typedef struct {
	int is_write;
	unsigned int size;
	const char *addr_reg;
	unsigned long long base;
	int has_base;
	long long delta;
	int is_stack;
	const char *stack_base;
	long long stack_offset;
} R2ILBlockMemAccess;
typedef struct {
	unsigned long long value;
} R2ILBlockImmediateValue;
typedef struct {
	const char *name;
} R2ILBlockRegValue;

#define R2TAINT_OP_OTHER 0
#define R2TAINT_OP_CALL 1
#define R2TAINT_OP_CALL_IND 2
#define R2TAINT_OP_STORE 3
typedef struct {
	unsigned long long block;
	const char * const *labels;
	size_t num_labels;
} R2TaintSource;
typedef struct {
	const char *var;
	const char * const *labels;
	size_t num_labels;
} R2TaintTaintedVar;
typedef struct {
	unsigned long long block;
	size_t op_idx;
	unsigned int op_kind;
	unsigned long long target_addr;
	int has_target_addr;
	const R2TaintTaintedVar *tainted_vars;
	size_t num_tainted_vars;
} R2TaintSinkHit;

#define R2SLEIGH_CONTEXT_VAR_REGISTER 0
#define R2SLEIGH_CONTEXT_VAR_STACK 1
#define R2SLEIGH_CONTEXT_STACK_LOCAL 0
#define R2SLEIGH_CONTEXT_STACK_ARG 1
#define R2SLEIGH_CONTEXT_STACK_HOME 2
#define R2SLEIGH_CONTEXT_STACK_SAVED_REG 3
#define R2SLEIGH_CONTEXT_STACK_SAVED_FP 4
#define R2SLEIGH_CONTEXT_STACK_UNKNOWN 5
#define R2SLEIGH_CONTEXT_BASE_STRUCT 0
#define R2SLEIGH_CONTEXT_BASE_UNION 1
#define R2SLEIGH_CONTEXT_BASE_ENUM 2
#define R2SLEIGH_CONTEXT_BASE_TYPEDEF 3
#define R2SLEIGH_CONTEXT_BASE_ATOMIC 4
typedef struct {
	unsigned long long from;
	unsigned long long to;
	unsigned int space_kind;
	unsigned int custom_space;
	char ref_kind;
} R2SleighDataRef;

#define R2SLEIGH_DATA_REF_SPACE_RAM 0
typedef struct {
	unsigned long long addr;
	const char *comment;
} R2SleighAnnotation;
typedef struct {
	unsigned long long addr;
	unsigned long long size;
} R2SleighRuntimeSource;
/* radare2 Deep Integration */

static const R2SleighApiV2 *sleigh_lift_api_v2(void) {
	R_STATIC_ASSERT (sizeof (((R2SleighDataRef *)0)->from) == 8);
	R_STATIC_ASSERT (sizeof (((R2SleighDataRef *)0)->to) == 8);
	R_STATIC_ASSERT (sizeof (((R2SleighDataRef *)0)->space_kind) == 4);
	R_STATIC_ASSERT (sizeof (((R2SleighDataRef *)0)->custom_space) == 4);
	R_STATIC_ASSERT (sizeof (((R2SleighDataRef *)0)->ref_kind) == 1);
	R_STATIC_ASSERT (r_offsetof (R2SleighDataRef, from) == 0);
	R_STATIC_ASSERT (r_offsetof (R2SleighDataRef, to) == 8);
	R_STATIC_ASSERT (r_offsetof (R2SleighDataRef, space_kind) == 16);
	R_STATIC_ASSERT (r_offsetof (R2SleighDataRef, custom_space) == 20);
	R_STATIC_ASSERT (r_offsetof (R2SleighDataRef, ref_kind) == 24);
	R_STATIC_ASSERT (sizeof (R2SleighDataRef) == 28 || sizeof (R2SleighDataRef) == 32);
	const R2SleighApiV2 *api = r2sleigh_api_v2 ();
	if (!api || api->abi_version != R2SLEIGH_ABI_V2
		|| api->struct_size != sizeof (*api)
		|| !(api->capabilities & R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2)
		|| api->byte_view_size != sizeof (R2SleighByteViewV2)
		|| api->string_view_size != sizeof (R2SleighStringViewV2)
		|| api->switch_case_size != sizeof (R2SleighSwitchCaseV2)
		|| api->direct_call_identity_size != sizeof (R2SleighDirectCallIdentityV2)
		|| api->analysis_render_request_size != sizeof (R2SleighAnalysisRenderRequestV2)
		|| api->analysis_query_request_size != sizeof (R2SleighAnalysisQueryRequestV2)
		|| api->analysis_result_view_size != sizeof (R2SleighAnalysisResultViewV2)
		|| api->data_ref_size != sizeof (R2SleighDataRef)
		|| api->data_ref_schema_version != R2SLEIGH_DATA_REF_SCHEMA_V2
		|| api->planner_query_request_size != sizeof (R2SleighPlannerQueryRequestV2)
		|| api->planner_query_response_size != sizeof (R2SleighPlannerQueryResponseV2)
		|| !(api->capabilities & R2SLEIGH_CAP_LIFT_CORE_V2)
		|| !(api->capabilities & R2SLEIGH_CAP_PLANNER_QUERY_V2)
		|| !api->lift_context_create || !api->lift_context_free
		|| !api->lift_context_is_loaded || !api->lift_context_arch_name
		|| !api->lift_context_error || !api->lift_last_error
		|| !api->lift_context_reg_profile
		|| !api->lift_instruction || !api->lift_block
		|| !api->lift_context_set_semantic_metadata || !api->lift_block_free
		|| !api->lift_block_validate || !api->lift_block_set_switch_info
		|| !api->lift_block_op_count || !api->lift_block_direct_call_identity
		|| !api->lift_block_size || !api->lift_block_addr
		|| !api->lift_block_mnemonic || !api->lift_block_type
		|| !api->lift_block_jump || !api->lift_block_fail
		|| !api->owned_bytes_view || !api->owned_bytes_free
		|| !api->analysis_render
		|| !api->analysis_query || !api->analysis_result_view
		|| !api->analysis_result_free
		|| !api->planner_query) {
		return NULL;
	}
	return api;
}

static uint32_t sleigh_v2_planner_query(unsigned int kind, R2SleighPlannerQueryRequestV2 *request, R2SleighPlannerQueryResponseV2 *response) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!request || !response) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	request->abi_version = R2SLEIGH_ABI_V2;
	request->struct_size = sizeof (*request);
	request->schema_version = R2SLEIGH_PLANNER_QUERY_SCHEMA_V2;
	request->kind = kind;
	memset (response, 0, sizeof (*response));
	return api? api->planner_query (request, response): R2SLEIGH_STATUS_ABI_MISMATCH_V2;
}

static R2SleighAnalysisPolicyV2 sleigh_v2_query_analysis_policy(unsigned int depth) {
	R2SleighPlannerQueryRequestV2 request = {0};
	R2SleighPlannerQueryResponseV2 response = {0};
	request.depth = depth;
	uint32_t status = sleigh_v2_planner_query (R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2, &request, &response);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: analysis policy query failed (%u)", status);
		return (R2SleighAnalysisPolicyV2){0};
	}
	return response.analysis_policy;
}

static R2SleighPostAnalysisPlanV2 sleigh_v2_query_post_analysis(unsigned int depth, size_t function_count) {
	R2SleighPlannerQueryRequestV2 request = {0};
	R2SleighPlannerQueryResponseV2 response = {0};
	request.depth = depth;
	request.function_count = function_count;
	uint32_t status = sleigh_v2_planner_query (R2SLEIGH_PLANNER_POST_ANALYSIS_V2, &request, &response);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: post-analysis plan query failed (%u)", status);
		return (R2SleighPostAnalysisPlanV2){0};
	}
	return response.post_analysis;
}

static R2SleighAutoCallbackPlanV2 sleigh_v2_query_auto_callback(unsigned int depth, unsigned int kind, unsigned int basic_block_count, unsigned int cost, unsigned long long linear_size) {
	R2SleighPlannerQueryRequestV2 request = {0};
	R2SleighPlannerQueryResponseV2 response = {0};
	request.depth = depth;
	request.callback_kind = kind;
	request.basic_block_count = basic_block_count;
	request.cost = cost;
	request.linear_size = linear_size;
	uint32_t status = sleigh_v2_planner_query (R2SLEIGH_PLANNER_AUTO_CALLBACK_V2, &request, &response);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: auto-callback plan query failed (%u)", status);
		R2SleighAutoCallbackPlanV2 denied = {
			.kind = kind,
			.reason = R2SLEIGH_AUTO_CALLBACK_REASON_MODE_NOT_FULL_V2,
		};
		return denied;
	}
	return response.auto_callback;
}

static R_TH_LOCAL R2SleighOwnedBytesV2 *sleigh_pending_owned_bytes = NULL;

static char *sleigh_byte_view_v2_copy(R2SleighByteViewV2 view) {
	if ((!view.data && view.len) || view.len == SIZE_MAX) {
		return NULL;
	}
	char *copy = malloc (view.len + 1);
	if (!copy) {
		return NULL;
	}
	if (view.len) {
		memcpy (copy, view.data, view.len);
	}
	copy[view.len] = '\0';
	return copy;
}

static uint32_t sleigh_v2_owned_bytes_release(const R2SleighApiV2 *api, R2SleighOwnedBytesV2 **bytes) {
	if (!bytes || !*bytes) {
		return R2SLEIGH_STATUS_OK_V2;
	}
	if (!api || !api->owned_bytes_free) {
		R_LOG_ERROR ("r2sleigh: retaining owned bytes because the V2 API is unavailable");
		return R2SLEIGH_STATUS_ABI_MISMATCH_V2;
	}
	R2SleighOwnedBytesV2 *owned = *bytes;
	uint32_t status = api->owned_bytes_free (owned);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: retaining owned bytes after free failure (%u)", status);
		return status;
	}
	if (sleigh_pending_owned_bytes == owned) {
		sleigh_pending_owned_bytes = NULL;
	}
	*bytes = NULL;
	return R2SLEIGH_STATUS_OK_V2;
}

static uint32_t sleigh_v2_owned_bytes_release_or_preserve(const R2SleighApiV2 *api, R2SleighOwnedBytesV2 **bytes) {
	uint32_t status = sleigh_v2_owned_bytes_release (api, bytes);
	if (status != R2SLEIGH_STATUS_OK_V2 && bytes && *bytes) {
		sleigh_pending_owned_bytes = *bytes;
		*bytes = NULL;
	}
	return status;
}

static uint32_t sleigh_lift_owned_bytes_copy(const R2SleighApiV2 *api, R2SleighOwnedBytesV2 *bytes, char **output) {
	if (!output) {
		R2SleighOwnedBytesV2 *owned = bytes;
		uint32_t free_status = sleigh_v2_owned_bytes_release_or_preserve (api, &owned);
		return free_status == R2SLEIGH_STATUS_OK_V2
			? R2SLEIGH_STATUS_INVALID_ARGUMENT_V2: free_status;
	}
	*output = NULL;
	if (!bytes) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	if (!api || !api->owned_bytes_view || !api->owned_bytes_free) {
		sleigh_pending_owned_bytes = bytes;
		R_LOG_ERROR ("r2sleigh: retaining owned bytes because the V2 API is unavailable");
		return R2SLEIGH_STATUS_ABI_MISMATCH_V2;
	}
	R2SleighByteViewV2 view = {0};
	uint32_t status = api->owned_bytes_view (bytes, &view);
	if (status == R2SLEIGH_STATUS_OK_V2) {
		*output = sleigh_byte_view_v2_copy (view);
		if (!*output) {
			status = R2SLEIGH_STATUS_ENGINE_ERROR_V2;
		}
	}
	R2SleighOwnedBytesV2 *owned = bytes;
	uint32_t free_status = sleigh_v2_owned_bytes_release_or_preserve (api, &owned);
	if (free_status != R2SLEIGH_STATUS_OK_V2) {
		free (*output);
		*output = NULL;
		return free_status;
	}
	return status;
}

static uint32_t sleigh_v2_context_create(const char *arch, R2ILContext **context) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!context) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*context = NULL;
	if (!api || !arch) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	R2SleighStringViewV2 view = {
		.data = (const uint8_t *)arch,
		.len = strlen (arch),
	};
	return api->lift_context_create (view, context);
}

static uint32_t sleigh_v2_context_free(R2ILContext *context) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	return api && context? api->lift_context_free (context)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_context_is_loaded(const R2ILContext *context, uint32_t *loaded) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!loaded) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*loaded = 0;
	return api && context? api->lift_context_is_loaded (context, loaded)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_context_arch_name(const R2ILContext *context, char **name) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!name) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*name = NULL;
	R2SleighByteViewV2 view = {0};
	if (!api || !context) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	uint32_t status = api->lift_context_arch_name (context, &view);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
	}
	*name = sleigh_byte_view_v2_copy (view);
	return *name? R2SLEIGH_STATUS_OK_V2: R2SLEIGH_STATUS_ENGINE_ERROR_V2;
}

static uint32_t sleigh_v2_context_error(const R2ILContext *context, char **message) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!message) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*message = NULL;
	R2SleighByteViewV2 view = {0};
	if (!api || !context) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	uint32_t status = api->lift_context_error (context, &view);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
	}
	*message = sleigh_byte_view_v2_copy (view);
	return *message? R2SLEIGH_STATUS_OK_V2: R2SLEIGH_STATUS_ENGINE_ERROR_V2;
}

static uint32_t sleigh_v2_context_reg_profile(const R2ILContext *context, char **profile) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!profile) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*profile = NULL;
	R2SleighOwnedBytesV2 *bytes = NULL;
	if (!api || !context) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	uint32_t status = sleigh_v2_owned_bytes_release (api, &sleigh_pending_owned_bytes);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
	}
	status = api->lift_context_reg_profile (context, &bytes);
	if (status != R2SLEIGH_STATUS_OK_V2 || !bytes) {
		uint32_t free_status = sleigh_v2_owned_bytes_release_or_preserve (api, &bytes);
		return free_status == R2SLEIGH_STATUS_OK_V2
			? (status == R2SLEIGH_STATUS_OK_V2? R2SLEIGH_STATUS_ENGINE_ERROR_V2: status)
			: free_status;
	}
	return sleigh_lift_owned_bytes_copy (api, bytes, profile);
}

static uint32_t sleigh_v2_lift_instruction(R2ILContext *context, const unsigned char *bytes, size_t len, unsigned long long addr, R2ILBlock **block) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!block) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*block = NULL;
	R2SleighByteViewV2 view = {
		.data = bytes,
		.len = len,
	};
	return api? api->lift_instruction (context, view, addr, block)
		: R2SLEIGH_STATUS_ABI_MISMATCH_V2;
}

static uint32_t sleigh_v2_lift_block(R2ILContext *context, const unsigned char *bytes, size_t len, unsigned long long addr, unsigned int block_size, R2ILBlock **block) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!block) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*block = NULL;
	R2SleighByteViewV2 view = {
		.data = bytes,
		.len = len,
	};
	return api? api->lift_block (context, view, addr, block_size, block)
		: R2SLEIGH_STATUS_ABI_MISMATCH_V2;
}

static uint32_t sleigh_v2_context_set_semantic_metadata(R2ILContext *context, bool enabled) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	return api && context? api->lift_context_set_semantic_metadata (context, enabled? 1: 0)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_block_free(R2ILBlock *block) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	return api && block? api->lift_block_free (block)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static bool sleigh_v2_block_release(R2ILBlock **block) {
	if (!block || !*block) {
		return true;
	}
	uint32_t status = sleigh_v2_block_free (*block);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: retaining block after free failure (%u)", status);
		return false;
	}
	*block = NULL;
	return true;
}

static uint32_t sleigh_v2_block_validate(R2ILContext *context, const R2ILBlock *block) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	return api && context && block? api->lift_block_validate (context, block)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_block_set_switch_info(R2ILBlock *block, unsigned long long switch_addr,
	unsigned long long min_val, unsigned long long max_val,
	unsigned long long default_target, int has_default,
	const R2SleighSwitchCaseV2 *cases, size_t case_count) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	return api && block? api->lift_block_set_switch_info (block, switch_addr,
		min_val, max_val, default_target, has_default? 1: 0, cases, case_count)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_block_op_count(const R2ILBlock *block, size_t *count) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!count) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*count = 0;
	return api && block? api->lift_block_op_count (block, count)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_block_size(const R2ILBlock *block, uint32_t *value) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (value) {
		*value = 0;
	}
	return api && block && value? api->lift_block_size (block, value)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_block_mnemonic(const R2ILContext *context, const unsigned char *bytes, size_t len, unsigned long long addr, char **text) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!text) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*text = NULL;
	R2SleighOwnedBytesV2 *mnemonic = NULL;
	R2SleighByteViewV2 view = {
		.data = bytes,
		.len = len,
	};
	if (!api) {
		return R2SLEIGH_STATUS_ABI_MISMATCH_V2;
	}
	uint32_t status = sleigh_v2_owned_bytes_release (api, &sleigh_pending_owned_bytes);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
	}
	status = api->lift_block_mnemonic (context, view, addr, &mnemonic);
	if (status != R2SLEIGH_STATUS_OK_V2 || !mnemonic) {
		uint32_t free_status = sleigh_v2_owned_bytes_release_or_preserve (api, &mnemonic);
		return free_status == R2SLEIGH_STATUS_OK_V2
			? (status == R2SLEIGH_STATUS_OK_V2? R2SLEIGH_STATUS_ENGINE_ERROR_V2: status)
			: free_status;
	}
	return sleigh_lift_owned_bytes_copy (api, mnemonic, text);
}

static uint32_t sleigh_v2_block_type(const R2ILBlock *block, uint32_t *value) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (value) {
		*value = 0;
	}
	return api && block && value? api->lift_block_type (block, value)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_block_jump(const R2ILBlock *block, uint64_t *value) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (value) {
		*value = 0;
	}
	return api && block && value? api->lift_block_jump (block, value)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_block_fail(const R2ILBlock *block, uint64_t *value) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (value) {
		*value = 0;
	}
	return api && block && value? api->lift_block_fail (block, value)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static uint32_t sleigh_v2_analysis_render(uint32_t kind, const R2ILContext *context,
	const R2ILBlock *const *blocks, size_t num_blocks, size_t op_index,
	const char *argument, char **text) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!text) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*text = NULL;
	if (!api) {
		return R2SLEIGH_STATUS_ABI_MISMATCH_V2;
	}
	uint32_t status = sleigh_v2_owned_bytes_release (api, &sleigh_pending_owned_bytes);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
	}
	R2SleighAnalysisRenderRequestV2 request = {
		.kind = kind,
		.context = context,
		.blocks = blocks,
		.num_blocks = num_blocks,
		.op_index = op_index,
		.argument = {
			.data = (const uint8_t *)argument,
			.len = argument? strlen (argument): 0,
		},
	};
	R2SleighOwnedBytesV2 *bytes = NULL;
	status = api->analysis_render (&request, &bytes);
	if (status != R2SLEIGH_STATUS_OK_V2 || !bytes) {
		uint32_t free_status = sleigh_v2_owned_bytes_release_or_preserve (api, &bytes);
		return free_status == R2SLEIGH_STATUS_OK_V2
			? (status == R2SLEIGH_STATUS_OK_V2? R2SLEIGH_STATUS_ENGINE_ERROR_V2: status)
			: free_status;
	}
	return sleigh_lift_owned_bytes_copy (api, bytes, text);
}

static uint32_t sleigh_v2_analysis_query(uint32_t kind, const R2ILContext *context,
	const R2ILBlock *const *blocks, size_t num_blocks, uint64_t function_addr,
	R2SleighAnalysisResultV2 **result, R2SleighAnalysisResultViewV2 *view) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!result || !view) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*result = NULL;
	memset (view, 0, sizeof (*view));
	if (!api) {
		return R2SLEIGH_STATUS_ABI_MISMATCH_V2;
	}
	R2SleighAnalysisQueryRequestV2 request = {
		.kind = kind,
		.context = context,
		.blocks = blocks,
		.num_blocks = num_blocks,
		.function_addr = function_addr,
	};
	uint32_t status = api->analysis_query (&request, result);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
	}
	status = api->analysis_result_view (*result, view);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		uint32_t free_status = api->analysis_result_free (*result);
		if (free_status == R2SLEIGH_STATUS_OK_V2) {
			*result = NULL;
		} else {
			R_LOG_ERROR ("r2sleigh: retaining analysis result after free failure (%u)", free_status);
		}
	}
	return status;
}

static uint32_t sleigh_v2_analysis_result_free(R2SleighAnalysisResultV2 *result) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	return api && result? api->analysis_result_free (result)
		: R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
}

static bool sleigh_v2_analysis_result_release(R2SleighAnalysisResultV2 **result) {
	if (!result || !*result) {
		return true;
	}
	uint32_t status = sleigh_v2_analysis_result_free (*result);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: retaining analysis result after free failure (%u)", status);
		return false;
	}
	*result = NULL;
	return true;
}

/* Per-architecture context (lazy init)
 *
 * WARNING: These globals are NOT thread-safe. This plugin assumes
 * single-threaded radare2 usage. If radare2 becomes multi-threaded,
 * this code must be updated with proper synchronization (e.g., mutex).
 */
static R2ILContext *sleigh_ctx = NULL;
static char *sleigh_arch = NULL;
static char *sleigh_reg_profile = NULL;
static char *sleigh_arch_override = NULL;
static R_TH_LOCAL R2SleighResponseV2 *sleigh_pending_engine_response = NULL;
static R_TH_LOCAL R2SleighSessionV2 *sleigh_pending_engine_session = NULL;

void r2sleigh_set_arch_override(const char *arch) {
	if (!arch || !*arch || (sleigh_arch_override && !strcmp (sleigh_arch_override, arch))) {
		return;
	}
	free (sleigh_arch_override);
	sleigh_arch_override = strdup (arch);
}

static bool sleigh_get_data_refs(RAnal *anal, RAnalFunction *fcn, R_OUT RVecAnalRef **refs);
static bool collect_data_refs_from_typed(
	RAnal *anal,
	RAnalFunction *fcn,
	const R2SleighDataRef *items,
	size_t count,
	RVecAnalRef *refs,
	R_OUT size_t *discovered);

typedef enum {
	SLEIGH_MODE_FAST = 0,
	SLEIGH_MODE_BALANCED = 1,
	SLEIGH_MODE_FULL = 2,
} SleighMode;

typedef enum {
	SLEIGH_PROFILE_STAGE_LIFT,
	SLEIGH_PROFILE_STAGE_TYPED_CONTEXT,
	SLEIGH_PROFILE_STAGE_SESSION,
	SLEIGH_PROFILE_STAGE_MUTATION,
	SLEIGH_PROFILE_STAGE_XREF,
	SLEIGH_PROFILE_STAGE_TAINT,
	SLEIGH_PROFILE_STAGE_DECOMPILE,
} SleighProfileStage;

typedef struct {
	ut64 addr;
	char *name;
	ut64 lift_us;
	ut64 typed_context_us;
	ut64 session_us;
	ut64 mutation_us;
	ut64 xref_us;
	ut64 taint_us;
	ut64 decompile_us;
	ut64 total_us;
} SleighProfileEntry;

static SleighProfileEntry *sleigh_profile_entries = NULL;
static size_t sleigh_profile_count = 0;
static size_t sleigh_profile_cap = 0;

/* Minimum bytes to pass to libsla (it reads ahead for variable-length instructions) */
#define SLEIGH_MIN_BYTES 16
#define SLEIGH_LIFT_BLOCK_MAX_ALLOC (1024 * 1024)
#define SLEIGH_LIFT_PREFIX_HEAL_MAX_TRIMS 64
#define SLEIGH_TAINT_MAX_BLOCKS 200
#define SLEIGH_PROFILE_MAX_DEFAULT 20
#define SLEIGH_CALLER_PROP_MAX_PER_CALLEE 256
#define SLEIGH_CALLER_PROP_MAX_TOTAL 2048
#define SLEIGH_CALLER_PROP_SAMPLE_MAX 5
#define SLEIGH_TAINT_LABEL_MAX 6
#define SLEIGH_COMMENT_PREFIX_SEMANTIC "sla:"
#define SLEIGH_COMMENT_PREFIX_PROOF "sla.proof:"
#define SLEIGH_COMMENT_PREFIX_TAINT "sla.taint:"
#define SLEIGH_COMMENT_PREFIX_TAINT_RISK "sla.taint.risk:"

/* Helper to lift all basic blocks of a function */
typedef struct {
	R2ILBlock **blocks;
	size_t count;
	size_t capacity;
} BlockArray;

typedef struct {
	ut64 start_us;
	ut64 budget_us;
	bool exhausted;
} SleighPostAnalysisBudget;

static SleighPostAnalysisBudget sleigh_post_analysis_budget_new(ut64 budget_us) {
	SleighPostAnalysisBudget budget = {
		.start_us = r_time_now_mono (),
		.budget_us = budget_us,
		.exhausted = false,
	};
	return budget;
}

static ut64 sleigh_post_analysis_budget_elapsed(const SleighPostAnalysisBudget *budget) {
	if (!budget || !budget->start_us) {
		return 0;
	}
	return r_time_now_mono () - budget->start_us;
}

static bool sleigh_post_analysis_budget_allows(SleighPostAnalysisBudget *budget, const char *stage) {
	if (!budget || !budget->budget_us) {
		return true;
	}
	ut64 elapsed = sleigh_post_analysis_budget_elapsed (budget);
	if (elapsed <= budget->budget_us) {
		return true;
	}
	if (!budget->exhausted) {
		R_LOG_WARN ("r2sleigh: post-analysis budget exhausted during %s after %llu usec; refusing remaining automatic enrichment",
			stage && *stage ? stage : "unknown",
			(unsigned long long)elapsed);
	}
	budget->exhausted = true;
	return false;
}

static void sleigh_engine_v2_log_error(
	const R2SleighApiV2 *api,
	const R2SleighSessionV2 *session,
	uint32_t status
) {
	R2SleighByteViewV2 error = {0};
	if (api && session && api->session_error
		&& api->session_error (session, &error) == R2SLEIGH_STATUS_OK_V2
		&& error.data && error.len) {
		int len = error.len > INT_MAX? INT_MAX: (int)error.len;
		R_LOG_ERROR ("r2sleigh: V2 engine request failed (%u): %.*s",
			status, len, (const char *)error.data);
		return;
	}
	R_LOG_ERROR ("r2sleigh: V2 engine request failed (%u)", status);
}



static bool sleigh_engine_v2_phase_status_is_valid(uint32_t status) {
	switch (status) {
	case R2SLEIGH_PHASE_STATUS_NOT_EXECUTED_V2:
	case R2SLEIGH_PHASE_STATUS_EXECUTED_V2:
	case R2SLEIGH_PHASE_STATUS_FOLDED_V2:
	case R2SLEIGH_PHASE_STATUS_REFUSED_V2:
		return true;
	default:
		return false;
	}
}

#define SLEIGH_DECJ_SCHEMA_VERSION 1

static char *sleigh_engine_v2_error_json(const char *state, uint32_t status, const char *message) {
	PJ *pj = pj_new ();
	if (!pj) {
		return NULL;
	}
	pj_o (pj);
	pj_kn (pj, "schema_version", SLEIGH_DECJ_SCHEMA_VERSION);
	pj_ks (pj, "request_kind", "decompile");
	pj_kn (pj, "request_kind_code", R2SLEIGH_REQUEST_DECOMPILE_V2);
	pj_ks (pj, "outcome", "error");
	pj_knull (pj, "outcome_code");
	pj_knull (pj, "rendered_output");
	pj_knull (pj, "diagnostics");
	pj_ka (pj, "phase_timings");
	pj_end (pj);
	pj_kn (pj, "ffi_conversion_elapsed_us", 0);
	pj_kb (pj, "refused", false);
	pj_ko (pj, "error");
	pj_ks (pj, "state", state? state: "unknown");
	pj_kn (pj, "status", status);
	pj_ks (pj, "message", message? message: "V2 decompile request failed");
	pj_end (pj);
	pj_end (pj);
	return pj_drain (pj);
}


static bool sleigh_json_is_single_object(const char *text, size_t len) {
	if (!text || !len) {
		return false;
	}
	size_t i = 0;
	while (i < len && isspace ((unsigned char)text[i])) {
		i++;
	}
	if (i == len || text[i] != '{') {
		return false;
	}
	char closers[R_PRINT_JSON_DEPTH_LIMIT] = {0};
	size_t depth = 0;
	bool in_string = false;
	bool escaped = false;
	for (; i < len; i++) {
		unsigned char ch = (unsigned char)text[i];
		if (in_string) {
			if (escaped) {
				escaped = false;
			} else if (ch == '\\') {
				escaped = true;
			} else if (ch == '"') {
				in_string = false;
			} else if (ch < 0x20) {
				return false;
			}
			continue;
		}
		if (ch == '"') {
			in_string = true;
			continue;
		}
		if (ch == '{' || ch == '[') {
			if (depth == R_PRINT_JSON_DEPTH_LIMIT) {
				return false;
			}
			closers[depth++] = ch == '{'? '}': ']';
			continue;
		}
		if (ch == '}' || ch == ']') {
			if (!depth || closers[depth - 1] != ch) {
				return false;
			}
			depth--;
			if (!depth) {
				i++;
				while (i < len && isspace ((unsigned char)text[i])) {
					i++;
				}
				return i == len;
			}
		}
	}
	return false;
}

#define SLEIGH_SEMANTIC_KERNEL_WARNING_PREFIX "semantic-kernel:"
#define SLEIGH_SEMANTIC_KERNEL_WARNING_LIMIT 8
#define SLEIGH_SEMANTIC_KERNEL_WARNING_BYTES 4096
#define SLEIGH_ENGINE_DIAGNOSTICS_BYTES (1024 * 1024)

static void sleigh_engine_v2_log_semantic_kernel_warnings(R2SleighByteViewV2 view) {
	if (!view.data || !view.len || view.len > SLEIGH_ENGINE_DIAGNOSTICS_BYTES
		|| !sleigh_json_is_single_object ((const char *)view.data, view.len)) {
		return;
	}
	char *text = sleigh_byte_view_v2_copy (view);
	if (!text) {
		return;
	}
	RJson *diagnostics = r_json_parse (text);
	if (!diagnostics || diagnostics->type != R_JSON_OBJECT) {
		r_json_free (diagnostics);
		free (text);
		return;
	}
	const RJson *warnings = r_json_get (diagnostics, "warnings");
	if (warnings && warnings->type == R_JSON_ARRAY) {
		const RJson *warning;
		size_t count = 0;
		for (warning = warnings->children.first; warning
				&& count < SLEIGH_SEMANTIC_KERNEL_WARNING_LIMIT;
			warning = warning->next) {
			if (warning->type != R_JSON_STRING || !warning->str_value
				|| !r_str_startswith (warning->str_value,
					SLEIGH_SEMANTIC_KERNEL_WARNING_PREFIX)) {
				continue;
			}
			const size_t length = r_str_nlen (warning->str_value,
				SLEIGH_SEMANTIC_KERNEL_WARNING_BYTES + 1);
			if (!length || length > SLEIGH_SEMANTIC_KERNEL_WARNING_BYTES) {
				continue;
			}
			R_LOG_DEBUG ("r2sleigh: %s", warning->str_value);
			count++;
		}
	}
	r_json_free (diagnostics);
	free (text);
}

static uint32_t sleigh_engine_v2_release_handles(const R2SleighApiV2 *api,
	R2SleighResponseV2 **response, R2SleighSessionV2 **session) {
	if ((!response || !*response) && (!session || !*session)) {
		return R2SLEIGH_STATUS_OK_V2;
	}
	if (!api || !api->response_free || !api->session_free) {
		R_LOG_ERROR ("r2sleigh: retaining V2 engine handles because the API is unavailable");
		return R2SLEIGH_STATUS_ABI_MISMATCH_V2;
	}
	if (response && *response) {
		uint32_t status = api->response_free (*response);
		if (status != R2SLEIGH_STATUS_OK_V2) {
			R_LOG_ERROR ("r2sleigh: retaining V2 engine response after free failure (%u)", status);
			return status;
		}
		*response = NULL;
	}
	if (session && *session) {
		uint32_t status = api->session_free (*session);
		if (status != R2SLEIGH_STATUS_OK_V2) {
			R_LOG_ERROR ("r2sleigh: retaining V2 engine session after free failure (%u)", status);
			return status;
		}
		*session = NULL;
	}
	return R2SLEIGH_STATUS_OK_V2;
}

static uint32_t sleigh_engine_v2_release_or_preserve(const R2SleighApiV2 *api,
	R2SleighResponseV2 **response, R2SleighSessionV2 **session) {
	uint32_t status = sleigh_engine_v2_release_handles (api, response, session);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		if (response && *response) {
			sleigh_pending_engine_response = *response;
			*response = NULL;
		}
		if (session && *session) {
			sleigh_pending_engine_session = *session;
			*session = NULL;
		}
	}
	return status;
}

static uint32_t sleigh_engine_v2_retry_pending(const R2SleighApiV2 *api) {
	return sleigh_engine_v2_release_handles (api,
		&sleigh_pending_engine_response, &sleigh_pending_engine_session);
}

// Returns a malloc-owned NUL-terminated projection. Every borrowed response
// view is consumed before response_free releases the opaque Rust owner.
static char *sleigh_engine_execute_v2(uint32_t kind, uint64_t required_capability, const R2SleighEngineRequestPayloadV2 *payload) {
	required_capability |= R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2
		| R2SLEIGH_CAP_RESPONSE_INFO_V2
		| R2SLEIGH_CAP_EXECUTION_CONTROL_V2;
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!api || api->abi_version != R2SLEIGH_ABI_V2
		|| api->struct_size != sizeof (*api)
		|| !(api->capabilities & R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2)
		|| api->session_config_size != sizeof (R2SleighSessionConfigV2)
		|| api->request_size != sizeof (R2SleighRequestV2)
		|| api->engine_request_payload_size != sizeof (R2SleighEngineRequestPayloadV2)
		|| api->byte_view_size != sizeof (R2SleighByteViewV2)
		|| api->phase_timing_size != sizeof (R2SleighPhaseTimingV2)
		|| api->response_info_size != sizeof (R2SleighResponseInfoV2)
		|| (api->capabilities & required_capability) != required_capability
		|| !api->session_create || !api->session_free
		|| !api->session_cancel || !api->session_reset_cancellation || !api->execute
		|| !api->response_bytes || !api->response_info
		|| !api->response_free || !api->session_error) {
		R_LOG_ERROR ("r2sleigh: incompatible V2 engine API table");
		return NULL;
	}
	uint32_t status = sleigh_engine_v2_retry_pending (api);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return NULL;
	}
	if (!payload || payload->abi_version != R2SLEIGH_ABI_V2
		|| payload->struct_size != sizeof (*payload)) {
		R_LOG_ERROR ("r2sleigh: invalid native V2 request graph");
		return NULL;
	}

	R2SleighSessionConfigV2 config = {
		.abi_version = R2SLEIGH_ABI_V2,
		.struct_size = sizeof (config),
		.required_capabilities = required_capability,
	};
	R2SleighSessionV2 *session = NULL;
	status = api->session_create (&config, &session);
	if (status != R2SLEIGH_STATUS_OK_V2 || !session) {
		R_LOG_ERROR ("r2sleigh: failed to create V2 engine session (%u)", status);
		uint32_t free_status = sleigh_engine_v2_release_or_preserve (api, NULL, &session);
		if (free_status != R2SLEIGH_STATUS_OK_V2) {
			return NULL;
		}
		return NULL;
	}

	R2SleighRequestV2 request = {
		.abi_version = R2SLEIGH_ABI_V2,
		.struct_size = sizeof (request),
		.kind = kind,
		.payload = payload,
		.payload_size = sizeof (*payload),
	};
	R2SleighResponseV2 *response = NULL;
	status = api->execute (session, &request, &response);
	if (status != R2SLEIGH_STATUS_OK_V2 || !response) {
		sleigh_engine_v2_log_error (api, session, status);
		uint32_t free_status = sleigh_engine_v2_release_or_preserve (api, &response, &session);
		(void)free_status;
		return NULL;
	}
	R2SleighResponseInfoV2 info = {0};
	status = api->response_info (response, &info);
	if (status != R2SLEIGH_STATUS_OK_V2
		|| info.schema_version != R2SLEIGH_RESPONSE_INFO_SCHEMA_V2
		|| info.struct_size != sizeof (info)
		|| info.request_kind != kind
		|| info.num_phase_timings != R2SLEIGH_PHASE_COUNT_V2
		|| !info.phase_timings
		|| (info.outcome != R2SLEIGH_OUTCOME_COMPLETED_V2
			&& info.outcome != R2SLEIGH_OUTCOME_REFUSED_V2)
		|| !info.diagnostics_json.data || !info.diagnostics_json.len) {
		sleigh_engine_v2_log_error (api, session, status);
		uint32_t free_status = sleigh_engine_v2_release_or_preserve (api, &response, &session);
		if (free_status != R2SLEIGH_STATUS_OK_V2) {
			return NULL;
		}
		return NULL;
	}
	size_t phase_index;
	for (phase_index = 0; phase_index < info.num_phase_timings; phase_index++) {
		if (info.phase_timings[phase_index].phase != phase_index
			|| !sleigh_engine_v2_phase_status_is_valid (info.phase_timings[phase_index].status)) {
			R_LOG_ERROR ("r2sleigh: invalid V2 engine phase metadata");
			uint32_t free_status = sleigh_engine_v2_release_or_preserve (api, &response, &session);
			if (free_status != R2SLEIGH_STATUS_OK_V2) {
				return NULL;
			}
			return NULL;
		}
	}
	if (info.phase_timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2].status
			!= R2SLEIGH_PHASE_STATUS_EXECUTED_V2
		|| info.phase_timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2].elapsed_us
			!= info.ffi_conversion_elapsed_us) {
		R_LOG_ERROR ("r2sleigh: invalid V2 FFI conversion metadata");
		uint32_t free_status = sleigh_engine_v2_release_or_preserve (api, &response, &session);
		if (free_status != R2SLEIGH_STATUS_OK_V2) {
			return NULL;
		}
		return NULL;
	}

	R2SleighByteViewV2 bytes = {0};
	status = api->response_bytes (response, &bytes);
	char *result = NULL;
	if (status == R2SLEIGH_STATUS_OK_V2 && bytes.len < SIZE_MAX
		&& (!bytes.len || bytes.data)) {
		result = sleigh_byte_view_v2_copy (bytes);
	} else {
		sleigh_engine_v2_log_error (api, session, status);
	}
	sleigh_engine_v2_log_semantic_kernel_warnings (info.diagnostics_json);
	uint32_t free_status = sleigh_engine_v2_release_or_preserve (api, &response, &session);
	if (free_status != R2SLEIGH_STATUS_OK_V2) {
		free (result);
		return NULL;
	}
	return result;
}

static void block_array_init(BlockArray *arr) {
	arr->blocks = NULL;
	arr->count = 0;
	arr->capacity = 0;
}

static bool block_array_push(BlockArray *arr, R2ILBlock *block) {
	if (arr->count >= arr->capacity) {
		size_t next_capacity = arr->capacity? arr->capacity * 2: 8;
		size_t allocation_size;
		if (next_capacity < arr->capacity
			|| r_mul_overflow (next_capacity, sizeof (R2ILBlock *), &allocation_size)) {
			return false;
		}
		R2ILBlock **next = realloc (arr->blocks, allocation_size);
		if (!next) {
			return false;
		}
		arr->capacity = next_capacity;
		arr->blocks = next;
	}
	arr->blocks[arr->count++] = block;
	return true;
}

static bool block_array_free(BlockArray *arr) {
	size_t i;
	size_t retained = 0;
	for (i = 0; i < arr->count; i++) {
		R2ILBlock *block = arr->blocks[i];
		if (!sleigh_v2_block_release (&block)) {
			arr->blocks[retained++] = block;
		}
	}
	if (retained) {
		arr->count = retained;
		return false;
	}
	free (arr->blocks);
	arr->blocks = NULL;
	arr->count = 0;
	arr->capacity = 0;
	return true;
}


static char *sleigh_collect_function_assumptions_json(RAnal *anal, RAnalFunction *fcn) {
	char *assumptions_json;

	if (!anal || !fcn) {
		return strdup ("[]");
	}
	assumptions_json = r_anal_function_get_assumptions_json (anal, fcn);
	if (R_STR_ISEMPTY (assumptions_json)) {
		free (assumptions_json);
		return strdup ("[]");
	}
	return assumptions_json;
}

static const char *skip_cmd_spaces(const char *s) {
	while (s && *s == ' ') {
		s++;
	}
	return s;
}

static bool read_block_bytes_for_lifting(
	RAnal *anal,
	const RAnalBlock *bb,
	ut8 **out_buf,
	size_t *out_len,
	size_t *out_lift_size
) {
	size_t logical_size;
	size_t lift_size;
	size_t read_len;
	ut8 *buf;

	R_RETURN_VAL_IF_FAIL (
		anal && bb && out_buf && out_len && out_lift_size,
		false
	);

	if (!bb->size) {
		return false;
	}
	logical_size = (size_t)bb->size;
	if ((ut64)bb->size > (ut64)SLEIGH_LIFT_BLOCK_MAX_ALLOC) {
		R_LOG_WARN (
			"r2sleigh: capping block read/lift from %"PFMT64u" to %u bytes at 0x%"PFMT64x,
			(ut64)bb->size,
			(unsigned int)SLEIGH_LIFT_BLOCK_MAX_ALLOC,
			bb->addr
		);
		lift_size = (size_t)SLEIGH_LIFT_BLOCK_MAX_ALLOC;
	} else {
		lift_size = logical_size;
	}

	read_len = R_MAX (lift_size, (size_t)SLEIGH_MIN_BYTES);
	buf = calloc (1, read_len);
	if (!buf) {
		return false;
	}
	if (!anal->iob.read_at (anal->iob.io, bb->addr, buf, lift_size)) {
		free (buf);
		return false;
	}

	*out_buf = buf;
	*out_len = read_len;
	*out_lift_size = lift_size;
	return true;
}

static bool parse_sym_target_expr(RCore *core, const char *expr, ut64 *target) {
	if (!core || !core->num || !expr || !*expr || !target) {
		return false;
	}
	if (!r_num_is_valid_input (core->num, expr)) {
		return false;
	}
	*target = r_num_math (core->num, expr);
	return true;
}

static RAnalFunction *resolve_function_target_by_name(RAnal *anal, const char *target_name) {
	if (!anal || !target_name || !*target_name) {
		return NULL;
	}

	RAnalFunction *fcn = r_anal_get_function_byname (anal, target_name);
	if (fcn) {
		return fcn;
	}

	char *trimmed = r_str_trim_dup (target_name);
	if (!trimmed || !*trimmed) {
		free (trimmed);
		return NULL;
	}

	char *base = trimmed;
	for (;;) {
		if (r_str_startswith (base, "dbg.")) {
			base += 4;
			continue;
		}
		if (r_str_startswith (base, "sym.")) {
			base += 4;
			continue;
		}
		if (r_str_startswith (base, "fcn.")) {
			base += 4;
			continue;
		}
		break;
	}

	const char *plain = (*base == '_')? base + 1: base;
	char *candidates[] = {
		strdup (base),
		*plain? strdup (plain): NULL,
		r_str_newf ("sym.%s", base),
		*plain? r_str_newf ("sym.%s", plain): NULL,
		*plain? r_str_newf ("sym._%s", plain): NULL,
		r_str_newf ("dbg.%s", base),
		*plain? r_str_newf ("dbg.%s", plain): NULL,
		r_str_newf ("fcn.%s", base),
		*plain? r_str_newf ("fcn.%s", plain): NULL,
		(*base == '_')? strdup (plain): r_str_newf ("_%s", plain),
	};
	size_t i;
	for (i = 0; i < R_ARRAY_SIZE (candidates); i++) {
		const char *candidate = candidates[i];
		if (!candidate || !*candidate) {
			continue;
		}
		fcn = r_anal_get_function_byname (anal, candidate);
		if (fcn) {
			break;
		}
	}
	for (i = 0; i < R_ARRAY_SIZE (candidates); i++) {
		free (candidates[i]);
	}
	free (trimmed);
	return fcn;
}

static int function_bb_count(const RAnalFunction *fcn) {
	return (fcn && fcn->bbs)? r_list_length (fcn->bbs): 0;
}

static const char *auto_callback_refusal_reason_name(unsigned int reason) {
	switch (reason) {
	case R2SLEIGH_AUTO_CALLBACK_REASON_ALLOWED_V2:
		return "allowed";
	case R2SLEIGH_AUTO_CALLBACK_REASON_MODE_NOT_FULL_V2:
		return "mode";
	case R2SLEIGH_AUTO_CALLBACK_REASON_TOO_MANY_BLOCKS_V2:
		return "blocks";
	case R2SLEIGH_AUTO_CALLBACK_REASON_TOO_LARGE_V2:
		return "size";
	case R2SLEIGH_AUTO_CALLBACK_REASON_TOO_COSTLY_V2:
		return "cost";
	default:
		return "unknown";
	}
}

static R2SleighAutoCallbackPlanV2 auto_callback_plan_for_function(
	RAnal *anal,
	const RAnalFunction *fcn,
	unsigned int kind) {
	unsigned int bb_count = UINT_MAX;
	unsigned int cost = UINT_MAX;
	unsigned long long linear_size = ULLONG_MAX;
	if (fcn) {
		int raw_bb_count = function_bb_count (fcn);
		int raw_linear_size = r_anal_function_linear_size ((RAnalFunction *)fcn);
		bb_count = raw_bb_count >= 0? (unsigned int)raw_bb_count: UINT_MAX;
		cost = (unsigned int)r_anal_function_cost ((RAnalFunction *)fcn);
		linear_size = raw_linear_size > 0? (unsigned long long)raw_linear_size: 0;
	}
	return sleigh_v2_query_auto_callback (
		anal? (unsigned int)anal->plugin_analysis_depth: 0,
		(unsigned int)kind,
		bb_count,
		cost,
		linear_size);
}

static bool auto_callback_allows_function(
	RAnal *anal,
	const RAnalFunction *fcn,
	unsigned int kind,
	const char *stage) {
	R2SleighAutoCallbackPlanV2 plan = auto_callback_plan_for_function (anal, fcn, kind);
	if (plan.allowed) {
		return true;
	}
	R_LOG_DEBUG ("r2sleigh: auto %s skipped by engine callback policy reason=%s fcn=0x%"PFMT64x" blocks=%d",
		stage && *stage? stage: "callback",
		auto_callback_refusal_reason_name (plan.reason),
		fcn? fcn->addr: 0,
		fcn? function_bb_count (fcn): -1);
	return false;
}

static RAnalFunction *materialize_function_at(RAnal *anal, ut64 addr) {
	RAnalFunction *fcn;
	int ret;
	RCore *core;

	if (!anal || addr == UT64_MAX) {
		return NULL;
	}

	fcn = r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
	if (fcn) {
		return fcn;
	}

	core = anal->coreb.core;
	if (core) {
		if (r_core_anal_fcn (core, addr, UT64_MAX, R_ANAL_REF_TYPE_NULL, 1)) {
			fcn = r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
			if (fcn) {
				return fcn;
			}
		}
	}

	fcn = r_anal_create_function (anal, NULL, addr, R_ANAL_FCN_TYPE_FCN, NULL);
	if (!fcn) {
		return r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
	}

	ret = r_anal_function (anal, fcn, addr, R_ANAL_REF_TYPE_NULL);
	if ((ret < 0 && ret != R_ANAL_RET_END) || function_bb_count (fcn) <= 0) {
		if (!r_anal_function_delete (anal, fcn)) {
			r_anal_function_free (fcn);
		}
		return NULL;
	}

	return r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
}

static RAnalFunction *resolve_or_materialize_function_target(RCore *core, RAnal *anal, const char *target_arg) {
	ut64 target_addr = 0;
	RAnalFunction *fcn;

	if (!core || !anal || !target_arg || !*target_arg) {
		return NULL;
	}

	fcn = resolve_function_target_by_name (anal, target_arg);
	if (fcn) {
		return fcn;
	}

	if (!parse_sym_target_expr (core, target_arg, &target_addr)) {
		return NULL;
	}
	return materialize_function_at (anal, target_addr);
}

static RAnalFunction *resolve_or_materialize_current_function(RCore *core, RAnal *anal) {
	if (!core || !anal) {
		return NULL;
	}
	return materialize_function_at (anal, core->addr);
}

static bool vec_has_reg(const RVecRArchValue *vec, const char *reg_name) {
	size_t len;
	size_t i;

	if (!vec || !reg_name) {
		return false;
	}

	len = RVecRArchValue_length (vec);
	for (i = 0; i < len; i++) {
		RArchValue *value = RVecRArchValue_at (vec, i);
		if (value && value->reg && !strcmp (value->reg, reg_name)) {
			return true;
		}
	}

	return false;
}

static RRegItem *resolve_anal_reg(RAnal *anal, const char *name) {
	RRegItem *reg;
	if (!anal || !anal->reg || !name || !*name) {
		return NULL;
	}
	reg = r_reg_get (anal->reg, name, -1);
	if (!reg) {
		char alt[64];
		r_str_ncpy (alt, name, sizeof (alt));
		r_str_case (alt, false);
		reg = r_reg_get (anal->reg, alt, -1);
	}
		if (!reg) {
			char alt[64];
			r_str_ncpy (alt, name, sizeof (alt));
			r_str_case (alt, true);
			reg = r_reg_get (anal->reg, alt, -1);
		}
	return reg;
}

static void add_typed_reg_value(RAnal *anal, const char *name, RVecRArchValue *vec, int access) {
	RRegItem *reg;
	RArchValue value = {0};
	if (!anal || !name || !vec) {
		return;
	}
	reg = resolve_anal_reg (anal, name);
	if (!reg || !reg->name || vec_has_reg (vec, reg->name)) {
		return;
	}
	value.type = R_ANAL_VAL_REG;
	value.reg = reg->name;
	value.access = access;
	RVecRArchValue_push_back (vec, &value);
}

static void add_typed_reg_values(RAnal *anal, const R2ILBlockRegValue *items, size_t count, RVecRArchValue *vec, int access) {
	size_t i;
	if (!items || !vec) {
		return;
	}
	for (i = 0; i < count; i++) {
		add_typed_reg_value (anal, items[i].name, vec, access);
	}
}

static void add_typed_memory_archvalue(RAnal *anal, const R2ILBlockMemAccess *mem, RVecRArchValue *vec) {
	RArchValue value = {0};
	int access;
	if (!anal || !mem || !vec) {
		return;
	}
	access = mem->is_write? R_PERM_W: R_PERM_R;
	value.type = R_ANAL_VAL_MEM;
	value.access = access;
	value.memref = mem->size? mem->size: 1;
	if (mem->addr_reg) {
		RRegItem *reg = resolve_anal_reg (anal, mem->addr_reg);
		if (reg && reg->name) {
			value.reg = reg->name;
			value.base = 0;
			value.delta = mem->delta;
		}
	} else if (mem->has_base) {
		value.base = mem->base;
		value.delta = 0;
	}
	if (!value.reg && mem->is_stack && mem->stack_base) {
		RRegItem *reg = resolve_anal_reg (anal, mem->stack_base);
		if (reg && reg->name) {
			value.reg = reg->name;
			value.base = 0;
			value.delta = mem->stack_offset;
		}
	}
	RVecRArchValue_push_back (vec, &value);
}

static void add_typed_immediate_archvalue(const R2ILBlockImmediateValue *imm, RVecRArchValue *vec, int access) {
	RArchValue value = {0};
	if (!imm || !vec) {
		return;
	}
	value.type = R_ANAL_VAL_IMM;
	value.access = access;
	value.imm = imm->value;
	RVecRArchValue_push_back (vec, &value);
}

static void fill_op_values_enhanced(RAnal *anal, RAnalOp *op, R2ILContext *ctx, const R2ILBlock *block) {
	R2SleighAnalysisResultV2 *result = NULL;
	R2SleighAnalysisResultViewV2 view = {0};
	const R2ILBlockMemAccess *memory;
	const R2ILBlockImmediateValue *immediates;
	const R2ILBlockRegValue *reg_reads;
	const R2ILBlockRegValue *reg_writes;
	size_t memory_count = 0;
	size_t immediate_count = 0;
	size_t reg_read_count = 0;
	size_t reg_write_count = 0;
	size_t i;

	if (!anal || !op || !ctx || !block) {
		return;
	}

	op->direction = 0;
	const R2ILBlock *blocks[] = { block };
	if (sleigh_v2_analysis_query (R2SLEIGH_QUERY_BLOCK_VALUES_V2,
		ctx, blocks, 1, 0, &result, &view)
		!= R2SLEIGH_STATUS_OK_V2) {
		op->direction = R_ANAL_OP_DIR_READ;
		return;
	}

	memory = (const R2ILBlockMemAccess *)view.primary;
	memory_count = view.primary_count;
	for (i = 0; memory && i < memory_count; i++) {
		const R2ILBlockMemAccess *mem = &memory[i];
		if (mem->is_write) {
			op->direction |= R_ANAL_OP_DIR_WRITE;
			add_typed_memory_archvalue (anal, mem, &op->dsts);
		} else {
			op->direction |= R_ANAL_OP_DIR_READ;
			add_typed_memory_archvalue (anal, mem, &op->srcs);
		}
		if (mem->is_stack && !op->stackop) {
			op->stackop = mem->is_write? R_ANAL_STACK_SET: R_ANAL_STACK_GET;
			op->stackptr = mem->stack_offset;
		}
	}
	if (op->direction == 0) {
		op->direction = R_ANAL_OP_DIR_READ;
	}

	immediates = (const R2ILBlockImmediateValue *)view.secondary;
	immediate_count = view.secondary_count;
	for (i = 0; immediates && i < immediate_count; i++) {
		add_typed_immediate_archvalue (&immediates[i], &op->srcs, R_PERM_R);
	}

	reg_reads = (const R2ILBlockRegValue *)view.tertiary;
	reg_read_count = view.tertiary_count;
	add_typed_reg_values (anal, reg_reads, reg_read_count, &op->srcs, R_PERM_R);
	reg_writes = (const R2ILBlockRegValue *)view.quaternary;
	reg_write_count = view.quaternary_count;
	add_typed_reg_values (anal, reg_writes, reg_write_count, &op->dsts, R_PERM_W);

	(void)sleigh_v2_analysis_result_release (&result);
}

static void print_reg_values_json(RCons *cons, const RVecRArchValue *vec) {
	size_t len;
	size_t i;
	bool first = true;

	if (!cons || !vec) {
		return;
	}

	len = RVecRArchValue_length (vec);
	for (i = 0; i < len; i++) {
		const RArchValue *value = RVecRArchValue_at (vec, i);
		if (!value || value->type != R_ANAL_VAL_REG || !value->reg) {
			continue;
		}

		if (!first) {
			r_cons_print (cons, ",");
		}
		r_cons_printf (cons, "\"%s\"", value->reg);
		first = false;
	}
}

typedef struct {
	char *label;
	ut64 *blocks;
	size_t count;
	size_t capacity;
} TaintLabelSource;

typedef struct {
	TaintLabelSource *items;
	size_t count;
	size_t capacity;
} TaintSourceMap;

typedef struct {
	ut64 addr;
	int hits;
	int call_hits;
	int store_hits;
	char **call_names;
	size_t ncall_names;
	size_t call_name_cap;
	char **labels;
	size_t nlabels;
	size_t label_cap;
} TaintBlockSummary;

typedef struct {
	TaintBlockSummary *items;
	size_t count;
	size_t capacity;
} TaintSummaryMap;

typedef struct {
	ut64 revision;
	bool captured;
} SleighArtifactRevision;

typedef struct {
	RCore *core;
	const char *domain_id;
	ut64 scope_id;
	ut64 function_epoch;
	ut64 type_epoch;
	ut64 snapshot_revision;
	RCoreAnalArtifactComment *comments;
	size_t comment_count;
	size_t comment_capacity;
	RCoreAnalArtifactFlag *flags;
	size_t flag_count;
	size_t flag_capacity;
	RAnalRef *xrefs;
	size_t xref_count;
	size_t xref_capacity;
	bool failed;
} SleighArtifactPlan;

static bool sleigh_artifact_revision_cb(const RAnalFunctionSnapshot *snapshot, void *user) {
	SleighArtifactRevision *result = user;
	RAnalFunctionSnapshotView view = {0};
	if (!r_anal_function_snapshot_view (snapshot, &view)) {
		return false;
	}
	result->revision = view.revision_identity;
	result->captured = true;
	return true;
}

static bool sleigh_artifact_plan_init(SleighArtifactPlan *plan, RAnal *anal,
		RAnalFunction *fcn, const char *domain_id) {
	if (!plan || !anal || !fcn || !domain_id || !*domain_id) {
		return false;
	}
	memset (plan, 0, sizeof (*plan));
	RCore *core = anal->coreb.core;
	if (!core) {
		return false;
	}
	const ut64 function_epoch = r_anal_function_dirty_epoch (fcn);
	const ut64 type_epoch = r_anal_types_dirty_epoch (anal);
	SleighArtifactRevision revision = {0};
	if (!r_core_function_snapshot_at (core, fcn->addr,
			sleigh_artifact_revision_cb, &revision, NULL)
			|| !revision.captured || !revision.revision
			|| r_anal_function_dirty_epoch (fcn) != function_epoch
			|| r_anal_types_dirty_epoch (anal) != type_epoch) {
		return false;
	}
	plan->core = core;
	plan->domain_id = domain_id;
	plan->scope_id = fcn->addr;
	plan->function_epoch = function_epoch;
	plan->type_epoch = type_epoch;
	plan->snapshot_revision = revision.revision;
	return true;
}

static bool sleigh_artifact_plan_reserve(void **items, size_t *capacity,
		size_t count, size_t item_size) {
	if (!items || !capacity || !item_size) {
		return false;
	}
	if (count < *capacity) {
		return true;
	}
	size_t new_capacity = *capacity? *capacity * 2: 8;
	if (new_capacity <= *capacity) {
		return false;
	}
	size_t allocation_size;
	if (r_mul_overflow (new_capacity, item_size, &allocation_size)) {
		return false;
	}
	void *next = realloc (*items, allocation_size);
	if (!next) {
		return false;
	}
	*items = next;
	*capacity = new_capacity;
	return true;
}

static bool sleigh_artifact_plan_add_comment(SleighArtifactPlan *plan, ut64 addr,
		const char *prefix, const char *text) {
	if (!plan || plan->failed || !prefix || !*prefix || !text || !*text
			|| strchr (prefix, '\n') || strchr (text, '\n')
			|| !r_str_startswith (text, prefix)) {
		if (plan) {
			plan->failed = true;
		}
		return false;
	}
	size_t i;
	for (i = 0; i < plan->comment_count; i++) {
		RCoreAnalArtifactComment *comment = &plan->comments[i];
		if (comment->addr == addr && !strcmp (comment->prefix, prefix)) {
			char *replacement = strdup (text);
			if (!replacement) {
				plan->failed = true;
				return false;
			}
			free ((char *)comment->text);
			comment->text = replacement;
			return true;
		}
	}
	char *owned_prefix = strdup (prefix);
	char *owned_text = strdup (text);
	if (!owned_prefix || !owned_text
			|| !sleigh_artifact_plan_reserve ((void **)&plan->comments,
				&plan->comment_capacity, plan->comment_count, sizeof (*plan->comments))) {
		free (owned_prefix);
		free (owned_text);
		plan->failed = true;
		return false;
	}
	plan->comments[plan->comment_count++] = (RCoreAnalArtifactComment) {
		.addr = addr,
		.prefix = owned_prefix,
		.text = owned_text,
	};
	return true;
}

static bool sleigh_artifact_plan_add_flag(SleighArtifactPlan *plan, const char *name,
		ut64 addr, ut64 size) {
	if (!plan || plan->failed || !name || !*name) {
		if (plan) {
			plan->failed = true;
		}
		return false;
	}
	size_t i;
	for (i = 0; i < plan->flag_count; i++) {
		RCoreAnalArtifactFlag *flag = &plan->flags[i];
		if (!strcmp (flag->name, name)) {
			if (flag->addr != addr || flag->size != size) {
				plan->failed = true;
				return false;
			}
			return true;
		}
	}
	char *owned_name = strdup (name);
	if (!owned_name
			|| !sleigh_artifact_plan_reserve ((void **)&plan->flags,
				&plan->flag_capacity, plan->flag_count, sizeof (*plan->flags))) {
		free (owned_name);
		plan->failed = true;
		return false;
	}
	plan->flags[plan->flag_count++] = (RCoreAnalArtifactFlag) {
		.name = owned_name,
		.addr = addr,
		.size = size,
	};
	return true;
}

static bool sleigh_artifact_plan_add_xref(SleighArtifactPlan *plan, ut64 from,
		ut64 to, RAnalRefType type) {
	if (!plan || plan->failed || from == UT64_MAX || to == UT64_MAX || from == to) {
		if (plan) {
			plan->failed = true;
		}
		return false;
	}
	size_t i;
	for (i = 0; i < plan->xref_count; i++) {
		RAnalRef *xref = &plan->xrefs[i];
		if (xref->at == from && xref->addr == to) {
			if (xref->type != type) {
				plan->failed = true;
				return false;
			}
			return true;
		}
	}
	if (!sleigh_artifact_plan_reserve ((void **)&plan->xrefs,
			&plan->xref_capacity, plan->xref_count, sizeof (*plan->xrefs))) {
		plan->failed = true;
		return false;
	}
	plan->xrefs[plan->xref_count++] = (RAnalRef) {
		.at = from,
		.addr = to,
		.type = type,
	};
	return true;
}

static bool sleigh_artifact_plan_submit(SleighArtifactPlan *plan) {
	if (!plan || plan->failed || !plan->core || !plan->domain_id) {
		return false;
	}
	RCoreAnalArtifactReplacement replacement = {
		.provider_id = "sla",
		.domain_id = plan->domain_id,
		.scope_id = plan->scope_id,
		.expected_function_epoch = plan->function_epoch,
		.expected_type_epoch = plan->type_epoch,
		.expected_snapshot_revision = plan->snapshot_revision,
		.comments = plan->comments,
		.comment_count = plan->comment_count,
		.flags = plan->flags,
		.flag_count = plan->flag_count,
		.xrefs = plan->xrefs,
		.xref_count = plan->xref_count,
	};
	RCoreAnalArtifactReplaceResult result = r_core_anal_artifacts_replace (
		plan->core, &replacement, 1);
	if (result.status != R_CORE_ANAL_ARTIFACT_REPLACE_OK) {
		R_LOG_WARN ("r2sleigh: cannot replace %s artifacts at 0x%08"PFMT64x": %u",
			plan->domain_id, plan->scope_id, result.status);
		return false;
	}
	return true;
}

static void sleigh_artifact_plan_fini(SleighArtifactPlan *plan) {
	if (!plan) {
		return;
	}
	size_t i;
	for (i = 0; i < plan->comment_count; i++) {
		free ((char *)plan->comments[i].prefix);
		free ((char *)plan->comments[i].text);
	}
	for (i = 0; i < plan->flag_count; i++) {
		free ((char *)plan->flags[i].name);
	}
	free (plan->comments);
	free (plan->flags);
	free (plan->xrefs);
	memset (plan, 0, sizeof (*plan));
}

static bool append_unique_ut64(ut64 **items, size_t *count, size_t *capacity, ut64 value) {
	size_t i;
	ut64 *next;

	if (!items || !count || !capacity) {
		return false;
	}

	for (i = 0; i < *count; i++) {
		if ((*items)[i] == value) {
			return true;
		}
	}

	if (*count >= *capacity) {
		size_t new_capacity = *capacity ? (*capacity * 2) : 4;
		next = realloc (*items, new_capacity * sizeof (ut64));
		if (!next) {
			return false;
		}
		*items = next;
		*capacity = new_capacity;
	}

	(*items)[(*count)++] = value;
	return true;
}

static bool append_unique_string(char ***items, size_t *count, size_t *capacity, const char *value) {
	size_t i;
	char **next;
	char *dup;

	if (!items || !count || !capacity || !value || !*value) {
		return false;
	}

	for (i = 0; i < *count; i++) {
		if (!strcmp ((*items)[i], value)) {
			return true;
		}
	}

	if (*count >= *capacity) {
		size_t new_capacity = *capacity ? (*capacity * 2) : 4;
		next = realloc (*items, new_capacity * sizeof (char *));
		if (!next) {
			return false;
		}
		*items = next;
		*capacity = new_capacity;
	}

	dup = strdup (value);
	if (!dup) {
		return false;
	}
	(*items)[(*count)++] = dup;
	return true;
}

static void free_string_array(char **items, size_t count) {
	size_t i;
	if (!items) {
		return;
	}
	for (i = 0; i < count; i++) {
		free (items[i]);
	}
	free (items);
}

static void taint_source_map_init(TaintSourceMap *map) {
	if (!map) {
		return;
	}
	map->items = NULL;
	map->count = 0;
	map->capacity = 0;
}

static void taint_source_map_free(TaintSourceMap *map) {
	size_t i;
	if (!map) {
		return;
	}
	for (i = 0; i < map->count; i++) {
		free (map->items[i].label);
		free (map->items[i].blocks);
	}
	free (map->items);
	map->items = NULL;
	map->count = 0;
	map->capacity = 0;
}

static TaintLabelSource *taint_source_map_get_or_add(TaintSourceMap *map, const char *label) {
	size_t i;
	TaintLabelSource *next;

	if (!map || !label || !*label) {
		return NULL;
	}

	for (i = 0; i < map->count; i++) {
		if (!strcmp (map->items[i].label, label)) {
			return &map->items[i];
		}
	}

	if (map->count >= map->capacity) {
		size_t new_capacity = map->capacity ? (map->capacity * 2) : 8;
		next = realloc (map->items, new_capacity * sizeof (TaintLabelSource));
		if (!next) {
			return NULL;
		}
		map->items = next;
		map->capacity = new_capacity;
	}

	map->items[map->count].label = strdup (label);
	map->items[map->count].blocks = NULL;
	map->items[map->count].count = 0;
	map->items[map->count].capacity = 0;
	if (!map->items[map->count].label) {
		return NULL;
	}
	return &map->items[map->count++];
}

static const TaintLabelSource *taint_source_map_find(const TaintSourceMap *map, const char *label) {
	size_t i;
	if (!map || !label || !*label) {
		return NULL;
	}
	for (i = 0; i < map->count; i++) {
		if (!strcmp (map->items[i].label, label)) {
			return &map->items[i];
		}
	}
	return NULL;
}

static bool taint_source_map_add(TaintSourceMap *map, const char *label, ut64 block_addr) {
	TaintLabelSource *entry = taint_source_map_get_or_add (map, label);
	if (!entry) {
		return false;
	}
	return append_unique_ut64 (&entry->blocks, &entry->count, &entry->capacity, block_addr);
}

static void taint_summary_map_init(TaintSummaryMap *map) {
	if (!map) {
		return;
	}
	map->items = NULL;
	map->count = 0;
	map->capacity = 0;
}

static void taint_summary_map_free(TaintSummaryMap *map) {
	size_t i;
	if (!map) {
		return;
	}
	for (i = 0; i < map->count; i++) {
		free_string_array (map->items[i].call_names, map->items[i].ncall_names);
		free_string_array (map->items[i].labels, map->items[i].nlabels);
	}
	free (map->items);
	map->items = NULL;
	map->count = 0;
	map->capacity = 0;
}

static TaintBlockSummary *taint_summary_map_get_or_add(TaintSummaryMap *map, ut64 addr) {
	size_t i;
	TaintBlockSummary *next;

	if (!map) {
		return NULL;
	}
	for (i = 0; i < map->count; i++) {
		if (map->items[i].addr == addr) {
			return &map->items[i];
		}
	}

	if (map->count >= map->capacity) {
		size_t new_capacity = map->capacity ? (map->capacity * 2) : 8;
		next = realloc (map->items, new_capacity * sizeof (TaintBlockSummary));
		if (!next) {
			return NULL;
		}
		map->items = next;
		map->capacity = new_capacity;
	}

	map->items[map->count].addr = addr;
	map->items[map->count].hits = 0;
	map->items[map->count].call_hits = 0;
	map->items[map->count].store_hits = 0;
	map->items[map->count].call_names = NULL;
	map->items[map->count].ncall_names = 0;
	map->items[map->count].call_name_cap = 0;
	map->items[map->count].labels = NULL;
	map->items[map->count].nlabels = 0;
	map->items[map->count].label_cap = 0;
	return &map->items[map->count++];
}

static bool taint_summary_add_label(TaintBlockSummary *summary, const char *label) {
	if (!summary) {
		return false;
	}
	return append_unique_string (&summary->labels, &summary->nlabels, &summary->label_cap, label);
}

static bool taint_summary_add_call_name(TaintBlockSummary *summary, const char *name) {
	if (!summary) {
		return false;
	}
	return append_unique_string (&summary->call_names, &summary->ncall_names, &summary->call_name_cap, name);
}

typedef enum {
	TAINT_RISK_NONE = 0,
	TAINT_RISK_LOW,
	TAINT_RISK_MEDIUM,
	TAINT_RISK_HIGH,
	TAINT_RISK_CRITICAL,
} TaintRiskLevel;

static const char *taint_risk_level_name(TaintRiskLevel level) {
	switch (level) {
	case TAINT_RISK_CRITICAL:
		return "CRITICAL";
	case TAINT_RISK_HIGH:
		return "HIGH";
	case TAINT_RISK_MEDIUM:
		return "MEDIUM";
	case TAINT_RISK_LOW:
		return "LOW";
	case TAINT_RISK_NONE:
	default:
		return "NONE";
	}
}

static const char *taint_risk_level_flag_name(TaintRiskLevel level) {
	switch (level) {
	case TAINT_RISK_CRITICAL:
		return "critical";
	case TAINT_RISK_HIGH:
		return "high";
	case TAINT_RISK_MEDIUM:
		return "medium";
	case TAINT_RISK_LOW:
		return "low";
	case TAINT_RISK_NONE:
	default:
		return "none";
	}
}

static const char *dangerous_sinks[] = {
	"__memcpy_chk",
	"__memmove_chk",
	"__snprintf_chk",
	"__sprintf_chk",
	"__strcat_chk",
	"__strcpy_chk",
	"memcpy",
	"memmove",
	"strcpy",
	"strcat",
	"gets",
	"sprintf",
	"snprintf",
	"system",
	"execve",
	"execl",
	"popen",
	"read",
	"recv",
	"recvfrom",
	"scanf",
	"fscanf",
};

static int cmp_strings_lex(const void *a, const void *b) {
	const char *sa = *(const char * const *)a;
	const char *sb = *(const char * const *)b;
	return strcmp (sa ? sa : "", sb ? sb : "");
}

static void trim_call_prefixes(char *name) {
	static const char *prefixes[] = {"sym.imp.", "sym.", "dbg.", "imp.", "reloc."};
	bool changed = true;
	size_t i;

	if (!name || !*name) {
		return;
	}

	while (changed) {
		changed = false;
		for (i = 0; i < R_ARRAY_SIZE (prefixes); i++) {
			size_t plen = strlen (prefixes[i]);
			if (r_str_startswith (name, prefixes[i])) {
				memmove (name, name + plen, strlen (name + plen) + 1);
				changed = true;
			}
		}
	}
}

static bool clean_call_name(const char *raw, R_OUT char **result) {
	char *name;
	char *at;
	size_t len;

	if (!result) {
		return false;
	}
	*result = NULL;
	if (!raw || !*raw) {
		return true;
	}

	name = strdup (raw);
	if (!name) {
		return false;
	}

	trim_call_prefixes (name);

	len = strlen (name);
	while (len >= 4 && !strcmp (name + len - 4, "@plt")) {
		name[len - 4] = '\0';
		len -= 4;
	}
	while (len >= 4 && !strcmp (name + len - 4, ".plt")) {
		name[len - 4] = '\0';
		len -= 4;
	}

	at = strchr (name, '@');
	if (at) {
		*at = '\0';
	}

	trim_call_prefixes (name);

	if (!*name) {
		free (name);
		return true;
	}
	*result = name;
	return true;
}

static bool resolve_call_target_name_from_addr(RCore *core, RAnal *anal, ut64 addr,
		R_OUT char **result) {
	const char *raw_name = NULL;

	if (!result) {
		return false;
	}
	*result = NULL;
	if (!core || !anal) {
		return false;
	}

	if (core->flags) {
		RFlagItem *flag = r_flag_get_at (core->flags, addr, false);
		if (flag && flag->name && *flag->name) {
			raw_name = flag->name;
		}
	}
	if (!raw_name) {
		RAnalFunction *target_fcn = r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
		if (target_fcn && target_fcn->name && *target_fcn->name) {
			raw_name = target_fcn->name;
		}
	}
	if (!raw_name) {
		return true;
	}
	return clean_call_name (raw_name, result);
}

static bool is_dangerous_sink(const char *name) {
	size_t i;

	if (!name || !*name) {
		return false;
	}

	for (i = 0; i < R_ARRAY_SIZE (dangerous_sinks); i++) {
		if (!r_str_casecmp (name, dangerous_sinks[i])) {
			return true;
		}
	}
	if (!r_str_ncasecmp (name, "exec", 4)) {
		return true;
	}
	return false;
}

static TaintRiskLevel classify_taint_risk(bool meaningful, bool has_dangerous_call, int call_hits, int store_hits) {
	if (!meaningful) {
		return TAINT_RISK_NONE;
	}
	if (has_dangerous_call) {
		return TAINT_RISK_CRITICAL;
	}
	if (call_hits > 0 && store_hits > 0) {
		return TAINT_RISK_HIGH;
	}
	if (call_hits > 0 || store_hits > 1) {
		return TAINT_RISK_MEDIUM;
	}
	if (store_hits > 0) {
		return TAINT_RISK_LOW;
	}
	return TAINT_RISK_LOW;
}

static bool is_noisy_taint_label(const char *label) {
	if (!label || !*label) {
		return true;
	}

	return !strcmp (label, "input:rsp")
		|| !strcmp (label, "input:rbp")
		|| !strcmp (label, "input:esp")
		|| !strcmp (label, "input:ebp")
		|| !strcmp (label, "input:sp")
		|| !strcmp (label, "input:bp")
		|| !strcmp (label, "input:rip")
		|| !strcmp (label, "input:eip")
		|| !strcmp (label, "input:ip")
		|| r_str_startswith (label, "input:ram:");
}

static int label_rank(const char *label) {
	const char *name = label;
	if (!name) {
		return 1000;
	}
	if (r_str_startswith (name, "input:")) {
		name += 6;
	}

	if (!strcmp (name, "rdi") || !strcmp (name, "edi")) {
		return 0;
	}
	if (!strcmp (name, "rsi") || !strcmp (name, "esi")) {
		return 1;
	}
	if (!strcmp (name, "rdx") || !strcmp (name, "edx")) {
		return 2;
	}
	if (!strcmp (name, "rcx") || !strcmp (name, "ecx")) {
		return 3;
	}
	if (!strcmp (name, "r8") || !strcmp (name, "r8d")) {
		return 4;
	}
	if (!strcmp (name, "r9") || !strcmp (name, "r9d")) {
		return 5;
	}
	if (!strcmp (name, "rax") || !strcmp (name, "eax")) {
		return 10;
	}
	if (!strcmp (name, "rbx") || !strcmp (name, "ebx")) {
		return 11;
	}
	if (!strcmp (name, "r10") || !strcmp (name, "r10d")) {
		return 12;
	}
	if (!strcmp (name, "r11") || !strcmp (name, "r11d")) {
		return 13;
	}
	if (!strcmp (name, "r12") || !strcmp (name, "r12d")) {
		return 14;
	}
	if (!strcmp (name, "r13") || !strcmp (name, "r13d")) {
		return 15;
	}
	if (!strcmp (name, "r14") || !strcmp (name, "r14d")) {
		return 16;
	}
	if (!strcmp (name, "r15") || !strcmp (name, "r15d")) {
		return 17;
	}
	if (r_str_startswith (name, "xmm")) {
		return 40;
	}
	if (r_str_startswith (name, "input:")) {
		return 90;
	}
	return 100;
}

static int cmp_labels_interesting(const void *a, const void *b) {
	const char *la = *(const char * const *)a;
	const char *lb = *(const char * const *)b;
	int ra = label_rank (la);
	int rb = label_rank (lb);

	if (ra < rb) {
		return -1;
	}
	if (ra > rb) {
		return 1;
	}
	return strcmp (la ? la : "", lb ? lb : "");
}

static bool collect_semantic_comments_for_function(SleighArtifactPlan *plan,
		const R2ILContext *ctx, const BlockArray *blocks, bool enabled) {
	size_t i;
	R2SleighAnalysisResultV2 *result = NULL;
	R2SleighAnalysisResultViewV2 view = {0};
	const R2SleighAnnotation *items = NULL;
	size_t count = 0;
	bool success = false;
	if (!plan || !ctx || !blocks) {
		return false;
	}
	if (!enabled || blocks->count == 0) {
		return true;
	}

	if (sleigh_v2_analysis_query (R2SLEIGH_QUERY_ANNOTATIONS_V2,
		ctx, (const R2ILBlock *const *)blocks->blocks, blocks->count,
		plan->scope_id, &result, &view) != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_DEBUG ("r2sleigh: semantic annotation generation failed for fcn=0x%"PFMT64x,
			plan->scope_id);
		goto cleanup;
	}
	items = (const R2SleighAnnotation *)view.primary;
	count = view.primary_count;
	if (!items && count > 0) {
		R_LOG_DEBUG ("r2sleigh: semantic annotation typed payload failure for fcn=0x%"PFMT64x,
			plan->scope_id);
		goto cleanup;
	}

	for (i = 0; i < count; i++) {
		const R2SleighAnnotation *item = &items[i];
		if (!item->comment || !*item->comment) {
			continue;
		}
		if (!sleigh_artifact_plan_add_comment (plan, (ut64)item->addr,
				SLEIGH_COMMENT_PREFIX_SEMANTIC, item->comment)) {
			goto cleanup;
		}
	}
	success = true;
cleanup:
	return sleigh_v2_analysis_result_release (&result) && success;
}

static char *format_taint_summary_comment(TaintBlockSummary *summary) {
	char *comment;
	char *cursor;
	size_t total_len;
	size_t i;
	size_t label_limit;
	int prefix_len;
	int suffix_len;
	char call_count_buf[32];
	const char *call_field = NULL;
	size_t call_field_len = 0;

	if (!summary || !summary->labels || summary->nlabels == 0) {
		return NULL;
	}

	qsort (summary->labels, summary->nlabels, sizeof (char *), cmp_labels_interesting);
	label_limit = R_MIN (summary->nlabels, (size_t)SLEIGH_TAINT_LABEL_MAX);

	if (summary->ncall_names > 0) {
		qsort (summary->call_names, summary->ncall_names, sizeof (char *), cmp_strings_lex);
		call_field_len = 0;
		for (i = 0; i < summary->ncall_names; i++) {
			call_field_len += strlen (summary->call_names[i]);
			if (i > 0) {
				call_field_len += 1;
			}
		}
	} else {
		snprintf (call_count_buf, sizeof (call_count_buf), "%d", summary->call_hits);
		call_field = call_count_buf;
		call_field_len = strlen (call_field);
	}

	prefix_len = snprintf (NULL, 0, "sla.taint: hits=%d calls=", summary->hits);
	suffix_len = snprintf (NULL, 0, " stores=%d labels=", summary->store_hits);
	if (prefix_len < 0 || suffix_len < 0) {
		return NULL;
	}

	total_len = (size_t)prefix_len + call_field_len + (size_t)suffix_len;
	for (i = 0; i < label_limit; i++) {
		total_len += strlen (summary->labels[i]);
		if (i > 0) {
			total_len += 1;
		}
	}
	if (summary->nlabels > label_limit) {
		total_len += 4;
	}

	comment = calloc (1, total_len + 1);
	if (!comment) {
		return NULL;
	}

	snprintf (comment, total_len + 1, "sla.taint: hits=%d calls=", summary->hits);
	cursor = comment + strlen (comment);
	if (summary->ncall_names > 0) {
		for (i = 0; i < summary->ncall_names; i++) {
			if (i > 0) {
				*cursor++ = ',';
			}
			{
				size_t name_len = strlen (summary->call_names[i]);
				memcpy (cursor, summary->call_names[i], name_len);
				cursor += name_len;
			}
		}
	} else {
		size_t count_len = strlen (call_field);
		memcpy (cursor, call_field, count_len);
		cursor += count_len;
	}
	cursor += snprintf (cursor, total_len + 1 - (size_t)(cursor - comment),
		" stores=%d labels=", summary->store_hits);

	for (i = 0; i < label_limit; i++) {
		if (i > 0) {
			*cursor++ = ',';
		}
		size_t label_len = strlen (summary->labels[i]);
		memcpy (cursor, summary->labels[i], label_len);
		cursor += label_len;
	}
	if (summary->nlabels > label_limit) {
		memcpy (cursor, ",...", 4);
		cursor += 4;
	}
	*cursor = '\0';
	return comment;
}

static char *format_taint_risk_comment(
	TaintRiskLevel level,
	char **call_names,
	size_t ncall_names,
	int call_hits,
	int store_hits,
	char **labels,
	size_t nlabels
) {
	char *comment;
	char *cursor;
	size_t total_len = 0;
	size_t i;
	size_t label_limit;
	const char *level_name;
	char call_count_buf[32];
	const char *call_field = NULL;
	size_t call_field_len = 0;

	if (level == TAINT_RISK_NONE) {
		return NULL;
	}

	level_name = taint_risk_level_name (level);
	if (!level_name || !*level_name) {
		return NULL;
	}

	if (ncall_names > 0) {
		qsort (call_names, ncall_names, sizeof (char *), cmp_strings_lex);
		for (i = 0; i < ncall_names; i++) {
			call_field_len += strlen (call_names[i]);
			if (i > 0) {
				call_field_len += 1;
			}
		}
	} else {
		snprintf (call_count_buf, sizeof (call_count_buf), "%d", call_hits);
		call_field = call_count_buf;
		call_field_len = strlen (call_field);
	}

	if (!labels || nlabels == 0) {
		return NULL;
	}
	qsort (labels, nlabels, sizeof (char *), cmp_labels_interesting);
	label_limit = R_MIN (nlabels, (size_t)SLEIGH_TAINT_LABEL_MAX);

	total_len += (size_t)snprintf (NULL, 0, "sla.taint.risk: %s (calls=", level_name);
	total_len += call_field_len;
	total_len += (size_t)snprintf (NULL, 0, " stores=%d labels=", store_hits);
	for (i = 0; i < label_limit; i++) {
		total_len += strlen (labels[i]);
		if (i > 0) {
			total_len += 1;
		}
	}
	if (nlabels > label_limit) {
		total_len += 4;
	}
	total_len += 1; /* ')' */

	comment = calloc (1, total_len + 1);
	if (!comment) {
		return NULL;
	}

	snprintf (comment, total_len + 1, "sla.taint.risk: %s (calls=", level_name);
	cursor = comment + strlen (comment);
	if (ncall_names > 0) {
		for (i = 0; i < ncall_names; i++) {
			if (i > 0) {
				*cursor++ = ',';
			}
			{
				size_t name_len = strlen (call_names[i]);
				memcpy (cursor, call_names[i], name_len);
				cursor += name_len;
			}
		}
	} else {
		size_t count_len = strlen (call_field);
		memcpy (cursor, call_field, count_len);
		cursor += count_len;
	}

	cursor += snprintf (cursor, total_len + 1 - (size_t)(cursor - comment),
		" stores=%d labels=", store_hits);
	for (i = 0; i < label_limit; i++) {
		if (i > 0) {
			*cursor++ = ',';
		}
		{
			size_t label_len = strlen (labels[i]);
			memcpy (cursor, labels[i], label_len);
			cursor += label_len;
		}
	}
	if (nlabels > label_limit) {
		memcpy (cursor, ",...", 4);
		cursor += 4;
	}
	*cursor++ = ')';
	*cursor = '\0';
	return comment;
}

static bool attach_switch_info_to_block(R2ILBlock *block, const RAnalBlock *bb) {
	if (!block || !bb || !bb->switch_op || !bb->switch_op->cases) {
		return true;
	}

	const RAnalSwitchOp *swop = bb->switch_op;
	const int ncases = r_list_length (swop->cases);
	if (ncases <= 0) {
		return true;
	}

	const size_t case_count = (size_t)ncases;
	if (case_count > R2SLEIGH_MAX_SWITCH_CASES_V2) {
		/* Let the Rust boundary record the exact limit failure on the
		 * owning lift context without allocating an oversized C buffer. */
		(void)sleigh_v2_block_set_switch_info (block, swop->addr,
			swop->min_val, swop->max_val, swop->def_val,
			swop->def_val != UT64_MAX, NULL, case_count);
		return false;
	}
	R2SleighSwitchCaseV2 *cases = R_NEWS0 (R2SleighSwitchCaseV2, case_count);
	if (!cases) {
		return false;
	}

	RListIter *iter;
	RAnalCaseOp *caseop;
	size_t i = 0;
	r_list_foreach (swop->cases, iter, caseop) {
		if (!caseop) {
			continue;
		}
		if (i >= case_count) {
			break;
		}
		cases[i].value = caseop->value;
		cases[i].target = caseop->jump;
		i++;
	}

	if (i > 0) {
		const ut64 switch_addr = (swop->jump_addr && swop->jump_addr != UT64_MAX)
			? swop->jump_addr: swop->addr;
		const int has_default = swop->def_val != UT64_MAX;
		const bool accepted = sleigh_v2_block_set_switch_info (block, switch_addr,
			swop->min_val, swop->max_val, swop->def_val,
			has_default, cases, i) == R2SLEIGH_STATUS_OK_V2;
		free (cases);
		return accepted;
	}
	free (cases);
	return false;
}

/* Lift all basic blocks of a function */
static bool lift_function_blocks_with_limits(
	RAnal *anal,
	RAnalFunction *fcn,
	R2ILContext *ctx,
	BlockArray *out,
	size_t max_blocks,
	size_t max_ops
) {
	R_RETURN_VAL_IF_FAIL (anal && fcn && ctx && out, false);

	RListIter *iter;
	RAnalBlock *bb;
	size_t total_ops = 0;

	block_array_init (out);

	r_list_foreach (fcn->bbs, iter, bb) {
		ut8 *buf = NULL;
		size_t lift_size = 0;
		size_t to_read = 0;

		if (!read_block_bytes_for_lifting (anal, bb, &buf, &to_read, &lift_size)) {
			R_LOG_ERROR ("r2sleigh: failed to read block at 0x%"PFMT64x, bb->addr);
			continue;
		}

		/* Lift entire basic block (multiple instructions) */
		R2ILBlock *block = NULL;
		uint32_t lift_status = sleigh_v2_lift_block (ctx, buf, to_read,
			bb->addr, (unsigned int)lift_size, &block);
		if (lift_status == R2SLEIGH_STATUS_OK_V2 && block) {
			if (sleigh_v2_block_validate (ctx, block) != R2SLEIGH_STATUS_OK_V2) {
				char *err = NULL;
				(void)sleigh_v2_context_error (ctx, &err);
				if (err && *err) {
					R_LOG_ERROR ("r2sleigh: invalid block at 0x%"PFMT64x": %s", bb->addr, err);
				} else {
					R_LOG_ERROR ("r2sleigh: invalid block at 0x%"PFMT64x, bb->addr);
				}
				free (err);
				(void)sleigh_v2_block_release (&block);
				free (buf);
				continue;
			}
			size_t block_ops = 0;
			if (sleigh_v2_block_op_count (block, &block_ops) != R2SLEIGH_STATUS_OK_V2) {
				(void)sleigh_v2_block_release (&block);
				free (buf);
				continue;
			}
			if ((max_blocks && out->count >= max_blocks)
				|| (max_ops && (block_ops > max_ops || total_ops > max_ops - block_ops))) {
				R_LOG_ERROR ("r2sleigh: lift budget refused function 0x%"PFMT64x": blocks cap %zu, operations cap %zu",
					fcn->addr, max_blocks, max_ops);
				(void)sleigh_v2_block_release (&block);
				free (buf);
				block_array_free (out);
				return false;
			}
			if (!attach_switch_info_to_block (block, bb)) {
				char *err = NULL;
				(void)sleigh_v2_context_error (ctx, &err);
				R_LOG_ERROR ("r2sleigh: rejected switch metadata at 0x%"PFMT64x"%s%s",
					bb->addr, err && *err? ": ": "", err && *err? err: "");
				free (err);
				(void)sleigh_v2_block_release (&block);
				free (buf);
				continue;
			}
			if (!block_array_push (out, block)) {
				R_LOG_ERROR ("r2sleigh: failed to grow lifted block array for function 0x%"PFMT64x, fcn->addr);
				(void)sleigh_v2_block_release (&block);
				free (buf);
				block_array_free (out);
				return false;
			}
			total_ops += block_ops;
		}
		free (buf);
	}

	return out->count > 0;
}

static bool lift_function_blocks(
	RAnal *anal,
	RAnalFunction *fcn,
	R2ILContext *ctx,
	BlockArray *out
) {
	return lift_function_blocks_with_limits (anal, fcn, ctx, out, 0, 0);
}

static SleighMode sleigh_mode_from_analysis_depth(RAnal *anal) {
	R2SleighAnalysisPolicyV2 rust_policy = sleigh_v2_query_analysis_policy (anal? (unsigned int)anal->plugin_analysis_depth: 0);
	return rust_policy.mode <= (unsigned int)SLEIGH_MODE_FULL? (SleighMode)rust_policy.mode: SLEIGH_MODE_BALANCED;
}

static bool sleigh_mode_is_fast(RAnal *anal) {
	SleighMode mode = sleigh_mode_from_analysis_depth (anal);
	return mode == SLEIGH_MODE_FAST;
}

static void sleigh_profile_clear(void) {
	for (size_t i = 0; i < sleigh_profile_count; i++) {
		free (sleigh_profile_entries[i].name);
	}
	free (sleigh_profile_entries);
	sleigh_profile_entries = NULL;
	sleigh_profile_count = 0;
	sleigh_profile_cap = 0;
}

static SleighProfileEntry *sleigh_profile_entry_get(ut64 addr, const char *name) {
	for (size_t i = 0; i < sleigh_profile_count; i++) {
		if (sleigh_profile_entries[i].addr == addr) {
			if (!sleigh_profile_entries[i].name && name && *name) {
				sleigh_profile_entries[i].name = strdup (name);
			}
			return &sleigh_profile_entries[i];
		}
	}
	if (sleigh_profile_count >= sleigh_profile_cap) {
		size_t next_cap = sleigh_profile_cap? sleigh_profile_cap * 2: 64;
		SleighProfileEntry *next = realloc (sleigh_profile_entries, next_cap * sizeof (*next));
		if (!next) {
			return NULL;
		}
		sleigh_profile_entries = next;
		sleigh_profile_cap = next_cap;
	}
	SleighProfileEntry *entry = &sleigh_profile_entries[sleigh_profile_count++];
	memset (entry, 0, sizeof (*entry));
	entry->addr = addr;
	entry->name = (name && *name)? strdup (name): NULL;
	return entry;
}

static void sleigh_profile_add(RAnal *anal, const RAnalFunction *fcn, SleighProfileStage stage, ut64 elapsed_us) {
	(void)anal;
	const char *name = (fcn && fcn->name)? fcn->name: NULL;
	ut64 addr = fcn? fcn->addr: UT64_MAX;
	SleighProfileEntry *entry = sleigh_profile_entry_get (addr, name);
	if (!entry) {
		return;
	}
	entry->total_us += elapsed_us;
	switch (stage) {
	case SLEIGH_PROFILE_STAGE_LIFT:
		entry->lift_us += elapsed_us;
		break;
	case SLEIGH_PROFILE_STAGE_TYPED_CONTEXT:
		entry->typed_context_us += elapsed_us;
		break;
	case SLEIGH_PROFILE_STAGE_SESSION:
		entry->session_us += elapsed_us;
		break;
	case SLEIGH_PROFILE_STAGE_MUTATION:
		entry->mutation_us += elapsed_us;
		break;
	case SLEIGH_PROFILE_STAGE_XREF:
		entry->xref_us += elapsed_us;
		break;
	case SLEIGH_PROFILE_STAGE_TAINT:
		entry->taint_us += elapsed_us;
		break;
	case SLEIGH_PROFILE_STAGE_DECOMPILE:
		entry->decompile_us += elapsed_us;
		break;
	}
}

static int sleigh_profile_entry_cmp(const void *a, const void *b) {
	const SleighProfileEntry *left = *(const SleighProfileEntry * const *)a;
	const SleighProfileEntry *right = *(const SleighProfileEntry * const *)b;
	if (left->total_us != right->total_us) {
		return left->total_us < right->total_us ? 1 : -1;
	}
	if (left->addr != right->addr) {
		return left->addr < right->addr ? -1 : 1;
	}
	return strcmp (left->name? left->name: "", right->name? right->name: "");
}

static char *sleigh_profile_json(RAnal *anal) {
	(void)anal;
	PJ *pj = pj_new ();
	if (!pj) {
		return NULL;
	}
	size_t max_items = SLEIGH_PROFILE_MAX_DEFAULT;
	SleighProfileEntry **items = NULL;
	if (sleigh_profile_count > 0) {
		items = calloc (sleigh_profile_count, sizeof (*items));
		if (items) {
			for (size_t i = 0; i < sleigh_profile_count; i++) {
				items[i] = &sleigh_profile_entries[i];
			}
			qsort (items, sleigh_profile_count, sizeof (*items), sleigh_profile_entry_cmp);
		}
	}
	pj_o (pj);
	pj_kb (pj, "enabled", true);
	pj_kn (pj, "count", sleigh_profile_count);
	pj_kn (pj, "max", max_items);
	pj_ka (pj, "functions");
	size_t shown = 0;
	if (items) {
		for (size_t i = 0; i < sleigh_profile_count && shown < max_items; i++, shown++) {
			const SleighProfileEntry *entry = items[i];
			pj_o (pj);
			pj_kn (pj, "addr", entry->addr);
			pj_ks (pj, "name", entry->name? entry->name: "");
			pj_kn (pj, "total_us", entry->total_us);
			pj_kn (pj, "lift_us", entry->lift_us);
			pj_kn (pj, "typed_context_us", entry->typed_context_us);
			pj_kn (pj, "session_us", entry->session_us);
			pj_kn (pj, "mutation_us", entry->mutation_us);
			pj_kn (pj, "xref_us", entry->xref_us);
			pj_kn (pj, "taint_us", entry->taint_us);
			pj_kn (pj, "decompile_us", entry->decompile_us);
			pj_end (pj);
		}
	}
	pj_end (pj);
	pj_end (pj);
	free (items);
	return pj_drain (pj);
}

static void configure_context_runtime_options(RAnal *anal, R2ILContext *ctx) {
	if (!ctx) {
		return;
	}
	(void)sleigh_v2_context_set_semantic_metadata (ctx, !sleigh_mode_is_fast (anal));
}

static bool cache_context_reg_profile(R2ILContext *ctx) {
	if (!ctx || ctx != sleigh_ctx) {
		return false;
	}
	char *profile = NULL;
	uint32_t status = sleigh_v2_context_reg_profile (ctx, &profile);
	if (status != R2SLEIGH_STATUS_OK_V2 || R_STR_ISEMPTY (profile)) {
		free (profile);
		return false;
	}
	free (sleigh_reg_profile);
	sleigh_reg_profile = profile;
	return true;
}

static bool install_context_reg_profile(RAnal *anal, R2ILContext *ctx) {
	if (!anal || !anal->reg || !ctx || ctx != sleigh_ctx
			|| R_STR_ISEMPTY (sleigh_reg_profile)) {
		return false;
	}
	if (anal->reg->reg_profile_str
			&& !strcmp (anal->reg->reg_profile_str, sleigh_reg_profile)) {
		return true;
	}
	return r_anal_set_reg_profile (anal, sleigh_reg_profile)
		&& anal->reg->reg_profile_str
		&& !strcmp (anal->reg->reg_profile_str, sleigh_reg_profile);
}

static bool release_sleigh_context(void) {
	if (sleigh_ctx) {
		uint32_t status = sleigh_v2_context_free (sleigh_ctx);
		if (status != R2SLEIGH_STATUS_OK_V2) {
			return false;
		}
		sleigh_ctx = NULL;
	}
	free (sleigh_reg_profile);
	sleigh_reg_profile = NULL;
	return true;
}

/* ---------------------------------------------------------------------------
 * Machine evidence -> Sleigh language
 *
 * One decision, one implementation. Both entry points (the anal plugin, which
 * reads asm.arch/asm.bits/asm.cpu/asm.abi/cfg.bigendian, and the arch plugin,
 * which reads the binary's own headers) funnel their evidence through
 * SleighMachine and get the same answer.
 *
 * A NULL answer is a refusal, and refusing is the correct output whenever no
 * bundled language matches the evidence. Loading a neighbouring language
 * instead yields well-formed, confidently wrong disassembly, which is worse
 * than none.
 * ------------------------------------------------------------------------ */

typedef struct {
	const char *arch;	/* asm.arch or RBinInfo.arch */
	int bits;		/* 16 means Thumb on ARM, real mode on x86 */
	bool big_endian;
	const char *cpu;	/* asm.cpu or RBinInfo.cpu, may be NULL */
	const char *abi;	/* asm.abi or RBinInfo.abi, may be NULL */
} SleighMachine;

/* ARMv6 introduced BE8: only data is big-endian, instructions stay
 * little-endian. Pre-v6 big-endian ARM (BE32) fetches instructions big-endian
 * too. Ghidra draws exactly this line -- ARM:LEBE:32:v8LEInstruction uses
 * ARM8_le.sla while ARM:BE:32:v8 uses ARM8_be.sla -- and the ELF e_flags bit
 * is the only evidence, which radare2 surfaces as " be8" inside the ABI
 * string. */
static bool sleigh_arm_instructions_are_big_endian(const SleighMachine *m) {
	if (!m->big_endian) {
		return false;
	}
	return !(m->abi && strstr (m->abi, "be8"));
}

static const char *sleigh_language_for_arm(const SleighMachine *m) {
	if (m->bits == 64) {
		/* Data endianness follows the slaspec, so a big-endian AArch64 image
		 * needs the big-endian language even though the encoding is fixed. */
		return m->big_endian? "arm64be": "arm64";
	}
	/* radare2 spells Thumb as asm.bits=16; asm.cpu=cortex is Thumb-only. */
	const bool thumb = (m->bits == 16)
		|| (m->cpu && !r_str_casecmp (m->cpu, "cortex"));
	const bool be = sleigh_arm_instructions_are_big_endian (m);
	if (thumb) {
		return be? "thumbbe": "thumb";
	}
	return be? "armbe": "arm";
}

/* MIPS release 6 re-encoded and removed instructions the pre-R6 languages
 * still accept, so it needs its own slaspec rather than the base one. */
static bool sleigh_mips_cpu_is_r6(const char *cpu) {
	const size_t len = strlen (cpu);
	return len >= 2 && !r_str_casecmp (cpu + len - 2, "r6");
}

/* Set when a machine we otherwise support carries a variant no bundled
 * language covers. A bare refusal reads as a missing backend, so the caller
 * says this once instead of leaving `invalid` unexplained. Left NULL for
 * architectures this build simply does not carry, which stay quiet so other
 * plugins can take over. */
static const char *sleigh_refusal_reason = NULL;

static const char *sleigh_refuse(const char *why) {
	sleigh_refusal_reason = why;
	return NULL;
}

static const char *sleigh_language_for_mips(const SleighMachine *m) {
	const char *arch = m->arch;
	bool is64 = m->bits >= 64
		|| !strcmp (arch, "mips64")
		|| !strcmp (arch, "mips64be")
		|| !strcmp (arch, "mips64le")
		|| !strcmp (arch, "mips64el");
	bool be = m->big_endian;
	if (!strcmp (arch, "mipsel") || !strcmp (arch, "mips32le")
			|| !strcmp (arch, "mips32el")
			|| !strcmp (arch, "mips64le")
			|| !strcmp (arch, "mips64el")) {
		be = false;
	} else if (!strcmp (arch, "mips32be") || !strcmp (arch, "mipsbe")
			|| !strcmp (arch, "mipseb") || !strcmp (arch, "mips64be")) {
		be = true;
	}
	if (m->cpu) {
		/* microMIPS and MIPS16e are distinct encodings selected by the
		 * ISA_MODE context bit. sleigh-config bundles mips32micro.pspec, but
		 * it only clears RELP: every micromips constructor is additionally
		 * gated on ISA_MODE=1, which no bundled pspec sets and the lift API
		 * offers no way to override. Under the base MIPS32 language these
		 * images decode as real mnemonics at misaligned offsets interleaved
		 * with `invalid`, so refuse. */
		if (!r_str_casecmp (m->cpu, "micro") || strstr (m->cpu, "micromips")) {
			return sleigh_refuse ("microMIPS decoding needs the ISA_MODE context bit, which no bundled processor spec sets");
		}
		if (strstr (m->cpu, "mips16") || !r_str_casecmp (m->cpu, "16")) {
			return sleigh_refuse ("MIPS16e decoding needs the ISA_MODE context bit, which no bundled processor spec sets");
		}
		if (sleigh_mips_cpu_is_r6 (m->cpu)) {
			if (is64) {
				/* mips64R6.pspec is bundled but no MIPS64 R6 slaspec is. */
				return sleigh_refuse ("no MIPS64 release-6 slaspec is bundled");
			}
			return be? "mips32r6be": "mips32r6le";
		}
	}
	if (is64) {
		return be? "mips64be": "mips64le";
	}
	return be? "mips32be": "mips32le";
}

static const char *sleigh_language_for_machine(const SleighMachine *m) {
	sleigh_refusal_reason = NULL;
	if (!m->arch || !*m->arch) {
		return NULL;
	}
	const char *arch = m->arch;
	if (!strcmp (arch, "x86")) {
		if (m->big_endian) {
			return sleigh_refuse ("no big-endian x86 language exists");
		}
		if (m->bits == 16) {
			return sleigh_refuse ("x86-16 ships a processor spec but no slaspec");
		}
		return (m->bits == 64)? "x86-64": "x86";
	}
	if (!strcmp (arch, "arm") || !strcmp (arch, "thumb")) {
		return sleigh_language_for_arm (m);
	}
	if (!strcmp (arch, "arm64") || !strcmp (arch, "aarch64")) {
		SleighMachine wide = *m;
		wide.bits = 64;
		return sleigh_language_for_arm (&wide);
	}
	if (!strcmp (arch, "riscv") || !strcmp (arch, "riscv32")
			|| !strcmp (arch, "riscv64") || !strcmp (arch, "rv32")
			|| !strcmp (arch, "rv64")) {
		if (m->big_endian) {
			return sleigh_refuse ("only the little-endian RISC-V languages are bundled");
		}
		if (!strcmp (arch, "riscv32") || !strcmp (arch, "rv32")) {
			return "riscv32";
		}
		if (!strcmp (arch, "riscv64") || !strcmp (arch, "rv64")) {
			return "riscv64";
		}
		return (m->bits >= 64)? "riscv64": "riscv32";
	}
	if (!strncmp (arch, "mips", 4)) {
		return sleigh_language_for_mips (m);
	}
	return NULL; /* unsupported architecture */
}

/* The arch plugin's route: decide from the binary's own headers. */
const char *r2sleigh_language_for_bin_info(RBinInfo *info) {
	if (!info || !info->arch) {
		return NULL;
	}
	SleighMachine machine = {
		.arch = info->arch,
		.bits = info->bits,
		.big_endian = info->big_endian != 0,
		.cpu = info->cpu,
		.abi = info->abi,
	};
	return sleigh_language_for_machine (&machine);
}

/* asm.arch=r2sleigh names this plugin, not a machine. The decoder still
 * reaches a language through the binary's headers, so answer from that same
 * evidence rather than reporting nothing loaded. */
static bool sleigh_arch_is_not_a_machine(const char *arch) {
	return !strcmp (arch, "r2sleigh") || !strcmp (arch, "null")
		|| !strcmp (arch, "any");
}

static const char *sleigh_language_for_anal(RAnal *anal) {
	RBinInfo *info = anal->binb.bin? r_bin_get_info (anal->binb.bin): NULL;
	if (sleigh_arch_is_not_a_machine (anal->config->arch)) {
		return r2sleigh_language_for_bin_info (info);
	}
	SleighMachine machine = {
		.arch = anal->config->arch,
		.bits = anal->config->bits,
		.big_endian = R_ARCH_CONFIG_IS_BIG_ENDIAN (anal->config),
		.cpu = anal->config->cpu,
		.abi = anal->config->abi,
	};
	/* The session config is authoritative, but it carries no BE8 flag of its
	 * own when the user never set asm.abi; borrow that one fact from the
	 * headers rather than guessing BE32. */
	if (!machine.abi && info && info->abi && info->arch
			&& !strcmp (info->arch, machine.arch)) {
		machine.abi = info->abi;
	}
	return sleigh_language_for_machine (&machine);
}

static void sleigh_report_refusal(RAnal *anal) {
	if (!sleigh_refusal_reason) {
		return;
	}
	static char *last = NULL;
	char *what = r_str_newf ("%s|%d|%s", anal->config->arch, anal->config->bits,
		anal->config->cpu? anal->config->cpu: "-");
	if (!what) {
		return;
	}
	if (last && !strcmp (last, what)) {
		free (what);
		return;
	}
	free (last);
	last = what;
	R_LOG_WARN ("r2sleigh: refusing to disassemble: %s", sleigh_refusal_reason);
}

R2ILContext *get_context(RAnal *anal) {
	if (!anal || !anal->config || !anal->config->arch[0]) {
		return NULL;
	}
	const char *sleigh_arch_str = sleigh_arch_override
		? sleigh_arch_override
		: sleigh_language_for_anal (anal);
	if (!sleigh_arch_str) {
		/* No bundled language matches this machine. Say why once when the
		 * architecture itself is one we carry, so a refusal is not mistaken
		 * for a missing backend; stay quiet otherwise so other plugins can
		 * take over without noise. */
		sleigh_report_refusal (anal);
		return NULL;
	}

	/* Check if we need to reinitialize */
	if (sleigh_ctx && sleigh_arch && !strcmp (sleigh_arch, sleigh_arch_str)) {
		if (!install_context_reg_profile (anal, sleigh_ctx)) {
			R_LOG_DEBUG ("r2sleigh: cached register profile installation failed for %s", sleigh_arch_str);
			return NULL;
		}
		configure_context_runtime_options (anal, sleigh_ctx);
		return sleigh_ctx;
	}

	/* Free old context */
	if (!release_sleigh_context ()) {
		R_LOG_ERROR ("r2sleigh: refusing architecture reload because context free failed");
		return NULL;
	}
	free (sleigh_arch);
	sleigh_arch = NULL;

	/* Initialize new context */
	uint32_t status = sleigh_v2_context_create (sleigh_arch_str, &sleigh_ctx);
	if (status != R2SLEIGH_STATUS_OK_V2 || !sleigh_ctx) {
		/* Optional-arch builds are expected to miss some backends; stay silent
		 * so unsupported architectures fall back to other anal plugins. */
		R_LOG_DEBUG ("r2sleigh: backend unavailable for %s", sleigh_arch_str);
		if (sleigh_ctx && !release_sleigh_context ()) {
			R_LOG_ERROR ("r2sleigh: retaining failed context handle after create failure");
		}
		return NULL;
	}

	uint32_t loaded = 0;
	if (sleigh_v2_context_is_loaded (sleigh_ctx, &loaded) != R2SLEIGH_STATUS_OK_V2 || !loaded) {
		char *err = NULL;
		(void)sleigh_v2_context_error (sleigh_ctx, &err);
		if (err && *err) {
			R_LOG_DEBUG ("r2sleigh: %s", err);
		}
		free (err);
		if (!release_sleigh_context ()) {
			R_LOG_ERROR ("r2sleigh: retaining failed context handle");
		}
		return NULL;
	}

	/* Establish the exact Sleigh register geometry before any typed consumer. */
	char *loaded_arch = strdup (sleigh_arch_str);
	if (!loaded_arch || !cache_context_reg_profile (sleigh_ctx)
			|| !install_context_reg_profile (anal, sleigh_ctx)) {
		R_LOG_DEBUG ("r2sleigh: failed to install register profile for %s", sleigh_arch_str);
		free (loaded_arch);
		if (!release_sleigh_context ()) {
			R_LOG_ERROR ("r2sleigh: retaining context after register profile failure");
		}
		return NULL;
	}
	sleigh_arch = loaded_arch;

	configure_context_runtime_options (anal, sleigh_ctx);
	return sleigh_ctx;
}

int sleigh_op(RAnal *anal, RAnalOp *op, ut64 addr, const ut8 *data, int len, RAnalOpMask mask) {
	R_RETURN_VAL_IF_FAIL (anal && op && data, -1);

	R2ILContext *ctx = get_context (anal);
	if (!ctx) {
		return -1;
	}

	/* Ensure we have enough bytes for libsla */
	ut8 buf[SLEIGH_MIN_BYTES] = {0};
	int use_len = len;
	const ut8 *use_data = data;

	if (len < SLEIGH_MIN_BYTES) {
		memset (buf, 0, sizeof (buf));
		memcpy (buf, data, len);
		use_data = buf;
		use_len = SLEIGH_MIN_BYTES;
	}

	R2ILBlock *block = NULL;
	if (sleigh_v2_lift_instruction (sleigh_ctx, use_data, use_len, addr, &block)
		!= R2SLEIGH_STATUS_OK_V2 || !block) {
		return -1;
	}

	op->addr = addr;
	uint32_t block_size = 0;
	uint32_t block_type = 0;
	if (sleigh_v2_block_size (block, &block_size) != R2SLEIGH_STATUS_OK_V2
		|| sleigh_v2_block_type (block, &block_type) != R2SLEIGH_STATUS_OK_V2) {
		(void)sleigh_v2_block_release (&block);
		return -1;
	}
	op->size = block_size;
	op->type = block_type;
	ut64 jump_addr = 0;
	(void)sleigh_v2_block_jump (block, &jump_addr);
	if (jump_addr != 0) {
		op->jump = jump_addr;
	}
	ut64 fail_addr = 0;
	(void)sleigh_v2_block_fail (block, &fail_addr);
	if (fail_addr != 0) {
		op->fail = fail_addr;
	}

	if (mask & R_ARCH_OP_MASK_DISASM) {
		char *mnem = NULL;
		(void)sleigh_v2_block_mnemonic (ctx, use_data, use_len, addr, &mnem);
		if (mnem) {
			op->mnemonic = strdup (mnem);
			free (mnem);
		}
	}

	if (mask & R_ARCH_OP_MASK_ESIL) {
		char *esil = NULL;
		const R2ILBlock *blocks[] = { block };
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_BLOCK_ESIL_V2,
			ctx, blocks, 1, 0, NULL, &esil);
		if (esil) {
			r_strbuf_set (&op->esil, esil);
			free (esil);
		}
	}

	if (mask & R_ARCH_OP_MASK_VAL) {
		RVecRArchValue_clear (&op->srcs);
		RVecRArchValue_clear (&op->dsts);
		fill_op_values_enhanced (anal, op, ctx, block);
	}

	(void)sleigh_v2_block_release (&block);
	return op->size;
}

static bool sleigh_init(RAnal *anal) {
	/* Prime context early so register aliases are available before aa/aaa passes. */
	(void)get_context (anal);
	return true;
}

static bool sleigh_fini(RAnal *anal) {
	(void)anal;
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	uint32_t status = sleigh_v2_owned_bytes_release (api, &sleigh_pending_owned_bytes);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return false;
	}
	status = sleigh_engine_v2_retry_pending (api);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return false;
	}
	if (!release_sleigh_context ()) {
		R_LOG_ERROR ("r2sleigh: retaining context after free failure");
		return false;
	}
	free (sleigh_arch);
	sleigh_arch = NULL;
	return true;
}

static bool cmd_matches_exact_or_arg(const char *cmd, const char *prefix) {
	size_t len;
	if (!cmd || !prefix) {
		return false;
	}
	len = strlen (prefix);
	return !strncmp (cmd, prefix, len) && (!cmd[len] || isspace ((unsigned char)cmd[len]));
}

static bool cmd_matches_family(const char *cmd, const char *prefix) {
	if (!cmd || !prefix) {
		return false;
	}
	size_t prefix_len = strlen (prefix);
	if (strncmp (cmd, prefix, prefix_len)) {
		return false;
	}
	return !cmd[prefix_len] || cmd[prefix_len] == '.' || isspace ((unsigned char)cmd[prefix_len]);
}

static bool sleigh_direct_sla_debug_only_command(const char *cmd) {
	if (!cmd) {
		return false;
	}
	if (!strcmp (cmd, "sla.info")
		|| !strcmp (cmd, "sla.json")
		|| !strcmp (cmd, "sla.regs")
		|| !strcmp (cmd, "sla.opvals")
		|| !strcmp (cmd, "sla.mem")
		|| !strcmp (cmd, "sla.vars")
		|| !strcmp (cmd, "sla.ssa")
		|| !strcmp (cmd, "sla.defuse")
		|| !strcmp (cmd, "sla.ssa.func")
		|| !strcmp (cmd, "sla.ssa.func.opt")
		|| !strcmp (cmd, "sla.defuse.func")
		|| !strcmp (cmd, "sla.dom")
		|| !strcmp (cmd, "sla.taint")
		|| !strcmp (cmd, "sla.cfg")
		|| !strcmp (cmd, "sla.cfg.json")) {
		return true;
	}
	return cmd_matches_exact_or_arg (cmd, "sla.arch")
		|| cmd_matches_exact_or_arg (cmd, "sla.profilej")
		|| cmd_matches_exact_or_arg (cmd, "sla.assumptions-")
		|| cmd_matches_exact_or_arg (cmd, "sla.assumptions")
		|| cmd_matches_exact_or_arg (cmd, "sla.assumej")
		|| cmd_matches_exact_or_arg (cmd, "sla.slice")
		|| cmd_matches_exact_or_arg (cmd, "sla.sym.paths")
		|| cmd_matches_exact_or_arg (cmd, "sla.sym");
}

static bool sleigh_direct_sym_snapshot_required_command(const char *cmd) {
	if (!cmd) {
		return false;
	}
	return cmd_matches_exact_or_arg (cmd, "sym.runj")
		|| cmd_matches_exact_or_arg (cmd, "sym.replayj")
		|| cmd_matches_family (cmd, "sym.explore")
		|| cmd_matches_family (cmd, "sym.solve")
		|| cmd_matches_family (cmd, "sym.state")
		|| cmd_matches_exact_or_arg (cmd, "sla.sym.paths")
		|| cmd_matches_exact_or_arg (cmd, "sla.sym");
}

static char *sleigh_decompile_execute(RAnal *anal, RAnalFunction *fcn, bool json_projection);


static char *sleigh_decompile_execute(RAnal *anal, RAnalFunction *fcn, bool json_projection) {
	(void)anal;
	(void)fcn;
	R_LOG_ERROR ("r2sleigh: direct decompile commands cannot construct source authority; use radare2's borrowed snapshot decompiler provider");
	return json_projection
		? sleigh_engine_v2_error_json ("borrowed_snapshot_required",
			R2SLEIGH_STATUS_UNSUPPORTED_V2,
			"decompilation requires the borrowed snapshot provider")
		: NULL;
}

static RCodeMeta *sleigh_decompile(const RAnalFunctionSnapshot *snapshot) {
	R_RETURN_VAL_IF_FAIL (snapshot, NULL);
	/* Serialize once and hand the engine one buffer. The accessor table stays
	 * wired as the fallback while the two paths are compared; when it goes, so
	 * do its callbacks and their size handshakes. */
	size_t buffer_len = 0;
	uint8_t *buffer = NULL;
	R2SleighWireWriter *writer = r2sleigh_wire_writer_new ();
	if (writer) {
		if (r2sleigh_wire_write_snapshot (writer, snapshot)) {
			buffer = r2sleigh_wire_writer_finish (writer, &buffer_len);
		}
		r2sleigh_wire_writer_free (writer);
	}
	const R2SleighEngineRequestPayloadV2 payload = {
		.abi_version = R2SLEIGH_ABI_V2,
		.struct_size = sizeof (payload),
		.timeout_us = 0,
		.snapshot_buffer = buffer,
		.snapshot_buffer_len = buffer_len,
	};
	char *result = sleigh_engine_execute_v2 (
		R2SLEIGH_REQUEST_DECOMPILE_V2,
		R2SLEIGH_CAP_DECOMPILE_V2 | R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2,
		&payload);
	free (buffer);
	if (!result) {
		R_LOG_ERROR ("r2sleigh: borrowed snapshot decompilation was refused");
		return NULL;
	}
	RCodeMeta *metadata = r_codemeta_new (result);
	free (result);
	return metadata;
}

static char *sleigh_cmd(RAnal *anal, const char *cmd) {
	bool is_sla_ns = r_str_startswith (cmd, "sla");
	bool is_sym_ns = r_str_startswith (cmd, "sym");
	bool is_sla_debug_ns = false;
	char debug_cmd[4096];
	if (!is_sla_ns && !is_sym_ns) {
		return NULL;
	}

	RCore *core = anal->coreb.core;
	RCons *cons = core ? core->cons : NULL;

	if (r_str_startswith (cmd, "sla.debug.")) {
		int n = snprintf (debug_cmd, sizeof (debug_cmd), "sla.%s", cmd + strlen ("sla.debug."));
		if (n < 0 || (size_t)n >= sizeof (debug_cmd)) {
			if (cons) {
				r_cons_println (cons, "r2sleigh: debug command too long");
			}
			return strdup ("");
		}
		cmd = debug_cmd;
		is_sla_debug_ns = true;
	}
	if (r_str_startswith (cmd, "sym.debug.")) {
		int n = snprintf (debug_cmd, sizeof (debug_cmd), "sym.%s", cmd + strlen ("sym.debug."));
		if (n < 0 || (size_t)n >= sizeof (debug_cmd)) {
			if (cons) {
				r_cons_println (cons, "r2sleigh: debug command too long");
			}
			return strdup ("");
		}
		cmd = debug_cmd;
	}
	if (!strcmp (cmd, "sla.dec?") || !strcmp (cmd, "sla.dec ?")) {
		if (cons) {
			r_cons_println (cons, "sla.dec is unavailable outside radare2's borrowed-snapshot decompiler provider; use pdd.");
		}
		return strdup ("");
	}
	if (!strcmp (cmd, "sla.decj?") || !strcmp (cmd, "sla.decj ?")) {
		if (cons) {
			r_cons_println (cons, "sla.decj is unavailable outside radare2's borrowed-snapshot decompiler provider; use pdd.");
		}
		return strdup ("");
	}

	if (sleigh_direct_sym_snapshot_required_command (cmd)) {
		R_LOG_ERROR ("r2sleigh: symbolic execution requires a borrowed function snapshot");
		if (cons) {
			r_cons_println (cons, "r2sleigh: symbolic execution requires the borrowed function snapshot provider");
		}
		return strdup ("");
	}
	if (!is_sla_debug_ns) {
		if (sleigh_direct_sla_debug_only_command (cmd)) {
			// Engine inspection lives under the debug namespace. Returning an
			// empty string here left the bare spelling looking like a command
			// that ran and had nothing to say.
			R_LOG_ERROR ("r2sleigh: '%s' is engine inspection; use 'a:sla.debug.%s'",
				cmd, cmd + strlen ("sla."));
			if (cons) {
				r_cons_printf (cons, "r2sleigh: use a:sla.debug.%s\n",
					cmd + strlen ("sla."));
			}
			return strdup ("");
		}
	}

	if (cmd[3] == '?') {
		if (cons) {
			r_cons_println (cons, "| a:sla        - Show r2sleigh status");
			r_cons_println (cons, "| pdd - decompile through the borrowed-snapshot provider");
			r_cons_println (cons, "| a:sla.debug.* - engine inspection (ssa, defuse, dom, cfg, taint, regs, mem, vars)");
			r_cons_println (cons, "| a:sla.dec / a:sla.decj - unavailable outside that provider");
			r_cons_println (cons, "| a:sym.* - unavailable without the borrowed function snapshot provider");
		}
		return strdup("");
	}

	if (is_sla_ns && !strcmp (cmd, "sla.profilej")) {
		char *profile_json = sleigh_profile_json (anal);
		if (cons && profile_json) {
			r_cons_printf (cons, "%s\n", profile_json);
		}
		free (profile_json);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.assumptions-") || (!strncmp (cmd, "sla.assumptions-", 16) && isspace ((unsigned char)cmd[16]))) {
		const char *target_arg = skip_cmd_spaces (cmd + 16);
		RAnalFunction *fcn = (target_arg && *target_arg)
			? resolve_or_materialize_function_target (core, anal, target_arg)
			: resolve_or_materialize_current_function (core, anal);
		if (!fcn) {
			if (target_arg && *target_arg) {
				R_LOG_ERROR ("r2sleigh: function target not found: %s", target_arg);
			} else {
				R_LOG_ERROR ("r2sleigh: no function at current address");
			}
			return strdup ("");
		}
		if (!r_anal_function_set_assumptions_json (anal, fcn, "")) {
			R_LOG_ERROR ("r2sleigh: failed to clear assumptions for 0x%"PFMT64x, fcn->addr);
			return strdup ("");
		}
		if (cons) {
			r_cons_println (cons, "[]");
		}
		return strdup ("");
	}

	if (!strncmp (cmd, "sla.assumptions", 15) && (!cmd[15] || isspace ((unsigned char)cmd[15]))) {
		const char *target_arg = skip_cmd_spaces (cmd + 15);
		RAnalFunction *fcn = (target_arg && *target_arg)
			? resolve_or_materialize_function_target (core, anal, target_arg)
			: resolve_or_materialize_current_function (core, anal);
		char *assumptions_json;
		if (!fcn) {
			if (target_arg && *target_arg) {
				R_LOG_ERROR ("r2sleigh: function target not found: %s", target_arg);
			} else {
				R_LOG_ERROR ("r2sleigh: no function at current address");
			}
			return strdup ("");
		}
		assumptions_json = sleigh_collect_function_assumptions_json (anal, fcn);
		if (cons) {
			r_cons_printf (cons, "%s\n", assumptions_json? assumptions_json: "[]");
		}
		free (assumptions_json);
		return strdup ("");
	}

	if (!strncmp (cmd, "sla.assumej", 11) && (!cmd[11] || isspace ((unsigned char)cmd[11]))) {
		const char *arg = skip_cmd_spaces (cmd + 11);
		RAnalFunction *fcn;
		char *assumptions_json;

		if (!arg || !*arg) {
			if (cons) {
				r_cons_println (cons, "Usage: a:sla.assumej <json-array>");
			}
			return strdup ("");
		}
		fcn = resolve_or_materialize_current_function (core, anal);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup ("");
		}
		assumptions_json = strdup (arg);
		if (!assumptions_json) {
			return strdup ("");
		}
		r_str_unescape (assumptions_json);
		if (!r_anal_function_set_assumptions_json (anal, fcn, assumptions_json)) {
			R_LOG_ERROR ("r2sleigh: invalid assumptions json array");
			free (assumptions_json);
			return strdup ("");
		}
		free (assumptions_json);
		assumptions_json = sleigh_collect_function_assumptions_json (anal, fcn);
		if (cons) {
			r_cons_printf (cons, "%s\n", assumptions_json? assumptions_json: "[]");
		}
		free (assumptions_json);
		return strdup ("");
	}

	if (!strncmp (cmd, "sla.arch", 8)) {
		const char *arg = cmd + 8;
		if (*arg == ' ') {
			arg++; // skip space
			while (*arg == ' ') arg++;
			if (*arg) {
				if (!release_sleigh_context ()) {
					R_LOG_ERROR ("r2sleigh: architecture unchanged because context free failed");
					return strdup ("");
				}
				/* Set override */
				free (sleigh_arch_override);
				sleigh_arch_override = strdup (arg);
				/* Force context reload on next use */
				free (sleigh_arch);
				sleigh_arch = NULL;
				if (cons) {
					r_cons_printf (cons, "r2sleigh: architecture set to '%s' (reload deferred)\n", sleigh_arch_override);
				}
			}
		} else {
			/* Get current */
			R2ILContext *ctx = get_context (anal);
			char *name = NULL;
			if (ctx) {
				(void)sleigh_v2_context_arch_name (ctx, &name);
			}
			const char *loaded = ctx? (sleigh_arch? sleigh_arch: name): NULL;
			if (cons) {
				r_cons_println (cons, loaded? loaded: "none");
			}
			free (name);
		}
		return strdup("");
	}

	if (!strcmp (cmd, "sla") || !strcmp (cmd, "sla.info")) {
		R2ILContext *ctx = get_context (anal);
		if (ctx) {
			/* Report the language key that actually selected the slaspec and
			 * pspec, not the coarser ArchSpec name: "ARM" alone cannot say
			 * whether A32 or Thumb, little- or big-endian, is in use. */
			char *name = NULL;
			(void)sleigh_v2_context_arch_name (ctx, &name);
			const char *loaded = sleigh_arch? sleigh_arch: (name? name: "unknown");
			if (cons) {
				r_cons_printf (cons, "sla: loaded architecture '%s'\n", loaded);
			}
			free (name);
		} else {
			if (cons) {
				r_cons_println (cons, "sla: no architecture loaded (unsupported or init failed)");
			}
		}
		return strdup("");
	}

	if (!strcmp (cmd, "sla.json")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		/* Get current seek */
		ut64 addr = core->addr;

		ut8 buf[SLEIGH_MIN_BYTES] = {0};
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = NULL;
		if (sleigh_v2_lift_instruction (ctx, buf, sizeof (buf), addr, &block)
			!= R2SLEIGH_STATUS_OK_V2 || !block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		size_t count = 0;
		(void)sleigh_v2_block_op_count (block, &count);
		if (cons) {
			r_cons_println (cons, "[");
		}
		if (count == 0) {
			if (cons) {
				r_cons_println (cons, "  {\"Nop\":{},\"note\":\"instruction lifted with no semantic ops\"}");
			}
		} else {
			size_t i;
			for (i = 0; i < count; i++) {
				char *json = NULL;
				const R2ILBlock *blocks[] = { block };
				(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_BLOCK_OP_JSON_V2,
					ctx, blocks, 1, i, NULL, &json);
				if (json && cons) {
					r_cons_printf (cons, "  %s%s\n", json, (i + 1 < count) ? "," : "");
				}
				free (json);
			}
		}
		if (cons) {
			r_cons_println (cons, "]");
		}

		(void)sleigh_v2_block_release (&block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.regs")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES] = {0};
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = NULL;
		if (sleigh_v2_lift_instruction (ctx, buf, sizeof (buf), addr, &block)
			!= R2SLEIGH_STATUS_OK_V2 || !block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *read_json = NULL;
		char *write_json = NULL;
		const R2ILBlock *blocks[] = { block };
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_BLOCK_REGS_READ_V2,
			ctx, blocks, 1, 0, NULL, &read_json);
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_BLOCK_REGS_WRITE_V2,
			ctx, blocks, 1, 0, NULL, &write_json);

		if (cons) {
			r_cons_printf (cons, "{\"read\":%s,\"write\":%s}\n",
				read_json ? read_json : "[]",
				write_json ? write_json : "[]");
		}

		free (read_json);
		free (write_json);
		(void)sleigh_v2_block_release (&block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.opvals")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES] = {0};
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = NULL;
		if (sleigh_v2_lift_instruction (ctx, buf, sizeof (buf), addr, &block)
			!= R2SLEIGH_STATUS_OK_V2 || !block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		RVecRArchValue srcs;
		RVecRArchValue dsts;
		RVecRArchValue_init (&srcs);
		RVecRArchValue_init (&dsts);

		R2SleighAnalysisResultV2 *result = NULL;
		R2SleighAnalysisResultViewV2 view = {0};
		const R2ILBlock *query_blocks[] = { block };
		if (sleigh_v2_analysis_query (R2SLEIGH_QUERY_BLOCK_VALUES_V2,
			ctx, query_blocks, 1, 0, &result, &view)
			== R2SLEIGH_STATUS_OK_V2) {
			const R2ILBlockRegValue *reads = (const R2ILBlockRegValue *)view.tertiary;
			const R2ILBlockRegValue *writes = (const R2ILBlockRegValue *)view.quaternary;
			add_typed_reg_values (anal, reads, view.tertiary_count, &srcs, R_PERM_R);
			add_typed_reg_values (anal, writes, view.quaternary_count, &dsts, R_PERM_W);
			(void)sleigh_v2_analysis_result_release (&result);
		}

		if (cons) {
			r_cons_print (cons, "{\"srcs\":[");
			print_reg_values_json (cons, &srcs);
			r_cons_print (cons, "],\"dsts\":[");
			print_reg_values_json (cons, &dsts);
			r_cons_println (cons, "]}");
		}

		RVecRArchValue_fini (&srcs);
		RVecRArchValue_fini (&dsts);
		(void)sleigh_v2_block_release (&block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.mem")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES] = {0};
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = NULL;
		if (sleigh_v2_lift_instruction (ctx, buf, sizeof (buf), addr, &block)
			!= R2SLEIGH_STATUS_OK_V2 || !block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *mem_json = NULL;
		const R2ILBlock *blocks[] = { block };
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_BLOCK_MEMORY_V2,
			ctx, blocks, 1, 0, NULL, &mem_json);
		if (cons && mem_json) {
			r_cons_printf (cons, "%s\n", mem_json);
		}

		free (mem_json);
		(void)sleigh_v2_block_release (&block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.vars")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES] = {0};
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = NULL;
		if (sleigh_v2_lift_instruction (ctx, buf, sizeof (buf), addr, &block)
			!= R2SLEIGH_STATUS_OK_V2 || !block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *vars_json = NULL;
		const R2ILBlock *blocks[] = { block };
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_BLOCK_VARNODES_V2,
			ctx, blocks, 1, 0, NULL, &vars_json);
		if (cons && vars_json) {
			r_cons_printf (cons, "%s\n", vars_json);
		}

		free (vars_json);
		(void)sleigh_v2_block_release (&block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.ssa")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES] = {0};
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = NULL;
		if (sleigh_v2_lift_instruction (ctx, buf, sizeof (buf), addr, &block)
			!= R2SLEIGH_STATUS_OK_V2 || !block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *ssa_json = NULL;
		const R2ILBlock *blocks[] = { block };
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_BLOCK_SSA_V2,
			ctx, blocks, 1, 0, NULL, &ssa_json);
		if (cons && ssa_json) {
			r_cons_printf (cons, "%s\n", ssa_json);
		}

		free (ssa_json);
		(void)sleigh_v2_block_release (&block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.defuse")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES] = {0};
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = NULL;
		if (sleigh_v2_lift_instruction (ctx, buf, sizeof (buf), addr, &block)
			!= R2SLEIGH_STATUS_OK_V2 || !block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *defuse_json = NULL;
		const R2ILBlock *blocks[] = { block };
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_BLOCK_DEFUSE_V2,
			ctx, blocks, 1, 0, NULL, &defuse_json);
		if (cons && defuse_json) {
			r_cons_printf (cons, "%s\n", defuse_json);
		}

		free (defuse_json);
		(void)sleigh_v2_block_release (&block);
		return strdup("");
	}

	/* ========== Function-level SSA commands ========== */

	if (!strcmp (cmd, "sla.ssa.func")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		/* Get current function */
		RAnalFunction *fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}

		/* Lift all blocks */
		BlockArray blocks;
		ut64 profile_start_us = r_time_now_mono ();
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}
		sleigh_profile_add (anal, fcn, SLEIGH_PROFILE_STAGE_LIFT, r_time_now_mono () - profile_start_us);

		/* Get function SSA */
		char *result = NULL;
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_FUNCTION_SSA_V2,
			ctx, (const R2ILBlock *const *)blocks.blocks, blocks.count,
			0, NULL, &result);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		free (result);
		block_array_free (&blocks);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.ssa.func.opt")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		RAnalFunction *fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}

		BlockArray blocks;
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}

		char *result = NULL;
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_FUNCTION_SSA_OPT_V2,
			ctx, (const R2ILBlock *const *)blocks.blocks, blocks.count,
			0, NULL, &result);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		free (result);
		block_array_free (&blocks);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.defuse.func")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		/* Get current function */
		RAnalFunction *fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}

		/* Lift all blocks */
		BlockArray blocks;
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}

		/* Get function def-use analysis */
		char *result = NULL;
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_FUNCTION_DEFUSE_V2,
			ctx, (const R2ILBlock *const *)blocks.blocks, blocks.count,
			0, NULL, &result);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		free (result);
		block_array_free (&blocks);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.dom")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		/* Get current function */
		RAnalFunction *fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}

		/* Lift all blocks */
		BlockArray blocks;
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}

		/* Get dominator tree */
		char *result = NULL;
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_FUNCTION_DOMTREE_V2,
			ctx, (const R2ILBlock *const *)blocks.blocks, blocks.count,
			0, NULL, &result);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		free (result);
		block_array_free (&blocks);
		return strdup("");
	}

	if (!strncmp (cmd, "sla.slice", 9)) {
		const char *arg = cmd + 9;
		if (*arg == ' ') {
			arg++;
			while (*arg == ' ') {
				arg++;
			}
		}

		if (!*arg) {
			if (cons) {
				r_cons_println (cons, "Usage: a:sla.debug.slice <var_name>");
				r_cons_println (cons, "Example: a:sla.debug.slice rax_3");
				r_cons_println (cons, "         a:sla.debug.slice zf_1");
			}
			return strdup("");
		}

		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		/* Get current function */
		RAnalFunction *fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}

		/* Lift all blocks */
		BlockArray blocks;
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}

		/* Get backward slice */
		char *result = NULL;
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_FUNCTION_SLICE_V2,
			ctx, (const R2ILBlock *const *)blocks.blocks, blocks.count,
			0, arg, &result);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		free (result);
		block_array_free (&blocks);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.taint")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		/* Get current function */
		RAnalFunction *fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}

		/* Lift all blocks */
		BlockArray blocks;
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}

		char *result = NULL;
		(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_FUNCTION_TAINT_V2,
			ctx, (const R2ILBlock *const *)blocks.blocks, blocks.count,
			0, NULL, &result);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		free (result);
		block_array_free (&blocks);
		return strdup("");
	}

	if (cmd_matches_exact_or_arg (cmd, "sla.decj")) {
		char *json = sleigh_decompile_execute (anal, NULL, true);
		if (cons && json) {
			r_cons_printf (cons, "%s\n", json);
		}
		free (json);
		return strdup ("");
	}

	if (cmd_matches_exact_or_arg (cmd, "sla.dec")) {
		(void)sleigh_decompile_execute (anal, NULL, false);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.cfg") || !strcmp (cmd, "sla.cfg.json")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		/* Get current function */
		RAnalFunction *fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}

		/* Lift all blocks */
		BlockArray blocks;
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}

		/* Generate CFG */
		char *result = NULL;
		const uint32_t kind = !strcmp (cmd, "sla.cfg.json")
			? R2SLEIGH_ANALYSIS_FUNCTION_CFG_JSON_V2
			: R2SLEIGH_ANALYSIS_FUNCTION_CFG_ASCII_V2;
		(void)sleigh_v2_analysis_render (kind, ctx,
			(const R2ILBlock *const *)blocks.blocks, blocks.count,
			0, NULL, &result);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		free (result);
		block_array_free (&blocks);
		return strdup("");
	}

	R_LOG_ERROR ("Unknown subcommand. See 'a:sla?' or 'a:sym?' for help");
	return strdup("");
}

/* ============================================================================
 * radare2 Deep Integration Callbacks
 * These are called automatically by radare2 during analysis (aaa, afv, ax)
 * ============================================================================ */

/* Called after function analysis completes */
static bool sleigh_analyze_fcn(RAnal *anal, RAnalFunction *fcn) {
	if (!fcn || !anal) {
		return false;
	}

	if (!auto_callback_allows_function (
		anal,
		fcn,
		R2SLEIGH_AUTO_CALLBACK_ANALYZE_FUNCTION_V2,
		"analyze_fcn")) {
		return true;
	}

	R2ILContext *ctx = get_context (anal);
	if (!ctx) {
		return false;
	}
	SleighArtifactPlan plan;
	if (!sleigh_artifact_plan_init (&plan, anal, fcn, "semantic")) {
		return false;
	}

	BlockArray blocks;
	if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
		sleigh_artifact_plan_fini (&plan);
		return false;
	}

	bool collected = collect_semantic_comments_for_function (&plan, ctx, &blocks, true);
	bool committed = collected && sleigh_artifact_plan_submit (&plan);
	size_t semantic_comments_emitted = committed? plan.comment_count: 0;
	R_LOG_DEBUG ("r2sleigh: semantic comments fcn=0x%"PFMT64x" enabled=%d emitted=%zu",
		plan.scope_id, 1, semantic_comments_emitted);

	block_array_free (&blocks);
	sleigh_artifact_plan_fini (&plan);
	return committed;
}

static RAnalRefType data_ref_type_from_json(RAnal *anal, ut64 to_addr, const char *type_name) {
	if (type_name && *type_name) {
		switch (type_name[0]) {
		case 'c':
		case 'C':
			return R_ANAL_REF_TYPE_CALL;
		case 'j':
		case 'J':
			return R_ANAL_REF_TYPE_JUMP;
		case 's':
		case 'S':
			return R_ANAL_REF_TYPE_STRN;
		default:
			break;
		}
	}
	return r_anal_get_fcn_in (anal, to_addr, 0)? R_ANAL_REF_TYPE_CODE: R_ANAL_REF_TYPE_DATA;
}

static RAnalRefType data_ref_type_from_kind(RAnal *anal, ut64 to_addr, char kind) {
	char type_name[2] = { kind, 0 };
	return data_ref_type_from_json (anal, to_addr, kind? type_name: NULL);
}

static bool data_ref_targets_ram(const R2SleighDataRef *item) {
	return item
		&& item->space_kind == R2SLEIGH_DATA_REF_SPACE_RAM
		&& item->custom_space == 0;
}

static bool collect_data_refs_from_typed(
	RAnal *anal,
	RAnalFunction *fcn,
	const R2SleighDataRef *items,
	size_t count,
	RVecAnalRef *refs,
	R_OUT size_t *discovered
) {
	if (!discovered) {
		return false;
	}
	*discovered = 0;
	size_t i;
	if (!anal || !items || count == 0) {
		return false;
	}
	for (i = 0; i < count; i++) {
		if (!data_ref_targets_ram (&items[i])) {
			continue;
		}
		ut64 from_addr = (ut64)items[i].from;
		ut64 to_addr = (ut64)items[i].to;
		if (fcn && to_addr >= fcn->addr && to_addr < fcn->addr + r_anal_function_linear_size (fcn)) {
			continue;
		}
		if (refs) {
			RAnalRef *ref = RVecAnalRef_emplace_back (refs);
			if (!ref) {
				return false;
			}
			*ref = (RAnalRef) {
				.at = from_addr,
				.addr = to_addr,
				.type = data_ref_type_from_kind (anal, to_addr, items[i].ref_kind),
			};
		}
		(*discovered)++;
	}
	return true;
}

/* Called during reference analysis (aar) */
static bool sleigh_get_data_refs(RAnal *anal, RAnalFunction *fcn, R_OUT RVecAnalRef **refs) {
	if (!refs) {
		return false;
	}
	*refs = NULL;
	if (!fcn || !anal) {
		return false;
	}
	if (!auto_callback_allows_function (
		anal,
		fcn,
		R2SLEIGH_AUTO_CALLBACK_DATA_REFS_V2,
		"get_data_refs")) {
		return false;
	}

	R2ILContext *ctx = get_context (anal);
	if (!ctx) {
		return false;
	}

	BlockArray blocks;
	if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
		return false;
	}

	bool success = false;
	RVecAnalRef *result = NULL;
	R2SleighAnalysisResultV2 *typed_refs = NULL;
	R2SleighAnalysisResultViewV2 typed_view = {0};
	uint32_t typed_status = sleigh_v2_analysis_query (R2SLEIGH_QUERY_DATA_REFS_V2,
		ctx, (const R2ILBlock *const *)blocks.blocks, blocks.count, fcn->addr,
		&typed_refs, &typed_view);
	if (typed_status != R2SLEIGH_STATUS_OK_V2) {
		goto beach;
	}
	size_t typed_count = typed_view.primary_count;
	if (!typed_count) {
		success = true;
		goto beach;
	}
	const R2SleighDataRef *typed_items = (const R2SleighDataRef *)typed_view.primary;
	if (!typed_items) {
		goto beach;
	}
	size_t ref_count = 0;
	if (!collect_data_refs_from_typed (
			anal, fcn, typed_items, typed_count, NULL, &ref_count)) {
		goto beach;
	}
	if (!ref_count) {
		success = true;
		goto beach;
	}
	result = RVecAnalRef_new ();
	if (!result || !RVecAnalRef_reserve (result, ref_count)) {
		goto beach;
	}
	size_t written = 0;
	if (!collect_data_refs_from_typed (
			anal, fcn, typed_items, typed_count, result, &written)
			|| written != ref_count) {
		goto beach;
	}
	*refs = result;
	result = NULL;
	success = true;
beach:
	RVecAnalRef_free (result);
	(void)sleigh_v2_analysis_result_release (&typed_refs);
	block_array_free (&blocks);
	return success;
}

typedef struct {
	size_t sink_hits;
	TaintRiskLevel risk_level;
	int best_sink_rank;
	ut64 best_sink_addr;
	char *best_sink_label;
} SleighTaintPlanStats;

static void sleigh_taint_plan_stats_fini(SleighTaintPlanStats *stats) {
	if (!stats) {
		return;
	}
	free (stats->best_sink_label);
	memset (stats, 0, sizeof (*stats));
}

/* Whether a function has anything for the prover to work on.
 *
 * Proving costs a snapshot capture and an engine round trip per function, and
 * on a statically linked binary that is hundreds of them. What the prover
 * contributes is targets for transfers radare2 could not follow and blocks
 * nothing reaches, so a function whose every transfer already has a known
 * target has nothing here to find. The deep pass takes them all regardless. */
static bool sleigh_function_may_prove(RAnalFunction *fcn) {
	if (!fcn || !fcn->bbs) {
		return false;
	}
	RListIter *iter;
	RAnalBlock *bb;
	r_list_foreach (fcn->bbs, iter, bb) {
		if (!bb) {
			continue;
		}
		if (bb->switch_op) {
			return true;
		}
		/* A block ending with no known successor ended in a transfer radare2
		 * could not resolve, which is what the prover reads. */
		if (bb->jump == UT64_MAX && bb->fail == UT64_MAX) {
			return true;
		}
	}
	return false;
}

/* Every fact the engine proved about one function, as JSON.
 *
 * The snapshot has to be serialized inside the borrow: the pointer tables the
 * proof needs are read from memory during the capture, and the snapshot stops
 * being valid the moment the callback returns. */
typedef struct {
	uint8_t *buffer;
	size_t len;
} SleighSnapshotWire;

static bool sleigh_snapshot_wire_cb(const RAnalFunctionSnapshot *snapshot, void *user) {
	SleighSnapshotWire *out = user;
	R2SleighWireWriter *writer = r2sleigh_wire_writer_new ();
	if (!writer) {
		return false;
	}
	if (r2sleigh_wire_write_snapshot (writer, snapshot)) {
		out->buffer = r2sleigh_wire_writer_finish (writer, &out->len);
	}
	r2sleigh_wire_writer_free (writer);
	return out->buffer != NULL;
}

static char *sleigh_proven_facts_json(RCore *core, ut64 function_addr) {
	SleighSnapshotWire wire = {0};
	if (!r_core_function_snapshot_at (core, function_addr,
			sleigh_snapshot_wire_cb, &wire, NULL) || !wire.buffer) {
		free (wire.buffer);
		return NULL;
	}
	const R2SleighEngineRequestPayloadV2 payload = {
		.abi_version = R2SLEIGH_ABI_V2,
		.struct_size = sizeof (payload),
		.timeout_us = 0,
		.snapshot_buffer = wire.buffer,
		.snapshot_buffer_len = wire.len,
	};
	char *json = sleigh_engine_execute_v2 (R2SLEIGH_REQUEST_PROVEN_FACTS_V2,
		R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2, &payload);
	free (wire.buffer);
	return json;
}

/* Turn the proofs into the xrefs and comments radare2 stores.
 *
 * A resolved dispatch becomes one call xref per entry the index can select,
 * which is what makes the callees reachable to every later pass. The comment
 * next to it names the table and the count so a reader can check the claim
 * instead of taking it. */
static bool collect_proof_artifacts_for_function(SleighArtifactPlan *plan,
		RCore *core, RAnalFunction *fcn, size_t *out_xrefs, size_t *out_dead) {
	char *json = sleigh_proven_facts_json (core, fcn->addr);
	if (!json) {
		// Refusing is the fail-closed path, so say which function and move on.
		R_LOG_DEBUG ("r2sleigh: no proofs for 0x%08"PFMT64x, fcn->addr);
		return false;
	}
	R_LOG_DEBUG ("r2sleigh: proofs at 0x%08"PFMT64x": %s", fcn->addr, json);
	RJson *facts = r_json_parse (json);
	if (!facts) {
		free (json);
		return false;
	}
	bool ok = true;
	const RJson *calls = r_json_get (facts, "indirect_calls");
	if (calls && calls->type == R_JSON_ARRAY) {
		const RJson *call;
		for (call = calls->children.first; call && ok; call = call->next) {
			const RJson *block = r_json_get (call, "block");
			const RJson *table = r_json_get (call, "table");
			const RJson *targets = r_json_get (call, "targets");
			if (!block || !table || !targets || targets->type != R_JSON_ARRAY) {
				continue;
			}
			size_t count = 0;
			const RJson *target;
			for (target = targets->children.first; target; target = target->next) {
				if (!sleigh_artifact_plan_add_xref (plan, block->num.u_value,
						target->num.u_value, R_ANAL_REF_TYPE_CALL)) {
					ok = false;
					break;
				}
				count++;
			}
			if (!ok || !count) {
				continue;
			}
			char *note = r_str_newf (
				SLEIGH_COMMENT_PREFIX_PROOF
				" dispatch through table 0x%08"PFMT64x
				" reaches exactly %zu of its entries",
				table->num.u_value, count);
			if (!note || !sleigh_artifact_plan_add_comment (plan,
					block->num.u_value, SLEIGH_COMMENT_PREFIX_PROOF, note)) {
				ok = false;
			}
			free (note);
			if (out_xrefs) {
				*out_xrefs += count;
			}
		}
	}
	const RJson *dead = r_json_get (facts, "unreachable_blocks");
	if (ok && dead && dead->type == R_JSON_ARRAY) {
		const RJson *entry;
		for (entry = dead->children.first; entry && ok; entry = entry->next) {
			const RJson *addr = r_json_get (entry, "addr");
			const RJson *reason = r_json_get (entry, "reason");
			if (!addr || !reason || reason->type != R_JSON_STRING) {
				continue;
			}
			char *note = r_str_newf (SLEIGH_COMMENT_PREFIX_PROOF
				" unreachable, %s", reason->str_value);
			if (!note || !sleigh_artifact_plan_add_comment (plan,
					addr->num.u_value, SLEIGH_COMMENT_PREFIX_PROOF, note)) {
				ok = false;
			}
			free (note);
			if (out_dead) {
				*out_dead += 1;
			}
		}
	}
	r_json_free (facts);
	free (json);
	return ok;
}

static bool collect_taint_artifacts_for_function(SleighArtifactPlan *plan,
		RAnal *anal, const R2ILContext *ctx, const BlockArray *blocks,
		SleighTaintPlanStats *stats) {
	R2SleighAnalysisResultV2 *result = NULL;
	R2SleighAnalysisResultViewV2 view = {0};
	TaintSourceMap source_map;
	TaintSummaryMap summaries;
	char **function_call_names = NULL;
	size_t function_ncall_names = 0;
	size_t function_call_name_cap = 0;
	char **function_labels = NULL;
	size_t function_nlabels = 0;
	size_t function_label_cap = 0;
	int function_call_hits = 0;
	int function_store_hits = 0;
	bool function_meaningful = false;
	bool function_has_dangerous_call = false;
	bool success = false;
	size_t i;

	if (!plan || !anal || !ctx || !blocks || !stats) {
		return false;
	}
	memset (stats, 0, sizeof (*stats));
	stats->best_sink_rank = 1000;
	taint_source_map_init (&source_map);
	taint_summary_map_init (&summaries);
	uint32_t status = sleigh_v2_analysis_query (R2SLEIGH_QUERY_TAINT_SUMMARY_V2,
		ctx, (const R2ILBlock *const *)blocks->blocks, blocks->count, 0,
		&result, &view);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		goto cleanup;
	}
	const R2TaintSource *sources = (const R2TaintSource *)view.primary;
	const R2TaintSinkHit *sink_hits = (const R2TaintSinkHit *)view.secondary;
	if ((!sources && view.primary_count > 0)
			|| (!sink_hits && view.secondary_count > 0)) {
		goto cleanup;
	}

	for (i = 0; i < view.primary_count; i++) {
		const R2TaintSource *source = &sources[i];
		if (source->num_labels > 0 && !source->labels) {
			goto cleanup;
		}
		size_t label_index;
		for (label_index = 0; label_index < source->num_labels; label_index++) {
			const char *label = source->labels? source->labels[label_index]: NULL;
			if (label && *label
					&& !taint_source_map_add (&source_map, label, (ut64)source->block)) {
				goto cleanup;
			}
		}
	}

	for (i = 0; i < view.secondary_count; i++) {
		const R2TaintSinkHit *hit = &sink_hits[i];
		char **sink_labels = NULL;
		size_t sink_label_count = 0;
		size_t sink_label_cap = 0;
		ut64 sink_block = (ut64)hit->block;
		bool is_call_sink = hit->op_kind == R2TAINT_OP_CALL
			|| hit->op_kind == R2TAINT_OP_CALL_IND;
		bool had_primary_sources = false;
		bool added_nonself = false;
		size_t variable_index;
		size_t label_index;
		if (hit->num_tainted_vars > 0 && !hit->tainted_vars) {
			goto cleanup;
		}

		for (variable_index = 0; variable_index < hit->num_tainted_vars; variable_index++) {
			const R2TaintTaintedVar *variable = &hit->tainted_vars[variable_index];
			if (variable->num_labels > 0 && !variable->labels) {
				free_string_array (sink_labels, sink_label_count);
				goto cleanup;
			}
			for (label_index = 0; label_index < variable->num_labels; label_index++) {
				const char *label = variable->labels? variable->labels[label_index]: NULL;
				if (label && *label && !is_noisy_taint_label (label)
						&& !append_unique_string (&sink_labels, &sink_label_count,
							&sink_label_cap, label)) {
					free_string_array (sink_labels, sink_label_count);
					goto cleanup;
				}
			}
		}

		TaintBlockSummary *summary = taint_summary_map_get_or_add (&summaries, sink_block);
		if (!summary) {
			free_string_array (sink_labels, sink_label_count);
			goto cleanup;
		}
		stats->sink_hits++;
		summary->hits++;
		if (is_call_sink) {
			summary->call_hits++;
		}
		if (hit->op_kind == R2TAINT_OP_STORE) {
			summary->store_hits++;
		}
		if (is_call_sink && hit->has_target_addr) {
			char *call_name = NULL;
			if (!resolve_call_target_name_from_addr (
					plan->core, anal, (ut64)hit->target_addr, &call_name)) {
				free_string_array (sink_labels, sink_label_count);
				goto cleanup;
			}
			if (call_name) {
				bool added = taint_summary_add_call_name (summary, call_name);
				free (call_name);
				if (!added) {
					free_string_array (sink_labels, sink_label_count);
					goto cleanup;
				}
			}
		}
		for (label_index = 0; label_index < sink_label_count; label_index++) {
			if (!taint_summary_add_label (summary, sink_labels[label_index])) {
				free_string_array (sink_labels, sink_label_count);
				goto cleanup;
			}
		}
		for (label_index = 0; label_index < sink_label_count; label_index++) {
			const TaintLabelSource *label_sources = taint_source_map_find (
				&source_map, sink_labels[label_index]);
			if (!label_sources || !label_sources->count) {
				continue;
			}
			had_primary_sources = true;
			size_t source_index;
			for (source_index = 0; source_index < label_sources->count; source_index++) {
				ut64 source_block = label_sources->blocks[source_index];
				if (source_block == sink_block) {
					continue;
				}
				if (!sleigh_artifact_plan_add_xref (plan, source_block,
						sink_block, R_ANAL_REF_TYPE_DATA)) {
					free_string_array (sink_labels, sink_label_count);
					goto cleanup;
				}
				added_nonself = true;
			}
		}
		if (had_primary_sources && !added_nonself && sink_block != plan->scope_id
				&& !sleigh_artifact_plan_add_xref (plan, plan->scope_id,
					sink_block, R_ANAL_REF_TYPE_DATA)) {
			free_string_array (sink_labels, sink_label_count);
			goto cleanup;
		}
		free_string_array (sink_labels, sink_label_count);
	}

	for (i = 0; i < summaries.count; i++) {
		TaintBlockSummary *summary = &summaries.items[i];
		size_t label_index;
		if (summary->nlabels > 0
				&& (summary->hits > 0 || summary->call_hits > 0 || summary->store_hits > 0)) {
			function_meaningful = true;
			function_call_hits += summary->call_hits;
			function_store_hits += summary->store_hits;
			for (label_index = 0; label_index < summary->ncall_names; label_index++) {
				if (!append_unique_string (&function_call_names, &function_ncall_names,
						&function_call_name_cap, summary->call_names[label_index])) {
					goto cleanup;
				}
				if (is_dangerous_sink (summary->call_names[label_index])) {
					function_has_dangerous_call = true;
				}
			}
		}
		for (label_index = 0; label_index < summary->nlabels; label_index++) {
			if (!append_unique_string (&function_labels, &function_nlabels,
					&function_label_cap, summary->labels[label_index])) {
				goto cleanup;
			}
		}
		if (summary->nlabels > 0) {
			char *comment = format_taint_summary_comment (summary);
			if (!comment) {
				goto cleanup;
			}
			bool added = sleigh_artifact_plan_add_comment (plan, summary->addr,
				SLEIGH_COMMENT_PREFIX_TAINT, comment);
			free (comment);
			if (!added) {
				goto cleanup;
			}
			char flag_name[160];
			snprintf (flag_name, sizeof (flag_name),
				"sla.taint.fcn_%"PFMT64x".blk_%"PFMT64x,
				plan->scope_id, summary->addr);
			if (!sleigh_artifact_plan_add_flag (plan, flag_name, summary->addr, 1)) {
				goto cleanup;
			}
			int rank = label_rank (summary->labels[0]);
			if (rank < stats->best_sink_rank) {
				char *label = strdup (summary->labels[0]);
				if (!label) {
					goto cleanup;
				}
				free (stats->best_sink_label);
				stats->best_sink_label = label;
				stats->best_sink_addr = summary->addr;
				stats->best_sink_rank = rank;
			}
		}
	}

	stats->risk_level = classify_taint_risk (function_meaningful,
		function_has_dangerous_call, function_call_hits, function_store_hits);
	if (stats->risk_level != TAINT_RISK_NONE) {
		char *risk_comment = format_taint_risk_comment (stats->risk_level,
			function_call_names, function_ncall_names, function_call_hits,
			function_store_hits, function_labels, function_nlabels);
		if (!risk_comment) {
			goto cleanup;
		}
		bool added = sleigh_artifact_plan_add_comment (plan, plan->scope_id,
			SLEIGH_COMMENT_PREFIX_TAINT_RISK, risk_comment);
		free (risk_comment);
		if (!added) {
			goto cleanup;
		}
		char flag_name[192];
		snprintf (flag_name, sizeof (flag_name),
			"sla.taint.risk.fcn_%"PFMT64x, plan->scope_id);
		if (!sleigh_artifact_plan_add_flag (plan, flag_name, plan->scope_id, 1)) {
			goto cleanup;
		}
		snprintf (flag_name, sizeof (flag_name),
			"sla.taint.risk.%s.fcn_%"PFMT64x,
			taint_risk_level_flag_name (stats->risk_level), plan->scope_id);
		if (!sleigh_artifact_plan_add_flag (plan, flag_name, plan->scope_id, 1)) {
			goto cleanup;
		}
	}
	success = true;

cleanup:
	free_string_array (function_call_names, function_ncall_names);
	free_string_array (function_labels, function_nlabels);
	taint_summary_map_free (&summaries);
	taint_source_map_free (&source_map);
	if (!sleigh_v2_analysis_result_release (&result)) {
		success = false;
	}
	return success;
}

/* Eligibility/priority callback: score > 0 = eligible with priority, < 0 = ineligible */
static int sleigh_eligible(RAnal *anal) {
	R2ILContext *ctx = get_context (anal);
	return ctx ? 10 : -1;
}

/* Reapply the cached context profile before variable/DWARF integration. The
 * context is process-global while register state belongs to each RAnal. */
static bool sleigh_pre_analysis(RAnal *anal) {
	R2ILContext *ctx = get_context (anal);
	if (!ctx || !install_context_reg_profile (anal, ctx)) {
		R_LOG_DEBUG ("r2sleigh: pre-analysis register profile installation failed");
		return false;
	}
	return true;
}

/* Called at end of aaaa for global post-analysis passes */
static bool sleigh_post_analysis(RAnal *anal) {
	R2ILContext *ctx = get_context (anal);
	size_t taint_comments = 0;
	size_t taint_flags = 0;
	size_t taint_xrefs = 0;
	size_t proof_xrefs = 0;
	size_t proof_dead_blocks = 0;
	int proof_fcns = 0;
	int proof_refused = 0;
	int proof_skipped = 0;
	int taint_parse_failures = 0;
	int taint_fcns_eligible = 0;
	int taint_fcns_skipped = 0;
	size_t taint_sink_hits = 0;
	int taint_risk_critical = 0;
	int taint_risk_high = 0;
	int taint_risk_medium = 0;
	int taint_risk_low = 0;
	int best_sink_rank = 1000;
	ut64 best_sink_addr = 0;
	ut64 focus_callee_addr = 0;
	char *best_sink_label = NULL;
	int num_fcns = anal && anal->fcns? r_list_length (anal->fcns): 0;
	R2SleighPostAnalysisPlanV2 post_plan = sleigh_v2_query_post_analysis (
		anal? (unsigned int)anal->plugin_analysis_depth: 0,
		(size_t)num_fcns);
	SleighMode post_mode = post_plan.mode <= (unsigned int)SLEIGH_MODE_FULL
		? (SleighMode)post_plan.mode: SLEIGH_MODE_BALANCED;
	bool taint_enabled = post_plan.taint_enabled != 0;
	bool taint_focus_only = post_plan.taint_focus_only != 0;
	ut64 post_budget_us = post_plan.post_budget_us;
	SleighPostAnalysisBudget post_budget = sleigh_post_analysis_budget_new (post_budget_us);
	bool post_budget_exhausted = false;

	if (!ctx) {
		return false;
	}
	RCore *core = anal->coreb.core;
	if (core) {
		RAnalFunction *focus_fcn = r_anal_get_fcn_in (anal, core->addr, 0);
		if (focus_fcn) {
			focus_callee_addr = focus_fcn->addr;
		}
	}

	if (num_fcns == 0) {
		return true;
	}
	sleigh_profile_clear ();
	if (post_mode == SLEIGH_MODE_FAST) {
		R_LOG_INFO ("r2sleigh: post-analysis running in basic mode");
	} else if (post_mode == SLEIGH_MODE_BALANCED) {
		R_LOG_INFO ("r2sleigh: post-analysis running in balanced mode");
	} else {
		R_LOG_INFO ("r2sleigh: post-analysis running in aggressive mode");
	}

	RListIter *iter;
	RAnalFunction *fcn;
	r_list_foreach (anal->fcns, iter, fcn) {
		if (!sleigh_post_analysis_budget_allows (&post_budget, "function sweep")) {
			post_budget_exhausted = true;
			break;
		}
		if (!fcn) {
			continue;
		}
		/* Proofs run for every function, not just the ones taint looks at.
		 * They are what the analysis pass is here to contribute, and the work
		 * is the engine's rather than ours. */
		SleighArtifactPlan proof_plan;
		const bool proof_eligible = post_mode >= SLEIGH_MODE_FULL
			|| sleigh_function_may_prove (fcn);
		if (proof_eligible && sleigh_artifact_plan_init (&proof_plan, anal, fcn, "proof")) {
			if (collect_proof_artifacts_for_function (&proof_plan, core, fcn,
					&proof_xrefs, &proof_dead_blocks)
					&& sleigh_artifact_plan_submit (&proof_plan)) {
				proof_fcns++;
			} else {
				proof_refused++;
			}
			sleigh_artifact_plan_fini (&proof_plan);
		} else if (!proof_eligible) {
			proof_skipped++;
		}
		int bb_count = fcn->bbs? r_list_length (fcn->bbs): 0;
		bool auto_callback_allowed = !taint_enabled || auto_callback_allows_function (
			anal, fcn, R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_TAINT_V2,
			"post_analysis_taint");
		bool taint_scope_eligible = !taint_focus_only
			|| (focus_callee_addr && fcn->addr == focus_callee_addr);
		bool taint_eligible = taint_enabled && taint_scope_eligible
			&& bb_count <= SLEIGH_TAINT_MAX_BLOCKS && auto_callback_allowed;
		SleighArtifactPlan taint_plan;
		if (!sleigh_artifact_plan_init (&taint_plan, anal, fcn, "taint")) {
			continue;
		}
		if (taint_enabled) {
			if (taint_eligible) {
				taint_fcns_eligible++;
			} else {
				taint_fcns_skipped++;
			}
		}
		if (!taint_eligible) {
			(void)sleigh_artifact_plan_submit (&taint_plan);
			sleigh_artifact_plan_fini (&taint_plan);
			continue;
		}
		if (!sleigh_post_analysis_budget_allows (&post_budget, "function lift")) {
			post_budget_exhausted = true;
			sleigh_artifact_plan_fini (&taint_plan);
			break;
		}
		BlockArray blocks;
		ut64 profile_start_us = r_time_now_mono ();
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			sleigh_artifact_plan_fini (&taint_plan);
			continue;
		}
		sleigh_profile_add (anal, fcn, SLEIGH_PROFILE_STAGE_LIFT,
			r_time_now_mono () - profile_start_us);
		if (!sleigh_post_analysis_budget_allows (&post_budget, "taint summary")) {
			post_budget_exhausted = true;
			block_array_free (&blocks);
			sleigh_artifact_plan_fini (&taint_plan);
			break;
		}
		SleighTaintPlanStats stats;
		bool collected = collect_taint_artifacts_for_function (
			&taint_plan, anal, ctx, &blocks, &stats);
		bool committed = collected && sleigh_artifact_plan_submit (&taint_plan);
		if (!collected) {
			taint_parse_failures++;
			R_LOG_WARN ("r2sleigh: taint collection failed at 0x%08"PFMT64x,
				taint_plan.scope_id);
		}
		if (committed) {
			taint_comments += taint_plan.comment_count;
			taint_flags += taint_plan.flag_count;
			taint_xrefs += taint_plan.xref_count;
			taint_sink_hits += stats.sink_hits;
			switch (stats.risk_level) {
			case TAINT_RISK_CRITICAL:
				taint_risk_critical++;
				break;
			case TAINT_RISK_HIGH:
				taint_risk_high++;
				break;
			case TAINT_RISK_MEDIUM:
				taint_risk_medium++;
				break;
			case TAINT_RISK_LOW:
				taint_risk_low++;
				break;
			case TAINT_RISK_NONE:
			default:
				break;
			}
			if (stats.best_sink_label && stats.best_sink_rank < best_sink_rank) {
				free (best_sink_label);
				best_sink_label = stats.best_sink_label;
				stats.best_sink_label = NULL;
				best_sink_addr = stats.best_sink_addr;
				best_sink_rank = stats.best_sink_rank;
			}
		}
		sleigh_taint_plan_stats_fini (&stats);
		block_array_free (&blocks);
		sleigh_artifact_plan_fini (&taint_plan);
	}

	post_budget_exhausted = post_budget_exhausted || post_budget.exhausted;
	R_LOG_INFO ("r2sleigh: post-analysis taint enabled=%d eligible=%d skipped=%d comments=%zu flags=%zu xrefs=%zu sink_hits=%zu parse_failures=%d",
		taint_enabled? 1: 0, taint_fcns_eligible, taint_fcns_skipped, taint_comments, taint_flags, taint_xrefs,
		taint_sink_hits, taint_parse_failures);
	R_LOG_INFO ("r2sleigh: post-analysis proofs fcns=%d skipped=%d refused=%d call_targets=%zu unreachable_blocks=%zu",
		proof_fcns, proof_skipped, proof_refused, proof_xrefs, proof_dead_blocks);
	R_LOG_INFO ("r2sleigh: post-analysis risk summary: critical=%d high=%d medium=%d low=%d",
		taint_risk_critical, taint_risk_high, taint_risk_medium, taint_risk_low);
	R_LOG_INFO ("r2sleigh: post-analysis summary fcns=%d budget_exhausted=%d",
		num_fcns, post_budget_exhausted? 1: 0);
	if (best_sink_label) {
		R_LOG_INFO ("r2sleigh: post-analysis most interesting sink 0x%"PFMT64x" label=%s",
			best_sink_addr, best_sink_label);
		free (best_sink_label);
	}
	return true;
}

RAnalPlugin r_anal_plugin_sleigh = {
	.meta = {
		.name = "sla",
		.desc = "Sleigh-based analysis via r2sleigh (P-code to ESIL)",
		.license = "LGPL3",
		.author = "r2sleigh project",
	},
	.init = sleigh_init,
	.fini = sleigh_fini,
	.eligible = sleigh_eligible,
	.op = sleigh_op,
	.cmd = sleigh_cmd,
	/* Deep integration callbacks */
	.pre_analysis = sleigh_pre_analysis,
	.analyze_fcn = sleigh_analyze_fcn,
	.get_data_refs = sleigh_get_data_refs,
	.post_analysis = sleigh_post_analysis,
	.decompile = sleigh_decompile,
};

#ifndef R2_PLUGIN_INCORE
R_API RLibStruct radare_plugin = {
	.type = R_LIB_TYPE_ANAL,
	.data = &r_anal_plugin_sleigh,
	.version = R2_VERSION,
	.abiversion = R2_ABIVERSION
};
#endif
