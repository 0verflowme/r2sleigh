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
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include "r2sleigh_api_v2.h"

#if R2_ABIVERSION != 138
#error "r2sleigh borrowed snapshot transport requires exactly radare2 ABI 138"
#endif
#if R2SLEIGH_RADARE_ABI_V2 != 138
#error "r2sleigh generated V2 header must target exactly radare2 ABI 138"
#endif
#if R_ANAL_FUNCTION_SNAPSHOT_SCHEMA_VERSION != 7
#error "r2sleigh borrowed snapshot transport requires function snapshot schema 7"
#endif

static bool sleigh_radare_storage_view(R2SleighRadareRegisterStorageViewV2 *destination, const RAnalSnapshotRegisterStorageView *source) {
	if (!destination || !source) {
		return false;
	}
	*destination = (R2SleighRadareRegisterStorageViewV2) {
		.name_length = source->name_length,
		.offset = source->offset,
		.size = source->size,
	};
	return true;
}

static bool sleigh_radare_carrier(R2SleighRadareCarrierProjectionV2 *destination, const RAnalSnapshotCarrierProjection *source) {
	if (!destination || !source) {
		return false;
	}
	switch (source->kind) {
	case R_ANAL_SNAPSHOT_CARRIER_INVALID:
		destination->kind = 0;
		break;
	case R_ANAL_SNAPSHOT_CARRIER_FULL:
		destination->kind = 1;
		break;
	case R_ANAL_SNAPSHOT_CARRIER_LOW_BITS:
		destination->kind = 2;
		break;
	default:
		return false;
	}
	destination->offset_bits = source->offset_bits;
	destination->size_bits = source->size_bits;
	return true;
}

static bool sleigh_radare_return_kind(int32_t *destination, RAnalSnapshotReturnKind source) {
	if (!destination) {
		return false;
	}
	switch (source) {
	case R_ANAL_SNAPSHOT_RETURN_UNKNOWN:
		*destination = 0;
		return true;
	case R_ANAL_SNAPSHOT_RETURN_VOID:
		*destination = 1;
		return true;
	case R_ANAL_SNAPSHOT_RETURN_REGISTER:
		*destination = 2;
		return true;
	default:
		return false;
	}
}

static uint8_t sleigh_radare_snapshot_view(const void *opaque, R2SleighRadareSnapshotViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	const RAnalFunctionSnapshot *snapshot = opaque;
	RAnalFunctionSnapshotView source = {0};
	if (!r_anal_function_snapshot_view (snapshot, &source)) {
		return 0;
	}
	*destination = (R2SleighRadareSnapshotViewV2) {
		.schema_version = source.schema_version,
		.struct_size = sizeof (*destination),
		.capabilities = source.capabilities,
		.function_addr = source.function_addr,
		.function_size = source.function_size,
		.bits = source.bits,
		.endian = source.endian,
		.maxstack = source.maxstack,
		.arch_id_length = source.arch_id_length,
		.cpu_id_length = source.cpu_id_length,
		.function_name_length = source.function_name_length,
		.num_base_types = source.num_base_types,
		.type_context_hash = source.type_context_hash,
		.num_call_site_interfaces = source.num_call_site_interfaces,
		.num_stack_slots = source.num_stack_slots,
		.revision_identity = source.revision_identity,
		.num_types = source.num_types,
		.num_aggregates = source.num_aggregates,
		.num_blocks = source.num_blocks,
		.num_external_exits = source.num_external_exits,
		.total_source_bytes = source.total_source_bytes,
	};
	return 1;
}

static uint8_t sleigh_radare_arch_id(const void *opaque, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_arch_id (opaque, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_cpu_id(const void *opaque, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_cpu_id (opaque, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_function_name(const void *opaque, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_function_name (opaque, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_interface_view(const void *opaque, R2SleighRadareFunctionInterfaceViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalFunctionInterfaceSnapshotView source = {0};
	if (!r_anal_function_snapshot_interface_view (opaque, &source)) {
		return 0;
	}
	R2SleighRadareFunctionInterfaceViewV2 result = {
		.calling_convention_length = source.calling_convention_length,
		.num_parameters = source.num_parameters,
		.variadic = source.variadic? 1: 0,
		.noreturn = source.noreturn? 1: 0,
		.stack_resources_complete = source.stack_resources_complete? 1: 0,
		.stack_slot_roles_complete = source.stack_slot_roles_complete? 1: 0,
		.complete = source.complete? 1: 0,
		.return_type_id = source.return_type_id,
		.logical_types_complete = source.logical_types_complete? 1: 0,
	};
	if (!sleigh_radare_return_kind (&result.return_kind, source.return_kind)
		|| !sleigh_radare_storage_view (&result.return_storage, &source.return_storage)
		|| !sleigh_radare_storage_view (&result.return_address_storage, &source.return_address_storage)
		|| !sleigh_radare_storage_view (&result.stack_pointer_storage, &source.stack_pointer_storage)
		|| !sleigh_radare_carrier (&result.return_carrier, &source.return_carrier)) {
		return 0;
	}
	*destination = result;
	return 1;
}

static uint8_t sleigh_radare_interface_calling_convention(const void *opaque, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_interface_calling_convention (opaque, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_interface_storage_name(const void *opaque, int32_t kind, uint8_t *buffer, size_t buffer_size) {
	if (!opaque || !buffer) {
		return 0;
	}
	RAnalSnapshotInterfaceStorageKind source_kind;
	switch (kind) {
	case 0:
		source_kind = R_ANAL_SNAPSHOT_INTERFACE_STORAGE_RETURN;
		break;
	case 1:
		source_kind = R_ANAL_SNAPSHOT_INTERFACE_STORAGE_RETURN_ADDRESS;
		break;
	case 2:
		source_kind = R_ANAL_SNAPSHOT_INTERFACE_STORAGE_STACK_POINTER;
		break;
	default:
		return 0;
	}
	return r_anal_function_snapshot_interface_storage_name (
		opaque, source_kind, (char *)buffer, buffer_size)? 1: 0;
}

static bool sleigh_radare_parameter_copy(R2SleighRadareParameterViewV2 *destination, const RAnalSnapshotParameterView *source) {
	if (!destination || !source) {
		return false;
	}
	R2SleighRadareParameterViewV2 result = {
		.index = source->index,
		.logical_type_id = source->logical_type_id,
	};
	if (!sleigh_radare_storage_view (&result.storage, &source->storage)
		|| !sleigh_radare_carrier (&result.carrier, &source->carrier)) {
		return false;
	}
	*destination = result;
	return true;
}

static uint8_t sleigh_radare_parameter_view(const void *opaque, size_t index, R2SleighRadareParameterViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotParameterView source = {0};
	return r_anal_function_snapshot_parameter_view (opaque, index, &source)
		&& sleigh_radare_parameter_copy (destination, &source)? 1: 0;
}

static uint8_t sleigh_radare_parameter_storage_name(const void *opaque, size_t index, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_parameter_storage_name (
			opaque, index, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_stack_slot_view(const void *opaque, size_t index, R2SleighRadareStackSlotViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotStackSlotView source = {0};
	if (!r_anal_function_snapshot_stack_slot_view (opaque, index, &source)) {
		return 0;
	}
	int32_t base;
	switch (source.base) {
	case R_ANAL_FCN_BASE_BP:
		base = 0;
		break;
	case R_ANAL_FCN_BASE_SP:
		base = 1;
		break;
	case R_ANAL_FCN_BASE_NAMED:
		base = 2;
		break;
	default:
		return 0;
	}
	int32_t role;
	switch (source.role) {
	case R_ANAL_FCN_SLOT_LOCAL:
		role = 0;
		break;
	case R_ANAL_FCN_SLOT_ARG:
		role = 1;
		break;
	case R_ANAL_FCN_SLOT_HOME:
		role = 2;
		break;
	case R_ANAL_FCN_SLOT_UNKNOWN:
		role = 3;
		break;
	default:
		return 0;
	}
	*destination = (R2SleighRadareStackSlotViewV2) {
		.name_length = source.name_length,
		.type_length = source.type_length,
		.base = base,
		.base_name_length = source.base_name_length,
		.base_offset = source.base_offset,
		.base_size = source.base_size,
		.offset = source.offset,
		.size = source.size,
		.offset_valid = source.offset_valid? 1: 0,
		.role = role,
		.arg_index = source.arg_index,
		.arg_name_length = source.arg_name_length,
		.home_reg_length = source.home_reg_length,
		.home_reg_offset = source.home_reg_offset,
		.home_reg_size = source.home_reg_size,
	};
	return 1;
}

static uint8_t sleigh_radare_stack_slot_string(const void *opaque, size_t index, int32_t kind, uint8_t *buffer, size_t buffer_size) {
	if (!opaque || !buffer) {
		return 0;
	}
	RAnalSnapshotStackSlotStringKind source_kind;
	switch (kind) {
	case 0:
		source_kind = R_ANAL_SNAPSHOT_STACK_SLOT_STRING_NAME;
		break;
	case 1:
		source_kind = R_ANAL_SNAPSHOT_STACK_SLOT_STRING_TYPE;
		break;
	case 2:
		source_kind = R_ANAL_SNAPSHOT_STACK_SLOT_STRING_BASE_NAME;
		break;
	case 3:
		source_kind = R_ANAL_SNAPSHOT_STACK_SLOT_STRING_ARG_NAME;
		break;
	case 4:
		source_kind = R_ANAL_SNAPSHOT_STACK_SLOT_STRING_HOME_REGISTER;
		break;
	default:
		return 0;
	}
	return r_anal_function_snapshot_stack_slot_string (
		opaque, index, source_kind, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_call_site_view(const void *opaque, size_t index, R2SleighRadareCallSiteViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalCallSiteInterfaceSnapshotView source = {0};
	if (!r_anal_function_snapshot_call_site_view (opaque, index, &source)) {
		return 0;
	}
	R2SleighRadareCallSiteViewV2 result = {
		.instruction_addr = source.instruction_addr,
		.target_addr = source.target_addr,
		.calling_convention_length = source.calling_convention_length,
		.num_arguments = source.num_arguments,
		.variadic = source.variadic? 1: 0,
		.noreturn = source.noreturn? 1: 0,
		.complete = source.complete? 1: 0,
	};
	if (!sleigh_radare_return_kind (&result.result_kind, source.result_kind)
		|| !sleigh_radare_storage_view (&result.result_storage, &source.result_storage)) {
		return 0;
	}
	*destination = result;
	return 1;
}

static uint8_t sleigh_radare_call_site_calling_convention(const void *opaque, size_t index, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_call_site_calling_convention (
			opaque, index, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_call_site_result_storage_name(const void *opaque, size_t index, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_call_site_result_storage_name (
			opaque, index, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_call_argument_view(const void *opaque, size_t call_index, size_t argument_index, R2SleighRadareParameterViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotParameterView source = {0};
	return r_anal_function_snapshot_call_argument_view (
			opaque, call_index, argument_index, &source)
		&& sleigh_radare_parameter_copy (destination, &source)? 1: 0;
}

static uint8_t sleigh_radare_call_argument_storage_name(const void *opaque, size_t call_index, size_t argument_index, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_call_argument_storage_name (
			opaque, call_index, argument_index, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_type_graph_view(const void *opaque, R2SleighRadareTypeGraphViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotTypeGraphView source = {0};
	if (!r_anal_function_snapshot_type_graph_view (opaque, &source)) {
		return 0;
	}
	*destination = (R2SleighRadareTypeGraphViewV2) {
		.num_types = source.num_types,
		.num_aggregates = source.num_aggregates,
		.complete = source.complete? 1: 0,
	};
	return 1;
}

static uint8_t sleigh_radare_type_view(const void *opaque, size_t index, R2SleighRadareTypeViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotType source = {0};
	if (!r_anal_function_snapshot_type_view (opaque, index, &source)) {
		return 0;
	}
	int32_t kind;
	switch (source.kind) {
	case R_ANAL_SNAPSHOT_TYPE_INVALID:
		kind = 0;
		break;
	case R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER:
		kind = 1;
		break;
	case R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER:
		kind = 2;
		break;
	case R_ANAL_SNAPSHOT_TYPE_POINTER:
		kind = 3;
		break;
	case R_ANAL_SNAPSHOT_TYPE_STRUCT:
		kind = 4;
		break;
	default:
		return 0;
	}
	*destination = (R2SleighRadareTypeViewV2) {
		.id = source.id,
		.kind = kind,
		.size_bits = source.size_bits,
		.align_bits = source.align_bits,
		.target_type_id = source.target_type_id,
		.aggregate_id = source.aggregate_id,
	};
	return 1;
}

static uint8_t sleigh_radare_aggregate_view(const void *opaque, size_t index, R2SleighRadareAggregateViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotAggregateLayoutView source = {0};
	if (!r_anal_function_snapshot_aggregate_view (opaque, index, &source)) {
		return 0;
	}
	*destination = (R2SleighRadareAggregateViewV2) {
		.id = source.id,
		.type_id = source.type_id,
		.size_bits = source.size_bits,
		.align_bits = source.align_bits,
		.name_length = source.name_length,
		.num_members = source.num_members,
		.complete = source.complete? 1: 0,
		.c_layout_compatible = source.c_layout_compatible? 1: 0,
	};
	return 1;
}

static uint8_t sleigh_radare_aggregate_name(const void *opaque, size_t index, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_aggregate_name (opaque, index, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_aggregate_member_view(const void *opaque, size_t aggregate_index, size_t member_index, R2SleighRadareAggregateMemberViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotAggregateMemberView source = {0};
	if (!r_anal_function_snapshot_aggregate_member_view (
			opaque, aggregate_index, member_index, &source)) {
		return 0;
	}
	*destination = (R2SleighRadareAggregateMemberViewV2) {
		.member_id = source.member_id,
		.type_id = source.type_id,
		.offset_bits = source.offset_bits,
		.size_bits = source.size_bits,
		.count = source.count,
		.name_length = source.name_length,
	};
	return 1;
}

static uint8_t sleigh_radare_aggregate_member_name(const void *opaque, size_t aggregate_index, size_t member_index, uint8_t *buffer, size_t buffer_size) {
	return opaque && buffer
		&& r_anal_function_snapshot_aggregate_member_name (
			opaque, aggregate_index, member_index, (char *)buffer, buffer_size)? 1: 0;
}

static uint8_t sleigh_radare_block_view(const void *opaque, size_t index, R2SleighRadareBlockViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotBlockView source = {0};
	if (!r_anal_function_snapshot_block_view (opaque, index, &source)) {
		return 0;
	}
	*destination = (R2SleighRadareBlockViewV2) {
		.addr = source.addr,
		.size = source.size,
		.num_successors = source.num_successors,
		.switch_addr = source.switch_addr,
	};
	return 1;
}

static uint8_t sleigh_radare_block_bytes(const void *opaque, size_t index, size_t offset, uint8_t *buffer, size_t length) {
	return opaque && buffer
		&& r_anal_function_snapshot_block_bytes (opaque, index, offset, buffer, length)? 1: 0;
}

static uint8_t sleigh_radare_successor_view(const void *opaque, size_t block_index, size_t successor_index, R2SleighRadareSuccessorViewV2 *destination) {
	if (!opaque || !destination) {
		return 0;
	}
	RAnalSnapshotSuccessorView source = {0};
	if (!r_anal_function_snapshot_successor_view (
			opaque, block_index, successor_index, &source)) {
		return 0;
	}
	int32_t kind;
	switch (source.kind) {
	case R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT:
		kind = 0;
		break;
	case R_ANAL_SNAPSHOT_SUCCESSOR_FALLTHROUGH:
		kind = 1;
		break;
	case R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_CASE:
		kind = 2;
		break;
	case R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_DEFAULT:
		kind = 3;
		break;
	default:
		return 0;
	}
	*destination = (R2SleighRadareSuccessorViewV2) {
		.kind = kind,
		.target_addr = source.target_addr,
		.case_value = source.case_value,
		.external = source.external? 1: 0,
	};
	return 1;
}

static uint8_t sleigh_radare_external_exit(const void *opaque, size_t index, uint64_t *target) {
	return opaque && target
		&& r_anal_function_snapshot_external_exit (opaque, index, target)? 1: 0;
}

static const R2SleighRadareAccessorsV2 sleigh_radare_accessors = {
	.struct_size = sizeof (sleigh_radare_accessors),
	.abi_version = R2SLEIGH_RADARE_ABI_V2,
	.snapshot_schema_version = R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2,
	.accessor_schema_version = R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2,
	.snapshot_view = sleigh_radare_snapshot_view,
	.arch_id = sleigh_radare_arch_id,
	.cpu_id = sleigh_radare_cpu_id,
	.function_name = sleigh_radare_function_name,
	.interface_view = sleigh_radare_interface_view,
	.interface_calling_convention = sleigh_radare_interface_calling_convention,
	.interface_storage_name = sleigh_radare_interface_storage_name,
	.parameter_view = sleigh_radare_parameter_view,
	.parameter_storage_name = sleigh_radare_parameter_storage_name,
	.stack_slot_view = sleigh_radare_stack_slot_view,
	.stack_slot_string = sleigh_radare_stack_slot_string,
	.call_site_view = sleigh_radare_call_site_view,
	.call_site_calling_convention = sleigh_radare_call_site_calling_convention,
	.call_site_result_storage_name = sleigh_radare_call_site_result_storage_name,
	.call_argument_view = sleigh_radare_call_argument_view,
	.call_argument_storage_name = sleigh_radare_call_argument_storage_name,
	.type_graph_view = sleigh_radare_type_graph_view,
	.type_view = sleigh_radare_type_view,
	.aggregate_view = sleigh_radare_aggregate_view,
	.aggregate_name = sleigh_radare_aggregate_name,
	.aggregate_member_view = sleigh_radare_aggregate_member_view,
	.aggregate_member_name = sleigh_radare_aggregate_member_name,
	.block_view = sleigh_radare_block_view,
	.block_bytes = sleigh_radare_block_bytes,
	.successor_view = sleigh_radare_successor_view,
	.external_exit = sleigh_radare_external_exit,
};

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

/* Symbolic execution */
struct R2ILFunctionBlocks {
	unsigned long long entry_addr;
	const char *name;
	const R2ILBlock **blocks;
	size_t num_blocks;
	unsigned int provenance;
};

#define R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_ANALYZED 0U
#define R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_RUNTIME_MATERIALIZED 1U
typedef struct {
	const char *name;
	unsigned long long value;
} R2SymReplayRegister;
typedef struct {
	unsigned long long addr;
	const unsigned char *bytes;
	size_t size;
	const char *label;
} R2SymReplayMemoryWindow;
typedef struct {
	const char *name;
	const char *symbol;
} R2SymReplayRegisterOverlay;
typedef struct {
	unsigned long long addr;
	unsigned int size;
	const char *name;
} R2SymReplayMemoryOverlay;
typedef struct {
	unsigned long long checkpoint_id;
	unsigned long long entry_addr;
	const R2SymReplayRegister *registers;
	size_t num_registers;
	const R2SymReplayMemoryWindow *memory;
	size_t num_memory;
	const R2SymReplayRegisterOverlay *register_overlays;
	size_t num_register_overlays;
	const R2SymReplayMemoryOverlay *memory_overlays;
	size_t num_memory_overlays;
	const int *tty_fds;
	size_t num_tty_fds;
	int skip_sleep_calls;
} R2SymReplaySeed;

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
typedef enum {
	R2SLEIGH_INTERPROC_LINKAGE_UNKNOWN = 0,
	R2SLEIGH_INTERPROC_LINKAGE_INTERNAL = 1,
	R2SLEIGH_INTERPROC_LINKAGE_IMPORTED = 2,
} R2SleighInterprocLinkage;
typedef struct {
	const char *name;
	const char *type_name;
	const char *reg;
	long long delta;
	char kind;
	int is_arg;
} R2SleighRecoveredVar;
typedef struct {
	unsigned long long from;
	unsigned long long to;
	char ref_kind;
} R2SleighDataRef;
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
	const R2SleighApiV2 *api = r2sleigh_api_v2 ();
	if (!api || api->abi_version != R2SLEIGH_ABI_V2
		|| api->struct_size != sizeof (*api)
		|| api->radare_abi_version != R2_ABIVERSION
		|| api->byte_view_size != sizeof (R2SleighByteViewV2)
		|| api->string_view_size != sizeof (R2SleighStringViewV2)
		|| api->switch_case_size != sizeof (R2SleighSwitchCaseV2)
		|| api->direct_call_identity_size != sizeof (R2SleighDirectCallIdentityV2)
		|| api->analysis_render_request_size != sizeof (R2SleighAnalysisRenderRequestV2)
		|| api->scope_render_request_size != sizeof (R2SleighScopeRenderRequestV2)
		|| api->scope_symbol_size != sizeof (R2SleighScopeSymbolV2)
		|| api->analysis_query_request_size != sizeof (R2SleighAnalysisQueryRequestV2)
		|| api->analysis_result_view_size != sizeof (R2SleighAnalysisResultViewV2)
		|| api->planner_query_request_size != sizeof (R2SleighPlannerQueryRequestV2)
		|| api->planner_query_response_size != sizeof (R2SleighPlannerQueryResponseV2)
		|| api->planner_target_input_size != sizeof (R2SleighPlannerTargetInputV2)
		|| api->planner_result_view_size != sizeof (R2SleighPlannerResultViewV2)
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
		|| !api->analysis_render || !api->scope_render
		|| !api->analysis_query || !api->analysis_result_view
		|| !api->analysis_result_free || !api->engine_cache_reset
		|| !api->planner_query || !api->planner_result_view
		|| !api->planner_result_copy || !api->planner_result_free) {
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

static R2SleighInterprocSessionPlan sleigh_v2_query_interproc_session(unsigned int depth, unsigned int purpose, size_t basic_block_count, unsigned int cost) {
	R2SleighPlannerQueryRequestV2 request = {0};
	R2SleighPlannerQueryResponseV2 response = {0};
	request.depth = depth;
	request.purpose = purpose;
	request.basic_block_count = basic_block_count;
	request.cost = cost;
	uint32_t status = sleigh_v2_planner_query (R2SLEIGH_PLANNER_INTERPROC_SESSION_V2, &request, &response);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: interproc session plan query failed (%u)", status);
		return (R2SleighInterprocSessionPlan){0};
	}
	return response.interproc_session;
}

static R2SleighSymbolicScopeFunctionPlanV2 sleigh_v2_query_symbolic_scope(size_t current_scope_count, int root_function, int target_hint_function, R2SleighInterprocSessionPlan interproc) {
	R2SleighPlannerQueryRequestV2 request = {0};
	R2SleighPlannerQueryResponseV2 response = {0};
	request.current_scope_count = current_scope_count;
	request.root_function = root_function? 1: 0;
	request.target_hint_function = target_hint_function? 1: 0;
	request.interproc = interproc;
	uint32_t status = sleigh_v2_planner_query (R2SLEIGH_PLANNER_SYMBOLIC_SCOPE_V2, &request, &response);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: symbolic scope plan query failed (%u)", status);
		return (R2SleighSymbolicScopeFunctionPlanV2){0};
	}
	return response.symbolic_scope;
}

static R2SleighRuntimeMaterializedSourcePlanV2 sleigh_v2_query_runtime_source(size_t current_scope_count, unsigned long long addr, unsigned long long size) {
	R2SleighPlannerQueryRequestV2 request = {0};
	R2SleighPlannerQueryResponseV2 response = {0};
	request.current_scope_count = current_scope_count;
	request.addr = addr;
	request.size = size;
	uint32_t status = sleigh_v2_planner_query (R2SLEIGH_PLANNER_RUNTIME_SOURCE_V2, &request, &response);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: runtime source plan query failed (%u)", status);
		return (R2SleighRuntimeMaterializedSourcePlanV2){0};
	}
	return response.runtime_source;
}

static char *sleigh_lift_byte_view_copy(R2SleighByteViewV2 view) {
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

static uint32_t sleigh_lift_owned_bytes_copy(const R2SleighApiV2 *api, R2SleighOwnedBytesV2 *bytes, char **output) {
	if (!output) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*output = NULL;
	if (!api || !bytes) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	R2SleighByteViewV2 view = {0};
	uint32_t status = api->owned_bytes_view (bytes, &view);
	if (status == R2SLEIGH_STATUS_OK_V2) {
		*output = sleigh_lift_byte_view_copy (view);
		if (!*output) {
			status = R2SLEIGH_STATUS_ENGINE_ERROR_V2;
		}
	}
	uint32_t free_status = api->owned_bytes_free (bytes);
	return status == R2SLEIGH_STATUS_OK_V2? free_status: status;
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
	*name = sleigh_lift_byte_view_copy (view);
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
	*message = sleigh_lift_byte_view_copy (view);
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
	uint32_t status = api->lift_context_reg_profile (context, &bytes);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
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

static uint32_t sleigh_v2_block_addr(const R2ILBlock *block, uint64_t *value) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (value) {
		*value = 0;
	}
	return api && block && value? api->lift_block_addr (block, value)
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
	uint32_t status = api->lift_block_mnemonic (context, view, addr, &mnemonic);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
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
	uint32_t status = api->analysis_render (&request, &bytes);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
	}
	return sleigh_lift_owned_bytes_copy (api, bytes, text);
}

static uint32_t sleigh_v2_scope_render(uint32_t kind, const R2ILContext *context,
	const R2ILFunctionBlocks *functions, size_t num_functions,
	uint64_t entry_addr, uint64_t target_addr, const R2SymReplaySeed *replay_seed,
	const char *argument, const char *external_context,
	const R2SleighScopeSymbolV2 *symbols, size_t num_symbols, bool merge_states,
	char **text) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!text) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	*text = NULL;
	if (!api) {
		return R2SLEIGH_STATUS_ABI_MISMATCH_V2;
	}
	R2SleighScopeRenderRequestV2 request = {
		.kind = kind,
		.context = context,
		.functions = functions,
		.num_functions = num_functions,
		.entry_addr = entry_addr,
		.target_addr = target_addr,
		.replay_seed = replay_seed,
		.argument = {
			.data = (const uint8_t *)argument,
			.len = argument? strlen (argument): 0,
		},
		.external_context = {
			.data = (const uint8_t *)external_context,
			.len = external_context? strlen (external_context): 0,
		},
		.symbols = symbols,
		.num_symbols = num_symbols,
		.merge_states = merge_states? 1: 0,
	};
	R2SleighOwnedBytesV2 *bytes = NULL;
	uint32_t status = api->scope_render (&request, &bytes);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		return status;
	}
	return sleigh_lift_owned_bytes_copy (api, bytes, text);
}

static uint32_t sleigh_v2_analysis_query(uint32_t kind, const R2ILContext *context,
	const R2ILBlock *const *blocks, size_t num_blocks, uint64_t function_addr,
	const char *function_name, const uint64_t *input_values, size_t num_input_values,
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
		.function_name = {
			.data = (const uint8_t *)function_name,
			.len = function_name? strlen (function_name): 0,
		},
		.input_values = input_values,
		.num_input_values = num_input_values,
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

static uint32_t sleigh_v2_engine_cache_reset(void) {
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	return api? api->engine_cache_reset (): R2SLEIGH_STATUS_ABI_MISMATCH_V2;
}

/* Per-architecture context (lazy init)
 *
 * WARNING: These globals are NOT thread-safe. This plugin assumes
 * single-threaded radare2 usage. If radare2 becomes multi-threaded,
 * this code must be updated with proper synchronization (e.g., mutex).
 */
static R2ILContext *sleigh_ctx = NULL;
static char *sleigh_arch = NULL;
static char *sleigh_arch_override = NULL;
static R_TH_LOCAL R2SleighPlannerResultV2 *sleigh_pending_target_plan = NULL;

static bool sleigh_v2_planner_result_release(R2SleighPlannerResultV2 **result) {
	if (!result || !*result) {
		return true;
	}
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!api) {
		R_LOG_ERROR ("r2sleigh: retaining planner result because the V2 API is unavailable");
		return false;
	}
	R2SleighPlannerResultV2 *owned = *result;
	uint32_t status = api->planner_result_free (owned);
	if (status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: retaining planner result after free failure (%u)", status);
		return false;
	}
	if (sleigh_pending_target_plan == owned) {
		sleigh_pending_target_plan = NULL;
	}
	*result = NULL;
	return true;
}

static bool sleigh_v2_planner_result_retry_pending(void) {
	return sleigh_v2_planner_result_release (&sleigh_pending_target_plan);
}

void r2sleigh_set_arch_override(const char *arch) {
	if (!arch || !*arch || (sleigh_arch_override && !strcmp (sleigh_arch_override, arch))) {
		return;
	}
	free (sleigh_arch_override);
	sleigh_arch_override = strdup (arch);
}

typedef struct {
	bool has_state;
	char *mode;
	ut64 function_addr;
	ut64 entry_addr;
	ut64 target_addr;
	char *result_json;
} SymStateCache;

static SymStateCache sym_state_cache = {0};
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
#define SLEIGH_COMMENT_PREFIX_TAINT "sla.taint:"
#define SLEIGH_COMMENT_PREFIX_TAINT_RISK "sla.taint.risk:"

/* Helper to lift all basic blocks of a function */
typedef struct {
	R2ILBlock **blocks;
	size_t count;
	size_t capacity;
	R2SleighLiftQuality quality;
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

typedef struct {
	R2ILFunctionBlocks *functions;
	BlockArray *owned_blocks;
	char **owned_names;
	size_t count;
	size_t capacity;
	size_t total_blocks;
	size_t total_ops;
} SymFunctionScope;

typedef struct {
	R2SleighScopeSymbolV2 *symbols;
	char **owned_names;
	size_t count;
	size_t total_name_bytes;
} SymScopeSymbolSnapshot;

static uint32_t sleigh_v2_scope_render_for_scope(uint32_t kind, RCore *core, RAnal *anal,
	const R2ILContext *context, const SymFunctionScope *scope, uint64_t entry_addr,
	uint64_t target_addr, const R2SymReplaySeed *replay_seed, const char *argument,
	const char *external_context, char **text);

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

static const char *sleigh_engine_v2_phase_name(uint32_t phase) {
	switch (phase) {
	case R2SLEIGH_PHASE_SNAPSHOT_CONTEXT_V2:
		return "snapshot_context";
	case R2SLEIGH_PHASE_LIFT_NORMALIZE_V2:
		return "lift_normalize";
	case R2SLEIGH_PHASE_SSA_V2:
		return "ssa";
	case R2SLEIGH_PHASE_OBLIGATIONS_V2:
		return "obligations";
	case R2SLEIGH_PHASE_SYMBOLIC_V2:
		return "symbolic";
	case R2SLEIGH_PHASE_TYPES_V2:
		return "types";
	case R2SLEIGH_PHASE_CERTIFICATION_V2:
		return "certification";
	case R2SLEIGH_PHASE_STRUCTURING_V2:
		return "structuring";
	case R2SLEIGH_PHASE_NORMALIZATION_V2:
		return "normalization";
	case R2SLEIGH_PHASE_RENDERING_V2:
		return "rendering";
	case R2SLEIGH_PHASE_FFI_CONVERSION_V2:
		return "ffi_conversion";
	default:
		return "unknown";
	}
}

static const char *sleigh_engine_v2_phase_status_name(uint32_t status) {
	switch (status) {
	case R2SLEIGH_PHASE_STATUS_NOT_EXECUTED_V2:
		return "not_executed";
	case R2SLEIGH_PHASE_STATUS_EXECUTED_V2:
		return "executed";
	case R2SLEIGH_PHASE_STATUS_FOLDED_V2:
		return "folded";
	case R2SLEIGH_PHASE_STATUS_REUSED_V2:
		return "reused";
	case R2SLEIGH_PHASE_STATUS_REFUSED_V2:
		return "refused";
	default:
		return "unknown";
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

static char *sleigh_engine_v2_session_error_copy(const R2SleighApiV2 *api, const R2SleighSessionV2 *session, uint32_t status) {
	R2SleighByteViewV2 error = {0};
	if (api && session && api->session_error
		&& api->session_error (session, &error) == R2SLEIGH_STATUS_OK_V2
		&& error.data && error.len) {
		return sleigh_byte_view_v2_copy (error);
	}
	return r_str_newf ("V2 engine request failed (%u)", status);
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
#define SLEIGH_SEMANTIC_KERNEL_WARNING_LIMIT 7
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

static char *sleigh_engine_v2_response_json(const R2SleighResponseInfoV2 *info, R2SleighByteViewV2 bytes) {
	if (!info || !info->diagnostics_json.data || !info->diagnostics_json.len) {
		return NULL;
	}
	if (!sleigh_json_is_single_object (
		(const char *)info->diagnostics_json.data, info->diagnostics_json.len)) {
		return NULL;
	}
	char *output = sleigh_byte_view_v2_copy (bytes);
	char *diagnostics_text = sleigh_byte_view_v2_copy (info->diagnostics_json);
	if (!output || !diagnostics_text) {
		free (output);
		free (diagnostics_text);
		return NULL;
	}
	RJson *diagnostics = r_json_parsedup (diagnostics_text);
	free (diagnostics_text);
	if (!diagnostics || diagnostics->type != R_JSON_OBJECT) {
		r_json_free (diagnostics);
		free (output);
		return NULL;
	}
	PJ *pj = pj_new ();
	if (!pj) {
		r_json_free (diagnostics);
		free (output);
		return NULL;
	}
	pj_o (pj);
	pj_kn (pj, "schema_version", SLEIGH_DECJ_SCHEMA_VERSION);
	pj_ks (pj, "request_kind", "decompile");
	pj_kn (pj, "request_kind_code", info->request_kind);
	pj_ks (pj, "outcome", info->outcome == R2SLEIGH_OUTCOME_REFUSED_V2
		? "refused": "completed");
	pj_kn (pj, "outcome_code", info->outcome);
	pj_ks (pj, "rendered_output", output);
	pj_k (pj, "diagnostics");
	pj_rj (pj, diagnostics);
	pj_ka (pj, "phase_timings");
	size_t i = 0;
	for (; i < info->num_phase_timings; i++) {
		const R2SleighPhaseTimingV2 *timing = &info->phase_timings[i];
		pj_o (pj);
		pj_kn (pj, "phase", timing->phase);
		pj_ks (pj, "name", sleigh_engine_v2_phase_name (timing->phase));
		pj_kn (pj, "status", timing->status);
		pj_ks (pj, "status_name", sleigh_engine_v2_phase_status_name (timing->status));
		pj_kn (pj, "elapsed_us", timing->elapsed_us);
		pj_end (pj);
	}
	pj_end (pj);
	pj_kn (pj, "ffi_conversion_elapsed_us", info->ffi_conversion_elapsed_us);
	pj_kb (pj, "refused", info->outcome == R2SLEIGH_OUTCOME_REFUSED_V2);
	pj_knull (pj, "error");
	pj_end (pj);
	char *json = pj_drain (pj);
	r_json_free (diagnostics);
	free (output);
	return json;
}

// Returns a malloc-owned NUL-terminated projection. Every borrowed response
// view is consumed before response_free releases the opaque Rust owner.
static char *sleigh_engine_execute_v2_project(uint32_t kind, uint64_t required_capability, const R2SleighEngineRequestPayloadV2 *payload, bool json_projection) {
	required_capability |= R2SLEIGH_CAP_NATIVE_REQUEST_GRAPH_V2
		| R2SLEIGH_CAP_RESPONSE_INFO_V2
		| R2SLEIGH_CAP_EXECUTION_CONTROL_V2;
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	if (!api || api->abi_version != R2SLEIGH_ABI_V2
		|| api->struct_size != sizeof (*api)
		|| api->radare_abi_version != R2_ABIVERSION
		|| api->session_config_size != sizeof (R2SleighSessionConfigV2)
		|| api->request_size != sizeof (R2SleighRequestV2)
		|| api->engine_request_payload_size != sizeof (R2SleighEngineRequestPayloadV2)
		|| api->function_context_size != sizeof (R2SleighFunctionContext)
		|| api->context_param_size != sizeof (R2SleighContextParam)
		|| api->context_var_size != sizeof (R2SleighContextVar)
		|| api->context_base_member_size != sizeof (R2SleighContextBaseMember)
		|| api->context_enum_variant_size != sizeof (R2SleighContextEnumVariant)
		|| api->context_base_type_size != sizeof (R2SleighContextBaseType)
		|| api->context_callee_size != sizeof (R2SleighContextCallee)
		|| api->lift_quality_size != sizeof (R2SleighLiftQuality)
		|| api->interproc_seed_size != sizeof (R2SleighInterprocSeed)
		|| api->interproc_scope_size != sizeof (R2SleighInterprocScope)
		|| api->interproc_plan_size != sizeof (R2SleighInterprocSessionPlan)
		|| api->source_function_interface_size != sizeof (R2SleighSourceFunctionInterfaceV2)
		|| api->source_parameter_size != sizeof (R2SleighSourceParameterV2)
		|| api->source_parameter_type_size != sizeof (R2SleighSourceParameterTypeV2)
		|| api->source_carrier_projection_size != sizeof (R2SleighSourceCarrierProjectionV2)
		|| api->source_type_size != sizeof (R2SleighSourceTypeV2)
		|| api->source_aggregate_member_size != sizeof (R2SleighSourceAggregateMemberV2)
		|| api->source_aggregate_layout_size != sizeof (R2SleighSourceAggregateLayoutV2)
		|| api->source_register_size != sizeof (R2SleighSourceRegisterV2)
		|| api->source_stack_slot_size != sizeof (R2SleighSourceStackSlotV2)
		|| api->source_storage_size != sizeof (R2SleighSourceStorageV2)
		|| api->source_call_argument_size != sizeof (R2SleighSourceCallArgumentV2)
		|| api->source_call_site_interface_size != sizeof (R2SleighSourceCallSiteInterfaceV2)
		|| api->byte_view_size != sizeof (R2SleighByteViewV2)
		|| api->phase_timing_size != sizeof (R2SleighPhaseTimingV2)
		|| api->response_info_size != sizeof (R2SleighResponseInfoV2)
		|| (api->capabilities & required_capability) != required_capability
		|| !api->session_create || !api->session_free
		|| !api->session_cancel || !api->session_reset_cancellation || !api->execute
		|| !api->response_bytes || !api->response_info
		|| !api->response_free || !api->session_error) {
		R_LOG_ERROR ("r2sleigh: incompatible V2 engine API table");
		return json_projection
			? sleigh_engine_v2_error_json ("incompatible_api",
				R2SLEIGH_STATUS_ABI_MISMATCH_V2,
				"incompatible V2 engine API table")
			: NULL;
	}
	if (!payload || payload->abi_version != R2SLEIGH_ABI_V2
		|| payload->struct_size != sizeof (*payload)) {
		R_LOG_ERROR ("r2sleigh: invalid native V2 request graph");
		return json_projection
			? sleigh_engine_v2_error_json ("invalid_request",
				R2SLEIGH_STATUS_INVALID_ARGUMENT_V2,
				"invalid native V2 request graph")
			: NULL;
	}

	R2SleighSessionConfigV2 config = {
		.abi_version = R2SLEIGH_ABI_V2,
		.struct_size = sizeof (config),
		.required_capabilities = required_capability,
	};
	R2SleighSessionV2 *session = NULL;
	uint32_t status = api->session_create (&config, &session);
	if (status != R2SLEIGH_STATUS_OK_V2 || !session) {
		R_LOG_ERROR ("r2sleigh: failed to create V2 engine session (%u)", status);
		return json_projection
			? sleigh_engine_v2_error_json ("session_create", status,
				"failed to create V2 engine session")
			: NULL;
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
		char *message = json_projection
			? sleigh_engine_v2_session_error_copy (api, session, status)
			: NULL;
		api->session_free (session);
		if (json_projection) {
			char *json = sleigh_engine_v2_error_json ("execute", status, message);
			free (message);
			return json;
		}
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
		api->response_free (response);
		api->session_free (session);
		return json_projection
			? sleigh_engine_v2_error_json ("response_info",
				R2SLEIGH_STATUS_ENGINE_ERROR_V2,
				"invalid or missing V2 response metadata")
			: NULL;
	}
	size_t phase_index;
	for (phase_index = 0; phase_index < info.num_phase_timings; phase_index++) {
		if (info.phase_timings[phase_index].phase != phase_index
			|| info.phase_timings[phase_index].status > R2SLEIGH_PHASE_STATUS_REFUSED_V2) {
			R_LOG_ERROR ("r2sleigh: invalid V2 engine phase metadata");
			api->response_free (response);
			api->session_free (session);
			return json_projection
				? sleigh_engine_v2_error_json ("phase_metadata",
					R2SLEIGH_STATUS_ENGINE_ERROR_V2,
					"invalid V2 engine phase metadata")
				: NULL;
		}
	}
	if (info.phase_timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2].status
			!= R2SLEIGH_PHASE_STATUS_EXECUTED_V2
		|| info.phase_timings[R2SLEIGH_PHASE_FFI_CONVERSION_V2].elapsed_us
			!= info.ffi_conversion_elapsed_us) {
		R_LOG_ERROR ("r2sleigh: invalid V2 FFI conversion metadata");
		api->response_free (response);
		api->session_free (session);
		return json_projection
			? sleigh_engine_v2_error_json ("ffi_conversion_metadata",
				R2SLEIGH_STATUS_ENGINE_ERROR_V2,
				"invalid V2 FFI conversion metadata")
			: NULL;
	}

	R2SleighByteViewV2 bytes = {0};
	status = api->response_bytes (response, &bytes);
	char *result = NULL;
	if (status == R2SLEIGH_STATUS_OK_V2 && bytes.len < SIZE_MAX
		&& (!bytes.len || bytes.data)) {
		result = json_projection
			? sleigh_engine_v2_response_json (&info, bytes)
			: sleigh_byte_view_v2_copy (bytes);
	} else {
		sleigh_engine_v2_log_error (api, session, status);
	}
	if (json_projection && !result) {
		result = sleigh_engine_v2_error_json ("response_projection",
			R2SLEIGH_STATUS_ENGINE_ERROR_V2,
			"invalid output or diagnostics in V2 response");
	}
	if (!json_projection) {
		sleigh_engine_v2_log_semantic_kernel_warnings (info.diagnostics_json);
	}
	api->response_free (response);
	api->session_free (session);
	return result;
}

static char *sleigh_engine_execute_v2(uint32_t kind, uint64_t required_capability, const R2SleighEngineRequestPayloadV2 *payload) {
	return sleigh_engine_execute_v2_project (
		kind, required_capability, payload, false);
}

typedef struct {
	ut64 addr;
	ut64 size;
} RuntimeMaterializedSource;

static ut64 *collect_type_interproc_direct_targets_from_blocks(
	R2ILContext *ctx,
	const BlockArray *blocks,
	ut64 fcn_addr,
	const char *fcn_name,
	size_t *out_count
);
static ut64 *collect_runtime_scope_targets_from_blocks(
	R2ILContext *ctx,
	const BlockArray *blocks,
	ut64 fcn_addr,
	const char *fcn_name,
	const ut64 *registration_targets,
	size_t registration_target_count,
	size_t *out_count
);
static RuntimeMaterializedSource *collect_runtime_materialized_sources_from_blocks(
	R2ILContext *ctx,
	const BlockArray *blocks,
	ut64 fcn_addr,
	const char *fcn_name,
	const ut64 *copy_targets,
	size_t copy_target_count,
	size_t *out_count
);
static void sym_function_scope_init(SymFunctionScope *scope);
static void sym_function_scope_free(SymFunctionScope *scope);
static bool sym_function_scope_ensure_capacity(SymFunctionScope *scope, size_t needed);
static bool sym_function_scope_append(
	SymFunctionScope *scope,
	RAnal *anal,
	RAnalFunction *fcn,
	R2ILContext *ctx
);
static bool sym_function_scope_append_runtime_source(
	SymFunctionScope *scope,
	RAnal *anal,
	R2ILContext *ctx,
	ut64 addr,
	ut64 size
);
static bool build_symbolic_function_scope(
	RAnal *anal,
	RAnalFunction *root_fcn,
	R2ILContext *ctx,
	SymFunctionScope *scope
);
static bool build_symbolic_function_scope_with_target(
	RAnal *anal,
	RAnalFunction *root_fcn,
	R2ILContext *ctx,
	SymFunctionScope *scope,
	ut64 target_hint
);
static char *resolve_interproc_seed_name(RCore *core, RAnal *anal, ut64 addr);
static unsigned int resolve_interproc_seed_linkage(RCore *core, RAnal *anal, ut64 addr);
static ut64 *collect_type_interproc_direct_targets_from_blocks(
	R2ILContext *ctx,
	const BlockArray *blocks,
	ut64 fcn_addr,
	const char *fcn_name,
	size_t *out_count
);

static void block_array_init(BlockArray *arr) {
	arr->blocks = NULL;
	arr->count = 0;
	arr->capacity = 0;
	memset (&arr->quality, 0, sizeof (arr->quality));
}

static bool sleigh_debug_scope_enabled(void) {
	return r_sys_getenv_asbool ("R2SLEIGH_DEBUG_SCOPE");
}

static void sleigh_debug_scope_log(const char *fmt, ...) {
	char *path = NULL;
	FILE *fd = NULL;
	va_list ap;

	if (!sleigh_debug_scope_enabled ()) {
		return;
	}
	path = r_sys_getenv ("R2SLEIGH_DEBUG_SCOPE_LOG");
	if (!path || !*path) {
		free (path);
		path = strdup ("/tmp/r2sleigh_scope.log");
	}
	if (!path) {
		return;
	}
	fd = fopen (path, "a");
	free (path);
	if (!fd) {
		return;
	}
	va_start (ap, fmt);
	vfprintf (fd, fmt, ap);
	va_end (ap);
	fputc ('\n', fd);
	fclose (fd);
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

static int block_array_compare_addr(const void *a, const void *b) {
	const R2ILBlock *const *block_a = (const R2ILBlock *const *)a;
	const R2ILBlock *const *block_b = (const R2ILBlock *const *)b;
	ut64 addr_a = 0;
	ut64 addr_b = 0;
	if (block_a && *block_a) {
		(void)sleigh_v2_block_addr (*block_a, &addr_a);
	}
	if (block_b && *block_b) {
		(void)sleigh_v2_block_addr (*block_b, &addr_b);
	}
	if (addr_a < addr_b) {
		return -1;
	}
	if (addr_a > addr_b) {
		return 1;
	}
	return 0;
}

static void block_array_sort(BlockArray *arr) {
	if (!arr || arr->count < 2 || !arr->blocks) {
		return;
	}
	qsort (arr->blocks, arr->count, sizeof (R2ILBlock *), block_array_compare_addr);
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
	memset (&arr->quality, 0, sizeof (arr->quality));
	return true;
}


static char *sleigh_collect_sym_assumptions_json(RAnal *anal, RAnalFunction *fcn) {
	if (!anal || !fcn) {
		return strdup ("[]");
	}
	char *assumptions_json = r_anal_function_get_assumptions_json (anal, fcn);
	if (R_STR_ISEMPTY (assumptions_json) || !strcmp (assumptions_json, "[]")) {
		free (assumptions_json);
		return strdup ("[]");
	}
	return assumptions_json;
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

static void sym_state_cache_clear(void) {
	free (sym_state_cache.mode);
	free (sym_state_cache.result_json);
	sym_state_cache.mode = NULL;
	sym_state_cache.result_json = NULL;
	sym_state_cache.function_addr = 0;
	sym_state_cache.entry_addr = 0;
	sym_state_cache.target_addr = 0;
	sym_state_cache.has_state = false;
}

static void sym_state_cache_update(const char *mode, ut64 function_addr, ut64 entry_addr, ut64 target_addr, const char *result_json) {
	if (!mode || !result_json || !*result_json) {
		return;
	}
	sym_state_cache_clear ();
	sym_state_cache.mode = strdup (mode);
	sym_state_cache.result_json = strdup (result_json);
	if (!sym_state_cache.mode || !sym_state_cache.result_json) {
		sym_state_cache_clear ();
		return;
	}
	sym_state_cache.function_addr = function_addr;
	sym_state_cache.entry_addr = entry_addr;
	sym_state_cache.target_addr = target_addr;
	sym_state_cache.has_state = true;
}

static bool sym_result_has_error(const char *json) {
	char *json_copy;
	RJson *root;
	const RJson *error_field;
	bool has_error;

	if (!json || !*json) {
		return true;
	}
	json_copy = strdup (json);
	if (!json_copy) {
		return true;
	}
	root = r_json_parse (json_copy);
	free (json_copy);
	if (!root) {
		return true;
	}
	has_error = false;
	if (root->type == R_JSON_OBJECT) {
		error_field = r_json_get (root, "error");
		if (error_field && error_field->type == R_JSON_STRING && error_field->str_value && *error_field->str_value) {
			has_error = true;
		}
	}
	r_json_free (root);
	return has_error;
}

static char *sym_state_cache_to_json(void) {
	int needed;
	char *json;

	if (!sym_state_cache.has_state || !sym_state_cache.result_json) {
		return strdup ("{\"has_state\":false}");
	}
	needed = snprintf (NULL, 0,
		"{\"has_state\":true,\"mode\":\"%s\",\"entry\":\"0x%"PFMT64x"\",\"target\":\"0x%"PFMT64x"\",\"function\":\"0x%"PFMT64x"\",\"result\":%s}",
		sym_state_cache.mode ? sym_state_cache.mode : "",
		sym_state_cache.entry_addr,
		sym_state_cache.target_addr,
		sym_state_cache.function_addr,
		sym_state_cache.result_json);
	if (needed < 0) {
		return strdup ("{\"has_state\":false}");
	}
	json = malloc ((size_t)needed + 1);
	if (!json) {
		return strdup ("{\"has_state\":false}");
	}
	snprintf (json, (size_t)needed + 1,
		"{\"has_state\":true,\"mode\":\"%s\",\"entry\":\"0x%"PFMT64x"\",\"target\":\"0x%"PFMT64x"\",\"function\":\"0x%"PFMT64x"\",\"result\":%s}",
		sym_state_cache.mode ? sym_state_cache.mode : "",
		sym_state_cache.entry_addr,
		sym_state_cache.target_addr,
		sym_state_cache.function_addr,
		sym_state_cache.result_json);
	return json;
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
	size_t *out_lift_size,
	size_t *out_logical_size
) {
	size_t logical_size;
	size_t lift_size;
	size_t read_len;
	ut8 *buf;

	R_RETURN_VAL_IF_FAIL (
		anal && bb && out_buf && out_len && out_lift_size && out_logical_size,
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
	*out_logical_size = logical_size;
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

static bool parse_replay_target_and_json(RCore *core, const char *arg, ut64 *target, char **out_json) {
	char *owned = NULL;
	char *json = NULL;
	char *sep;
	const char *json_start;
	if (!core || !arg || !*arg || !target || !out_json) {
		return false;
	}
	*out_json = NULL;
	owned = strdup (arg);
	if (!owned) {
		return false;
	}
	sep = owned;
	while (*sep && !isspace ((unsigned char)*sep)) {
		sep++;
	}
	if (!*sep) {
		free (owned);
		return false;
	}
	*sep++ = '\0';
	json_start = skip_cmd_spaces (sep);
	if (!*json_start || !parse_sym_target_expr (core, owned, target)) {
		free (owned);
		return false;
	}
	json = strdup (json_start);
	free (owned);
	if (!json) {
		return false;
	}
	r_str_unescape (json);
	*out_json = json;
	return true;
}

static bool parse_target_and_optional_json(RCore *core, const char *arg, ut64 *target, char **out_json) {
	char *owned = NULL;
	char *json = NULL;
	char *sep;
	const char *json_start = NULL;

	if (!core || !arg || !*arg || !target || !out_json) {
		return false;
	}
	*out_json = NULL;
	owned = strdup (arg);
	if (!owned) {
		return false;
	}
	sep = owned;
	while (*sep && !isspace ((unsigned char)*sep)) {
		sep++;
	}
	if (*sep) {
		*sep++ = '\0';
		json_start = skip_cmd_spaces (sep);
	}
	if (!parse_sym_target_expr (core, owned, target)) {
		free (owned);
		return false;
	}
	if (json_start && *json_start) {
		json = strdup (json_start);
	} else {
		json = strdup ("{}");
	}
	free (owned);
	if (!json) {
		return false;
	}
	r_str_unescape (json);
	*out_json = json;
	return true;
}

typedef enum {
	REPLAY_EXPR_CONST = 0,
	REPLAY_EXPR_REG,
	REPLAY_EXPR_MEM,
	REPLAY_EXPR_META,
	REPLAY_EXPR_UNARY,
	REPLAY_EXPR_BINARY,
} ReplayExprKind;

typedef enum {
	REPLAY_MEM_U8 = 8,
	REPLAY_MEM_U16 = 16,
	REPLAY_MEM_U32 = 32,
	REPLAY_MEM_U64 = 64,
} ReplayMemWidth;

typedef enum {
	REPLAY_META_DEPTH = 0,
	REPLAY_META_INPUT_LEN,
} ReplayMetaKind;

typedef enum {
	REPLAY_UN_NEG = 0,
	REPLAY_UN_NOT,
} ReplayUnaryOp;

typedef enum {
	REPLAY_BIN_ADD = 0,
	REPLAY_BIN_SUB,
	REPLAY_BIN_MUL,
	REPLAY_BIN_DIV,
	REPLAY_BIN_MOD,
	REPLAY_BIN_SHL,
	REPLAY_BIN_SHR,
	REPLAY_BIN_BAND,
	REPLAY_BIN_BOR,
	REPLAY_BIN_BXOR,
	REPLAY_BIN_EQ,
	REPLAY_BIN_NE,
	REPLAY_BIN_LT,
	REPLAY_BIN_LE,
	REPLAY_BIN_GT,
	REPLAY_BIN_GE,
	REPLAY_BIN_AND,
	REPLAY_BIN_OR,
	REPLAY_BIN_ABSDIFF,
} ReplayBinaryOp;

typedef enum {
	REPLAY_SCORE_MAX = 0,
	REPLAY_SCORE_MIN,
} ReplayScoreOrder;

typedef struct replay_expr_t ReplayExpr;

struct replay_expr_t {
	int kind;
	union {
		st64 const_value;
		char *reg_name;
		struct {
			ut64 addr;
			int width_bits;
		} mem;
		int meta_kind;
		struct {
			int op;
			ReplayExpr *arg;
		} unary;
		struct {
			int op;
			ReplayExpr *lhs;
			ReplayExpr *rhs;
		} binary;
	};
};

typedef struct {
	bool ok;
	bool is_bool;
	union {
		st64 i;
		bool b;
	};
} ReplayEvalValue;

typedef struct {
	const RDebugStateSnapshot *snapshot;
	size_t depth;
	size_t input_len;
	bool big_endian;
} ReplayEvalContext;

typedef struct {
	ut64 seed_checkpoint;
	int replay_fd;
	char *alphabet;
	size_t max_depth;
	size_t beam_width;
	ReplayExpr **frontier_preds;
	size_t frontier_count;
	ReplayExpr **find_preds;
	size_t find_count;
	ReplayExpr **avoid_preds;
	size_t avoid_count;
	ReplayExpr *score_expr;
	int score_order;
	RDebugStateRequest *snapshot_request;
	ut64 *frontier_stop_addrs;
	size_t frontier_stop_count;
	ut64 *stop_addrs;
	size_t stop_count;
	bool big_endian;
} ReplaySearchSpec;

typedef struct {
	char *name;
	char *symbol;
} ReplaySymRegisterOverlay;

typedef struct {
	ut64 addr;
	ut32 size;
	char *name;
} ReplaySymMemoryOverlay;

typedef struct {
	ut64 checkpoint_id;
	ut64 entry_addr;
	RDebugStateRequest *snapshot_request;
	ReplaySymRegisterOverlay *register_overlays;
	size_t register_overlay_count;
	ReplaySymMemoryOverlay *memory_overlays;
	size_t memory_overlay_count;
	int *tty_fds;
	size_t tty_fd_count;
	bool skip_sleep_calls;
} ReplaySymSeedSpec;

typedef struct {
	ut64 checkpoint_id;
	char *input;
	size_t input_len;
	st64 score;
	char *snapshot_json;
} ReplaySearchNode;

typedef struct {
	ut64 checkpoint_id;
	char *input;
	size_t input_len;
	ut64 hit_addr;
	st64 score;
	char *snapshot_json;
} ReplaySearchMatch;

typedef enum {
	REPLAY_SEARCH_STOP_NONE = 0,
	REPLAY_SEARCH_STOP_FRONTIER,
	REPLAY_SEARCH_STOP_FIND,
	REPLAY_SEARCH_STOP_AVOID,
	REPLAY_SEARCH_STOP_OTHER,
} ReplaySearchStopKind;

typedef struct {
	ut64 *addrs;
	size_t count;
} ReplayTempBpSet;

static bool replay_parse_num_expr(RCore *core, const RJson *value, st64 *out) {
	if (!core || !value || !out) {
		return false;
	}
	if (value->type == R_JSON_INTEGER) {
		*out = value->num.s_value;
		return true;
	}
	if (value->type == R_JSON_STRING && value->str_value && *value->str_value) {
		*out = (st64)r_num_math (core->num, value->str_value);
		return true;
	}
	return false;
}

static bool replay_parse_addr_expr(RCore *core, const RJson *value, ut64 *out) {
	st64 signed_value = 0;
	if (!replay_parse_num_expr (core, value, &signed_value) || signed_value < 0) {
		return false;
	}
	*out = (ut64)signed_value;
	return true;
}

static void replay_expr_free(ReplayExpr *expr) {
	if (!expr) {
		return;
	}
	switch (expr->kind) {
	case REPLAY_EXPR_REG:
		free (expr->reg_name);
		break;
	case REPLAY_EXPR_UNARY:
		replay_expr_free (expr->unary.arg);
		break;
	case REPLAY_EXPR_BINARY:
		replay_expr_free (expr->binary.lhs);
		replay_expr_free (expr->binary.rhs);
		break;
	default:
		break;
	}
	free (expr);
}

static void replay_expr_array_free(ReplayExpr **exprs, size_t count) {
	size_t i;
	if (!exprs) {
		return;
	}
	for (i = 0; i < count; i++) {
		replay_expr_free (exprs[i]);
	}
	free (exprs);
}

static bool replay_is_pc_reg_name(const char *name) {
	return name && !strcasecmp (name, "pc");
}

static bool replay_expr_is_const_int(const ReplayExpr *expr, st64 *out) {
	if (!expr || expr->kind != REPLAY_EXPR_CONST) {
		return false;
	}
	if (out) {
		*out = expr->const_value;
	}
	return true;
}

static bool replay_expr_extract_pc_eq_addr(const ReplayExpr *expr, ut64 *out_addr) {
	st64 value = 0;
	if (!expr || expr->kind != REPLAY_EXPR_BINARY || expr->binary.op != REPLAY_BIN_EQ) {
		return false;
	}
	if (expr->binary.lhs && expr->binary.lhs->kind == REPLAY_EXPR_REG
		&& replay_is_pc_reg_name (expr->binary.lhs->reg_name)
		&& replay_expr_is_const_int (expr->binary.rhs, &value)
		&& value >= 0) {
		*out_addr = (ut64)value;
		return true;
	}
	if (expr->binary.rhs && expr->binary.rhs->kind == REPLAY_EXPR_REG
		&& replay_is_pc_reg_name (expr->binary.rhs->reg_name)
		&& replay_expr_is_const_int (expr->binary.lhs, &value)
		&& value >= 0) {
		*out_addr = (ut64)value;
		return true;
	}
	return false;
}

static bool replay_addr_list_contains(const ut64 *addrs, size_t count, ut64 addr) {
	size_t i;
	for (i = 0; i < count; i++) {
		if (addrs[i] == addr) {
			return true;
		}
	}
	return false;
}

static bool replay_addr_list_push_unique(ut64 **addrs, size_t *count, ut64 addr) {
	ut64 *next;
	if (!addrs || !count || !addr) {
		return false;
	}
	if (replay_addr_list_contains (*addrs, *count, addr)) {
		return true;
	}
	next = realloc (*addrs, (*count + 1) * sizeof (ut64));
	if (!next) {
		return false;
	}
	*addrs = next;
	(*addrs)[(*count)++] = addr;
	return true;
}

static const char *replay_json_kind_name(const RJson *value) {
	if (!value || value->type != R_JSON_OBJECT) {
		return NULL;
	}
	const RJson *kind = r_json_get (value, "kind");
	return (kind && kind->type == R_JSON_STRING)? kind->str_value: NULL;
}

static const char *replay_json_op_name(const RJson *value) {
	if (!value || value->type != R_JSON_OBJECT) {
		return NULL;
	}
	const RJson *op = r_json_get (value, "op");
	return (op && op->type == R_JSON_STRING)? op->str_value: NULL;
}

static bool replay_json_get_arg_array(const RJson *value, const RJson **first, const RJson **second, size_t *count) {
	const RJson *args = r_json_get (value, "args");
	RJson *child;
	size_t idx = 0;
	if (!first || !second || !count) {
		return false;
	}
	*first = NULL;
	*second = NULL;
	*count = 0;
	if (!args || args->type != R_JSON_ARRAY) {
		return false;
	}
	for (child = args->children.first; child; child = child->next) {
		if (idx == 0) {
			*first = child;
		} else if (idx == 1) {
			*second = child;
		}
		idx++;
	}
	*count = idx;
	return true;
}

static bool replay_parse_unary_op(const char *name, int *out) {
	if (!name || !out) {
		return false;
	}
	if (!strcmp (name, "neg")) {
		*out = REPLAY_UN_NEG;
		return true;
	}
	if (!strcmp (name, "not")) {
		*out = REPLAY_UN_NOT;
		return true;
	}
	return false;
}

static bool replay_parse_binary_op(const char *name, int *out) {
	if (!name || !out) {
		return false;
	}
	if (!strcmp (name, "add")) { *out = REPLAY_BIN_ADD; return true; }
	if (!strcmp (name, "sub")) { *out = REPLAY_BIN_SUB; return true; }
	if (!strcmp (name, "mul")) { *out = REPLAY_BIN_MUL; return true; }
	if (!strcmp (name, "div")) { *out = REPLAY_BIN_DIV; return true; }
	if (!strcmp (name, "mod")) { *out = REPLAY_BIN_MOD; return true; }
	if (!strcmp (name, "shl")) { *out = REPLAY_BIN_SHL; return true; }
	if (!strcmp (name, "shr")) { *out = REPLAY_BIN_SHR; return true; }
	if (!strcmp (name, "band")) { *out = REPLAY_BIN_BAND; return true; }
	if (!strcmp (name, "bor")) { *out = REPLAY_BIN_BOR; return true; }
	if (!strcmp (name, "bxor")) { *out = REPLAY_BIN_BXOR; return true; }
	if (!strcmp (name, "eq")) { *out = REPLAY_BIN_EQ; return true; }
	if (!strcmp (name, "ne")) { *out = REPLAY_BIN_NE; return true; }
	if (!strcmp (name, "lt")) { *out = REPLAY_BIN_LT; return true; }
	if (!strcmp (name, "le")) { *out = REPLAY_BIN_LE; return true; }
	if (!strcmp (name, "gt")) { *out = REPLAY_BIN_GT; return true; }
	if (!strcmp (name, "ge")) { *out = REPLAY_BIN_GE; return true; }
	if (!strcmp (name, "and")) { *out = REPLAY_BIN_AND; return true; }
	if (!strcmp (name, "or")) { *out = REPLAY_BIN_OR; return true; }
	if (!strcmp (name, "absdiff")) { *out = REPLAY_BIN_ABSDIFF; return true; }
	return false;
}

static bool replay_parse_meta_kind(const char *name, int *out) {
	if (!name || !out) {
		return false;
	}
	if (!strcmp (name, "depth")) {
		*out = REPLAY_META_DEPTH;
		return true;
	}
	if (!strcmp (name, "input_len")) {
		*out = REPLAY_META_INPUT_LEN;
		return true;
	}
	return false;
}

static bool replay_expr_parse(RCore *core, const RJson *value, ReplayExpr **out_expr) {
	const char *kind_name;
	const char *op_name;
	ReplayExpr *expr = NULL;
	const RJson *lhs = NULL;
	const RJson *rhs = NULL;
	const RJson *arg = NULL;
	const RJson *first = NULL;
	const RJson *second = NULL;
	size_t arg_count = 0;

	R_RETURN_VAL_IF_FAIL (core && value && out_expr, false);
	*out_expr = NULL;
	if (value->type != R_JSON_OBJECT) {
		return false;
	}
	expr = R_NEW0 (ReplayExpr);
	if (!expr) {
		return false;
	}

	kind_name = replay_json_kind_name (value);
	if (kind_name) {
		if (!strcmp (kind_name, "const")) {
			expr->kind = REPLAY_EXPR_CONST;
			if (!replay_parse_num_expr (core, r_json_get (value, "value"), &expr->const_value)) {
				goto fail;
			}
		} else if (!strcmp (kind_name, "reg")) {
			const RJson *name = r_json_get (value, "name");
			expr->kind = REPLAY_EXPR_REG;
			if (!name || name->type != R_JSON_STRING || R_STR_ISEMPTY (name->str_value)) {
				goto fail;
			}
			expr->reg_name = strdup (name->str_value);
			if (!expr->reg_name) {
				goto fail;
			}
		} else if (!strcmp (kind_name, "mem_u8") || !strcmp (kind_name, "mem_u16")
			|| !strcmp (kind_name, "mem_u32") || !strcmp (kind_name, "mem_u64")) {
			expr->kind = REPLAY_EXPR_MEM;
			if (!replay_parse_addr_expr (core, r_json_get (value, "addr"), &expr->mem.addr)) {
				goto fail;
			}
			if (!strcmp (kind_name, "mem_u8")) {
				expr->mem.width_bits = REPLAY_MEM_U8;
			} else if (!strcmp (kind_name, "mem_u16")) {
				expr->mem.width_bits = REPLAY_MEM_U16;
			} else if (!strcmp (kind_name, "mem_u32")) {
				expr->mem.width_bits = REPLAY_MEM_U32;
			} else {
				expr->mem.width_bits = REPLAY_MEM_U64;
			}
		} else if (!strcmp (kind_name, "meta")) {
			const RJson *name = r_json_get (value, "name");
			expr->kind = REPLAY_EXPR_META;
			if (!name || name->type != R_JSON_STRING || !replay_parse_meta_kind (name->str_value, &expr->meta_kind)) {
				goto fail;
			}
		} else {
			goto fail;
		}
		*out_expr = expr;
		return true;
	}

	op_name = replay_json_op_name (value);
	if (!op_name) {
		goto fail;
	}
	if (replay_parse_unary_op (op_name, &expr->unary.op)) {
		expr->kind = REPLAY_EXPR_UNARY;
		arg = r_json_get (value, "arg");
		if (!arg && replay_json_get_arg_array (value, &first, &second, &arg_count) && arg_count == 1) {
			arg = first;
		}
		if (!arg || !replay_expr_parse (core, arg, &expr->unary.arg)) {
			goto fail;
		}
		*out_expr = expr;
		return true;
	}
	if (!replay_parse_binary_op (op_name, &expr->binary.op)) {
		goto fail;
	}
	expr->kind = REPLAY_EXPR_BINARY;
	lhs = r_json_get (value, "lhs");
	rhs = r_json_get (value, "rhs");
	if ((!lhs || !rhs) && replay_json_get_arg_array (value, &first, &second, &arg_count) && arg_count == 2) {
		lhs = first;
		rhs = second;
	}
	if (!lhs || !rhs) {
		goto fail;
	}
	if (!replay_expr_parse (core, lhs, &expr->binary.lhs) || !replay_expr_parse (core, rhs, &expr->binary.rhs)) {
		goto fail;
	}
	*out_expr = expr;
	return true;

fail:
	replay_expr_free (expr);
	return false;
}

static bool replay_parse_predicate_array(RCore *core, const RJson *value, bool allow_empty, ReplayExpr ***out_exprs, size_t *out_count) {
	ReplayExpr **exprs = NULL;
	size_t count = 0;
	RJson *child;
	if (!out_exprs || !out_count) {
		return false;
	}
	*out_exprs = NULL;
	*out_count = 0;
	if (!value || value->type != R_JSON_ARRAY) {
		return false;
	}
	for (child = value->children.first; child; child = child->next) {
		ReplayExpr *expr = NULL;
		ReplayExpr **next;
		if (!replay_expr_parse (core, child, &expr)) {
			replay_expr_array_free (exprs, count);
			return false;
		}
		next = realloc (exprs, (count + 1) * sizeof (ReplayExpr *));
		if (!next) {
			replay_expr_free (expr);
			replay_expr_array_free (exprs, count);
			return false;
		}
		exprs = next;
		exprs[count++] = expr;
	}
	if (!count) {
		return allow_empty;
	}
	*out_exprs = exprs;
	*out_count = count;
	return true;
}

static RDebugStateRequest *replay_state_request_new(void) {
	RDebugStateRequest *request = R_NEW0 (RDebugStateRequest);
	if (!request) {
		return NULL;
	}
	request->registers = r_list_newf ((RListFree)r_debug_state_reg_spec_free);
	request->memory = r_list_newf ((RListFree)r_debug_state_mem_spec_free);
	if (!request->registers || !request->memory) {
		r_debug_state_request_free (request);
		return NULL;
	}
	return request;
}

static bool replay_state_request_add_reg(RDebugStateRequest *request, const char *name) {
	RListIter *iter;
	RDebugStateRegSpec *spec;
	if (!request || !name || replay_is_pc_reg_name (name)) {
		return true;
	}
	r_list_foreach (request->registers, iter, spec) {
		if (spec->name && !strcasecmp (spec->name, name)) {
			return true;
		}
	}
	spec = R_NEW0 (RDebugStateRegSpec);
	if (!spec) {
		return false;
	}
	spec->name = strdup (name);
	if (!spec->name) {
		r_debug_state_reg_spec_free (spec);
		return false;
	}
	r_list_append (request->registers, spec);
	return true;
}

static bool replay_state_request_add_mem_range(RDebugStateRequest *request, ut64 addr, ut32 size, const char *label) {
	RListIter *iter;
	RDebugStateMemSpec *spec;
	if (!request || !size) {
		return false;
	}
	r_list_foreach (request->memory, iter, spec) {
		if (spec->addr == addr && spec->size == size) {
			return true;
		}
	}
	spec = R_NEW0 (RDebugStateMemSpec);
	if (!spec) {
		return false;
	}
	spec->addr = addr;
	spec->size = size;
	if (label && *label) {
		spec->label = strdup (label);
		if (!spec->label) {
			r_debug_state_mem_spec_free (spec);
			return false;
		}
	}
	r_list_append (request->memory, spec);
	return true;
}

static bool replay_state_request_add_mem(RDebugStateRequest *request, ut64 addr, int width_bits) {
	ut32 size = (ut32)(width_bits / 8);
	return replay_state_request_add_mem_range (request, addr, size, NULL);
}

static bool replay_state_request_add_all_gprs(RDebug *dbg, RDebugStateRequest *request) {
	RListIter *iter;
	RRegItem *item;
	RList *regs;
	if (!dbg || !dbg->reg || !request) {
		return false;
	}
	regs = r_reg_get_list (dbg->reg, R_REG_TYPE_GPR);
	if (!regs) {
		return false;
	}
	r_list_foreach (regs, iter, item) {
		if (item && item->name && !replay_state_request_add_reg (request, item->name)) {
			return false;
		}
	}
	return true;
}

static bool replay_expr_collect_state(const ReplayExpr *expr, RDebugStateRequest *request) {
	if (!expr || !request) {
		return false;
	}
	switch (expr->kind) {
	case REPLAY_EXPR_REG:
		return replay_state_request_add_reg (request, expr->reg_name);
	case REPLAY_EXPR_MEM:
		return replay_state_request_add_mem (request, expr->mem.addr, expr->mem.width_bits);
	case REPLAY_EXPR_UNARY:
		return replay_expr_collect_state (expr->unary.arg, request);
	case REPLAY_EXPR_BINARY:
		return replay_expr_collect_state (expr->binary.lhs, request)
			&& replay_expr_collect_state (expr->binary.rhs, request);
	default:
		return true;
	}
}

static bool replay_collect_stop_addrs(ReplayExpr **exprs, size_t count, ut64 **out_addrs, size_t *out_count) {
	size_t i;
	if (!out_addrs || !out_count) {
		return false;
	}
	*out_addrs = NULL;
	*out_count = 0;
	for (i = 0; i < count; i++) {
		ut64 addr = 0;
		if (replay_expr_extract_pc_eq_addr (exprs[i], &addr) && !replay_addr_list_push_unique (out_addrs, out_count, addr)) {
			free (*out_addrs);
			*out_addrs = NULL;
			*out_count = 0;
			return false;
		}
	}
	return true;
}

static void replay_search_spec_fini(ReplaySearchSpec *spec) {
	if (!spec) {
		return;
	}
	free (spec->alphabet);
	spec->alphabet = NULL;
	replay_expr_array_free (spec->frontier_preds, spec->frontier_count);
	replay_expr_array_free (spec->find_preds, spec->find_count);
	replay_expr_array_free (spec->avoid_preds, spec->avoid_count);
	spec->frontier_preds = NULL;
	spec->find_preds = NULL;
	spec->avoid_preds = NULL;
	spec->frontier_count = 0;
	spec->find_count = 0;
	spec->avoid_count = 0;
	replay_expr_free (spec->score_expr);
	spec->score_expr = NULL;
	r_debug_state_request_free (spec->snapshot_request);
	spec->snapshot_request = NULL;
	free (spec->frontier_stop_addrs);
	free (spec->stop_addrs);
	spec->frontier_stop_addrs = NULL;
	spec->stop_addrs = NULL;
	spec->frontier_stop_count = 0;
	spec->stop_count = 0;
}

static void replay_sym_seed_spec_fini(ReplaySymSeedSpec *spec) {
	size_t i;
	if (!spec) {
		return;
	}
	r_debug_state_request_free (spec->snapshot_request);
	spec->snapshot_request = NULL;
	for (i = 0; i < spec->register_overlay_count; i++) {
		free (spec->register_overlays[i].name);
		free (spec->register_overlays[i].symbol);
	}
	free (spec->register_overlays);
	spec->register_overlays = NULL;
	spec->register_overlay_count = 0;
	for (i = 0; i < spec->memory_overlay_count; i++) {
		free (spec->memory_overlays[i].name);
	}
	free (spec->memory_overlays);
	spec->memory_overlays = NULL;
	spec->memory_overlay_count = 0;
	free (spec->tty_fds);
	spec->tty_fds = NULL;
	spec->tty_fd_count = 0;
	spec->checkpoint_id = 0;
	spec->entry_addr = 0;
	spec->skip_sleep_calls = false;
}

static bool replay_sym_seed_add_register_overlay(ReplaySymSeedSpec *spec, const char *name, const char *symbol) {
	ReplaySymRegisterOverlay *next;
	size_t index;
	if (!spec || !name || !*name || !symbol || !*symbol) {
		return false;
	}
	next = realloc (spec->register_overlays, (spec->register_overlay_count + 1) * sizeof (*next));
	if (!next) {
		return false;
	}
	spec->register_overlays = next;
	index = spec->register_overlay_count++;
	memset (&spec->register_overlays[index], 0, sizeof (spec->register_overlays[index]));
	spec->register_overlays[index].name = strdup (name);
	spec->register_overlays[index].symbol = strdup (symbol);
	if (!spec->register_overlays[index].name || !spec->register_overlays[index].symbol) {
		free (spec->register_overlays[index].name);
		free (spec->register_overlays[index].symbol);
		spec->register_overlays[index].name = NULL;
		spec->register_overlays[index].symbol = NULL;
		spec->register_overlay_count--;
		return false;
	}
	return true;
}

static bool replay_sym_seed_add_memory_overlay(ReplaySymSeedSpec *spec, ut64 addr, ut32 size, const char *name) {
	ReplaySymMemoryOverlay *next;
	size_t index;
	if (!spec || !size || !name || !*name) {
		return false;
	}
	next = realloc (spec->memory_overlays, (spec->memory_overlay_count + 1) * sizeof (*next));
	if (!next) {
		return false;
	}
	spec->memory_overlays = next;
	index = spec->memory_overlay_count++;
	memset (&spec->memory_overlays[index], 0, sizeof (spec->memory_overlays[index]));
	spec->memory_overlays[index].addr = addr;
	spec->memory_overlays[index].size = size;
	spec->memory_overlays[index].name = strdup (name);
	if (!spec->memory_overlays[index].name) {
		spec->memory_overlay_count--;
		return false;
	}
	return true;
}

static bool replay_sym_seed_add_tty_fd(ReplaySymSeedSpec *spec, int fd) {
	int *next;
	if (!spec) {
		return false;
	}
	next = realloc (spec->tty_fds, (spec->tty_fd_count + 1) * sizeof (*next));
	if (!next) {
		return false;
	}
	spec->tty_fds = next;
	spec->tty_fds[spec->tty_fd_count++] = fd;
	return true;
}

static bool replay_sym_seed_spec_parse(RCore *core, const char *json, ReplaySymSeedSpec *spec, bool require_checkpoint) {
	char *json_copy;
	char *owned_json = NULL;
	RJson *root;
	const RJson *value;
	size_t i;

	R_RETURN_VAL_IF_FAIL (core && core->dbg && json && spec, false);
	memset (spec, 0, sizeof (*spec));
	spec->snapshot_request = replay_state_request_new ();
	if (!spec->snapshot_request || !replay_state_request_add_all_gprs (core->dbg, spec->snapshot_request)) {
		replay_sym_seed_spec_fini (spec);
		return false;
	}

	json_copy = strdup (json);
	if (!json_copy) {
		replay_sym_seed_spec_fini (spec);
		return false;
	}
	owned_json = json_copy;
	root = r_json_parse (json_copy);
	if (!root || root->type != R_JSON_OBJECT) {
		R_LOG_ERROR ("r2sleigh replay sym seed: json root parse failed");
		free (owned_json);
		r_json_free (root);
		replay_sym_seed_spec_fini (spec);
		return false;
	}

	value = r_json_get (root, "checkpoint");
	if (!value) {
		value = r_json_get (root, "seed_checkpoint");
	}
	if (value) {
		if (!replay_parse_addr_expr (core, value, &spec->checkpoint_id) || !spec->checkpoint_id) {
			R_LOG_ERROR ("r2sleigh replay sym seed: invalid checkpoint");
			goto fail;
		}
	} else if (require_checkpoint) {
		R_LOG_ERROR ("r2sleigh replay sym seed: missing/invalid checkpoint");
		goto fail;
	}
	value = r_json_get (root, "entry");
	if (value && !replay_parse_addr_expr (core, value, &spec->entry_addr)) {
		R_LOG_ERROR ("r2sleigh replay sym seed: invalid entry");
		goto fail;
	}
	value = r_json_get (root, "skip_sleep");
	if (value) {
		if (value->type != R_JSON_BOOLEAN) {
			R_LOG_ERROR ("r2sleigh replay sym seed: invalid skip_sleep");
			goto fail;
		}
		spec->skip_sleep_calls = value->num.u_value;
	}
	value = r_json_get (root, "tty_fds");
	if (value) {
		if (value->type != R_JSON_ARRAY) {
			R_LOG_ERROR ("r2sleigh replay sym seed: invalid tty_fds");
			goto fail;
		}
		for (i = 0; i < value->children.count; i++) {
			const RJson *item = r_json_item (value, i);
			st64 fd = 0;
			if (!replay_parse_num_expr (core, item, &fd)) {
				R_LOG_ERROR ("r2sleigh replay sym seed: invalid tty fd");
				goto fail;
			}
			if (!replay_sym_seed_add_tty_fd (spec, (int)fd)) {
				goto fail;
			}
		}
	}
	value = r_json_get (root, "memory");
	if (value) {
		if (value->type != R_JSON_ARRAY) {
			R_LOG_ERROR ("r2sleigh replay sym seed: invalid memory");
			goto fail;
		}
		for (i = 0; i < value->children.count; i++) {
			const RJson *item = r_json_item (value, i);
			const RJson *label_json;
			char *label = NULL;
			ut64 addr = 0;
			st64 size_value = 0;
			if (!item || item->type != R_JSON_OBJECT) {
				R_LOG_ERROR ("r2sleigh replay sym seed: invalid memory item");
				goto fail;
			}
			if (!replay_parse_addr_expr (core, r_json_get (item, "addr"), &addr)
				|| !replay_parse_num_expr (core, r_json_get (item, "size"), &size_value)
				|| size_value <= 0 || size_value > UT32_MAX) {
				R_LOG_ERROR ("r2sleigh replay sym seed: invalid memory window");
				goto fail;
			}
			label_json = r_json_get (item, "label");
			if (label_json && label_json->type == R_JSON_STRING && label_json->str_value) {
				label = strdup (label_json->str_value);
				if (!label) {
					goto fail;
				}
			}
			if (!replay_state_request_add_mem_range (spec->snapshot_request, addr, (ut32)size_value, label)) {
				free (label);
				goto fail;
			}
			free (label);
		}
	}
	value = r_json_get (root, "symbolic_registers");
	if (value) {
		if (value->type != R_JSON_ARRAY) {
			R_LOG_ERROR ("r2sleigh replay sym seed: invalid symbolic_registers");
			goto fail;
		}
		for (i = 0; i < value->children.count; i++) {
			const RJson *item = r_json_item (value, i);
			const char *name = NULL;
			const char *symbol = NULL;
			char default_symbol[128];
			if (!item) {
				goto fail;
			}
			if (item->type == R_JSON_STRING && item->str_value) {
				name = item->str_value;
			} else if (item->type == R_JSON_OBJECT) {
				const RJson *name_json = r_json_get (item, "name");
				const RJson *symbol_json = r_json_get (item, "symbol");
				if (name_json && name_json->type == R_JSON_STRING) {
					name = name_json->str_value;
				}
				if (symbol_json && symbol_json->type == R_JSON_STRING) {
					symbol = symbol_json->str_value;
				}
			}
			if (!name || !*name) {
				R_LOG_ERROR ("r2sleigh replay sym seed: invalid symbolic register");
				goto fail;
			}
			if (!symbol || !*symbol) {
				snprintf (default_symbol, sizeof (default_symbol), "replay_%s", name);
				symbol = default_symbol;
			}
			if (!replay_sym_seed_add_register_overlay (spec, name, symbol)) {
				goto fail;
			}
		}
	}
	value = r_json_get (root, "symbolic_memory");
	if (value) {
		if (value->type != R_JSON_ARRAY) {
			R_LOG_ERROR ("r2sleigh replay sym seed: invalid symbolic_memory");
			goto fail;
		}
		for (i = 0; i < value->children.count; i++) {
			const RJson *item = r_json_item (value, i);
			const RJson *name_json;
			char default_name[128];
			const char *name = NULL;
			ut64 addr = 0;
			st64 size_value = 0;
			if (!item || item->type != R_JSON_OBJECT) {
				R_LOG_ERROR ("r2sleigh replay sym seed: invalid symbolic memory item");
				goto fail;
			}
			if (!replay_parse_addr_expr (core, r_json_get (item, "addr"), &addr)
				|| !replay_parse_num_expr (core, r_json_get (item, "size"), &size_value)
				|| size_value <= 0 || size_value > UT32_MAX) {
				R_LOG_ERROR ("r2sleigh replay sym seed: invalid symbolic memory window");
				goto fail;
			}
			name_json = r_json_get (item, "name");
			if (name_json && name_json->type == R_JSON_STRING && name_json->str_value) {
				name = name_json->str_value;
			} else {
				snprintf (default_name, sizeof (default_name), "replay_mem_%zu", i);
				name = default_name;
			}
			if (!replay_state_request_add_mem_range (spec->snapshot_request, addr, (ut32)size_value, name)
				|| !replay_sym_seed_add_memory_overlay (spec, addr, (ut32)size_value, name)) {
				goto fail;
			}
		}
	}

	free (owned_json);
	r_json_free (root);
	return true;

fail:
	free (owned_json);
	r_json_free (root);
	replay_sym_seed_spec_fini (spec);
	return false;
}

static RDebugStateSnapshot *replay_sym_collect_seed_snapshot(RCore *core, const ReplaySymSeedSpec *spec) {
	RDebugStateSnapshot *snapshot;
	ut64 previous_checkpoint;

	R_RETURN_VAL_IF_FAIL (core && core->dbg && spec && spec->snapshot_request, NULL);
	if (!spec->checkpoint_id) {
		return r_debug_state_snapshot_collect (core->dbg, spec->snapshot_request);
	}
	R_RETURN_VAL_IF_FAIL (core->dbg->session, NULL);
	previous_checkpoint = core->dbg->session->current_checkpoint_id;
	if (!r_debug_session_restore_checkpoint (core->dbg, spec->checkpoint_id)) {
		return NULL;
	}
	snapshot = r_debug_state_snapshot_collect (core->dbg, spec->snapshot_request);
	if (previous_checkpoint != UT64_MAX && previous_checkpoint != spec->checkpoint_id) {
		r_debug_session_restore_checkpoint (core->dbg, previous_checkpoint);
	}
	return snapshot;
}

static char *replay_sym_query_run(RCore *core, const R2ILContext *ctx, const SymFunctionScope *scope,
	ut64 entry_addr, ut64 target_addr, const ReplaySymSeedSpec *spec, bool is_explore,
	const char *external_context_json) {
	RDebugStateSnapshot *snapshot = NULL;
	R2SymReplayRegister *registers = NULL;
	R2SymReplayMemoryWindow *memory = NULL;
	R2SymReplayRegisterOverlay *register_overlays = NULL;
	R2SymReplayMemoryOverlay *memory_overlays = NULL;
	R2SymReplaySeed seed = {0};
	RListIter *iter;
	RDebugStateRegValue *reg;
	RDebugStateMemValue *memv;
	size_t reg_count = 0;
	size_t mem_count = 0;
	size_t idx = 0;
	char *result = NULL;

	R_RETURN_VAL_IF_FAIL (core && ctx && scope && spec, NULL);

	snapshot = replay_sym_collect_seed_snapshot (core, spec);
	if (!snapshot) {
		return NULL;
	}
	r_list_foreach (snapshot->registers, iter, reg) {
		if (reg && reg->found && reg->name) {
			reg_count++;
		}
	}
	r_list_foreach (snapshot->memory, iter, memv) {
		if (memv && memv->ok && memv->bytes && memv->size > 0) {
			mem_count++;
		}
	}
	registers = reg_count? calloc (reg_count, sizeof (*registers)): NULL;
	memory = mem_count? calloc (mem_count, sizeof (*memory)): NULL;
	register_overlays = spec->register_overlay_count? calloc (spec->register_overlay_count, sizeof (*register_overlays)): NULL;
	memory_overlays = spec->memory_overlay_count? calloc (spec->memory_overlay_count, sizeof (*memory_overlays)): NULL;
	if ((reg_count && !registers) || (mem_count && !memory)
		|| (spec->register_overlay_count && !register_overlays)
		|| (spec->memory_overlay_count && !memory_overlays)) {
		goto cleanup;
	}

	idx = 0;
	r_list_foreach (snapshot->registers, iter, reg) {
		if (!reg || !reg->found || !reg->name) {
			continue;
		}
		registers[idx].name = reg->name;
		registers[idx].value = reg->value;
		idx++;
	}
	idx = 0;
	r_list_foreach (snapshot->memory, iter, memv) {
		if (!memv || !memv->ok || !memv->bytes || !memv->size) {
			continue;
		}
		memory[idx].addr = memv->addr;
		memory[idx].bytes = memv->bytes;
		memory[idx].size = memv->size;
		memory[idx].label = memv->label;
		idx++;
	}
	for (idx = 0; idx < spec->register_overlay_count; idx++) {
		register_overlays[idx].name = spec->register_overlays[idx].name;
		register_overlays[idx].symbol = spec->register_overlays[idx].symbol;
	}
	for (idx = 0; idx < spec->memory_overlay_count; idx++) {
		memory_overlays[idx].addr = spec->memory_overlays[idx].addr;
		memory_overlays[idx].size = spec->memory_overlays[idx].size;
		memory_overlays[idx].name = spec->memory_overlays[idx].name;
	}

	seed.checkpoint_id = spec->checkpoint_id;
	seed.entry_addr = spec->entry_addr? spec->entry_addr: snapshot->pc;
	seed.registers = registers;
	seed.num_registers = reg_count;
	seed.memory = memory;
	seed.num_memory = mem_count;
	seed.register_overlays = register_overlays;
	seed.num_register_overlays = spec->register_overlay_count;
	seed.memory_overlays = memory_overlays;
	seed.num_memory_overlays = spec->memory_overlay_count;
	seed.tty_fds = spec->tty_fds;
	seed.num_tty_fds = spec->tty_fd_count;
	seed.skip_sleep_calls = spec->skip_sleep_calls? 1: 0;

	const uint32_t kind = is_explore
		? R2SLEIGH_SCOPE_EXPLORE_REPLAY_V2: R2SLEIGH_SCOPE_SOLVE_REPLAY_V2;
	(void)sleigh_v2_scope_render_for_scope (kind, core, core->anal, ctx, scope,
		entry_addr, target_addr, &seed, NULL, external_context_json, &result);

cleanup:
	free (registers);
	free (memory);
	free (register_overlays);
	free (memory_overlays);
	r_debug_state_snapshot_free (snapshot);
	return result;
}

static void replay_search_node_free(ReplaySearchNode *node) {
	if (!node) {
		return;
	}
	free (node->input);
	free (node->snapshot_json);
	free (node);
}

static void replay_search_match_free(ReplaySearchMatch *match) {
	if (!match) {
		return;
	}
	free (match->input);
	free (match->snapshot_json);
	free (match);
}

static bool replay_eval_snapshot_reg(const ReplayEvalContext *ctx, const char *name, st64 *out) {
	RListIter *iter;
	RDebugStateRegValue *reg;
	if (!ctx || !ctx->snapshot || !name || !out) {
		return false;
	}
	if (replay_is_pc_reg_name (name)) {
		*out = (st64)ctx->snapshot->pc;
		return true;
	}
	r_list_foreach (ctx->snapshot->registers, iter, reg) {
		if (reg->name && !strcasecmp (reg->name, name) && reg->found) {
			*out = (st64)reg->value;
			return true;
		}
	}
	return false;
}

static bool replay_eval_snapshot_mem(const ReplayEvalContext *ctx, ut64 addr, int width_bits, st64 *out) {
	RListIter *iter;
	RDebugStateMemValue *mem;
	ut32 size = (ut32)(width_bits / 8);
	if (!ctx || !ctx->snapshot || !out || !size) {
		return false;
	}
	r_list_foreach (ctx->snapshot->memory, iter, mem) {
		if (mem->addr == addr && mem->size == size && mem->ok && mem->bytes) {
			*out = (st64)r_read_ble (mem->bytes, ctx->big_endian, size);
			return true;
		}
	}
	return false;
}

static ReplayEvalValue replay_eval_error(void) {
	ReplayEvalValue value = {0};
	return value;
}

static ReplayEvalValue replay_eval_int(st64 i) {
	ReplayEvalValue value = {0};
	value.ok = true;
	value.i = i;
	value.is_bool = false;
	return value;
}

static ReplayEvalValue replay_eval_bool(bool b) {
	ReplayEvalValue value = {0};
	value.ok = true;
	value.b = b;
	value.is_bool = true;
	return value;
}

static ReplayEvalValue replay_eval_expr(const ReplayExpr *expr, const ReplayEvalContext *ctx) {
	ReplayEvalValue lhs;
	ReplayEvalValue rhs;
	if (!expr || !ctx) {
		return replay_eval_error ();
	}
	switch (expr->kind) {
	case REPLAY_EXPR_CONST:
		return replay_eval_int (expr->const_value);
	case REPLAY_EXPR_REG: {
		st64 value = 0;
		return replay_eval_snapshot_reg (ctx, expr->reg_name, &value)? replay_eval_int (value): replay_eval_error ();
	}
	case REPLAY_EXPR_MEM: {
		st64 value = 0;
		return replay_eval_snapshot_mem (ctx, expr->mem.addr, expr->mem.width_bits, &value)? replay_eval_int (value): replay_eval_error ();
	}
	case REPLAY_EXPR_META:
		return replay_eval_int (expr->meta_kind == REPLAY_META_DEPTH? (st64)ctx->depth: (st64)ctx->input_len);
	case REPLAY_EXPR_UNARY: {
		ReplayEvalValue arg = replay_eval_expr (expr->unary.arg, ctx);
		if (!arg.ok) {
			return arg;
		}
		if (expr->unary.op == REPLAY_UN_NEG) {
			return arg.is_bool? replay_eval_error (): replay_eval_int (-arg.i);
		}
		if (expr->unary.op == REPLAY_UN_NOT) {
			return arg.is_bool? replay_eval_bool (!arg.b): replay_eval_error ();
		}
		return replay_eval_error ();
	}
	case REPLAY_EXPR_BINARY:
		lhs = replay_eval_expr (expr->binary.lhs, ctx);
		rhs = replay_eval_expr (expr->binary.rhs, ctx);
		if (!lhs.ok || !rhs.ok) {
			return replay_eval_error ();
		}
		switch (expr->binary.op) {
		case REPLAY_BIN_ADD: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_int (lhs.i + rhs.i): replay_eval_error ();
		case REPLAY_BIN_SUB: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_int (lhs.i - rhs.i): replay_eval_error ();
		case REPLAY_BIN_MUL: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_int (lhs.i * rhs.i): replay_eval_error ();
		case REPLAY_BIN_DIV: return (!lhs.is_bool && !rhs.is_bool && rhs.i != 0)? replay_eval_int (lhs.i / rhs.i): replay_eval_error ();
		case REPLAY_BIN_MOD: return (!lhs.is_bool && !rhs.is_bool && rhs.i != 0)? replay_eval_int (lhs.i % rhs.i): replay_eval_error ();
		case REPLAY_BIN_SHL: return (!lhs.is_bool && !rhs.is_bool && rhs.i >= 0)? replay_eval_int ((st64)((ut64)lhs.i << rhs.i)): replay_eval_error ();
		case REPLAY_BIN_SHR: return (!lhs.is_bool && !rhs.is_bool && rhs.i >= 0)? replay_eval_int ((st64)((ut64)lhs.i >> rhs.i)): replay_eval_error ();
		case REPLAY_BIN_BAND: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_int ((st64)((ut64)lhs.i & (ut64)rhs.i)): replay_eval_error ();
		case REPLAY_BIN_BOR: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_int ((st64)((ut64)lhs.i | (ut64)rhs.i)): replay_eval_error ();
		case REPLAY_BIN_BXOR: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_int ((st64)((ut64)lhs.i ^ (ut64)rhs.i)): replay_eval_error ();
		case REPLAY_BIN_EQ:
			if (lhs.is_bool != rhs.is_bool) {
				return replay_eval_error ();
			}
			return lhs.is_bool? replay_eval_bool (lhs.b == rhs.b): replay_eval_bool (lhs.i == rhs.i);
		case REPLAY_BIN_NE:
			if (lhs.is_bool != rhs.is_bool) {
				return replay_eval_error ();
			}
			return lhs.is_bool? replay_eval_bool (lhs.b != rhs.b): replay_eval_bool (lhs.i != rhs.i);
		case REPLAY_BIN_LT: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_bool (lhs.i < rhs.i): replay_eval_error ();
		case REPLAY_BIN_LE: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_bool (lhs.i <= rhs.i): replay_eval_error ();
		case REPLAY_BIN_GT: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_bool (lhs.i > rhs.i): replay_eval_error ();
		case REPLAY_BIN_GE: return (!lhs.is_bool && !rhs.is_bool)? replay_eval_bool (lhs.i >= rhs.i): replay_eval_error ();
		case REPLAY_BIN_AND: return (lhs.is_bool && rhs.is_bool)? replay_eval_bool (lhs.b && rhs.b): replay_eval_error ();
		case REPLAY_BIN_OR: return (lhs.is_bool && rhs.is_bool)? replay_eval_bool (lhs.b || rhs.b): replay_eval_error ();
		case REPLAY_BIN_ABSDIFF:
			if (lhs.is_bool || rhs.is_bool) {
				return replay_eval_error ();
			}
			return replay_eval_int (lhs.i > rhs.i? lhs.i - rhs.i: rhs.i - lhs.i);
		default:
			return replay_eval_error ();
		}
	default:
		return replay_eval_error ();
	}
}

static bool replay_eval_predicates(ReplayExpr **exprs, size_t count, const ReplayEvalContext *ctx) {
	size_t i;
	for (i = 0; i < count; i++) {
		ReplayEvalValue value = replay_eval_expr (exprs[i], ctx);
		if (value.ok && value.is_bool && value.b) {
			return true;
		}
	}
	return false;
}

static bool replay_eval_score(const ReplaySearchSpec *spec, const ReplayEvalContext *ctx, st64 *out_score) {
	ReplayEvalValue value;
	if (!spec || !spec->score_expr || !out_score) {
		return false;
	}
	value = replay_eval_expr (spec->score_expr, ctx);
	if (!value.ok || value.is_bool) {
		return false;
	}
	*out_score = value.i;
	return true;
}

static RDebugStateSnapshot *replay_collect_snapshot(RCore *core, const ReplaySearchSpec *spec) {
	if (!core || !spec || !spec->snapshot_request) {
		return NULL;
	}
	return r_debug_state_snapshot_collect (core->dbg, spec->snapshot_request);
}

static bool replay_search_spec_parse(RCore *core, const char *json, ReplaySearchSpec *spec) {
	char *json_copy;
	char *owned_json = NULL;
	RJson *root;
	const RJson *value;
	size_t i;

	R_RETURN_VAL_IF_FAIL (core && json && spec, false);
	memset (spec, 0, sizeof (*spec));
	spec->replay_fd = 0;
	spec->max_depth = 1;
	spec->beam_width = 16;
	spec->score_order = REPLAY_SCORE_MAX;
	spec->big_endian = core->rasm && core->rasm->config
		? R_ARCH_CONFIG_IS_BIG_ENDIAN (core->rasm->config)
		: false;

	json_copy = strdup (json);
	if (!json_copy) {
		return false;
	}
	owned_json = json_copy;
	root = r_json_parse (json_copy);
	if (!root || root->type != R_JSON_OBJECT) {
		R_LOG_ERROR ("r2sleigh replayj: json root parse failed");
		free (owned_json);
		r_json_free (root);
		return false;
	}

	value = r_json_get (root, "seed_checkpoint");
	if (!value) {
		value = r_json_get (root, "seed");
	}
	if (!replay_parse_addr_expr (core, value, &spec->seed_checkpoint) || !spec->seed_checkpoint) {
		R_LOG_ERROR ("r2sleigh replayj: missing/invalid seed_checkpoint");
		goto fail;
	}
	value = r_json_get (root, "replay_fd");
	if (value) {
		if (value->type != R_JSON_INTEGER) {
			R_LOG_ERROR ("r2sleigh replayj: invalid replay_fd");
			goto fail;
		}
		spec->replay_fd = value->num.s_value;
	}
	value = r_json_get (root, "alphabet");
	if (!value || value->type != R_JSON_STRING || !value->str_value || !*value->str_value) {
		R_LOG_ERROR ("r2sleigh replayj: missing/invalid alphabet");
		goto fail;
	}
	spec->alphabet = strdup (value->str_value);
	if (!spec->alphabet) {
		goto fail;
	}
	value = r_json_get (root, "max_depth");
	if (value) {
		if (value->type != R_JSON_INTEGER || !value->num.u_value) {
			R_LOG_ERROR ("r2sleigh replayj: invalid max_depth");
			goto fail;
		}
		spec->max_depth = (size_t)value->num.u_value;
	}
	value = r_json_get (root, "beam_width");
	if (value) {
		if (value->type != R_JSON_INTEGER || !value->num.u_value) {
			R_LOG_ERROR ("r2sleigh replayj: invalid beam_width");
			goto fail;
		}
		spec->beam_width = (size_t)value->num.u_value;
	}
	if (!replay_parse_predicate_array (core, r_json_get (root, "frontier"), false, &spec->frontier_preds, &spec->frontier_count)) {
		R_LOG_ERROR ("r2sleigh replayj: missing/invalid frontier");
		goto fail;
	}
	if (!replay_parse_predicate_array (core, r_json_get (root, "find"), false, &spec->find_preds, &spec->find_count)) {
		R_LOG_ERROR ("r2sleigh replayj: missing/invalid find");
		goto fail;
	}
	value = r_json_get (root, "avoid");
	if (value && !replay_parse_predicate_array (core, value, true, &spec->avoid_preds, &spec->avoid_count)) {
		R_LOG_ERROR ("r2sleigh replayj: invalid avoid");
		goto fail;
	}
	value = r_json_get (root, "score");
	if (!value || value->type != R_JSON_OBJECT) {
		R_LOG_ERROR ("r2sleigh replayj: missing/invalid score");
		goto fail;
	}
	{
		const RJson *order = r_json_get (value, "order");
		if (!order || order->type != R_JSON_STRING) {
			R_LOG_ERROR ("r2sleigh replayj: missing score.order");
			goto fail;
		}
		if (!strcmp (order->str_value, "max")) {
			spec->score_order = REPLAY_SCORE_MAX;
		} else if (!strcmp (order->str_value, "min")) {
			spec->score_order = REPLAY_SCORE_MIN;
		} else {
			R_LOG_ERROR ("r2sleigh replayj: invalid score.order");
			goto fail;
		}
		if (!replay_expr_parse (core, r_json_get (value, "expr"), &spec->score_expr)) {
			R_LOG_ERROR ("r2sleigh replayj: invalid score.expr");
			goto fail;
		}
	}

	spec->snapshot_request = replay_state_request_new ();
	if (!spec->snapshot_request) {
		goto fail;
	}
	for (i = 0; i < spec->frontier_count; i++) {
		if (!replay_expr_collect_state (spec->frontier_preds[i], spec->snapshot_request)) {
			goto fail;
		}
	}
	for (i = 0; i < spec->find_count; i++) {
		if (!replay_expr_collect_state (spec->find_preds[i], spec->snapshot_request)) {
			goto fail;
		}
	}
	for (i = 0; i < spec->avoid_count; i++) {
		if (!replay_expr_collect_state (spec->avoid_preds[i], spec->snapshot_request)) {
			goto fail;
		}
	}
	if (!replay_expr_collect_state (spec->score_expr, spec->snapshot_request)) {
		goto fail;
	}

	if (!replay_collect_stop_addrs (spec->frontier_preds, spec->frontier_count, &spec->frontier_stop_addrs, &spec->frontier_stop_count)
		|| !spec->frontier_stop_count) {
		R_LOG_ERROR ("r2sleigh replayj: frontier must contain at least one exact PC == const predicate");
		goto fail;
	}
	for (i = 0; i < spec->frontier_stop_count; i++) {
		if (!replay_addr_list_push_unique (&spec->stop_addrs, &spec->stop_count, spec->frontier_stop_addrs[i])) {
			goto fail;
		}
	}
	{
		ut64 *tmp = NULL;
		size_t tmp_count = 0;
		if (!replay_collect_stop_addrs (spec->find_preds, spec->find_count, &tmp, &tmp_count)) {
			goto fail;
		}
		for (i = 0; i < tmp_count; i++) {
			if (!replay_addr_list_push_unique (&spec->stop_addrs, &spec->stop_count, tmp[i])) {
				free (tmp);
				goto fail;
			}
		}
		free (tmp);
		tmp = NULL;
		tmp_count = 0;
		if (spec->avoid_count && !replay_collect_stop_addrs (spec->avoid_preds, spec->avoid_count, &tmp, &tmp_count)) {
			goto fail;
		}
		for (i = 0; i < tmp_count; i++) {
			if (!replay_addr_list_push_unique (&spec->stop_addrs, &spec->stop_count, tmp[i])) {
				free (tmp);
				goto fail;
			}
		}
		free (tmp);
	}

	free (owned_json);
	r_json_free (root);
	return true;

fail:
	free (owned_json);
	r_json_free (root);
	replay_search_spec_fini (spec);
	return false;
}

static char *replay_input_append_char(const char *input, size_t input_len, char ch) {
	char *next = malloc (input_len + 2);
	if (!next) {
		return NULL;
	}
	if (input_len && input) {
		memcpy (next, input, input_len);
	}
	next[input_len] = ch;
	next[input_len + 1] = '\0';
	return next;
}

static void replay_temp_bps_fini(RCore *core, ReplayTempBpSet *set) {
	size_t i;
	if (!core || !set || !set->addrs) {
		return;
	}
	for (i = 0; i < set->count; i++) {
		r_bp_del (core->dbg->bp, set->addrs[i]);
	}
	free (set->addrs);
	set->addrs = NULL;
	set->count = 0;
}

static bool replay_temp_bps_add(RCore *core, ReplayTempBpSet *set, ut64 addr) {
	ut64 *next;
	if (!core || !set || !addr) {
		return false;
	}
	if (r_bp_get_in (core->dbg->bp, addr, R_BP_PROT_EXEC)) {
		return true;
	}
	if (!r_bp_add_sw (core->dbg->bp, addr, core->dbg->options.bpsize, R_BP_PROT_EXEC)) {
		return false;
	}
	next = realloc (set->addrs, (set->count + 1) * sizeof (ut64));
	if (!next) {
		r_bp_del (core->dbg->bp, addr);
		return false;
	}
	set->addrs = next;
	set->addrs[set->count++] = addr;
	return true;
}

static ReplaySearchStopKind replay_classify_stop(const ReplaySearchSpec *spec, const ReplayEvalContext *ctx) {
	if (replay_eval_predicates (spec->find_preds, spec->find_count, ctx)) {
		return REPLAY_SEARCH_STOP_FIND;
	}
	if (replay_eval_predicates (spec->avoid_preds, spec->avoid_count, ctx)) {
		return REPLAY_SEARCH_STOP_AVOID;
	}
	if (replay_eval_predicates (spec->frontier_preds, spec->frontier_count, ctx)) {
		return REPLAY_SEARCH_STOP_FRONTIER;
	}
	return REPLAY_SEARCH_STOP_OTHER;
}

static ReplaySearchStopKind replay_continue_to_any(RCore *core, const ReplaySearchSpec *spec, size_t depth, size_t input_len,
	ut64 *hit_addr, RDebugStateSnapshot **out_snapshot) {
	ReplayTempBpSet temps = {0};
	size_t i;
	ut64 pc = 0;
	RDebugStateSnapshot *snapshot = NULL;
	ReplayEvalContext eval_ctx;

	R_RETURN_VAL_IF_FAIL (core && core->dbg && spec && hit_addr && out_snapshot, REPLAY_SEARCH_STOP_NONE);
	*hit_addr = 0;
	*out_snapshot = NULL;

	snapshot = replay_collect_snapshot (core, spec);
	if (!snapshot) {
		goto cleanup;
	}
	eval_ctx.snapshot = snapshot;
	eval_ctx.depth = depth;
	eval_ctx.input_len = input_len;
	eval_ctx.big_endian = spec->big_endian;
	pc = snapshot->pc;
	if (replay_eval_predicates (spec->find_preds, spec->find_count, &eval_ctx)) {
		*hit_addr = pc;
		*out_snapshot = snapshot;
		return REPLAY_SEARCH_STOP_FIND;
	}
	if (replay_eval_predicates (spec->avoid_preds, spec->avoid_count, &eval_ctx)) {
		*hit_addr = pc;
		*out_snapshot = snapshot;
		return REPLAY_SEARCH_STOP_AVOID;
	}
	if (replay_addr_list_contains (spec->frontier_stop_addrs, spec->frontier_stop_count, pc)) {
		r_debug_state_snapshot_free (snapshot);
		snapshot = NULL;
		if (r_debug_step (core->dbg, 1) != 1) {
			goto cleanup;
		}
		snapshot = replay_collect_snapshot (core, spec);
		if (!snapshot) {
			goto cleanup;
		}
		pc = snapshot->pc;
	}

	for (i = 0; i < spec->stop_count; i++) {
		if (spec->stop_addrs[i] != pc && !replay_temp_bps_add (core, &temps, spec->stop_addrs[i])) {
			goto cleanup;
		}
	}
	r_debug_state_snapshot_free (snapshot);
	snapshot = NULL;
	if (r_debug_continue (core->dbg) <= 0) {
		goto cleanup;
	}
	snapshot = replay_collect_snapshot (core, spec);
	if (!snapshot) {
		goto cleanup;
	}
	eval_ctx.snapshot = snapshot;
	eval_ctx.depth = depth;
	eval_ctx.input_len = input_len;
	eval_ctx.big_endian = spec->big_endian;
	*hit_addr = snapshot->pc;
	*out_snapshot = snapshot;
	snapshot = NULL;
	replay_temp_bps_fini (core, &temps);
	return replay_classify_stop (spec, &eval_ctx);

cleanup:
	replay_temp_bps_fini (core, &temps);
	r_debug_state_snapshot_free (snapshot);
	return REPLAY_SEARCH_STOP_NONE;
}

static int replay_search_node_cmp(const ReplaySearchSpec *spec, const ReplaySearchNode *na, const ReplaySearchNode *nb) {
	if (na->score != nb->score) {
		if (spec->score_order == REPLAY_SCORE_MAX) {
			return (na->score < nb->score) - (na->score > nb->score);
		}
		return (na->score > nb->score) - (na->score < nb->score);
	}
	if (na->input_len != nb->input_len) {
		return (na->input_len > nb->input_len) - (na->input_len < nb->input_len);
	}
	if (!na->input || !nb->input) {
		return (!na->input && nb->input) ? -1 : (na->input && !nb->input);
	}
	return strcmp (na->input, nb->input);
}

static void replay_search_sort_nodes(const ReplaySearchSpec *spec, ReplaySearchNode **nodes, size_t count) {
	size_t i;
	size_t j;
	for (i = 1; i < count; i++) {
		ReplaySearchNode *key = nodes[i];
		j = i;
		while (j > 0 && replay_search_node_cmp (spec, nodes[j - 1], key) > 0) {
			nodes[j] = nodes[j - 1];
			j--;
		}
		nodes[j] = key;
	}
}

static char *replay_search_run_json(RCore *core, const ReplaySearchSpec *spec) {
	RList *active = NULL;
	RList *next = NULL;
	RList *found = NULL;
	ReplaySearchNode *seed = NULL;
	size_t explored = 0;
	size_t depth;
	char *out = NULL;

	R_RETURN_VAL_IF_FAIL (core && core->dbg && core->dbg->session && spec && spec->score_expr, NULL);

	active = r_list_newf ((RListFree)replay_search_node_free);
	next = r_list_newf ((RListFree)replay_search_node_free);
	found = r_list_newf ((RListFree)replay_search_match_free);
	if (!active || !next || !found) {
		goto cleanup;
	}
	seed = R_NEW0 (ReplaySearchNode);
	if (!seed) {
		goto cleanup;
	}
	seed->checkpoint_id = spec->seed_checkpoint;
	seed->input = strdup ("");
	if (!seed->input) {
		replay_search_node_free (seed);
		goto cleanup;
	}
	r_list_append (active, seed);

	for (depth = 0; depth < spec->max_depth && !r_list_empty (active) && r_list_empty (found); depth++) {
		RListIter *iter;
		ReplaySearchNode *node;
		r_list_free (next);
		next = r_list_newf ((RListFree)replay_search_node_free);
		if (!next) {
			goto cleanup;
		}
		r_list_foreach (active, iter, node) {
			const char *alphabet = spec->alphabet;
			while (alphabet && *alphabet) {
				ut64 child_checkpoint = 0;
				ut64 frontier_checkpoint = 0;
				ut64 hit_addr = 0;
				ReplaySearchStopKind stop;
				RDebugStateSnapshot *snapshot = NULL;
				ReplayEvalContext eval_ctx;
				char *next_input = NULL;
				char *snapshot_json = NULL;
				st64 score = 0;

				if (!r_debug_session_restore_checkpoint (core->dbg, node->checkpoint_id)) {
					alphabet++;
					continue;
				}
				child_checkpoint = r_debug_checkpoint_create (core->dbg, node->checkpoint_id, NULL);
				if (!child_checkpoint) {
					alphabet++;
					continue;
				}
				if (!r_debug_session_checkpoint_replay_append (core->dbg->session, child_checkpoint,
						spec->replay_fd, (const ut8 *)alphabet, 1, NULL)) {
					alphabet++;
					continue;
				}
				if (!r_debug_session_restore_checkpoint (core->dbg, child_checkpoint)) {
					alphabet++;
					continue;
				}
				if (!r_debug_session_checkpoint_replay_apply (core->dbg, child_checkpoint, spec->replay_fd)) {
					alphabet++;
					continue;
				}

				explored++;
				stop = replay_continue_to_any (core, spec, depth + 1, node->input_len + 1, &hit_addr, &snapshot);
				next_input = replay_input_append_char (node->input, node->input_len, *alphabet);
				if (!next_input || !snapshot) {
					free (next_input);
					r_debug_state_snapshot_free (snapshot);
					alphabet++;
					continue;
				}
				eval_ctx.snapshot = snapshot;
				eval_ctx.depth = depth + 1;
				eval_ctx.input_len = node->input_len + 1;
				eval_ctx.big_endian = spec->big_endian;
				if (!replay_eval_score (spec, &eval_ctx, &score)) {
					free (next_input);
					r_debug_state_snapshot_free (snapshot);
					alphabet++;
					continue;
				}
				snapshot_json = r_debug_state_snapshot_to_json (snapshot);
				r_debug_state_snapshot_free (snapshot);
				snapshot = NULL;

				if (stop == REPLAY_SEARCH_STOP_FIND) {
					ReplaySearchMatch *match = R_NEW0 (ReplaySearchMatch);
					if (match) {
						match->checkpoint_id = child_checkpoint;
						match->input = next_input;
						match->input_len = node->input_len + 1;
						match->hit_addr = hit_addr;
						match->score = score;
						match->snapshot_json = snapshot_json;
						r_list_append (found, match);
						next_input = NULL;
						snapshot_json = NULL;
					}
				} else if (stop == REPLAY_SEARCH_STOP_FRONTIER) {
					ReplaySearchNode *frontier = R_NEW0 (ReplaySearchNode);
					frontier_checkpoint = r_debug_checkpoint_create (core->dbg, child_checkpoint, NULL);
					if (frontier && frontier_checkpoint) {
						frontier->checkpoint_id = frontier_checkpoint;
						frontier->input = next_input;
						frontier->input_len = node->input_len + 1;
						frontier->score = score;
						frontier->snapshot_json = snapshot_json;
						r_list_append (next, frontier);
						next_input = NULL;
						snapshot_json = NULL;
					} else {
						replay_search_node_free (frontier);
					}
				}
				free (snapshot_json);
				free (next_input);
				if (!r_list_empty (found)) {
					break;
				}
				alphabet++;
			}
			if (!r_list_empty (found)) {
				break;
			}
		}

		{
			int next_len = r_list_length (next);
			if (spec->beam_width && next_len > 0 && (size_t)next_len > spec->beam_width) {
				size_t count = (size_t)next_len;
				size_t i;
				ReplaySearchNode **nodes = calloc (count, sizeof (ReplaySearchNode *));
				if (!nodes) {
					goto cleanup;
				}
				i = 0;
				{
					RListIter *iter;
					ReplaySearchNode *node;
					r_list_foreach (next, iter, node) {
						nodes[i++] = node;
					}
				}
				replay_search_sort_nodes (spec, nodes, count);
				for (i = spec->beam_width; i < count; i++) {
					r_list_delete_data (next, nodes[i]);
				}
				free (nodes);
			}
		}

		{
			RList *tmp = active;
			active = next;
			next = tmp;
		}
	}

	{
		PJ *pj = pj_new ();
		RListIter *iter;
		ReplaySearchMatch *match;
		ReplaySearchNode *node;
		if (!pj) {
			goto cleanup;
		}
		pj_o (pj);
		pj_kn (pj, "seed_checkpoint", spec->seed_checkpoint);
		pj_kn (pj, "replay_fd", spec->replay_fd);
		pj_ks (pj, "alphabet", spec->alphabet);
		pj_kn (pj, "max_depth", spec->max_depth);
		pj_kn (pj, "beam_width", spec->beam_width);
		pj_ks (pj, "score_order", spec->score_order == REPLAY_SCORE_MAX? "max": "min");
		pj_kn (pj, "explored_branches", explored);
		pj_kb (pj, "found", !r_list_empty (found));
		pj_ka (pj, "matches");
		r_list_foreach (found, iter, match) {
			pj_o (pj);
			pj_kn (pj, "checkpoint", match->checkpoint_id);
			pj_ks (pj, "input", match->input ? match->input : "");
			pj_kn (pj, "hit", match->hit_addr);
			pj_ki (pj, "score", match->score);
			if (match->snapshot_json) {
				pj_k (pj, "snapshot");
				pj_raw (pj, match->snapshot_json);
			} else {
				pj_knull (pj, "snapshot");
			}
			pj_end (pj);
		}
		pj_end (pj);
		pj_ka (pj, "active");
		r_list_foreach (active, iter, node) {
			pj_o (pj);
			pj_kn (pj, "checkpoint", node->checkpoint_id);
			pj_ks (pj, "input", node->input ? node->input : "");
			pj_ki (pj, "score", node->score);
			if (node->snapshot_json) {
				pj_k (pj, "snapshot");
				pj_raw (pj, node->snapshot_json);
			} else {
				pj_knull (pj, "snapshot");
			}
			pj_end (pj);
		}
		pj_end (pj);
		pj_end (pj);
		out = strdup (pj_string (pj));
		pj_free (pj);
	}

cleanup:
	r_list_free (active);
	r_list_free (next);
	r_list_free (found);
	return out;
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

static R2SleighInterprocSessionPlan sleigh_interproc_session_plan_for_function(RAnal *anal, const RAnalFunction *fcn, unsigned int purpose) {
	ut32 cost;
	int bb_count;
	if (!fcn) {
		return sleigh_v2_query_interproc_session (
			anal? (unsigned int)anal->plugin_analysis_depth: 0,
			purpose,
			SIZE_MAX,
			UINT_MAX);
	}
	bb_count = function_bb_count (fcn);
	if (bb_count < 0) {
		return sleigh_v2_query_interproc_session (
			anal? (unsigned int)anal->plugin_analysis_depth: 0,
			purpose,
			SIZE_MAX,
			UINT_MAX);
	}
	cost = r_anal_function_cost ((RAnalFunction *)fcn);
	return sleigh_v2_query_interproc_session (
		anal? (unsigned int)anal->plugin_analysis_depth: 0,
		purpose,
		(size_t)bb_count,
		(unsigned int)cost);
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

static ut64 resolve_local_direct_jump_thunk_target(RAnal *anal, ut64 addr) {
	ut64 cur = addr;
	size_t depth = 0;

	while (anal && cur != UT64_MAX && cur && depth++ < 4) {
		ut8 buf[16] = {0};
		RAnalOp op = {0};
		int size;

		if (!anal->iob.read_at || anal->iob.read_at (anal->iob.io, cur, buf, sizeof (buf)) <= 0) {
			break;
		}
		size = r_anal_op (anal, &op, cur, buf, sizeof (buf), R_ARCH_OP_MASK_BASIC);
		if (size <= 0) {
			r_anal_op_fini (&op);
			break;
		}
		if ((op.type != R_ANAL_OP_TYPE_JMP && op.type != R_ANAL_OP_TYPE_UJMP)
			|| op.jump == UT64_MAX || !op.jump || op.jump == cur || op.size > 8) {
			r_anal_op_fini (&op);
			break;
		}
		cur = op.jump;
		r_anal_op_fini (&op);
	}

	return cur;
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

static void sym_scope_symbol_snapshot_fini(SymScopeSymbolSnapshot *snapshot) {
	size_t i;
	if (!snapshot) {
		return;
	}
	for (i = 0; i < snapshot->count; i++) {
		free (snapshot->owned_names[i]);
	}
	free (snapshot->owned_names);
	free (snapshot->symbols);
	memset (snapshot, 0, sizeof (*snapshot));
}

static bool sym_scope_symbol_snapshot_append(SymScopeSymbolSnapshot *snapshot, ut64 addr,
	const char *name, unsigned int linkage) {
	size_t i;
	size_t name_len;
	char *owned_name;
	if (!snapshot || !name || !*name
		|| (linkage != R2SLEIGH_INTERPROC_LINKAGE_UNKNOWN_V2
			&& linkage != R2SLEIGH_INTERPROC_LINKAGE_INTERNAL_V2
			&& linkage != R2SLEIGH_INTERPROC_LINKAGE_IMPORTED_V2)) {
		return false;
	}
	name_len = strlen (name);
	if (name_len > R2SLEIGH_MAX_STRING_BYTES_V2
		|| snapshot->total_name_bytes > R2SLEIGH_MAX_AGGREGATE_STRING_BYTES_V2 - name_len) {
		return false;
	}
	for (i = 0; i < snapshot->count; i++) {
		const R2SleighScopeSymbolV2 *existing = &snapshot->symbols[i];
		if (existing->addr != addr) {
			continue;
		}
		return existing->linkage == linkage
			&& existing->name.len == name_len
			&& !memcmp (existing->name.data, name, name_len);
	}
	if (snapshot->count >= R2SLEIGH_MAX_SCOPE_SYMBOLS_V2) {
		return false;
	}
	if (!snapshot->symbols) {
		snapshot->symbols = calloc (R2SLEIGH_MAX_SCOPE_SYMBOLS_V2, sizeof (*snapshot->symbols));
		snapshot->owned_names = calloc (R2SLEIGH_MAX_SCOPE_SYMBOLS_V2, sizeof (*snapshot->owned_names));
		if (!snapshot->symbols || !snapshot->owned_names) {
			sym_scope_symbol_snapshot_fini (snapshot);
			return false;
		}
	}
	owned_name = strdup (name);
	if (!owned_name) {
		return false;
	}
	R2SleighScopeSymbolV2 *symbol = &snapshot->symbols[snapshot->count];
	symbol->abi_version = R2SLEIGH_ABI_V2;
	symbol->struct_size = sizeof (*symbol);
	symbol->schema_version = R2SLEIGH_SCOPE_SYMBOL_SCHEMA_V2;
	symbol->addr = addr;
	symbol->name.data = (const uint8_t *)owned_name;
	symbol->name.len = name_len;
	symbol->linkage = linkage;
	snapshot->owned_names[snapshot->count] = owned_name;
	snapshot->count++;
	snapshot->total_name_bytes += name_len;
	return true;
}

static bool build_sym_scope_symbol_snapshot(RCore *core, RAnal *anal, R2ILContext *ctx,
	const SymFunctionScope *scope, SymScopeSymbolSnapshot *snapshot) {
	size_t i;
	if (!core || !anal || !ctx || !scope || !scope->functions || !scope->count || !snapshot) {
		return false;
	}
	memset (snapshot, 0, sizeof (*snapshot));
	for (i = 0; i < scope->count; i++) {
		const R2ILFunctionBlocks *function = &scope->functions[i];
		const BlockArray *blocks = &scope->owned_blocks[i];
		size_t direct_target_count = 0;
		ut64 *direct_targets = NULL;
		size_t j;
		if (function->name && *function->name
			&& !sym_scope_symbol_snapshot_append (snapshot, function->entry_addr,
				function->name, resolve_interproc_seed_linkage (core, anal, function->entry_addr))) {
			goto fail;
		}
		direct_targets = collect_type_interproc_direct_targets_from_blocks (
			ctx,
			blocks,
			function->entry_addr,
			function->name,
			&direct_target_count
		);
		for (j = 0; j < direct_target_count; j++) {
			char *target_name = resolve_interproc_seed_name (core, anal, direct_targets[j]);
			if (target_name && *target_name
				&& !sym_scope_symbol_snapshot_append (snapshot, direct_targets[j], target_name,
					resolve_interproc_seed_linkage (core, anal, direct_targets[j]))) {
				free (target_name);
				free (direct_targets);
				goto fail;
			}
			free (target_name);
		}
		free (direct_targets);
	}
	return true;

fail:
	sym_scope_symbol_snapshot_fini (snapshot);
	return false;
}

static bool sleigh_sym_merge_enabled(RCore *core) {
	return core && core->config && r_config_get_b (core->config, "anal.sleigh.sym.merge");
}

static void sleigh_sym_merge_set_enabled(RCore *core, bool enabled) {
	if (core && core->config) {
		r_config_set_b (core->config, "anal.sleigh.sym.merge", enabled);
	}
}

static uint32_t sleigh_v2_scope_render_for_scope(uint32_t kind, RCore *core, RAnal *anal,
	const R2ILContext *context, const SymFunctionScope *scope, uint64_t entry_addr,
	uint64_t target_addr, const R2SymReplaySeed *replay_seed, const char *argument,
	const char *external_context, char **text) {
	SymScopeSymbolSnapshot snapshot = {0};
	if (text) {
		*text = NULL;
	}
	if (!build_sym_scope_symbol_snapshot (core, anal, (R2ILContext *)context, scope, &snapshot)) {
		return R2SLEIGH_STATUS_INVALID_ARGUMENT_V2;
	}
	uint32_t status = sleigh_v2_scope_render (kind, context, scope->functions, scope->count,
		entry_addr, target_addr, replay_seed, argument, external_context,
		snapshot.symbols, snapshot.count, sleigh_sym_merge_enabled (core), text);
	sym_scope_symbol_snapshot_fini (&snapshot);
	return status;
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
		ctx, blocks, 1, 0, NULL, NULL, 0, &result, &view)
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
			sleigh_artifact_revision_cb, &revision)
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
		plan->scope_id, NULL, NULL, 0, &result, &view) != R2SLEIGH_STATUS_OK_V2) {
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

static bool sleigh_engine_function_preflight(const RAnalFunction *fcn, const char *operation) {
	if (!fcn || !fcn->bbs) {
		R_LOG_ERROR ("r2sleigh: %s preflight refused a function without a CFG",
			operation? operation: "engine");
		return false;
	}
	const int listed_blocks = r_list_length (fcn->bbs);
	if (listed_blocks <= 0) {
		R_LOG_ERROR ("r2sleigh: %s preflight refused function 0x%"PFMT64x" without CFG blocks",
			operation? operation: "engine", fcn->addr);
		return false;
	}
	if ((size_t)listed_blocks > (size_t)R2SLEIGH_MAX_FUNCTION_BLOCKS_V2) {
		R_LOG_ERROR ("r2sleigh: %s preflight refused function 0x%"PFMT64x": %d CFG blocks exceed cap %u",
			operation? operation: "engine", fcn->addr, listed_blocks,
			(unsigned int)R2SLEIGH_MAX_FUNCTION_BLOCKS_V2);
		return false;
	}

	size_t total_bytes = 0;
	RListIter *iter;
	RAnalBlock *bb;
	r_list_foreach (fcn->bbs, iter, bb) {
		if (!bb || !bb->size) {
			R_LOG_ERROR ("r2sleigh: %s preflight refused function 0x%"PFMT64x": CFG contains an empty block",
				operation? operation: "engine", fcn->addr);
			return false;
		}
		if ((ut64)bb->size > (ut64)SLEIGH_LIFT_BLOCK_MAX_ALLOC) {
			R_LOG_ERROR ("r2sleigh: %s preflight refused block 0x%"PFMT64x": %"PFMT64u" bytes exceed per-block cap %u",
				operation? operation: "engine", bb->addr, (ut64)bb->size,
				(unsigned int)SLEIGH_LIFT_BLOCK_MAX_ALLOC);
			return false;
		}
		if ((ut64)bb->size > (ut64)(R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2 - total_bytes)) {
			R_LOG_ERROR ("r2sleigh: %s preflight refused function 0x%"PFMT64x": aggregate CFG bytes exceed cap %u",
				operation? operation: "engine", fcn->addr,
				(unsigned int)R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2);
			return false;
		}
		total_bytes += (size_t)bb->size;
	}
	return true;
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
	out->quality.expected_blocks = fcn->bbs? (size_t)r_list_length (fcn->bbs): 0;

	r_list_foreach (fcn->bbs, iter, bb) {
		ut8 *buf = NULL;
		size_t lift_size = 0;
		size_t logical_size = 0;
		size_t to_read = 0;

		if (!read_block_bytes_for_lifting (anal, bb, &buf, &to_read, &lift_size, &logical_size)) {
			R_LOG_ERROR ("r2sleigh: failed to read block at 0x%"PFMT64x, bb->addr);
			out->quality.read_failures++;
			continue;
		}
		if (lift_size < logical_size) {
			out->quality.truncated_blocks++;
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
				out->quality.invalid_blocks++;
				continue;
			}
			size_t block_ops = 0;
			if (sleigh_v2_block_op_count (block, &block_ops) != R2SLEIGH_STATUS_OK_V2) {
				(void)sleigh_v2_block_release (&block);
				free (buf);
				out->quality.invalid_blocks++;
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
				out->quality.invalid_blocks++;
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
		} else {
			out->quality.null_lift_failures++;
		}
		free (buf);
	}
	out->quality.lifted_blocks = out->count;

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
	uint32_t reset_status = sleigh_v2_engine_cache_reset ();
	if (reset_status != R2SLEIGH_STATUS_OK_V2) {
		R_LOG_ERROR ("r2sleigh: engine cache reset failed (%u)", reset_status);
	}
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
	if (!elapsed_us) {
		return;
	}
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
	char *engine_cache = NULL;
	(void)sleigh_v2_analysis_render (R2SLEIGH_ANALYSIS_ENGINE_CACHE_STATS_V2,
		NULL, NULL, 0, 0, NULL, &engine_cache);
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
	if (engine_cache && *engine_cache) {
		pj_k (pj, "engine_cache");
		pj_raw (pj, engine_cache);
	}
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
	free (engine_cache);
	return pj_drain (pj);
}

static void configure_context_runtime_options(RAnal *anal, R2ILContext *ctx) {
	if (!ctx) {
		return;
	}
	(void)sleigh_v2_context_set_semantic_metadata (ctx, !sleigh_mode_is_fast (anal));
}

R2ILContext *get_context(RAnal *anal) {
	if (!anal || !anal->config || !anal->config->arch[0]) {
		return NULL;
	}
	const char *arch = anal->config->arch;
	int bits = anal->config->bits;

	/* Determine sleigh arch string */
	const char *sleigh_arch_str;
	if (sleigh_arch_override) {
		sleigh_arch_str = sleigh_arch_override;
	} else if (!strcmp (arch, "x86")) {
		sleigh_arch_str = (bits == 64) ? "x86-64" : "x86";
	} else if (!strcmp (arch, "arm")) {
		sleigh_arch_str = (bits == 64) ? "arm64" : "arm";
	} else if (!strcmp (arch, "arm64") || !strcmp (arch, "aarch64")) {
		sleigh_arch_str = "arm64";
	} else if (!strcmp (arch, "riscv")) {
		sleigh_arch_str = (bits >= 64) ? "riscv64" : "riscv32";
	} else if (!strcmp (arch, "riscv32") || !strcmp (arch, "rv32")) {
		sleigh_arch_str = "riscv32";
	} else if (!strcmp (arch, "riscv64") || !strcmp (arch, "rv64")) {
		sleigh_arch_str = "riscv64";
	} else if (!strcmp (arch, "mips") || !strcmp (arch, "mips32")
			|| !strcmp (arch, "mips32be") || !strcmp (arch, "mipsbe")
			|| !strcmp (arch, "mipseb") || !strcmp (arch, "mipsel")
			|| !strcmp (arch, "mips32le") || !strcmp (arch, "mips32el")
			|| !strcmp (arch, "mips64") || !strcmp (arch, "mips64be")
			|| !strcmp (arch, "mips64le") || !strcmp (arch, "mips64el")) {
		bool is64 = bits >= 64
			|| !strcmp (arch, "mips64")
			|| !strcmp (arch, "mips64be")
			|| !strcmp (arch, "mips64le")
			|| !strcmp (arch, "mips64el");
		bool big_endian = R_ARCH_CONFIG_IS_BIG_ENDIAN (anal->config);
		if (!strcmp (arch, "mipsel") || !strcmp (arch, "mips32le")
				|| !strcmp (arch, "mips32el")
				|| !strcmp (arch, "mips64le")
				|| !strcmp (arch, "mips64el")) {
			big_endian = false;
		} else if (!strcmp (arch, "mips32be") || !strcmp (arch, "mipsbe")
				|| !strcmp (arch, "mipseb") || !strcmp (arch, "mips64be")) {
			big_endian = true;
		}
		sleigh_arch_str = is64
			? (big_endian ? "mips64be" : "mips64le")
			: (big_endian ? "mips32be" : "mips32le");
	} else {
		return NULL; /* unsupported arch */
	}

	/* Check if we need to reinitialize */
	if (sleigh_ctx && sleigh_arch && !strcmp (sleigh_arch, sleigh_arch_str)) {
		configure_context_runtime_options (anal, sleigh_ctx);
		return sleigh_ctx;
	}

	/* Free old context */
	if (sleigh_ctx) {
		uint32_t free_status = sleigh_v2_context_free (sleigh_ctx);
		if (free_status != R2SLEIGH_STATUS_OK_V2) {
			R_LOG_ERROR ("r2sleigh: refusing architecture reload because context free failed (%u)", free_status);
			return NULL;
		}
		sleigh_ctx = NULL;
	}
	free (sleigh_arch);
	sleigh_arch = NULL;
	sym_state_cache_clear ();

	/* Initialize new context */
	uint32_t status = sleigh_v2_context_create (sleigh_arch_str, &sleigh_ctx);
	if (status != R2SLEIGH_STATUS_OK_V2 || !sleigh_ctx) {
		/* Optional-arch builds are expected to miss some backends; stay silent
		 * so unsupported architectures fall back to other anal plugins. */
		R_LOG_DEBUG ("r2sleigh: backend unavailable for %s", sleigh_arch_str);
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
		uint32_t free_status = sleigh_v2_context_free (sleigh_ctx);
		if (free_status == R2SLEIGH_STATUS_OK_V2) {
			sleigh_ctx = NULL;
		} else {
			R_LOG_ERROR ("r2sleigh: retaining failed context handle (%u)", free_status);
		}
		return NULL;
	}

	sleigh_arch = strdup (sleigh_arch_str);

	/* Set register profile from Sleigh definitions */
	char *profile = NULL;
	(void)sleigh_v2_context_reg_profile (sleigh_ctx, &profile);
	if (profile) {
		r_anal_set_reg_profile (anal, profile);
		free (profile);
	}

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
	RCore *core = anal? anal->coreb.core: NULL;
	if (core && core->config) {
		r_config_set_b (core->config, "anal.sleigh.sym.merge",
			r_config_get_b (core->config, "anal.sleigh.sym.merge"));
	}
	/* Prime context early so register aliases are available before aa/aaa passes. */
	(void)get_context (anal);
	return true;
}

static bool sleigh_fini(RAnal *anal) {
	(void)anal;
	if (!sleigh_v2_planner_result_retry_pending ()) {
		return false;
	}
	if (sleigh_ctx) {
		uint32_t free_status = sleigh_v2_context_free (sleigh_ctx);
		if (free_status != R2SLEIGH_STATUS_OK_V2) {
			R_LOG_ERROR ("r2sleigh: retaining context after free failure (%u)", free_status);
			return false;
		}
		sleigh_ctx = NULL;
	}
	free (sleigh_arch);
	sleigh_arch = NULL;
	sym_state_cache_clear ();
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
		|| cmd_matches_exact_or_arg (cmd, "sla.types")
		|| cmd_matches_exact_or_arg (cmd, "sla.profilej")
		|| cmd_matches_exact_or_arg (cmd, "sla.assumptions-")
		|| cmd_matches_exact_or_arg (cmd, "sla.assumptions")
		|| cmd_matches_exact_or_arg (cmd, "sla.assumej")
		|| cmd_matches_exact_or_arg (cmd, "sla.slice")
		|| cmd_matches_exact_or_arg (cmd, "sla.sym.merge")
		|| cmd_matches_exact_or_arg (cmd, "sla.sym.paths")
		|| cmd_matches_exact_or_arg (cmd, "sla.sym");
}

static bool sleigh_direct_sym_debug_only_command(const char *cmd) {
	if (!cmd) {
		return false;
	}
	return cmd_matches_exact_or_arg (cmd, "sym.runj")
		|| cmd_matches_exact_or_arg (cmd, "sym.replayj")
		|| cmd_matches_exact_or_arg (cmd, "sym.explore.replayj")
		|| cmd_matches_exact_or_arg (cmd, "sym.solve.replayj")
		|| cmd_matches_exact_or_arg (cmd, "sym.explore.state")
		|| cmd_matches_exact_or_arg (cmd, "sym.solve.state");
}

static char *sleigh_decompile_execute(RAnal *anal, RAnalFunction *fcn, bool json_projection);


static char *sleigh_decompile_execute(RAnal *anal, RAnalFunction *fcn, bool json_projection) {
	(void)anal;
	(void)fcn;
	R_LOG_ERROR ("r2sleigh: direct decompile commands cannot construct source authority; use radare2's borrowed snapshot decompiler provider");
	return json_projection
		? sleigh_engine_v2_error_json ("borrowed_snapshot_required",
			R2SLEIGH_STATUS_UNSUPPORTED_V2,
			"decompilation requires the ABI-138 borrowed snapshot provider")
		: NULL;
}

static RCodeMeta *sleigh_decompile(const RAnalFunctionSnapshot *snapshot) {
	R_RETURN_VAL_IF_FAIL (snapshot, NULL);
	const R2SleighRadareSnapshotInputV2 source = {
		.struct_size = sizeof (source),
		.abi_version = R2SLEIGH_RADARE_ABI_V2,
		.snapshot_schema_version = R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2,
		.accessor_schema_version = R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2,
		.snapshot = snapshot,
		.accessors = &sleigh_radare_accessors,
	};
	const R2SleighEngineRequestPayloadV2 payload = {
		.abi_version = R2SLEIGH_ABI_V2,
		.struct_size = sizeof (payload),
		.timeout_us = 0,
		.radare_snapshot = &source,
	};
	char *result = sleigh_engine_execute_v2 (
		R2SLEIGH_REQUEST_DECOMPILE_V2,
		R2SLEIGH_CAP_DECOMPILE_V2 | R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2,
		&payload);
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
	bool is_sym_debug_ns = false;
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
		is_sym_debug_ns = true;
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

	if (!is_sla_debug_ns) {
		if (sleigh_direct_sla_debug_only_command (cmd)) {
			return strdup ("");
		}
	}
	if (!is_sym_debug_ns) {
		if (sleigh_direct_sym_debug_only_command (cmd)) {
			return strdup ("");
		}
	}

	if (cmd[3] == '?') {
		if (cons) {
			r_cons_println (cons, "| a:sla        - Show r2sleigh status");
			r_cons_println (cons, "| pdd - decompile through the borrowed-snapshot provider");
			r_cons_println (cons, "| a:sla.dec / a:sla.decj - unavailable outside that provider");
			r_cons_println (cons, "| a:sym.explore <target> - Explore symbolic paths reaching target");
			r_cons_println (cons, "| a:sym.solve <target> - Solve concrete input for target reachability");
			r_cons_println (cons, "| a:sym.state  - Show last symbolic explore/solve cached result");
		}
		return strdup("");
	}

	if (is_sym_ns && !strcmp (cmd, "sym.state")) {
		char *state_json = sym_state_cache_to_json ();
		if (cons && state_json) {
			r_cons_printf (cons, "%s\n", state_json);
		}
		free (state_json);
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

	if (is_sym_ns && !strncmp (cmd, "sym.runj", 8)) {
		const char *arg = skip_cmd_spaces (cmd + 8);
		R2ILContext *ctx;
		RAnalFunction *fcn;
		SymFunctionScope scope;
		char *spec_json = NULL;
		char *external_context_json = NULL;
		char *result = NULL;

		if (!arg || !*arg) {
			if (cons) {
				r_cons_println (cons, "Usage: a:sym.runj <json-spec>");
			}
			return strdup("");
		}

		ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}
		fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}
		if (!build_symbolic_function_scope (anal, fcn, ctx, &scope)) {
			R_LOG_ERROR ("r2sleigh: failed to build symbolic function scope");
			return strdup("");
		}
		external_context_json = sleigh_collect_sym_assumptions_json (anal, fcn);

		spec_json = strdup (arg);
		if (!spec_json) {
			free (external_context_json);
			sym_function_scope_free (&scope);
			return strdup("");
		}
		r_str_unescape (spec_json);
		(void)sleigh_v2_scope_render_for_scope (R2SLEIGH_SCOPE_RUN_SPEC_V2,
			core, anal, ctx, &scope, fcn->addr, 0, NULL,
			spec_json, external_context_json, &result);
		free (spec_json);
		free (external_context_json);
		if (!result) {
			result = strdup ("{\"error\":\"symbolic execution failed\"}");
		}

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}
		if (result && !sym_result_has_error (result)) {
			sym_state_cache_update ("runj", fcn->addr, fcn->addr, 0, result);
		}
		free (result);
		sym_function_scope_free (&scope);
		return strdup("");
	}

	if (is_sym_ns && !strncmp (cmd, "sym.replayj", 11)) {
		const char *arg = skip_cmd_spaces (cmd + 11);
		ReplaySearchSpec spec;
		char *result = NULL;

		if (!arg || !*arg) {
			if (cons) {
				r_cons_println (cons, "Usage: a:sym.replayj <json-spec>");
			}
			return strdup ("");
		}
		if (!core->dbg || !core->dbg->session) {
			R_LOG_ERROR ("r2sleigh: debug session with checkpoints is required");
			return strdup ("");
		}
		R_LOG_DEBUG ("r2sleigh replayj arg: %s", arg);
		if (!replay_search_spec_parse (core, arg, &spec)) {
			R_LOG_ERROR ("r2sleigh: invalid replay search spec");
			return strdup ("");
		}
		result = replay_search_run_json (core, &spec);
		replay_search_spec_fini (&spec);
		if (!result) {
			result = strdup ("{\"error\":\"replay search failed\"}");
		}
		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}
		if (result && !sym_result_has_error (result)) {
			sym_state_cache_update ("replayj", 0, 0, 0, result);
		}
		free (result);
		return strdup ("");
	}

	if (is_sym_ns && (!strncmp (cmd, "sym.explore.replayj", 19) || !strncmp (cmd, "sym.solve.replayj", 17))) {
		bool is_explore = r_str_startswith (cmd, "sym.explore.replayj");
		size_t prefix_len = is_explore ? 19 : 17;
		const char *arg = skip_cmd_spaces (cmd + prefix_len);
		ReplaySymSeedSpec spec;
		ut64 target = 0;
		R2ILContext *ctx;
		RAnalFunction *fcn;
		SymFunctionScope scope;
		char *spec_json = NULL;
		char *external_context_json = NULL;
		char *result = NULL;

		if (!arg || !*arg) {
			if (cons) {
				r_cons_println (cons, is_explore
					? "Usage: a:sym.explore.replayj <target_addr_expr> <json-spec>"
					: "Usage: a:sym.solve.replayj <target_addr_expr> <json-spec>");
			}
			return strdup ("");
		}
		if (!core->dbg || !core->dbg->session) {
			R_LOG_ERROR ("r2sleigh: debug session with checkpoints is required");
			return strdup ("");
		}
		if (!parse_replay_target_and_json (core, arg, &target, &spec_json)) {
			R_LOG_ERROR ("r2sleigh: invalid replay symbolic target/spec");
			if (cons) {
				r_cons_println (cons, is_explore
					? "Usage: a:sym.explore.replayj <target_addr_expr> <json-spec>"
					: "Usage: a:sym.solve.replayj <target_addr_expr> <json-spec>");
			}
			return strdup ("");
		}
			if (!replay_sym_seed_spec_parse (core, spec_json, &spec, true)) {
			R_LOG_ERROR ("r2sleigh: invalid replay symbolic seed spec");
			free (spec_json);
			return strdup ("");
		}
		free (spec_json);

		ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			replay_sym_seed_spec_fini (&spec);
			return strdup ("");
		}
		fcn = resolve_or_materialize_current_function (core, anal);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			replay_sym_seed_spec_fini (&spec);
			return strdup ("");
		}
		if (!build_symbolic_function_scope_with_target (anal, fcn, ctx, &scope, target)) {
			R_LOG_ERROR ("r2sleigh: failed to build symbolic function scope");
			replay_sym_seed_spec_fini (&spec);
			return strdup ("");
		}
		external_context_json = sleigh_collect_sym_assumptions_json (anal, fcn);

		result = replay_sym_query_run (core, ctx, &scope, fcn->addr, target, &spec, is_explore, external_context_json);
		free (external_context_json);
		if (!result) {
			result = strdup ("{\"error\":\"replay symbolic execution failed\"}");
		}

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}
		if (result && !sym_result_has_error (result)) {
			sym_state_cache_update (is_explore ? "explore.replayj" : "solve.replayj",
				fcn->addr, spec.entry_addr? spec.entry_addr: fcn->addr, target, result);
		}
		free (result);
		sym_function_scope_free (&scope);
		replay_sym_seed_spec_fini (&spec);
		return strdup ("");
	}

	if (is_sym_ns && (!strncmp (cmd, "sym.explore.state", 17) || !strncmp (cmd, "sym.solve.state", 15))) {
		bool is_explore = r_str_startswith (cmd, "sym.explore.state");
		size_t prefix_len = is_explore ? 17 : 15;
		const char *arg = skip_cmd_spaces (cmd + prefix_len);
		ReplaySymSeedSpec spec;
		ut64 target = 0;
		R2ILContext *ctx;
		RAnalFunction *fcn;
		SymFunctionScope scope;
		char *spec_json = NULL;
		char *external_context_json = NULL;
		char *result = NULL;

		if (!arg || !*arg) {
			if (cons) {
				r_cons_println (cons, is_explore
					? "Usage: a:sym.explore.state <target_addr_expr> [json-spec]"
					: "Usage: a:sym.solve.state <target_addr_expr> [json-spec]");
			}
			return strdup ("");
		}
		if (!core->dbg) {
			R_LOG_ERROR ("r2sleigh: active debugger state is required");
			return strdup ("");
		}
		if (!parse_target_and_optional_json (core, arg, &target, &spec_json)) {
			R_LOG_ERROR ("r2sleigh: invalid state symbolic target/spec");
			if (cons) {
				r_cons_println (cons, is_explore
					? "Usage: a:sym.explore.state <target_addr_expr> [json-spec]"
					: "Usage: a:sym.solve.state <target_addr_expr> [json-spec]");
			}
			return strdup ("");
		}
		if (!replay_sym_seed_spec_parse (core, spec_json, &spec, false)) {
			R_LOG_ERROR ("r2sleigh: invalid state symbolic seed spec");
			free (spec_json);
			return strdup ("");
		}
		free (spec_json);

		ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			replay_sym_seed_spec_fini (&spec);
			return strdup ("");
		}
		fcn = resolve_or_materialize_current_function (core, anal);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			replay_sym_seed_spec_fini (&spec);
			return strdup ("");
		}
		if (!build_symbolic_function_scope_with_target (anal, fcn, ctx, &scope, target)) {
			R_LOG_ERROR ("r2sleigh: failed to build symbolic function scope");
			replay_sym_seed_spec_fini (&spec);
			return strdup ("");
		}
		external_context_json = sleigh_collect_sym_assumptions_json (anal, fcn);

		result = replay_sym_query_run (core, ctx, &scope, fcn->addr, target, &spec, is_explore, external_context_json);
		free (external_context_json);
		if (!result) {
			result = strdup ("{\"error\":\"state symbolic execution failed\"}");
		}

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}
		if (result && !sym_result_has_error (result)) {
			sym_state_cache_update (is_explore ? "explore.state" : "solve.state",
				fcn->addr, spec.entry_addr? spec.entry_addr: core->addr, target, result);
		}
		free (result);
		sym_function_scope_free (&scope);
		replay_sym_seed_spec_fini (&spec);
		return strdup ("");
	}

	if (is_sym_ns && (!strncmp (cmd, "sym.explore", 11) || !strncmp (cmd, "sym.solve", 9))) {
		bool is_explore = r_str_startswith (cmd, "sym.explore");
		size_t prefix_len = is_explore ? 11 : 9;
		const char *arg = skip_cmd_spaces (cmd + prefix_len);
		ut64 target = 0;
		R2ILContext *ctx;
		RAnalFunction *fcn;
		SymFunctionScope scope;
		char *result = NULL;
		char *external_context_json = NULL;

		if (!arg || !*arg) {
			if (cons) {
				r_cons_println (cons, is_explore
					? "Usage: a:sym.explore <target_addr_expr>"
					: "Usage: a:sym.solve <target_addr_expr>");
			}
			return strdup("");
		}
		if (!parse_sym_target_expr (core, arg, &target)) {
			R_LOG_ERROR ("r2sleigh: invalid symbolic target expression: %s", arg);
			if (cons) {
				r_cons_println (cons, is_explore
					? "Usage: a:sym.explore <target_addr_expr>"
					: "Usage: a:sym.solve <target_addr_expr>");
			}
			return strdup("");
		}

		ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}
		fcn = resolve_or_materialize_current_function (core, anal);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}
		if (!build_symbolic_function_scope_with_target (anal, fcn, ctx, &scope, target)) {
			R_LOG_ERROR ("r2sleigh: failed to build symbolic function scope");
			return strdup("");
		}
		sleigh_debug_scope_log ("sym_query_stage scope_ready count=%zu", scope.count);
		sleigh_debug_scope_log ("sym_query_stage assumptions_begin");
		external_context_json = sleigh_collect_sym_assumptions_json (anal, fcn);
		sleigh_debug_scope_log ("sym_query_stage assumptions_done");

		sleigh_debug_scope_log ("sym_query_stage rust_call_begin target=0x%"PFMT64x, target);
		const uint32_t kind = is_explore
			? R2SLEIGH_SCOPE_EXPLORE_V2: R2SLEIGH_SCOPE_SOLVE_V2;
		(void)sleigh_v2_scope_render_for_scope (kind, core, anal, ctx, &scope,
			fcn->addr, target, NULL, NULL, external_context_json, &result);
		sleigh_debug_scope_log ("sym_query_stage rust_call_done");
		free (external_context_json);
		if (!result) {
			result = strdup ("{\"error\":\"symbolic execution failed\"}");
		}

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}
		if (result && !sym_result_has_error (result)) {
			sym_state_cache_update (is_explore ? "explore" : "solve", fcn->addr, fcn->addr, target, result);
		}

		free (result);
		sym_function_scope_free (&scope);
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
				if (sleigh_ctx) {
					uint32_t free_status = sleigh_v2_context_free (sleigh_ctx);
					if (free_status != R2SLEIGH_STATUS_OK_V2) {
						R_LOG_ERROR ("r2sleigh: architecture unchanged because context free failed (%u)", free_status);
						return strdup ("");
					}
					sleigh_ctx = NULL;
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
			if (cons) {
				if (name) {
					r_cons_printf (cons, "%s\n", name);
				} else {
					r_cons_println (cons, "none");
				}
			}
			free (name);
		}
		return strdup("");
	}

	if (!strcmp (cmd, "sla") || !strcmp (cmd, "sla.info")) {
		R2ILContext *ctx = get_context (anal);
		if (ctx) {
			char *name = NULL;
			(void)sleigh_v2_context_arch_name (ctx, &name);
			if (cons) {
				r_cons_printf (cons, "sla: loaded architecture '%s'\n", name ? name : "unknown");
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
			ctx, query_blocks, 1, 0, NULL, NULL, 0, &result, &view)
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

	if (!strncmp (cmd, "sla.types", 9) && (!cmd[9] || isspace ((unsigned char)cmd[9]))) {
		R_LOG_ERROR ("r2sleigh: sla.types cannot construct source authority from live mutable analysis state");
		return strdup ("");
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

	/* ========== Function-level commands ========== */

	if (!strncmp (cmd, "sla.sym.merge", 13)) {
		const char *arg = cmd + 13;
		if (*arg == ' ') {
			arg++;
			while (*arg == ' ') {
				arg++;
			}
		}

		if (*arg) {
			if (!strcmp (arg, "on") || !strcmp (arg, "1") || !strcmp (arg, "true")) {
				sleigh_sym_merge_set_enabled (core, true);
			} else if (!strcmp (arg, "off") || !strcmp (arg, "0") || !strcmp (arg, "false")) {
				sleigh_sym_merge_set_enabled (core, false);
			} else if (cons) {
				r_cons_println (cons, "Usage: a:sla.debug.sym.merge [on|off]");
				return strdup("");
			}
		} else {
			bool enabled = sleigh_sym_merge_enabled (core);
			sleigh_sym_merge_set_enabled (core, !enabled);
		}

		if (cons) {
			r_cons_printf (cons, "sym merge: %s\n", sleigh_sym_merge_enabled (core) ? "on" : "off");
		}
		return strdup("");
	}

	if ((!strncmp (cmd, "sla.sym.paths", 13) && (!cmd[13] || isspace ((unsigned char)cmd[13])))
		|| (!strncmp (cmd, "sla.sym", 7) && (!cmd[7] || isspace ((unsigned char)cmd[7])))) {
		R2ILContext *ctx = get_context (anal);
		bool is_paths_cmd = r_str_startswith (cmd, "sla.sym.paths");
		size_t prefix_len = is_paths_cmd ? 13: 7;
		const char *target_arg = skip_cmd_spaces (cmd + prefix_len);
		RAnalFunction *fcn;
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		fcn = (target_arg && *target_arg)
			? resolve_or_materialize_function_target (core, anal, target_arg)
			: resolve_or_materialize_current_function (core, anal);
		if (!fcn) {
			if (target_arg && *target_arg) {
				R_LOG_ERROR ("r2sleigh: function target not found: %s", target_arg);
			} else {
				R_LOG_ERROR ("r2sleigh: no function at current address");
			}
			return strdup("");
		}

		/* Lift root + reachable helper closure */
		SymFunctionScope scope;
		if (!build_symbolic_function_scope (anal, fcn, ctx, &scope)) {
			R_LOG_ERROR ("r2sleigh: failed to build symbolic function scope");
			return strdup("");
		}
		/* Call symbolic execution */
		char *result;
		char *external_context_json = sleigh_collect_sym_assumptions_json (anal, fcn);
		const uint32_t kind = is_paths_cmd
			? R2SLEIGH_SCOPE_PATHS_V2: R2SLEIGH_SCOPE_FUNCTION_V2;
		(void)sleigh_v2_scope_render_for_scope (kind, core, anal, ctx, &scope,
			fcn->addr, 0, NULL, NULL, external_context_json, &result);
		free (external_context_json);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		free (result);
		sym_function_scope_free (&scope);
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

/* Helper to free RAnalVarProt */
static void var_prot_free(void *ptr) {
	if (!ptr) {
		return;
	}
	RAnalVarProt *prot = (RAnalVarProt *)ptr;
	free (prot->name);
	free (prot->type);
	free (prot);
}

/* Called during variable recovery (afva) */
static RList *sleigh_recover_vars(RAnal *anal, RAnalFunction *fcn) {
	if (!fcn || !anal) {
		return NULL;
	}
	if (!auto_callback_allows_function (
		anal,
		fcn,
		R2SLEIGH_AUTO_CALLBACK_RECOVER_VARS_V2,
		"recover_vars")) {
		return NULL;
	}

	R2ILContext *ctx = get_context (anal);
	if (!ctx) {
		return NULL;
	}

	BlockArray blocks;
	if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
		return NULL;
	}

	R2SleighAnalysisResultV2 *typed_vars = NULL;
	R2SleighAnalysisResultViewV2 typed_vars_view = {0};
	(void)sleigh_v2_analysis_query (R2SLEIGH_QUERY_RECOVERED_VARS_V2,
		ctx, (const R2ILBlock *const *)blocks.blocks, blocks.count,
		fcn->addr, fcn->name, NULL, 0, &typed_vars, &typed_vars_view);
	size_t typed_count = typed_vars_view.primary_count;
	const R2SleighRecoveredVar *typed_items =
		(const R2SleighRecoveredVar *)typed_vars_view.primary;

	block_array_free (&blocks);

	if (!typed_items || typed_count == 0) {
		if (typed_vars) {
			(void)sleigh_v2_analysis_result_release (&typed_vars);
		}
		return NULL;
	}

	RList *vars = r_list_newf ((RListFree)var_prot_free);
	if (!vars) {
		(void)sleigh_v2_analysis_result_release (&typed_vars);
		return NULL;
	}

	for (size_t i = 0; i < typed_count; i++) {
		const R2SleighRecoveredVar *item = &typed_items[i];
		RAnalVarProt *prot = R_NEW0 (RAnalVarProt);
		if (!prot) {
			continue;
		}

		prot->name = strdup (item->name ? item->name : "");
		prot->type = strdup (item->type_name ? item->type_name : "int64_t");
		prot->delta = (st64)item->delta;
		prot->isarg = item->is_arg != 0;

		/* Parse kind: "r" = register, "s" = stack, "b" = bp-relative */
		if (item->kind) {
			switch (item->kind) {
			case 'r':
				/* Register-based argument: use r_reg_get to find index */
				if (item->reg && *item->reg && anal->reg) {
					/* Try uppercase version (Sleigh uses uppercase reg names) */
					char *upper_reg = strdup (item->reg);
					if (upper_reg) {
						for (char *p = upper_reg; *p; p++) {
							*p = toupper ((unsigned char)*p);
						}
					}
					RRegItem *ri = upper_reg
						? r_reg_get (anal->reg, upper_reg, R_REG_TYPE_GPR)
						: NULL;
					if (!ri) {
						/* Try original case as fallback */
						ri = r_reg_get (anal->reg, item->reg, R_REG_TYPE_GPR);
					}
					free (upper_reg);
					if (ri) {
						prot->kind = R_ANAL_VAR_KIND_REG;
						prot->delta = ri->index;
					} else {
						/* Reg lookup failed, skip this arg */
						free (prot->name);
						free (prot->type);
						free (prot);
						continue;
					}
				} else {
					/* No reg name provided, skip */
					free (prot->name);
					free (prot->type);
					free (prot);
					continue;
				}
				break;
			case 's':
				prot->kind = R_ANAL_VAR_KIND_SPV;
				break;
			case 'b':
				prot->kind = R_ANAL_VAR_KIND_BPV;
				break;
			default:
				prot->kind = R_ANAL_VAR_KIND_SPV;
			}
		}

		r_list_append (vars, prot);
	}

	(void)sleigh_v2_analysis_result_release (&typed_vars);

	if (r_list_empty (vars)) {
		r_list_free (vars);
		return NULL;
	}

	return vars;
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
		NULL, NULL, 0, &typed_refs, &typed_view);
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

static char *resolve_interproc_seed_name(RCore *core, RAnal *anal, ut64 addr) {
	const char *raw_name = NULL;
	RFlagItem *flag = NULL;
	RAnalFunction *target_fcn;

	if (core && core->flags) {
		flag = r_flag_get_at (core->flags, addr, false);
		if (flag && flag->name && *flag->name) {
			raw_name = flag->name;
		}
	}
	if (!raw_name && anal) {
		target_fcn = r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
		if (target_fcn && target_fcn->name && *target_fcn->name) {
			raw_name = target_fcn->name;
		}
	}
	return raw_name? strdup (raw_name): NULL;
}

static unsigned int resolve_interproc_seed_linkage(RCore *core, RAnal *anal, ut64 addr) {
	RAnalFunction *target_fcn = NULL;
	RBinSymbol *symbol = NULL;

	if (anal) {
		target_fcn = r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
		if (target_fcn) {
			return (target_fcn->type & R_ANAL_FCN_TYPE_IMP)
				? R2SLEIGH_INTERPROC_LINKAGE_IMPORTED
				: R2SLEIGH_INTERPROC_LINKAGE_INTERNAL;
		}
		if (anal->binb.bin && anal->binb.get_symbol_at) {
			symbol = anal->binb.get_symbol_at (anal->binb.bin, addr);
			if (symbol) {
				return symbol->is_imported
					? R2SLEIGH_INTERPROC_LINKAGE_IMPORTED
					: R2SLEIGH_INTERPROC_LINKAGE_INTERNAL;
			}
		}
	}
	if (core && core->bin) {
		symbol = r_bin_get_symbol_at (core->bin, addr);
		if (symbol) {
			return symbol->is_imported
				? R2SLEIGH_INTERPROC_LINKAGE_IMPORTED
				: R2SLEIGH_INTERPROC_LINKAGE_INTERNAL;
		}
	}
	return R2SLEIGH_INTERPROC_LINKAGE_UNKNOWN;
}

static ut64 *collect_type_interproc_direct_targets_from_blocks(
	R2ILContext *ctx,
	const BlockArray *blocks,
	ut64 fcn_addr,
	const char *fcn_name,
	size_t *out_count
) {
	R2SleighAnalysisResultV2 *typed_targets = NULL;
	R2SleighAnalysisResultViewV2 typed_view;
	const unsigned long long *items = NULL;
	ut64 *targets = NULL;
	size_t count = 0;
	size_t cap = 0;
	size_t item_count = 0;
	size_t i;

	if (out_count) {
		*out_count = 0;
	}
	if (!ctx || !blocks || !blocks->blocks || blocks->count == 0) {
		return NULL;
	}
	uint32_t typed_status = sleigh_v2_analysis_query (R2SLEIGH_QUERY_DIRECT_TARGETS_V2,
		ctx, (const R2ILBlock *const *)blocks->blocks, blocks->count, fcn_addr,
		fcn_name, NULL, 0, &typed_targets, &typed_view);
	if (typed_status != R2SLEIGH_STATUS_OK_V2) {
		return NULL;
	}
	items = (const unsigned long long *)typed_view.primary;
	item_count = typed_view.primary_count;
	for (i = 0; items && i < item_count; i++) {
		append_unique_ut64 (&targets, &count, &cap, (ut64)items[i]);
	}
	(void)sleigh_v2_analysis_result_release (&typed_targets);
	if (out_count) {
		*out_count = count;
	}
	return targets;
}


static void free_interproc_target_names(char **target_names, size_t target_count) {
	size_t i;
	if (!target_names) {
		return;
	}
	for (i = 0; i < target_count; i++) {
		free (target_names[i]);
	}
	free (target_names);
}

static bool plan_interproc_targets_from_direct_targets(
	RCore *core,
	RAnal *anal,
	const ut64 *direct_targets,
	size_t target_count,
	R2SleighPlannerResultV2 **out
) {
	R2SleighPlannerTargetInputV2 *target_inputs = NULL;
	char **target_names = NULL;
	R2SleighPlannerQueryRequestV2 request = {0};
	R2SleighPlannerQueryResponseV2 response = {0};
	uint32_t status;
	size_t i;
	if (out) {
		*out = NULL;
	}
	if (!anal || !direct_targets || !target_count || target_count > R2SLEIGH_MAX_PLANNER_TARGETS_V2 || !out) {
		return false;
	}
	if (!sleigh_v2_planner_result_retry_pending ()) {
		return false;
	}
	target_inputs = calloc (target_count, sizeof (*target_inputs));
	target_names = calloc (target_count, sizeof (*target_names));
	if (!target_inputs || !target_names) {
		free (target_inputs);
		free_interproc_target_names (target_names, target_count);
		return false;
	}
	for (i = 0; i < target_count; i++) {
		ut64 scope_target = direct_targets[i];
		RAnalFunction *target_fcn = NULL;
		target_names[i] = resolve_interproc_seed_name (core, anal, direct_targets[i]);
		scope_target = resolve_local_direct_jump_thunk_target (anal, direct_targets[i]);
		target_fcn = materialize_function_at (anal, scope_target);
		target_inputs[i].abi_version = R2SLEIGH_ABI_V2;
		target_inputs[i].struct_size = sizeof (target_inputs[i]);
		target_inputs[i].schema_version = R2SLEIGH_PLANNER_TARGET_INPUT_SCHEMA_V2;
		target_inputs[i].direct_target = direct_targets[i];
		if (target_names[i]) {
			target_inputs[i].name.data = (const uint8_t *)target_names[i];
			target_inputs[i].name.len = strlen (target_names[i]);
		}
		target_inputs[i].linkage = resolve_interproc_seed_linkage (core, anal, direct_targets[i]);
		target_inputs[i].resolved_target = scope_target;
		target_inputs[i].has_resolved_target = 1;
		target_inputs[i].target_materialized = target_fcn? 1: 0;
		if (target_fcn) {
			int bb_count = function_bb_count (target_fcn);
			target_inputs[i].has_target_metrics = 1;
			target_inputs[i].target_basic_block_count = bb_count > 0? (unsigned int)bb_count: 0;
			target_inputs[i].target_cost = (unsigned int)r_anal_function_cost (target_fcn);
		}
		if (scope_target != direct_targets[i]) {
			sleigh_debug_scope_log (
				"scope_resolved_thunk_target from=0x%"PFMT64x" to=0x%"PFMT64x" name=%s",
				direct_targets[i],
				scope_target,
				target_names[i]? target_names[i]: "(null)"
			);
		}
	}
	request.targets = target_inputs;
	request.num_targets = target_count;
	status = sleigh_v2_planner_query (
		R2SLEIGH_PLANNER_INTERPROC_TARGETS_V2,
		&request,
		&response);
	if (response.result) {
		sleigh_pending_target_plan = response.result;
	}
	free (target_inputs);
	free_interproc_target_names (target_names, target_count);
	if (status != R2SLEIGH_STATUS_OK_V2 || !response.result) {
		(void)sleigh_v2_planner_result_retry_pending ();
		return false;
	}
	*out = response.result;
	return true;
}

static ut64 *copy_planner_result_targets(
	const R2SleighApiV2 *api,
	const R2SleighPlannerResultV2 *result,
	unsigned int selector,
	size_t count
) {
	ut64 *targets = NULL;
	size_t copied = 0;
	if (!count) {
		return NULL;
	}
	if (!api || !result || count > SIZE_MAX / sizeof (*targets)) {
		return NULL;
	}
	targets = calloc (count, sizeof (*targets));
	if (!targets) {
		return NULL;
	}
	if (api->planner_result_copy (result, selector, targets, count, &copied) != R2SLEIGH_STATUS_OK_V2
		|| copied != count) {
		free (targets);
		return NULL;
	}
	return targets;
}

static ut64 *collect_runtime_scope_targets_from_blocks(
	R2ILContext *ctx,
	const BlockArray *blocks,
	ut64 fcn_addr,
	const char *fcn_name,
	const ut64 *registration_targets,
	size_t registration_target_count,
	size_t *out_count
) {
	R2SleighAnalysisResultV2 *typed_targets = NULL;
	R2SleighAnalysisResultViewV2 typed_view;
	const unsigned long long *items = NULL;
	ut64 *targets = NULL;
	size_t count = 0;
	size_t cap = 0;
	size_t item_count = 0;
	size_t i;

	if (out_count) {
		*out_count = 0;
	}
	if (!ctx || !blocks || !blocks->blocks || blocks->count == 0 || !registration_target_count) {
		return NULL;
	}
	uint32_t typed_status = sleigh_v2_analysis_query (R2SLEIGH_QUERY_SYMBOLIC_TARGETS_V2,
		ctx, (const R2ILBlock *const *)blocks->blocks, blocks->count, fcn_addr,
		fcn_name, registration_targets, registration_target_count, &typed_targets, &typed_view);
	if (typed_status != R2SLEIGH_STATUS_OK_V2) {
		return NULL;
	}
	items = (const unsigned long long *)typed_view.primary;
	item_count = typed_view.primary_count;
	for (i = 0; items && i < item_count; i++) {
		append_unique_ut64 (&targets, &count, &cap, (ut64)items[i]);
	}
	(void)sleigh_v2_analysis_result_release (&typed_targets);
	if (out_count) {
		*out_count = count;
	}
	return targets;
}

static bool append_runtime_materialized_source(
	RuntimeMaterializedSource **sources,
	size_t *count,
	size_t *cap,
	ut64 addr,
	ut64 size
) {
	RuntimeMaterializedSource *next;
	size_t i;
	if (!sources || !count || !cap || !addr || !size) {
		return false;
	}
	for (i = 0; i < *count; i++) {
		if ((*sources)[i].addr == addr) {
			if ((*sources)[i].size < size) {
				(*sources)[i].size = size;
			}
			return true;
		}
	}
	if (*count >= *cap) {
		size_t new_cap = *cap? *cap * 2: 4;
		next = realloc (*sources, new_cap * sizeof (**sources));
		if (!next) {
			return false;
		}
		*sources = next;
		*cap = new_cap;
	}
	(*sources)[*count].addr = addr;
	(*sources)[*count].size = size;
	(*count)++;
	return true;
}

static RuntimeMaterializedSource *collect_runtime_materialized_sources_from_blocks(
	R2ILContext *ctx,
	const BlockArray *blocks,
	ut64 fcn_addr,
	const char *fcn_name,
	const ut64 *copy_targets,
	size_t copy_target_count,
	size_t *out_count
) {
	R2SleighAnalysisResultV2 *typed_sources = NULL;
	R2SleighAnalysisResultViewV2 typed_view;
	const R2SleighRuntimeSource *items = NULL;
	RuntimeMaterializedSource *sources = NULL;
	size_t count = 0;
	size_t cap = 0;
	size_t item_count = 0;
	size_t i;

	if (out_count) {
		*out_count = 0;
	}
	if (!ctx || !blocks || !blocks->blocks || blocks->count == 0 || !copy_target_count) {
		return NULL;
	}
	uint32_t typed_status = sleigh_v2_analysis_query (R2SLEIGH_QUERY_RUNTIME_SOURCES_V2,
		ctx, (const R2ILBlock *const *)blocks->blocks, blocks->count, fcn_addr,
		fcn_name, copy_targets, copy_target_count, &typed_sources, &typed_view);
	if (typed_status != R2SLEIGH_STATUS_OK_V2) {
		return NULL;
	}
	items = (const R2SleighRuntimeSource *)typed_view.primary;
	item_count = typed_view.primary_count;
	for (i = 0; items && i < item_count; i++) {
		ut64 addr;
		ut64 size;
		addr = (ut64)items[i].addr;
		size = (ut64)items[i].size;
		if (addr && size) {
			(void)append_runtime_materialized_source (&sources, &count, &cap, addr, size);
		}
	}
	(void)sleigh_v2_analysis_result_release (&typed_sources);
	if (out_count) {
		*out_count = count;
	}
	return sources;
}

static void sym_function_scope_init(SymFunctionScope *scope) {
	if (!scope) {
		return;
	}
	memset (scope, 0, sizeof (*scope));
}

static void sym_function_scope_free(SymFunctionScope *scope) {
	size_t i;
	if (!scope) {
		return;
	}
	for (i = 0; i < scope->count; i++) {
		block_array_free (&scope->owned_blocks[i]);
		free (scope->owned_names[i]);
	}
	free (scope->functions);
	free (scope->owned_blocks);
	free (scope->owned_names);
	memset (scope, 0, sizeof (*scope));
}

static bool sym_function_scope_ensure_capacity(SymFunctionScope *scope, size_t needed) {
	R2ILFunctionBlocks *functions_next;
	BlockArray *blocks_next;
	char **names_next;
	size_t new_cap;
	if (!scope) {
		return false;
	}
	if (needed > (size_t)R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2) {
		R_LOG_ERROR ("r2sleigh: interprocedural function count exceeds cap %u",
			(unsigned int)R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2);
		return false;
	}
	if (needed <= scope->capacity) {
		return true;
	}
	new_cap = scope->capacity? scope->capacity * 2: 4;
	if (new_cap < scope->capacity) {
		return false;
	}
	while (new_cap < needed && new_cap <= (size_t)R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2 / 2) {
		new_cap *= 2;
	}
	if (new_cap < needed) {
		new_cap = needed;
	}
	size_t functions_size;
	size_t blocks_size;
	size_t names_size;
	if (r_mul_overflow (new_cap, sizeof (*scope->functions), &functions_size)
		|| r_mul_overflow (new_cap, sizeof (*scope->owned_blocks), &blocks_size)
		|| r_mul_overflow (new_cap, sizeof (*scope->owned_names), &names_size)) {
		return false;
	}
	functions_next = calloc (1, functions_size);
	blocks_next = calloc (1, blocks_size);
	names_next = calloc (1, names_size);
	if (!functions_next || !blocks_next || !names_next) {
		free (functions_next);
		free (blocks_next);
		free (names_next);
		return false;
	}
	if (scope->count) {
		memcpy (functions_next, scope->functions, scope->count * sizeof (*scope->functions));
		memcpy (blocks_next, scope->owned_blocks, scope->count * sizeof (*scope->owned_blocks));
		memcpy (names_next, scope->owned_names, scope->count * sizeof (*scope->owned_names));
	}
	free (scope->functions);
	free (scope->owned_blocks);
	free (scope->owned_names);
	scope->functions = functions_next;
	scope->owned_blocks = blocks_next;
	scope->owned_names = names_next;
	scope->capacity = new_cap;
	return true;
}

static bool sym_function_scope_append(
	SymFunctionScope *scope,
	RAnal *anal,
	RAnalFunction *fcn,
	R2ILContext *ctx
) {
	BlockArray blocks;
	if (!scope || !anal || !fcn || !ctx) {
		return false;
	}
	if (!sleigh_engine_function_preflight (fcn, "interprocedural scope")) {
		return false;
	}
	const size_t scope_block_cap = (size_t)R2SLEIGH_MAX_AGGREGATE_BLOCKS_V2
		- (size_t)R2SLEIGH_MAX_FUNCTION_BLOCKS_V2;
	const size_t scope_op_cap = (size_t)R2SLEIGH_MAX_AGGREGATE_OPS_V2
		- (size_t)R2SLEIGH_MAX_FUNCTION_OPS_V2;
	if (scope->total_blocks >= scope_block_cap || scope->total_ops >= scope_op_cap) {
		R_LOG_ERROR ("r2sleigh: interprocedural scope budget exhausted before function 0x%"PFMT64x, fcn->addr);
		return false;
	}
	if (!sym_function_scope_ensure_capacity (scope, scope->count + 1)) {
		return false;
	}
	sleigh_debug_scope_log (
		"scope_append addr=0x%"PFMT64x" name=%s",
		fcn->addr,
		fcn->name? fcn->name: "(null)"
	);
	const size_t remaining_blocks = scope_block_cap - scope->total_blocks;
	const size_t remaining_ops = scope_op_cap - scope->total_ops;
	const size_t function_block_cap = R_MIN (
		(size_t)R2SLEIGH_MAX_FUNCTION_BLOCKS_V2, remaining_blocks);
	const size_t function_op_cap = R_MIN (
		(size_t)R2SLEIGH_MAX_FUNCTION_OPS_V2, remaining_ops);
	if (!lift_function_blocks_with_limits (
			anal, fcn, ctx, &blocks, function_block_cap, function_op_cap)) {
		sleigh_debug_scope_log ("scope_append_failed addr=0x%"PFMT64x, fcn->addr);
		return false;
	}
	size_t lifted_ops = 0;
	size_t block_index;
	for (block_index = 0; block_index < blocks.count; block_index++) {
		size_t block_ops = 0;
		if (sleigh_v2_block_op_count (blocks.blocks[block_index], &block_ops)
			!= R2SLEIGH_STATUS_OK_V2) {
			block_array_free (&blocks);
			return false;
		}
		if (block_ops > function_op_cap - lifted_ops) {
			block_array_free (&blocks);
			return false;
		}
		lifted_ops += block_ops;
	}
	scope->owned_blocks[scope->count] = blocks;
	scope->owned_names[scope->count] = fcn->name? strdup (fcn->name): NULL;
	scope->functions[scope->count].entry_addr = fcn->addr;
	scope->functions[scope->count].name = scope->owned_names[scope->count];
	scope->functions[scope->count].blocks = (const R2ILBlock **)scope->owned_blocks[scope->count].blocks;
	scope->functions[scope->count].num_blocks = scope->owned_blocks[scope->count].count;
	scope->functions[scope->count].provenance = R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_ANALYZED;
	scope->total_blocks += blocks.count;
	scope->total_ops += lifted_ops;
	scope->count++;
	sleigh_debug_scope_log (
		"scope_appended addr=0x%"PFMT64x" blocks=%zu",
		fcn->addr,
		blocks.count
	);
	return true;
}

static bool lift_runtime_materialized_source_blocks(
	RAnal *anal,
	R2ILContext *ctx,
	ut64 addr,
	ut64 size,
	ut64 slot_bytes,
	BlockArray *out
) {
	ut64 offset = 0;

	if (!anal || !ctx || !out || !addr || !size || !slot_bytes || !anal->iob.read_at) {
		return false;
	}
	block_array_init (out);
	while (offset < size) {
		ut64 cur = addr + offset;
		ut8 buf[SLEIGH_MIN_BYTES] = {0};
		ut64 remaining = size - offset;
		ut64 logical_size = R_MIN (remaining, slot_bytes);
		R2ILBlock *block = NULL;

		if (!anal->iob.read_at (anal->iob.io, cur, buf, sizeof (buf))) {
			break;
		}
		uint32_t status = sleigh_v2_lift_block (ctx, buf, sizeof (buf), cur,
			(unsigned int)logical_size, &block);
		if (status == R2SLEIGH_STATUS_OK_V2 && block) {
			if (sleigh_v2_block_validate (ctx, block) == R2SLEIGH_STATUS_OK_V2) {
				if (!block_array_push (out, block)) {
					(void)sleigh_v2_block_release (&block);
					block_array_free (out);
					return false;
				}
			} else {
				(void)sleigh_v2_block_release (&block);
			}
		}
		offset += logical_size;
	}
	block_array_sort (out);
	return out->count > 0;
}

static bool sym_function_scope_append_runtime_source(
	SymFunctionScope *scope,
	RAnal *anal,
	R2ILContext *ctx,
	ut64 addr,
	ut64 size
) {
	BlockArray blocks;
	char name[64];
	R2SleighRuntimeMaterializedSourcePlanV2 plan;

	if (!scope || !anal || !ctx || !addr || !size) {
		return false;
	}
	plan = sleigh_v2_query_runtime_source (scope->count, addr, size);
	if (!plan.append_source || !plan.capped_size || !plan.slot_bytes) {
		return false;
	}
	if (!lift_runtime_materialized_source_blocks (
		anal,
		ctx,
		addr,
		(ut64)plan.capped_size,
		(ut64)plan.slot_bytes,
		&blocks)) {
		return false;
	}
	const size_t scope_block_cap = (size_t)R2SLEIGH_MAX_AGGREGATE_BLOCKS_V2
		- (size_t)R2SLEIGH_MAX_FUNCTION_BLOCKS_V2;
	const size_t scope_op_cap = (size_t)R2SLEIGH_MAX_AGGREGATE_OPS_V2
		- (size_t)R2SLEIGH_MAX_FUNCTION_OPS_V2;
	if (scope->total_blocks > scope_block_cap || scope->total_ops > scope_op_cap
		|| blocks.count > scope_block_cap - scope->total_blocks) {
		block_array_free (&blocks);
		return false;
	}
	size_t lifted_ops = 0;
	size_t block_index;
	for (block_index = 0; block_index < blocks.count; block_index++) {
		size_t block_ops = 0;
		if (sleigh_v2_block_op_count (blocks.blocks[block_index], &block_ops)
			!= R2SLEIGH_STATUS_OK_V2) {
			block_array_free (&blocks);
			return false;
		}
		if (block_ops > scope_op_cap - scope->total_ops - lifted_ops) {
			block_array_free (&blocks);
			return false;
		}
		lifted_ops += block_ops;
	}
	if (!sym_function_scope_ensure_capacity (scope, scope->count + 1)) {
		block_array_free (&blocks);
		return false;
	}
	snprintf (name, sizeof (name), "runtime.source.%"PFMT64x, addr);
	scope->owned_blocks[scope->count] = blocks;
	scope->owned_names[scope->count] = strdup (name);
	scope->functions[scope->count].entry_addr = addr;
	scope->functions[scope->count].name = scope->owned_names[scope->count];
	scope->functions[scope->count].blocks = (const R2ILBlock **)scope->owned_blocks[scope->count].blocks;
	scope->functions[scope->count].num_blocks = scope->owned_blocks[scope->count].count;
	scope->functions[scope->count].provenance = R2SLEIGH_SCOPED_FUNCTION_PROVENANCE_RUNTIME_MATERIALIZED;
	scope->total_blocks += blocks.count;
	scope->total_ops += lifted_ops;
	scope->count++;
	sleigh_debug_scope_log (
		"scope_runtime_source addr=0x%"PFMT64x" size=%"PFMT64u" blocks=%zu",
		addr,
		size,
		blocks.count
	);
	return true;
}

static bool build_symbolic_function_scope_with_target(
	RAnal *anal,
	RAnalFunction *root_fcn,
	R2ILContext *ctx,
	SymFunctionScope *scope,
	ut64 target_hint
) {
	size_t queue_count = 0;
	size_t queue_cap = 0;
	size_t queue_index = 0;
	ut64 *queue = NULL;
	ut64 *seen = NULL;
	size_t seen_count = 0;
	size_t seen_cap = 0;
	ut64 target_entry = UT64_MAX;
	const R2SleighApiV2 *api = sleigh_lift_api_v2 ();
	bool build_ok = true;

	if (!anal || !root_fcn || !ctx || !scope || !api) {
		return false;
	}
	if (!sleigh_v2_planner_result_retry_pending ()) {
		return false;
	}
	sym_function_scope_init (scope);
	if (!append_unique_ut64 (&queue, &queue_count, &queue_cap, root_fcn->addr)) {
		free (queue);
		return false;
	}
	if (target_hint != UT64_MAX && target_hint && target_hint != root_fcn->addr) {
		RAnalFunction *target_fcn = materialize_function_at (anal, target_hint);
		if (target_fcn) {
			target_entry = target_fcn->addr;
			append_unique_ut64 (&queue, &queue_count, &queue_cap, target_fcn->addr);
			sleigh_debug_scope_log (
				"scope_target_hint target=0x%"PFMT64x" entry=0x%"PFMT64x" name=%s",
				target_hint,
				target_fcn->addr,
				target_fcn->name? target_fcn->name: "(null)"
			);
		} else {
			sleigh_debug_scope_log (
				"scope_target_hint_unmaterialized target=0x%"PFMT64x,
				target_hint
			);
		}
	}
	sleigh_debug_scope_log (
		"scope_build_start root=0x%"PFMT64x" name=%s",
		root_fcn->addr,
		root_fcn->name? root_fcn->name: "(null)"
	);

	while (queue_index < queue_count) {
		RAnalFunction *fcn;
		ut64 addr = queue[queue_index++];
		ut64 *direct_targets = NULL;
		ut64 *queued_direct_targets = NULL;
		ut64 *runtime_targets = NULL;
		RuntimeMaterializedSource *runtime_sources = NULL;
		R2SleighPlannerResultV2 *target_plan = NULL;
		R2SleighPlannerResultViewV2 target_plan_view = {0};
		size_t target_count = 0;
		size_t queued_direct_target_count = 0;
		size_t queued_direct_target_cap = 0;
		size_t runtime_target_count = 0;
		size_t runtime_source_count = 0;
		size_t planned_count = 0;
		ut64 *planned_items = NULL;
		size_t planned_runtime_copy_count = 0;
		ut64 *planned_runtime_copy_items = NULL;
		size_t planned_queued_count = 0;
		ut64 *planned_queued_items = NULL;
			size_t i;
			const BlockArray *blocks;
			R2SleighSymbolicScopeFunctionPlanV2 scope_plan;

			fcn = materialize_function_at (anal, addr);
			if (!fcn || !append_unique_ut64 (&seen, &seen_count, &seen_cap, fcn->addr)) {
			continue;
		}
		bool target_hint_function = target_entry != UT64_MAX && fcn->addr == target_entry;
			R2SleighInterprocSessionPlan interproc_plan =
				sleigh_interproc_session_plan_for_function (anal, fcn, R2SLEIGH_INTERPROC_SESSION_TYPE_ANALYSIS_V2);
			scope_plan = sleigh_v2_query_symbolic_scope (
				scope->count,
				fcn->addr == root_fcn->addr,
				target_hint_function,
				interproc_plan);
			if (!scope_plan.append_function) {
				sleigh_debug_scope_log (
					"scope_skip_engine_policy addr=0x%"PFMT64x" name=%s reason=%u",
					fcn->addr,
					fcn->name? fcn->name: "(null)",
					scope_plan.reason
				);
				continue;
			}
		if (!sym_function_scope_append (
			scope,
			anal,
			fcn,
			ctx
		)) {
			continue;
		}
		if (fcn->addr != root_fcn->addr) {
			sleigh_debug_scope_log (
				"scope_expand_helper addr=0x%"PFMT64x" name=%s",
				fcn->addr,
				fcn->name? fcn->name: "(null)"
			);
		}
			if (!scope_plan.expand_targets) {
				sleigh_debug_scope_log (
					"scope_expansion_stopped_by_engine addr=0x%"PFMT64x" target=0x%"PFMT64x" reason=%u",
					fcn->addr,
					target_hint,
					scope_plan.reason
				);
				continue;
			}
		blocks = &scope->owned_blocks[scope->count - 1];
		direct_targets = collect_type_interproc_direct_targets_from_blocks (
			ctx, blocks, fcn->addr, fcn->name, &target_count);
		sleigh_debug_scope_log (
			"scope_targets addr=0x%"PFMT64x" direct=%zu",
			fcn->addr,
			target_count
		);
		if (direct_targets && target_count) {
			build_ok = plan_interproc_targets_from_direct_targets (
				anal->coreb.core,
				anal,
				direct_targets,
				target_count,
				&target_plan
			);
		}
		if (!build_ok) {
			sleigh_debug_scope_log ("scope_target_plan_failed addr=0x%"PFMT64x, fcn->addr);
			free (direct_targets);
			break;
		}
		if (target_plan) {
			if (api->planner_result_view (target_plan, &target_plan_view) == R2SLEIGH_STATUS_OK_V2
				&& target_plan_view.abi_version == R2SLEIGH_ABI_V2
				&& target_plan_view.struct_size == sizeof (target_plan_view)
				&& target_plan_view.schema_version == R2SLEIGH_PLANNER_RESULT_SCHEMA_V2) {
				planned_count = target_plan_view.registration_target_count;
				planned_runtime_copy_count = target_plan_view.runtime_copy_target_count;
				planned_queued_count = target_plan_view.queued_target_count;
				planned_items = copy_planner_result_targets (
					api, target_plan, R2SLEIGH_PLANNER_RESULT_REGISTRATION_TARGETS_V2, planned_count);
				planned_runtime_copy_items = copy_planner_result_targets (
					api, target_plan, R2SLEIGH_PLANNER_RESULT_RUNTIME_COPY_TARGETS_V2, planned_runtime_copy_count);
				planned_queued_items = copy_planner_result_targets (
					api, target_plan, R2SLEIGH_PLANNER_RESULT_QUEUED_TARGETS_V2, planned_queued_count);
				if (planned_count && !planned_items) {
					planned_count = 0;
				}
				if (planned_runtime_copy_count && !planned_runtime_copy_items) {
					planned_runtime_copy_count = 0;
				}
				if (planned_queued_count && !planned_queued_items) {
					planned_queued_count = 0;
				}
			}
			for (i = 0; planned_queued_items && i < planned_queued_count; i++) {
				append_unique_ut64 (
					&queued_direct_targets,
					&queued_direct_target_count,
					&queued_direct_target_cap,
					(ut64)planned_queued_items[i]
				);
			}
		}
		runtime_targets = collect_runtime_scope_targets_from_blocks (
			ctx,
			blocks,
			fcn->addr,
			fcn->name,
			(const ut64 *)planned_items,
			planned_count,
			&runtime_target_count);
		runtime_sources = collect_runtime_materialized_sources_from_blocks (
			ctx,
			blocks,
			fcn->addr,
			fcn->name,
			(const ut64 *)planned_runtime_copy_items,
			planned_runtime_copy_count,
			&runtime_source_count);
		sleigh_debug_scope_log (
			"scope_runtime_targets addr=0x%"PFMT64x" registrations=%zu runtime=%zu materialized=%zu",
			fcn->addr,
			planned_count,
			runtime_target_count,
			runtime_source_count
		);
		for (i = 0; i < runtime_target_count; i++) {
			append_unique_ut64 (&queue, &queue_count, &queue_cap, runtime_targets[i]);
		}
			for (i = 0; i < runtime_source_count; i++) {
				if (append_unique_ut64 (&seen, &seen_count, &seen_cap, runtime_sources[i].addr)) {
					(void)sym_function_scope_append_runtime_source (
					scope,
					anal,
					ctx,
					runtime_sources[i].addr,
					runtime_sources[i].size
				);
			}
		}
		for (i = 0; i < queued_direct_target_count; i++) {
			append_unique_ut64 (&queue, &queue_count, &queue_cap, queued_direct_targets[i]);
		}
		if (!sleigh_v2_planner_result_release (&target_plan)) {
			build_ok = false;
		}
		free (planned_items);
		free (planned_runtime_copy_items);
		free (planned_queued_items);
		free (queued_direct_targets);
		free (runtime_targets);
		free (runtime_sources);
		free (direct_targets);
		if (!build_ok) {
			break;
		}
	}

	free (queue);
	free (seen);
	if (!build_ok) {
		sym_function_scope_free (scope);
		return false;
	}
	sleigh_debug_scope_log ("scope_build_done count=%zu", scope->count);
	return scope->count > 0;
}

static bool build_symbolic_function_scope(
	RAnal *anal,
	RAnalFunction *root_fcn,
	R2ILContext *ctx,
	SymFunctionScope *scope
) {
	return build_symbolic_function_scope_with_target (anal, root_fcn, ctx, scope, UT64_MAX);
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
		NULL, NULL, 0, &result, &view);
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

/* Called at end of aaaa for global post-analysis passes */
static bool sleigh_post_analysis(RAnal *anal) {
	R2ILContext *ctx = get_context (anal);
	size_t taint_comments = 0;
	size_t taint_flags = 0;
	size_t taint_xrefs = 0;
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
	.analyze_fcn = sleigh_analyze_fcn,
	.recover_vars = sleigh_recover_vars,
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
