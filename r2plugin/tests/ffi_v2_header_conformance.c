#include "r2sleigh_api_v2.h"

#include <stddef.h>

#ifdef R2SLEIGH_QUERY_DIRECT_TARGETS_V2
#error "detached direct-target query must not be public"
#endif
#ifdef R2SLEIGH_QUERY_SYMBOLIC_TARGETS_V2
#error "detached symbolic-target query must not be public"
#endif
#ifdef R2SLEIGH_QUERY_RUNTIME_SOURCES_V2
#error "mutable runtime-source query must not be public"
#endif

static int data_ref_contract_matches(const R2SleighApiV2 *api, uint32_t size, uint32_t schema_version) {
	return api
		&& api->data_ref_size == size
		&& api->data_ref_schema_version == schema_version;
}

int main(void) {
	R2SleighFunctionContext function_context = {
		.schema_version = R2SLEIGH_FUNCTION_CONTEXT_SCHEMA_V2,
	};
	R2SleighInterprocScope interproc_scope = {
		.schema_version = R2SLEIGH_INTERPROC_SCOPE_SCHEMA_V2,
	};
	R2SleighEngineRequestPayloadV2 request_payload = {
		.abi_version = R2SLEIGH_ABI_V2,
		.struct_size = sizeof (request_payload),
		.timeout_us = 10,
	};
	R2SleighRadareAccessorsV2 radare_accessors = {
		.struct_size = sizeof (radare_accessors),
		.abi_version = R2SLEIGH_RADARE_ABI_V2,
		.snapshot_schema_version = R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2,
		.accessor_schema_version = R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2,
	};
	R2SleighRadareSnapshotInputV2 radare_snapshot = {
		.struct_size = sizeof (radare_snapshot),
		.abi_version = R2SLEIGH_RADARE_ABI_V2,
		.snapshot_schema_version = R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2,
		.accessor_schema_version = R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2,
		.accessors = &radare_accessors,
	};
	R2SleighSourceStackSlotV2 stack_slot = {
		.base_kind = R2SLEIGH_SOURCE_STACK_BASE_SP_V2,
		.role = R2SLEIGH_SOURCE_STACK_ROLE_LOCAL_V2,
		.parameter_index = R2SLEIGH_SOURCE_PARAMETER_INDEX_INVALID_V2,
	};
	R2SleighSourceCarrierProjectionV2 carrier = {
		.kind = R2SLEIGH_SOURCE_CARRIER_FULL_V2,
		.size_bits = 64,
	};
	R2SleighSourceParameterTypeV2 parameter_type = {
		.type_id = 2,
		.carrier = carrier,
	};
	R2SleighSourceTypeV2 source_type = {
		.id = 1,
		.kind = R2SLEIGH_SOURCE_TYPE_SIGNED_INTEGER_V2,
		.size_bits = 32,
		.align_bits = 32,
		.target_type_id = R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
		.aggregate_id = R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2,
	};
	R2SleighSourceAggregateMemberV2 aggregate_member = {
		.type_id = 1,
		.size_bits = 32,
	};
	R2SleighSourceAggregateLayoutV2 aggregate_layout = {
		.members = &aggregate_member,
		.num_members = 1,
		.complete = 1,
		.c_layout_compatible = 1,
	};
	R2SleighSourceFunctionInterfaceV2 source_interface = {
		.schema_version = R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2,
		.struct_size = sizeof (source_interface),
		.function_addr = 0x401000,
		.stack_slots = &stack_slot,
		.num_stack_slots = 1,
		.parameter_types = &parameter_type,
		.num_parameter_types = 1,
		.types = &source_type,
		.num_types = 1,
		.aggregates = &aggregate_layout,
		.num_aggregates = 1,
		.exact_types_complete = 1,
		.stack_slot_roles_complete = 1,
		.return_address_storage = {
			.space = R2SLEIGH_SOURCE_STORAGE_REGISTER_V2,
			.offset = 0x30,
			.size = 8,
		},
		.stack_pointer_storage = {
			.space = R2SLEIGH_SOURCE_STORAGE_REGISTER_V2,
			.offset = 0x38,
			.size = 8,
		},
	};
	R2SleighSourceCallSiteInterfaceV2 call_site = {
		.schema_version = R2SLEIGH_SOURCE_CALL_SITE_SCHEMA_V2,
		.target = {
			.space = R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2,
			.offset = 0x402000,
			.size = 8,
		},
	};
	R2SleighSwitchCaseV2 switch_case = {
		.value = 1,
		.target = 0x402000,
	};
	R2SleighDirectCallIdentityV2 call_identity = {
		.op_index = 3,
		.target_space = R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2,
		.target_offset = 0x402000,
		.target_size = 8,
	};
	R2SleighAnalysisRenderRequestV2 analysis_render = {
		.kind = R2SLEIGH_ANALYSIS_BLOCK_ESIL_V2,
	};
	R2SleighAnalysisQueryRequestV2 analysis_query = {
		.kind = R2SLEIGH_QUERY_BLOCK_VALUES_V2,
	};
	R2SleighAnalysisResultViewV2 analysis_view = {0};
	R2SleighPlannerQueryRequestV2 planner_query = {
		.abi_version = R2SLEIGH_ABI_V2,
		.struct_size = sizeof (planner_query),
		.schema_version = R2SLEIGH_PLANNER_QUERY_SCHEMA_V2,
		.kind = R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2,
	};
	R2SleighPlannerQueryResponseV2 planner_response = {0};
	request_payload.radare_snapshot = &radare_snapshot;
	const R2SleighApiV2 *api = r2sleigh_api_v2 ();
	if (R2SLEIGH_RADARE_ABI_V2 != 138
		|| R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2 != 9
		|| R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2 != 3
		|| radare_snapshot.struct_size != sizeof (R2SleighRadareSnapshotInputV2)
		|| radare_snapshot.accessors != &radare_accessors
		|| radare_accessors.struct_size != sizeof (R2SleighRadareAccessorsV2)
		|| R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2 != 7
		|| source_interface.schema_version != 7
		|| function_context.schema_version != 3
		|| interproc_scope.schema_version != 1
		|| R2SLEIGH_RESPONSE_INFO_SCHEMA_V2 != 2
		|| source_interface.function_addr != 0x401000
		|| source_interface.parameter_types[0].carrier.kind != R2SLEIGH_SOURCE_CARRIER_FULL_V2
		|| source_interface.types[0].kind != R2SLEIGH_SOURCE_TYPE_SIGNED_INTEGER_V2
		|| source_interface.aggregates[0].members[0].size_bits != 32
		|| call_site.schema_version != 1
		|| call_site.target.space != R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2
		|| switch_case.target != 0x402000
		|| call_identity.op_index != 3
		|| analysis_render.kind != R2SLEIGH_ANALYSIS_BLOCK_ESIL_V2
		|| analysis_query.kind != R2SLEIGH_QUERY_BLOCK_VALUES_V2
		|| analysis_view.kind != 0
		|| request_payload.timeout_us != 10
		|| request_payload.radare_snapshot != &radare_snapshot
		|| source_interface.stack_slots[0].base_kind != R2SLEIGH_SOURCE_STACK_BASE_SP_V2
		|| source_interface.return_address_storage.space != R2SLEIGH_SOURCE_STORAGE_REGISTER_V2
		|| source_interface.return_address_storage.offset != 0x30
		|| source_interface.return_address_storage.size != 8
		|| source_interface.stack_pointer_storage.space != R2SLEIGH_SOURCE_STORAGE_REGISTER_V2
		|| source_interface.stack_pointer_storage.offset != 0x38
		|| source_interface.stack_pointer_storage.size != 8
		|| R2SLEIGH_MAX_FUNCTION_BLOCKS_V2 != 200
		|| R2SLEIGH_MAX_FUNCTION_OPS_V2 != 512
		|| R2SLEIGH_MAX_SWITCH_CASES_V2 != 4096
		|| R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2 != (16U << 20)
		|| R2SLEIGH_MAX_AGGREGATE_BLOCKS_V2 != 1024
		|| R2SLEIGH_MAX_AGGREGATE_OPS_V2 != 4096
		|| R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2 != 4096
		|| R2SLEIGH_MAX_CONTEXT_ITEMS_V2 != 65536
		|| R2SLEIGH_MAX_NESTED_ITEMS_V2 != 262144
		|| R2SLEIGH_MAX_AGGREGATE_STRING_BYTES_V2 != (4U << 20)
		|| R2SLEIGH_MAX_AGGREGATE_JSON_BYTES_V2 != (16U << 20)
		|| !api || api->abi_version != R2SLEIGH_ABI_V2
		|| api->struct_size != sizeof (*api)
		|| api->radare_abi_version != R2SLEIGH_RADARE_ABI_V2
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
		|| api->string_view_size != sizeof (R2SleighStringViewV2)
		|| api->phase_timing_size != sizeof (R2SleighPhaseTimingV2)
		|| api->response_info_size != sizeof (R2SleighResponseInfoV2)
		|| api->switch_case_size != sizeof (R2SleighSwitchCaseV2)
		|| api->direct_call_identity_size != sizeof (R2SleighDirectCallIdentityV2)
		|| api->analysis_render_request_size != sizeof (R2SleighAnalysisRenderRequestV2)
		|| api->analysis_query_request_size != sizeof (R2SleighAnalysisQueryRequestV2)
		|| api->analysis_result_view_size != sizeof (R2SleighAnalysisResultViewV2)
		|| api->data_ref_size == 0
		|| api->data_ref_schema_version != R2SLEIGH_DATA_REF_SCHEMA_V2
		|| api->planner_query_request_size != sizeof (R2SleighPlannerQueryRequestV2)
		|| api->planner_query_response_size != sizeof (R2SleighPlannerQueryResponseV2)
		|| api->radare_snapshot_input_size != sizeof (R2SleighRadareSnapshotInputV2)
		|| api->radare_accessors_size != sizeof (R2SleighRadareAccessorsV2)
		|| (api->capabilities & R2SLEIGH_CAPABILITIES_V2) != R2SLEIGH_CAPABILITIES_V2
		|| !(api->capabilities & R2SLEIGH_CAP_NATIVE_REQUEST_GRAPH_V2)
		|| !(api->capabilities & R2SLEIGH_CAP_RESPONSE_INFO_V2)
		|| !(api->capabilities & R2SLEIGH_CAP_EXECUTION_CONTROL_V2)
		|| !(api->capabilities & R2SLEIGH_CAP_EXACT_TYPE_LAYOUT_V2)
		|| !(api->capabilities & R2SLEIGH_CAP_LIFT_CORE_V2)
		|| !(api->capabilities & R2SLEIGH_CAP_PLANNER_QUERY_V2)
		|| !(api->capabilities & R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2)
		|| R2SLEIGH_PHASE_COUNT_V2 != 11
		|| R2SLEIGH_PHASE_FFI_CONVERSION_V2 != 10
		|| !api->session_create || !api->session_free
		|| !api->session_cancel || !api->session_reset_cancellation || !api->execute
		|| !api->response_bytes || !api->response_info
		|| !api->response_free || !api->session_error
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
		|| !api->analysis_render || !api->analysis_query
		|| !api->analysis_result_view || !api->analysis_result_free
		|| !api->engine_cache_reset || !api->planner_query) {
		return 1;
	}
	if (!data_ref_contract_matches (api, api->data_ref_size, R2SLEIGH_DATA_REF_SCHEMA_V2)
		|| data_ref_contract_matches (api, api->data_ref_size + 1, R2SLEIGH_DATA_REF_SCHEMA_V2)
		|| data_ref_contract_matches (api, api->data_ref_size, R2SLEIGH_DATA_REF_SCHEMA_V2 + 1)) {
		return 14;
	}
	if (api->planner_query (&planner_query, &planner_response) != R2SLEIGH_STATUS_OK_V2
		|| planner_response.abi_version != R2SLEIGH_ABI_V2
		|| planner_response.struct_size != sizeof (planner_response)
		|| planner_response.schema_version != R2SLEIGH_PLANNER_QUERY_SCHEMA_V2
		|| planner_response.kind != R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2
		|| planner_response.analysis_policy.mode != R2SLEIGH_MODE_BALANCED_V2) {
		return 8;
	}
	planner_query.kind = R2SLEIGH_PLANNER_AUTO_CALLBACK_V2;
	planner_query.callback_kind = UINT32_MAX;
	if (api->planner_query (&planner_query, &planner_response) != R2SLEIGH_STATUS_INVALID_ARGUMENT_V2) {
		return 9;
	}
	planner_query.callback_kind = 0;

	static const uint8_t arch[] = "x86-64";
	R2SleighStringViewV2 arch_view = {
		.data = arch,
		.len = sizeof (arch) - 1,
	};
	if (api->lift_context_create (arch_view, NULL) != R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
		|| api->lift_context_create (arch_view, (R2ILContext **)(uintptr_t)1)
			!= R2SLEIGH_STATUS_INVALID_ARGUMENT_V2) {
		return 2;
	}
	R2ILContext *context = NULL;
	if (api->lift_context_create (arch_view, &context) != R2SLEIGH_STATUS_OK_V2
		|| !context) {
		return 3;
	}
	uint32_t loaded = 0;
	if (api->lift_context_is_loaded (context, &loaded) != R2SLEIGH_STATUS_OK_V2
		|| loaded != 1) {
		api->lift_context_free (context);
		return 4;
	}
	R2SleighOwnedBytesV2 *profile = NULL;
	if (api->lift_context_reg_profile (context, &profile) != R2SLEIGH_STATUS_OK_V2
		|| !profile) {
		api->lift_context_free (context);
		return 5;
	}
	R2SleighByteViewV2 profile_view = {0};
	if (api->owned_bytes_view (profile, &profile_view) != R2SLEIGH_STATUS_OK_V2
		|| !profile_view.data || !profile_view.len) {
		api->owned_bytes_free (profile);
		api->lift_context_free (context);
		return 6;
	}
	uint32_t wrong_kind_size = 0;
	if (api->lift_block_size ((const R2ILBlock *)profile, &wrong_kind_size)
			!= R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
		|| api->lift_context_free (context) != R2SLEIGH_STATUS_ENGINE_ERROR_V2
		|| api->owned_bytes_free (profile) != R2SLEIGH_STATUS_OK_V2
		|| api->owned_bytes_free (profile) != R2SLEIGH_STATUS_INVALID_ARGUMENT_V2
		|| api->lift_context_free (context) != R2SLEIGH_STATUS_OK_V2) {
		return 7;
	}
	return 0;
}
