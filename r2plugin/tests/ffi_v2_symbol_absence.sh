#!/bin/sh
set -eu

library=$1
if [ "$(uname -s)" = Darwin ]; then
	symbols=$(nm -gU "$library" | awk '{ print $NF }')
else
	symbols=$(nm -g --defined-only "$library" | awk '{ print $NF }')
fi

for forbidden in \
	r2sleigh_engine_decompile_function \
	r2sleigh_engine_type_function_json \
	r2sleigh_ffi_sizeof_function_context \
	r2sleigh_ffi_alignof_function_context \
	r2sleigh_ffi_sizeof_engine_decompile_input \
	r2sleigh_ffi_alignof_engine_decompile_input \
	r2il_arch_init \
	r2il_free \
	r2il_is_loaded \
	r2il_arch_name \
	r2il_error \
	r2il_get_reg_profile \
	r2il_lift \
	r2il_lift_block \
	r2il_set_semantic_metadata_enabled \
	r2il_block_free \
	r2il_block_validate \
	r2il_block_set_switch_info \
	r2il_block_op_count \
	r2il_block_direct_call_identity \
	r2il_block_size \
	r2il_block_addr \
	r2il_block_mnemonic \
	r2il_block_type \
	r2il_block_jump \
	r2il_block_fail \
	r2il_string_free \
	r2il_block_to_esil \
	r2il_block_op_json_named \
	r2il_block_regs_read \
	r2il_block_regs_write \
	r2il_block_mem_access \
	r2il_block_varnodes \
	r2il_block_values_typed \
	r2il_block_values_memory \
	r2il_block_values_immediates \
	r2il_block_values_reg_reads \
	r2il_block_values_reg_writes \
	r2il_block_values_free \
	r2il_block_to_ssa_json \
	r2il_block_defuse_json \
	r2ssa_function_json \
	r2ssa_function_opt_json \
	r2ssa_defuse_function_json \
	r2ssa_domtree_json \
	r2ssa_backward_slice_json \
	r2cfg_function_ascii \
	r2cfg_function_json \
	r2taint_function_json \
	r2taint_function_summary_typed \
	r2taint_function_summary_sources \
	r2taint_function_summary_sink_hits \
	r2taint_function_summary_free \
	r2sym_function_scope \
	r2sym_paths_scope \
	r2sym_explore_to_scope \
	r2sym_solve_to_scope \
	r2sym_run_spec_json_scope \
	r2sym_explore_to_replay_scope \
	r2sym_solve_to_replay_scope \
	r2sleigh_engine_cache_stats_json \
	r2sleigh_engine_cache_stats_reset \
	r2sleigh_get_direct_call_targets_typed \
	r2sleigh_get_symbolic_scope_targets_typed \
	r2sleigh_get_runtime_materialized_sources_typed \
	r2sleigh_u64_array_items \
	r2sleigh_u64_array_free \
	r2sleigh_runtime_sources_items \
	r2sleigh_runtime_sources_free \
	r2sleigh_analyze_fcn_annotations_typed \
	r2sleigh_annotations_items \
	r2sleigh_annotations_free \
	r2sleigh_recover_vars_typed \
	r2sleigh_recovered_vars_items \
	r2sleigh_recovered_vars_free \
	r2sleigh_data_refs_typed \
	r2sleigh_data_refs_items \
	r2sleigh_data_refs_free \
	r2sleigh_interproc_session_plan_for_depth \
	r2sleigh_symbolic_scope_function_plan \
	r2sleigh_runtime_materialized_source_plan \
	r2sleigh_analysis_policy_for_depth \
	r2sleigh_post_analysis_plan_for_depth \
	r2sleigh_auto_callback_plan_for_depth \
	r2sleigh_plan_interproc_scope_targets \
	r2sleigh_interproc_target_plan_queued_items \
	r2sleigh_interproc_target_plan_registration_items \
	r2sleigh_interproc_target_plan_runtime_copy_items \
	r2sleigh_interproc_target_plan_free \
	r2sym_merge_is_enabled \
	r2sym_merge_set_enabled \
	r2sym_set_symbol_map_json
do
	if printf '%s\n' "$symbols" | grep -Eq "^_?${forbidden}$"; then
		echo "forbidden legacy engine symbol remains: ${forbidden}" >&2
		exit 1
	fi
done

if ! printf '%s\n' "$symbols" | grep -Eq '^_?r2sleigh_api_v2$'; then
	echo "native V2 API symbol is missing" >&2
	exit 1
fi
