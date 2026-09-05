/* r2sleigh function-snapshot capture.
 *
 * Moved out of the radare2 fork. Deciding which facts to collect from
 * radare2's analysis, at what granularity and with what proof marking, is
 * r2sleigh's policy, and radare2 does not need it to live inside radare2:
 * everything here runs against radare2's public API while the caller holds
 * anal->lock, which is the one thing the fork still has to provide. */

#include <r_anal.h>
#include <r_core.h>
#include <r_util.h>
#include "snapshot_capture.h"

/* forward declarations, so the moved bodies keep their original order */

/* ---- helpers radare2 also keeps ----
 * Duplicated rather than exported: growing radare2's public API to serve
 * one plugin is what this move exists to undo. */
static void function_context_fini(RAnalFcnContext *ctx);
static ut64 function_context_hash_mix(ut64 hash, ut64 value);
static ut64 function_context_hash_string(ut64 hash, const char *value);
static void function_logical_types_clear(RAnalFunctionInterfaceSnapshot *interface);
static RList *types_baselist_with_limits(RAnal *anal, const RAnalFunctionSnapshotLimits *limits);
static ut64 types_context_hash_from_snapshot(RAnal *anal, const RList *types, ut64 type_dirty_epoch);
static bool r_anal_cc_preserves_reg(RAnal *anal, const char *convention, const char *reg);
static bool r_anal_cc_return_mechanism(RAnal *anal, const char *convention, RAnalCCReturnMechanism *mechanism);
static bool r_anal_cc_stack_allocation_contract(RAnal *anal, const char *convention, RAnalCCStackAllocationContract *contract);
static RAnalFunctionSignature *r_anal_function_signature_from_type_name(RAnal *anal, const char *name);
static void r_anal_function_vars_cache_init_readonly(RAnal *anal, RAnalFcnVarsCache *cache, RAnalFunction *fcn);
static int base_type_name_cmp(const void *a, const void *b);
static bool type_context_hash_link_cb(void *user, const char *key, const char *value);
static ut64 type_context_hash_mix(ut64 hash, ut64 value);
static ut64 type_context_hash_string(ut64 hash, const char *value);
static bool types_snapshot_clone_cb(void *user, const char *name, const char *kind);
static bool types_snapshot_preflight(RAnal *anal, const RAnalFunctionSnapshotLimits *limits, RAnalTypeSnapshotBudget *result);
static bool cc_parse_return_mechanism(const char *record, RAnalCCReturnMechanism *mechanism);
static bool cc_parse_stack_allocation_contract(const char *record, const char *red_zone_record, RAnalCCStackAllocationContract *contract);
static const char *cc_regset(RAnal *anal, const char *convention, const char *field);
static bool r_anal_cc_regset_contains(const char *regset, const char *reg);
static RAnalFunctionSignature *function_signature_build(RAnal *anal, RAnalFunction *function, char *type_name, bool load_types);
static char *function_signature_try_type_name(Sdb *types, const char *candidate);
static int var_ptr_comparator(RAnalVar * const *a, RAnalVar * const *b);
static BaseTypeAppendResult append_base_type_if_unseen(RAnal *anal, RList *types, Sdb *seen, const char *kind, const char *sname);
static bool split_base_type_namespace_key(const char *key, const char **kind, const char **sname);
static bool type_context_hash_should_include_sdb_key(const char *key);
static bool type_snapshot_kind_supported(const char *kind);
static bool types_snapshot_preflight_cb(void *user, const char *name, const char *kind);
static bool cc_parse_s64_field(const char **sp, const char *end, char separator, st64 *out);
static bool cc_parse_u64_field(const char **sp, const char *end, ut64 limit, char separator, ut64 *out);
static const char *dyncc_intern(RAnal *anal, const char *p, size_t len);
static bool dyncc_parse(const char *cc, RAnalDynCC *out);
static void function_param_free(RAnalFunctionParam *param);
static const char *function_signature_callconv(RAnal *anal, RAnalFunction *fcn, const char *type_name, bool resolve_dynamic);
static bool function_signature_fallback_to_vars(RAnal *anal, RAnalFunction *fcn, RAnalFunctionSignature *signature);
static bool function_signature_is_noreturn(Sdb *types, const char *type_name, bool fallback);
static char *function_signature_string(const char *name, const char *ret_type, RList *params, bool sanitize_name, bool fill_defaults);
static int var_comparator(const RAnalVar *a, const RAnalVar *b);
static RAnalBaseType *get_base_type_for_kind(RAnal *anal, const char *kind, const char *sname);
static bool type_snapshot_preflight_one( RAnal *anal, Sdb *seen, RAnalTypeSnapshotBudget *used, const RAnalFunctionSnapshotLimits *limits, const char *kind, const char *sname);
static bool dyncc_parse_attrs(const char *s, const char *end, RAnalDynCC *d);
static bool dyncc_parse_homed_list(const char *s, const char *end, RAnalDynCC *d, bool args);
static int function_arg_cc_index(RAnal *anal, RAnalFunction *fcn, const RAnalVar *var);
static int function_arg_order_cmp(const void *a, const void *b);
static bool function_signature_append_arg(RStrBuf *args, const RAnalFunctionParam *param, bool first);
static const RAnalFunctionParam *function_signature_default_param(const RAnalFunctionParam *param, RAnalFunctionParam *tmp, size_t idx, char **default_name);
static RAnalBaseType *get_atomic_type(RAnal *anal, const char *sname);
static RAnalBaseType *get_composite_type(RAnal *anal, const char *sname, RAnalBaseTypeKind kind);
static RAnalBaseType *get_enum_type(RAnal *anal, const char *sname);
static RAnalBaseType *get_typedef_type(RAnal *anal, const char *sname);
static bool type_snapshot_budget_add(size_t *total, size_t amount, size_t maximum);
static bool type_snapshot_budget_add_string(RAnalTypeSnapshotBudget *budget, size_t length);
static bool type_snapshot_budget_commit( RAnalTypeSnapshotBudget *used, const RAnalTypeSnapshotBudget *added, const RAnalFunctionSnapshotLimits *limits);
static bool type_snapshot_budget_fits( const RAnalTypeSnapshotBudget *used, const RAnalTypeSnapshotBudget *added, const RAnalFunctionSnapshotLimits *limits);
static size_t type_snapshot_member_type_length(const char *value);
static bool dyncc_parse_fpargs(const char *s, const char *end, RAnalDynCC *d);
static bool dyncc_parse_homes(const char *s, const char *end, RAnalDynCCHomes *homes, int *count);
static bool dyncc_parse_int(const char **sp, int *out);
static bool dyncc_parse_ref_only(const char *s, const char *end, RAnalDynCCSlice *out);
static bool dyncc_set_role(RAnalDynCC *d, char tag, const char *s, const char *end);
static bool dyncc_set_slice(const char *s, const char *end, RAnalDynCCSlice *out, size_t maxlen);
static bool dyncc_tail_loc(const RAnalDynCCLoc *loc);
static int function_arg_var_cmp(const RAnalVar *a, const RAnalVar *b);
static char *function_param_string(const RAnalFunctionParam *param);
static char *get_type_data(Sdb *sdb_types, const char *type, const char *sname);
static void split_member_csv(char *values, const char **offset, const char **count);
static int dyncc_find_role(const RAnalDynCC *d, char tag);
static bool dyncc_parse_loc_seq(const char *s, const char *end, RAnalDynCCSeq *seq);
static bool dyncc_parse_ref(const char *s, const char *end, RAnalDynCCSlice *out);
static bool dyncc_role_tag(char tag);
static bool dyncc_slice_empty(const RAnalDynCCSlice *slice);
static bool dyncc_slice_eq(const RAnalDynCCSlice *slice, const char *s);
static int dyncc_parse_indexed_seq(RAnalDynCCSeq *seq, const char *s, const char *end, char prefix);
static bool dyncc_parse_loc(const char *s, const char *end, RAnalDynCCLoc *out);
static bool dyncc_parse_name(const char **sp, const char *end, RAnalDynCCSlice *out);
static const char *dyncc_range_startswith(const char *s, const char *end, const char *prefix);
static bool dyncc_set_indexed_seq(RAnalDynCCSeq *seq, char prefix, int base, int count, int delta);
static void fcn_context_slot_free(RAnalFcnSlot *slot);
static void fcn_context_callee_free(RAnalFcnCallee *callee);
static RRegItem *fcn_context_var_regitem(RAnal *anal, const RAnalVar *var);
static bool fcn_context_stack_offset(const RAnalFunction *fcn, const RAnalVar *var, st64 *offset);
static RAnalVar *fcn_context_find_register_home_source(RVecAnalVarPtr *rvars, RAnalVar *slot);
static int fcn_context_raw_register_arg_index(RAnal *anal, RAnalFunction *fcn, const RAnalVar *var);
static int fcn_context_register_arg_index(RAnal *anal, RAnalFunction *fcn, RVecAnalVarPtr *rvars, RAnalVar *target);
static RAnalFcnSlotRole fcn_context_classify_slot(const RAnalVar *var, RAnalVar *home_source);
static RAnalFcnSlot *fcn_context_collect_slot(RAnal *anal, const RAnalFcnContext *ctx, RAnalFunction *fcn, RAnalVar *var, RAnalVar *home_source, int arg_index);
static RAnalFunctionSignature *fcn_context_collect_signature(RAnalFunction *fcn);
static bool fcn_context_callee_symbol_is_imported(RAnal *anal, ut64 addr);
static char *fcn_context_callee_symbol_name(RAnal *anal, ut64 addr);
static RAnalFcnCalleeLinkage fcn_context_resolve_callee_linkage(RAnal *anal, ut64 addr);
static char *fcn_context_resolve_callee_name(RAnal *anal, ut64 addr);
static RAnalFunctionSignature *fcn_context_resolve_callee_signature(RAnal *anal, ut64 addr);
static bool fcn_context_has_callee(RList *callees, ut64 call_addr, ut64 addr);
static bool fcn_context_append_callee(RAnal *anal, RList *callees, ut64 call_addr, ut64 addr, RAnalCallTransfer transfer);
static const char *fcn_context_reloc_name(const RBinReloc *reloc);
static bool fcn_context_append_slot_callee(RAnal *anal, RList *callees, ut64 call_addr, ut64 slot, const RBinReloc *reloc);
static FcnContextTransferKind fcn_context_block_transfer(RAnal *anal, const RAnalSnapshotBlock *block, ut64 transfer_addr, ut64 *target, ut64 *memory_operand);
static bool fcn_context_offer_slot_callee(RAnal *anal, RList *callees, ut64 call_addr, ut64 slot);
static bool fcn_context_collect_slot_callees(RAnal *anal, RList *callees, const RAnalSnapshotBlock *block, ut64 transfer_addr, ut64 memory_operand, const RVecAnalRef *refs);
static bool fcn_context_collect_tail_callees(RAnal *anal, RList *callees, const RAnalFunctionImageSnapshot *image, const RVecAnalRef *refs);
static RList *fcn_context_collect_callees(RAnal *anal, const RAnalFunctionImageSnapshot *image);
static void function_image_snapshot_fini(RAnalFunctionImageSnapshot *image);
static int snapshot_successor_compare(const void *left, const void *right);
static int snapshot_block_compare(const void *left, const void *right);
static int snapshot_addr_compare(const void *left, const void *right);
static SnapshotTerminalFlow snapshot_terminal_flow(const RAnalOp *op, ut64 target);
static bool snapshot_block_sequential_jump_normalize(RAnal *anal, RAnalSnapshotBlock *block);
static bool snapshot_switch_cases_target(const RAnalSwitchOp *switch_op, ut64 addr);
static bool snapshot_block_successors_collect(const RAnalBlock *source, RAnalSnapshotBlock *block, size_t *total_successors, const RAnalFunctionSnapshotLimits *limits);
static int function_image_target_classify(const RAnalFunctionImageSnapshot *image, ut64 target);
static bool snapshot_addr_starts_function(RAnal *anal, ut64 addr);
static bool function_image_code_pointer_table_collect(RAnal *anal, RAnalFunctionImageSnapshot *image, ut64 addr, ut32 entry_size);
static bool function_image_code_pointer_tables_collect(RAnal *anal, RAnalFunctionImageSnapshot *image);
static bool function_image_string_literals_collect(RAnal *anal, RAnalFunctionImageSnapshot *image, const RAnalFunctionSnapshotLimits *limits);
static bool function_image_data_symbols_collect(RAnal *anal, RAnalFunctionImageSnapshot *image, const RAnalFunctionSnapshotLimits *limits);
static bool function_image_snapshot_collect(RAnal *anal, const RAnalFunction *fcn, const RAnalFunctionSnapshotLimits *limits, RAnalFunctionImageSnapshot *image, const char **reason);
static bool function_image_snapshot_equal(const RAnalFunctionImageSnapshot *left, const RAnalFunctionImageSnapshot *right);
static void snapshot_register_storage_fini(RAnalSnapshotRegisterStorage *storage);
static void function_interface_snapshot_fini(RAnalFunctionInterfaceSnapshot *interface);
static void snapshot_type_graph_fini(RAnalSnapshotTypeGraph *graph);
static void call_site_interface_snapshot_fini(RAnalCallSiteInterfaceSnapshot *interface);
static void r_anal_function_snapshot_free(RAnalFunctionSnapshot *snapshot);
static RAnalSnapshotReturnArity snapshot_signature_return_arity(const RAnalFunctionSignature *signature);
static ut64 function_snapshot_hash_signature(ut64 hash, const RAnalFunctionSignature *signature);
static ut64 function_snapshot_hash_base_types(ut64 hash, const RList *base_types);
static ut64 function_snapshot_hash_storage(ut64 hash, const RAnalSnapshotRegisterStorage *storage);
static ut64 function_snapshot_hash_interface(ut64 hash, const RAnalFunctionInterfaceSnapshot *interface);
static ut64 function_snapshot_hash_return_mechanism(ut64 hash, const RAnalSnapshotReturnMechanismView *mechanism);
static ut64 function_snapshot_hash_stack_allocation_contract(ut64 hash, const RAnalSnapshotStackAllocationContractView *contract);
static ut64 function_snapshot_hash_type_graph(ut64 hash, const RAnalSnapshotTypeGraph *graph);
static ut64 function_snapshot_hash_call_interface(ut64 hash, const RAnalCallSiteInterfaceSnapshot *interface);
static ut64 function_snapshot_hash_image(ut64 hash, const RAnalFunctionImageSnapshot *image);
static ut64 function_snapshot_hash(const RAnalFunctionSnapshot *snapshot);
static SnapshotStorageResult snapshot_register_storage_collect( RAnal *anal, const char *name, bool copy_name, RAnalSnapshotRegisterStorage *storage);
static bool snapshot_function_address_size(const RAnalFunction *fcn, ut32 *size);
static SnapshotStorageResult snapshot_return_address_storage_collect( RAnal *anal, const RAnalFunction *fcn, RAnalSnapshotRegisterStorage *storage);
static SnapshotStorageResult snapshot_stack_pointer_storage_collect( RAnal *anal, const RAnalFunction *fcn, RAnalSnapshotRegisterStorage *storage);
static bool snapshot_register_storage_resolve(RAnal *anal, const char *name, ut64 *offset, ut32 *size);
static bool snapshot_cc_argument_storage(RAnal *anal, const char *calling_convention, int index, int count, ut64 *offset, ut32 *size);
static bool snapshot_cc_maps_register_interface(RAnal *anal, const RAnalFunctionSignature *signature, const char *calling_convention);
static bool snapshot_promote_exact_dwarf_stack_homes( RAnal *anal, RAnalFunction *fcn, RAnalFcnContext *ctx, RAnalFunctionInterfaceSnapshot *interface, const char *calling_convention);
static bool snapshot_parameter_storages_overlap( const RAnalSnapshotParameter *parameters, size_t count);
static bool snapshot_register_storages_overlap( const RAnalSnapshotRegisterStorage *left, const RAnalSnapshotRegisterStorage *right);
static bool snapshot_register_storages_equal( const RAnalSnapshotRegisterStorage *left, const RAnalSnapshotRegisterStorage *right);
static bool snapshot_return_address_storage_overlaps_interface( const RAnalFunctionInterfaceSnapshot *interface, const RAnalFcnContext *ctx);
static bool snapshot_stack_pointer_storage_conflicts_interface( const RAnalFunctionInterfaceSnapshot *interface, const RAnalFcnContext *ctx);
static bool snapshot_stack_resources_complete(const RAnalFcnContext *ctx);
static bool snapshot_stack_slot_roles_complete( const RAnalFcnContext *ctx, const RAnalFunctionInterfaceSnapshot *interface);
static bool snapshot_convention_slots_collect( RAnal *anal, RAnalFunction *fcn, RAnalFunctionInterfaceSnapshot *interface);
static bool function_interface_snapshot_collect( RAnal *anal, RAnalFunction *fcn, RAnalFcnContext *ctx, RAnalFunctionInterfaceSnapshot *interface, const RAnalFunctionSnapshotLimits *limits);
static void snapshot_return_mechanism_collect(RAnal *anal, const RAnalFunction *fcn, const RAnalFcnContext *ctx, const RAnalFunctionInterfaceSnapshot *interface, RAnalSnapshotReturnMechanismView *view);
static bool snapshot_return_mechanism_equal(const RAnalSnapshotReturnMechanismView *a, const RAnalSnapshotReturnMechanismView *b);
static void snapshot_stack_allocation_contract_collect(RAnal *anal, const RAnalFunctionInterfaceSnapshot *interface, RAnalSnapshotStackAllocationContractView *view);
static bool snapshot_stack_allocation_contract_equal( const RAnalSnapshotStackAllocationContractView *a, const RAnalSnapshotStackAllocationContractView *b);
static bool snapshot_frame_pointer_storage_conflicts_interface( const RAnalSnapshotRegisterStorage *storage, const RAnalFunctionInterfaceSnapshot *interface, const RAnalFcnContext *ctx);
static bool snapshot_frame_pointer_storage_collect(RAnal *anal, const RAnalFunction *fcn, const RAnalFcnContext *ctx, const RAnalFunctionInterfaceSnapshot *interface, RAnalSnapshotRegisterStorage *storage);
static bool snapshot_frame_pointer_storage_equal( const RAnalSnapshotRegisterStorage *a, const RAnalSnapshotRegisterStorage *b);
static int snapshot_base_type_compare(const void *left, const void *right);
static bool snapshot_nullable_string_equal(const char *left, const char *right);
static bool snapshot_base_type_equal(const RAnalBaseType *left, const RAnalBaseType *right);
static bool snapshot_base_types_equal(const RList *left, const RList *right);
static bool snapshot_base_type_string_add(size_t *total, const char *string);
static bool snapshot_base_type_string_bytes(const RList *base_types, size_t *result);
static void snapshot_type_resolver_select_current_roots(Sdb *type_db, RList *base_types);
static bool snapshot_type_resolver_capture_cb(void *user, const char *name, const char *kind);
static RList *snapshot_type_resolver_capture(RAnal *anal, const RAnalFunctionSnapshotLimits *limits);
static bool snapshot_arch_char_kind(const char *arch, RAnalSnapshotTypeKind *kind);
static const RAnalBaseType *snapshot_type_find_unique_base( const RList *base_types, const char *name, RAnalBaseTypeKind kind, bool *ambiguous);
static const RAnalBaseType *snapshot_type_find_bare_base( const SnapshotTypeGraphBuilder *builder, const char *name, bool *ambiguous);
static void snapshot_type_strip_qualifiers(char *spec);
static char *snapshot_type_member_element_spec(const char *spec, ut64 *count);
static bool snapshot_type_spec_rejected(const char *spec);
static SnapshotTypeGraphResult snapshot_type_unalias( const SnapshotTypeGraphBuilder *builder, const char *type, char **result);
static bool snapshot_type_integer_width_supported(ut64 bits);
static SnapshotIntegerSyntax snapshot_type_integer_syntax(const char *spec);
static SnapshotTypeGraphResult snapshot_type_integer_spec( const SnapshotTypeGraphBuilder *builder, const char *type, RAnalSnapshotTypeKind *kind, ut64 *bits);
static SnapshotTypeGraphResult snapshot_type_add_integer( SnapshotTypeGraphBuilder *builder, const char *type, RAnalSnapshotTypeId *result_id);
static bool snapshot_type_align_up(ut64 value, ut64 alignment, ut64 *result);
static SnapshotTypeGraphResult snapshot_type_resolve_struct( const SnapshotTypeGraphBuilder *builder, const char *type, const RAnalBaseType **result_base);
static SnapshotTypeGraphResult snapshot_type_add_struct( SnapshotTypeGraphBuilder *builder, const char *type, RAnalSnapshotTypeId *result_id);
static SnapshotTypeGraphResult snapshot_type_add_pointer( SnapshotTypeGraphBuilder *builder, const char *type, RAnalSnapshotTypeId *result_id);
static SnapshotTypeGraphResult snapshot_type_add_root( SnapshotTypeGraphBuilder *builder, const char *type, RAnalSnapshotTypeId *result_id);
static bool snapshot_type_carrier_project( const RAnalSnapshotTypeGraph *graph, RAnalSnapshotTypeId type_id, const RAnalSnapshotRegisterStorage *storage, RAnalSnapshotCarrierProjection *projection);
static SnapshotTypeGraphResult function_type_graph_snapshot_collect( RAnal *anal, const RAnalFcnContext *ctx, RAnalFunctionSnapshot *snapshot, const RAnalFunctionSnapshotLimits *limits);
static int call_site_interface_snapshot_compare(const void *left, const void *right);
static bool call_site_interface_snapshot_collect_one( RAnal *anal, const RAnalFcnCallee *callee, RAnalCallSiteInterfaceSnapshot *interface, const RAnalFunctionSnapshotLimits *limits);
static bool call_site_interfaces_snapshot_collect( RAnal *anal, const RAnalFcnContext *ctx, RAnalFunctionSnapshot *snapshot, const RAnalFunctionSnapshotLimits *limits);
static bool snapshot_string_budget_add(const char *string, size_t limit, size_t *used);
static bool snapshot_signature_budget_add(const RAnalFunctionSignature *signature, const RAnalFunctionSnapshotLimits *limits, size_t *items, size_t *strings);
static bool snapshot_context_within_limits(const RAnalFunctionSnapshot *snapshot, const RAnalFunctionSnapshotLimits *limits);
static bool snapshot_interface_within_limits(const RAnalFunctionSnapshot *snapshot, const RAnalFunctionSnapshotLimits *limits);
static bool snapshot_limits_valid(const RAnalFunctionSnapshotLimits *limits);
static const RArchConfig *function_snapshot_active_arch_config(const RAnal *anal);
static bool function_snapshot_machine_tuple_collect(RAnalFunctionSnapshot *snapshot, const RAnal *anal);
static bool function_snapshot_machine_tuple_is_current(const RAnalFunctionSnapshot *snapshot, const RAnal *anal);
static RAnalFunctionSnapshot *function_snapshot_collect_with_limits_unlocked(RAnal *anal, RAnalFunction *fcn, const RAnalFunctionSnapshotLimits *limits, const char **reason);
static void r_anal_function_snapshot_limits_default(RAnalFunctionSnapshotLimits *limits);
static void function_snapshot_collect_callees_unlocked(RAnal *anal, RAnalFunctionSnapshot *snapshot, const RAnalFunctionSnapshotLimits *limits);
static RAnalFunctionSnapshot *r_anal_function_snapshot_collect_with_limits(RAnal *anal, RAnalFunction *fcn, const RAnalFunctionSnapshotLimits *limits, const char **reason);
static RAnalFunctionSnapshot *r_anal_function_snapshot_collect_bounded(RAnal *anal, RAnalFunction *fcn, const char **reason);
static RList *r_anal_types_snapshot_with_limits(RAnal *anal, const RAnalFunctionSnapshotLimits *limits);
static ut64 r_anal_types_context_hash_from_snapshot(RAnal *anal, const RList *types, ut64 type_dirty_epoch);


/* ---- moved from libr/anal/function.c ---- */
static void fcn_context_slot_free(RAnalFcnSlot *slot) {
	if (!slot) {
		return;
	}
	free (slot->name);
	free (slot->type);
	free (slot->base_name);
	free (slot->home_reg);
	free (slot);
}
static void fcn_context_callee_free(RAnalFcnCallee *callee) {
	if (!callee) {
		return;
	}
	free (callee->name);
	r_anal_function_signature_free (callee->signature);
	free (callee);
}
static RRegItem *fcn_context_var_regitem(RAnal *anal, const RAnalVar *var) {
	if (R_STR_ISNOTEMPTY (var->regname)) {
		return r_reg_get (anal->reg, var->regname, -1);
	}
	if (var->kind == R_ANAL_VAR_KIND_REG) {
		return r_reg_index_get (anal->reg, R_ABS (var->delta));
	}
	return NULL;
}
static bool fcn_context_stack_offset(const RAnalFunction *fcn, const RAnalVar *var, st64 *offset) {
	R_RETURN_VAL_IF_FAIL (fcn && var && offset, false);
	switch (var->kind) {
	case R_ANAL_VAR_KIND_BPV:
		return !r_add_overflow ((st64)var->delta, fcn->bp_off, offset);
	case R_ANAL_VAR_KIND_SPV:
		*offset = var->delta;
		return true;
	default:
		*offset = var->delta;
		return false;
	}
}
static RAnalVar *fcn_context_find_register_home_source(RVecAnalVarPtr *rvars, RAnalVar *slot) {
	if (!rvars) {
		return NULL;
	}
	RAnalVar **it;
	R_VEC_FOREACH (rvars, it) {
		RAnalVar *var = *it;
		if (var && var->isarg && var->kind == R_ANAL_VAR_KIND_REG) {
			RAnalVar *dst = r_anal_var_get_dst_var (var);
			if (dst == slot) {
				return var;
			}
		}
	}
	return NULL;
}
static int fcn_context_raw_register_arg_index(RAnal *anal, RAnalFunction *fcn, const RAnalVar *var) {
	if (!var || !var->isarg || var->kind != R_ANAL_VAR_KIND_REG
		|| R_STR_ISEMPTY (fcn->callconv)) {
		return -1;
	}
	RRegItem *reg = fcn_context_var_regitem (anal, var);
	if (!reg) {
		return -1;
	}
	const int maximum = r_anal_cc_max_arg (anal, fcn->callconv);
	int index;
	for (index = 0; index < maximum; index++) {
		const char *location = r_anal_cc_argloc (
			anal, fcn->callconv, index, 0, 0);
		if (location && r_anal_cc_location_uses (anal, location, reg->name)) {
			r_unref (reg);
			return index;
		}
	}
	r_unref (reg);
	return -1;
}
static int fcn_context_register_arg_index(RAnal *anal, RAnalFunction *fcn, RVecAnalVarPtr *rvars, RAnalVar *target) {
	const int raw_index = fcn_context_raw_register_arg_index (anal, fcn, target);
	if (raw_index < 0 || !rvars) {
		return -1;
	}
	int dense_index = 0;
	bool found = false;
	RAnalVar **it;
	R_VEC_FOREACH (rvars, it) {
		RAnalVar *var = *it;
		const int other_index = fcn_context_raw_register_arg_index (anal, fcn, var);
		if (var == target) {
			found = true;
			continue;
		}
		if (other_index >= 0 && (other_index < raw_index
				|| (other_index == raw_index && !found))) {
			dense_index++;
		}
	}
	return found? dense_index: -1;
}
static RAnalFcnSlotRole fcn_context_classify_slot(const RAnalVar *var, RAnalVar *home_source) {
	R_RETURN_VAL_IF_FAIL (var, R_ANAL_FCN_SLOT_UNKNOWN);
	if (home_source) {
		return R_ANAL_FCN_SLOT_HOME;
	}
	if (var->isarg) {
		return R_ANAL_FCN_SLOT_ARG;
	}
	if (var->kind == R_ANAL_VAR_KIND_BPV || var->kind == R_ANAL_VAR_KIND_SPV) {
		return R_ANAL_FCN_SLOT_LOCAL;
	}
	return R_ANAL_FCN_SLOT_UNKNOWN;
}
static RAnalFcnSlot *fcn_context_collect_slot(RAnal *anal, const RAnalFcnContext *ctx, RAnalFunction *fcn, RAnalVar *var, RAnalVar *home_source, int arg_index) {
	const RAnalFunctionParam *signature_param = NULL;

	R_RETURN_VAL_IF_FAIL (anal && ctx && fcn && var, NULL);
	RAnalFcnSlot *slot = R_NEW0 (RAnalFcnSlot);
	if (R_STR_ISNOTEMPTY (var->name)) {
		slot->name = strdup (var->name);
	}
	if (R_STR_ISNOTEMPTY (var->type)) {
		slot->type = strdup (var->type);
	}
	switch (var->kind) {
	case R_ANAL_VAR_KIND_BPV:
		slot->base = R_ANAL_FCN_BASE_BP;
		break;
	case R_ANAL_VAR_KIND_SPV:
		slot->base = R_ANAL_FCN_BASE_SP;
		break;
	default:
		slot->base = R_ANAL_FCN_BASE_NAMED;
		break;
	}
	const RRegAlias base_alias = slot->base == R_ANAL_FCN_BASE_BP
		? R_REG_ALIAS_BP: R_REG_ALIAS_SP;
	const char *base_name = slot->base == R_ANAL_FCN_BASE_NAMED
		? NULL: r_reg_alias_getname (anal->reg, base_alias);
	if (R_STR_ISNOTEMPTY (base_name)) {
		RRegItem *base_reg = r_reg_get (anal->reg, base_name, -1);
		if (base_reg && base_reg->offset >= 0 && !(base_reg->offset % 8)
			&& base_reg->size > 0
			&& !(base_reg->size % 8) && base_reg->size / 8 <= UT32_MAX) {
			slot->base_name = strdup (base_name);
			if (!slot->base_name) {
				r_unref (base_reg);
				fcn_context_slot_free (slot);
				return NULL;
			}
			slot->base_offset = (ut64)(base_reg->offset / 8);
			slot->base_size = (ut32)(base_reg->size / 8);
		}
		r_unref (base_reg);
	}
	slot->offset_valid = fcn_context_stack_offset (fcn, var, &slot->offset);
	slot->role = fcn_context_classify_slot (var, home_source);

	if (home_source) {
		signature_param = (ctx->signature && arg_index >= 0)? r_list_get_n (ctx->signature->params, arg_index): NULL;
		slot->arg_index = arg_index;
		RRegItem *home_reg = fcn_context_var_regitem (anal, home_source);
		if (home_reg && home_reg->offset >= 0 && !(home_reg->offset % 8)
			&& home_reg->size > 0
			&& !(home_reg->size % 8) && home_reg->size / 8 <= UT32_MAX) {
			slot->home_reg = strdup (r_str_get (home_reg->name));
			if (!slot->home_reg) {
				r_unref (home_reg);
				fcn_context_slot_free (slot);
				return NULL;
			}
			slot->home_reg_offset = (ut64)(home_reg->offset / 8);
			slot->home_reg_size = (ut32)(home_reg->size / 8);
		}
		r_unref (home_reg);
		if (!slot->type && signature_param && R_STR_ISNOTEMPTY (signature_param->type)) {
			slot->type = strdup (signature_param->type);
		}
	} else if (var->isarg) {
		slot->arg_index = arg_index;
		if (arg_index >= 0) {
			signature_param = ctx->signature? r_list_get_n (ctx->signature->params, arg_index): NULL;
			if (!slot->type && signature_param && R_STR_ISNOTEMPTY (signature_param->type)) {
				slot->type = strdup (signature_param->type);
			}
		}
	} else {
		slot->arg_index = -1;
	}
	if (R_STR_ISNOTEMPTY (slot->type)) {
		ut64 bits = r_anal_type_bitsize (anal, slot->type);
		if (bits && !(bits % 8) && bits / 8 <= UT32_MAX) {
			slot->size = (ut32)(bits / 8);
		}
	}

	if ((R_STR_ISNOTEMPTY (var->name) && !slot->name)
		|| (R_STR_ISNOTEMPTY (var->type) && !slot->type)) {
		fcn_context_slot_free (slot);
		return NULL;
	}
	return slot;
}
static RAnalFunctionSignature *fcn_context_collect_signature(RAnalFunction *fcn) {
	R_RETURN_VAL_IF_FAIL (fcn, NULL);
	RAnalFunctionSignature *signature = r_anal_function_get_signature_current (fcn);
	const char *fcncc = fcn->callconv;
	if (signature || (!R_STR_ISNOTEMPTY (fcncc) && !fcn->is_noreturn)) {
		return signature;
	}
	signature = R_NEW0 (RAnalFunctionSignature);
	signature->params = r_list_new ();
	if (!signature->params) {
		r_anal_function_signature_free (signature);
		return NULL;
	}
	if (R_STR_ISNOTEMPTY (fcncc)) {
		signature->callconv = strdup (fcncc);
		if (!signature->callconv) {
			r_anal_function_signature_free (signature);
			return NULL;
		}
	}
	signature->noreturn = fcn->is_noreturn;
	return signature;
}
static bool fcn_context_callee_symbol_is_imported(RAnal *anal, ut64 addr) {
	RBinSymbol *sym;
	if (!anal || !anal->binb.bin || !anal->binb.get_symbol_at) {
		return false;
	}
	sym = anal->binb.get_symbol_at (anal->binb.bin, addr);
	return sym && sym->is_imported;
}
static char *fcn_context_callee_symbol_name(RAnal *anal, ut64 addr) {
	RBinSymbol *sym;
	const char *name;
	if (!anal || !anal->binb.bin || !anal->binb.get_symbol_at) {
		return NULL;
	}
	sym = anal->binb.get_symbol_at (anal->binb.bin, addr);
	if (!sym || !sym->name) {
		return NULL;
	}
	name = sym->name->name;
	if (!name) {
		name = sym->name->oname;
	}
	if (!name) {
		name = sym->name->fname;
	}
	return R_STR_ISNOTEMPTY (name)? strdup (name): NULL;
}
static RAnalFcnCalleeLinkage fcn_context_resolve_callee_linkage(RAnal *anal, ut64 addr) {
	RAnalFunction *callee_fcn;
	R_RETURN_VAL_IF_FAIL (anal, R_ANAL_FCN_CALLEE_UNKNOWN);
	if (fcn_context_callee_symbol_is_imported (anal, addr)) {
		return R_ANAL_FCN_CALLEE_IMPORTED;
	}
	callee_fcn = r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
	if (!callee_fcn) {
		return R_ANAL_FCN_CALLEE_UNKNOWN;
	}
	if (callee_fcn->type & R_ANAL_FCN_TYPE_IMP) {
		return R_ANAL_FCN_CALLEE_IMPORTED;
	}
	return R_ANAL_FCN_CALLEE_INTERNAL;
}
static char *fcn_context_resolve_callee_name(RAnal *anal, ut64 addr) {
	RAnalFunction *callee_fcn;
	R_RETURN_VAL_IF_FAIL (anal, NULL);
	callee_fcn = r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
	if (callee_fcn && R_STR_ISNOTEMPTY (callee_fcn->name)) {
		return strdup (callee_fcn->name);
	}
	return fcn_context_callee_symbol_name (anal, addr);
}
static RAnalFunctionSignature *fcn_context_resolve_callee_signature(RAnal *anal, ut64 addr) {
	RAnalFunction *callee_fcn;
	R_RETURN_VAL_IF_FAIL (anal, NULL);
	callee_fcn = r_anal_get_fcn_in (anal, addr, R_ANAL_FCN_TYPE_ANY);
	return callee_fcn? r_anal_function_get_signature_current (callee_fcn): NULL;
}
static bool fcn_context_has_callee(RList *callees, ut64 call_addr, ut64 addr) {
	RListIter *iter;
	RAnalFcnCallee *callee;
	r_list_foreach (callees, iter, callee) {
		if (callee && callee->call_addr == call_addr && callee->addr == addr) {
			return true;
		}
	}
	return false;
}
static bool fcn_context_append_callee(RAnal *anal, RList *callees, ut64 call_addr, ut64 addr, RAnalCallTransfer transfer) {
	RAnalFcnCallee *callee;
	R_RETURN_VAL_IF_FAIL (anal && callees, false);
	if (addr == UT64_MAX || fcn_context_has_callee (callees, call_addr, addr)) {
		return true;
	}
	callee = R_NEW0 (RAnalFcnCallee);
	if (!callee) {
		return false;
	}
	callee->call_addr = call_addr;
	callee->addr = addr;
	callee->name = fcn_context_resolve_callee_name (anal, addr);
	callee->linkage = fcn_context_resolve_callee_linkage (anal, addr);
	callee->signature = fcn_context_resolve_callee_signature (anal, addr);
	callee->transfer = transfer;
	r_list_append (callees, callee);
	return true;
}
static const char *fcn_context_reloc_name(const RBinReloc *reloc) {
	const RBinName *name = reloc->import? reloc->import->name
		: reloc->symbol? reloc->symbol->name: NULL;
	if (!name) {
		return NULL;
	}
	if (R_STR_ISNOTEMPTY (name->name)) {
		return name->name;
	}
	if (R_STR_ISNOTEMPTY (name->oname)) {
		return name->oname;
	}
	return R_STR_ISNOTEMPTY (name->fname)? name->fname: NULL;
}
static bool fcn_context_append_slot_callee(RAnal *anal, RList *callees, ut64 call_addr, ut64 slot, const RBinReloc *reloc) {
	RAnalFcnCallee *callee;
	R_RETURN_VAL_IF_FAIL (anal && callees && reloc, false);
	const char *name = fcn_context_reloc_name (reloc);
	if (!name || fcn_context_has_callee (callees, call_addr, slot)) {
		return true;
	}
	callee = R_NEW0 (RAnalFcnCallee);
	if (!callee) {
		return false;
	}
	callee->call_addr = call_addr;
	callee->addr = slot;
	callee->name = strdup (name);
	if (!callee->name) {
		fcn_context_callee_free (callee);
		return false;
	}
	callee->linkage = reloc->import? R_ANAL_FCN_CALLEE_IMPORTED
		: reloc->symbol? R_ANAL_FCN_CALLEE_INTERNAL: R_ANAL_FCN_CALLEE_UNKNOWN;
	callee->signature = r_anal_function_signature_from_type_name (anal, name);
	callee->transfer = R_ANAL_CALL_TRANSFER_TAIL_SLOT;
	r_list_append (callees, callee);
	return true;
}
static FcnContextTransferKind fcn_context_block_transfer(RAnal *anal, const RAnalSnapshotBlock *block, ut64 transfer_addr, ut64 *target, ut64 *memory_operand) {
	RAnalOp op;
	*target = UT64_MAX;
	*memory_operand = UT64_MAX;
	const ut64 offset = transfer_addr - block->addr;
	if (offset >= block->size || block->size - offset > INT_MAX) {
		return FCN_TRANSFER_NONE;
	}
	r_anal_op_init (&op);
	const int decoded = r_anal_op (anal, &op, transfer_addr, block->bytes + offset,
		(int)(block->size - offset), R_ARCH_OP_MASK_BASIC);
	const ut32 base = op.type & 0xffff;
	const bool conditional = (op.type & R_ANAL_OP_TYPE_COND) != 0;
	const bool through_memory = base == R_ANAL_OP_TYPE_JMP && (op.type & R_ANAL_OP_TYPE_MEM) != 0;
	FcnContextTransferKind kind = FCN_TRANSFER_NONE;
	if (decoded > 0 && !conditional) {
		if (base == R_ANAL_OP_TYPE_UJMP || through_memory) {
			kind = FCN_TRANSFER_VALUE_JUMP;
			if (through_memory) {
				*memory_operand = op.ptr;
			}
		} else if (base == R_ANAL_OP_TYPE_JMP && op.jump != UT64_MAX) {
			kind = FCN_TRANSFER_DIRECT_JUMP;
			*target = op.jump;
		}
	}
	r_anal_op_fini (&op);
	return kind;
}
static bool fcn_context_offer_slot_callee(RAnal *anal, RList *callees, ut64 call_addr, ut64 slot) {
	if (slot == UT64_MAX) {
		return true;
	}
	const RBinReloc *reloc = anal->binb.get_reloc_at (anal->binb.bin, slot);
	return !reloc || fcn_context_append_slot_callee (anal, callees, call_addr, slot, reloc);
}
static bool fcn_context_collect_slot_callees(RAnal *anal, RList *callees, const RAnalSnapshotBlock *block, ut64 transfer_addr, ut64 memory_operand, const RVecAnalRef *refs) {
	if (!anal->binb.bin || !anal->binb.get_reloc_at) {
		return true;
	}
	if (!fcn_context_offer_slot_callee (anal, callees, transfer_addr, memory_operand)) {
		return false;
	}
	if (!refs) {
		return true;
	}
	const ut64 block_end = block->addr + block->size;
	const size_t len = RVecAnalRef_length (refs);
	size_t i;
	for (i = 0; i < len; i++) {
		const RAnalRef *ref = RVecAnalRef_at (refs, i);
		if (!ref || ref->at < block->addr || ref->at >= block_end
			|| R_ANAL_REF_TYPE_MASK (ref->type) != R_ANAL_REF_TYPE_DATA) {
			continue;
		}
		if (!fcn_context_offer_slot_callee (anal, callees, transfer_addr, ref->addr)) {
			return false;
		}
	}
	return true;
}
static bool fcn_context_collect_tail_callees(RAnal *anal, RList *callees, const RAnalFunctionImageSnapshot *image, const RVecAnalRef *refs) {
	size_t block_index;
	for (block_index = 0; block_index < image->num_blocks; block_index++) {
		const RAnalSnapshotBlock *block = &image->blocks[block_index];
		RAnalBlock *bb = r_anal_get_block_at (anal, block->addr);
		if (!bb || bb->size != block->size || bb->ninstr < 1) {
			continue;
		}
		const ut64 transfer_addr = r_anal_bb_opaddr_i (bb, bb->ninstr - 1);
		if (transfer_addr < block->addr || transfer_addr >= block->addr + block->size) {
			continue;
		}
		size_t successor_index;
		for (successor_index = 0; successor_index < block->num_successors; successor_index++) {
			const RAnalSnapshotSuccessor *successor = &block->successors[successor_index];
			if (successor->kind != R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT
				|| function_image_target_classify (image, successor->target_addr) != 0
				|| !r_anal_get_function_at (anal, successor->target_addr)) {
				continue;
			}
			if (!fcn_context_append_callee (anal, callees, transfer_addr,
					successor->target_addr, R_ANAL_CALL_TRANSFER_TAIL_JUMP)) {
				return false;
			}
		}
		if (block->switch_addr != UT64_MAX || !block->bytes) {
			continue;
		}
		// A tail jump usually records no successor to have found above. The
		// function walk stops at a jump whose target is a named function or an
		// import, and it stops before it stores the edge, so the block ends
		// with an edge the analysis declined to keep rather than with none.
		// The instruction still names the target, so it is decoded and the
		// function map asked directly.
		ut64 direct_target = UT64_MAX;
		ut64 memory_operand = UT64_MAX;
		const FcnContextTransferKind kind = fcn_context_block_transfer (
			anal, block, transfer_addr, &direct_target, &memory_operand);
		if (kind == FCN_TRANSFER_DIRECT_JUMP) {
			if (function_image_target_classify (image, direct_target) == 0
				&& r_anal_get_function_at (anal, direct_target)
				&& !fcn_context_append_callee (anal, callees, transfer_addr,
					direct_target, R_ANAL_CALL_TRANSFER_TAIL_JUMP)) {
				return false;
			}
			continue;
		}
		if (kind != FCN_TRANSFER_VALUE_JUMP || block->num_successors) {
			continue;
		}
		if (!fcn_context_collect_slot_callees (anal, callees, block, transfer_addr,
				memory_operand, refs)) {
			return false;
		}
	}
	return true;
}
static RList *fcn_context_collect_callees(RAnal *anal, const RAnalFunctionImageSnapshot *image) {
	RVecAnalRef *refs;
	RList *callees;
	size_t i, len;

	R_RETURN_VAL_IF_FAIL (anal && image, NULL);
	callees = r_list_newf ((RListFree)fcn_context_callee_free);
	if (!callees) {
		return NULL;
	}
	refs = r_anal_refs_get (anal, UT64_MAX);
	if (refs) {
		len = RVecAnalRef_length (refs);
		for (i = 0; i < len; i++) {
			RAnalRef *ref = RVecAnalRef_at (refs, i);
			if (!ref || R_ANAL_REF_TYPE_MASK (ref->type) != R_ANAL_REF_TYPE_CALL
				|| function_image_target_classify (image, ref->at) == 0) {
				continue;
			}
			if (!fcn_context_append_callee (anal, callees, ref->at, ref->addr,
					R_ANAL_CALL_TRANSFER_CALL)) {
				RVecAnalRef_free (refs);
				r_list_free (callees);
				return NULL;
			}
		}
	}
	if (!fcn_context_collect_tail_callees (anal, callees, image, refs)) {
		RVecAnalRef_free (refs);
		r_list_free (callees);
		return NULL;
	}
	RVecAnalRef_free (refs);
	return callees;
}
static void function_image_snapshot_fini(RAnalFunctionImageSnapshot *image) {
	if (!image) {
		return;
	}
	size_t i;
	for (i = 0; i < image->num_blocks; i++) {
		free (image->blocks[i].bytes);
		free (image->blocks[i].successors);
	}
	free (image->blocks);
	free (image->external_exits);
	{
		size_t literal;
		for (literal = 0; literal < image->num_string_literals; literal++) {
			free (image->string_literals[literal].text);
		}
		free (image->string_literals);
		size_t symbol;
		for (symbol = 0; symbol < image->num_data_symbols; symbol++) {
			free (image->data_symbols[symbol].name);
			free (image->data_symbols[symbol].type_name);
		}
		free (image->data_symbols);
		size_t table;
		for (table = 0; table < image->num_code_pointer_tables; table++) {
			free (image->code_pointer_tables[table].targets);
		}
		free (image->code_pointer_tables);
	}
	memset (image, 0, sizeof (*image));
}
static int snapshot_successor_compare(const void *left, const void *right) {
	const RAnalSnapshotSuccessor *a = left;
	const RAnalSnapshotSuccessor *b = right;
	if (a->kind != b->kind) {
		return a->kind < b->kind? -1: 1;
	}
	if (a->case_value != b->case_value) {
		return a->case_value < b->case_value? -1: 1;
	}
	if (a->target_addr != b->target_addr) {
		return a->target_addr < b->target_addr? -1: 1;
	}
	return 0;
}
static int snapshot_block_compare(const void *left, const void *right) {
	const RAnalSnapshotBlock *a = left;
	const RAnalSnapshotBlock *b = right;
	if (a->addr != b->addr) {
		return a->addr < b->addr? -1: 1;
	}
	if (a->size != b->size) {
		return a->size < b->size? -1: 1;
	}
	return 0;
}
static int snapshot_addr_compare(const void *left, const void *right) {
	const ut64 a = *(const ut64 *)left;
	const ut64 b = *(const ut64 *)right;
	return a == b? 0: a < b? -1: 1;
}
static SnapshotTerminalFlow snapshot_terminal_flow(const RAnalOp *op, ut64 target) {
	const int type = op->type & R_ANAL_OP_TYPE_MASK;
	if (op->type == R_ANAL_OP_TYPE_JMP) {
		return op->jump == target
			? SNAPSHOT_TERMINAL_DIRECT: SNAPSHOT_TERMINAL_REJECT;
	}
	// An unconditional transfer to an address the analysis could not resolve
	// exits the block without naming where it goes, so a recorded successor is
	// a placeholder rather than something the instruction supports.
	if (!(op->type & R_ANAL_OP_TYPE_COND)
		&& (type == R_ANAL_OP_TYPE_UJMP
			|| type == R_ANAL_OP_TYPE_TRAP
			|| type == R_ANAL_OP_TYPE_ILL
			|| type == R_ANAL_OP_TYPE_UNK
			|| type == R_ANAL_OP_TYPE_SWI)) {
		return SNAPSHOT_TERMINAL_UNKNOWN_EXIT;
	}
	switch (type) {
	case R_ANAL_OP_TYPE_JMP:
	case R_ANAL_OP_TYPE_UJMP:
	case R_ANAL_OP_TYPE_CJMP:
	case R_ANAL_OP_TYPE_UCJMP:
	case R_ANAL_OP_TYPE_RET:
	case R_ANAL_OP_TYPE_CRET:
	case R_ANAL_OP_TYPE_TRAP:
	case R_ANAL_OP_TYPE_ILL:
	case R_ANAL_OP_TYPE_UNK:
	case R_ANAL_OP_TYPE_SWI:
		return SNAPSHOT_TERMINAL_REJECT;
	default:
		return op->eob? SNAPSHOT_TERMINAL_REJECT: SNAPSHOT_TERMINAL_SEQUENTIAL;
	}
}
static bool snapshot_block_sequential_jump_normalize(RAnal *anal, RAnalSnapshotBlock *block) {
	R_RETURN_VAL_IF_FAIL (anal && block, false);
	if (block->switch_addr != UT64_MAX || block->num_successors != 1) {
		return true;
	}
	RAnalSnapshotSuccessor *successor = block->successors;
	if (successor->kind != R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT
		|| successor->target_addr != block->addr + block->size) {
		return true;
	}
	RArchSession *live = R_UNWRAP3 (anal, arch, session);
	if (!live || !live->config || !live->plugin) {
		return false;
	}
	RArchConfig *config = r_arch_config_clone (live->config);
	RArchSession *decoder = config
		? r_arch_session (anal->arch, config, live->plugin): NULL;
	r_arch_config_free (config);
	if (!decoder) {
		return false;
	}
	SnapshotTerminalFlow delayed_flow = SNAPSHOT_TERMINAL_SEQUENTIAL;
	int delay_remaining = 0;
	size_t offset = 0;
	while (offset < block->size) {
		RAnalOp op = {0};
		const size_t remaining = (size_t)block->size - offset;
		const ut64 addr = block->addr + offset;
		const int codealign = decoder->config->codealign;
		const RAnalOpMask mask = R_ARCH_OP_MASK_BASIC
			| (anal->opt.stateful? R_ARCH_OP_MASK_STATEFUL: 0);
		r_anal_op_init (&op);
		const bool decoded = (codealign <= 1 || !(addr % codealign))
			&& r_anal_op_set_bytes (&op, addr, block->bytes + offset, (int)remaining)
			&& r_arch_session_decode (decoder, &op, mask);
		const int length = op.size;
		if (!decoded || length < 1 || (size_t)length > remaining) {
			r_anal_op_fini (&op);
			goto fail;
		}
		offset += (size_t)length;
		const SnapshotTerminalFlow flow = snapshot_terminal_flow (
			&op, successor->target_addr);
		if (delay_remaining) {
			if (op.delay > 0 || flow != SNAPSHOT_TERMINAL_SEQUENTIAL) {
				r_anal_op_fini (&op);
				goto fail;
			}
			delay_remaining--;
			if (!delay_remaining && offset != block->size) {
				r_anal_op_fini (&op);
				goto fail;
			}
		} else if (op.delay > 0) {
			if (flow == SNAPSHOT_TERMINAL_SEQUENTIAL || offset == block->size) {
				r_anal_op_fini (&op);
				goto fail;
			}
			delayed_flow = flow;
			delay_remaining = op.delay;
		} else if (flow != SNAPSHOT_TERMINAL_SEQUENTIAL && offset != block->size) {
			r_anal_op_fini (&op);
			goto fail;
		} else if (offset == block->size) {
			delayed_flow = flow;
		}
		r_anal_op_fini (&op);
	}
	if (delay_remaining || delayed_flow == SNAPSHOT_TERMINAL_REJECT) {
		goto fail;
	}
	if (delayed_flow == SNAPSHOT_TERMINAL_UNKNOWN_EXIT) {
		// The recorded edge to the next address is not something this
		// terminator does. Drop it rather than capture a transfer the
		// instruction contradicts, and rather than refuse the whole function
		// over one unresolved branch.
		R_FREE (block->successors);
		block->num_successors = 0;
		r_unref (decoder);
		return true;
	}
	if (delayed_flow == SNAPSHOT_TERMINAL_SEQUENTIAL) {
		successor->kind = R_ANAL_SNAPSHOT_SUCCESSOR_FALLTHROUGH;
	}
	r_unref (decoder);
	return true;

fail:
	r_unref (decoder);
	return false;
}
static bool snapshot_switch_cases_target(const RAnalSwitchOp *switch_op, ut64 addr) {
	RListIter *iter;
	RAnalCaseOp *case_op;
	r_list_foreach (switch_op->cases, iter, case_op) {
		if (case_op && case_op->jump == addr) {
			return true;
		}
	}
	return false;
}
static bool snapshot_block_successors_collect(const RAnalBlock *source, RAnalSnapshotBlock *block, size_t *total_successors, const RAnalFunctionSnapshotLimits *limits) {
	size_t count = 0;
	ut64 default_addr = UT64_MAX;
	bool jump_is_distinct = false;
	if (source->switch_op) {
		const RAnalSwitchOp *switch_op = source->switch_op;
		const int listed_cases = switch_op->cases? r_list_length (switch_op->cases): 0;
		if (listed_cases <= 0) {
			return false;
		}
		// A snapshot describes the graph the function analysis built, not the
		// architecture metadata it was built from, so the block fail edge is the
		// authority for the default target and switch_op->def_val is only a
		// cross-check. A switch with no default is a complete description rather
		// than a missing one, so its absence is not a failure; the two views
		// disagreeing is, because then the block has no single default.
		default_addr = source->fail;
		if (default_addr != UT64_MAX && switch_op->def_val != UT64_MAX
			&& switch_op->def_val != default_addr) {
			return false;
		}
		count = (size_t)listed_cases;
		if (default_addr != UT64_MAX
			&& r_add_overflow_size_t (count, 1, &count)) {
			return false;
		}
		// Some architectures leave the linear flow edge on a dispatch block in
		// addition to the case list. Keep it only when it names a target the
		// case list and the default do not already cover.
		if (source->jump != UT64_MAX && source->jump != default_addr
			&& !snapshot_switch_cases_target (switch_op, source->jump)) {
			jump_is_distinct = true;
			if (r_add_overflow_size_t (count, 1, &count)) {
				return false;
			}
		}
		block->switch_addr = switch_op->jump_addr != UT64_MAX
			? switch_op->jump_addr: switch_op->addr;
		const ut64 block_end = source->addr + source->size;
		if (block->switch_addr < source->addr || block->switch_addr >= block_end) {
			return false;
		}
	} else {
		block->switch_addr = UT64_MAX;
		count = (source->jump != UT64_MAX? 1: 0)
			+ (source->fail != UT64_MAX? 1: 0);
	}
	size_t next_total;
	if (r_add_overflow_size_t (*total_successors, count, &next_total)
		|| next_total > limits->max_function_successors) {
		return false;
	}
	*total_successors = next_total;
	if (!count) {
		return true;
	}
	size_t allocation_size;
	if (r_mul_overflow (count, sizeof (RAnalSnapshotSuccessor), &allocation_size)) {
		return false;
	}
	block->successors = calloc (1, allocation_size);
	if (!block->successors) {
		return false;
	}
	block->num_successors = count;
	if (source->switch_op) {
		RListIter *iter;
		RAnalCaseOp *case_op;
		size_t index = 0;
		r_list_foreach (source->switch_op->cases, iter, case_op) {
			if (!case_op || case_op->jump == UT64_MAX || index >= count) {
				return false;
			}
			block->successors[index++] = (RAnalSnapshotSuccessor) {
				.kind = R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_CASE,
				.target_addr = case_op->jump,
				.case_value = case_op->value,
			};
		}
		if (default_addr != UT64_MAX) {
			if (index >= count) {
				return false;
			}
			block->successors[index++] = (RAnalSnapshotSuccessor) {
				.kind = R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_DEFAULT,
				.target_addr = default_addr,
			};
		}
		if (jump_is_distinct) {
			if (index >= count) {
				return false;
			}
			block->successors[index++] = (RAnalSnapshotSuccessor) {
				.kind = R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT,
				.target_addr = source->jump,
			};
		}
		if (index != count) {
			return false;
		}
	} else {
		size_t index = 0;
		if (source->jump != UT64_MAX) {
			block->successors[index++] = (RAnalSnapshotSuccessor) {
				.kind = R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT,
				.target_addr = source->jump,
			};
		}
		if (source->fail != UT64_MAX) {
			block->successors[index++] = (RAnalSnapshotSuccessor) {
				.kind = R_ANAL_SNAPSHOT_SUCCESSOR_FALLTHROUGH,
				.target_addr = source->fail,
			};
		}
	}
	qsort (block->successors, count, sizeof (RAnalSnapshotSuccessor),
		snapshot_successor_compare);
	size_t i;
	for (i = 1; i < count; i++) {
		const RAnalSnapshotSuccessor *previous = &block->successors[i - 1];
		const RAnalSnapshotSuccessor *current = &block->successors[i];
		if (previous->kind == R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_CASE
			&& current->kind == R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_CASE
			&& previous->case_value == current->case_value) {
			return false;
		}
	}
	return true;
}
static int function_image_target_classify(const RAnalFunctionImageSnapshot *image, ut64 target) {
	size_t lower = 0;
	size_t upper = image->num_blocks;
	while (lower < upper) {
		const size_t middle = lower + (upper - lower) / 2;
		if (image->blocks[middle].addr <= target) {
			lower = middle + 1;
		} else {
			upper = middle;
		}
	}
	if (!lower) {
		return 0;
	}
	const RAnalSnapshotBlock *block = &image->blocks[lower - 1];
	if (block->addr == target) {
		return 1;
	}
	return target < block->addr + block->size? -1: 0;
}
static bool snapshot_addr_starts_function(RAnal *anal, ut64 addr) {
	return addr && addr != UT64_MAX && r_anal_get_function_at (anal, addr) != NULL;
}
static bool function_image_code_pointer_table_collect(RAnal *anal,
		RAnalFunctionImageSnapshot *image, ut64 addr, ut32 entry_size) {
	size_t existing;
	for (existing = 0; existing < image->num_code_pointer_tables; existing++) {
		if (image->code_pointer_tables[existing].addr == addr) {
			return true;
		}
	}
	if (image->num_code_pointer_tables >= SNAPSHOT_MAX_CODE_POINTER_TABLES) {
		return true;
	}
	ut64 *targets = NULL;
	size_t num_targets = 0;
	while (num_targets < SNAPSHOT_MAX_CODE_POINTER_TABLE_ENTRIES) {
		ut8 word[8] = {0};
		const ut64 at = addr + (ut64)num_targets * entry_size;
		if (!anal->iob.read_at || !anal->iob.read_at (anal->iob.io, at, word, entry_size)) {
			break;
		}
		const ut64 target = entry_size == 8
			? r_read_le64 (word)
			: (ut64)r_read_le32 (word);
		if (!snapshot_addr_starts_function (anal, target)) {
			break;
		}
		ut64 *grown = realloc (targets, (num_targets + 1) * sizeof (*grown));
		if (!grown) {
			free (targets);
			return false;
		}
		targets = grown;
		targets[num_targets++] = target;
	}
	if (num_targets < 2) {
		// One pointer is a variable holding a function, not a table to index.
		free (targets);
		return true;
	}
	RAnalSnapshotCodePointerTable *grown = realloc (image->code_pointer_tables,
		(image->num_code_pointer_tables + 1) * sizeof (*grown));
	if (!grown) {
		free (targets);
		return false;
	}
	image->code_pointer_tables = grown;
	RAnalSnapshotCodePointerTable *table =
		&image->code_pointer_tables[image->num_code_pointer_tables++];
	table->addr = addr;
	table->entry_size = entry_size;
	table->targets = targets;
	table->num_targets = num_targets;
	return true;
}
static bool function_image_code_pointer_tables_collect(RAnal *anal,
		RAnalFunctionImageSnapshot *image) {
	const ut32 entry_size = anal->config && anal->config->bits == 32? 4: 8;
	size_t index;
	for (index = 0; index < image->num_blocks; index++) {
		const RAnalSnapshotBlock *block = &image->blocks[index];
		ut64 offset;
		for (offset = 0; offset < block->size; offset++) {
			RVecAnalRef *refs = r_anal_xrefs_get_from (anal, block->addr + offset);
			if (!refs) {
				continue;
			}
			RAnalRef *ref;
			R_VEC_FOREACH (refs, ref) {
				const int type = R_ANAL_REF_TYPE_MASK (ref->type);
				if (type != R_ANAL_REF_TYPE_DATA && type != R_ANAL_REF_TYPE_ICOD) {
					continue;
				}
				if (!function_image_code_pointer_table_collect (anal, image, ref->addr, entry_size)) {
					RVecAnalRef_free (refs);
					return false;
				}
			}
			RVecAnalRef_free (refs);
		}
	}
	return true;
}
static bool function_image_string_literals_collect(RAnal *anal,
		RAnalFunctionImageSnapshot *image,
		const RAnalFunctionSnapshotLimits *limits) {
	size_t index;
	for (index = 0; index < image->num_blocks; index++) {
		const RAnalSnapshotBlock *block = &image->blocks[index];
		ut64 offset;
		for (offset = 0; offset < block->size; offset++) {
			RVecAnalRef *refs = r_anal_xrefs_get_from (anal, block->addr + offset);
			if (!refs) {
				continue;
			}
			RAnalRef *ref;
			R_VEC_FOREACH (refs, ref) {
				const char *text = r_meta_get_string (anal, R_META_TYPE_STRING, ref->addr);
				if (!text || !*text) {
					continue;
				}
				size_t existing;
				bool known = false;
				for (existing = 0; existing < image->num_string_literals; existing++) {
					if (image->string_literals[existing].addr == ref->addr) {
						known = true;
						break;
					}
				}
				if (known) {
					continue;
				}
				if (image->num_string_literals >= limits->max_function_successors) {
					RVecAnalRef_free (refs);
					return false;
				}
				RAnalSnapshotStringLiteral *grown = realloc (image->string_literals,
					(image->num_string_literals + 1) * sizeof (*grown));
				if (!grown) {
					RVecAnalRef_free (refs);
					return false;
				}
				image->string_literals = grown;
				RAnalSnapshotStringLiteral *literal =
					&image->string_literals[image->num_string_literals];
				literal->addr = ref->addr;
				literal->text = strdup (text);
				if (!literal->text) {
					RVecAnalRef_free (refs);
					return false;
				}
				image->num_string_literals++;
			}
			RVecAnalRef_free (refs);
		}
	}
	return true;
}
static bool function_image_data_symbols_collect(RAnal *anal,
		RAnalFunctionImageSnapshot *image,
		const RAnalFunctionSnapshotLimits *limits) {
	if (!anal->flb.get_at || !anal->flb.f) {
		return true;
	}
	size_t index;
	for (index = 0; index < image->num_blocks; index++) {
		const RAnalSnapshotBlock *block = &image->blocks[index];
		ut64 offset;
		for (offset = 0; offset < block->size; offset++) {
			RVecAnalRef *refs = r_anal_xrefs_get_from (anal, block->addr + offset);
			if (!refs) {
				continue;
			}
			RAnalRef *ref;
			R_VEC_FOREACH (refs, ref) {
				RFlagItem *flag = anal->flb.get_at (anal->flb.f, ref->addr, false);
				if (!flag || !flag->name || !*flag->name) {
					continue;
				}
				// What the reference is decides this, not how the flag is
				// spelled. Skipping every "sym." name dropped ordinary data
				// objects: a lookup table emitted by the compiler carries a
				// "sym." flag exactly as an imported function does, so the
				// name test threw away the symbol the caller asked for while
				// keeping nothing it needed. A data reference is a reference
				// to data whatever its target is called.
				// A `lea` of a lookup table is typed ICOD, because the
				// analysis cannot tell a loaded data pointer from a loaded
				// code pointer by the instruction alone. Both kinds of
				// reference are admitted here and the target settles it: an
				// address a function starts at is code, and anything else a
				// reference points at is data.
				ut64 kind = R_ANAL_REF_TYPE_MASK (ref->type);
				if (kind != R_ANAL_REF_TYPE_DATA && kind != R_ANAL_REF_TYPE_ICOD) {
					continue;
				}
				if (r_anal_get_function_at (anal, ref->addr)) {
					continue;
				}
				// Strings have their own table, and a code label is not data.
				if (!strncmp (flag->name, "str.", 4) || !strncmp (flag->name, "fcn.", 4)
					|| !strncmp (flag->name, "loc.", 4)) {
					continue;
				}
				size_t existing;
				bool known = false;
				for (existing = 0; existing < image->num_data_symbols; existing++) {
					if (image->data_symbols[existing].addr == ref->addr) {
						known = true;
						break;
					}
				}
				if (known) {
					continue;
				}
				if (image->num_data_symbols >= limits->max_function_successors) {
					RVecAnalRef_free (refs);
					return false;
				}
				RAnalSnapshotDataSymbol *grown = realloc (image->data_symbols,
					(image->num_data_symbols + 1) * sizeof (*grown));
				if (!grown) {
					RVecAnalRef_free (refs);
					return false;
				}
				image->data_symbols = grown;
				RAnalSnapshotDataSymbol *symbol = &image->data_symbols[image->num_data_symbols];
				symbol->addr = ref->addr;
				symbol->name = strdup (flag->name);
				if (!symbol->name) {
					RVecAnalRef_free (refs);
					return false;
				}
				symbol->type_name = r_type_link_at (anal->sdb_types, ref->addr);
				if (symbol->type_name && !*symbol->type_name) {
					free (symbol->type_name);
					symbol->type_name = NULL;
				}
				image->num_data_symbols++;
			}
			RVecAnalRef_free (refs);
		}
	}
	return true;
}
static bool function_image_snapshot_collect(RAnal *anal, const RAnalFunction *fcn, const RAnalFunctionSnapshotLimits *limits, RAnalFunctionImageSnapshot *image, const char **reason) {
	const char *refusal = "the function image is not coherent";
	R_RETURN_VAL_IF_FAIL (anal && fcn && limits && image, false);
	if (fcn->anal != anal || !anal->iob.read_at || !fcn->bbs) {
		IMAGE_REFUSE ("the function does not belong to this analysis or has no blocks");
	}
	const int listed_blocks = r_list_length (fcn->bbs);
	if (listed_blocks <= 0 || (size_t)listed_blocks > limits->max_function_blocks) {
		IMAGE_REFUSE ("the block count is zero or past its limit");
	}
	const size_t count = (size_t)listed_blocks;
	size_t allocation_size;
	if (r_mul_overflow (count, sizeof (RAnalSnapshotBlock), &allocation_size)) {
		IMAGE_REFUSE ("the block table size overflows");
	}
	image->blocks = calloc (1, allocation_size);
	if (!image->blocks) {
		IMAGE_REFUSE ("out of memory allocating the block table");
	}
	image->num_blocks = count;
	image->entry_addr = fcn->addr;
	size_t total_successors = 0;
	size_t total_source_bytes = 0;
	size_t index = 0;
	RListIter *iter;
	RAnalBlock *source;
	r_list_foreach (fcn->bbs, iter, source) {
		if (!source || index >= count || !source->size
			|| source->size > (ut64)SIZE_MAX || source->size > (ut64)INT_MAX
			|| source->size > (ut64)limits->max_block_source_bytes
			|| source->addr > UT64_MAX - source->size) {
			IMAGE_REFUSE ("a block is empty, oversized, or wraps its address");
		}
		const size_t source_size = (size_t)source->size;
		size_t next_source_bytes;
		if (r_add_overflow_size_t (
				total_source_bytes, source_size, &next_source_bytes)
			|| next_source_bytes > limits->max_function_source_bytes) {
			IMAGE_REFUSE ("the total block bytes exceed the function limit");
		}
		total_source_bytes = next_source_bytes;
		RAnalSnapshotBlock *block = &image->blocks[index++];
		block->addr = source->addr;
		block->size = source->size;
		block->switch_addr = UT64_MAX;
		if (!snapshot_block_successors_collect (
				source, block, &total_successors, limits)) {
			IMAGE_REFUSE ("the block successors are not coherent");
		}
	}
	if (index != count) {
		IMAGE_REFUSE ("the block list changed while it was read");
	}
	image->total_source_bytes = total_source_bytes;
	qsort (image->blocks, count, sizeof (RAnalSnapshotBlock), snapshot_block_compare);
	ut64 previous_end = 0;
	for (index = 0; index < count; index++) {
		RAnalSnapshotBlock *block = &image->blocks[index];
		if (index && block->addr < previous_end) {
			IMAGE_REFUSE ("two blocks overlap");
		}
		previous_end = block->addr + block->size;
		block->bytes = malloc ((size_t)block->size);
		if (!block->bytes) {
			IMAGE_REFUSE ("out of memory allocating block bytes");
		}
		const int block_size = (int)block->size;
		if (anal->iob.read_at (anal->iob.io, block->addr, block->bytes, block_size) != block_size) {
			IMAGE_REFUSE ("the block bytes could not be read from io");
		}
		if (!snapshot_block_sequential_jump_normalize (anal, block)) {
			IMAGE_REFUSE ("a sequential jump could not be normalized");
		}
	}
	if (function_image_target_classify (image, image->entry_addr) != 1) {
		IMAGE_REFUSE ("the entry address is not a block start");
	}
	if (total_successors) {
		if (r_mul_overflow (total_successors, sizeof (ut64), &allocation_size)) {
			IMAGE_REFUSE ("the external exit table size overflows");
		}
		image->external_exits = malloc (allocation_size);
		if (!image->external_exits) {
			IMAGE_REFUSE ("out of memory allocating external exits");
		}
	}
	for (index = 0; index < count; index++) {
		RAnalSnapshotBlock *block = &image->blocks[index];
		size_t successor_index;
		for (successor_index = 0;
			successor_index < block->num_successors; successor_index++) {
			RAnalSnapshotSuccessor *successor = &block->successors[successor_index];
			const int target_class = function_image_target_classify (
				image, successor->target_addr);
			if (target_class < 0) {
				IMAGE_REFUSE ("a successor targets the middle of a block");
			}
			if (!target_class) {
				successor->external = true;
				image->external_exits[image->num_external_exits++] = successor->target_addr;
			}
		}
	}
	if (image->num_external_exits) {
		qsort (image->external_exits, image->num_external_exits,
			sizeof (ut64), snapshot_addr_compare);
		size_t unique = 1;
		for (index = 1; index < image->num_external_exits; index++) {
			if (image->external_exits[index] != image->external_exits[unique - 1]) {
				image->external_exits[unique++] = image->external_exits[index];
			}
		}
		image->num_external_exits = unique;
	}
	if (!function_image_code_pointer_tables_collect (anal, image)) {
		return false;
	}
	if (!function_image_data_symbols_collect (anal, image, limits)) {
		IMAGE_REFUSE ("the data symbol table could not be built");
	}
	if (!function_image_string_literals_collect (anal, image, limits)) {
		IMAGE_REFUSE ("the referenced string literals are not coherent");
	}
	return true;

fail:
	function_image_snapshot_fini (image);
	if (reason) {
		*reason = refusal;
	}
	return false;
}
static bool function_image_snapshot_equal(const RAnalFunctionImageSnapshot *left, const RAnalFunctionImageSnapshot *right) {
	if (left->entry_addr != right->entry_addr
		|| left->num_blocks != right->num_blocks
		|| left->num_external_exits != right->num_external_exits
		|| left->total_source_bytes != right->total_source_bytes) {
		return false;
	}
	if (left->num_external_exits && memcmp (left->external_exits,
			right->external_exits,
			left->num_external_exits * sizeof (ut64))) {
		return false;
	}
	size_t i;
	for (i = 0; i < left->num_blocks; i++) {
		const RAnalSnapshotBlock *a = &left->blocks[i];
		const RAnalSnapshotBlock *b = &right->blocks[i];
		if (a->addr != b->addr || a->size != b->size
			|| a->switch_addr != b->switch_addr
			|| a->num_successors != b->num_successors
			|| memcmp (a->bytes, b->bytes, (size_t)a->size)) {
			return false;
		}
		size_t j;
		for (j = 0; j < a->num_successors; j++) {
			const RAnalSnapshotSuccessor *as = &a->successors[j];
			const RAnalSnapshotSuccessor *bs = &b->successors[j];
			if (as->kind != bs->kind || as->target_addr != bs->target_addr
				|| as->case_value != bs->case_value
				|| as->external != bs->external) {
				return false;
			}
		}
	}
	return true;
}
static void snapshot_register_storage_fini(RAnalSnapshotRegisterStorage *storage) {
	free (storage->name);
	memset (storage, 0, sizeof (*storage));
}
static void function_interface_snapshot_fini(RAnalFunctionInterfaceSnapshot *interface) {
	size_t i;
	for (i = 0; i < interface->num_parameters; i++) {
		free (interface->parameters[i].name);
		snapshot_register_storage_fini (&interface->parameters[i].storage);
	}
	free (interface->parameters);
	free (interface->calling_convention);
	for (size_t slot = 0; slot < interface->num_convention_argument_slots; slot++) {
		snapshot_register_storage_fini (&interface->convention_argument_slots[slot]);
	}
	R_FREE (interface->convention_argument_slots);
	interface->num_convention_argument_slots = 0;
	snapshot_register_storage_fini (&interface->convention_result_slot);
	snapshot_register_storage_fini (&interface->return_storage);
	snapshot_register_storage_fini (&interface->return_address_storage);
	snapshot_register_storage_fini (&interface->stack_pointer_storage);
}
static void snapshot_type_graph_fini(RAnalSnapshotTypeGraph *graph) {
	size_t i;
	for (i = 0; i < graph->num_aggregates; i++) {
		RAnalSnapshotAggregateLayout *aggregate = &graph->aggregates[i];
		size_t j;
		for (j = 0; j < aggregate->num_members; j++) {
			free (aggregate->members[j].name);
		}
		free (aggregate->members);
		free (aggregate->name);
	}
	free (graph->aggregates);
	free (graph->types);
	memset (graph, 0, sizeof (*graph));
}
static void call_site_interface_snapshot_fini(RAnalCallSiteInterfaceSnapshot *interface) {
	size_t i;
	for (i = 0; i < interface->num_arguments; i++) {
		free (interface->arguments[i].name);
		snapshot_register_storage_fini (&interface->arguments[i].storage);
	}
	free (interface->arguments);
	free (interface->target_name);
	free (interface->calling_convention);
	snapshot_register_storage_fini (&interface->result_storage);
}
static void r_anal_function_snapshot_free(RAnalFunctionSnapshot *snapshot) {
	if (!snapshot) {
		return;
	}
	size_t callee;
	for (callee = 0; callee < snapshot->num_callee_snapshots; callee++) {
		r_anal_function_snapshot_free (snapshot->callee_snapshots[callee]);
	}
	free (snapshot->callee_snapshots);
	function_context_fini (&snapshot->context);
	function_interface_snapshot_fini (&snapshot->function_interface);
	snapshot_register_storage_fini (&snapshot->frame_pointer_storage);
	size_t i;
	for (i = 0; i < snapshot->num_call_site_interfaces; i++) {
		call_site_interface_snapshot_fini (&snapshot->call_site_interfaces[i]);
	}
	free (snapshot->call_site_interfaces);
	snapshot_type_graph_fini (&snapshot->type_graph);
	function_image_snapshot_fini (&snapshot->image);
	r_anal_types_snapshot_free (snapshot->base_types);
	free (snapshot->arch_id);
	free (snapshot->cpu_id);
	free (snapshot->function_name);
	free (snapshot);
}
static RAnalSnapshotReturnArity snapshot_signature_return_arity(const RAnalFunctionSignature *signature) {
	RAnalSnapshotReturnArity return_arity = R_ANAL_SNAPSHOT_RETURN_ARITY_UNKNOWN;
	if (signature && !strcmp (r_str_get (signature->ret_type), "void")) {
		return_arity = R_ANAL_SNAPSHOT_RETURN_ARITY_VOID;
	} else if (signature && R_STR_ISNOTEMPTY (signature->ret_type)) {
		return_arity = R_ANAL_SNAPSHOT_RETURN_ARITY_VALUE;
	}
	return return_arity;
}
static ut64 function_snapshot_hash_signature(ut64 hash, const RAnalFunctionSignature *signature) {
	if (!signature) {
		return function_context_hash_mix (hash, 0);
	}
	hash = function_context_hash_string (hash, signature->signature);
	hash = function_context_hash_string (hash, signature->ret_type);
	hash = function_context_hash_string (hash, signature->callconv);
	hash = function_context_hash_mix (hash, signature->noreturn? 1: 0);
	RListIter *iter;
	RAnalFunctionParam *param;
	r_list_foreach (signature->params, iter, param) {
		hash = function_context_hash_string (hash, param? param->name: NULL);
		hash = function_context_hash_string (hash, param? param->type: NULL);
	}
	return hash;
}
static ut64 function_snapshot_hash_base_types(ut64 hash, const RList *base_types) {
	RListIter *iter;
	RAnalBaseType *type;
	r_list_foreach (base_types, iter, type) {
		if (!type) {
			hash = function_context_hash_mix (hash, 0);
			continue;
		}
		hash = function_context_hash_string (hash, type->name);
		hash = function_context_hash_string (hash, type->type);
		hash = function_context_hash_mix (hash, (ut64)type->size);
		hash = function_context_hash_mix (hash, (ut64)type->kind);
		switch (type->kind) {
		case R_ANAL_BASE_TYPE_KIND_STRUCT: {
			RAnalStructMember *member;
			R_VEC_FOREACH (&type->struct_data.members, member) {
				hash = function_context_hash_string (hash, member->name);
				hash = function_context_hash_string (hash, member->type);
				hash = function_context_hash_mix (hash, (ut64)member->offset);
				hash = function_context_hash_mix (hash, (ut64)member->bitsize);
				hash = function_context_hash_mix (hash, (ut64)member->count);
			}
			break;
		}
		case R_ANAL_BASE_TYPE_KIND_UNION: {
			RAnalUnionMember *member;
			R_VEC_FOREACH (&type->union_data.members, member) {
				hash = function_context_hash_string (hash, member->name);
				hash = function_context_hash_string (hash, member->type);
				hash = function_context_hash_mix (hash, (ut64)member->offset);
				hash = function_context_hash_mix (hash, (ut64)member->bitsize);
				hash = function_context_hash_mix (hash, (ut64)member->count);
			}
			break;
		}
		case R_ANAL_BASE_TYPE_KIND_ENUM: {
			RAnalEnumCase *cas;
			R_VEC_FOREACH (&type->enum_data.cases, cas) {
				hash = function_context_hash_string (hash, cas->name);
				hash = function_context_hash_mix (hash, (ut64)(st64)cas->val);
			}
			break;
		}
		default:
			break;
		}
	}
	return hash;
}
static ut64 function_snapshot_hash_storage(ut64 hash, const RAnalSnapshotRegisterStorage *storage) {
	hash = function_context_hash_string (hash, storage->name);
	hash = function_context_hash_mix (hash, storage->offset);
	return function_context_hash_mix (hash, storage->size);
}
static ut64 function_snapshot_hash_interface(ut64 hash, const RAnalFunctionInterfaceSnapshot *interface) {
	hash = function_context_hash_string (hash, interface->calling_convention);
	hash = function_context_hash_mix (hash, interface->num_parameters);
	size_t i;
	for (i = 0; i < interface->num_parameters; i++) {
		const RAnalSnapshotParameter *parameter = &interface->parameters[i];
		hash = function_context_hash_mix (hash, parameter->index);
		hash = function_snapshot_hash_storage (hash, &parameter->storage);
		hash = function_context_hash_mix (hash, parameter->logical_type_id);
		hash = function_context_hash_mix (hash, parameter->carrier.kind);
		hash = function_context_hash_mix (hash, parameter->carrier.offset_bits);
		hash = function_context_hash_mix (hash, parameter->carrier.size_bits);
	}
	hash = function_context_hash_mix (hash, interface->return_kind);
	hash = function_snapshot_hash_storage (hash, &interface->return_storage);
	hash = function_snapshot_hash_storage (hash, &interface->return_address_storage);
	hash = function_snapshot_hash_storage (hash, &interface->stack_pointer_storage);
	hash = function_context_hash_mix (hash, interface->variadic? 1: 0);
	hash = function_context_hash_mix (hash, interface->noreturn? 1: 0);
	hash = function_context_hash_mix (hash, interface->stack_resources_complete? 1: 0);
	hash = function_context_hash_mix (hash, interface->stack_slot_roles_complete? 1: 0);
	hash = function_context_hash_mix (hash, interface->complete? 1: 0);
	hash = function_context_hash_mix (hash, interface->return_type_id);
	hash = function_context_hash_mix (hash, interface->return_carrier.kind);
	hash = function_context_hash_mix (hash, interface->return_carrier.offset_bits);
	hash = function_context_hash_mix (hash, interface->return_carrier.size_bits);
	hash = function_context_hash_mix (hash,
		interface->stack_pointer_preserved_across_calls? 1: 0);
	hash = function_context_hash_mix (hash,
		interface->frame_pointer_preserved_across_calls? 1: 0);
	return function_context_hash_mix (hash, interface->logical_types_complete? 1: 0);
}
static ut64 function_snapshot_hash_return_mechanism(ut64 hash, const RAnalSnapshotReturnMechanismView *mechanism) {
	hash = function_context_hash_mix (hash, mechanism->kind);
	hash = function_context_hash_mix (hash, (ut64)mechanism->entry_sp_offset);
	hash = function_context_hash_mix (hash, mechanism->slot_size);
	return function_context_hash_mix (hash, (ut64)mechanism->exit_sp_delta);
}
static ut64 function_snapshot_hash_stack_allocation_contract(ut64 hash, const RAnalSnapshotStackAllocationContractView *contract) {
	hash = function_context_hash_mix (hash, contract->growth);
	return function_context_hash_mix (hash, contract->implicit_active_sp_bytes);
}
static ut64 function_snapshot_hash_type_graph(ut64 hash, const RAnalSnapshotTypeGraph *graph) {
	hash = function_context_hash_mix (hash, graph->num_types);
	size_t i;
	for (i = 0; i < graph->num_types; i++) {
		const RAnalSnapshotType *type = &graph->types[i];
		hash = function_context_hash_mix (hash, type->id);
		hash = function_context_hash_mix (hash, type->kind);
		hash = function_context_hash_mix (hash, type->size_bits);
		hash = function_context_hash_mix (hash, type->align_bits);
		hash = function_context_hash_mix (hash, type->target_type_id);
		hash = function_context_hash_mix (hash, type->aggregate_id);
	}
	hash = function_context_hash_mix (hash, graph->num_aggregates);
	for (i = 0; i < graph->num_aggregates; i++) {
		const RAnalSnapshotAggregateLayout *aggregate = &graph->aggregates[i];
		hash = function_context_hash_mix (hash, aggregate->id);
		hash = function_context_hash_mix (hash, aggregate->type_id);
		hash = function_context_hash_mix (hash, aggregate->size_bits);
		hash = function_context_hash_mix (hash, aggregate->align_bits);
		hash = function_context_hash_string (hash, aggregate->name);
		hash = function_context_hash_mix (hash, aggregate->num_members);
		size_t j;
		for (j = 0; j < aggregate->num_members; j++) {
			const RAnalSnapshotAggregateMember *member = &aggregate->members[j];
			hash = function_context_hash_mix (hash, member->member_id);
			hash = function_context_hash_mix (hash, member->type_id);
			hash = function_context_hash_mix (hash, member->offset_bits);
			hash = function_context_hash_mix (hash, member->size_bits);
			hash = function_context_hash_string (hash, member->name);
		}
		hash = function_context_hash_mix (hash, aggregate->complete? 1: 0);
	}
	return function_context_hash_mix (hash, graph->complete? 1: 0);
}
static ut64 function_snapshot_hash_call_interface(ut64 hash, const RAnalCallSiteInterfaceSnapshot *interface) {
	hash = function_context_hash_mix (hash, interface->instruction_addr);
	hash = function_context_hash_mix (hash, interface->target_addr);
	hash = function_context_hash_string (hash, interface->calling_convention);
	hash = function_context_hash_mix (hash, interface->num_arguments);
	size_t i;
	for (i = 0; i < interface->num_arguments; i++) {
		hash = function_context_hash_mix (hash, interface->arguments[i].index);
		hash = function_snapshot_hash_storage (hash, &interface->arguments[i].storage);
		hash = function_context_hash_mix (hash, interface->arguments[i].logical_type_id);
		hash = function_context_hash_mix (hash, interface->arguments[i].carrier.kind);
		hash = function_context_hash_mix (hash, interface->arguments[i].carrier.offset_bits);
		hash = function_context_hash_mix (hash, interface->arguments[i].carrier.size_bits);
	}
	hash = function_context_hash_mix (hash, interface->result_kind);
	hash = function_snapshot_hash_storage (hash, &interface->result_storage);
	hash = function_context_hash_mix (hash, interface->variadic? 1: 0);
	hash = function_context_hash_mix (hash, interface->noreturn? 1: 0);
	hash = function_context_hash_mix (hash, interface->transfer);
	return function_context_hash_mix (hash, interface->complete? 1: 0);
}
static ut64 function_snapshot_hash_image(ut64 hash, const RAnalFunctionImageSnapshot *image) {
	hash = function_context_hash_mix (hash, image->entry_addr);
	hash = function_context_hash_mix (hash, image->num_blocks);
	hash = function_context_hash_mix (hash, image->total_source_bytes);
	size_t i;
	for (i = 0; i < image->num_blocks; i++) {
		const RAnalSnapshotBlock *block = &image->blocks[i];
		hash = function_context_hash_mix (hash, block->addr);
		hash = function_context_hash_mix (hash, block->size);
		hash = function_context_hash_mix (hash, block->switch_addr);
		hash = function_context_hash_mix (hash, block->num_successors);
		size_t byte_index;
		for (byte_index = 0; byte_index < (size_t)block->size; byte_index++) {
			hash = function_context_hash_mix (hash, block->bytes[byte_index]);
		}
		size_t successor_index;
		for (successor_index = 0;
			successor_index < block->num_successors; successor_index++) {
			const RAnalSnapshotSuccessor *successor =
				&block->successors[successor_index];
			hash = function_context_hash_mix (hash, successor->kind);
			hash = function_context_hash_mix (hash, successor->target_addr);
			hash = function_context_hash_mix (hash, successor->case_value);
			hash = function_context_hash_mix (hash, successor->external? 1: 0);
		}
	}
	hash = function_context_hash_mix (hash, image->num_external_exits);
	for (i = 0; i < image->num_external_exits; i++) {
		hash = function_context_hash_mix (hash, image->external_exits[i]);
	}
	hash = function_context_hash_mix (hash, image->num_data_symbols);
	for (i = 0; i < image->num_data_symbols; i++) {
		const RAnalSnapshotDataSymbol *symbol = &image->data_symbols[i];
		hash = function_context_hash_mix (hash, symbol->addr);
		hash = function_context_hash_string (hash, symbol->name);
		hash = function_context_hash_string (hash, symbol->type_name);
	}
	return hash;
}
static ut64 function_snapshot_hash(const RAnalFunctionSnapshot *snapshot) {
	ut64 hash = 0xcbf29ce484222325ULL;
	hash = function_context_hash_mix (hash, snapshot->schema_version);
	hash = function_context_hash_mix (hash, snapshot->struct_size);
	hash = function_context_hash_mix (hash, snapshot->capabilities);
	hash = function_context_hash_mix (hash, snapshot->function_addr);
	hash = function_context_hash_mix (hash, snapshot->function_size);
	hash = function_context_hash_mix (hash, snapshot->context.function_dirty_epoch);
	hash = function_context_hash_mix (hash, snapshot->context.type_dirty_epoch);
	hash = function_context_hash_mix (hash, snapshot->type_context_hash);
	hash = function_context_hash_mix (hash, (ut64)snapshot->bits);
	hash = function_context_hash_mix (hash, snapshot->endian);
	hash = function_context_hash_mix (hash, (ut64)snapshot->maxstack);
	hash = function_context_hash_string (hash, snapshot->arch_id);
	hash = function_context_hash_string (hash, snapshot->cpu_id);
	hash = function_context_hash_string (hash, snapshot->function_name);
	hash = function_context_hash_mix (hash, snapshot->return_arity);
	hash = function_snapshot_hash_base_types (hash, snapshot->base_types);
	hash = function_snapshot_hash_interface (hash, &snapshot->function_interface);
	hash = function_snapshot_hash_return_mechanism (hash, &snapshot->return_mechanism);
	hash = function_snapshot_hash_storage (hash, &snapshot->frame_pointer_storage);
	hash = function_snapshot_hash_stack_allocation_contract (
		hash, &snapshot->stack_allocation_contract);
	hash = function_snapshot_hash_type_graph (hash, &snapshot->type_graph);
	hash = function_snapshot_hash_image (hash, &snapshot->image);
	size_t call_index;
	for (call_index = 0; call_index < snapshot->num_call_site_interfaces; call_index++) {
		hash = function_snapshot_hash_call_interface (
			hash, &snapshot->call_site_interfaces[call_index]);
	}
	hash = function_snapshot_hash_signature (hash, snapshot->context.signature);
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (snapshot->context.fcn_slots, iter, slot) {
		hash = function_context_hash_string (hash, slot? slot->name: NULL);
		hash = function_context_hash_string (hash, slot? slot->type: NULL);
		hash = function_context_hash_mix (hash, slot? (ut64)slot->base: 0);
		hash = function_context_hash_string (hash, slot? slot->base_name: NULL);
		hash = function_context_hash_mix (hash, slot? slot->base_offset: 0);
		hash = function_context_hash_mix (hash, slot? slot->base_size: 0);
		hash = function_context_hash_mix (hash, slot? (ut64)slot->offset: 0);
		hash = function_context_hash_mix (hash, slot? slot->size: 0);
		hash = function_context_hash_mix (hash, slot && slot->offset_valid? 1: 0);
		hash = function_context_hash_mix (hash, slot? (ut64)slot->role: 0);
		hash = function_context_hash_mix (hash, slot? (ut64)(st64)slot->arg_index: 0);
		hash = function_context_hash_string (hash, slot? slot->home_reg: NULL);
		hash = function_context_hash_mix (hash, slot? slot->home_reg_offset: 0);
		hash = function_context_hash_mix (hash, slot? slot->home_reg_size: 0);
	}
	RAnalFcnCallee *callee;
	r_list_foreach (snapshot->context.callees, iter, callee) {
		hash = function_context_hash_mix (hash, callee? callee->call_addr: 0);
		hash = function_context_hash_mix (hash, callee? callee->addr: 0);
		hash = function_context_hash_mix (hash, callee? (ut64)callee->linkage: 0);
		hash = function_context_hash_string (hash, callee? callee->name: NULL);
		hash = function_snapshot_hash_signature (hash, callee? callee->signature: NULL);
	}
	return hash? hash: 1;
}
static SnapshotStorageResult snapshot_register_storage_collect(
	RAnal *anal, const char *name, bool copy_name,
	RAnalSnapshotRegisterStorage *storage) {
	if (R_STR_ISEMPTY (name) || !anal->reg) {
		return SNAPSHOT_STORAGE_INVALID;
	}
	RRegItem *item = r_reg_get (anal->reg, name, -1);
	if (!item || item->offset < 0 || item->offset % 8
		|| item->size <= 0 || item->size % 8) {
		r_unref (item);
		return SNAPSHOT_STORAGE_INVALID;
	}
	if (copy_name) {
		storage->name = strdup (r_str_get (item->name));
		if (!storage->name) {
			r_unref (item);
			return SNAPSHOT_STORAGE_NO_MEMORY;
		}
	}
	storage->offset = (ut64)(item->offset / 8);
	storage->size = (ut32)(item->size / 8);
	r_unref (item);
	return SNAPSHOT_STORAGE_VALID;
}
static bool snapshot_function_address_size(const RAnalFunction *fcn, ut32 *size) {
	if (!fcn || fcn->bits <= 0 || fcn->bits % 8
		|| fcn->bits / 8 > UT32_MAX) {
		return false;
	}
	*size = (ut32)(fcn->bits / 8);
	return true;
}
static SnapshotStorageResult snapshot_return_address_storage_collect(
	RAnal *anal, const RAnalFunction *fcn, RAnalSnapshotRegisterStorage *storage) {
	ut32 address_size = 0;
	if (!anal->reg || !snapshot_function_address_size (fcn, &address_size)) {
		return SNAPSHOT_STORAGE_INVALID;
	}
	const RRegAlias aliases[] = {
		R_REG_ALIAS_LR,
		R_REG_ALIAS_RA,
		R_REG_ALIAS_PC,
	};
	size_t i;
	for (i = 0; i < R_ARRAY_SIZE (aliases); i++) {
		RAnalSnapshotRegisterStorage candidate = {0};
		SnapshotStorageResult collected = snapshot_register_storage_collect (
			anal, r_reg_alias_getname (anal->reg, aliases[i]), true, &candidate);
		if (collected == SNAPSHOT_STORAGE_NO_MEMORY) {
			return collected;
		}
		if (collected == SNAPSHOT_STORAGE_VALID && candidate.size == address_size) {
			*storage = candidate;
			return SNAPSHOT_STORAGE_VALID;
		}
		snapshot_register_storage_fini (&candidate);
	}
	return SNAPSHOT_STORAGE_INVALID;
}
static SnapshotStorageResult snapshot_stack_pointer_storage_collect(
	RAnal *anal, const RAnalFunction *fcn, RAnalSnapshotRegisterStorage *storage) {
	ut32 address_size;
	if (!anal->reg || !snapshot_function_address_size (fcn, &address_size)) {
		return SNAPSHOT_STORAGE_INVALID;
	}
	SnapshotStorageResult collected = snapshot_register_storage_collect (
		anal, r_reg_alias_getname (anal->reg, R_REG_ALIAS_SP), true, storage);
	if (collected == SNAPSHOT_STORAGE_VALID && storage->size != address_size) {
		snapshot_register_storage_fini (storage);
		return SNAPSHOT_STORAGE_INVALID;
	}
	return collected;
}
static bool snapshot_register_storage_resolve(RAnal *anal, const char *name, ut64 *offset, ut32 *size) {
	if (R_STR_ISEMPTY (name) || !anal->reg) {
		return false;
	}
	RRegItem *item = r_reg_get (anal->reg, name, -1);
	if (!item || item->offset < 0 || item->offset % 8
		|| item->size <= 0 || item->size % 8) {
		r_unref (item);
		return false;
	}
	*offset = (ut64)(item->offset / 8);
	*size = (ut32)(item->size / 8);
	r_unref (item);
	return true;
}
static bool snapshot_cc_argument_storage(RAnal *anal, const char *calling_convention, int index, int count, ut64 *offset, ut32 *size) {
	const char *place = r_anal_cc_argloc (anal, calling_convention, index, 0, count);
	RAnalCCArgSlot slot = {0};
	return R_STR_ISNOTEMPTY (place) && *place != '^' && *place != '{'
		&& r_anal_cc_argslot (anal, calling_convention, index, count, false, &slot)
		&& slot.reg && snapshot_register_storage_resolve (anal, slot.reg, offset, size);
}
static bool snapshot_cc_maps_register_interface(RAnal *anal, const RAnalFunctionSignature *signature, const char *calling_convention) {
	if (!signature || R_STR_ISEMPTY (calling_convention)
		|| !r_anal_cc_exist (anal, calling_convention)) {
		return false;
	}
	size_t parameter_count = (size_t)r_list_length (signature->params);
	if (parameter_count > INT_MAX) {
		return false;
	}
	size_t i;
	for (i = 0; i < parameter_count; i++) {
		ut64 offset;
		ut32 size;
		if (!snapshot_cc_argument_storage (anal, calling_convention, (int)i,
				(int)parameter_count, &offset, &size)) {
			return false;
		}
		ut64 end;
		if (r_add_overflow (offset, (ut64)size, &end)) {
			return false;
		}
		size_t j;
		for (j = 0; j < i; j++) {
			ut64 previous_offset;
			ut32 previous_size;
			ut64 previous_end;
			if (!snapshot_cc_argument_storage (anal, calling_convention, (int)j,
					(int)parameter_count, &previous_offset, &previous_size)
				|| r_add_overflow (previous_offset, (ut64)previous_size, &previous_end)
				|| (offset < previous_end && previous_offset < end)) {
				return false;
			}
		}
	}
	if (!strcmp (r_str_get (signature->ret_type), "void")) {
		return true;
	}
	if (R_STR_ISEMPTY (signature->ret_type)) {
		return false;
	}
	const char *return_name = r_anal_cc_ret (anal, calling_convention, 0);
	const char *second_return = r_anal_cc_ret (anal, calling_convention, 1);
	ut64 return_offset;
	ut32 return_size;
	return R_STR_ISNOTEMPTY (return_name) && *return_name != '{'
		&& *return_name != '^' && R_STR_ISEMPTY (second_return)
		&& snapshot_register_storage_resolve (
			anal, return_name, &return_offset, &return_size);
}
static bool snapshot_promote_exact_dwarf_stack_homes(
	RAnal *anal, RAnalFunction *fcn, RAnalFcnContext *ctx,
	RAnalFunctionInterfaceSnapshot *interface, const char *calling_convention) {
	if (!ctx->signature
		|| !r_anal_function_has_address_linked_signature_current (fcn)) {
		return true;
	}
	const size_t parameter_count = (size_t)r_list_length (ctx->signature->params);
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (ctx->fcn_slots, iter, slot) {
		if (!slot || slot->role != R_ANAL_FCN_SLOT_ARG
			|| (slot->base != R_ANAL_FCN_BASE_BP
				&& slot->base != R_ANAL_FCN_BASE_SP)
			|| slot->arg_index < 0
			|| (size_t)slot->arg_index >= parameter_count
			|| (size_t)slot->arg_index >= interface->num_parameters) {
			continue;
		}
		const RAnalFunctionParam *signature_parameter =
			r_list_get_n (ctx->signature->params, slot->arg_index);
		if (!signature_parameter || R_STR_ISEMPTY (slot->type)
			|| R_STR_ISEMPTY (signature_parameter->type)
			|| strcmp (slot->type, signature_parameter->type)) {
			continue;
		}
		const char *place = r_anal_cc_argloc (anal, calling_convention,
			slot->arg_index, 0, (int)parameter_count);
		RAnalCCArgSlot abi_slot = {0};
		if (R_STR_ISEMPTY (place) || *place == '^' || *place == '{'
			|| !r_anal_cc_argslot (anal, calling_convention,
				slot->arg_index, (int)parameter_count, false, &abi_slot)
			|| !abi_slot.reg) {
			continue;
		}
		RAnalSnapshotRegisterStorage storage = {0};
		SnapshotStorageResult collected = snapshot_register_storage_collect (
			anal, abi_slot.reg, true, &storage);
		if (collected == SNAPSHOT_STORAGE_NO_MEMORY) {
			return false;
		}
		const RAnalSnapshotRegisterStorage *parameter_storage =
			&interface->parameters[slot->arg_index].storage;
		if (collected != SNAPSHOT_STORAGE_VALID
			|| R_STR_ISEMPTY (parameter_storage->name)
			|| strcmp (storage.name, parameter_storage->name)
			|| storage.offset != parameter_storage->offset
			|| storage.size != parameter_storage->size) {
			snapshot_register_storage_fini (&storage);
			continue;
		}
		slot->role = R_ANAL_FCN_SLOT_HOME;
		slot->home_reg = storage.name;
		slot->home_reg_offset = storage.offset;
		slot->home_reg_size = storage.size;
	}
	return true;
}
static bool snapshot_parameter_storages_overlap(
	const RAnalSnapshotParameter *parameters, size_t count) {
	size_t i, j;
	for (i = 0; i < count; i++) {
		ut64 left_end;
		if (r_add_overflow (parameters[i].storage.offset,
				(ut64)parameters[i].storage.size, &left_end)) {
			return true;
		}
		for (j = i + 1; j < count; j++) {
			ut64 right_end;
			if (r_add_overflow (parameters[j].storage.offset,
					(ut64)parameters[j].storage.size, &right_end)
				|| (parameters[i].storage.offset < right_end
					&& parameters[j].storage.offset < left_end)) {
				return true;
			}
		}
	}
	return false;
}
static bool snapshot_register_storages_overlap(
	const RAnalSnapshotRegisterStorage *left,
	const RAnalSnapshotRegisterStorage *right) {
	ut64 left_end;
	ut64 right_end;
	return !left->size || !right->size
		|| r_add_overflow (left->offset, (ut64)left->size, &left_end)
		|| r_add_overflow (right->offset, (ut64)right->size, &right_end)
		|| (left->offset < right_end && right->offset < left_end);
}
static bool snapshot_register_storages_equal(
	const RAnalSnapshotRegisterStorage *left,
	const RAnalSnapshotRegisterStorage *right) {
	return left->size && right->size
		&& left->offset == right->offset && left->size == right->size;
}
static bool snapshot_return_address_storage_overlaps_interface(
	const RAnalFunctionInterfaceSnapshot *interface, const RAnalFcnContext *ctx) {
	if (interface->stack_pointer_storage.name
		&& interface->stack_pointer_storage.size
		&& snapshot_register_storages_overlap (
			&interface->return_address_storage,
			&interface->stack_pointer_storage)) {
		return true;
	}
	size_t i;
	for (i = 0; i < interface->num_parameters; i++) {
		if (interface->parameters[i].storage.name
			&& interface->parameters[i].storage.size
			&& snapshot_register_storages_overlap (
				&interface->return_address_storage,
				&interface->parameters[i].storage)) {
			return true;
		}
	}
	if (interface->return_kind == R_ANAL_SNAPSHOT_RETURN_REGISTER
		&& snapshot_register_storages_overlap (
			&interface->return_address_storage, &interface->return_storage)) {
		return true;
	}
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (ctx->fcn_slots, iter, slot) {
		if (!slot) {
			continue;
		}
		RAnalSnapshotRegisterStorage base_storage = {
			.offset = slot->base_offset,
			.size = slot->base_size,
		};
		if (slot->base_name && slot->base_size
			&& snapshot_register_storages_overlap (
				&interface->return_address_storage, &base_storage)) {
			return true;
		}
		RAnalSnapshotRegisterStorage home_storage = {
			.offset = slot->home_reg_offset,
			.size = slot->home_reg_size,
		};
		if (slot->home_reg && slot->home_reg_size
			&& snapshot_register_storages_overlap (
				&interface->return_address_storage, &home_storage)) {
			return true;
		}
	}
	return false;
}
static bool snapshot_stack_pointer_storage_conflicts_interface(
	const RAnalFunctionInterfaceSnapshot *interface, const RAnalFcnContext *ctx) {
	if (interface->return_address_storage.name
		&& interface->return_address_storage.size
		&& snapshot_register_storages_overlap (
			&interface->stack_pointer_storage,
			&interface->return_address_storage)) {
		return true;
	}
	size_t i;
	for (i = 0; i < interface->num_parameters; i++) {
		if (interface->parameters[i].storage.name
			&& interface->parameters[i].storage.size
			&& snapshot_register_storages_overlap (
				&interface->stack_pointer_storage,
				&interface->parameters[i].storage)) {
			return true;
		}
	}
	if (interface->return_kind == R_ANAL_SNAPSHOT_RETURN_REGISTER
		&& snapshot_register_storages_overlap (
			&interface->stack_pointer_storage, &interface->return_storage)) {
		return true;
	}
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (ctx->fcn_slots, iter, slot) {
		if (!slot) {
			continue;
		}
		RAnalSnapshotRegisterStorage base_storage = {
			.offset = slot->base_offset,
			.size = slot->base_size,
		};
		if (slot->base == R_ANAL_FCN_BASE_SP) {
			if (R_STR_ISEMPTY (slot->base_name) || !snapshot_register_storages_equal (
					&interface->stack_pointer_storage, &base_storage)) {
				return true;
			}
		} else if (slot->base_size
			&& snapshot_register_storages_overlap (
				&interface->stack_pointer_storage, &base_storage)) {
			return true;
		}
		RAnalSnapshotRegisterStorage home_storage = {
			.offset = slot->home_reg_offset,
			.size = slot->home_reg_size,
		};
		if (slot->home_reg && slot->home_reg_size
			&& snapshot_register_storages_overlap (
				&interface->stack_pointer_storage, &home_storage)) {
			return true;
		}
	}
	return false;
}
static bool snapshot_stack_resources_complete(const RAnalFcnContext *ctx) {
	RListIter *left_iter;
	RAnalFcnSlot *left;
	r_list_foreach (ctx->fcn_slots, left_iter, left) {
		if (!left || (left->base != R_ANAL_FCN_BASE_BP
				&& left->base != R_ANAL_FCN_BASE_SP)
			|| R_STR_ISEMPTY (left->base_name) || !left->base_size
			|| left->base_offset > UT64_MAX - left->base_size
			|| !left->offset_valid || !left->size
			|| left->offset > ST64_MAX - (st64)left->size) {
			return false;
		}
		const st64 left_end = left->offset + (st64)left->size;
		RListIter *right_iter;
		for (right_iter = left_iter->n; right_iter; right_iter = right_iter->n) {
			RAnalFcnSlot *right = right_iter->data;
			if (!right || right->base != left->base) {
				continue;
			}
			if (!right->offset_valid || !right->size
				|| right->offset > ST64_MAX - (st64)right->size) {
				return false;
			}
			const st64 right_end = right->offset + (st64)right->size;
			if (left->offset < right_end && right->offset < left_end) {
				return false;
			}
		}
	}
	return true;
}
static bool snapshot_stack_slot_roles_complete(
	const RAnalFcnContext *ctx, const RAnalFunctionInterfaceSnapshot *interface) {
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (ctx->fcn_slots, iter, slot) {
		if (!slot) {
			return false;
		}
		if (slot->role == R_ANAL_FCN_SLOT_LOCAL) {
			if (slot->arg_index != -1 || slot->home_reg_offset
				|| slot->home_reg_size) {
				return false;
			}
			continue;
		}
		if (slot->role != R_ANAL_FCN_SLOT_HOME || slot->arg_index < 0
			|| (size_t)slot->arg_index >= interface->num_parameters
			|| !slot->home_reg_size
			|| slot->home_reg_offset > UT64_MAX - slot->home_reg_size) {
			return false;
		}
		const RAnalSnapshotParameter *parameter =
			&interface->parameters[slot->arg_index];
		if (parameter->index != (ut32)slot->arg_index
			|| slot->home_reg_offset != parameter->storage.offset
			|| slot->home_reg_size != parameter->storage.size) {
			return false;
		}
		RListIter *previous_iter;
		RAnalFcnSlot *previous;
		r_list_foreach (ctx->fcn_slots, previous_iter, previous) {
			if (previous == slot) {
				break;
			}
			if (previous && previous->role == R_ANAL_FCN_SLOT_HOME
				&& previous->arg_index == slot->arg_index) {
				return false;
			}
		}
	}
	return true;
}
static bool snapshot_convention_slots_collect(
	RAnal *anal, RAnalFunction *fcn, RAnalFunctionInterfaceSnapshot *interface) {
	const char *convention = R_STR_ISNOTEMPTY (fcn->callconv)
		? fcn->callconv
		: r_anal_cc_default (anal);
	if (R_STR_ISEMPTY (convention) || !r_anal_cc_exist (anal, convention)) {
		return true;
	}
	/* Name the convention even when no signature was recovered: a consumer that
	 * recovers parameters from machine code needs to know which convention the
	 * candidate slots belong to. The signature path below replaces this when it
	 * resolves a more specific convention. */
	if (!interface->calling_convention) {
		interface->calling_convention = strdup (convention);
		if (!interface->calling_convention) {
			return false;
		}
	}
	RAnalSnapshotRegisterStorage slots[R_ANAL_CC_MAXARG] = {0};
	size_t count = 0;
	while (count < R_ANAL_CC_MAXARG) {
		RAnalCCArgSlot slot = {0};
		if (!r_anal_cc_argslot (anal, convention, (int)count, -1, false, &slot)
			|| R_STR_ISEMPTY (slot.reg)) {
			break;
		}
		if (snapshot_register_storage_collect (anal, slot.reg, false, &slots[count])
				!= SNAPSHOT_STORAGE_VALID) {
			break;
		}
		count++;
	}
	if (!count) {
		return true;
	}
	interface->convention_argument_slots = R_NEWS0 (RAnalSnapshotRegisterStorage, count);
	if (!interface->convention_argument_slots) {
		for (size_t i = 0; i < count; i++) {
			snapshot_register_storage_fini (&slots[i]);
		}
		return false;
	}
	for (size_t i = 0; i < count; i++) {
		interface->convention_argument_slots[i] = slots[i];
	}
	interface->num_convention_argument_slots = count;
	const char *result = r_anal_cc_ret (anal, convention, 0);
	if (R_STR_ISNOTEMPTY (result)
		&& snapshot_register_storage_collect (anal, result,
			false, &interface->convention_result_slot) == SNAPSHOT_STORAGE_NO_MEMORY) {
		return false;
	}
	interface->convention_slots_known = true;
	return true;
}
static bool function_interface_snapshot_collect(
	RAnal *anal, RAnalFunction *fcn, RAnalFcnContext *ctx,
	RAnalFunctionInterfaceSnapshot *interface,
	const RAnalFunctionSnapshotLimits *limits) {
	interface->return_type_id = R_ANAL_SNAPSHOT_TYPE_ID_INVALID;
	interface->variadic = fcn->is_variadic;
	interface->noreturn = fcn->is_noreturn;
	interface->stack_resources_complete = snapshot_stack_resources_complete (ctx);
	SnapshotStorageResult return_address_collected =
		snapshot_return_address_storage_collect (
			anal, fcn, &interface->return_address_storage);
	if (return_address_collected == SNAPSHOT_STORAGE_NO_MEMORY) {
		return false;
	}
	SnapshotStorageResult stack_pointer_collected =
		snapshot_stack_pointer_storage_collect (
			anal, fcn, &interface->stack_pointer_storage);
	if (stack_pointer_collected == SNAPSHOT_STORAGE_NO_MEMORY) {
		return false;
	}
	bool return_address_complete = return_address_collected == SNAPSHOT_STORAGE_VALID;
	bool stack_pointer_complete = stack_pointer_collected == SNAPSHOT_STORAGE_VALID;
	const bool return_address_conflict = return_address_complete
		&& snapshot_return_address_storage_overlaps_interface (interface, ctx);
	const bool stack_pointer_conflict = stack_pointer_complete
		&& snapshot_stack_pointer_storage_conflicts_interface (interface, ctx);
	if (return_address_conflict) {
		snapshot_register_storage_fini (&interface->return_address_storage);
		return_address_complete = false;
	}
	if (stack_pointer_conflict) {
		snapshot_register_storage_fini (&interface->stack_pointer_storage);
		stack_pointer_complete = false;
	}
	if (!snapshot_convention_slots_collect (anal, fcn, interface)) {
		return false;
	}
	/* Preservation belongs to the calling convention, not to a recovered
	 * prototype. Seal it as soon as the convention and machine carriers are
	 * available so signatureless functions do not lose entry-relative facts. */
	const char *sp_name = interface->stack_pointer_storage.name;
	const char *fp_name = anal->reg
		? r_reg_alias_getname (anal->reg, R_REG_ALIAS_BP): NULL;
	interface->stack_pointer_preserved_across_calls =
		r_anal_cc_preserves_reg (anal, interface->calling_convention, sp_name);
	interface->frame_pointer_preserved_across_calls =
		r_anal_cc_preserves_reg (anal, interface->calling_convention, fp_name);
	if (r_sys_getenv_asbool ("R2SLEIGH_DEBUG_MERGES")) {
		eprintf ("R2CALLPRESERVE cc=%s sp=%s/%d fp=%s/%d\n",
			r_str_get (interface->calling_convention), r_str_get (sp_name),
			interface->stack_pointer_preserved_across_calls,
			r_str_get (fp_name), interface->frame_pointer_preserved_across_calls);
	}
	const bool address_linked =
		r_anal_function_has_address_linked_signature_current (fcn);
	if (!ctx->signature || !address_linked) {
		// Leaving without a word here hid the largest refusal cause in the
		// benchmark. A function that takes this exit carries no interface into
		// the snapshot, so the engine recovers one from the instructions
		// instead -- and a recovered interface reports the width the code
		// observes rather than the width the source declared, which is what
		// makes an `int` return look like a 64-bit carrier no exact definition
		// reaches. Whether radare2 had a prototype and whether it was linked
		// to this address are different failures wanting different fixes.
		if (r_sys_getenv_asbool ("R2SLEIGH_DEBUG_INTERFACE")) {
			eprintf ("R2SLEIGH_INTERFACE addr=0x%" PFMT64x
				" signature=%d address_linked=%d\n",
				fcn->addr, ctx->signature? 1: 0, address_linked? 1: 0);
		}
		return true;
	}
	const char *signature_calling_convention = ctx->signature->callconv;
	const char *live_calling_convention = fcn->callconv;
	const char *calling_convention = R_STR_ISNOTEMPTY (signature_calling_convention)
		? signature_calling_convention
		: live_calling_convention;
	if (R_STR_ISNOTEMPTY (signature_calling_convention)
		&& !snapshot_cc_maps_register_interface (
			anal, ctx->signature, signature_calling_convention)
		&& R_STR_ISNOTEMPTY (live_calling_convention)
		&& strcmp (signature_calling_convention, live_calling_convention)
		&& snapshot_cc_maps_register_interface (
			anal, ctx->signature, live_calling_convention)) {
		calling_convention = live_calling_convention;
	}
	if (R_STR_ISEMPTY (calling_convention) || !r_anal_cc_exist (anal, calling_convention)) {
		return true;
	}
	free (interface->calling_convention);
	interface->calling_convention = strdup (calling_convention);
	if (!interface->calling_convention) {
		return false;
	}
	size_t parameter_count = (size_t)r_list_length (ctx->signature->params);
	/* A variadic signature carries the ellipsis as a trailing parameter. It
	 * names no storage, so counting it as a parameter leaves a slot the
	 * convention cannot fill and marks the whole interface incomplete, which
	 * throws away the recovered carriers for the fixed prefix and every stack
	 * slot the function owns. Record it as variadic and describe only the fixed
	 * parameters, the way the call-site path already does.
	 *
	 * `r_type_arg_is_vararg` is the canonical test and the only one that holds.
	 * Reading the ellipsis as "empty type named ..." looks equivalent and is
	 * not: `func.fprintf.arg.2` stores a single space for its type, which is
	 * not empty, so that spelling reported two of the fifty-six vararg entries
	 * in the type database -- `fprintf` and `sscanf` -- as fixed-arity with one
	 * parameter too many. */
	if (parameter_count > 0) {
		RAnalFunctionParam *last = r_list_get_n (ctx->signature->params,
			(int)(parameter_count - 1));
		if (last && r_type_arg_is_vararg (last->type, last->name)) {
			interface->variadic = true;
			parameter_count--;
		}
	}
	if (parameter_count > INT_MAX || parameter_count > UT32_MAX
		|| parameter_count > limits->max_interface_parameters) {
		return false;
	}
	size_t allocation_size;
	if (r_mul_overflow (parameter_count, sizeof (RAnalSnapshotParameter), &allocation_size)) {
		return false;
	}
	if (allocation_size) {
		interface->parameters = calloc (1, allocation_size);
		if (!interface->parameters) {
			return false;
		}
	}
	interface->num_parameters = parameter_count;
	bool parameters_complete = true;
	RListIter *iter;
	RAnalFunctionParam *parameter;
	size_t index = 0;
	r_list_foreach (ctx->signature->params, iter, parameter) {
		if (index >= parameter_count) {
			break;
		}
		RAnalSnapshotParameter *snapshot_parameter = &interface->parameters[index];
		snapshot_parameter->index = (ut32)index;
		snapshot_parameter->logical_type_id = R_ANAL_SNAPSHOT_TYPE_ID_INVALID;
		if (parameter && R_STR_ISNOTEMPTY (parameter->name)) {
			snapshot_parameter->name = strdup (parameter->name);
			if (!snapshot_parameter->name) {
				return false;
			}
		}
		if (!parameter || R_STR_ISEMPTY (parameter->type)) {
			parameters_complete = false;
		}
		const char *place = r_anal_cc_argloc (
			anal, calling_convention, (int)index, 0, (int)parameter_count);
		RAnalCCArgSlot slot = {0};
		if (R_STR_ISEMPTY (place) || *place == '^' || *place == '{'
			|| !r_anal_cc_argslot (anal, calling_convention,
				(int)index, (int)parameter_count, false, &slot)
			|| !slot.reg) {
			parameters_complete = false;
			index++;
			continue;
		}
		SnapshotStorageResult collected = snapshot_register_storage_collect (
			anal, slot.reg, true, &snapshot_parameter->storage);
		if (collected == SNAPSHOT_STORAGE_NO_MEMORY) {
			return false;
		}
		if (collected != SNAPSHOT_STORAGE_VALID) {
			parameters_complete = false;
		}
		index++;
	}
	if (index != parameter_count
		|| snapshot_parameter_storages_overlap (interface->parameters, parameter_count)) {
		parameters_complete = false;
	}
	if (!snapshot_promote_exact_dwarf_stack_homes (
			anal, fcn, ctx, interface, calling_convention)) {
		return false;
	}
	bool return_complete = false;
	if (!strcmp (r_str_get (ctx->signature->ret_type), "void")) {
		interface->return_kind = R_ANAL_SNAPSHOT_RETURN_VOID;
		return_complete = true;
	} else if (R_STR_ISNOTEMPTY (ctx->signature->ret_type)) {
		const char *return_name = r_anal_cc_ret (anal, calling_convention, 0);
		const char *second_return = r_anal_cc_ret (anal, calling_convention, 1);
		if (R_STR_ISNOTEMPTY (return_name) && *return_name != '{'
			&& *return_name != '^' && R_STR_ISEMPTY (second_return)) {
			SnapshotStorageResult collected = snapshot_register_storage_collect (
				anal, return_name, false, &interface->return_storage);
			if (collected == SNAPSHOT_STORAGE_NO_MEMORY) {
				return false;
			}
			if (collected == SNAPSHOT_STORAGE_VALID) {
				interface->return_kind = R_ANAL_SNAPSHOT_RETURN_REGISTER;
				return_complete = true;
			}
		}
	}
	const bool final_return_address_conflict = return_address_complete
		&& snapshot_return_address_storage_overlaps_interface (interface, ctx);
	const bool final_stack_pointer_conflict = stack_pointer_complete
		&& snapshot_stack_pointer_storage_conflicts_interface (interface, ctx);
	if (final_return_address_conflict) {
		snapshot_register_storage_fini (&interface->return_address_storage);
		return_address_complete = false;
	}
	if (final_stack_pointer_conflict) {
		snapshot_register_storage_fini (&interface->stack_pointer_storage);
		stack_pointer_complete = false;
	}
	// noreturn says control does not come back, and variadic says the call site
	// may pass more than the declaration names. Neither is a statement about
	// whether the parameter and return storage were recovered. Every field the
	// completeness of this interface rests on was resolved independently of
	// both, and the call-site path computes the same notion without consulting
	// them, so letting either disqualify an interface discards recovered
	// storage for every exit, abort and assert helper, and for every function
	// that takes a "...". A variadic interface still carries where its named
	// parameters live, and the tail travels separately as `variadic`, so a
	// consumer that must account for it can still read it.
	// the frame extent is a separate claim, so it is not what makes an interface exact
	const bool physical_interface_complete = parameters_complete && return_complete
		&& return_address_complete && stack_pointer_complete;
	// roles carry the extent claim: unsized slots cannot prove they do not overlap
	interface->stack_slot_roles_complete = physical_interface_complete
		&& interface->stack_resources_complete
		&& snapshot_stack_slot_roles_complete (ctx, interface);
	interface->complete = physical_interface_complete;
	return true;
}
static void snapshot_return_mechanism_collect(RAnal *anal, const RAnalFunction *fcn,
		const RAnalFcnContext *ctx, const RAnalFunctionInterfaceSnapshot *interface,
		RAnalSnapshotReturnMechanismView *view) {
	*view = (RAnalSnapshotReturnMechanismView) {0};
	if (!interface->complete || R_STR_ISEMPTY (interface->calling_convention)) {
		return;
	}
	ut32 address_size;
	if (!snapshot_function_address_size (fcn, &address_size)
		|| R_STR_ISEMPTY (interface->return_address_storage.name)
		|| R_STR_ISEMPTY (interface->stack_pointer_storage.name)
		|| interface->return_address_storage.size != address_size
		|| interface->stack_pointer_storage.size != address_size) {
		return;
	}
	RAnalCCReturnMechanism mechanism = {0};
	if (!r_anal_cc_return_mechanism (
			anal, interface->calling_convention, &mechanism)
		|| mechanism.kind != R_ANAL_CC_RETURN_MECHANISM_STACK
		|| mechanism.entry_sp_offset != 0
		|| mechanism.slot_size != address_size
		|| mechanism.exit_sp_delta != (st64)mechanism.slot_size) {
		return;
	}
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (ctx->fcn_slots, iter, slot) {
		if (!slot || slot->base != R_ANAL_FCN_BASE_SP
			|| R_STR_ISEMPTY (slot->base_name)
			|| strcmp (slot->base_name, interface->stack_pointer_storage.name)
			|| slot->base_offset != interface->stack_pointer_storage.offset
			|| slot->base_size != interface->stack_pointer_storage.size) {
			continue;
		}
		if (!slot->offset_valid || !slot->size
			|| slot->offset > ST64_MAX - (st64)slot->size) {
			return;
		}
		const st64 slot_end = slot->offset + (st64)slot->size;
		if (slot->offset < (st64)mechanism.slot_size && slot_end > 0) {
			return;
		}
	}
	*view = (RAnalSnapshotReturnMechanismView) {
		.kind = R_ANAL_SNAPSHOT_RETURN_MECHANISM_STACK,
		.entry_sp_offset = mechanism.entry_sp_offset,
		.slot_size = mechanism.slot_size,
		.exit_sp_delta = mechanism.exit_sp_delta,
	};
}
static bool snapshot_return_mechanism_equal(const RAnalSnapshotReturnMechanismView *a,
		const RAnalSnapshotReturnMechanismView *b) {
	return a->kind == b->kind
		&& a->entry_sp_offset == b->entry_sp_offset
		&& a->slot_size == b->slot_size
		&& a->exit_sp_delta == b->exit_sp_delta;
}
static void snapshot_stack_allocation_contract_collect(RAnal *anal,
		const RAnalFunctionInterfaceSnapshot *interface,
		RAnalSnapshotStackAllocationContractView *view) {
	*view = (RAnalSnapshotStackAllocationContractView) {0};
	if (R_STR_ISEMPTY (interface->calling_convention)
		|| R_STR_ISEMPTY (interface->stack_pointer_storage.name)
		|| !interface->stack_pointer_storage.size) {
		return;
	}
	RAnalCCStackAllocationContract contract = {0};
	if (!r_anal_cc_stack_allocation_contract (
			anal, interface->calling_convention, &contract)) {
		return;
	}
	view->implicit_active_sp_bytes = contract.red_zone_bytes;
	switch (contract.growth) {
	case R_ANAL_CC_STACK_GROWTH_LOWER:
		view->growth = R_ANAL_SNAPSHOT_STACK_GROWTH_LOWER;
		break;
	case R_ANAL_CC_STACK_GROWTH_HIGHER:
		view->growth = R_ANAL_SNAPSHOT_STACK_GROWTH_HIGHER;
		break;
	case R_ANAL_CC_STACK_GROWTH_NONE:
	default:
		break;
	}
}
static bool snapshot_stack_allocation_contract_equal(
		const RAnalSnapshotStackAllocationContractView *a,
		const RAnalSnapshotStackAllocationContractView *b) {
	return a->growth == b->growth
		&& a->implicit_active_sp_bytes == b->implicit_active_sp_bytes;
}
static bool snapshot_frame_pointer_storage_conflicts_interface(
		const RAnalSnapshotRegisterStorage *storage,
		const RAnalFunctionInterfaceSnapshot *interface,
		const RAnalFcnContext *ctx) {
	if (snapshot_register_storages_overlap (
			storage, &interface->return_address_storage)
		|| snapshot_register_storages_overlap (
			storage, &interface->stack_pointer_storage)) {
		return true;
	}
	size_t i;
	for (i = 0; i < interface->num_parameters; i++) {
		if (snapshot_register_storages_overlap (
				storage, &interface->parameters[i].storage)) {
			return true;
		}
	}
	if (interface->return_kind == R_ANAL_SNAPSHOT_RETURN_REGISTER
		&& snapshot_register_storages_overlap (
			storage, &interface->return_storage)) {
		return true;
	}
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (ctx->fcn_slots, iter, slot) {
		if (!slot) {
			return true;
		}
		RAnalSnapshotRegisterStorage home = {
			.offset = slot->home_reg_offset,
			.size = slot->home_reg_size,
		};
		if (slot->home_reg && slot->home_reg_size
			&& snapshot_register_storages_overlap (storage, &home)) {
			return true;
		}
		if (slot->base == R_ANAL_FCN_BASE_BP) {
			RAnalSnapshotRegisterStorage base = {
				.offset = slot->base_offset,
				.size = slot->base_size,
			};
			if (!snapshot_register_storages_equal (storage, &base)) {
				return true;
			}
		}
	}
	return false;
}
static bool snapshot_frame_pointer_storage_collect(RAnal *anal,
		const RAnalFunction *fcn, const RAnalFcnContext *ctx,
		const RAnalFunctionInterfaceSnapshot *interface,
		RAnalSnapshotRegisterStorage *storage) {
	if (!interface->complete
		|| !r_anal_function_has_address_linked_signature_current (
			(RAnalFunction *)fcn)) {
		return true;
	}
	RAnalDwarfFramePointerStorage proof = {0};
	if (!r_anal_dwarf_function_frame_pointer_get (
			anal, fcn->addr, &proof)) {
		return true;
	}
	ut32 address_size;
	RAnalSnapshotRegisterStorage candidate = {0};
	SnapshotStorageResult collected = snapshot_register_storage_collect (
		anal, proof.name, true, &candidate);
	if (collected == SNAPSHOT_STORAGE_NO_MEMORY) {
		r_anal_dwarf_frame_pointer_storage_fini (&proof);
		return false;
	}
	const bool exact = collected == SNAPSHOT_STORAGE_VALID
		&& snapshot_function_address_size (fcn, &address_size)
		&& candidate.size == address_size
		&& !strcmp (candidate.name, proof.name)
		&& candidate.offset == proof.offset
		&& candidate.size == proof.size
		&& !snapshot_frame_pointer_storage_conflicts_interface (
			&candidate, interface, ctx);
	r_anal_dwarf_frame_pointer_storage_fini (&proof);
	if (!exact) {
		snapshot_register_storage_fini (&candidate);
		return true;
	}
	*storage = candidate;
	return true;
}
static bool snapshot_frame_pointer_storage_equal(
		const RAnalSnapshotRegisterStorage *a,
		const RAnalSnapshotRegisterStorage *b) {
	return !strcmp (r_str_get (a->name), r_str_get (b->name))
		&& a->offset == b->offset && a->size == b->size;
}
static int snapshot_base_type_compare(const void *left, const void *right) {
	const RAnalBaseType *a = left;
	const RAnalBaseType *b = right;
	const int name_cmp = strcmp (r_str_get (a? a->name: NULL),
		r_str_get (b? b->name: NULL));
	if (name_cmp || !a || !b || a->kind == b->kind) {
		return name_cmp;
	}
	return a->kind < b->kind? -1: 1;
}
static bool snapshot_nullable_string_equal(const char *left, const char *right) {
	return (!left && !right) || (left && right && !strcmp (left, right));
}
static bool snapshot_base_type_equal(const RAnalBaseType *left, const RAnalBaseType *right) {
	if (!left || !right) {
		return left == right;
	}
	if (left->kind != right->kind || left->size != right->size
		|| !snapshot_nullable_string_equal (left->name, right->name)
		|| !snapshot_nullable_string_equal (left->type, right->type)) {
		return false;
	}
	if (left->kind == R_ANAL_BASE_TYPE_KIND_STRUCT
		|| left->kind == R_ANAL_BASE_TYPE_KIND_UNION) {
		const RVecAnalTypeMember *left_members = r_anal_base_type_members (left);
		const RVecAnalTypeMember *right_members = r_anal_base_type_members (right);
		const size_t count = RVecAnalTypeMember_length (left_members);
		if (count != RVecAnalTypeMember_length (right_members)) {
			return false;
		}
		size_t i;
		for (i = 0; i < count; i++) {
			const RAnalTypeMember *a = RVecAnalTypeMember_at (left_members, i);
			const RAnalTypeMember *b = RVecAnalTypeMember_at (right_members, i);
			if (a->offset != b->offset || a->bitsize != b->bitsize
				|| a->count != b->count
				|| !snapshot_nullable_string_equal (a->name, b->name)
				|| !snapshot_nullable_string_equal (a->type, b->type)) {
				return false;
			}
		}
	} else if (left->kind == R_ANAL_BASE_TYPE_KIND_ENUM) {
		const size_t count = RVecAnalEnumCase_length (&left->enum_data.cases);
		if (count != RVecAnalEnumCase_length (&right->enum_data.cases)) {
			return false;
		}
		size_t i;
		for (i = 0; i < count; i++) {
			const RAnalEnumCase *a = RVecAnalEnumCase_at (&left->enum_data.cases, i);
			const RAnalEnumCase *b = RVecAnalEnumCase_at (&right->enum_data.cases, i);
			if (a->val != b->val
				|| !snapshot_nullable_string_equal (a->name, b->name)) {
				return false;
			}
		}
	}
	return true;
}
static bool snapshot_base_types_equal(const RList *left, const RList *right) {
	if (!left || !right || r_list_length (left) != r_list_length (right)) {
		return false;
	}
	RListIter *left_iter = r_list_iterator (left);
	RListIter *right_iter = r_list_iterator (right);
	while (left_iter && right_iter) {
		if (!snapshot_base_type_equal (left_iter->data, right_iter->data)) {
			return false;
		}
		left_iter = left_iter->n;
		right_iter = right_iter->n;
	}
	return !left_iter && !right_iter;
}
static bool snapshot_base_type_string_add(size_t *total, const char *string) {
	if (!string) {
		return true;
	}
	size_t bytes;
	return !r_add_overflow_size_t (strlen (string), 1, &bytes)
		&& !r_add_overflow_size_t (*total, bytes, total);
}
static bool snapshot_base_type_string_bytes(const RList *base_types, size_t *result) {
	size_t total = 0;
	RListIter *iter;
	RAnalBaseType *base;
	r_list_foreach (base_types, iter, base) {
		if (!base || !snapshot_base_type_string_add (&total, base->name)
			|| !snapshot_base_type_string_add (&total, base->type)) {
			return false;
		}
		switch (base->kind) {
		case R_ANAL_BASE_TYPE_KIND_STRUCT: {
			RAnalStructMember *member;
			R_VEC_FOREACH (&base->struct_data.members, member) {
				if (!snapshot_base_type_string_add (&total, member->name)
					|| !snapshot_base_type_string_add (&total, member->type)) {
					return false;
				}
			}
			break;
		}
		case R_ANAL_BASE_TYPE_KIND_UNION: {
			RAnalUnionMember *member;
			R_VEC_FOREACH (&base->union_data.members, member) {
				if (!snapshot_base_type_string_add (&total, member->name)
					|| !snapshot_base_type_string_add (&total, member->type)) {
					return false;
				}
			}
			break;
		}
		case R_ANAL_BASE_TYPE_KIND_ENUM: {
			RAnalEnumCase *cas;
			R_VEC_FOREACH (&base->enum_data.cases, cas) {
				if (!snapshot_base_type_string_add (&total, cas->name)) {
					return false;
				}
			}
			break;
		}
		default:
			break;
		}
	}
	*result = total;
	return true;
}
static void snapshot_type_resolver_select_current_roots(Sdb *type_db, RList *base_types) {
	RListIter *iter;
	RListIter *next;
	RAnalBaseType *base;
	r_list_foreach_safe (base_types, iter, next, base) {
		if (!base || R_STR_ISEMPTY (base->name)) {
			continue;
		}
		const char *current_kind = sdb_const_get (type_db, base->name, 0);
		const bool stale_atomic = base->kind == R_ANAL_BASE_TYPE_KIND_ATOMIC
			&& strcmp (r_str_get (current_kind), "type");
		const bool stale_typedef = base->kind == R_ANAL_BASE_TYPE_KIND_TYPEDEF
			&& strcmp (r_str_get (current_kind), "typedef");
		if (stale_atomic || stale_typedef) {
			r_list_delete (base_types, iter);
		}
	}
}
static bool snapshot_type_resolver_capture_cb(void *user, const char *name, const char *kind) {
	SnapshotTypeResolverCapture *capture = user;
	if (R_STR_ISEMPTY (name) || strcmp (r_str_get (kind), "type")
		|| strchr (name, '.')
		|| sdb_const_getf (capture->type_db, NULL, "type.%s", name)) {
		return true;
	}
	const ut64 bits = sdb_num_getf (capture->type_db, NULL, "type.%s.size", name);
	if (!bits) {
		return true;
	}
	RListIter *iter;
	RAnalBaseType *base;
	r_list_foreach (capture->base_types, iter, base) {
		if (base && base->kind == R_ANAL_BASE_TYPE_KIND_ATOMIC
			&& !strcmp (r_str_get (base->name), name)) {
			capture->valid = false;
			return false;
		}
	}
	size_t name_bytes;
	if (r_add_overflow_size_t (strlen (name), 1, &name_bytes)
		|| capture->base_type_count >= capture->limits->max_base_types
		|| name_bytes > capture->limits->max_base_type_string_bytes
			- capture->string_bytes) {
		capture->valid = false;
		return false;
	}
	base = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_ATOMIC);
	if (!base) {
		capture->valid = false;
		return false;
	}
	base->name = strdup (name);
	base->size = bits;
	if (!base->name || !r_list_append (capture->base_types, base)) {
		r_anal_base_type_free (base);
		capture->valid = false;
		return false;
	}
	capture->base_type_count++;
	capture->string_bytes += name_bytes;
	return true;
}
static RList *snapshot_type_resolver_capture(RAnal *anal, const RAnalFunctionSnapshotLimits *limits) {
	RList *base_types = r_anal_types_snapshot_with_limits (anal, limits);
	if (!base_types) {
		return NULL;
	}
	snapshot_type_resolver_select_current_roots (anal->sdb_types, base_types);
	SnapshotTypeResolverCapture capture = {
		.type_db = anal->sdb_types,
		.base_types = base_types,
		.limits = limits,
		.base_type_count = (size_t)r_list_length (base_types),
		.valid = true,
	};
	if (!snapshot_base_type_string_bytes (base_types, &capture.string_bytes)
		|| capture.base_type_count > limits->max_base_types
		|| capture.string_bytes > limits->max_base_type_string_bytes
		|| !sdb_foreach (anal->sdb_types, snapshot_type_resolver_capture_cb, &capture)
		|| !capture.valid) {
		r_list_free (base_types);
		return NULL;
	}
	r_list_sort (base_types, snapshot_base_type_compare);
	return base_types;
}
static bool snapshot_arch_char_kind(const char *arch, RAnalSnapshotTypeKind *kind) {
	if (R_STR_ISEMPTY (arch)) {
		return false;
	}
	static const char *signed_arches[] = { "x86", "mips", "sparc", NULL };
	static const char *unsigned_arches[] = { "arm", "ppc", "riscv", "s390", NULL };
	size_t i;
	for (i = 0; signed_arches[i]; i++) {
		if (!strcmp (arch, signed_arches[i])) {
			*kind = R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER;
			return true;
		}
	}
	for (i = 0; unsigned_arches[i]; i++) {
		if (!strcmp (arch, unsigned_arches[i])) {
			*kind = R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER;
			return true;
		}
	}
	return false;
}
static const RAnalBaseType *snapshot_type_find_unique_base(
	const RList *base_types, const char *name, RAnalBaseTypeKind kind,
	bool *ambiguous) {
	const RAnalBaseType *found = NULL;
	*ambiguous = false;
	RListIter *iter;
	RAnalBaseType *base;
	r_list_foreach (base_types, iter, base) {
		if (!base || base->kind != kind || strcmp (r_str_get (base->name), name)) {
			continue;
		}
		if (found) {
			*ambiguous = true;
			return NULL;
		}
		found = base;
	}
	return found;
}
static const RAnalBaseType *snapshot_type_find_bare_base(
	const SnapshotTypeGraphBuilder *builder, const char *name, bool *ambiguous) {
	static const RAnalBaseTypeKind preferred[] = {
		R_ANAL_BASE_TYPE_KIND_TYPEDEF,
		R_ANAL_BASE_TYPE_KIND_ATOMIC,
		R_ANAL_BASE_TYPE_KIND_ENUM,
		R_ANAL_BASE_TYPE_KIND_STRUCT,
	};
	const RAnalBaseType *bases[R_ARRAY_SIZE (preferred)] = {0};
	const RAnalBaseType *found = NULL;
	size_t i;
	*ambiguous = false;
	for (i = 0; i < R_ARRAY_SIZE (preferred); i++) {
		bases[i] = snapshot_type_find_unique_base (
			builder->base_types, name, preferred[i], ambiguous);
		if (*ambiguous) {
			return NULL;
		}
	}
	for (i = 0; i < R_ARRAY_SIZE (preferred); i++) {
		if (bases[i] && found) {
			*ambiguous = true;
			return NULL;
		}
		if (bases[i]) {
			found = bases[i];
		}
	}
	return found;
}
static void snapshot_type_strip_qualifiers(char *spec) {
	static const char *qualifiers[] = {
		"const", "volatile", "restrict", "__restrict", "_Atomic", NULL
	};
	size_t i;
	for (i = 0; qualifiers[i]; i++) {
		const size_t length = strlen (qualifiers[i]);
		char *cursor = spec;
		while ((cursor = strstr (cursor, qualifiers[i]))) {
			const bool starts_word = cursor == spec || !(isalnum ((unsigned char)cursor[-1])
				|| cursor[-1] == '_');
			char *after = cursor + length;
			const bool ends_word = !(isalnum ((unsigned char)*after) || *after == '_');
			if (!starts_word || !ends_word) {
				cursor = after;
				continue;
			}
			memmove (cursor, after, strlen (after) + 1);
		}
	}
	r_str_trim (spec);
	// Collapse the double blanks a removed qualifier leaves behind.
	char *read = spec;
	char *write = spec;
	bool blank = false;
	while (*read) {
		if (isspace ((unsigned char)*read)) {
			blank = true;
			read++;
			continue;
		}
		if (blank && write != spec) {
			*write++ = ' ';
		}
		blank = false;
		*write++ = *read++;
	}
	*write = '\0';
}
static char *snapshot_type_member_element_spec(const char *spec, ut64 *count) {
	*count = 1;
	char *element = r_str_trim_dup (spec);
	if (!element) {
		return NULL;
	}
	char *open = strchr (element, '[');
	if (!open) {
		return element;
	}
	char *close = strchr (open, ']');
	if (!close || close[1] != '\0' || close == open + 1) {
		free (element);
		return NULL;
	}
	*close = '\0';
	const char *digits = open + 1;
	const char *cursor;
	for (cursor = digits; *cursor; cursor++) {
		if (*cursor < '0' || *cursor > '9') {
			free (element);
			return NULL;
		}
	}
	const ut64 parsed = r_num_get (NULL, digits);
	if (!parsed) {
		free (element);
		return NULL;
	}
	*count = parsed;
	*open = '\0';
	r_str_trim (element);
	if (R_STR_ISEMPTY (element)) {
		free (element);
		return NULL;
	}
	return element;
}
static bool snapshot_type_spec_rejected(const char *spec) {
	return R_STR_ISEMPTY (spec) || strchr (spec, '[') || strchr (spec, ']')
		|| strchr (spec, '(') || strchr (spec, ')')
		|| strstr (spec, "atomic");
}
static SnapshotTypeGraphResult snapshot_type_unalias(
	const SnapshotTypeGraphBuilder *builder, const char *type, char **result) {
	char *current = r_str_trim_dup (type);
	if (!current) {
		return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
	}
	snapshot_type_strip_qualifiers (current);
	size_t depth;
	const size_t maximum_depth = (size_t)r_list_length (builder->base_types) + 1;
	for (depth = 0; depth < maximum_depth; depth++) {
		if (snapshot_type_spec_rejected (current)) {
			free (current);
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
		if (strchr (current, '*') || r_str_startswith (current, "struct ")
			|| r_str_startswith (current, "union ")) {
			*result = current;
			return SNAPSHOT_TYPE_GRAPH_VALID;
		}
		bool ambiguous;
		const RAnalBaseType *base = snapshot_type_find_bare_base (
			builder, current, &ambiguous);
		if (ambiguous) {
			free (current);
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
		if (!base || base->kind != R_ANAL_BASE_TYPE_KIND_TYPEDEF) {
			*result = current;
			return SNAPSHOT_TYPE_GRAPH_VALID;
		}
		if (R_STR_ISEMPTY (base->type)) {
			free (current);
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
		char *next = r_str_trim_dup (base->type);
		free (current);
		if (!next) {
			return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
		}
		current = next;
	}
	free (current);
	return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
}
static bool snapshot_type_integer_width_supported(ut64 bits) {
	return bits == 8 || bits == 16 || bits == 32 || bits == 64;
}
static SnapshotIntegerSyntax snapshot_type_integer_syntax(const char *spec) {
	SnapshotIntegerSyntax syntax = {0};
	const char *digits = NULL;
	if (r_str_startswith (spec, "uint")) {
		syntax.kind = R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER;
		digits = spec + strlen ("uint");
	} else if (r_str_startswith (spec, "int")) {
		syntax.kind = R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER;
		digits = spec + strlen ("int");
	}
	if (digits && *digits) {
		ut64 bits = 0;
		const char *cursor = digits;
		while (*cursor >= '0' && *cursor <= '9') {
			if (bits > (UT64_MAX - (ut64)(*cursor - '0')) / 10) {
				return syntax;
			}
			bits = bits * 10 + (ut64)(*cursor++ - '0');
		}
		if (!strcmp (cursor, "_t") && snapshot_type_integer_width_supported (bits)) {
			syntax.valid = true;
			syntax.required_bits = bits;
		}
		return syntax;
	}
	static const char *signed_specs[] = {
		"signed char", "short", "short int", "signed short",
		"signed short int", "int", "signed", "signed int", "long",
		"long int", "signed long", "signed long int", "long long",
		"long long int", "signed long long", "signed long long int",
	};
	static const char *unsigned_specs[] = {
		"unsigned char", "unsigned short", "unsigned short int", "unsigned",
		"unsigned int", "unsigned long", "unsigned long int",
		"unsigned long long", "unsigned long long int",
		// C fixes _Bool as unsigned, so unlike plain char this needs no
		// per-target choice. Both compilers spell it _Bool in debug info.
		"_Bool", "bool",
	};
	size_t i;
	for (i = 0; i < R_ARRAY_SIZE (signed_specs); i++) {
		if (!strcmp (spec, signed_specs[i])) {
			syntax.valid = true;
			syntax.kind = R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER;
			return syntax;
		}
	}
	for (i = 0; i < R_ARRAY_SIZE (unsigned_specs); i++) {
		if (!strcmp (spec, unsigned_specs[i])) {
			syntax.valid = true;
			syntax.kind = R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER;
			return syntax;
		}
	}
	return syntax;
}
static SnapshotTypeGraphResult snapshot_type_integer_spec(
	const SnapshotTypeGraphBuilder *builder, const char *type,
	RAnalSnapshotTypeKind *kind, ut64 *bits) {
	char *current = r_str_trim_dup (type);
	if (!current) {
		return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
	}
	snapshot_type_strip_qualifiers (current);
	bool have_kind = false;
	ut64 required_bits = 0;
	size_t depth;
	const size_t maximum_depth = (size_t)r_list_length (builder->base_types) + 1;
	for (depth = 0; depth < maximum_depth; depth++) {
		if (snapshot_type_spec_rejected (current) || strchr (current, '*')
			|| r_str_startswith (current, "struct ")
			|| r_str_startswith (current, "union ")) {
			break;
		}
		SnapshotIntegerSyntax syntax = snapshot_type_integer_syntax (current);
		// Plain char is an integer type of its own, distinct from both signed
		// and unsigned char, so the syntax table cannot name its kind. Take it
		// from the target when the target's choice is known.
		if (!syntax.valid && !strcmp (current, "char") && builder->char_kind_known) {
			syntax.valid = true;
			syntax.kind = builder->char_kind;
		}
		if (syntax.valid) {
			if ((have_kind && *kind != syntax.kind)
				|| (required_bits && syntax.required_bits
					&& required_bits != syntax.required_bits)) {
				break;
			}
			*kind = syntax.kind;
			have_kind = true;
			if (syntax.required_bits) {
				required_bits = syntax.required_bits;
			}
		}
		char *base_name = r_str_sanitize_sdb_key (current);
		if (!base_name) {
			free (current);
			return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
		}
		bool ambiguous;
		const RAnalBaseType *base = snapshot_type_find_bare_base (
			builder, base_name, &ambiguous);
		free (base_name);
		if (ambiguous) {
			break;
		}
		if (!base) {
			break;
		}
		// An enumeration is an integer whose width the base type records. Its
		// signedness is not a target choice like plain char: it follows from the
		// values, since a negative enumerator can only be held by a signed type.
		if (base->kind == R_ANAL_BASE_TYPE_KIND_ENUM) {
			if (!snapshot_type_integer_width_supported (base->size)
				|| (required_bits && required_bits != base->size)) {
				break;
			}
			bool has_negative_case = false;
			RAnalEnumCase *enum_case;
			R_VEC_FOREACH (&base->enum_data.cases, enum_case) {
				if (enum_case && enum_case->val < 0) {
					has_negative_case = true;
					break;
				}
			}
			const RAnalSnapshotTypeKind enum_kind = has_negative_case
				? R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER
				: R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER;
			if (have_kind && *kind != enum_kind) {
				break;
			}
			*kind = enum_kind;
			*bits = base->size;
			free (current);
			return SNAPSHOT_TYPE_GRAPH_VALID;
		}
		if (base->kind == R_ANAL_BASE_TYPE_KIND_ATOMIC) {
			if (!have_kind || !snapshot_type_integer_width_supported (base->size)
				|| (required_bits && required_bits != base->size)) {
				break;
			}
			*bits = base->size;
			free (current);
			return SNAPSHOT_TYPE_GRAPH_VALID;
		}
		if (base->kind != R_ANAL_BASE_TYPE_KIND_TYPEDEF
			|| R_STR_ISEMPTY (base->type)) {
			break;
		}
		char *next = r_str_trim_dup (base->type);
		if (!next) {
			free (current);
			return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
		}
		free (current);
		current = next;
	}
	free (current);
	return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
}
static SnapshotTypeGraphResult snapshot_type_add_integer(
	SnapshotTypeGraphBuilder *builder, const char *type,
	RAnalSnapshotTypeId *result_id) {
	RAnalSnapshotTypeKind kind;
	ut64 bits;
	SnapshotTypeGraphResult result = snapshot_type_integer_spec (
		builder, type, &kind, &bits);
	// Integer width is bounded by what the graph can describe, not by pointer
	// width. An int64_t on a 32-bit target is wider than a pointer and entirely
	// ordinary, and snapshot_type_integer_width_supported already fixed the
	// real ceiling when the width was resolved.
	if (result != SNAPSHOT_TYPE_GRAPH_VALID) {
		return result;
	}
	size_t i;
	for (i = 0; i < builder->graph->num_types; i++) {
		RAnalSnapshotType *existing = &builder->graph->types[i];
		if (existing->kind == kind && existing->size_bits == bits
			&& existing->align_bits == bits) {
			*result_id = existing->id;
			return SNAPSHOT_TYPE_GRAPH_VALID;
		}
	}
	if (builder->graph->num_types >= builder->type_capacity
		|| builder->graph->num_types >= UT32_MAX) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	RAnalSnapshotType *snapshot_type =
		&builder->graph->types[builder->graph->num_types];
	snapshot_type->id = (RAnalSnapshotTypeId)builder->graph->num_types;
	snapshot_type->kind = kind;
	snapshot_type->size_bits = bits;
	snapshot_type->align_bits = bits;
	snapshot_type->target_type_id = R_ANAL_SNAPSHOT_TYPE_ID_INVALID;
	snapshot_type->aggregate_id = UT32_MAX;
	builder->graph->num_types++;
	*result_id = snapshot_type->id;
	return SNAPSHOT_TYPE_GRAPH_VALID;
}
static bool snapshot_type_align_up(ut64 value, ut64 alignment, ut64 *result) {
	if (!alignment || (alignment & (alignment - 1))) {
		return false;
	}
	ut64 remainder = value & (alignment - 1);
	ut64 padding = remainder? alignment - remainder: 0;
	return !r_add_overflow (value, padding, result);
}
static SnapshotTypeGraphResult snapshot_type_resolve_struct(
	const SnapshotTypeGraphBuilder *builder, const char *type,
	const RAnalBaseType **result_base) {
	char *spec = NULL;
	SnapshotTypeGraphResult result = snapshot_type_unalias (builder, type, &spec);
	if (result != SNAPSHOT_TYPE_GRAPH_VALID) {
		return result;
	}
	const char *name = spec;
	if (r_str_startswith (name, "struct ")) {
		name = r_str_trim_head_ro (name + strlen ("struct "));
	}
	if (R_STR_ISEMPTY (name) || strchr (name, '*')
		|| r_str_startswith (name, "union ")) {
		free (spec);
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	bool ambiguous;
	const RAnalBaseType *base = snapshot_type_find_unique_base (
		builder->base_types, name, R_ANAL_BASE_TYPE_KIND_STRUCT, &ambiguous);
	free (spec);
	if (ambiguous || !base) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	*result_base = base;
	return SNAPSHOT_TYPE_GRAPH_VALID;
}
static SnapshotTypeGraphResult snapshot_type_add_struct(
	SnapshotTypeGraphBuilder *builder, const char *type,
	RAnalSnapshotTypeId *result_id) {
	const RAnalBaseType *base = NULL;
	SnapshotTypeGraphResult result = snapshot_type_resolve_struct (
		builder, type, &base);
	if (result != SNAPSHOT_TYPE_GRAPH_VALID) {
		return result;
	}
	size_t i;
	for (i = 0; i < builder->graph->num_aggregates; i++) {
		if (builder->aggregate_sources[i] == base) {
			*result_id = builder->graph->aggregates[i].type_id;
			return SNAPSHOT_TYPE_GRAPH_VALID;
		}
	}
	if (builder->graph->num_types >= builder->type_capacity
		|| builder->graph->num_types >= UT32_MAX
		|| builder->graph->num_aggregates >= builder->aggregate_capacity
		|| builder->graph->num_aggregates >= UT32_MAX) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	const size_t type_index = builder->graph->num_types++;
	const size_t aggregate_index = builder->graph->num_aggregates++;
	RAnalSnapshotType *snapshot_type = &builder->graph->types[type_index];
	snapshot_type->id = (RAnalSnapshotTypeId)type_index;
	snapshot_type->kind = R_ANAL_SNAPSHOT_TYPE_STRUCT;
	snapshot_type->target_type_id = R_ANAL_SNAPSHOT_TYPE_ID_INVALID;
	snapshot_type->aggregate_id = (ut32)aggregate_index;
	RAnalSnapshotAggregateLayout *aggregate =
		&builder->graph->aggregates[aggregate_index];
	aggregate->id = (ut32)aggregate_index;
	aggregate->type_id = snapshot_type->id;
	const char *presentation_name = type;
	if (r_str_startswith (presentation_name, "struct ")) {
		presentation_name = r_str_trim_head_ro (
			presentation_name + strlen ("struct "));
	}
	if (R_STR_ISEMPTY (presentation_name) || strchr (presentation_name, '*')) {
		presentation_name = base->name;
	}
	aggregate->name = strdup (r_str_get (presentation_name));
	builder->aggregate_sources[aggregate_index] = base;
	if (!aggregate->name) {
		return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
	}
	RVecAnalTypeMember *base_members = r_anal_base_type_members (base);
	aggregate->num_members = RVecAnalTypeMember_length (base_members);
	if (!aggregate->num_members) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	size_t allocation_size;
	if (r_mul_overflow_size_t (aggregate->num_members,
			sizeof (RAnalSnapshotAggregateMember), &allocation_size)) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	aggregate->members = calloc (1, allocation_size);
	if (!aggregate->members) {
		return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
	}
	ut64 cursor = 0;
	ut64 maximum_alignment = 0;
	RAnalTypeMember *base_member;
	size_t member_index = 0;
	R_VEC_FOREACH (base_members, base_member) {
		if (member_index >= aggregate->num_members || !base_member
			|| R_STR_ISEMPTY (base_member->name)
			|| R_STR_ISEMPTY (base_member->type)) {
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
		size_t prior;
		for (prior = 0; prior < member_index; prior++) {
			if (!strcmp (aggregate->members[prior].name, base_member->name)) {
				return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
			}
		}
		// A member is a type like any other. Resolving only integers made every
		// struct holding a pointer or a nested struct unrepresentable, which is
		// the shape of most non-trivial C structs.
		ut64 spec_count;
		char *element_spec = snapshot_type_member_element_spec (
			base_member->type, &spec_count);
		if (!element_spec) {
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
		RAnalSnapshotTypeId member_type_id;
		result = snapshot_type_add_root (
			builder, element_spec, &member_type_id);
		free (element_spec);
		if (result != SNAPSHOT_TYPE_GRAPH_VALID) {
			return result;
		}
		const RAnalSnapshotType *member_type =
			&builder->graph->types[member_type_id];
		if (base_member->bitsize
			|| base_member->offset > UT64_MAX / 8) {
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
		// An array member repeats its element type. Fold that extent into the
		// member's exact size; the consumer needs the occupied range, not a
		// second copy of the source spelling's element count.
		const ut64 member_count = base_member->count
			? (ut64)base_member->count : spec_count;
		ut64 member_size_bits;
		if (r_mul_overflow (member_type->size_bits, member_count, &member_size_bits)) {
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
		ut64 expected_offset;
		if (!snapshot_type_align_up (cursor, member_type->align_bits, &expected_offset)
			|| expected_offset != (ut64)base_member->offset * 8
			|| r_add_overflow (expected_offset, member_size_bits, &cursor)) {
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
		RAnalSnapshotAggregateMember *member = &aggregate->members[member_index];
		member->member_id = (ut32)member_index;
		member->type_id = member_type_id;
		member->offset_bits = expected_offset;
		member->size_bits = member_size_bits;
		member->name = strdup (base_member->name);
		if (!member->name) {
			return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
		}
		maximum_alignment = R_MAX (maximum_alignment, member_type->align_bits);
		member_index++;
	}
	ut64 size_bits;
	if (!snapshot_type_align_up (cursor, maximum_alignment, &size_bits)
		|| (base->size && base->size != size_bits)) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	aggregate->size_bits = size_bits;
	aggregate->align_bits = maximum_alignment;
	aggregate->complete = true;
	snapshot_type->size_bits = size_bits;
	snapshot_type->align_bits = maximum_alignment;
	*result_id = snapshot_type->id;
	return SNAPSHOT_TYPE_GRAPH_VALID;
}
static SnapshotTypeGraphResult snapshot_type_add_pointer(
	SnapshotTypeGraphBuilder *builder, const char *type,
	RAnalSnapshotTypeId *result_id) {
	char *spec = NULL;
	SnapshotTypeGraphResult result = snapshot_type_unalias (builder, type, &spec);
	if (result != SNAPSHOT_TYPE_GRAPH_VALID) {
		return result;
	}
	// Split at the last star so the pointee keeps any remaining ones: a
	// pointer to a pointer is described by describing what it points at, which
	// is another pointer this function can build. Refusing them left `char **`
	// unrepresentable, and with it the argv of every main.
	char *star = strrchr (spec, '*');
	if (!star || *r_str_trim_head_ro (star + 1)) {
		free (spec);
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	char *pointee = r_str_trim_ndup (spec, (size_t)(star - spec));
	free (spec);
	if (!pointee) {
		return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
	}
	RAnalSnapshotTypeId target_id;
	result = snapshot_type_add_integer (builder, pointee, &target_id);
	if (result == SNAPSHOT_TYPE_GRAPH_UNSUPPORTED) {
		result = strchr (pointee, '*')
			? snapshot_type_add_pointer (builder, pointee, &target_id)
			: snapshot_type_add_struct (builder, pointee, &target_id);
	}
	free (pointee);
	if (result != SNAPSHOT_TYPE_GRAPH_VALID) {
		return result;
	}
	size_t i;
	for (i = 0; i < builder->graph->num_types; i++) {
		RAnalSnapshotType *existing = &builder->graph->types[i];
		if (existing->kind == R_ANAL_SNAPSHOT_TYPE_POINTER
			&& existing->target_type_id == target_id
			&& existing->size_bits == builder->pointer_bits) {
			*result_id = existing->id;
			return SNAPSHOT_TYPE_GRAPH_VALID;
		}
	}
	if (builder->graph->num_types >= builder->type_capacity
		|| builder->graph->num_types >= UT32_MAX) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	RAnalSnapshotType *snapshot_type =
		&builder->graph->types[builder->graph->num_types];
	snapshot_type->id = (RAnalSnapshotTypeId)builder->graph->num_types;
	snapshot_type->kind = R_ANAL_SNAPSHOT_TYPE_POINTER;
	snapshot_type->size_bits = builder->pointer_bits;
	snapshot_type->align_bits = builder->pointer_bits;
	snapshot_type->target_type_id = target_id;
	snapshot_type->aggregate_id = UT32_MAX;
	builder->graph->num_types++;
	*result_id = snapshot_type->id;
	return SNAPSHOT_TYPE_GRAPH_VALID;
}
static SnapshotTypeGraphResult snapshot_type_add_root(
	SnapshotTypeGraphBuilder *builder, const char *type,
	RAnalSnapshotTypeId *result_id) {
	SnapshotTypeGraphResult result = snapshot_type_add_integer (
		builder, type, result_id);
	if (result != SNAPSHOT_TYPE_GRAPH_UNSUPPORTED) {
		return result;
	}
	char *spec = NULL;
	result = snapshot_type_unalias (builder, type, &spec);
	if (result != SNAPSHOT_TYPE_GRAPH_VALID) {
		return result;
	}
	const bool pointer = strchr (spec, '*') != NULL;
	free (spec);
	if (pointer) {
		return snapshot_type_add_pointer (builder, type, result_id);
	}
	// An aggregate could only enter the graph as something a pointer pointed at,
	// so a struct held directly -- returned by value, or kept in a frame slot --
	// contributed no layout at all and a consumer had to invent its width and its
	// member names from the offsets it saw touched.
	return snapshot_type_add_struct (builder, type, result_id);
}
static bool snapshot_type_carrier_project(
	const RAnalSnapshotTypeGraph *graph, RAnalSnapshotTypeId type_id,
	const RAnalSnapshotRegisterStorage *storage,
	RAnalSnapshotCarrierProjection *projection) {
	if (type_id >= graph->num_types || !storage->size) {
		return false;
	}
	const RAnalSnapshotType *type = &graph->types[type_id];
	const ut64 carrier_bits = (ut64)storage->size * 8;
	if (!type->size_bits || type->size_bits > carrier_bits
		|| (type->kind == R_ANAL_SNAPSHOT_TYPE_POINTER
			&& type->size_bits != carrier_bits)) {
		return false;
	}
	projection->kind = type->size_bits == carrier_bits
		? R_ANAL_SNAPSHOT_CARRIER_FULL
		: R_ANAL_SNAPSHOT_CARRIER_LOW_BITS;
	projection->size_bits = type->size_bits;
	return true;
}
static SnapshotTypeGraphResult function_type_graph_snapshot_collect(
	RAnal *anal, const RAnalFcnContext *ctx, RAnalFunctionSnapshot *snapshot,
	const RAnalFunctionSnapshotLimits *limits) {
	RAnalFunctionInterfaceSnapshot *interface = &snapshot->function_interface;
	function_logical_types_clear (interface);
	if (!interface->complete || !ctx->signature) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	// Pointer width is the only thing the builder takes from the target: it
	// sizes pointer types and bounds integer widths. Nothing in it is specific
	// to 64-bit, so a 32-bit target has no reason to lose its type graph.
	const ut64 pointer_bits = anal->config? (ut64)anal->config->bits: 0;
	if (pointer_bits != 32 && pointer_bits != 64) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	size_t base_count = (size_t)r_list_length (snapshot->base_types);
	size_t child_count = 0;
	RListIter *base_iter;
	RAnalBaseType *base;
	r_list_foreach (snapshot->base_types, base_iter, base) {
		if (base && (base->kind == R_ANAL_BASE_TYPE_KIND_STRUCT
				|| base->kind == R_ANAL_BASE_TYPE_KIND_UNION)
			&& r_add_overflow_size_t (child_count,
				RVecAnalTypeMember_length (r_anal_base_type_members (base)),
				&child_count)) {
			return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
	}
	// A local's type is as much a source type as a parameter's, so the slots
	// that declare one are roots too and the graph has to have room for them.
	const size_t slot_count = ctx->fcn_slots
		? (size_t)r_list_length (ctx->fcn_slots): 0;
	size_t root_capacity;
	if (r_add_overflow_size_t (interface->num_parameters, 1, &root_capacity)
		|| r_add_overflow_size_t (root_capacity, slot_count, &root_capacity)
		|| r_mul_overflow_size_t (root_capacity, 2, &root_capacity)) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	size_t type_capacity;
	if (r_add_overflow_size_t (root_capacity, base_count, &type_capacity)
		|| r_add_overflow_size_t (type_capacity, child_count, &type_capacity)
		|| type_capacity > UT32_MAX || base_count > UT32_MAX
		|| type_capacity > limits->max_type_graph_types
		|| base_count > limits->max_type_graph_aggregates
		|| child_count > limits->max_type_graph_members) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	RAnalSnapshotTypeGraph *graph = &snapshot->type_graph;
	size_t allocation_size;
	if (type_capacity && r_mul_overflow_size_t (
			type_capacity, sizeof (RAnalSnapshotType), &allocation_size)) {
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	graph->types = type_capacity? calloc (1, allocation_size): NULL;
	if (type_capacity && !graph->types) {
		return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
	}
	if (base_count && r_mul_overflow_size_t (
			base_count, sizeof (RAnalSnapshotAggregateLayout), &allocation_size)) {
		snapshot_type_graph_fini (graph);
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	graph->aggregates = base_count? calloc (1, allocation_size): NULL;
	if (base_count && !graph->aggregates) {
		snapshot_type_graph_fini (graph);
		return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
	}
	const RAnalBaseType **aggregate_sources = NULL;
	if (base_count && r_mul_overflow_size_t (
			base_count, sizeof (RAnalBaseType *), &allocation_size)) {
		snapshot_type_graph_fini (graph);
		return SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	if (base_count) {
		aggregate_sources = calloc (1, allocation_size);
		if (!aggregate_sources) {
			snapshot_type_graph_fini (graph);
			return SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
		}
	}
	RAnalSnapshotTypeKind char_kind = R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER;
	const bool char_kind_known = snapshot_arch_char_kind (
		anal->config? anal->config->arch: NULL, &char_kind);
	SnapshotTypeGraphBuilder builder = {
		.base_types = snapshot->base_types,
		.graph = graph,
		.aggregate_sources = aggregate_sources,
		.type_capacity = type_capacity,
		.aggregate_capacity = base_count,
		.pointer_bits = pointer_bits,
		.char_kind = char_kind,
		.char_kind_known = char_kind_known,
	};
	SnapshotTypeGraphResult result = SNAPSHOT_TYPE_GRAPH_VALID;
	RListIter *iter;
	RAnalFunctionParam *parameter;
	size_t index = 0;
	r_list_foreach (ctx->signature->params, iter, parameter) {
		if (!parameter || index >= interface->num_parameters) {
			result = SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
			break;
		}
		RAnalSnapshotParameter *snapshot_parameter = &interface->parameters[index];
		result = snapshot_type_add_root (
			&builder, parameter->type, &snapshot_parameter->logical_type_id);
		if (result != SNAPSHOT_TYPE_GRAPH_VALID
			|| !snapshot_type_carrier_project (graph,
				snapshot_parameter->logical_type_id, &snapshot_parameter->storage,
				&snapshot_parameter->carrier)) {
			if (result == SNAPSHOT_TYPE_GRAPH_VALID) {
				result = SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
			}
			break;
		}
		index++;
	}
	if (result == SNAPSHOT_TYPE_GRAPH_VALID && index != interface->num_parameters) {
		result = SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	if (result == SNAPSHOT_TYPE_GRAPH_VALID
		&& interface->return_kind == R_ANAL_SNAPSHOT_RETURN_REGISTER) {
		result = snapshot_type_add_root (
			&builder, ctx->signature->ret_type, &interface->return_type_id);
		if (result == SNAPSHOT_TYPE_GRAPH_VALID
			&& !snapshot_type_carrier_project (graph, interface->return_type_id,
				&interface->return_storage, &interface->return_carrier)) {
			result = SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
		}
	} else if (result == SNAPSHOT_TYPE_GRAPH_VALID
		&& interface->return_kind != R_ANAL_SNAPSHOT_RETURN_VOID) {
		result = SNAPSHOT_TYPE_GRAPH_UNSUPPORTED;
	}
	// Root what the locals are declared as. A struct a function only ever keeps
	// in a frame slot reached the graph through nothing, so its layout was absent
	// and a consumer had to invent both its width and its member names. A slot
	// whose type does not resolve is left alone rather than failing the graph,
	// because a local is not what the interface rests on.
	if (result == SNAPSHOT_TYPE_GRAPH_VALID && ctx->fcn_slots) {
		RListIter *slot_iter;
		RAnalFcnSlot *slot;
		r_list_foreach (ctx->fcn_slots, slot_iter, slot) {
			if (!slot || R_STR_ISEMPTY (slot->type)) {
				continue;
			}
			ut32 slot_type_id = 0;
			if (snapshot_type_add_root (&builder, slot->type, &slot_type_id)
					== SNAPSHOT_TYPE_GRAPH_NO_MEMORY) {
				result = SNAPSHOT_TYPE_GRAPH_NO_MEMORY;
				break;
			}
		}
	}
	free (aggregate_sources);
	if (result != SNAPSHOT_TYPE_GRAPH_VALID) {
		snapshot_type_graph_fini (graph);
		function_logical_types_clear (interface);
		return result;
	}
	graph->complete = true;
	interface->logical_types_complete = true;
	return SNAPSHOT_TYPE_GRAPH_VALID;
}
static int call_site_interface_snapshot_compare(const void *left, const void *right) {
	const RAnalCallSiteInterfaceSnapshot *a = left;
	const RAnalCallSiteInterfaceSnapshot *b = right;
	if (a->instruction_addr < b->instruction_addr) {
		return -1;
	}
	if (a->instruction_addr > b->instruction_addr) {
		return 1;
	}
	if (a->target_addr < b->target_addr) {
		return -1;
	}
	return a->target_addr > b->target_addr? 1: 0;
}
static bool call_site_interface_snapshot_collect_one(
	RAnal *anal, const RAnalFcnCallee *callee,
	RAnalCallSiteInterfaceSnapshot *interface,
	const RAnalFunctionSnapshotLimits *limits) {
	interface->instruction_addr = callee->call_addr;
	interface->target_addr = callee->addr;
	interface->transfer = callee->transfer;
	// A slot is not code, so no function is looked up at it: the relocation
	// named the callee when it was collected, and the name and prototype it
	// gave travel on the callee itself.
	const bool through_slot = callee->transfer == R_ANAL_CALL_TRANSFER_TAIL_SLOT;
	RAnalFunction *target = through_slot? NULL
		: r_anal_get_fcn_in (anal, callee->addr, R_ANAL_FCN_TYPE_ANY);
	const bool target_is_exact = target && target->addr == callee->addr;
	const char *target_name = target_is_exact? target->name: through_slot? callee->name: NULL;
	if (R_STR_ISNOTEMPTY (target_name)) {
		interface->target_name = strdup (target_name);
		if (!interface->target_name) {
			return false;
		}
	}
	if (!callee->signature || (!target_is_exact && !through_slot)) {
		return true;
	}
	const char *calling_convention = callee->signature->callconv;
	if (R_STR_ISEMPTY (calling_convention)
		|| !r_anal_cc_exist (anal, calling_convention)) {
		return true;
	}
	interface->calling_convention = strdup (calling_convention);
	if (!interface->calling_convention) {
		return false;
	}
	/* A variadic signature carries the ellipsis as a trailing parameter. It
	 * names no storage, so counting it as an argument leaves a slot the
	 * convention cannot fill and marks the whole call site incomplete. Record it
	 * as variadic and describe only the fixed arguments, the way argument
	 * recovery already does elsewhere. `r_type_arg_is_vararg` is the canonical
	 * test; see the note on the interface path above for why the shorter
	 * spelling silently misses two entries. */
	size_t argument_count = (size_t)r_list_length (callee->signature->params);
	bool signature_variadic = false;
	if (argument_count > 0) {
		RAnalFunctionParam *last = r_list_get_n (callee->signature->params,
			(int)(argument_count - 1));
		if (last && r_type_arg_is_vararg (last->type, last->name)) {
			signature_variadic = true;
			argument_count--;
		}
	}
	if (argument_count > INT_MAX || argument_count > UT32_MAX
		|| argument_count > limits->max_call_site_parameters) {
		return false;
	}
	size_t allocation_size;
	if (r_mul_overflow (argument_count, sizeof (RAnalSnapshotParameter), &allocation_size)) {
		return false;
	}
	if (allocation_size) {
		interface->arguments = calloc (1, allocation_size);
		if (!interface->arguments) {
			return false;
		}
	}
	interface->num_arguments = argument_count;
	bool arguments_complete = true;
	RListIter *iter;
	RAnalFunctionParam *argument;
	size_t index = 0;
	r_list_foreach (callee->signature->params, iter, argument) {
		if (index >= argument_count) {
			break;
		}
		RAnalSnapshotParameter *snapshot_argument = &interface->arguments[index];
		snapshot_argument->index = (ut32)index;
		snapshot_argument->logical_type_id = R_ANAL_SNAPSHOT_TYPE_ID_INVALID;
		memset (&snapshot_argument->carrier, 0, sizeof (snapshot_argument->carrier));
		if (!argument || R_STR_ISEMPTY (argument->type)) {
			arguments_complete = false;
		}
		const char *place = r_anal_cc_argloc (
			anal, calling_convention, (int)index, 0, (int)argument_count);
		RAnalCCArgSlot slot = {0};
		if (R_STR_ISEMPTY (place) || *place == '^' || *place == '{'
			|| !r_anal_cc_argslot (anal, calling_convention,
				(int)index, (int)argument_count, false, &slot)
			|| !slot.reg) {
			arguments_complete = false;
			index++;
			continue;
		}
		SnapshotStorageResult collected = snapshot_register_storage_collect (
			anal, slot.reg, false, &snapshot_argument->storage);
		if (collected == SNAPSHOT_STORAGE_NO_MEMORY) {
			return false;
		}
		if (collected != SNAPSHOT_STORAGE_VALID) {
			arguments_complete = false;
		}
		index++;
	}
	if (index != argument_count
		|| snapshot_parameter_storages_overlap (interface->arguments, argument_count)) {
		arguments_complete = false;
	}
	interface->variadic = (target && target->is_variadic) || signature_variadic;
	interface->noreturn = callee->signature->noreturn || (target && target->is_noreturn);
	bool result_complete = false;
	if (!strcmp (r_str_get (callee->signature->ret_type), "void")) {
		interface->result_kind = R_ANAL_SNAPSHOT_RETURN_VOID;
		result_complete = true;
	} else if (R_STR_ISNOTEMPTY (callee->signature->ret_type)) {
		const char *return_name = r_anal_cc_ret (anal, calling_convention, 0);
		const char *second_return = r_anal_cc_ret (anal, calling_convention, 1);
		if (R_STR_ISNOTEMPTY (return_name) && *return_name != '{'
			&& *return_name != '^' && R_STR_ISEMPTY (second_return)) {
			SnapshotStorageResult collected = snapshot_register_storage_collect (
				anal, return_name, false, &interface->result_storage);
			if (collected == SNAPSHOT_STORAGE_NO_MEMORY) {
				return false;
			}
			if (collected == SNAPSHOT_STORAGE_VALID) {
				interface->result_kind = R_ANAL_SNAPSHOT_RETURN_REGISTER;
				result_complete = true;
			}
		}
	}
	// Completeness describes the prototype, not the call instruction. Xrefs
	// establish which callee is reached, so the argument and result carriers
	// resolved above are exactly as good as the callee's own signature; which
	// lifted operation performs the call is a separate question, answered
	// downstream by matching this instruction and target address. Reporting
	// the prototype as incomplete because the identity is settled elsewhere
	// withholds what was recovered here.
	interface->complete = arguments_complete && result_complete;
	return true;
}
static bool call_site_interfaces_snapshot_collect(
	RAnal *anal, const RAnalFcnContext *ctx, RAnalFunctionSnapshot *snapshot,
	const RAnalFunctionSnapshotLimits *limits) {
	size_t count = (size_t)r_list_length (ctx->callees);
	if (!count) {
		return true;
	}
	if (count > limits->max_call_sites) {
		return false;
	}
	size_t total_arguments = 0;
	RListIter *preflight_iter;
	RAnalFcnCallee *preflight_callee;
	r_list_foreach (ctx->callees, preflight_iter, preflight_callee) {
		const int listed = preflight_callee && preflight_callee->signature
			&& preflight_callee->signature->params
			? r_list_length (preflight_callee->signature->params): 0;
		if (listed < 0 || (size_t)listed > limits->max_call_site_parameters
			|| r_add_overflow_size_t (
				total_arguments, (size_t)listed, &total_arguments)
			|| total_arguments > limits->max_total_call_site_parameters) {
			return false;
		}
	}
	size_t allocation_size;
	if (r_mul_overflow (count, sizeof (RAnalCallSiteInterfaceSnapshot), &allocation_size)) {
		return false;
	}
	snapshot->call_site_interfaces = calloc (1, allocation_size);
	if (!snapshot->call_site_interfaces) {
		return false;
	}
	snapshot->num_call_site_interfaces = count;
	RListIter *iter;
	RAnalFcnCallee *callee;
	size_t index = 0;
	r_list_foreach (ctx->callees, iter, callee) {
		if (!callee || index >= count
			|| !call_site_interface_snapshot_collect_one (
				anal, callee, &snapshot->call_site_interfaces[index], limits)) {
			return false;
		}
		index++;
	}
	if (index != count) {
		return false;
	}
	qsort (snapshot->call_site_interfaces, count,
		sizeof (RAnalCallSiteInterfaceSnapshot), call_site_interface_snapshot_compare);
	return true;
}
static bool snapshot_string_budget_add(const char *string, size_t limit, size_t *used) {
	if (!string) {
		return true;
	}
	size_t bytes;
	return !r_add_overflow_size_t (strlen (string), 1, &bytes)
		&& !r_add_overflow_size_t (*used, bytes, used) && *used <= limit;
}
static bool snapshot_signature_budget_add(const RAnalFunctionSignature *signature,
		const RAnalFunctionSnapshotLimits *limits, size_t *items, size_t *strings) {
	if (!signature) {
		return true;
	}
	const int listed = signature->params? r_list_length (signature->params): 0;
	if (listed < 0 || (size_t)listed > limits->max_interface_parameters
		|| !snapshot_string_budget_add (signature->signature,
			limits->max_context_string_bytes, strings)
		|| !snapshot_string_budget_add (signature->ret_type,
			limits->max_context_string_bytes, strings)
		|| !snapshot_string_budget_add (signature->callconv,
			limits->max_context_string_bytes, strings)) {
		return false;
	}
	RListIter *iter;
	RAnalFunctionParam *parameter;
	r_list_foreach (signature->params, iter, parameter) {
		if (!parameter || r_add_overflow_size_t (*items, 1, items)
			|| *items > limits->max_context_items
			|| !snapshot_string_budget_add (parameter->name,
				limits->max_context_string_bytes, strings)
			|| !snapshot_string_budget_add (parameter->type,
				limits->max_context_string_bytes, strings)) {
			return false;
		}
	}
	return true;
}
static bool snapshot_context_within_limits(const RAnalFunctionSnapshot *snapshot,
		const RAnalFunctionSnapshotLimits *limits) {
	size_t items = 0;
	size_t strings = 0;
	const RAnalFcnContext *ctx = &snapshot->context;
	if (!snapshot_string_budget_add (snapshot->arch_id,
			limits->max_context_string_bytes, &strings)
		|| !snapshot_string_budget_add (snapshot->cpu_id,
			limits->max_context_string_bytes, &strings)
		|| !snapshot_string_budget_add (snapshot->function_name,
			limits->max_context_string_bytes, &strings)
		|| !snapshot_signature_budget_add (ctx->signature, limits, &items, &strings)) {
		return false;
	}
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (ctx->fcn_slots, iter, slot) {
		if (!slot || r_add_overflow_size_t (items, 1, &items)
			|| items > limits->max_context_items
			|| !snapshot_string_budget_add (slot->name,
				limits->max_context_string_bytes, &strings)
			|| !snapshot_string_budget_add (slot->type,
				limits->max_context_string_bytes, &strings)
			|| !snapshot_string_budget_add (slot->base_name,
				limits->max_context_string_bytes, &strings)
			|| !snapshot_string_budget_add (slot->home_reg,
				limits->max_context_string_bytes, &strings)) {
			return false;
		}
	}
	RAnalFcnCallee *callee;
	r_list_foreach (ctx->callees, iter, callee) {
		if (!callee || r_add_overflow_size_t (items, 1, &items)
			|| items > limits->max_context_items
			|| !snapshot_string_budget_add (callee->name,
				limits->max_context_string_bytes, &strings)
			|| !snapshot_signature_budget_add (
				callee->signature, limits, &items, &strings)) {
			return false;
		}
	}
	return true;
}
static bool snapshot_interface_within_limits(const RAnalFunctionSnapshot *snapshot,
		const RAnalFunctionSnapshotLimits *limits) {
	size_t strings = 0;
	const RAnalFunctionInterfaceSnapshot *interface = &snapshot->function_interface;
	if (interface->num_parameters > limits->max_interface_parameters
		|| !snapshot_string_budget_add (interface->calling_convention,
			limits->max_interface_string_bytes, &strings)
		|| !snapshot_string_budget_add (interface->return_address_storage.name,
			limits->max_interface_string_bytes, &strings)
		|| !snapshot_string_budget_add (interface->stack_pointer_storage.name,
			limits->max_interface_string_bytes, &strings)
		|| !snapshot_string_budget_add (snapshot->frame_pointer_storage.name,
			limits->max_interface_string_bytes, &strings)) {
		return false;
	}
	size_t i;
	for (i = 0; i < interface->num_parameters; i++) {
		if (!snapshot_string_budget_add (interface->parameters[i].name,
				limits->max_interface_string_bytes, &strings)
			|| !snapshot_string_budget_add (interface->parameters[i].storage.name,
				limits->max_interface_string_bytes, &strings)) {
			return false;
		}
	}
	if (snapshot->num_call_site_interfaces > limits->max_call_sites) {
		return false;
	}
	for (i = 0; i < snapshot->num_call_site_interfaces; i++) {
		const RAnalCallSiteInterfaceSnapshot *call = &snapshot->call_site_interfaces[i];
		if (call->num_arguments > limits->max_call_site_parameters
			|| !snapshot_string_budget_add (call->calling_convention,
				limits->max_interface_string_bytes, &strings)) {
			return false;
		}
	}
	const RAnalSnapshotTypeGraph *graph = &snapshot->type_graph;
	if (graph->num_types > limits->max_type_graph_types
		|| graph->num_aggregates > limits->max_type_graph_aggregates) {
		return false;
	}
	size_t members = 0;
	for (i = 0; i < graph->num_aggregates; i++) {
		const RAnalSnapshotAggregateLayout *aggregate = &graph->aggregates[i];
		if (r_add_overflow_size_t (members, aggregate->num_members, &members)
			|| members > limits->max_type_graph_members
			|| !snapshot_string_budget_add (aggregate->name,
				limits->max_interface_string_bytes, &strings)) {
			return false;
		}
		size_t member_index;
		for (member_index = 0; member_index < aggregate->num_members; member_index++) {
			if (!snapshot_string_budget_add (aggregate->members[member_index].name,
					limits->max_interface_string_bytes, &strings)) {
				return false;
			}
		}
	}
	return true;
}
static bool snapshot_limits_valid(const RAnalFunctionSnapshotLimits *limits) {
	if (!limits || limits->struct_size != sizeof (*limits)) {
		return false;
	}
	const size_t values[] = {
		limits->max_base_types,
		limits->max_base_type_children,
		limits->max_base_type_string_bytes,
		limits->max_function_blocks,
		limits->max_block_source_bytes,
		limits->max_function_source_bytes,
		limits->max_function_successors,
		limits->max_context_items,
		limits->max_context_string_bytes,
		limits->max_interface_parameters,
		limits->max_call_sites,
		limits->max_call_site_parameters,
		limits->max_total_call_site_parameters,
		limits->max_interface_string_bytes,
		limits->max_type_graph_types,
		limits->max_type_graph_aggregates,
		limits->max_type_graph_members,
		limits->max_total_owned_bytes,
	};
	size_t i;
	for (i = 0; i < R_ARRAY_SIZE (values); i++) {
		if (!values[i] || values[i] == SIZE_MAX) {
			return false;
		}
	}
	if (limits->max_block_source_bytes > limits->max_function_source_bytes) {
		return false;
	}
	size_t total = sizeof (RAnalFunctionSnapshot);
#define SNAPSHOT_LIMIT_ADD(value) \
	do { \
		if (r_add_overflow_size_t (total, (value), &total)) { \
			return false; \
		} \
	} while (0)
#define SNAPSHOT_LIMIT_MUL_ADD(count, size) \
	do { \
		size_t bytes; \
		if (r_mul_overflow_size_t ((count), (size), &bytes)) { \
			return false; \
		} \
		SNAPSHOT_LIMIT_ADD (bytes); \
	} while (0)
	SNAPSHOT_LIMIT_ADD (limits->max_function_source_bytes);
	SNAPSHOT_LIMIT_ADD (limits->max_base_type_string_bytes);
	SNAPSHOT_LIMIT_ADD (limits->max_context_string_bytes);
	SNAPSHOT_LIMIT_ADD (limits->max_interface_string_bytes);
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_function_blocks, sizeof (RAnalSnapshotBlock));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_function_successors,
		sizeof (RAnalSnapshotSuccessor) + sizeof (ut64));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_base_types, sizeof (RAnalBaseType));
	const size_t base_type_child_size = R_MAX (sizeof (RAnalStructMember),
		R_MAX (sizeof (RAnalUnionMember), sizeof (RAnalEnumCase)));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_base_type_children, base_type_child_size);
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_context_items, sizeof (RAnalFcnSlot));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_interface_parameters,
		sizeof (RAnalSnapshotParameter));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_call_sites,
		sizeof (RAnalCallSiteInterfaceSnapshot));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_total_call_site_parameters,
		sizeof (RAnalSnapshotParameter));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_type_graph_types,
		sizeof (RAnalSnapshotType));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_type_graph_aggregates,
		sizeof (RAnalSnapshotAggregateLayout));
	SNAPSHOT_LIMIT_MUL_ADD (limits->max_type_graph_members,
		sizeof (RAnalSnapshotAggregateMember));
#undef SNAPSHOT_LIMIT_MUL_ADD
#undef SNAPSHOT_LIMIT_ADD
	return total <= limits->max_total_owned_bytes;
}
static const RArchConfig *function_snapshot_active_arch_config(const RAnal *anal) {
	if (anal && anal->arch && anal->arch->session && anal->arch->session->config) {
		return anal->arch->session->config;
	}
	return anal? anal->config: NULL;
}
static bool function_snapshot_machine_tuple_collect(RAnalFunctionSnapshot *snapshot, const RAnal *anal) {
	const RArchConfig *config = function_snapshot_active_arch_config (anal);
	if (!config) {
		return false;
	}
	snapshot->arch_id = strdup (r_str_get (config->arch));
	snapshot->cpu_id = strdup (r_str_get (config->cpu));
	snapshot->bits = config->bits;
	snapshot->endian = config->endian;
	return snapshot->arch_id && snapshot->cpu_id;
}
static bool function_snapshot_machine_tuple_is_current(const RAnalFunctionSnapshot *snapshot, const RAnal *anal) {
	const RArchConfig *config = function_snapshot_active_arch_config (anal);
	return config && snapshot->bits == config->bits && snapshot->endian == config->endian
		&& !strcmp (snapshot->arch_id, r_str_get (config->arch))
		&& !strcmp (snapshot->cpu_id, r_str_get (config->cpu));
}
static RAnalFunctionSnapshot *function_snapshot_collect_with_limits_unlocked(RAnal *anal, RAnalFunction *fcn, const RAnalFunctionSnapshotLimits *limits, const char **reason) {
	RAnalFcnVarsCache cache = {0};
	RAnalFunctionSnapshot *snapshot = NULL;
	const char *refusal = "unspecified refusal";

	R_RETURN_VAL_IF_FAIL (anal && fcn && limits, NULL);
	if (!snapshot_limits_valid (limits)) {
		SNAPSHOT_REFUSE ("snapshot limits are not internally consistent");
	}
	ut64 function_dirty_epoch = r_anal_function_dirty_epoch (fcn);
	ut64 type_dirty_epoch = r_anal_types_dirty_epoch (anal);
	snapshot = R_NEW0 (RAnalFunctionSnapshot);
	if (!snapshot) {
		SNAPSHOT_REFUSE ("out of memory allocating the snapshot");
	}
	if (!function_image_snapshot_collect (
			anal, fcn, limits, &snapshot->image, &refusal)) {
		goto fail;
	}
	RList *base_types = snapshot_type_resolver_capture (anal, limits);
	if (!base_types || type_dirty_epoch != r_anal_types_dirty_epoch (anal)) {
		r_anal_types_snapshot_free (base_types);
		SNAPSHOT_REFUSE ("the type database is unreadable or changed during capture");
	}

	snapshot->base_types = base_types;
	RAnalFcnContext *ctx = &snapshot->context;
	ctx->signature = fcn_context_collect_signature (fcn);
	snapshot->return_arity = snapshot_signature_return_arity (ctx->signature);
	if (snapshot->return_arity == R_ANAL_SNAPSHOT_RETURN_ARITY_UNKNOWN
		&& anal->binb.bin && anal->binb.get_sym) {
		const RBinAddr *init = anal->binb.get_sym (anal->binb.bin, R_BIN_SYM_INIT);
		if (init && init->vaddr == fcn->addr) {
			// The loader invokes the initialization hook for its effects and
			// discards the machine return carrier. This establishes logical
			// void arity without inventing a source prototype or parameter list.
			snapshot->return_arity = R_ANAL_SNAPSHOT_RETURN_ARITY_VOID;
		}
	}
	ctx->fcn_slots = r_list_newf ((RListFree)fcn_context_slot_free);
	ctx->callees = fcn_context_collect_callees (anal, &snapshot->image);
	snapshot->schema_version = R_ANAL_FUNCTION_SNAPSHOT_SCHEMA_VERSION;
	snapshot->struct_size = sizeof (RAnalFunctionSnapshot);
	snapshot->function_addr = snapshot->image.entry_addr;
	const RAnalSnapshotBlock *first_block = &snapshot->image.blocks[0];
	const RAnalSnapshotBlock *last_block =
		&snapshot->image.blocks[snapshot->image.num_blocks - 1];
	snapshot->function_size = last_block->addr + last_block->size - first_block->addr;
	snapshot->maxstack = fcn->maxstack;
	snapshot->function_name = strdup (r_str_get (fcn->name));
	if (!function_snapshot_machine_tuple_collect (snapshot, anal)) {
		SNAPSHOT_REFUSE ("the active architecture tuple is unavailable");
	}
	ctx->function_dirty_epoch = function_dirty_epoch;
	ctx->type_dirty_epoch = type_dirty_epoch;
	snapshot->type_context_hash = r_anal_types_context_hash_from_snapshot (
		anal, snapshot->base_types, type_dirty_epoch);
	if (!ctx->fcn_slots || !ctx->callees || !snapshot->function_name
		|| !snapshot->base_types) {
		SNAPSHOT_REFUSE ("out of memory collecting the function context");
	}

	r_anal_function_vars_cache_init_readonly (anal, &cache, fcn);
	RAnalVar **it;
	R_VEC_FOREACH (cache.bvars, it) {
		RAnalVar *var = *it;
		if (!var) {
			continue;
		}
		RAnalVar *home_source = fcn_context_find_register_home_source (cache.rvars, var);
		int exact_formal_ordinal = -1;
		const int arg_index = home_source
			? fcn_context_register_arg_index (anal, fcn, cache.rvars, home_source)
			: r_anal_var_exact_formal_get (anal, var, &exact_formal_ordinal)
				? exact_formal_ordinal: -1;
		RAnalFcnSlot *slot = fcn_context_collect_slot (
			anal, ctx, fcn, var, home_source, arg_index);
		if (!slot || !r_list_append (ctx->fcn_slots, slot)) {
			fcn_context_slot_free (slot);
			SNAPSHOT_REFUSE ("out of memory collecting function variables");
		}
	}
	R_VEC_FOREACH (cache.svars, it) {
		RAnalVar *var = *it;
		if (!var) {
			continue;
		}
		RAnalVar *home_source = fcn_context_find_register_home_source (cache.rvars, var);
		int exact_formal_ordinal = -1;
		const int arg_index = home_source
			? fcn_context_register_arg_index (anal, fcn, cache.rvars, home_source)
			: r_anal_var_exact_formal_get (anal, var, &exact_formal_ordinal)
				? exact_formal_ordinal: -1;
		RAnalFcnSlot *slot = fcn_context_collect_slot (
			anal, ctx, fcn, var, home_source, arg_index);
		if (!slot || !r_list_append (ctx->fcn_slots, slot)) {
			fcn_context_slot_free (slot);
			SNAPSHOT_REFUSE ("out of memory collecting function variables");
		}
	}
	r_anal_function_vars_cache_fini (&cache);
	if (!snapshot_context_within_limits (snapshot, limits)) {
		SNAPSHOT_REFUSE ("the function context exceeds its limits");
	}
	if (!function_interface_snapshot_collect (
			anal, fcn, ctx, &snapshot->function_interface, limits)) {
		SNAPSHOT_REFUSE ("the function interface could not be collected");
	}
	if (!snapshot_frame_pointer_storage_collect (anal, fcn, ctx,
			&snapshot->function_interface, &snapshot->frame_pointer_storage)) {
		SNAPSHOT_REFUSE ("the frame pointer storage could not be resolved");
	}
	snapshot_return_mechanism_collect (anal, fcn,
		ctx, &snapshot->function_interface, &snapshot->return_mechanism);
	snapshot_stack_allocation_contract_collect (anal,
		&snapshot->function_interface, &snapshot->stack_allocation_contract);
	SnapshotTypeGraphResult graph_result = function_type_graph_snapshot_collect (
		anal, ctx, snapshot, limits);
	if (graph_result == SNAPSHOT_TYPE_GRAPH_NO_MEMORY) {
		SNAPSHOT_REFUSE ("out of memory building the type graph");
	}
	if (!call_site_interfaces_snapshot_collect (anal, ctx, snapshot, limits)) {
		SNAPSHOT_REFUSE ("the call site interfaces could not be collected");
	}
	if (!snapshot_interface_within_limits (snapshot, limits)) {
		SNAPSHOT_REFUSE ("the function interface exceeds its limits");
	}
	RAnalFunctionImageSnapshot current_image = {0};
	const bool image_current = function_image_snapshot_collect (
		anal, fcn, limits, &current_image, NULL)
		&& function_image_snapshot_equal (&snapshot->image, &current_image);
	function_image_snapshot_fini (&current_image);
	RList *current_base_types = snapshot_type_resolver_capture (anal, limits);
	const bool base_types_current = snapshot_base_types_equal (
		snapshot->base_types, current_base_types);
	r_list_free (current_base_types);
	RAnalSnapshotReturnMechanismView current_return_mechanism = {0};
	snapshot_return_mechanism_collect (anal, fcn,
		ctx, &snapshot->function_interface, &current_return_mechanism);
	RAnalSnapshotStackAllocationContractView current_stack_allocation_contract = {0};
	snapshot_stack_allocation_contract_collect (anal,
		&snapshot->function_interface, &current_stack_allocation_contract);
	RAnalSnapshotRegisterStorage current_frame_pointer_storage = {0};
	const bool frame_pointer_current = snapshot_frame_pointer_storage_collect (
		anal, fcn, ctx, &snapshot->function_interface,
		&current_frame_pointer_storage)
		&& snapshot_frame_pointer_storage_equal (
			&snapshot->frame_pointer_storage, &current_frame_pointer_storage);
	snapshot_register_storage_fini (&current_frame_pointer_storage);
	if (function_dirty_epoch != r_anal_function_dirty_epoch (fcn)
		|| type_dirty_epoch != r_anal_types_dirty_epoch (anal)
		|| !function_snapshot_machine_tuple_is_current (snapshot, anal)
		|| !image_current || !base_types_current
		|| !snapshot_return_mechanism_equal (
			&snapshot->return_mechanism, &current_return_mechanism)
		|| !snapshot_stack_allocation_contract_equal (
			&snapshot->stack_allocation_contract,
			&current_stack_allocation_contract)
		|| !frame_pointer_current) {
		SNAPSHOT_REFUSE ("the function or type state changed during capture");
	}
	snapshot->capabilities = R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_SLOTS
		| R_ANAL_FUNCTION_SNAPSHOT_CAP_CALLEES
		| R_ANAL_FUNCTION_SNAPSHOT_CAP_TYPES
		| R_ANAL_FUNCTION_SNAPSHOT_CAP_REVISION
		| R_ANAL_FUNCTION_SNAPSHOT_CAP_OWNED_BOUNDED_FUNCTION_IMAGE;
	if (ctx->signature) {
		snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_SIGNATURE;
	}
	if (snapshot->function_interface.complete) {
		snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE;
	}
	if (snapshot->function_interface.return_address_storage.name
		&& snapshot->function_interface.return_address_storage.size) {
		snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE;
	}
	if (snapshot->function_interface.stack_pointer_storage.name
		&& snapshot->function_interface.stack_pointer_storage.size) {
		snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE;
	}
	if (snapshot->return_mechanism.kind != R_ANAL_SNAPSHOT_RETURN_MECHANISM_NONE
		&& (snapshot->capabilities & (
			R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE
			| R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE
			| R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE)) == (
			R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE
			| R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE
			| R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE)) {
		snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM;
	}
	if (snapshot->frame_pointer_storage.name
		&& snapshot->frame_pointer_storage.size
		&& (snapshot->capabilities & (
			R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE
			| R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE
			| R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE)) == (
			R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE
			| R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE
			| R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE)) {
		snapshot->capabilities |=
			R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE;
	}
	if (snapshot->stack_allocation_contract.growth
			!= R_ANAL_SNAPSHOT_STACK_GROWTH_NONE
		&& (snapshot->capabilities
			& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE)) {
		snapshot->capabilities |=
			R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT;
	}
	if (snapshot->function_interface.stack_slot_roles_complete) {
		snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES;
	}
	if (snapshot->type_graph.complete
		&& snapshot->function_interface.logical_types_complete) {
		snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES;
	}
	if (snapshot->num_call_site_interfaces) {
		snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_CALL_SITE_INTERFACES;
	}
	snapshot->revision_identity = function_snapshot_hash (snapshot);
	// The same hash, before any callee is attached and before a caller may
	// overwrite the revision with its own. For the function asked for the two
	// are equal; for a callee only this one survives.
	snapshot->content_identity = snapshot->revision_identity;
	return snapshot;

fail:
	r_anal_function_vars_cache_fini (&cache);
	r_anal_function_snapshot_free (snapshot);
	if (reason) {
		*reason = refusal;
	}
	return NULL;
}
static void r_anal_function_snapshot_limits_default(RAnalFunctionSnapshotLimits *limits) {
	R_RETURN_IF_FAIL (limits);
	*limits = (RAnalFunctionSnapshotLimits) {
		.struct_size = sizeof (*limits),
		.max_base_types = 4096,
		.max_base_type_children = 65536,
		.max_base_type_string_bytes = 16 * 1024 * 1024,
		.max_function_blocks = 65536,
		.max_block_source_bytes = 16 * 1024 * 1024,
		.max_function_source_bytes = 256 * 1024 * 1024,
		.max_function_successors = 262144,
		.max_context_items = 65536,
		.max_context_string_bytes = 16 * 1024 * 1024,
		.max_interface_parameters = 4096,
		.max_call_sites = 65536,
		.max_call_site_parameters = 4096,
		.max_total_call_site_parameters = 65536,
		.max_interface_string_bytes = 16 * 1024 * 1024,
		.max_type_graph_types = 131072,
		.max_type_graph_aggregates = 4096,
		.max_type_graph_members = 65536,
		.max_total_owned_bytes = 512 * 1024 * 1024,
	};
}
static void function_snapshot_collect_callees_unlocked(RAnal *anal, RAnalFunctionSnapshot *snapshot, const RAnalFunctionSnapshotLimits *limits) {
	if (!snapshot->context.callees) {
		return;
	}
	RAnalFunctionSnapshot **collected = R_NEWS0 (RAnalFunctionSnapshot *, SNAPSHOT_MAX_CALLEE_SNAPSHOTS);
	if (!collected) {
		return;
	}
	size_t count = 0;
	RListIter *iter;
	RAnalFcnCallee *callee;
	r_list_foreach (snapshot->context.callees, iter, callee) {
		if (count >= SNAPSHOT_MAX_CALLEE_SNAPSHOTS) {
			break;
		}
		// A callee that is the caller is the same body, and one already taken
		// is the same body too: a set with a repeat describes nothing extra and
		// costs a consumer a disjointness check it cannot satisfy.
		if (!callee || callee->addr == UT64_MAX || callee->addr == snapshot->function_addr) {
			continue;
		}
		size_t seen;
		bool duplicate = false;
		for (seen = 0; seen < count && !duplicate; seen++) {
			duplicate = collected[seen]->function_addr == callee->addr;
		}
		if (duplicate) {
			continue;
		}
		RAnalFunction *callee_fcn = r_anal_get_function_at (anal, callee->addr);
		if (!callee_fcn) {
			continue;
		}
		RAnalFunctionSnapshot *callee_snapshot = function_snapshot_collect_with_limits_unlocked (
			anal, callee_fcn, limits, NULL);
		if (!callee_snapshot) {
			continue;
		}
		// One level. A callee's own callees are its business, and collecting
		// them would make the cost of a capture depend on the shape of the
		// program rather than on the function asked for.
		size_t nested;
		for (nested = 0; nested < callee_snapshot->num_callee_snapshots; nested++) {
			r_anal_function_snapshot_free (callee_snapshot->callee_snapshots[nested]);
		}
		free (callee_snapshot->callee_snapshots);
		callee_snapshot->callee_snapshots = NULL;
		callee_snapshot->num_callee_snapshots = 0;
		callee_snapshot->capabilities &= ~R_ANAL_FUNCTION_SNAPSHOT_CAP_CALLEE_SNAPSHOTS;
		// The identity a set carries is the identity of the capture, not of one
		// function in it. A consumer reasoning across a call has to be able to
		// tell that these bodies were read together, and a per-function hash
		// says the opposite about every member.
		// Only the revision. `content_identity` stays the callee's own hash,
		// computed by its own collect above, so a consumer can tell both that
		// these bodies were read together and which body this is.
		callee_snapshot->revision_identity = snapshot->revision_identity;
		collected[count++] = callee_snapshot;
	}
	if (!count) {
		free (collected);
		return;
	}
	snapshot->callee_snapshots = collected;
	snapshot->num_callee_snapshots = count;
	snapshot->capabilities |= R_ANAL_FUNCTION_SNAPSHOT_CAP_CALLEE_SNAPSHOTS;
}
static RAnalFunctionSnapshot *r_anal_function_snapshot_collect_with_limits(RAnal *anal, RAnalFunction *fcn, const RAnalFunctionSnapshotLimits *limits, const char **reason) {
	R_RETURN_VAL_IF_FAIL (anal && anal->lock, NULL);
	r_th_lock_enter (anal->lock);
	RAnalFunctionSnapshot *snapshot = function_snapshot_collect_with_limits_unlocked (
		anal, fcn, limits, reason);
	if (snapshot) {
		function_snapshot_collect_callees_unlocked (anal, snapshot, limits);
	}
	r_th_lock_leave (anal->lock);
	return snapshot;
}
static RAnalFunctionSnapshot *r_anal_function_snapshot_collect_bounded(RAnal *anal, RAnalFunction *fcn, const char **reason) {
	RAnalFunctionSnapshotLimits limits;
	r_anal_function_snapshot_limits_default (&limits);
	return r_anal_function_snapshot_collect_with_limits (anal, fcn, &limits, reason);
}

/* ---- moved from libr/anal/type.c ---- */
static RList *r_anal_types_snapshot_with_limits(RAnal *anal, const RAnalFunctionSnapshotLimits *limits) {
	R_RETURN_VAL_IF_FAIL (anal && limits, NULL);
	return types_baselist_with_limits (anal, limits);
}
static ut64 r_anal_types_context_hash_from_snapshot(RAnal *anal, const RList *types, ut64 type_dirty_epoch) {
	R_RETURN_VAL_IF_FAIL (anal && types, 0);
	return types_context_hash_from_snapshot (anal, types, type_dirty_epoch);
}


static void function_context_fini(RAnalFcnContext *ctx) {
	r_anal_function_signature_free (ctx->signature);
	r_list_free (ctx->fcn_slots);
	r_list_free (ctx->callees);
}

static ut64 function_context_hash_mix(ut64 hash, ut64 value) {
	hash ^= value + 0x9e3779b97f4a7c15ULL + (hash << 6) + (hash >> 2);
	return hash;
}

static ut64 function_context_hash_string(ut64 hash, const char *value) {
	return function_context_hash_mix (hash, R_STR_ISNOTEMPTY (value)? r_str_hash64 (value): 0);
}

static void function_logical_types_clear(RAnalFunctionInterfaceSnapshot *interface) {
	size_t i;
	for (i = 0; i < interface->num_parameters; i++) {
		interface->parameters[i].logical_type_id = R_ANAL_SNAPSHOT_TYPE_ID_INVALID;
		memset (&interface->parameters[i].carrier, 0,
			sizeof (interface->parameters[i].carrier));
	}
	interface->return_type_id = R_ANAL_SNAPSHOT_TYPE_ID_INVALID;
	memset (&interface->return_carrier, 0, sizeof (interface->return_carrier));
	interface->logical_types_complete = false;
}

static RList *types_baselist_with_limits(RAnal *anal, const RAnalFunctionSnapshotLimits *limits) {
	R_RETURN_VAL_IF_FAIL (anal, NULL);
	RAnalTypeSnapshotBudget expected = {0};
	if (limits && !types_snapshot_preflight (anal, limits, &expected)) {
		return NULL;
	}
	RList *types = r_list_newf ((RListFree)r_anal_base_type_free);
	if (!types) {
		return NULL;
	}
	TypeSnapshotCloneContext ctx = {
		.anal = anal,
		.types = types,
		.seen = sdb_new0 (),
		.fail_closed = limits != NULL,
		.valid = true,
	};
	if (!ctx.seen) {
		if (limits) {
			r_list_free (types);
			return NULL;
		}
		return types;
	}
	const bool completed = sdb_foreach (anal->sdb_types, types_snapshot_clone_cb, &ctx);
	sdb_free (ctx.seen);
	r_list_sort (types, base_type_name_cmp);
	if (limits && (!completed || !ctx.valid
			|| (size_t)r_list_length (types) != expected.base_types)) {
		r_list_free (types);
		return NULL;
	}
	return types;
}

static ut64 types_context_hash_from_snapshot(RAnal *anal, const RList *types, ut64 type_dirty_epoch) {
	if (type_dirty_epoch == r_anal_types_dirty_epoch (anal)
		&& anal->type_context_hash_cache
		&& anal->type_context_hash_epoch == type_dirty_epoch) {
		return anal->type_context_hash_cache;
	}
	ut64 hash = 0xcbf29ce484222325ULL;
	hash = type_context_hash_mix (hash, type_dirty_epoch);
	RListIter *iter;
	RAnalBaseType *type;
	r_list_foreach (types, iter, type) {
		if (!type) {
			continue;
		}
		hash = type_context_hash_string (hash, type->name);
		hash = type_context_hash_string (hash, type->type);
		hash = type_context_hash_mix (hash, (ut64)type->size);
		hash = type_context_hash_mix (hash, (ut64)type->kind);
		switch (type->kind) {
		case R_ANAL_BASE_TYPE_KIND_STRUCT: {
			RAnalStructMember *member;
			R_VEC_FOREACH (&type->struct_data.members, member) {
				hash = type_context_hash_string (hash, member->name);
				hash = type_context_hash_string (hash, member->type);
				hash = type_context_hash_mix (hash, (ut64)member->offset);
				hash = type_context_hash_mix (hash, (ut64)member->bitsize);
				hash = type_context_hash_mix (hash, (ut64)member->count);
			}
			break;
		}
		case R_ANAL_BASE_TYPE_KIND_UNION: {
			RAnalUnionMember *member;
			R_VEC_FOREACH (&type->union_data.members, member) {
				hash = type_context_hash_string (hash, member->name);
				hash = type_context_hash_string (hash, member->type);
				hash = type_context_hash_mix (hash, (ut64)member->offset);
				hash = type_context_hash_mix (hash, (ut64)member->bitsize);
				hash = type_context_hash_mix (hash, (ut64)member->count);
			}
			break;
		}
		case R_ANAL_BASE_TYPE_KIND_ENUM: {
			RAnalEnumCase *cas;
			R_VEC_FOREACH (&type->enum_data.cases, cas) {
				hash = type_context_hash_string (hash, cas->name);
				hash = type_context_hash_mix (hash, (ut64)(st64)cas->val);
			}
			break;
		}
		default:
			break;
		}
	}
	TypeContextLinkHash links = {0};
	(void)sdb_foreach (anal->sdb_types, type_context_hash_link_cb, &links);
	if (links.count) {
		hash = type_context_hash_mix (hash, links.xor_hash);
		hash = type_context_hash_mix (hash, links.sum_hash);
		hash = type_context_hash_mix (hash, links.count);
	}
	if (!hash) {
		hash = 1;
	}
	if (type_dirty_epoch == r_anal_types_dirty_epoch (anal)) {
		anal->type_context_hash_cache = hash;
		anal->type_context_hash_epoch = type_dirty_epoch;
	}
	return hash;
}

static bool r_anal_cc_preserves_reg(RAnal *anal, const char *convention, const char *reg) {
	R_RETURN_VAL_IF_FAIL (anal, false);
	if (R_STR_ISEMPTY (convention) || R_STR_ISEMPTY (reg)) {
		return false;
	}
	const char *preserves = cc_regset (anal, convention, "preserve");
	if (R_STR_ISEMPTY (preserves)) {
		return false;
	}
	if (r_anal_cc_regset_contains (preserves, reg)) {
		return true;
	}
	// Register profiles and convention tables do not agree on case: an arch
	// plugin may name the carrier RSP where the convention lists rsp.
	char *folded = strdup (reg);
	if (!folded) {
		return false;
	}
	r_str_case (folded, false);
	const bool preserved = r_anal_cc_regset_contains (preserves, folded);
	free (folded);
	return preserved;
}

static bool r_anal_cc_return_mechanism(RAnal *anal, const char *convention, RAnalCCReturnMechanism *mechanism) {
	R_RETURN_VAL_IF_FAIL (anal && convention && mechanism, false);
	*mechanism = (RAnalCCReturnMechanism) {0};
	if (!r_anal_cc_exist (anal, convention)) {
		return false;
	}
	const char *record = sdb_const_getf (DB, NULL, "cc.%s.retmech", convention);
	return cc_parse_return_mechanism (record, mechanism);
}

static bool r_anal_cc_stack_allocation_contract(RAnal *anal, const char *convention, RAnalCCStackAllocationContract *contract) {
	R_RETURN_VAL_IF_FAIL (anal && convention && contract, false);
	*contract = (RAnalCCStackAllocationContract) {0};
	if (!r_anal_cc_exist (anal, convention)) {
		return false;
	}
	const char *record = sdb_const_getf (DB, NULL, "cc.%s.stackalloc", convention);
	const char *red_zone_record = sdb_const_getf (DB, NULL, "cc.%s.redzone", convention);
	return cc_parse_stack_allocation_contract (record, red_zone_record, contract);
}

static RAnalFunctionSignature *r_anal_function_signature_from_type_name(RAnal *anal, const char *name) {
	R_RETURN_VAL_IF_FAIL (anal && anal->sdb_types && name, NULL);
	char *type_name = function_signature_try_type_name (anal->sdb_types, name);
	if (!type_name) {
		return NULL;
	}
	return function_signature_build (anal, NULL, type_name, false);
}

static void r_anal_function_vars_cache_init_readonly(RAnal *anal, RAnalFcnVarsCache *cache, RAnalFunction *fcn) {
	cache->bvars = r_anal_var_vec (anal, fcn, R_ANAL_VAR_KIND_BPV);
	cache->rvars = r_anal_var_vec (anal, fcn, R_ANAL_VAR_KIND_REG);
	cache->svars = r_anal_var_vec (anal, fcn, R_ANAL_VAR_KIND_SPV);
	RVecAnalVarPtr_sort (cache->bvars, var_ptr_comparator);
	RVecAnalVarPtr_sort (cache->svars, var_ptr_comparator);
}

static int base_type_name_cmp(const void *a, const void *b) {
	const RAnalBaseType *ta = (const RAnalBaseType *)a;
	const RAnalBaseType *tb = (const RAnalBaseType *)b;
	return strcmp (ta && ta->name? ta->name: "", tb && tb->name? tb->name: "");
}

static bool type_context_hash_link_cb(void *user, const char *key, const char *value) {
	TypeContextLinkHash *links = user;
	if (type_context_hash_should_include_sdb_key (key)) {
		ut64 item = type_context_hash_string (0xcbf29ce484222325ULL, key);
		item = type_context_hash_string (item, value);
		links->xor_hash ^= item;
		links->sum_hash += item;
		links->count++;
	}
	return true;
}

static ut64 type_context_hash_mix(ut64 hash, ut64 value) {
	hash ^= value + 0x9e3779b97f4a7c15ULL + (hash << 6) + (hash >> 2);
	return hash;
}

static ut64 type_context_hash_string(ut64 hash, const char *value) {
	return type_context_hash_mix (hash, R_STR_ISNOTEMPTY (value)? r_str_hash64 (value): 0);
}

static bool types_snapshot_clone_cb(void *user, const char *name, const char *kind) {
	TypeSnapshotCloneContext *ctx = user;
	if (R_STR_ISEMPTY (name) || R_STR_ISEMPTY (kind)) {
		return true;
	}
	BaseTypeAppendResult result = BASE_TYPE_APPEND_SKIPPED;
	const char *namespace_kind = NULL;
	const char *namespace_name = NULL;
	if (split_base_type_namespace_key (name, &namespace_kind, &namespace_name)) {
		if (!sdb_const_getf (ctx->anal->sdb_types, NULL, "%s.%s",
				namespace_kind, namespace_name)) {
			return true;
		}
		result = append_base_type_if_unseen (
			ctx->anal, ctx->types, ctx->seen, namespace_kind, namespace_name);
	} else if (!strchr (name, '.') && type_snapshot_kind_supported (kind)) {
		if (!sdb_const_getf (ctx->anal->sdb_types, NULL, "%s.%s", kind, name)) {
			return true;
		}
		result = append_base_type_if_unseen (
			ctx->anal, ctx->types, ctx->seen, kind, name);
	}
	if (result == BASE_TYPE_APPEND_ERROR && ctx->fail_closed) {
		ctx->valid = false;
		return false;
	}
	return true;
}

static bool types_snapshot_preflight(RAnal *anal, const RAnalFunctionSnapshotLimits *limits, RAnalTypeSnapshotBudget *result) {
	TypeSnapshotPreflightContext ctx = {
		.anal = anal,
		.seen = sdb_new0 (),
		.limits = limits,
	};
	if (!ctx.seen) {
		return false;
	}
	const bool valid = sdb_foreach (anal->sdb_types, types_snapshot_preflight_cb, &ctx);
	sdb_free (ctx.seen);
	if (valid) {
		*result = ctx.budget;
	}
	return valid;
}

static bool cc_parse_return_mechanism(const char *record, RAnalCCReturnMechanism *mechanism) {
	const char prefix[] = "stack:";
	if (!record || !r_str_startswith (record, prefix)) {
		return false;
	}
	const char *p = record + sizeof (prefix) - 1;
	const char *end = record + strlen (record);
	st64 entry_sp_offset;
	ut64 slot_size;
	st64 exit_sp_delta;
	if (!cc_parse_s64_field (&p, end, ':', &entry_sp_offset)
		|| !cc_parse_u64_field (&p, end, UT32_MAX, ':', &slot_size)
		|| !cc_parse_s64_field (&p, end, 0, &exit_sp_delta)
		|| !slot_size || exit_sp_delta < (st64)slot_size
		|| entry_sp_offset > ST64_MAX - (st64)slot_size) {
		return false;
	}
	*mechanism = (RAnalCCReturnMechanism) {
		.kind = R_ANAL_CC_RETURN_MECHANISM_STACK,
		.entry_sp_offset = entry_sp_offset,
		.slot_size = (ut32)slot_size,
		.exit_sp_delta = exit_sp_delta,
	};
	return true;
}

static bool cc_parse_stack_allocation_contract(const char *record, const char *red_zone_record, RAnalCCStackAllocationContract *contract) {
	if (!record || !contract) {
		return false;
	}
	RAnalCCStackGrowth growth;
	if (!strcmp (record, "lower")) {
		growth = R_ANAL_CC_STACK_GROWTH_LOWER;
	} else if (!strcmp (record, "higher")) {
		growth = R_ANAL_CC_STACK_GROWTH_HIGHER;
	} else {
		return false;
	}
	ut64 red_zone_bytes = 0;
	if (red_zone_record) {
		const char *p = red_zone_record;
		const char *end = red_zone_record + strlen (red_zone_record);
		if (!cc_parse_u64_field (&p, end, UT32_MAX, 0, &red_zone_bytes)) {
			return false;
		}
	}
	*contract = (RAnalCCStackAllocationContract) {
		.growth = growth,
		.red_zone_bytes = (ut32)red_zone_bytes,
	};
	return true;
}

static const char *cc_regset(RAnal *anal, const char *convention, const char *field) {
	RAnalDynCC d;
	if (dyncc_parse (convention, &d)) {
		const RAnalDynCCSlice *slice = !strcmp (field, "clobber")? &d.clobbers: &d.preserves;
		return dyncc_intern (anal, slice->p, slice->len);
	}
	const char *ret = sdb_const_getf (DB, NULL, "cc.%s.%s", convention, field);
	return ret? r_str_constpool_get (&anal->constpool, ret): NULL;
}

static bool r_anal_cc_regset_contains(const char *regset, const char *reg) {
	R_RETURN_VAL_IF_FAIL (regset && reg, false);
	const char *s = regset;
	if (*s == '(') {
		s++;
	}
	while (*s) {
		while (*s == ',' || isspace ((ut8)*s)) {
			s++;
		}
		const char *e = s;
		while (*e && *e != ',' && *e != ')') {
			e++;
		}
		const char *t = e;
		while (t > s && isspace ((ut8)t[-1])) {
			t--;
		}
		if (t > s && strlen (reg) == (size_t)(t - s) && !strncmp (s, reg, t - s)) {
			return true;
		}
		if (*e == ')') {
			break;
		}
		s = e;
	}
	return false;
}

static RAnalFunctionSignature *function_signature_build(RAnal *anal, RAnalFunction *function, char *type_name, bool load_types) {
	int i;
	RAnalFunctionSignature *signature = NULL;

	signature = R_NEW0 (RAnalFunctionSignature);
	signature->params = r_list_newf ((RListFree)function_param_free);
	const char *type_kind = sdb_const_get (anal->sdb_types, type_name, 0);
	const char *ret_type = r_type_func_ret (anal->sdb_types, type_name);
	if (ret_type) {
		signature->ret_type = strdup (ret_type);
		if (!signature->ret_type) {
			goto beach;
		}
	}
	int argc = r_type_func_args_count (anal->sdb_types, type_name);
	for (i = 0; i < argc; i++) {
		const char *param_name = r_type_func_args_name (anal->sdb_types, type_name, i);
		RAnalFunctionParam *param = R_NEW0 (RAnalFunctionParam);
		param->name = param_name? strdup (param_name): NULL;
		param->type = r_type_func_args_type (anal->sdb_types, type_name, i);
		r_list_append (signature->params, param);
		if (!param->type) {
			break;
		}
	}
	if ((!type_kind || strcmp (type_kind, "func")) && r_list_empty (signature->params)
		&& (!function || !function_signature_fallback_to_vars (anal, function, signature))) {
		goto beach;
	}
	// the declaration carries the function's own name; the key is only a lookup handle
	signature->signature = function_signature_string (
		function && R_STR_ISNOTEMPTY (function->name)? function->name: type_name,
		signature->ret_type, signature->params, true, true);
	if (!signature->signature) {
		goto beach;
	}
	const char *callconv = function_signature_callconv (
		anal, function, type_name, load_types);
	if (callconv) {
		signature->callconv = strdup (callconv);
		if (!signature->callconv) {
			goto beach;
		}
	}
	signature->noreturn = function_signature_is_noreturn (anal->sdb_types, type_name,
		function? function->is_noreturn: false);
	free (type_name);
	return signature;

beach:
	free (type_name);
	r_anal_function_signature_free (signature);
	return NULL;
}

static char *function_signature_try_type_name(Sdb *types, const char *candidate) {
	R_RETURN_VAL_IF_FAIL (types && candidate && *candidate, NULL);
	char *name = r_type_func_key (types, candidate);
	if (name) {
		const char *kind = sdb_const_get (types, name, 0);
		if (kind && !strcmp (kind, "func")) {
			return name;
		}
		free (name);
	}
	name = r_type_func_guess (types, candidate);
	if (name) {
		const char *kind = sdb_const_get (types, name, 0);
		if (kind && !strcmp (kind, "func")) {
			return name;
		}
		free (name);
	}
	const char *kind = sdb_const_get (types, candidate, 0);
	if (kind && !strcmp (kind, "func")) {
		return strdup (candidate);
	}
	return NULL;
}

static int var_ptr_comparator(RAnalVar * const *a, RAnalVar * const *b) {
	return var_comparator (a? *a: NULL, b? *b: NULL);
}

static BaseTypeAppendResult append_base_type_if_unseen(RAnal *anal, RList *types, Sdb *seen, const char *kind, const char *sname) {
	R_RETURN_VAL_IF_FAIL (anal && types && seen && R_STR_ISNOTEMPTY (kind) && R_STR_ISNOTEMPTY (sname), BASE_TYPE_APPEND_ERROR);
	char *seen_key = r_str_newf ("%s.%s", kind, sname);
	if (!seen_key) {
		return BASE_TYPE_APPEND_ERROR;
	}
	if (sdb_exists (seen, seen_key)) {
		free (seen_key);
		return BASE_TYPE_APPEND_SKIPPED;
	}
	RAnalBaseType *base_type = get_base_type_for_kind (anal, kind, sname);
	if (!base_type) {
		free (seen_key);
		return BASE_TYPE_APPEND_ERROR;
	}
	base_type->name = strdup (sname);
	if (!base_type->name || !sdb_set (seen, seen_key, "1", 0)
		|| !r_list_append (types, base_type)) {
		sdb_unset (seen, seen_key, 0);
		r_anal_base_type_free (base_type);
		free (seen_key);
		return BASE_TYPE_APPEND_ERROR;
	}
	free (seen_key);
	return BASE_TYPE_APPEND_OK;
}

static bool split_base_type_namespace_key(const char *key, const char **kind, const char **sname) {
	static const char *kinds[] = { "struct", "union", "enum", "typedef", "type", NULL };
	R_RETURN_VAL_IF_FAIL (key && kind && sname, false);
	size_t i;
	for (i = 0; kinds[i]; i++) {
		const char *candidate = kinds[i];
		const size_t len = strlen (candidate);
		if (strncmp (key, candidate, len) || key[len] != '.') {
			continue;
		}
		const char *name = key + len + 1;
		if (R_STR_ISEMPTY (name) || strchr (name, '.')) {
			return false;
		}
		*kind = candidate;
		*sname = name;
		return true;
	}
	return false;
}

static bool type_context_hash_should_include_sdb_key(const char *key) {
	return r_str_startswith (key, "link.")
		|| r_str_startswith (key, "offset.")
		|| r_str_startswith (key, "fcnlink.");
}

static bool type_snapshot_kind_supported(const char *kind) {
	return !strcmp (kind, "struct") || !strcmp (kind, "union")
		|| !strcmp (kind, "enum") || !strcmp (kind, "typedef")
		|| !strcmp (kind, "type");
}

static bool types_snapshot_preflight_cb(void *user, const char *name, const char *kind) {
	TypeSnapshotPreflightContext *ctx = user;
	if (R_STR_ISEMPTY (name) || R_STR_ISEMPTY (kind)) {
		return true;
	}
	const char *namespace_kind = NULL;
	const char *namespace_name = NULL;
	if (split_base_type_namespace_key (name, &namespace_kind, &namespace_name)) {
		return type_snapshot_preflight_one (
			ctx->anal, ctx->seen, &ctx->budget, ctx->limits, namespace_kind, namespace_name);
	}
	if (!strchr (name, '.') && type_snapshot_kind_supported (kind)) {
		return type_snapshot_preflight_one (
			ctx->anal, ctx->seen, &ctx->budget, ctx->limits, kind, name);
	}
	return true;
}

static bool cc_parse_s64_field(const char **sp, const char *end, char separator, st64 *out) {
	const char *s = *sp;
	const bool negative = s < end && *s == '-';
	if (negative) {
		s++;
	}
	const ut64 negative_limit = (ut64)ST64_MAX + 1;
	ut64 magnitude;
	if (!cc_parse_u64_field (&s, end, negative? negative_limit: ST64_MAX,
			separator, &magnitude) || (negative && !magnitude)) {
		return false;
	}
	if (!negative) {
		*out = (st64)magnitude;
	} else if (magnitude == negative_limit) {
		*out = ST64_MIN;
	} else {
		*out = -(st64)magnitude;
	}
	*sp = s;
	return true;
}

static bool cc_parse_u64_field(const char **sp, const char *end, ut64 limit, char separator, ut64 *out) {
	const char *s = *sp;
	if (s >= end || !isdigit ((ut8)*s)) {
		return false;
	}
	ut64 n = 0;
	do {
		const ut64 digit = (ut64)(*s - '0');
		if (n > (limit - digit) / 10) {
			return false;
		}
		n = (n * 10) + digit;
		s++;
	} while (s < end && isdigit ((ut8)*s));
	if (separator) {
		if (s >= end || *s != separator) {
			return false;
		}
		s++;
	} else if (s != end) {
		return false;
	}
	*sp = s;
	*out = n;
	return true;
}

static const char *dyncc_intern(RAnal *anal, const char *p, size_t len) {
	if (!p || !len) {
		return NULL;
	}
	char tmp[R_ANAL_DYNCC_GROUP_SIZE];
	char *heap = NULL;
	if (len < sizeof (tmp)) {
		memcpy (tmp, p, len);
		tmp[len] = 0;
		p = tmp;
	} else {
		heap = r_str_ndup (p, len);
		if (!heap) {
			return NULL;
		}
		p = heap;
	}
	const char *ret = r_str_constpool_get (&anal->constpool, p);
	free (heap);
	return ret;
}

static bool dyncc_parse(const char *cc, RAnalDynCC *out) {
	if (!cc || !r_str_startswith (cc, "dyncc:")) {
		return false;
	}
	const char *args = cc + strlen ("dyncc:");
	const char *end = cc + strlen (cc);
	const char *rets = memchr (args, ':', end - args);
	if (!rets) {
		return false;
	}
	const char *attrs = memchr (rets + 1, '!', end - (rets + 1));
	const char *ret_end = attrs? attrs: end;
	RAnalDynCC d = {0};
	if (!dyncc_parse_homed_list (args, rets, &d, true)) {
		return false;
	}
	if (!dyncc_parse_homed_list (rets + 1, ret_end, &d, false)) {
		return false;
	}
	if (attrs && !dyncc_parse_attrs (attrs, end, &d)) {
		return false;
	}
	*out = d;
	return true;
}

static void function_param_free(RAnalFunctionParam *param) {
	if (!param) {
		return;
	}
	free (param->name);
	free (param->type);
	free (param);
}

static const char *function_signature_callconv(RAnal *anal, RAnalFunction *fcn, const char *type_name, bool resolve_dynamic) {
	const char *callconv = NULL;

	R_RETURN_VAL_IF_FAIL (anal, NULL);
	if (R_STR_ISNOTEMPTY (type_name)) {
		callconv = sdb_const_getf (anal->sdb_types, NULL, "func.%s.cc", type_name);
	}
	if (R_STR_ISNOTEMPTY (callconv) && r_anal_cc_exist (anal, callconv)) {
		return callconv;
	}
	const char *fcncc = !fcn? NULL: resolve_dynamic? r_anal_function_cc (fcn): fcn->callconv;
	if (R_STR_ISNOTEMPTY (fcncc) && r_anal_cc_exist (anal, fcncc)) {
		callconv = fcncc;
	}
	if (!callconv) {
		callconv = r_anal_cc_default (anal);
	}
	return callconv;
}

static bool function_signature_fallback_to_vars(RAnal *anal, RAnalFunction *fcn, RAnalFunctionSignature *signature) {
	bool ok = true;

	R_RETURN_VAL_IF_FAIL (anal && fcn && signature && signature->params, false);
	RVecAnalVarPtr *vars = RVecAnalVarPtr_new ();
	if (!vars) {
		return false;
	}
	RVecAnalVarPtr *kinds[] = {
		r_anal_var_vec (anal, fcn, R_ANAL_VAR_KIND_REG),
		r_anal_var_vec (anal, fcn, R_ANAL_VAR_KIND_BPV),
		r_anal_var_vec (anal, fcn, R_ANAL_VAR_KIND_SPV),
	};
	size_t k;
	for (k = 0; k < R_ARRAY_SIZE (kinds); k++) {
		if (kinds[k]) {
			RAnalVar **entry;
			R_VEC_FOREACH (kinds[k], entry) {
				RVecAnalVarPtr_push_back (vars, entry);
			}
			RVecAnalVarPtr_free (kinds[k]);
		}
	}
	const size_t count = RVecAnalVarPtr_length (vars);
	FunctionArgOrder *order = count? R_NEWS0 (FunctionArgOrder, count): NULL;
	if (count && !order) {
		RVecAnalVarPtr_free (vars);
		return false;
	}
	size_t i = 0;
	RAnalVar **entry;
	R_VEC_FOREACH (vars, entry) {
		const int cc_index = function_arg_cc_index (anal, fcn, *entry);
		order[i].var = *entry;
		// A register argument sorts by its convention slot; everything else
		// keeps the ordering the comparator already gave it.
		order[i].order = cc_index < 0? INT_MAX: cc_index;
		i++;
	}
	if (order) {
		qsort (order, count, sizeof (*order), function_arg_order_cmp);
		RVecAnalVarPtr_fini (vars);
		RVecAnalVarPtr_init (vars);
		for (i = 0; i < count; i++) {
			RVecAnalVarPtr_push_back (vars, &order[i].var);
		}
	}
	free (order);
	RAnalVar **it;
	R_VEC_FOREACH (vars, it) {
		RAnalVar *var = *it;
		RAnalFunctionParam *param;
		if (!var->isarg || R_STR_ISEMPTY (var->type)) {
			continue;
		}
		param = R_NEW0 (RAnalFunctionParam);
		param->name = var->name? strdup (var->name): NULL;
		param->type = strdup (var->type);
		r_list_append (signature->params, param);
		if (!param->type) {
			ok = false;
			break;
		}
	}
	RVecAnalVarPtr_free (vars);
	return ok;
}

static bool function_signature_is_noreturn(Sdb *types, const char *type_name, bool fallback) {
	R_RETURN_VAL_IF_FAIL (types, fallback);
	if (R_STR_ISEMPTY (type_name)) {
		return fallback;
	}
	const char *value = sdb_const_getf (types, NULL, "func.%s.noreturn", type_name);
	return value? r_str_is_true (value): fallback;
}

static char *function_signature_string(const char *name, const char *ret_type, RList *params, bool sanitize_name, bool fill_defaults) {
	RListIter *iter;
	RAnalFunctionParam *param;
	RStrBuf args;
	char *sane = NULL;
	char *signature = NULL;
	size_t i = 0;
	bool first = true;
	bool ok = true;

	R_RETURN_VAL_IF_FAIL (name, NULL);
	r_strbuf_init (&args);
	if (params) {
		r_list_foreach (params, iter, param) {
			RAnalFunctionParam tmp = {0};
			char *default_name = NULL;
			const RAnalFunctionParam *current = fill_defaults
				? function_signature_default_param (param, &tmp, i, &default_name)
				: param;
			ok = current && function_signature_append_arg (&args, current, first);
			free (default_name);
			if (!ok) {
				break;
			}
			first = false;
			i++;
		}
	}
	if (ok && sanitize_name) {
		sane = r_name_filter_dup (name);
		if (sane) {
			r_str_replace_ch (sane, ':', '_', true);
		}
	}
	if (ok) {
		const char *display_name = r_str_get_fail (sane, name);
		if (R_STR_ISNOTEMPTY (ret_type)) {
			signature = r_str_newf ("%s %s (%s);", ret_type, display_name, r_strbuf_get (&args));
		} else if (fill_defaults) {
			signature = r_str_newf ("void %s (%s);", display_name, r_strbuf_get (&args));
		} else {
			signature = r_str_newf ("%s (%s);", display_name, r_strbuf_get (&args));
		}
	}
	free (sane);
	r_strbuf_fini (&args);
	return signature;
}

static int var_comparator(const RAnalVar *a, const RAnalVar *b) {
	if (a && b) {
		if (a->isarg && !b->isarg) {
			return -1;
		}
		if (!a->isarg && b->isarg) {
			return 1;
		}
		if (a->kind == R_ANAL_VAR_KIND_REG && a->kind == b->kind) {
			if (a->argnum > b->argnum) {
				return 1;
			}
			if (a->argnum < b->argnum) {
				return -1;
			}
			return 0;
		}
		if (a->kind == b->kind && a->fcn) { // && a->fcn->bits == 32) {
			if (a->kind == R_ANAL_VAR_KIND_BPV) {
				if (a->isarg && b->isarg) {
					if (a->delta > b->delta) {
						return 1;
					}
					if (a->delta < b->delta) {
						return -1;
					}
				}
				if (a->delta > b->delta) {
					return -1;
				}
				if (a->delta < b->delta) {
					return 1;
				}
			}
		}
		if (a->delta > b->delta) {
			return 1;
		}
		if (a->delta < b->delta) {
			return -1;
		}
		return 0;
	} else if (a) {
		return 1;
	} else if (b) {
		return -1;
	}
	return 0;
	// avoid NULL dereference
	// return (a && b)? (a->delta > b->delta) - (a->delta < b->delta) : 0;
}

static RAnalBaseType *get_base_type_for_kind(RAnal *anal, const char *kind, const char *sname) {
	R_RETURN_VAL_IF_FAIL (anal && R_STR_ISNOTEMPTY (kind) && R_STR_ISNOTEMPTY (sname), NULL);
	if (!strcmp (kind, "struct")) {
		return get_composite_type (anal, sname, R_ANAL_BASE_TYPE_KIND_STRUCT);
	}
	if (!strcmp (kind, "enum")) {
		return get_enum_type (anal, sname);
	}
	if (!strcmp (kind, "union")) {
		return get_composite_type (anal, sname, R_ANAL_BASE_TYPE_KIND_UNION);
	}
	if (!strcmp (kind, "typedef")) {
		return get_typedef_type (anal, sname);
	}
	if (!strcmp (kind, "type")) {
		return get_atomic_type (anal, sname);
	}
	return NULL;
}

static bool type_snapshot_preflight_one(
	RAnal *anal,
	Sdb *seen,
	RAnalTypeSnapshotBudget *used,
	const RAnalFunctionSnapshotLimits *limits,
	const char *kind,
	const char *sname) {
	const char *data = sdb_const_getf (anal->sdb_types, NULL, "%s.%s", kind, sname);
	if (!data) {
		return true;
	}
	size_t name_bytes;
	if (r_add_overflow_size_t (strlen (sname), 1, &name_bytes)
		|| name_bytes > limits->max_base_type_string_bytes) {
		return false;
	}
	char *seen_key = r_str_newf ("%s.%s", kind, sname);
	if (!seen_key) {
		return false;
	}
	if (sdb_exists (seen, seen_key)) {
		free (seen_key);
		return true;
	}
	RAnalTypeSnapshotBudget added = { .base_types = 1 };
	if (!type_snapshot_budget_add_string (&added, strlen (sname))
		|| !type_snapshot_budget_fits (used, &added, limits)) {
		free (seen_key);
		return false;
	}
	if (!strcmp (kind, "typedef") || !strcmp (kind, "type")) {
		if (!type_snapshot_budget_add_string (&added, strlen (data))) {
			free (seen_key);
			return false;
		}
	} else {
		const bool composite = strcmp (kind, "enum");
		const char *cursor = data;
		while (*cursor) {
			const char *comma = strchr (cursor, ',');
			const size_t name_length = comma? (size_t)(comma - cursor): strlen (cursor);
			if (!name_length) {
				cursor = comma? comma + 1: cursor + 1;
				continue;
			}
			if (!type_snapshot_budget_add (&added.children, 1, SIZE_MAX)
				|| !type_snapshot_budget_add_string (&added, name_length)
				|| !type_snapshot_budget_fits (used, &added, limits)) {
				free (seen_key);
				return false;
			}
			char *child_name = r_str_ndup (cursor, name_length);
			char *child_key = child_name
				? r_str_newf ("%s.%s.%s", kind, sname, child_name): NULL;
			free (child_name);
			if (!child_key) {
				free (seen_key);
				return false;
			}
			const char *value = sdb_const_get (anal->sdb_types, child_key, NULL);
			free (child_key);
			if (!value) {
				free (seen_key);
				return true;
			}
			if (composite
				&& (!type_snapshot_budget_add_string (
						&added, type_snapshot_member_type_length (value))
					|| !type_snapshot_budget_fits (used, &added, limits))) {
				free (seen_key);
				return false;
			}
			if (!comma) {
				break;
			}
			cursor = comma + 1;
		}
	}
	if (!type_snapshot_budget_commit (used, &added, limits)
		|| !sdb_set (seen, seen_key, "1", 0)) {
		free (seen_key);
		return false;
	}
	free (seen_key);
	return true;
}

static bool dyncc_parse_attrs(const char *s, const char *end, RAnalDynCC *d) {
	while (s < end) {
		if (*s++ != '!' || s >= end) {
			return false;
		}
		const char tag = *s++;
		const char *next = memchr (s, '!', end - s);
		if (!next) {
			next = end;
		}
		if (tag == 'p') {
			if (s == next) {
				return false;
			}
			if (next - s == 1 && *s == '?') {
				d->stack_pop = R_ANAL_CC_STACK_POP_UNKNOWN;
			} else {
				const char *p = s;
				int pop = 0;
				if (!dyncc_parse_int (&p, &pop) || p != next) {
					return false;
				}
				d->stack_pop = pop;
			}
		} else if (tag == 'C' || tag == 'P') {
			if (next - s < 2 || *s != '(' || next[-1] != ')') {
				return false;
			}
			if (!dyncc_set_slice (s, next, tag == 'C'? &d->clobbers: &d->preserves, R_ANAL_DYNCC_REGSET_SIZE)) {
				return false;
			}
		} else if (tag == 'F') {
			if (!dyncc_parse_fpargs (s, next, d)) {
				return false;
			}
		} else if (!dyncc_set_role (d, tag, s, next)) {
			return false;
		}
		s = next;
	}
	return true;
}

static bool dyncc_parse_homed_list(const char *s, const char *end, RAnalDynCC *d, bool args) {
	if (s == end) {
		return true;
	}
	RAnalDynCCSlice *ref = args? &d->arg_ref: &d->ret_ref;
	if (dyncc_parse_ref_only (s, end, ref)) {
		return true;
	}
	RAnalDynCCHomes *dst = args? d->args: d->rets;
	int *dst_count = args? &d->arg_count: &d->ret_count;
	while (s < end) {
		const char *next = memchr (s, ',', end - s);
		if (!next) {
			next = end;
		}
		if (next == s || (args && d->arg_tail)) {
			return false;
		}
		RAnalDynCCHomes homes[R_ANAL_CC_MAXARG] = {0};
		int count = 0;
		if (!dyncc_parse_homes (s, next, homes, &count)) {
			return false;
		}
		if (args && count == 1 && homes[0].home_count == 1 && dyncc_tail_loc (&homes[0].homes[0])) {
			if (next < end) {
				return false;
			}
			d->arg_tail = true;
			d->arg_tail_loc = homes[0].homes[0];
		} else {
			if (*dst_count > R_ANAL_CC_MAXARG - count) {
				return false;
			}
			int i;
			for (i = 0; i < count; i++) {
				if (!args && homes[i].home_count != 1) {
					return false;
				}
				dst[(*dst_count)++] = homes[i];
			}
		}
		s = next < end? next + 1: next;
	}
	return true;
}

static int function_arg_cc_index(RAnal *anal, RAnalFunction *fcn, const RAnalVar *var) {
	if (!var || !var->isarg || var->kind != R_ANAL_VAR_KIND_REG
			|| R_STR_ISEMPTY (fcn->callconv)) {
		return -1;
	}
	RRegItem *reg = var->regname
		? r_reg_get (anal->reg, var->regname, -1)
		: r_reg_index_get (anal->reg, var->delta);
	if (!reg) {
		return -1;
	}
	int found = -1;
	const int maximum = r_anal_cc_max_arg (anal, fcn->callconv);
	int index;
	for (index = 0; index < maximum && found < 0; index++) {
		const char *location = r_anal_cc_argloc (anal, fcn->callconv, index, 0, 0);
		if (location && r_anal_cc_location_uses (anal, location, reg->name)) {
			found = index;
		}
	}
	r_unref (reg);
	return found;
}

static int function_arg_order_cmp(const void *a, const void *b) {
	const FunctionArgOrder *x = a;
	const FunctionArgOrder *y = b;
	if (x->order != y->order) {
		return x->order < y->order? -1: 1;
	}
	return function_arg_var_cmp (x->var, y->var);
}

static bool function_signature_append_arg(RStrBuf *args, const RAnalFunctionParam *param, bool first) {
	char *arg = function_param_string (param);
	if (!arg) {
		return false;
	}
	const bool ok = r_strbuf_appendf (args, "%s%s", first? "": ", ", arg);
	free (arg);
	return ok;
}

static const RAnalFunctionParam *function_signature_default_param(const RAnalFunctionParam *param, RAnalFunctionParam *tmp, size_t idx, char **default_name) {
	*default_name = NULL;
	tmp->type = (param && R_STR_ISNOTEMPTY (param->type))? param->type: "void";
	if (param && R_STR_ISNOTEMPTY (param->name)) {
		tmp->name = param->name;
		return tmp;
	}
	*default_name = r_str_newf ("arg%zu", idx);
	if (!*default_name) {
		return NULL;
	}
	tmp->name = *default_name;
	return tmp;
}

static RAnalBaseType *get_atomic_type(RAnal *anal, const char *sname) {
	R_RETURN_VAL_IF_FAIL (anal && R_STR_ISNOTEMPTY (sname), NULL);
	RAnalBaseType *base_type = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_ATOMIC);
	if (base_type) {
		base_type->type = get_type_data (anal->sdb_types, "type", sname);
		if (base_type->type) {
			base_type->size = sdb_num_getf (anal->sdb_types, NULL, "type.%s.size", sname);
			return base_type;
		}
		r_anal_base_type_free (base_type);
	}
	return NULL;
}

static RAnalBaseType *get_composite_type(RAnal *anal, const char *sname, RAnalBaseTypeKind kind) {
	R_RETURN_VAL_IF_FAIL (anal && sname, NULL);

	RAnalBaseType *base_type = r_anal_base_type_new (kind);
	if (!base_type) {
		return NULL;
	}

	const char *kindstr = (kind == R_ANAL_BASE_TYPE_KIND_UNION)? "union": "struct";
	char *sdb_members = get_type_data (anal->sdb_types, kindstr, sname);
	if (!sdb_members) {
		goto error;
	}

	RVecAnalTypeMember *members = r_anal_base_type_members (base_type);
	if (!RVecAnalTypeMember_reserve (members, (size_t)sdb_alen (sdb_members))) {
		goto error;
	}

	char *cur;
	sdb_aforeach (cur, sdb_members) {
		const char *value = sdb_const_getf (anal->sdb_types, NULL, "%s.%s.%s", kindstr, sname, cur);
		char *values = value? strdup (value): NULL;

		if (!values) {
			goto error;
		}
		const char *offset = NULL;
		const char *count = NULL;
		split_member_csv (values, &offset, &count);
		RAnalTypeMember memb = {
			.name = strdup (cur),
			.type = strdup (values),
			.offset = offset? strtoul (offset, NULL, 10): 0,
			.count = R_STR_ISNOTEMPTY (count)? strtoul (count, NULL, 10): 0
		};
		free (values);
		if (!memb.name || !memb.type) {
			anal_type_member_fini (&memb);
			goto error;
		}
		RAnalTypeMember *element = RVecAnalTypeMember_emplace_back (members);
		if (!element) {
			anal_type_member_fini (&memb);
			goto error;
		}
		*element = memb;

		sdb_aforeach_next (cur);
	}
	free (sdb_members);

	return base_type;

error:
	r_anal_base_type_free (base_type);
	free (sdb_members);
	return NULL;
}

static RAnalBaseType *get_enum_type(RAnal *anal, const char *sname) {
	R_RETURN_VAL_IF_FAIL (anal && sname, NULL);

	RAnalBaseType *base_type = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_ENUM);
	if (!base_type) {
		return NULL;
	}

	char *members = get_type_data (anal->sdb_types, "enum", sname);
	if (!members) {
		goto error;
	}

	RVecAnalEnumCase *cases = &base_type->enum_data.cases;
	if (!RVecAnalEnumCase_reserve (cases, (size_t)sdb_alen (members))) {
		goto error;
	}

	char *cur;
	sdb_aforeach (cur, members) {
		const char *value = sdb_const_getf (anal->sdb_types, NULL, "enum.%s.%s", sname, cur);

		if (!value) { // if nothing is found, ret NULL
			goto error;
		}

		RAnalEnumCase cas = { .name = strdup (cur), .val = strtol (value, NULL, 16) };
		if (!cas.name) {
			goto error;
		}
		RAnalEnumCase *element = RVecAnalEnumCase_emplace_back (cases);
		if (!element) {
			free (cas.name);
			goto error;
		}
		*element = cas;

		sdb_aforeach_next (cur);
	}
	free (members);

	return base_type;

error:
	free (members);
	r_anal_base_type_free (base_type);
	return NULL;
}

static RAnalBaseType *get_typedef_type(RAnal *anal, const char *sname) {
	R_RETURN_VAL_IF_FAIL (anal && R_STR_ISNOTEMPTY (sname), NULL);

	RAnalBaseType *base_type = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_TYPEDEF);
	if (!base_type) {
		return NULL;
	}

	base_type->type = get_type_data (anal->sdb_types, "typedef", sname);
	if (!base_type->type) {
		goto error;
	}
	return base_type;

error:
	r_anal_base_type_free (base_type);
	return NULL;
}

static bool type_snapshot_budget_add(size_t *total, size_t amount, size_t maximum) {
	size_t next;
	if (r_add_overflow_size_t (*total, amount, &next) || next > maximum) {
		return false;
	}
	*total = next;
	return true;
}

static bool type_snapshot_budget_add_string(RAnalTypeSnapshotBudget *budget, size_t length) {
	size_t owned_bytes;
	return !r_add_overflow_size_t (length, 1, &owned_bytes)
		&& type_snapshot_budget_add (&budget->string_bytes, owned_bytes, SIZE_MAX);
}

static bool type_snapshot_budget_commit(
	RAnalTypeSnapshotBudget *used,
	const RAnalTypeSnapshotBudget *added,
	const RAnalFunctionSnapshotLimits *limits) {
	if (!type_snapshot_budget_fits (used, added, limits)) {
		return false;
	}
	return type_snapshot_budget_add (&used->base_types, added->base_types, SIZE_MAX)
		&& type_snapshot_budget_add (&used->children, added->children, SIZE_MAX)
		&& type_snapshot_budget_add (&used->string_bytes, added->string_bytes, SIZE_MAX);
}

static bool type_snapshot_budget_fits(
	const RAnalTypeSnapshotBudget *used,
	const RAnalTypeSnapshotBudget *added,
	const RAnalFunctionSnapshotLimits *limits) {
	size_t total;
	return !r_add_overflow_size_t (used->base_types, added->base_types, &total)
		&& total <= limits->max_base_types
		&& !r_add_overflow_size_t (used->children, added->children, &total)
		&& total <= limits->max_base_type_children
		&& !r_add_overflow_size_t (used->string_bytes, added->string_bytes, &total)
		&& total <= limits->max_base_type_string_bytes;
}

static size_t type_snapshot_member_type_length(const char *value) {
	const char *last = strrchr (value, ',');
	if (!last) {
		return strlen (value);
	}
	const char *middle = NULL;
	const char *cursor;
	for (cursor = value; cursor < last; cursor++) {
		if (*cursor == ',') {
			middle = cursor;
		}
	}
	return (size_t)((middle? middle: last) - value);
}

static bool dyncc_parse_fpargs(const char *s, const char *end, RAnalDynCC *d) {
	if (s == end || !dyncc_slice_empty (&d->fparg_ref) || d->fparg_count) {
		return false;
	}
	if (dyncc_parse_ref_only (s, end, &d->fparg_ref)) {
		return true;
	}
	while (s < end) {
		const char *next = memchr (s, ',', end - s);
		if (!next) {
			next = end;
		}
		RAnalDynCCHomes homes[R_ANAL_CC_MAXARG] = {0};
		int count = 0;
		if (next == s || !dyncc_parse_homes (s, next, homes, &count)
				|| d->fparg_count > R_ANAL_CC_MAXARG - count) {
			return false;
		}
		int i;
		for (i = 0; i < count; i++) {
			d->fpargs[d->fparg_count++] = homes[i];
		}
		s = next < end? next + 1: next;
	}
	return true;
}

static bool dyncc_parse_homes(const char *s, const char *end, RAnalDynCCHomes *homes, int *count) {
	RAnalDynCCSeq seqs[R_ANAL_DYNCC_MAX_HOMES] = {0};
	int home_count = 0;
	int loc_count = -1;
	while (s < end) {
		if (home_count >= R_ANAL_DYNCC_MAX_HOMES) {
			return false;
		}
		const char *next = memchr (s, '\'', end - s);
		if (!next) {
			next = end;
		}
		if (next == s || !dyncc_parse_loc_seq (s, next, &seqs[home_count])) {
			return false;
		}
		if (loc_count < 0) {
			loc_count = seqs[home_count].count;
		} else if (loc_count != seqs[home_count].count) {
			return false;
		}
		home_count++;
		s = next < end? next + 1: next;
	}
	if (home_count < 1 || loc_count < 1) {
		return false;
	}
	int i;
	for (i = 0; i < loc_count; i++) {
		int h;
		for (h = 0; h < home_count; h++) {
			homes[i].homes[h] = seqs[h].locs[i];
		}
		homes[i].home_count = home_count;
	}
	*count = loc_count;
	return true;
}

static bool dyncc_parse_int(const char **sp, int *out) {
	const char *s = *sp;
	ut64 n = 0;
	if (!isdigit ((ut8)*s)) {
		return false;
	}
	while (isdigit ((ut8)*s)) {
		n = (n * 10) + (*s++ - '0');
		if (n > ST32_MAX) {
			return false;
		}
	}
	*out = (int)n;
	*sp = s;
	return true;
}

static bool dyncc_parse_ref_only(const char *s, const char *end, RAnalDynCCSlice *out) {
	return !memchr (s, ',', end - s) && !memchr (s, '\'', end - s)
		&& dyncc_parse_ref (s, end, out);
}

static bool dyncc_set_role(RAnalDynCC *d, char tag, const char *s, const char *end) {
	if (!dyncc_role_tag (tag) || s >= end) {
		return false;
	}
	int slot = dyncc_find_role (d, tag);
	if (slot < 0) {
		if (d->role_count >= R_ANAL_DYNCC_MAX_ROLES) {
			return false;
		}
		slot = d->role_count++;
	}
	RAnalDynCCRole *role = &d->roles[slot];
	memset (role, 0, sizeof (*role));
	role->tag = tag;
	role->arg = -1;
	const char *p = s;
	int arg = -1;
	if (dyncc_parse_int (&p, &arg) && p == end) {
		role->arg = arg;
		return true;
	}
	RAnalDynCCSeq seq = {0};
	if (!dyncc_parse_loc_seq (s, end, &seq) || seq.count != 1) {
		return false;
	}
	role->loc = seq.locs[0];
	return true;
}

static bool dyncc_set_slice(const char *s, const char *end, RAnalDynCCSlice *out, size_t maxlen) {
	size_t len = end - s;
	if (!len || len >= maxlen) {
		return false;
	}
	out->p = s;
	out->len = (ut16)len;
	return true;
}

static bool dyncc_tail_loc(const RAnalDynCCLoc *loc) {
	return loc && !loc->indexed
		&& (dyncc_slice_eq (&loc->text, "^") || dyncc_slice_eq (&loc->text, "^-"));
}

static int function_arg_var_cmp(const RAnalVar *a, const RAnalVar *b) {
	if (a && b) {
		if (a->isarg && !b->isarg) {
			return -1;
		}
		if (!a->isarg && b->isarg) {
			return 1;
		}
		if (a->kind == R_ANAL_VAR_KIND_REG && a->kind == b->kind) {
			if (a->argnum > b->argnum) {
				return 1;
			}
			if (a->argnum < b->argnum) {
				return -1;
			}
			return 0;
		}
		if (a->kind == b->kind && a->kind == R_ANAL_VAR_KIND_BPV && a->isarg && b->isarg) {
			if (a->delta > b->delta) {
				return 1;
			}
			if (a->delta < b->delta) {
				return -1;
			}
			return 0;
		}
		if (a->delta > b->delta) {
			return 1;
		}
		if (a->delta < b->delta) {
			return -1;
		}
	}
	return 0;
}

static char *function_param_string(const RAnalFunctionParam *param) {
	R_RETURN_VAL_IF_FAIL (param && param->type, NULL);
	if (r_type_arg_is_vararg (param->type, param->name)) {
		return strdup ("...");
	}
	if (R_STR_ISEMPTY (param->name)) {
		return strdup (param->type);
	}
	if (r_str_endswith (param->type, "*")) {
		return r_str_newf ("%s%s", param->type, param->name);
	}
	return r_str_newf ("%s %s", param->type, param->name);
}

static char *get_type_data(Sdb *sdb_types, const char *type, const char *sname) {
	const char *value = sdb_const_getf (sdb_types, NULL, "%s.%s", type, sname);
	return value? strdup (value): NULL;
}

static void split_member_csv(char *values, const char **offset, const char **count) {
	*offset = NULL;
	*count = NULL;
	char *last = (char *)r_str_rchr (values, NULL, ',');
	if (!last) {
		return;
	}
	*last = 0;
	char *mid = (char *)r_str_rchr (values, last - 1, ',');
	if (mid) {
		*mid = 0;
		*offset = mid + 1;
		*count = last + 1;
	} else {
		*offset = last + 1;
	}
}

static int dyncc_find_role(const RAnalDynCC *d, char tag) {
	int i;
	for (i = 0; i < d->role_count; i++) {
		if (d->roles[i].tag == tag) {
			return i;
		}
	}
	return -1;
}

static bool dyncc_parse_loc_seq(const char *s, const char *end, RAnalDynCCSeq *seq) {
	if (s >= end) {
		return false;
	}
	if (*s == '^') {
		s++;
		const bool rev = s < end && *s == '-';
		if (rev) {
			s++;
		}
		if (s == end) {
			seq->locs[0] = (RAnalDynCCLoc) {
				.text = {
					.p = rev? "^-": "^",
					.len = rev? 2: 1
				}
			};
			seq->count = 1;
			return true;
		}
		const char prefix = rev? R_ANAL_DYNCC_REVSTACK_PREFIX: R_ANAL_DYNCC_STACK_PREFIX;
		return dyncc_parse_indexed_seq (seq, s, end, prefix) == 1;
	}
	const char *token = s;
	if (isalpha ((ut8)*s)) {
		const char prefix = *s++;
		int parsed = dyncc_parse_indexed_seq (seq, s, end, prefix);
		if (parsed > 0) {
			return true;
		}
		if (parsed < 0) {
			return false;
		}
	}
	if (!dyncc_parse_loc (token, end, &seq->locs[0])) {
		return false;
	}
	seq->count = 1;
	return true;
}

static bool dyncc_parse_ref(const char *s, const char *end, RAnalDynCCSlice *out) {
	if (s >= end || *s++ != '&') {
		return false;
	}
	if (!dyncc_parse_name (&s, end, out)) {
		return false;
	}
	return s == end;
}

static bool dyncc_role_tag(char tag) {
	switch (tag) {
	case 'T':
	case 'R':
	case 'V':
	case 'E':
	case 'X':
		return true;
	default:
		return islower ((ut8)tag) && tag != 'p';
	}
}

static bool dyncc_slice_empty(const RAnalDynCCSlice *slice) {
	return !slice || !slice->p || !slice->len;
}

static bool dyncc_slice_eq(const RAnalDynCCSlice *slice, const char *s) {
	size_t len = strlen (s);
	return slice->len == len && !strncmp (slice->p, s, len);
}

static int dyncc_parse_indexed_seq(RAnalDynCCSeq *seq, const char *s, const char *end, char prefix) {
	const char *p = s;
	int base = 0;
	if (!dyncc_parse_int (&p, &base)) {
		return 0;
	}
	int count = 1;
	int delta = 1;
	if (p < end) {
		if (*p != '+' && *p != '-') {
			return 0;
		}
		delta = *p++ == '-'? -1: 1;
		if (!dyncc_parse_int (&p, &count) || p != end) {
			return -1;
		}
	}
	return p == end && dyncc_set_indexed_seq (seq, prefix, base, count, delta)? 1: -1;
}

static bool dyncc_parse_loc(const char *s, const char *end, RAnalDynCCLoc *out) {
	if (!dyncc_set_slice (s, end, &out->text, R_ANAL_DYNCC_GROUP_SIZE)) {
		return false;
	}
	if (dyncc_slice_eq (&out->text, "_")) {
		return true;
	}
	if (dyncc_range_startswith (s, end, "stack")) {
		return false;
	}
	if (*s == '&') {
		return false;
	}
	if (!isalnum ((ut8)*s)) {
		return false;
	}
	while (s < end) {
		if (!isalnum ((ut8)*s) && *s != '_' && *s != '.') {
			return false;
		}
		s++;
	}
	return true;
}

static bool dyncc_parse_name(const char **sp, const char *end, RAnalDynCCSlice *out) {
	const char *s = *sp;
	const char *n = s;
	while (n < end && (isalnum ((ut8)*n) || *n == '_' || *n == '.' || *n == '-')) {
		n++;
	}
	size_t len = n - s;
	if (!len || len >= R_ANAL_DYNCC_NAME_SIZE) {
		return false;
	}
	out->p = s;
	out->len = (ut16)len;
	*sp = n;
	return true;
}

static const char *dyncc_range_startswith(const char *s, const char *end, const char *prefix) {
	size_t len = strlen (prefix);
	return end - s >= len && !strncmp (s, prefix, len)? s + len: NULL;
}

static bool dyncc_set_indexed_seq(RAnalDynCCSeq *seq, char prefix, int base, int count, int delta) {
	if (count <= 0 || count > R_ANAL_CC_MAXARG || (delta < 0 && base < count - 1)) {
		return false;
	}
	int i;
	for (i = 0; i < count; i++) {
		seq->locs[i] = (RAnalDynCCLoc) {
			.indexed = true,
			.prefix = prefix,
			.index = base + (i * delta)
		};
	}
	seq->count = count;
	return true;
}

/* ---- entry points ---- */

/* True when any layer of the IO stack is a live debugger target.
 *
 * Mirrors radare2's own guard: a snapshot claims the bytes under a function
 * are what the analysis saw, and a running process can change them between
 * the read and the proof. */
static bool capture_io_is_debug(RIO *io) {
	if (!io) {
		return false;
	}
	RIODesc *desc = r_io_desc_get_lowest (io);
	while (desc) {
		if (r_io_desc_is_dbg (desc)) {
			return true;
		}
		desc = r_io_desc_get_next (io, desc);
	}
	return false;
}

RAnalFunctionSnapshot *r2sleigh_function_snapshot_take(RCore *core, ut64 function_addr, const char **reason) {
	R_RETURN_VAL_IF_FAIL (core && core->anal && core->lock && core->anal->lock, NULL);
	RAnalFunctionSnapshot *snapshot = NULL;
	if (reason) {
		*reason = NULL;
	}
	r_th_lock_enter (core->lock);
	if (capture_io_is_debug (core->io)) {
		if (reason) {
			*reason = "snapshots are not taken from a debug-backed target";
		}
		goto beach;
	}
	RAnalFunction *fcn = r_anal_get_function_at (core->anal, function_addr);
	if (!fcn || fcn->addr != function_addr) {
		if (reason) {
			*reason = "no function starts at that address";
		}
		goto beach;
	}
	r_th_lock_enter (core->anal->lock);
	snapshot = r_anal_function_snapshot_collect_bounded (core->anal, fcn, reason);
	r_th_lock_leave (core->anal->lock);
beach:
	r_th_lock_leave (core->lock);
	return snapshot;
}

void r2sleigh_function_snapshot_free(RAnalFunctionSnapshot *snapshot) {
	r_anal_function_snapshot_free (snapshot);
}
