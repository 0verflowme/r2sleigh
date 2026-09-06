/* Snapshot-capture tests moved out of the radare2 fork's test/unit suite.
 * They exercise the capture, which now lives in the plugin, so they belong
 * beside it rather than inside radare2. */


static RCore *snapshot_test_core_new(void) {
	RCore *core = r_core_new ();
	if (!core) {
		return NULL;
	}
	if (!r_io_open_at (core->io, "malloc://1048576", R_PERM_RW, 0, 0)) {
		r_core_free (core);
		return NULL;
	}
	return core;
}

static bool snapshot_test_ensure_block(RAnal *anal, RAnalFunction *fcn, ut64 size) {
	if (fcn->bbs && r_list_length (fcn->bbs)) {
		return true;
	}
	RAnalBlock *block = r_anal_create_block (anal, fcn->addr, size);
	if (!block) {
		return false;
	}
	r_anal_function_add_block (fcn, block);
	r_unref (block);
	return true;
}

static bool snapshot_test_publish_owned_function_link(RAnal *anal, RAnalFunction *fcn) {
	return set_function_type_link (anal, fcn->name, fcn->addr)
		&& r_anal_dwarf_function_link_mark_poisoned (
			anal, fcn->addr, fcn->name)
		&& r_anal_function_type_link_set_owned (
			anal, fcn->name, fcn->addr)
		&& r_anal_dwarf_function_link_publish_owned (
			anal, fcn->addr, fcn->name);
}

static bool snapshot_test_publish_frame_pointer(RAnal *anal,
		RAnalFunction *fcn, const char *reg_name) {
	HtUP *proofs = r_anal_dwarf_frame_pointer_proofs_new ();
	if (!proofs) {
		return false;
	}
	bool prepared = true;
	if (R_STR_ISNOTEMPTY (reg_name)) {
		const int dwarf_reg_num = !strcmp (reg_name, "rbp")
			? 6: (!strcmp (reg_name, "rsp")? 7: -1);
		RRegItem *reg = r_reg_get (anal->reg, reg_name, -1);
		prepared = dwarf_reg_num >= 0 && reg
			&& reg->offset >= 0 && !(reg->offset % 8)
			&& reg->size > 0 && !(reg->size % 8)
			&& r_anal_dwarf_frame_pointer_proof_add (
				proofs, fcn->addr, fcn->name, anal->config->arch,
				anal->config->bits, dwarf_reg_num, reg_name,
				(ut64)(reg->offset / 8), (ut32)(reg->size / 8));
		r_unref (reg);
	}
	if (prepared && r_anal_dwarf_frame_pointer_proofs_publish (anal, proofs)) {
		return true;
	}
	r_anal_dwarf_frame_pointer_proofs_free (proofs);
	return false;
}

static RAnalFcnSlot *find_stack_slot(RAnalFcnContext *ctx, const char *name) {
	RListIter *iter;
	RAnalFcnSlot *slot;

	r_list_foreach (ctx->fcn_slots, iter, slot) {
		if (slot && slot->name && !strcmp (slot->name, name)) {
			return slot;
		}
	}
	return NULL;
}

static RAnalBaseType *find_snapshot_base_type(const RAnalFunctionSnapshot *snapshot, const char *name) {
	RListIter *iter;
	RAnalBaseType *type;
	r_list_foreach (snapshot->base_types, iter, type) {
		if (type && type->name && !strcmp (type->name, name)) {
			return type;
		}
	}
	return NULL;
}

static RAnalBaseType *find_snapshot_base_type_kind(const RAnalFunctionSnapshot *snapshot, const char *name, RAnalBaseTypeKind kind) {
	RListIter *iter;
	RAnalBaseType *type;
	r_list_foreach (snapshot->base_types, iter, type) {
		if (type && type->kind == kind && type->name && !strcmp (type->name, name)) {
			return type;
		}
	}
	return NULL;
}

static bool test_r_anal_function_snapshot_reads_current_state_only(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create read-only snapshot analysis");
	RAnalFunction *caller = r_anal_create_function (
		anal, "snapshot_current_caller", 0x6600, R_ANAL_FCN_TYPE_FCN, NULL);
	RAnalFunction *callee = r_anal_create_function (
		anal, "snapshot_current_callee", 0x6700, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (caller, "create read-only snapshot caller");
	mu_assert_notnull (callee, "create read-only snapshot callee");
	mu_assert_true (snapshot_test_ensure_block (anal, caller, 0x20),
		"back caller with exact bytes");
	caller->callconv = r_str_constpool_get (&anal->constpool, "dyncc");
	anal->binb.get_cc = snapshot_lazy_cc;
	snapshot_lazy_cc_calls = 0;
	mu_assert_true (r_anal_xrefs_setf (
		anal, caller, 0x6610, callee->addr, R_ANAL_REF_TYPE_CALL),
		"record current-state callee");
	RAnalPriv *priv = R_ANAL_PRIV (anal);
	priv->types_dirty = true;
	priv->types_loaded_bits = 0;
	ut64 function_epoch = r_anal_function_dirty_epoch (caller);
	ut64 type_epoch = r_anal_types_dirty_epoch (anal);

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, caller, NULL);
	mu_assert_eq (snapshot_lazy_cc_calls, 0,
		"snapshot does not resolve a lazy calling convention");
	mu_assert_streq (caller->callconv, "dyncc",
		"snapshot leaves the live calling convention untouched");
	mu_assert_true (priv->types_dirty,
		"snapshot does not lazily load the type database for callees");
	mu_assert_eq (priv->types_loaded_bits, 0,
		"snapshot leaves the current type-load state untouched");
	mu_assert_eq (r_anal_function_dirty_epoch (caller), function_epoch,
		"snapshot does not publish a function mutation");
	mu_assert_eq (r_anal_types_dirty_epoch (anal), type_epoch,
		"snapshot does not publish a type mutation");
	mu_assert_notnull (snapshot, "collect read-only current-state snapshot");
	mu_assert_false (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"unresolved current calling convention remains inexact");
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

static bool test_r_anal_function_snapshot_carries_linked_data_object_type(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create typed-data snapshot analysis");
	RAnalFunction *fcn = r_anal_create_function (
		anal, "reads_typed_global", 0x6800, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create typed-data snapshot function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back typed-data function with exact bytes");
	mu_assert_notnull (r_flag_set (core->flags, "global_counter", 0x7000, 4),
		"name typed data object");
	mu_assert_true (r_anal_xrefs_setf (
		anal, fcn, fcn->addr, 0x7000, R_ANAL_REF_TYPE_DATA),
		"record typed data reference");
	mu_assert_true (set_function_type_link (anal, "int32_t", 0x7000),
		"link source-owned data type by address");

	RAnalFunctionSnapshot *snapshot =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect typed-data snapshot");
	mu_assert_eq (snapshot->image.num_data_symbols, 1, "one referenced data object");
	RAnalSnapshotDataSymbolView view;
	mu_assert_true (r_anal_function_snapshot_data_symbol_view (snapshot, 0, &view),
		"view typed data object");
	mu_assert_eq (view.addr, 0x7000, "typed data address");
	mu_assert_eq (view.name_length, strlen ("global_counter"), "typed data name length");
	mu_assert_eq (view.type_name_length, strlen ("int32_t"), "typed data type length");
	char name[32];
	char type_name[32];
	mu_assert_true (r_anal_function_snapshot_data_symbol_name (
		snapshot, 0, name, sizeof (name)), "copy typed data name");
	mu_assert_true (r_anal_function_snapshot_data_symbol_type_name (
		snapshot, 0, type_name, sizeof (type_name)), "copy typed data type");
	mu_assert_streq (name, "global_counter", "exact typed data name");
	mu_assert_streq (type_name, "int32_t", "exact source-owned data type spelling");

	const ut64 old_revision = snapshot->revision_identity;
	mu_assert_true (set_function_type_link (anal, "uint32_t", 0x7000),
		"replace source-owned data type");
	RAnalFunctionSnapshot *changed =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (changed, "collect changed typed-data snapshot");
	mu_assert_neq (changed->revision_identity, old_revision,
		"data type participates in snapshot identity");
	mu_assert_true (r_anal_function_snapshot_data_symbol_type_name (
		changed, 0, type_name, sizeof (type_name)), "copy changed data type");
	mu_assert_streq (type_name, "uint32_t", "changed data type is current");
	mu_assert_true (r_anal_function_snapshot_data_symbol_type_name (
		snapshot, 0, type_name, sizeof (type_name)), "old data type remains readable");
	mu_assert_streq (type_name, "int32_t", "old snapshot remains immutable");

	r_anal_function_snapshot_free (changed);
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

static bool test_r_anal_function_snapshot_does_not_mutate_var_cache(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create read-only variable-cache analysis");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	mu_assert_true (r_anal_cc_set (anal, "rax readonlycc(rdi)"),
		"seed read-only variable-cache calling convention");
	RAnalFunction *fcn = r_anal_create_function (
		anal, "snapshot_var_cache", 0x6800, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create read-only variable-cache function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back variable-cache function with exact bytes");
	fcn->callconv = r_str_constpool_get (&anal->constpool, "readonlycc");
	const int rdi = reg_index (anal, "rdi");
	mu_assert ("rdi register index must resolve", rdi >= 0);
	RAnalVar *arg = r_anal_function_set_var (
		fcn, rdi, R_ANAL_VAR_KIND_REG, "int", 4, true, "arg0");
	mu_assert_notnull (arg, "create default-named register argument");
	mu_assert_eq (arg->argnum, -1, "live argument index starts unresolved");
	ut64 function_epoch = r_anal_function_dirty_epoch (fcn);

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect read-only variable-cache snapshot");
	mu_assert_eq (arg->argnum, -1,
		"snapshot leaves the live argument index unresolved");
	mu_assert_streq (arg->name, "arg0",
		"snapshot leaves the live default argument name untouched");
	mu_assert_eq (r_anal_function_dirty_epoch (fcn), function_epoch,
		"snapshot leaves the live function revision untouched");
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_context_collect_is_conservative_for_stack_slots(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "Couldn't create new RAnal");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	mu_assert_true (r_anal_cc_set (anal, "rax ctxcall(rdi, rdx, stack)"), "Couldn't seed test-local calling convention");

	RAnalFunction *fcn = r_anal_create_function (anal, "fcn_ctx", 0x1000, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "Couldn't create function for function-context test");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back function-context fixture with exact bytes");
	fcn->callconv = r_str_constpool_get (&anal->constpool, "ctxcall");

	RAnalFunctionParam params_data[] = {
		{ .name = "first", .type = "int" },
		{ .name = "second", .type = "int" },
		{ .name = "third", .type = "int" },
		{ .name = "fourth", .type = "int" },
	};
	RList *params = r_list_new ();
	mu_assert_notnull (params, "Couldn't create param list for function-context test");
	r_list_append (params, &params_data[0]);
	r_list_append (params, &params_data[1]);
	r_list_append (params, &params_data[2]);
	r_list_append (params, &params_data[3]);
	RAnalFunctionSignature signature = {
		.ret_type = "int",
		.callconv = "ctxcall",
		.params = params,
		.noreturn = false,
	};
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature), "typed signature apply for function-context test");
	mu_assert_true (set_function_type_link (anal, fcn->name, fcn->addr),
		"link function-context signature by address");
	r_list_free (params);

	const int rdi = reg_index (anal, "rdi");
	const int rdx = reg_index (anal, "rdx");
	mu_assert ("rdi register index must resolve", rdi >= 0);
	mu_assert ("rdx register index must resolve", rdx >= 0);

	RAnalVar *home_source = r_anal_function_set_var (fcn, rdi, R_ANAL_VAR_KIND_REG, "int", 4, true, "arg1");
	RAnalVar *sparse_reg = r_anal_function_set_var (fcn, rdx, R_ANAL_VAR_KIND_REG, "int", 4, true, "arg3");
	RAnalVar *home_slot = r_anal_function_set_var (fcn, -8, R_ANAL_VAR_KIND_BPV, "int", 4, false, "arg1_home");
	RAnalVar *stack_arg = r_anal_function_set_var (fcn, 0x28, R_ANAL_VAR_KIND_SPV, "int", 4, true, "stack_input");
	RAnalVar *saved_named = r_anal_function_set_var (fcn, -0x10, R_ANAL_VAR_KIND_BPV, "int", 4, false, "saved_rbx");
	RAnalVar *arg_named_local = r_anal_function_set_var (fcn, 0x30, R_ANAL_VAR_KIND_SPV, "int", 4, false, "arg2");
	mu_assert_notnull (home_source, "create register home source");
	mu_assert_notnull (sparse_reg, "create sparse register arg");
	mu_assert_notnull (home_slot, "create home slot");
	mu_assert_notnull (stack_arg, "create stack arg");
	mu_assert_notnull (saved_named, "create saved-named local");
	mu_assert_notnull (arg_named_local, "create arg-named local");
	free (home_source->regname);
	home_source->regname = strdup ("rdi");
	free (sparse_reg->regname);
	sparse_reg->regname = strdup ("rdx");

	r_anal_var_set_access (anal, home_source, "rdi", 0x1010, R_PERM_R, 0);
	r_anal_var_set_access (anal, home_slot, "rbp", 0x1010, R_PERM_W, -8);

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect typed function snapshot");
	RAnalFcnContext *ctx = &snapshot->context;
	mu_assert_eq (snapshot->schema_version, R_ANAL_FUNCTION_SNAPSHOT_SCHEMA_VERSION, "snapshot schema version");
	mu_assert_eq (snapshot->struct_size, sizeof (RAnalFunctionSnapshot), "snapshot structure size");
	mu_assert_eq (snapshot->function_addr, fcn->addr, "snapshot function address");
	mu_assert_streq (snapshot->function_name, fcn->name, "snapshot function name");
	mu_assert_notnull (snapshot->base_types, "snapshot owns a type-layout list");
	mu_assert_neq (snapshot->revision_identity, 0, "snapshot revision identity");
	mu_assert_eq (r_anal_function_context_hash (anal, fcn), snapshot->revision_identity, "compatibility hash is snapshot-derived");

	RAnalFcnSlot *home_ctx = find_stack_slot (ctx, "arg1_home");
	RAnalFcnSlot *stack_arg_ctx = find_stack_slot (ctx, "stack_input");
	RAnalFcnSlot *saved_ctx = find_stack_slot (ctx, "saved_rbx");
	RAnalFcnSlot *arg_named_local_ctx = find_stack_slot (ctx, "arg2");
	mu_assert_notnull (home_ctx, "home slot must be present in function context");
	mu_assert_notnull (stack_arg_ctx, "stack arg slot must be present in function context");
	mu_assert_notnull (saved_ctx, "saved-named slot must be present in function context");
	mu_assert_notnull (arg_named_local_ctx, "arg-named local slot must be present in function context");

	mu_assert_eq (home_ctx->role, R_ANAL_FCN_SLOT_HOME, "register-home stack slot must stay param-home");
	mu_assert_eq (home_ctx->arg_index, 0, "param-home slot must use source register param index");
	mu_assert_streq (snapshot->function_interface.parameters[0].name, "first",
		"canonical signature owns the parameter presentation name");
	mu_assert_streq (home_ctx->home_reg, "rdi", "param-home slot must keep source register");
	mu_assert_eq (home_ctx->home_reg_offset,
		snapshot->function_interface.parameters[0].storage.offset,
		"param-home slot must keep canonical source-register offset");
	mu_assert_eq (home_ctx->home_reg_size,
		snapshot->function_interface.parameters[0].storage.size,
		"param-home slot must keep canonical source-register size");
	mu_assert_false (snapshot->function_interface.stack_slot_roles_complete,
		"unsupported stack arguments reject exact stack-slot roles");
	mu_assert_false (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES,
		"unsupported stack arguments omit exact stack-slot-role capability");

	mu_assert_eq (stack_arg_ctx->role, R_ANAL_FCN_SLOT_ARG, "stack arg slot must stay stack-arg");
	mu_assert_eq (stack_arg_ctx->arg_index, -1, "stack arg slot must not synthesize param indexes from sparse register args");

	mu_assert_eq (saved_ctx->role, R_ANAL_FCN_SLOT_LOCAL, "saved-named local must not be reclassified from its spelling");
	mu_assert_eq (arg_named_local_ctx->role, R_ANAL_FCN_SLOT_LOCAL, "arg-named local must not become a param-home without a proven register home");

	ut64 old_revision = snapshot->revision_identity;
	char *snapshot_slot_name = strdup (r_str_get (home_ctx->name));
	mu_assert_notnull (snapshot_slot_name, "copy snapshot stack-slot name");
	ut64 old_function_epoch = r_anal_function_dirty_epoch (fcn);
	mu_assert_true (r_anal_var_rename (anal, home_slot, "renamed_home"), "rename through revision-aware API");
	mu_assert_neq (r_anal_function_dirty_epoch (fcn), old_function_epoch,
		"variable rename bumps the function revision epoch");
	mu_assert_streq (home_ctx->name, snapshot_slot_name, "collected snapshot remains immutable after live mutation");
	free (snapshot_slot_name);
	RAnalFunctionSnapshot *next = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (next, "collect snapshot after live mutation");
	mu_assert_neq (next->revision_identity, old_revision, "live mutation changes snapshot revision");
	r_anal_function_snapshot_free (next);

	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

static bool test_r_anal_function_snapshot_distinguishes_split_fallthrough(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create snapshot CFG analysis");
	mu_assert_true (r_anal_use (anal, "x86"), "select x86 snapshot CFG analyzer");
	r_anal_set_bits (anal, 64);

	const ut8 split_bytes[] = { 0xc7, 0x45, 0xfc, 0, 0, 0, 0, 0xc3 };
	const ut64 split_addr = 0x1800;
	mu_assert_true (r_io_write_at (core->io, split_addr, split_bytes,
		sizeof (split_bytes)), "write split-fallthrough machine bytes");
	RAnalFunction *split_fcn = r_anal_create_function (
		anal, "split_fallthrough", split_addr, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (split_fcn, "create split-fallthrough function");
	RAnalBlock *whole = r_anal_create_block (anal, split_addr, sizeof (split_bytes));
	mu_assert_notnull (whole, "create block before split");
	r_anal_function_add_block (split_fcn, whole);
	RAnalBlock *tail = r_anal_block_split (whole, split_addr + 7);
	mu_assert_notnull (tail, "split sequential block before return");
	mu_assert_eq (whole->jump, split_addr + 7, "split records structural successor in jump");
	r_unref (tail);
	r_unref (whole);

	RAnalFunctionSnapshot *split_snapshot = r_anal_function_snapshot_collect_bounded (
		anal, split_fcn, NULL);
	mu_assert_notnull (split_snapshot, "collect split-fallthrough snapshot");
	RAnalSnapshotSuccessorView successor = {0};
	mu_assert_true (r_anal_function_snapshot_successor_view (
		split_snapshot, 0, 0, &successor), "read split-fallthrough successor");
	mu_assert_eq (successor.kind, R_ANAL_SNAPSHOT_SUCCESSOR_FALLTHROUGH,
		"MOV-only split block has a machine-sequential successor");
	mu_assert_eq (successor.target_addr, split_addr + 7,
		"split fallthrough keeps the exact block-end target");
	r_anal_function_snapshot_free (split_snapshot);

	const ut8 branch_bytes[] = { 0xeb, 0, 0xc3 };
	const ut64 branch_addr = 0x2800;
	mu_assert_true (r_io_write_at (core->io, branch_addr, branch_bytes,
		sizeof (branch_bytes)), "write branch-to-next machine bytes");
	RAnalFunction *branch_fcn = r_anal_create_function (
		anal, "branch_to_next", branch_addr, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (branch_fcn, "create branch-to-next function");
	RAnalBlock *branch = r_anal_create_block (anal, branch_addr, 2);
	RAnalBlock *branch_tail = r_anal_create_block (anal, branch_addr + 2, 1);
	mu_assert_notnull (branch, "create explicit branch block");
	mu_assert_notnull (branch_tail, "create explicit branch target block");
	branch->jump = branch_addr + 2;
	r_anal_function_add_block (branch_fcn, branch);
	r_anal_function_add_block (branch_fcn, branch_tail);
	r_unref (branch);
	r_unref (branch_tail);

	RAnalFunctionSnapshot *branch_snapshot = r_anal_function_snapshot_collect_bounded (
		anal, branch_fcn, NULL);
	mu_assert_notnull (branch_snapshot, "collect branch-to-next snapshot");
	mu_assert_true (r_anal_function_snapshot_successor_view (
		branch_snapshot, 0, 0, &successor), "read branch-to-next successor");
	mu_assert_eq (successor.kind, R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT,
		"explicit branch-to-next remains a direct successor");
	mu_assert_eq (successor.target_addr, branch_addr + 2,
		"explicit branch keeps its exact target");
	r_anal_function_snapshot_free (branch_snapshot);

	const ut8 conditional_bytes[] = { 0x74, 0, 0xc3 };
	const ut64 conditional_addr = 0x3800;
	mu_assert_true (r_io_write_at (core->io, conditional_addr, conditional_bytes,
		sizeof (conditional_bytes)), "write conditional branch-to-next bytes");
	RAnalFunction *conditional_fcn = r_anal_create_function (
		anal, "incomplete_conditional", conditional_addr, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (conditional_fcn, "create incomplete conditional function");
	RAnalBlock *conditional = r_anal_create_block (anal, conditional_addr, 2);
	RAnalBlock *conditional_tail = r_anal_create_block (anal, conditional_addr + 2, 1);
	mu_assert_notnull (conditional, "create conditional branch block");
	mu_assert_notnull (conditional_tail, "create conditional target block");
	conditional->jump = conditional_addr + 2;
	r_anal_function_add_block (conditional_fcn, conditional);
	r_anal_function_add_block (conditional_fcn, conditional_tail);
	r_unref (conditional);
	r_unref (conditional_tail);
	mu_assert_null (r_anal_function_snapshot_collect_bounded (anal, conditional_fcn, NULL),
		"sole conditional edge cannot masquerade as direct or fallthrough");

	const ut8 indirect_bytes[] = { 0xff, 0xe0, 0xc3 };
	const ut64 indirect_addr = 0x4800;
	mu_assert_true (r_io_write_at (core->io, indirect_addr, indirect_bytes,
		sizeof (indirect_bytes)), "write indirect branch bytes");
	RAnalFunction *indirect_fcn = r_anal_create_function (
		anal, "incomplete_indirect", indirect_addr, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (indirect_fcn, "create incomplete indirect function");
	RAnalBlock *indirect = r_anal_create_block (anal, indirect_addr, 2);
	RAnalBlock *indirect_tail = r_anal_create_block (anal, indirect_addr + 2, 1);
	mu_assert_notnull (indirect, "create indirect branch block");
	mu_assert_notnull (indirect_tail, "create indirect target block");
	indirect->jump = indirect_addr + 2;
	r_anal_function_add_block (indirect_fcn, indirect);
	r_anal_function_add_block (indirect_fcn, indirect_tail);
	r_unref (indirect);
	r_unref (indirect_tail);
	// An unresolved indirect branch exits the block without naming where it
	// goes, so the edge the analysis recorded to the next address is dropped
	// rather than captured as a transfer the instruction contradicts. One such
	// branch does not discard the function. What must never happen is the
	// recorded edge surviving as a direct or fallthrough successor.
	RAnalFunctionSnapshot *indirect_snapshot = r_anal_function_snapshot_collect_bounded (
		anal, indirect_fcn, NULL);
	mu_assert_notnull (indirect_snapshot,
		"one unresolved branch does not discard the whole function");
	RAnalSnapshotBlockView indirect_view = {0};
	mu_assert_true (r_anal_function_snapshot_block_view (
		indirect_snapshot, 0, &indirect_view), "read the indirect branch block");
	mu_assert_eq (indirect_view.addr, indirect_addr,
		"the first block is the one ending in the indirect branch");
	mu_assert_eq (indirect_view.num_successors, 0,
		"indirect edge cannot masquerade as direct or fallthrough");
	mu_assert_false (r_anal_function_snapshot_successor_view (
		indirect_snapshot, 0, 0, &successor),
		"the dropped indirect edge is not readable as a successor");
	r_anal_function_snapshot_free (indirect_snapshot);

	anal->config->endian = R_SYS_ENDIAN_BIG;
	r_anal_set_bits (anal, 32);
	mu_assert_true (r_anal_use (anal, "mips"), "select MIPS delay-slot analyzer");
	const ut8 delay_bytes[] = {
		0x08, 0x00, 0x16, 0x02, // j 0x5808
		0x00, 0x00, 0x00, 0x00, // delay-slot nop
		0x03, 0xe0, 0x00, 0x08, // jr ra
		0x00, 0x00, 0x00, 0x00, // delay-slot nop
	};
	const ut64 delay_addr = 0x5800;
	mu_assert_true (r_io_write_at (core->io, delay_addr, delay_bytes,
		sizeof (delay_bytes)), "write delayed branch-to-next bytes");
	RAnalFunction *delay_fcn = r_anal_create_function (
		anal, "delayed_branch_to_next", delay_addr, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (delay_fcn, "create delayed branch-to-next function");
	RAnalBlock *delay = r_anal_create_block (anal, delay_addr, 8);
	RAnalBlock *delay_tail = r_anal_create_block (anal, delay_addr + 8, 8);
	mu_assert_notnull (delay, "create delayed branch block");
	mu_assert_notnull (delay_tail, "create delayed branch target block");
	delay->jump = delay_addr + 8;
	r_anal_function_add_block (delay_fcn, delay);
	r_anal_function_add_block (delay_fcn, delay_tail);
	r_unref (delay);
	r_unref (delay_tail);
	RAnalFunctionSnapshot *delay_snapshot = r_anal_function_snapshot_collect_bounded (
		anal, delay_fcn, NULL);
	mu_assert_notnull (delay_snapshot, "collect delayed branch-to-next snapshot");
	mu_assert_true (r_anal_function_snapshot_successor_view (
		delay_snapshot, 0, 0, &successor), "read delayed branch successor");
	mu_assert_eq (successor.kind, R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT,
		"delay-slot instruction cannot demote the effective direct terminator");
	r_anal_function_snapshot_free (delay_snapshot);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_limits_bound_type_clone(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create bounded snapshot analysis");
	sdb_reset (anal->sdb_types);
	RAnalFunction *fcn = r_anal_create_function (
		anal, "bounded_snapshot", 0x6800, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create bounded snapshot function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back bounded snapshot with exact bytes");

	RAnalBaseType *atomic = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_ATOMIC);
	atomic->name = strdup ("limit_u8");
	atomic->type = strdup ("u");
	atomic->size = 8;
	r_anal_save_base_type (anal, atomic);
	r_anal_base_type_free (atomic);

	RAnalBaseType *composite = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_STRUCT);
	composite->name = strdup ("limit_pair");
	RAnalStructMember member = {
		.name = strdup ("field"),
		.type = strdup ("limit_u8"),
	};
	RVecAnalTypeMember_push_back (&composite->struct_data.members, &member);
	r_anal_save_base_type (anal, composite);
	r_anal_base_type_free (composite);
	RAnalBaseType *enumeration = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_ENUM);
	enumeration->name = strdup ("limit_choice");
	RAnalEnumCase cas = {
		.name = strdup ("yes"),
		.val = 1,
	};
	RVecAnalEnumCase_push_back (&enumeration->enum_data.cases, &cas);
	r_anal_save_base_type (anal, enumeration);
	r_anal_base_type_free (enumeration);
	RAnalBaseType *alias = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_TYPEDEF);
	alias->name = strdup ("limit_alias");
	alias->type = strdup ("limit_u8");
	r_anal_save_base_type (anal, alias);
	r_anal_base_type_free (alias);
	/* Real type databases can contain a root kind marker whose payload was
	 * intentionally omitted. It is not a cloneable base type and must be
	 * skipped consistently by both the bounded preflight and clone. */
	sdb_set (anal->sdb_types, "incomplete_atomic", "type", 0);

	const size_t exact_string_bytes = sizeof ("limit_u8") + sizeof ("u")
		+ sizeof ("limit_pair") + sizeof ("field") + sizeof ("limit_u8")
		+ sizeof ("limit_choice") + sizeof ("yes")
		+ sizeof ("limit_alias") + sizeof ("limit_u8");
	RAnalFunctionSnapshotLimits limits;
	r_anal_function_snapshot_limits_default (&limits);
	limits.max_base_types = 4;
	limits.max_base_type_children = 2;
	limits.max_base_type_string_bytes = exact_string_bytes;
	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_with_limits (
		anal, fcn, &limits, NULL);
	mu_assert_notnull (snapshot, "exact type count and byte bounds succeed");
	mu_assert_eq (r_list_length (snapshot->base_types), 4,
		"root/namespace duplicates and payload-less markers are not charged");
	mu_assert_null (find_snapshot_base_type (snapshot, "incomplete_atomic"),
		"payload-less type marker is not exposed as a partial base type");
	RAnalBaseType *snapshot_atomic = find_snapshot_base_type (snapshot, "limit_u8");
	mu_assert_notnull (snapshot_atomic, "bounded snapshot owns atomic type");
	mu_assert_streq (snapshot_atomic->type, "u", "bounded snapshot owns atomic declaration");
	RAnalBaseType *snapshot_enum = find_snapshot_base_type (snapshot, "limit_choice");
	mu_assert_notnull (snapshot_enum, "bounded snapshot owns enum type");
	mu_assert_eq (RVecAnalEnumCase_length (&snapshot_enum->enum_data.cases), 1,
		"exact child bound includes enum variants");
	mu_assert_streq (RVecAnalEnumCase_at (&snapshot_enum->enum_data.cases, 0)->name,
		"yes", "enum variant name is owned");
	RAnalBaseType *snapshot_alias = find_snapshot_base_type (snapshot, "limit_alias");
	mu_assert_notnull (snapshot_alias, "bounded snapshot owns typedef");
	mu_assert_streq (snapshot_alias->type, "limit_u8", "typedef target string is owned");
	ut64 revision = snapshot->revision_identity;

	RAnalFunctionSnapshotLimits rejected = limits;
	rejected.max_base_types--;
	mu_assert_null (r_anal_function_snapshot_collect_with_limits (anal, fcn, &rejected, NULL),
		"base-type count rejects before constructing a partial snapshot");
	rejected = limits;
	rejected.max_base_type_children--;
	mu_assert_null (r_anal_function_snapshot_collect_with_limits (anal, fcn, &rejected, NULL),
		"member count rejects before constructing a partial snapshot");
	rejected = limits;
	rejected.max_base_type_string_bytes--;
	mu_assert_null (r_anal_function_snapshot_collect_with_limits (anal, fcn, &rejected, NULL),
		"owned type bytes reject before cloning strings");
	rejected = limits;
	rejected.struct_size--;
	mu_assert_null (r_anal_function_snapshot_collect_with_limits (anal, fcn, &rejected, NULL),
		"truncated limits contract is rejected");

	RAnalFunctionSnapshotLimits unbounded = limits;
	unbounded.max_base_types = SIZE_MAX;
	mu_assert_null (r_anal_function_snapshot_collect_with_limits (
		anal, fcn, &unbounded, NULL), "SIZE_MAX authority ceiling is rejected");

	atomic = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_ATOMIC);
	atomic->name = strdup ("limit_u8");
	atomic->type = strdup ("v");
	atomic->size = 8;
	r_anal_save_base_type (anal, atomic);
	r_anal_base_type_free (atomic);
	mu_assert_streq (snapshot_atomic->type, "u", "live type mutation cannot alter owned snapshot");
	RAnalFunctionSnapshot *next = r_anal_function_snapshot_collect_with_limits (
		anal, fcn, &limits, NULL);
	mu_assert_notnull (next, "collect bounded snapshot after type mutation");
	RAnalBaseType *next_atomic = find_snapshot_base_type (next, "limit_u8");
	mu_assert_notnull (next_atomic, "mutated atomic type remains in new snapshot");
	mu_assert_streq (next_atomic->type, "v", "new bounded snapshot observes live mutation");
	mu_assert_neq (next->revision_identity, revision,
		"bounded snapshot revision changes with type epoch and content");
	r_anal_function_snapshot_free (next);
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_seals_exact_register_interface(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "Couldn't create new RAnal");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	mu_assert_true (r_anal_cc_set (anal, "rax exactcc(rdi)"), "seed exact calling convention");
	sdb_set (anal->sdb_cc, "cc.exactcc.preserve", "rbp,rsp", 0);
	sdb_set (anal->sdb_cc, "cc.exactcc.retmech", "stack:0:8:8", 0);
	sdb_set (anal->sdb_cc, "cc.exactcc.stackalloc", "lower", 0);
	sdb_set (anal->sdb_cc, "cc.exactcc.redzone", "128", 0);

	RAnalFunction *fcn = r_anal_create_function (anal, "exact_snapshot", 0x7000, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create exact snapshot function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back exact interface with exact bytes");
	RAnalFunctionParam parameter = {
		.name = "value",
		.type = "int64_t",
	};
	RList *parameters = r_list_new ();
	mu_assert_notnull (parameters, "create exact parameter list");
	mu_assert_true (r_list_append (parameters, &parameter), "append exact parameter");
	RAnalFunctionSignature signature = {
		.ret_type = "int64_t",
		.callconv = "exactcc",
		.params = parameters,
	};
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature), "apply exact signature");
	r_list_free (parameters);
	RAnalFunctionSnapshot *name_only = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (name_only, "collect name-only signature snapshot");
	mu_assert_true (name_only->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_SIGNATURE,
		"name lookup remains available for ordinary signatures");
	mu_assert_false (name_only->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"name-only signature cannot certify an exact interface");
	mu_assert_true (name_only->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT,
		"stack allocation authority is independent of prototype completeness");
	mu_assert_true (name_only->function_interface.stack_pointer_preserved_across_calls,
		"call preservation is independent of prototype authority");
	mu_assert_true (name_only->function_interface.frame_pointer_preserved_across_calls,
		"frame-carrier preservation is independent of prototype authority");
	RAnalSnapshotStackAllocationContractView name_only_stack_allocation = {0};
	mu_assert_true (r_anal_function_snapshot_interface_stack_allocation_contract (
		name_only, &name_only_stack_allocation),
		"incomplete prototype still exposes exact machine stack geometry");
	mu_assert_eq (name_only_stack_allocation.growth,
		R_ANAL_SNAPSHOT_STACK_GROWTH_LOWER,
		"incomplete prototype preserves exact stack growth");
	mu_assert_eq (name_only_stack_allocation.implicit_active_sp_bytes, 128,
		"incomplete prototype preserves exact implicit stack extent");
	ut64 link_epoch = r_anal_types_dirty_epoch (anal);
	ut64 link_hash = r_anal_types_context_hash (anal);
	r_anal_function_snapshot_free (name_only);
	mu_assert_true (set_function_type_link (anal, fcn->name, fcn->addr),
		"link exact signature by address");
	mu_assert_neq (r_anal_types_dirty_epoch (anal), link_epoch,
		"function link bumps the type epoch");
	mu_assert_neq (r_anal_types_context_hash (anal), link_hash,
		"function link changes the type context hash");
	mu_assert_true (r_anal_function_has_address_linked_signature_current (fcn),
		"ordinary address link remains authoritative without private ownership");
	mu_assert_true (r_anal_dwarf_function_link_mark_poisoned (
		anal, fcn->addr, fcn->name), "prepare parser-owned address link");
	mu_assert_false (r_anal_function_has_address_linked_signature_current (fcn),
		"prepared poison blocks the exact address-linked signature");
	RAnalFunctionSnapshot *poisoned = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (poisoned, "collect poisoned address-link snapshot");
	mu_assert_false (poisoned->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"poisoned parser link cannot certify an exact interface");
	r_anal_function_snapshot_free (poisoned);
	mu_assert_true (r_anal_function_type_link_set_owned (anal, fcn->name, fcn->addr),
		"owned setter accepts the identical prepared link");
	mu_assert_true (r_anal_dwarf_function_link_poisoned_matches (
		anal, fcn->addr, fcn->name), "owned setter preserves prepared poison");
	mu_assert_true (r_anal_dwarf_function_link_publish_owned (
		anal, fcn->addr, fcn->name), "publish complete parser-owned link");
	mu_assert_true (r_anal_function_has_address_linked_signature_current (fcn),
		"owned publication restores exact address-link authority");
	RAnalFunctionSnapshot *published = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (published, "collect published address-link snapshot");
	mu_assert_true (published->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"published parser link restores exact-interface capability");
	r_anal_function_snapshot_free (published);
	mu_assert_true (snapshot_test_publish_frame_pointer (anal, fcn, "rbp"),
		"publish parser-owned full-width frame pointer");
	RAnalFunctionSnapshot *frame_snapshot =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (frame_snapshot, "collect slotless exact frame-pointer snapshot");
	mu_assert_true (frame_snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE,
		"slotless exact interface carries parser-owned frame pointer");
	mu_assert_true (frame_snapshot->function_interface.stack_pointer_preserved_across_calls,
		"calling convention preserves the stack-pointer carrier across calls");
	mu_assert_true (frame_snapshot->function_interface.frame_pointer_preserved_across_calls,
		"calling convention preserves the frame-pointer carrier across calls");
	RAnalSnapshotRegisterStorageView frame_pointer = {0};
	mu_assert_true (r_anal_function_snapshot_interface_frame_pointer_storage (
		frame_snapshot, &frame_pointer), "copy exact frame-pointer storage");
	RRegItem *rbp = r_reg_get (anal->reg, "rbp", -1);
	mu_assert_notnull (rbp, "resolve exact frame-pointer register");
	mu_assert_eq (frame_pointer.offset, (ut64)(rbp->offset / 8),
		"frame pointer uses canonical byte coordinates");
	mu_assert_eq (frame_pointer.size, 8, "frame pointer is address width");
	r_unref (rbp);
	char frame_pointer_name[16] = {0};
	mu_assert_true (r_anal_function_snapshot_interface_storage_name (
		frame_snapshot, R_ANAL_SNAPSHOT_INTERFACE_STORAGE_FRAME_POINTER,
		frame_pointer_name, sizeof (frame_pointer_name)),
		"copy exact frame-pointer name");
	mu_assert_streq (frame_pointer_name, "rbp", "frame pointer name is owned");
	const ut64 frame_pointer_revision = frame_snapshot->revision_identity;

	mu_assert_true (snapshot_test_publish_frame_pointer (anal, fcn, NULL),
		"publish authoritative absence of a frame-pointer proof");
	RAnalFunctionSnapshot *no_frame_snapshot =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (no_frame_snapshot, "collect snapshot without frame proof");
	mu_assert_false (no_frame_snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE,
		"absent proof cannot carry frame-pointer authority");
	frame_pointer.offset = 99;
	frame_pointer.size = 99;
	mu_assert_false (r_anal_function_snapshot_interface_frame_pointer_storage (
		no_frame_snapshot, &frame_pointer), "absent frame-pointer accessor refuses");
	mu_assert_eq (frame_pointer.offset, 0, "failed frame accessor clears offset");
	mu_assert_eq (frame_pointer.size, 0, "failed frame accessor clears size");
	mu_assert_neq (no_frame_snapshot->revision_identity, frame_pointer_revision,
		"frame-pointer presence participates in snapshot identity");
	mu_assert_true (r_anal_function_snapshot_interface_frame_pointer_storage (
		frame_snapshot, &frame_pointer), "old snapshot retains frame-pointer proof");
	mu_assert_eq (frame_pointer.size, 8, "old frame-pointer snapshot is immutable");
	r_anal_function_snapshot_free (no_frame_snapshot);

	mu_assert_true (snapshot_test_publish_frame_pointer (anal, fcn, "rsp"),
		"publish structurally conflicting frame-pointer proof");
	RAnalFunctionSnapshot *conflicting_frame_snapshot =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (conflicting_frame_snapshot,
		"collect conflicting frame-pointer snapshot");
	mu_assert_false (conflicting_frame_snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE,
		"stack-pointer overlap cannot carry frame-pointer authority");
	r_anal_function_snapshot_free (conflicting_frame_snapshot);
	mu_assert_true (snapshot_test_publish_frame_pointer (anal, fcn, "rbp"),
		"restore parser-owned frame-pointer proof");
	r_anal_function_snapshot_free (frame_snapshot);
	mu_assert_true (r_anal_dwarf_function_link_mark_poisoned (
		anal, fcn->addr, fcn->name), "poison owned link before user replacement");
	mu_assert_true (r_anal_function_type_link_set (anal, fcn->name, fcn->addr),
		"ordinary identical setter accepts a user replacement");
	mu_assert_false (r_anal_dwarf_function_link_poisoned_matches (
		anal, fcn->addr, fcn->name), "ordinary identical setter clears private ownership");
	mu_assert_true (r_anal_function_has_address_linked_signature_current (fcn),
		"same-valued foreign replacement remains authoritative");
	RAnalFunctionSnapshot *rsp_snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (rsp_snapshot, "collect full-width RSP snapshot");
	mu_assert_true (rsp_snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"full-width RSP carries stack-pointer authority");
	mu_assert_true (rsp_snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"slotless exact interface accepts full-width RSP");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "rbx"),
		"point SP role at a distinct full-width register");
	RAnalFunctionSnapshot *rbx_snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (rbx_snapshot, "collect full-width RBX snapshot");
	mu_assert_true (rbx_snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"full-width RBX carries stack-pointer authority");
	mu_assert_true (rbx_snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"slotless exact interface accepts full-width RBX");
	mu_assert_neq (rbx_snapshot->function_interface.stack_pointer_storage.offset,
		rsp_snapshot->function_interface.stack_pointer_storage.offset,
		"alternate stack-pointer role changes canonical byte coordinates");
	mu_assert_neq (rbx_snapshot->revision_identity, rsp_snapshot->revision_identity,
		"full-width stack-pointer storage participates in snapshot identity");
	r_anal_function_snapshot_free (rbx_snapshot);
	r_anal_function_snapshot_free (rsp_snapshot);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "rsp"),
		"restore canonical SP role");
	const int rdi = reg_index (anal, "rdi");
	mu_assert ("rdi register index must resolve", rdi >= 0);
	RAnalVar *home_source = r_anal_function_set_var (
		fcn, rdi, R_ANAL_VAR_KIND_REG, "int64_t", 8, true, "value");
	RAnalVar *bp_slot = r_anal_function_set_var (
		fcn, -8, R_ANAL_VAR_KIND_BPV, "int32_t", 4, false, "exact_bp_slot");
	RAnalVar *sp_slot = r_anal_function_set_var (
		fcn, -8, R_ANAL_VAR_KIND_SPV, "int32_t", 4, false, "exact_sp_slot");
	mu_assert_notnull (home_source, "create exact parameter-home source");
	mu_assert_notnull (bp_slot, "create exact BP stack slot");
	mu_assert_notnull (sp_slot, "create exact SP stack slot");
	r_anal_var_set_access (anal, home_source, "rdi", 0x7010, R_PERM_R, 0);
	r_anal_var_set_access (anal, bp_slot, "rbp", 0x7010, R_PERM_W, -8);

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect exact function snapshot");
	mu_assert_true (snapshot->function_interface.complete, "exact register interface is complete");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"exact interface capability is present");
	mu_assert_true (snapshot->function_interface.stack_slot_roles_complete,
		"local and canonical parameter-home roles are exact");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES,
		"exact stack-slot-role capability is present");
	mu_assert_streq (snapshot->function_interface.calling_convention, "exactcc", "exact calling convention");
	mu_assert_eq (snapshot->function_interface.num_parameters, 1, "one exact parameter");
	mu_assert_eq (snapshot->function_interface.parameters[0].index, 0, "exact parameter order");
	mu_assert_streq (snapshot->function_interface.parameters[0].name, "value",
		"exact parameter presentation name is owned");
	mu_assert_streq (snapshot->function_interface.parameters[0].storage.name, "rdi", "exact parameter register");
	RAnalSnapshotParameterView parameter_view = {0};
	mu_assert_true (r_anal_function_snapshot_parameter_view (
		snapshot, 0, &parameter_view), "copy exact parameter view");
	mu_assert_eq (parameter_view.name_length, strlen ("value"),
		"parameter view reports the exact owned presentation length");
	char parameter_name[16] = {0};
	mu_assert_true (r_anal_function_snapshot_parameter_name (
		snapshot, 0, parameter_name, sizeof (parameter_name)),
		"copy exact parameter presentation name");
	mu_assert_streq (parameter_name, "value", "parameter presentation copy is exact");
	RRegItem *rdi_item = r_reg_get (anal->reg, "rdi", -1);
	mu_assert_notnull (rdi_item, "resolve exact parameter carrier");
	mu_assert_eq (snapshot->function_interface.parameters[0].storage.offset,
		(ut64)(rdi_item->offset / 8),
		"parameter storage uses canonical byte coordinates");
	mu_assert_eq (snapshot->function_interface.return_kind, R_ANAL_SNAPSHOT_RETURN_REGISTER, "register return kind");
	RRegItem *rax_item = r_reg_get (anal->reg, "rax", -1);
	mu_assert_notnull (rax_item, "resolve exact return carrier");
	mu_assert_eq (snapshot->function_interface.return_storage.offset,
		(ut64)(rax_item->offset / 8),
		"return storage uses canonical byte coordinates");
	r_unref (rax_item);
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"exact x86 snapshot carries the typed return-address register");
	mu_assert_streq (snapshot->function_interface.return_address_storage.name, "rip",
		"stack-return target is carried in the typed PC register");
	RRegItem *rip = r_reg_get (anal->reg, "rip", -1);
	mu_assert_notnull (rip, "resolve typed PC carrier");
	mu_assert_eq (snapshot->function_interface.return_address_storage.offset,
		(ut64)(rip->offset / 8),
		"x86 return-address carrier uses canonical byte coordinates");
	r_unref (rip);
	mu_assert_eq (snapshot->function_interface.return_address_storage.size, 8,
		"x86 return-address carrier is full width");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"exact x86 snapshot carries the typed stack pointer");
	mu_assert_streq (snapshot->function_interface.stack_pointer_storage.name, "rsp",
		"typed SP role carries the full-width stack pointer");
	RRegItem *rsp = r_reg_get (anal->reg, "rsp", -1);
	mu_assert_notnull (rsp, "resolve typed SP carrier");
	mu_assert_eq (snapshot->function_interface.stack_pointer_storage.offset,
		(ut64)(rsp->offset / 8),
		"x86 stack-pointer carrier uses canonical byte coordinates");
	r_unref (rsp);
	mu_assert_eq (snapshot->function_interface.stack_pointer_storage.size, 8,
		"x86 stack-pointer carrier is full width");
	mu_assert_true (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM,
		"exact x86 snapshot carries its stack-return mechanism");
	RAnalSnapshotReturnMechanismView return_mechanism;
	mu_assert_true (r_anal_function_snapshot_interface_return_mechanism (
		snapshot, &return_mechanism), "copy exact stack-return mechanism");
	mu_assert_eq (return_mechanism.kind,
		R_ANAL_SNAPSHOT_RETURN_MECHANISM_STACK, "stack-return mechanism kind");
	mu_assert_eq (return_mechanism.entry_sp_offset, 0, "return slot starts at entry SP");
	mu_assert_eq (return_mechanism.slot_size, 8, "return slot is address-sized");
	mu_assert_eq (return_mechanism.exit_sp_delta, 8, "stack return consumes one slot");
	mu_assert_true (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT,
		"exact x86 snapshot carries its source-owned stack allocation contract");
	RAnalSnapshotStackAllocationContractView stack_allocation_contract;
	mu_assert_true (r_anal_function_snapshot_interface_stack_allocation_contract (
		snapshot, &stack_allocation_contract), "copy exact stack allocation contract");
	mu_assert_eq (stack_allocation_contract.growth,
		R_ANAL_SNAPSHOT_STACK_GROWTH_LOWER, "exact CC owns only lower-address reservations");
	mu_assert_eq (stack_allocation_contract.implicit_active_sp_bytes, 128,
		"exact CC seals its implicit active-SP red zone");
	const ut64 stack_allocation_revision = snapshot->revision_identity;
	sdb_set (anal->sdb_cc, "cc.exactcc.redzone", "64", 0);
	RAnalFunctionSnapshot *changed_red_zone =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (changed_red_zone, "collect changed red-zone contract");
	mu_assert_true (r_anal_function_snapshot_interface_stack_allocation_contract (
		changed_red_zone, &stack_allocation_contract),
		"changed red zone remains exact allocation authority");
	mu_assert_eq (stack_allocation_contract.growth,
		R_ANAL_SNAPSHOT_STACK_GROWTH_LOWER, "changed red zone preserves growth direction");
	mu_assert_eq (stack_allocation_contract.implicit_active_sp_bytes, 64,
		"changed red zone is sealed exactly");
	mu_assert_neq (changed_red_zone->revision_identity,
		stack_allocation_revision, "red-zone bytes participate in snapshot identity");
	r_anal_function_snapshot_free (changed_red_zone);
	const char *malformed_red_zones[] = { "junk", "-1", "4294967296" };
	size_t malformed_red_zone_index;
	for (malformed_red_zone_index = 0;
		malformed_red_zone_index < R_ARRAY_SIZE (malformed_red_zones);
		malformed_red_zone_index++) {
		sdb_set (anal->sdb_cc, "cc.exactcc.redzone",
			malformed_red_zones[malformed_red_zone_index], 0);
		RAnalFunctionSnapshot *malformed_red_zone =
			r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
		mu_assert_notnull (malformed_red_zone, "collect malformed red-zone contract");
		mu_assert_false (malformed_red_zone->capabilities
			& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT,
			"malformed red zone disables exact stack-allocation authority");
		stack_allocation_contract.growth = R_ANAL_SNAPSHOT_STACK_GROWTH_HIGHER;
		stack_allocation_contract.implicit_active_sp_bytes = 1;
		mu_assert_false (r_anal_function_snapshot_interface_stack_allocation_contract (
			malformed_red_zone, &stack_allocation_contract),
			"malformed red-zone accessor refuses");
		mu_assert_eq (stack_allocation_contract.growth,
			R_ANAL_SNAPSHOT_STACK_GROWTH_NONE,
			"refused red-zone accessor clears growth");
		mu_assert_eq (stack_allocation_contract.implicit_active_sp_bytes, 0,
			"refused red-zone accessor clears implicit active-SP bytes");
		r_anal_function_snapshot_free (malformed_red_zone);
	}
	sdb_unset (anal->sdb_cc, "cc.exactcc.redzone", 0);
	RAnalFunctionSnapshot *absent_red_zone =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (absent_red_zone, "collect allocation contract without red zone");
	mu_assert_true (absent_red_zone->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT,
		"absent red zone preserves exact stack-allocation authority");
	mu_assert_true (r_anal_function_snapshot_interface_stack_allocation_contract (
		absent_red_zone, &stack_allocation_contract),
		"allocation accessor accepts an absent red zone");
	mu_assert_eq (stack_allocation_contract.growth,
		R_ANAL_SNAPSHOT_STACK_GROWTH_LOWER,
		"absent red zone does not disable allocation growth");
	mu_assert_eq (stack_allocation_contract.implicit_active_sp_bytes, 0,
		"absent red zone seals exact zero implicit bytes");
	mu_assert_neq (absent_red_zone->revision_identity,
		stack_allocation_revision, "red-zone absence participates in snapshot identity");
	r_anal_function_snapshot_free (absent_red_zone);
	sdb_set (anal->sdb_cc, "cc.exactcc.redzone", "128", 0);
	sdb_set (anal->sdb_cc, "cc.exactcc.stackalloc", "down", 0);
	RAnalFunctionSnapshot *malformed_stack_allocation =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (malformed_stack_allocation, "collect malformed stack allocation contract");
	mu_assert_false (malformed_stack_allocation->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT,
		"unknown growth spelling carries no allocation authority");
	stack_allocation_contract.growth = R_ANAL_SNAPSHOT_STACK_GROWTH_HIGHER;
	mu_assert_false (r_anal_function_snapshot_interface_stack_allocation_contract (
		malformed_stack_allocation, &stack_allocation_contract),
		"malformed allocation accessor refuses");
	mu_assert_eq (stack_allocation_contract.growth,
		R_ANAL_SNAPSHOT_STACK_GROWTH_NONE, "refused accessor clears its scalar view");
	mu_assert_neq (malformed_stack_allocation->revision_identity,
		stack_allocation_revision, "malformed allocation changes snapshot identity");
	r_anal_function_snapshot_free (malformed_stack_allocation);
	sdb_set (anal->sdb_cc, "cc.exactcc.stackalloc", "higher", 0);
	RAnalFunctionSnapshot *higher_stack_allocation =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (higher_stack_allocation, "collect higher-address stack allocation contract");
	mu_assert_true (r_anal_function_snapshot_interface_stack_allocation_contract (
		higher_stack_allocation, &stack_allocation_contract),
		"higher-address contract remains explicit authority");
	mu_assert_eq (stack_allocation_contract.growth,
		R_ANAL_SNAPSHOT_STACK_GROWTH_HIGHER, "higher-address contract preserves direction");
	mu_assert_neq (higher_stack_allocation->revision_identity,
		stack_allocation_revision, "allocation direction participates in snapshot identity");
	r_anal_function_snapshot_free (higher_stack_allocation);
	sdb_unset (anal->sdb_cc, "cc.exactcc.stackalloc", 0);
	RAnalFunctionSnapshot *missing_stack_allocation =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (missing_stack_allocation, "collect missing stack allocation contract");
	mu_assert_false (missing_stack_allocation->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT,
		"missing source contract carries no allocation authority");
	r_anal_function_snapshot_free (missing_stack_allocation);
	sdb_set (anal->sdb_cc, "cc.exactcc.stackalloc", "lower", 0);
	ut64 return_mechanism_revision = snapshot->revision_identity;
	sdb_set (anal->sdb_cc, "cc.exactcc.retmech", "stack:8:8:16", 0);
	RAnalFunctionSnapshot *noncanonical_return_mechanism =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (noncanonical_return_mechanism, "collect noncanonical return mechanism");
	mu_assert_false (noncanonical_return_mechanism->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM,
		"noncanonical return-slot geometry carries no authority");
	mu_assert_neq (noncanonical_return_mechanism->revision_identity,
		return_mechanism_revision, "refused return mechanism changes snapshot identity");
	mu_assert_true (r_anal_function_snapshot_interface_return_mechanism (
		snapshot, &return_mechanism), "old snapshot retains return mechanism");
	mu_assert_eq (return_mechanism.entry_sp_offset, 0, "old snapshot remains immutable");
	r_anal_function_snapshot_free (noncanonical_return_mechanism);
	sdb_set (anal->sdb_cc, "cc.exactcc.retmech", "stack:0:0:8", 0);
	RAnalFunctionSnapshot *malformed_return_mechanism =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (malformed_return_mechanism, "collect malformed return mechanism");
	mu_assert_false (malformed_return_mechanism->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM,
		"malformed return mechanism carries no authority");
	return_mechanism.kind = R_ANAL_SNAPSHOT_RETURN_MECHANISM_STACK;
	return_mechanism.slot_size = 99;
	mu_assert_false (r_anal_function_snapshot_interface_return_mechanism (
		malformed_return_mechanism, &return_mechanism),
		"accessor rejects malformed return mechanism");
	mu_assert_eq (return_mechanism.kind, R_ANAL_SNAPSHOT_RETURN_MECHANISM_NONE,
		"failed accessor clears its scalar view");
	mu_assert_eq (return_mechanism.slot_size, 0, "failed accessor clears return slot size");
	r_anal_function_snapshot_free (malformed_return_mechanism);
	sdb_unset (anal->sdb_cc, "cc.exactcc.retmech", 0);
	RAnalFunctionSnapshot *missing_return_mechanism =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (missing_return_mechanism, "collect missing return mechanism");
	mu_assert_false (missing_return_mechanism->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM,
		"missing return mechanism carries no authority");
	r_anal_function_snapshot_free (missing_return_mechanism);
	sdb_set (anal->sdb_cc, "cc.exactcc.retmech", "stack:0:8:8", 0);
	RAnalVar *return_slot_overlap = r_anal_function_set_var (
		fcn, 0, R_ANAL_VAR_KIND_SPV, "int32_t", 4, false, "return_slot_overlap");
	mu_assert_notnull (return_slot_overlap, "create SP local overlapping the return slot");
	RAnalFunctionSnapshot *overlapping_return_mechanism =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (overlapping_return_mechanism, "collect overlapping return slot");
	mu_assert_true (overlapping_return_mechanism->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"overlap refusal does not erase the independently exact interface");
	mu_assert_false (overlapping_return_mechanism->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM,
		"declared SP local overlapping the return slot carries no mechanism authority");
	r_anal_function_snapshot_free (overlapping_return_mechanism);
	mu_assert_true (r_anal_var_delete (anal, return_slot_overlap),
		"remove the overlapping return-slot local");
	ut64 stack_pointer_revision = snapshot->revision_identity;
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "sp"),
		"point SP role at a narrow register");
	RAnalFunctionSnapshot *narrow_stack_pointer =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (narrow_stack_pointer, "collect narrow stack-pointer snapshot");
	mu_assert_false (narrow_stack_pointer->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"narrow SP register cannot carry stack-pointer authority");
	mu_assert_false (narrow_stack_pointer->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"narrow SP register cannot preserve exact interface authority");
	mu_assert_neq (narrow_stack_pointer->revision_identity, stack_pointer_revision,
		"stack-pointer carrier changes snapshot revision identity");
	r_anal_function_snapshot_free (narrow_stack_pointer);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "not_a_register"),
		"make the typed SP role unresolvable");
	RAnalFunctionSnapshot *missing_stack_pointer =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (missing_stack_pointer, "collect missing stack-pointer snapshot");
	mu_assert_false (missing_stack_pointer->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"no literal register-name fallback supplies stack-pointer authority");
	r_anal_function_snapshot_free (missing_stack_pointer);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "rdi"),
		"point SP role at the parameter register");
	RAnalFunctionSnapshot *stack_parameter_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (stack_parameter_collision, "collect SP-parameter collision snapshot");
	mu_assert_false (stack_parameter_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"parameter collision rejects stack-pointer authority");
	mu_assert_false (stack_parameter_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"parameter collision rejects exact interface authority");
	r_anal_function_snapshot_free (stack_parameter_collision);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "rax"),
		"point SP role at the return-value register");
	RAnalFunctionSnapshot *stack_return_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (stack_return_collision, "collect SP-return collision snapshot");
	mu_assert_false (stack_return_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"return-value collision rejects stack-pointer authority");
	mu_assert_false (stack_return_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"return-value collision rejects exact interface authority");
	r_anal_function_snapshot_free (stack_return_collision);
	free (home_source->regname);
	home_source->regname = strdup ("r12");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "r12"),
		"point SP role at a distinct parameter-home register");
	RAnalFunctionSnapshot *stack_home_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (stack_home_collision, "collect SP-home collision snapshot");
	mu_assert_false (stack_home_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"parameter-home collision rejects stack-pointer authority");
	mu_assert_false (stack_home_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"parameter-home collision rejects exact interface authority");
	r_anal_function_snapshot_free (stack_home_collision);
	free (home_source->regname);
	home_source->regname = strdup ("rdi");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "rip"),
		"point SP role at the return-address register");
	RAnalFunctionSnapshot *stack_return_address_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (stack_return_address_collision,
		"collect SP-return-address collision snapshot");
	mu_assert_false (stack_return_address_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"return-address collision rejects stack-pointer authority");
	mu_assert_false (stack_return_address_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"SP collision simultaneously clears return-address authority");
	r_anal_function_snapshot_free (stack_return_address_collision);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "rbp"),
		"point SP role at the BP stack-slot base");
	RAnalFunctionSnapshot *stack_bp_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (stack_bp_collision, "collect SP-BP collision snapshot");
	mu_assert_false (stack_bp_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"BP-base collision rejects stack-pointer authority");
	r_anal_function_snapshot_free (stack_bp_collision);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "rsp"),
		"restore typed SP role");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_PC, "edi"),
		"point PC role at a narrow register");
	RAnalFunctionSnapshot *narrow_return_address =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (narrow_return_address, "collect narrow return-address snapshot");
	mu_assert_false (narrow_return_address->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"narrow PC register cannot carry return-address authority");
	mu_assert_false (narrow_return_address->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"narrow PC register cannot preserve exact interface authority");
	r_anal_function_snapshot_free (narrow_return_address);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_PC, "rdi"),
		"point PC role at the parameter register");
	RAnalFunctionSnapshot *parameter_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (parameter_collision, "collect parameter-collision snapshot");
	mu_assert_false (parameter_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"parameter collision rejects return-address authority");
	mu_assert_false (parameter_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"parameter collision rejects exact interface authority");
	r_anal_function_snapshot_free (parameter_collision);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_PC, "rax"),
		"point PC role at the return register");
	RAnalFunctionSnapshot *return_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (return_collision, "collect return-collision snapshot");
	mu_assert_false (return_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"return-value collision rejects return-address authority");
	mu_assert_false (return_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"return-value collision rejects exact interface authority");
	r_anal_function_snapshot_free (return_collision);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_PC, "rbp"),
		"point PC role at the BP stack-slot base");
	RAnalFunctionSnapshot *bp_base_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (bp_base_collision, "collect BP-base-collision snapshot");
	mu_assert_false (bp_base_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"BP stack-slot base collision rejects return-address authority");
	mu_assert_null (bp_base_collision->function_interface.return_address_storage.name,
		"BP stack-slot base collision clears the carrier");
	mu_assert_false (bp_base_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"BP stack-slot base collision rejects exact interface authority");
	r_anal_function_snapshot_free (bp_base_collision);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_PC, "rsp"),
		"point PC role at the SP stack-slot base");
	RAnalFunctionSnapshot *sp_base_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (sp_base_collision, "collect SP-base-collision snapshot");
	mu_assert_false (sp_base_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"SP stack-slot base collision rejects return-address authority");
	mu_assert_null (sp_base_collision->function_interface.return_address_storage.name,
		"SP stack-slot base collision clears the carrier");
	mu_assert_false (sp_base_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"SP stack-slot base collision rejects exact interface authority");
	r_anal_function_snapshot_free (sp_base_collision);
	free (home_source->regname);
	home_source->regname = strdup ("r12");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_PC, "r12"),
		"point PC role at a distinct parameter-home register");
	RAnalFunctionSnapshot *home_collision =
		r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (home_collision, "collect parameter-home-collision snapshot");
	mu_assert_false (home_collision->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"distinct parameter-home collision rejects return-address authority");
	mu_assert_null (home_collision->function_interface.return_address_storage.name,
		"distinct parameter-home collision clears the carrier");
	r_anal_function_snapshot_free (home_collision);
	free (home_source->regname);
	home_source->regname = strdup ("rdi");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_PC, "rip"),
		"restore typed PC role");
	RAnalFcnSlot *bp_resource = find_stack_slot (&snapshot->context, "exact_bp_slot");
	RAnalFcnSlot *sp_resource = find_stack_slot (&snapshot->context, "exact_sp_slot");
	mu_assert_notnull (bp_resource, "snapshot owns exact BP resource");
	mu_assert_notnull (sp_resource, "snapshot owns exact SP resource");
	RAnalFunctionSnapshotView public_snapshot;
	mu_assert_true (r_anal_function_snapshot_view (snapshot, &public_snapshot),
		"open public exact snapshot view");
	mu_assert_eq (public_snapshot.num_stack_slots,
		(size_t)r_list_length (snapshot->context.fcn_slots),
		"public view reports every owned stack slot");
	bool saw_public_bp_slot = false;
	size_t slot_index;
	for (slot_index = 0; slot_index < public_snapshot.num_stack_slots; slot_index++) {
		RAnalSnapshotStackSlotView slot_view;
		char slot_name[64];
		char base_name[64];
		mu_assert_true (r_anal_function_snapshot_stack_slot_view (
			snapshot, slot_index, &slot_view), "copy public stack-slot view");
		mu_assert_true (r_anal_function_snapshot_stack_slot_string (
			snapshot, slot_index, R_ANAL_SNAPSHOT_STACK_SLOT_STRING_NAME,
			slot_name, sizeof (slot_name)), "copy public stack-slot name");
		mu_assert_true (r_anal_function_snapshot_stack_slot_string (
			snapshot, slot_index, R_ANAL_SNAPSHOT_STACK_SLOT_STRING_BASE_NAME,
			base_name, sizeof (base_name)), "copy public stack-slot base name");
		if (!strcmp (slot_name, "exact_bp_slot")) {
			saw_public_bp_slot = slot_view.base == R_ANAL_FCN_BASE_BP
				&& slot_view.base_offset == bp_resource->base_offset
				&& slot_view.base_size == bp_resource->base_size
				&& slot_view.offset == bp_resource->offset
				&& slot_view.size == bp_resource->size
				&& slot_view.offset_valid && slot_view.role == bp_resource->role
				&& slot_view.arg_index == bp_resource->arg_index
				&& slot_view.home_reg_offset == bp_resource->home_reg_offset
				&& slot_view.home_reg_size == bp_resource->home_reg_size
				&& !strcmp (base_name, "rbp");
		}
	}
	mu_assert_true (saw_public_bp_slot,
		"public stack-slot accessors preserve exact typed coordinates");
	RAnalSnapshotStackSlotView invalid_slot;
	mu_assert_false (r_anal_function_snapshot_stack_slot_view (
		snapshot, public_snapshot.num_stack_slots, &invalid_slot),
		"public stack-slot view rejects out-of-range index");
	mu_assert_eq (bp_resource->base, R_ANAL_FCN_BASE_BP, "exact BP resource base");
	mu_assert_streq (bp_resource->base_name, "rbp", "exact BP resource register");
	mu_assert_eq (bp_resource->base_size, 8, "exact BP resource register size");
	RRegItem *rbp_item = r_reg_get (anal->reg, "rbp", -1);
	mu_assert_notnull (rbp_item, "resolve exact BP slot base");
	mu_assert_eq (bp_resource->base_offset, (ut64)(rbp_item->offset / 8),
		"BP slot base uses canonical byte coordinates");
	r_unref (rbp_item);
	mu_assert_eq (bp_resource->offset, -8, "exact BP resource offset");
	mu_assert_eq (bp_resource->size, 4, "exact BP resource size");
	mu_assert_true (bp_resource->offset_valid, "exact BP resource offset is valid");
	mu_assert_eq (bp_resource->role, R_ANAL_FCN_SLOT_HOME,
		"exact BP resource is a parameter home");
	mu_assert_eq (bp_resource->arg_index, 0,
		"exact parameter home identifies its interface parameter");
	mu_assert_eq (bp_resource->home_reg_offset,
		snapshot->function_interface.parameters[0].storage.offset,
		"exact parameter home has canonical register offset");
	mu_assert_eq (bp_resource->home_reg_offset, (ut64)(rdi_item->offset / 8),
		"parameter home uses canonical byte coordinates");
	r_unref (rdi_item);
	mu_assert_eq (bp_resource->home_reg_size,
		snapshot->function_interface.parameters[0].storage.size,
		"exact parameter home has canonical register size");
	mu_assert_eq (sp_resource->role, R_ANAL_FCN_SLOT_LOCAL,
		"exact SP resource remains a local");
	mu_assert_eq (sp_resource->arg_index, -1,
		"local stack resource carries no parameter authority");
	RRegItem *rsp_item = r_reg_get (anal->reg, "rsp", -1);
	mu_assert_notnull (rsp_item, "resolve exact SP slot base");
	mu_assert_eq (sp_resource->base_offset, (ut64)(rsp_item->offset / 8),
		"SP slot base uses canonical byte coordinates");
	r_unref (rsp_item);
	mu_assert_true (snapshot->function_interface.stack_resources_complete,
		"different exact bases may use the same relative range");
	ut64 exact_revision = snapshot->revision_identity;
	free (home_source->regname);
	home_source->regname = strdup ("edi");
	RAnalFunctionSnapshot *mismatched_home = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (mismatched_home, "collect mismatched parameter-home snapshot");
	mu_assert_false (mismatched_home->function_interface.stack_slot_roles_complete,
		"subregister storage cannot prove a full-register parameter home");
	mu_assert_false (mismatched_home->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES,
		"mismatched home storage omits exact-role capability");
	mu_assert_neq (mismatched_home->revision_identity, exact_revision,
		"canonical home payload changes snapshot revision identity");
	r_anal_function_snapshot_free (mismatched_home);
	free (home_source->regname);
	home_source->regname = strdup ("rdi");
	r_anal_var_set_type (anal, bp_slot, "int64_t");
	mu_assert_eq (bp_resource->size, 4, "owned snapshot resource remains immutable after live type mutation");
	RAnalFunctionSnapshot *resized = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (resized, "collect resized exact resource snapshot");
	RAnalFcnSlot *resized_resource = find_stack_slot (&resized->context, "exact_bp_slot");
	mu_assert_notnull (resized_resource, "resized exact resource remains owned");
	mu_assert_eq (resized_resource->size, 8, "new snapshot observes exact resource size change");
	mu_assert_neq (resized->revision_identity, exact_revision, "exact resource mutation changes revision");
	r_anal_function_snapshot_free (resized);

	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_BP, "r14"),
		"use valid non-whitelisted full-width BP register");
	RAnalFunctionSnapshot *nonstandard_base = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (nonstandard_base, "collect non-whitelisted exact base snapshot");
	RAnalFcnSlot *nonstandard_resource = find_stack_slot (&nonstandard_base->context, "exact_bp_slot");
	mu_assert_notnull (nonstandard_resource, "non-whitelisted base resource remains exact");
	mu_assert_eq (nonstandard_resource->base, R_ANAL_FCN_BASE_BP,
		"semantic BP role is independent of register spelling");
	mu_assert_streq (nonstandard_resource->base_name, "r14",
		"snapshot transports the actual full-width base register");
	mu_assert_eq (nonstandard_resource->base_size, 8,
		"non-whitelisted base keeps its full register width");
	mu_assert_true (nonstandard_base->function_interface.stack_resources_complete,
		"valid non-whitelisted base preserves exact stack resources");
	r_anal_function_snapshot_free (nonstandard_base);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_BP, "rbp"),
		"restore typed BP role");
	mu_assert_true (r_anal_var_delete (anal, sp_slot),
		"remove the SP-relative slot for BP-only coverage");
	RAnalFunctionSnapshot *bp_only = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (bp_only, "collect BP-only exact snapshot");
	mu_assert_null (find_stack_slot (&bp_only->context, "exact_sp_slot"),
		"BP-only snapshot contains no SP-relative slot");
	mu_assert_true (bp_only->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"BP-only snapshot carries typed SP independently of slots");
	mu_assert_true (bp_only->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"BP-only frame preserves exact interface authority");
	mu_assert_false (bp_only->function_interface.noreturn,
		"control still comes back before the noreturn mutation");
	r_anal_function_snapshot_free (bp_only);
	r_anal_function_snapshot_free (snapshot);

	signature.noreturn = true;
	parameters = r_list_new ();
	mu_assert_notnull (parameters, "recreate exact parameter list");
	mu_assert_true (r_list_append (parameters, &parameter), "reappend exact parameter");
	signature.params = parameters;
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature), "apply noreturn signature");
	r_list_free (parameters);
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect noreturn snapshot");
	// noreturn says control does not come back, which is not a statement about
	// whether the parameter and return storage were recovered. It is recorded
	// as a fact of the interface, and it withholds nothing: the carriers below
	// were all resolved without reference to whether the function returns.
	mu_assert_true (snapshot->function_interface.noreturn,
		"the snapshot records that control does not come back");
	mu_assert_true (snapshot->function_interface.complete,
		"noreturn does not withhold the recovered interface");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"noreturn snapshot keeps exact interface capability");
	mu_assert_eq (snapshot->function_interface.num_parameters, 1,
		"noreturn snapshot keeps the parameter it recovered");
	mu_assert_streq (snapshot->function_interface.parameters[0].name, "value",
		"noreturn snapshot keeps the parameter name a consumer would show");
	mu_assert_streq (snapshot->function_interface.parameters[0].storage.name, "rdi",
		"noreturn snapshot keeps the parameter carrier");
	mu_assert_eq (snapshot->function_interface.return_kind,
		R_ANAL_SNAPSHOT_RETURN_REGISTER,
		"noreturn snapshot keeps the result carrier kind");
	rax_item = r_reg_get (anal->reg, "rax", -1);
	mu_assert_notnull (rax_item, "resolve noreturn result carrier");
	mu_assert_eq (snapshot->function_interface.return_storage.offset,
		(ut64)(rax_item->offset / 8),
		"noreturn snapshot keeps the canonical result carrier");
	r_unref (rax_item);
	mu_assert_neq (snapshot->revision_identity, exact_revision, "interface mutation changes revision");
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_prefers_link_register_return_address(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create ARM64 return-address snapshot analysis");
	mu_assert_true (r_anal_use (anal, "arm"), "load ARM analysis profile");
	r_anal_set_bits (anal, 64);
	RAnalFunction *fcn = r_anal_create_function (
		anal, "arm64_return_address_snapshot", 0x7100, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create ARM64 return-address snapshot function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back ARM64 snapshot with exact bytes");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_RA, "x29"),
		"seed typed RA fallback distinct from LR and PC");

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect ARM64 return-address snapshot");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"ARM64 snapshot carries the typed return-address register");
	mu_assert_streq (snapshot->function_interface.return_address_storage.name, "x30",
		"typed LR alias wins over the PC alias");
	mu_assert_eq (snapshot->function_interface.return_address_storage.size, 8,
		"ARM64 link-register carrier is full width");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"ARM64 snapshot carries SP independently of stack slots");
	mu_assert_streq (snapshot->function_interface.stack_pointer_storage.name, "sp",
		"ARM64 typed SP role is carried without slot inference");
	mu_assert_eq (snapshot->function_interface.stack_pointer_storage.size, 8,
		"ARM64 stack-pointer carrier is full width");
	mu_assert_false (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM,
		"ARM64 profile without an exact mechanism carries no return authority");
	RAnalSnapshotReturnMechanismView return_mechanism;
	mu_assert_false (r_anal_function_snapshot_interface_return_mechanism (
		snapshot, &return_mechanism), "ARM64 absent mechanism is not exposed");
	r_anal_function_snapshot_free (snapshot);

	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "wsp"),
		"make ARM64 SP role narrower than the function address");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect narrow ARM64 stack-pointer snapshot");
	mu_assert_false (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"narrow ARM64 SP cannot carry stack-pointer authority");
	r_anal_function_snapshot_free (snapshot);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, ""),
		"clear typed ARM64 SP alias");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect ARM64 snapshot without SP alias");
	mu_assert_false (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE,
		"literal SP name cannot replace missing typed role authority");
	r_anal_function_snapshot_free (snapshot);
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_SP, "sp"),
		"restore typed ARM64 SP role");

	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_LR, "not_a_register"),
		"make higher-priority LR alias unresolvable");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect RA fallback snapshot");
	mu_assert_true (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"usable RA fallback carries return-address authority");
	mu_assert_streq (snapshot->function_interface.return_address_storage.name, "x29",
		"typed RA alias follows an unusable LR alias");
	r_anal_function_snapshot_free (snapshot);

	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_LR, "w30"),
		"make higher-priority LR alias narrower than the function address");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect RA fallback from narrow LR snapshot");
	mu_assert_true (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"full-width RA fallback carries return-address authority");
	mu_assert_streq (snapshot->function_interface.return_address_storage.name, "x29",
		"full-width RA alias follows a narrow LR alias");
	r_anal_function_snapshot_free (snapshot);

	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_LR, ""),
		"clear typed LR alias");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_RA, "not_a_register"),
		"make higher-priority RA alias unresolvable");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect PC fallback snapshot");
	mu_assert_true (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"usable PC fallback carries return-address authority");
	mu_assert_streq (snapshot->function_interface.return_address_storage.name, "pc",
		"typed PC alias follows unusable LR and RA aliases");
	r_anal_function_snapshot_free (snapshot);

	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_PC, ""),
		"clear final typed PC alias");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect snapshot without a usable typed alias");
	mu_assert_false (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE,
		"no literal name fallback supplies return-address authority");
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_falls_back_from_unusable_linked_cc(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create calling-convention fallback analysis");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	mu_assert_true (r_anal_cc_set (anal, "rax amd64(rdi,rsi,rdx,rcx,r8,r9)"),
		"seed live target calling convention");
	mu_assert_true (r_anal_cc_set (anal, "rax cdecl(stack)"),
		"seed stack-only linked calling convention");
	mu_assert_true (r_anal_cc_set (anal, "rax usablecc(rdx)"),
		"seed usable conflicting calling convention");
	sdb_set (anal->sdb_cc, "cc.amd64.retmech", "stack:0:8:8", 0);
	sdb_set (anal->sdb_cc, "cc.cdecl.retmech", "stack:8:8:16", 0);

	sdb_set (anal->sdb_types, "linked_cdecl", "func", 0);
	sdb_set (anal->sdb_types, "func.linked_cdecl.ret", "int32_t", 0);
	sdb_set (anal->sdb_types, "func.linked_cdecl.args", "1", 0);
	sdb_set (anal->sdb_types, "func.linked_cdecl.arg.0", "int32_t,x", 0);
	sdb_set (anal->sdb_types, "func.linked_cdecl", "x", 0);
	sdb_set (anal->sdb_types, "func.linked_cdecl.cc", "cdecl", 0);
	RAnalFunction *fallback = r_anal_create_function (
		anal, "fallback_snapshot", 0x7200, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fallback, "create linked-CC fallback function");
	mu_assert_true (snapshot_test_ensure_block (anal, fallback, 1),
		"back fallback snapshot with exact bytes");
	fallback->callconv = r_str_constpool_get (&anal->constpool, "amd64");
	mu_assert_true (set_function_type_link (anal, "linked_cdecl", fallback->addr),
		"link stack-CC type by address");
	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fallback, NULL);
	mu_assert_notnull (snapshot, "collect linked-CC fallback snapshot");
	mu_assert_true (snapshot->function_interface.complete,
		"live register CC completes an unusable linked stack interface");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"fallback snapshot certifies its exact interface");
	mu_assert_streq (snapshot->function_interface.calling_convention, "amd64",
		"physical carriers use the usable live target CC");
	RAnalSnapshotReturnMechanismView return_mechanism;
	mu_assert_true (r_anal_function_snapshot_interface_return_mechanism (
		snapshot, &return_mechanism), "fallback exposes selected live CC mechanism");
	mu_assert_eq (return_mechanism.entry_sp_offset, 0,
		"fallback mechanism comes from selected amd64 CC");
	mu_assert_eq (return_mechanism.exit_sp_delta, 8,
		"fallback ignores the unusable linked CC mechanism");
	mu_assert_eq (snapshot->function_interface.num_parameters, 1,
		"linked logical signature retains one parameter");
	mu_assert_streq (snapshot->function_interface.parameters[0].storage.name, "rdi",
		"live target CC supplies the parameter carrier");
	mu_assert_eq (snapshot->function_interface.parameters[0].carrier.kind,
		R_ANAL_SNAPSHOT_CARRIER_LOW_BITS, "linked int parameter retains its logical width");
	mu_assert_eq (snapshot->function_interface.parameters[0].carrier.size_bits, 32,
		"linked int parameter projects to 32 carrier bits");
	mu_assert_eq (snapshot->function_interface.return_kind,
		R_ANAL_SNAPSHOT_RETURN_REGISTER, "live target CC supplies a register return");
	RRegItem *rax = r_reg_get (anal->reg, "rax", -1);
	mu_assert_notnull (rax, "resolve live target return carrier");
	mu_assert_eq (snapshot->function_interface.return_storage.offset,
		(ut64)(rax->offset / 8),
		"live target CC supplies the canonical return carrier");
	r_unref (rax);
	mu_assert_eq (snapshot->function_interface.return_carrier.kind,
		R_ANAL_SNAPSHOT_CARRIER_LOW_BITS, "linked int return retains its logical width");
	mu_assert_eq (snapshot->function_interface.return_carrier.size_bits, 32,
		"linked int return projects to 32 carrier bits");
	r_anal_function_snapshot_free (snapshot);

	sdb_set (anal->sdb_types, "linked_usable", "func", 0);
	sdb_set (anal->sdb_types, "func.linked_usable.ret", "int64_t", 0);
	sdb_set (anal->sdb_types, "func.linked_usable.args", "1", 0);
	sdb_set (anal->sdb_types, "func.linked_usable.arg.0", "int64_t,x", 0);
	sdb_set (anal->sdb_types, "func.linked_usable", "x", 0);
	sdb_set (anal->sdb_types, "func.linked_usable.cc", "usablecc", 0);
	RAnalFunction *preserved = r_anal_create_function (
		anal, "preserved_snapshot", 0x7210, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (preserved, "create usable linked-CC function");
	mu_assert_true (snapshot_test_ensure_block (anal, preserved, 1),
		"back preserved snapshot with exact bytes");
	preserved->callconv = r_str_constpool_get (&anal->constpool, "amd64");
	mu_assert_true (set_function_type_link (anal, "linked_usable", preserved->addr),
		"link usable-CC type by address");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, preserved, NULL);
	mu_assert_notnull (snapshot, "collect usable linked-CC snapshot");
	mu_assert_true (snapshot->function_interface.complete,
		"usable linked calling convention remains exact");
	mu_assert_streq (snapshot->function_interface.calling_convention, "usablecc",
		"usable linked calling convention is not overridden");
	mu_assert_streq (snapshot->function_interface.parameters[0].storage.name, "rdx",
		"usable linked calling convention retains its parameter carrier");
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_seals_exact_reachable_type_graph(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create exact type-graph analysis");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	r_anal_types_ensure_loaded (anal);
	sdb_reset (anal->sdb_types);
	mu_assert_true (r_anal_cc_set (anal, "rax exacttypes(rdi,rsi,rdx)"),
		"seed exact type-graph calling convention");
	RAnalBaseType *integer = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_ATOMIC);
	integer->name = strdup ("int32_t");
	integer->type = strdup ("d");
	integer->size = 32;
	r_anal_save_base_type (anal, integer);
	r_anal_base_type_free (integer);
	mu_assert_true (save_snapshot_demo_struct_type (anal, 52, 0),
		"seed exact DemoStruct layout");

	RAnalFunction *fcn = r_anal_create_function (
		anal, "typed_graph_snapshot", 0x7800, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create exact type-graph function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back type-graph snapshot with exact bytes");
	RAnalFunctionParam parameters_data[] = {
		{ .name = "arr", .type = "DemoStruct *" },
		{ .name = "idx", .type = "int32_t" },
		{ .name = "v", .type = "int32_t" },
	};
	RList *parameters = r_list_new ();
	mu_assert_notnull (parameters, "create exact type-graph parameter list");
	size_t i;
	for (i = 0; i < R_ARRAY_SIZE (parameters_data); i++) {
		mu_assert_true (r_list_append (parameters, &parameters_data[i]),
			"append exact type-graph parameter");
	}
	RAnalFunctionSignature signature = {
		.ret_type = "int32_t",
		.callconv = "exacttypes",
		.params = parameters,
	};
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature),
		"apply exact type-graph signature");
	mu_assert_true (set_function_type_link (anal, fcn->name, fcn->addr),
		"link exact type-graph signature by address");

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect exact reachable type graph");
	mu_assert_eq (snapshot->schema_version, R_ANAL_FUNCTION_SNAPSHOT_SCHEMA_VERSION,
		"exact graph uses the current snapshot schema");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"exact function-types capability is present");
	mu_assert_true (snapshot->type_graph.complete, "reachable type graph is complete");
	mu_assert_true (snapshot->function_interface.logical_types_complete,
		"parameter and return logical types are complete");
	mu_assert_eq (snapshot->type_graph.num_types, 3,
		"reachable graph contains one struct, scalar, and pointer node");
	mu_assert_eq (snapshot->type_graph.num_aggregates, 1,
		"reachable graph contains one aggregate layout");
	RAnalSnapshotParameter *arr = &snapshot->function_interface.parameters[0];
	RAnalSnapshotParameter *idx = &snapshot->function_interface.parameters[1];
	RAnalSnapshotParameter *value = &snapshot->function_interface.parameters[2];
	mu_assert ("array pointer logical type id is valid",
		arr->logical_type_id < snapshot->type_graph.num_types);
	mu_assert ("index logical type id is valid",
		idx->logical_type_id < snapshot->type_graph.num_types);
	mu_assert_eq (idx->logical_type_id, value->logical_type_id,
		"equal-width signed parameters share structural scalar identity");
	mu_assert_eq (idx->logical_type_id, snapshot->function_interface.return_type_id,
		"return shares the signed int32 logical identity");
	const RAnalSnapshotType *pointer =
		&snapshot->type_graph.types[arr->logical_type_id];
	const RAnalSnapshotType *scalar =
		&snapshot->type_graph.types[idx->logical_type_id];
	mu_assert_eq (pointer->kind, R_ANAL_SNAPSHOT_TYPE_POINTER,
		"array parameter is an exact pointer node");
	mu_assert_eq (pointer->size_bits, 64, "pointer width is sealed");
	mu_assert ("pointer target id is valid",
		pointer->target_type_id < snapshot->type_graph.num_types);
	const RAnalSnapshotType *structure =
		&snapshot->type_graph.types[pointer->target_type_id];
	mu_assert_eq (structure->kind, R_ANAL_SNAPSHOT_TYPE_STRUCT,
		"pointer target is an exact struct node");
	mu_assert_eq (structure->size_bits, 56 * 8, "DemoStruct stride is 56 bytes");
	mu_assert_eq (structure->align_bits, 32, "DemoStruct alignment is four bytes");
	mu_assert_eq (scalar->kind, R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER,
		"member/index/value/return scalar is signed");
	mu_assert_eq (scalar->size_bits, 32, "logical integer width is 32 bits");
	mu_assert ("structure aggregate id is valid",
		structure->aggregate_id < snapshot->type_graph.num_aggregates);
	const RAnalSnapshotAggregateLayout *layout =
		&snapshot->type_graph.aggregates[structure->aggregate_id];
	mu_assert_true (layout->complete, "DemoStruct layout is complete");
	mu_assert_streq (layout->name, "DemoStruct", "aggregate label is preserved");
	mu_assert_eq (layout->num_members, 14, "all DemoStruct members are reachable");
	mu_assert_eq (layout->members[2].member_id, 2, "third field ordinal is exact");
	mu_assert_streq (layout->members[2].name, "third", "third field label is preserved");
	mu_assert_eq (layout->members[2].offset_bits, 8 * 8, "third field offset is eight bytes");
	mu_assert_eq (layout->members[13].member_id, 13, "fourteenth field ordinal is exact");
	mu_assert_streq (layout->members[13].name, "fourteenth",
		"fourteenth field label is preserved");
	mu_assert_eq (layout->members[13].offset_bits, 52 * 8,
		"fourteenth field offset is 52 bytes");
	mu_assert_eq (arr->carrier.kind, R_ANAL_SNAPSHOT_CARRIER_FULL,
		"pointer consumes its full 64-bit ABI carrier");
	mu_assert_eq (arr->carrier.size_bits, 64, "pointer carrier projection is 64 bits");
	mu_assert_eq (idx->carrier.kind, R_ANAL_SNAPSHOT_CARRIER_LOW_BITS,
		"signed int32 parameter occupies the low carrier slice");
	mu_assert_eq (idx->carrier.offset_bits, 0, "integer carrier slice begins at bit zero");
	mu_assert_eq (idx->carrier.size_bits, 32, "integer carrier slice is 32 bits");
	mu_assert_eq (snapshot->function_interface.return_carrier.kind,
		R_ANAL_SNAPSHOT_CARRIER_LOW_BITS, "signed int32 return occupies the low carrier slice");
	mu_assert_eq (snapshot->function_interface.return_carrier.size_bits, 32,
		"return carrier slice is 32 bits");

	mu_assert_true (save_snapshot_demo_struct_type (anal, 52, 2),
		"replace DemoStruct with an array member");
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature),
		"refresh signature after array-layout mutation");
	RAnalFunctionSnapshot *rejected = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (rejected, "legacy snapshot survives unsupported array layout");
	mu_assert_false (rejected->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"array layout is not certified by the closed exact subset");
	mu_assert_false (rejected->type_graph.complete, "rejected graph is not partially exposed");
	mu_assert_eq (rejected->function_interface.parameters[0].logical_type_id,
		R_ANAL_SNAPSHOT_TYPE_ID_INVALID, "rejected graph clears parameter logical refs");
	mu_assert_eq (rejected->function_interface.return_type_id,
		R_ANAL_SNAPSHOT_TYPE_ID_INVALID, "rejected graph clears return logical ref");
	mu_assert_true (snapshot->type_graph.complete,
		"previous exact graph remains immutable after live type mutation");
	mu_assert_eq (layout->members[13].size_bits, 32,
		"previous exact aggregate retains its owned non-array member width");
	r_anal_function_snapshot_free (rejected);

	mu_assert_true (save_snapshot_demo_struct_type (anal, 48, 0),
		"replace DemoStruct with an overlapping member");
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature),
		"refresh signature after overlap mutation");
	rejected = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (rejected, "legacy snapshot survives overlapping layout");
	mu_assert_false (rejected->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"overlapping layout is not certified");
	r_anal_function_snapshot_free (rejected);

	mu_assert_true (save_snapshot_demo_struct_type (anal, 52, 0),
		"restore exact DemoStruct layout");
	RAnalBaseType *alias = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_TYPEDEF);
	alias->name = strdup ("DemoStruct");
	alias->type = strdup ("struct DemoStruct");
	r_anal_save_base_type (anal, alias);
	r_anal_base_type_free (alias);
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature),
		"refresh signature after ambiguous alias mutation");
	rejected = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (rejected, "legacy snapshot survives ambiguous bare type");
	mu_assert_false (rejected->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"same bare name in tag and typedef namespaces fails closed");
	r_anal_function_snapshot_free (rejected);

	r_anal_function_snapshot_free (snapshot);
	r_list_free (parameters);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_seals_exact_scalar_pointer_graph(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create exact scalar-pointer analysis");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	sdb_reset (anal->sdb_types);
	mu_assert_true (r_anal_cc_set (anal, "rax exactscalarptr(rdi,rsi)"),
		"seed exact scalar-pointer calling convention");

	RAnalFunction *fcn = r_anal_create_function (
		anal, "typed_scalar_pointer_snapshot", 0x7900, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create exact scalar-pointer function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back scalar-pointer snapshot with exact bytes");
	RAnalFunctionParam parameters_data[] = {
		{ .name = "bytes", .type = "uint8_t *" },
		{ .name = "length", .type = "uint64_t" },
	};
	RList *parameters = r_list_new ();
	mu_assert_notnull (parameters, "create exact scalar-pointer parameter list");
	size_t i;
	for (i = 0; i < R_ARRAY_SIZE (parameters_data); i++) {
		mu_assert_true (r_list_append (parameters, &parameters_data[i]),
			"append exact scalar-pointer parameter");
	}
	RAnalFunctionSignature signature = {
		.ret_type = "uint64_t",
		.callconv = "exactscalarptr",
		.params = parameters,
	};
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature),
		"apply exact scalar-pointer signature");
	mu_assert_true (set_function_type_link (anal, fcn->name, fcn->addr),
		"link exact scalar-pointer signature by address");
	r_list_free (parameters);

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect exact scalar-pointer type graph");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"exact scalar-pointer function-types capability is present");
	mu_assert_true (snapshot->type_graph.complete,
		"exact scalar-pointer graph is complete");
	mu_assert_true (snapshot->function_interface.logical_types_complete,
		"scalar-pointer logical values are complete");
	mu_assert_eq (snapshot->type_graph.num_types, 3,
		"reachable graph contains byte, byte pointer, and uint64 nodes");
	mu_assert_eq (snapshot->type_graph.num_aggregates, 0,
		"scalar pointee does not invent an aggregate");

	const RAnalSnapshotParameter *bytes =
		&snapshot->function_interface.parameters[0];
	const RAnalSnapshotParameter *length =
		&snapshot->function_interface.parameters[1];
	mu_assert ("scalar pointer logical type id is valid",
		bytes->logical_type_id < snapshot->type_graph.num_types);
	const RAnalSnapshotType *pointer =
		&snapshot->type_graph.types[bytes->logical_type_id];
	mu_assert_eq (pointer->kind, R_ANAL_SNAPSHOT_TYPE_POINTER,
		"byte parameter is an exact pointer node");
	mu_assert_eq (pointer->size_bits, 64, "byte pointer width is sealed");
	mu_assert ("scalar pointer target id is valid",
		pointer->target_type_id < snapshot->type_graph.num_types);
	const RAnalSnapshotType *pointee =
		&snapshot->type_graph.types[pointer->target_type_id];
	mu_assert_eq (pointee->kind, R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER,
		"byte pointer target is an exact unsigned scalar");
	mu_assert_eq (pointee->size_bits, 8, "byte pointee width is exact");
	mu_assert_eq (pointee->align_bits, 8, "byte pointee alignment is exact");
	mu_assert_eq (length->logical_type_id,
		snapshot->function_interface.return_type_id,
		"length and return share the uint64 logical node");
	const RAnalSnapshotType *word =
		&snapshot->type_graph.types[length->logical_type_id];
	mu_assert_eq (word->kind, R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER,
		"length and return remain unsigned");
	mu_assert_eq (word->size_bits, 64, "length and return width is exact");
	mu_assert_eq (bytes->carrier.kind, R_ANAL_SNAPSHOT_CARRIER_FULL,
		"byte pointer consumes its full ABI carrier");
	mu_assert_eq (length->carrier.kind, R_ANAL_SNAPSHOT_CARRIER_FULL,
		"uint64 length consumes its full ABI carrier");
	mu_assert_eq (snapshot->function_interface.return_carrier.kind,
		R_ANAL_SNAPSHOT_CARRIER_FULL,
		"uint64 return consumes its full ABI carrier");

	ut64 revision = snapshot->revision_identity;
	parameters = r_list_new ();
	mu_assert_notnull (parameters, "recreate scalar-pointer parameter list");
	parameters_data[0].type = "uint16_t *";
	for (i = 0; i < R_ARRAY_SIZE (parameters_data); i++) {
		mu_assert_true (r_list_append (parameters, &parameters_data[i]),
			"reappend mutated scalar-pointer parameter");
	}
	signature.params = parameters;
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature),
		"apply mutated scalar-pointer signature");
	r_list_free (parameters);
	RAnalFunctionSnapshot *mutated = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (mutated, "collect mutated scalar-pointer graph");
	mu_assert_true (mutated->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"supported scalar-pointee mutation stays exact");
	mu_assert_neq (mutated->revision_identity, revision,
		"scalar-pointee mutation changes snapshot revision");
	const RAnalSnapshotType *mutated_pointer = &mutated->type_graph.types[
		mutated->function_interface.parameters[0].logical_type_id];
	const RAnalSnapshotType *mutated_pointee =
		&mutated->type_graph.types[mutated_pointer->target_type_id];
	mu_assert_eq (mutated_pointee->size_bits, 16,
		"new snapshot owns the mutated scalar-pointee width");
	mu_assert_eq (pointee->size_bits, 8,
		"previous snapshot retains its owned byte-pointee width");

	r_anal_function_snapshot_free (mutated);
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_resolves_lp64_integer_typedefs(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create LP64 typedef analysis");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	sdb_reset (anal->sdb_types);
	mu_assert_true (save_snapshot_atomic_type (anal, "uint64_t", "q", 64),
		"seed stale built-in uint64 atomic");
	mu_assert_true (save_snapshot_atomic_type (anal, "uint32_t", "d", 32),
		"seed stale built-in uint32 atomic");
	mu_assert_true (save_snapshot_typedef_type (anal, "uint64_t", "unsigned long long"),
		"seed DWARF-style uint64 typedef");
	mu_assert_true (save_snapshot_typedef_type (anal, "uint32_t", "unsigned int"),
		"seed DWARF-style uint32 typedef");
	sdb_set (anal->sdb_types, "unsigned_long_long", "type", 0);
	sdb_num_set (anal->sdb_types, "type.unsigned_long_long.size", 64, 0);
	sdb_set (anal->sdb_types, "unsigned_int", "type", 0);
	sdb_num_set (anal->sdb_types, "type.unsigned_int.size", 32, 0);
	r_anal_types_bump_dirty_epoch (anal);
	mu_assert_true (r_anal_cc_set (anal, "rax lp64types(rdi,rsi)"),
		"seed LP64 typedef calling convention");

	RAnalFunction *fcn = r_anal_create_function (
		anal, "lp64_typedef_snapshot", 0x7a00, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create LP64 typedef function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back LP64 typedef snapshot with exact bytes");
	sdb_set (anal->sdb_types, fcn->name, "func", 0);
	sdb_setf (anal->sdb_types, "uint64_t", 0, "func.%s.ret", fcn->name);
	sdb_setf (anal->sdb_types, "2", 0, "func.%s.args", fcn->name);
	sdb_setf (anal->sdb_types, "uint64_t,wide", 0, "func.%s.arg.0", fcn->name);
	sdb_setf (anal->sdb_types, "uint32_t,narrow", 0, "func.%s.arg.1", fcn->name);
	sdb_setf (anal->sdb_types, "wide,narrow", 0, "func.%s", fcn->name);
	sdb_setf (anal->sdb_types, "lp64types", 0, "func.%s.cc", fcn->name);
	r_anal_types_bump_dirty_epoch (anal);
	mu_assert_true (set_function_type_link (anal, fcn->name, fcn->addr),
		"link LP64 typedef signature by address");

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect LP64 typedef type graph");
	mu_assert_true (snapshot->function_interface.complete,
		"LP64 typedef physical interface is complete");
	mu_assert_notnull (snapshot->context.signature, "LP64 typedef signature is present");
	mu_assert_streq (snapshot->context.signature->ret_type, "uint64_t",
		"LP64 typedef return spelling is preserved");
	RAnalSnapshotCodePointerTableView table_view = {0};
	mu_assert_false (r_anal_function_snapshot_code_pointer_table_view (snapshot, 0, &table_view),
		"a function referencing no pointer table carries none");
	ut64 table_target = 0;
	mu_assert_false (r_anal_function_snapshot_code_pointer_table_target (snapshot, 0, 0, &table_target),
		"a table that was not collected hands out no target");
	RAnalFunctionSnapshotView callee_top = {0};
	mu_assert_true (r_anal_function_snapshot_view (snapshot, &callee_top),
		"read the top view for the callee snapshot count");
	mu_assert_eq (callee_top.num_callee_snapshots, 0,
		"a function that calls nothing carries no callee snapshot");
	mu_assert_null (r_anal_function_snapshot_callee_snapshot (snapshot, 0),
		"a callee snapshot that was not taken is not handed out");
	RAnalSnapshotSignatureView signature_view = {0};
	mu_assert_true (r_anal_function_snapshot_signature_view (snapshot, &signature_view),
		"the recovered signature is offered to a reader");
	mu_assert_eq (signature_view.num_parameters, 2,
		"the offered signature keeps both parameters");
	char spelling[64];
	mu_assert_true (r_anal_function_snapshot_signature_string (snapshot,
		R_ANAL_SNAPSHOT_SIGNATURE_STRING_RETURN_TYPE, 0, spelling, sizeof (spelling)),
		"the return spelling is readable");
	mu_assert_streq (spelling, "uint64_t", "the return spelling is the source's");
	mu_assert_true (r_anal_function_snapshot_signature_string (snapshot,
		R_ANAL_SNAPSHOT_SIGNATURE_STRING_PARAMETER_TYPE, 1, spelling, sizeof (spelling)),
		"the second parameter spelling is readable");
	mu_assert_streq (spelling, "uint32_t", "the parameter spelling is the source's");
	mu_assert_true (r_anal_function_snapshot_signature_string (snapshot,
		R_ANAL_SNAPSHOT_SIGNATURE_STRING_PARAMETER_NAME, 1, spelling, sizeof (spelling)),
		"the second parameter name is readable");
	mu_assert_streq (spelling, "narrow", "the parameter name is the source's");
	mu_assert_false (r_anal_function_snapshot_signature_string (snapshot,
		R_ANAL_SNAPSHOT_SIGNATURE_STRING_PARAMETER_TYPE, 2, spelling, sizeof (spelling)),
		"a parameter the signature does not have is refused");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"LP64 typedef graph carries exact type authority");
	mu_assert_true (snapshot->function_interface.logical_types_complete,
		"LP64 typedef logical values are complete");
	const RAnalSnapshotParameter *wide = &snapshot->function_interface.parameters[0];
	const RAnalSnapshotParameter *narrow = &snapshot->function_interface.parameters[1];
	mu_assert ("LP64 typedef type id is valid",
		wide->logical_type_id < snapshot->type_graph.num_types);
	mu_assert ("uint32 type id is valid",
		narrow->logical_type_id < snapshot->type_graph.num_types);
	const RAnalSnapshotType *wide_type =
		&snapshot->type_graph.types[wide->logical_type_id];
	const RAnalSnapshotType *narrow_type =
		&snapshot->type_graph.types[narrow->logical_type_id];
	mu_assert_eq (wide_type->kind, R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER,
		"LP64 typedef preserves unsignedness");
	mu_assert_eq (wide_type->size_bits, 64,
		"LP64 typedef width comes from its sized DWARF terminal");
	mu_assert_eq (narrow_type->kind, R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER,
		"uint32 interface preserves unsignedness");
	mu_assert_eq (narrow_type->size_bits, 32,
		"uint32 width comes from authoritative type state");
	mu_assert_eq (wide->logical_type_id, snapshot->function_interface.return_type_id,
		"LP64 parameter and return share structural identity");
	mu_assert_eq (wide->carrier.kind, R_ANAL_SNAPSHOT_CARRIER_FULL,
		"LP64 typedef consumes its full carrier");
	mu_assert_eq (wide->carrier.size_bits, 64,
		"LP64 typedef carrier projection is 64 bits");
	mu_assert_eq (narrow->carrier.kind, R_ANAL_SNAPSHOT_CARRIER_LOW_BITS,
		"uint32 projects into the low carrier bits");
	mu_assert_eq (narrow->carrier.size_bits, 32,
		"uint32 carrier projection is 32 bits");
	mu_assert_notnull (find_snapshot_base_type_kind (snapshot, "uint64_t",
		R_ANAL_BASE_TYPE_KIND_TYPEDEF), "snapshot owns the current uint64 typedef root");
	mu_assert_null (find_snapshot_base_type_kind (snapshot, "uint64_t",
		R_ANAL_BASE_TYPE_KIND_ATOMIC), "snapshot excludes the stale same-name atomic root");
	RAnalBaseType *owned_terminal = find_snapshot_base_type_kind (
		snapshot, "unsigned_long_long", R_ANAL_BASE_TYPE_KIND_ATOMIC);
	mu_assert_notnull (owned_terminal, "snapshot owns the encoding-less DWARF terminal");
	mu_assert_null (owned_terminal->type,
		"encoding-less terminal stays distinct from an encoded atomic");
	mu_assert_eq (owned_terminal->size, 64,
		"snapshot owns the terminal width used by the logical graph");
	const ut64 revision = snapshot->revision_identity;
	sdb_num_set (anal->sdb_types, "type.unsigned_long_long.size", 32, 0);
	mu_assert_eq (owned_terminal->size, 64,
		"raw type database mutation cannot alter captured resolver state");
	RAnalFunctionSnapshot *raw_mutated = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (raw_mutated, "collect snapshot after raw resolver mutation");
	mu_assert_false (raw_mutated->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"new snapshot observes a raw mismatched terminal mutation");
	mu_assert_neq (raw_mutated->revision_identity, revision,
		"owned resolver metadata participates in snapshot revision");
	r_anal_function_snapshot_free (raw_mutated);
	sdb_num_set (anal->sdb_types, "type.unsigned_long_long.size", 64, 0);
	sdb_set (anal->sdb_types, "uint64_t", "type", 0);
	RAnalFunctionSnapshot *raw_root_mutated = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (raw_root_mutated, "collect snapshot after raw root-kind mutation");
	mu_assert_true (raw_root_mutated->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"current same-width atomic root remains exact");
	mu_assert_notnull (find_snapshot_base_type_kind (raw_root_mutated, "uint64_t",
		R_ANAL_BASE_TYPE_KIND_ATOMIC), "new snapshot owns the current atomic root");
	mu_assert_null (find_snapshot_base_type_kind (raw_root_mutated, "uint64_t",
		R_ANAL_BASE_TYPE_KIND_TYPEDEF), "new snapshot excludes the stale typedef root");
	mu_assert_neq (raw_root_mutated->revision_identity, revision,
		"current root-kind selection participates in snapshot revision");
	r_anal_function_snapshot_free (raw_root_mutated);
	sdb_set (anal->sdb_types, "uint64_t", "typedef", 0);
	r_anal_function_snapshot_free (snapshot);

	sdb_num_set (anal->sdb_types, "type.unsigned_long_long.size", 32, 0);
	r_anal_types_bump_dirty_epoch (anal);
	RAnalFunctionSnapshot *rejected = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (rejected, "collect mismatched typedef snapshot");
	mu_assert_false (rejected->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"fixed-width typedef rejects mismatched terminal width");
	mu_assert_false (rejected->function_interface.logical_types_complete,
		"mismatched typedef exposes no partial logical graph");
	r_anal_function_snapshot_free (rejected);

	sdb_num_set (anal->sdb_types, "type.unsigned_long_long.size", 64, 0);
	r_anal_types_bump_dirty_epoch (anal);
	RAnalBaseType *collision = r_anal_base_type_new (R_ANAL_BASE_TYPE_KIND_STRUCT);
	mu_assert_notnull (collision, "create conflicting uint64 tag");
	collision->name = strdup ("uint64_t");
	collision->size = 32;
	RAnalStructMember member = {
		.name = strdup ("value"),
		.type = strdup ("uint32_t"),
	};
	mu_assert_notnull (collision->name, "name conflicting uint64 tag");
	mu_assert_notnull (member.name, "name conflicting uint64 member");
	mu_assert_notnull (member.type, "type conflicting uint64 member");
	RAnalStructMember *collision_member = RVecAnalTypeMember_emplace_back (
		&collision->struct_data.members);
	mu_assert_notnull (collision_member, "append conflicting uint64 member");
	*collision_member = member;
	r_anal_save_base_type (anal, collision);
	r_anal_base_type_free (collision);
	mu_assert_true (save_snapshot_typedef_type (anal, "uint64_t", "unsigned long long"),
		"restore current typedef root beside conflicting tag");
	rejected = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (rejected, "collect ambiguous typedef snapshot");
	mu_assert_false (rejected->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES,
		"current typedef and same-name tag fail closed");
	mu_assert_false (rejected->function_interface.logical_types_complete,
		"ambiguous root exposes no partial logical graph");
	r_anal_function_snapshot_free (rejected);

	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_seals_exact_call_site_interfaces(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create callsite snapshot analysis");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	mu_assert_true (r_anal_cc_set (anal, "rax exactcall(rdi)"),
		"seed exact callsite calling convention");

	RAnalFunction *caller = r_anal_create_function (
		anal, "callsite_caller", 0x8000, R_ANAL_FCN_TYPE_FCN, NULL);
	RAnalFunction *callee = r_anal_create_function (
		anal, "callsite_callee", 0x9000, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (caller, "create callsite caller");
	mu_assert_notnull (callee, "create callsite callee");
	RAnalBlock *block = r_anal_create_block (anal, 0x8000, 0x20);
	mu_assert_notnull (block, "create caller block");
	block->ninstr = 2;
	mu_assert_true (r_anal_bb_set_offset (block, 0, 0), "record caller entry instruction");
	mu_assert_true (r_anal_bb_set_offset (block, 1, 0x10), "record raw call instruction");
	r_anal_function_add_block (caller, block);
	r_unref (block);
	RAnalBlock *callee_block = r_anal_create_block (anal, 0x9000, 1);
	mu_assert_notnull (callee_block, "create callee block");
	r_anal_function_add_block (callee, callee_block);
	r_unref (callee_block);
	RAnalFunctionParam argument = {
		.name = "value",
		.type = "int64_t",
	};
	RList *arguments = r_list_new ();
	mu_assert_notnull (arguments, "create callsite arguments");
	mu_assert_true (r_list_append (arguments, &argument), "append callsite argument");
	RAnalFunctionSignature signature = {
		.ret_type = "void",
		.callconv = "exactcall",
		.params = arguments,
	};
	mu_assert_true (r_anal_function_set_signature (anal, callee, &signature),
		"apply exact callee signature");
	r_list_free (arguments);
	mu_assert_true (r_anal_xrefs_setf (
		anal, caller, 0x8010, 0x9000, R_ANAL_REF_TYPE_CALL),
		"record direct callsite");

	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, caller, NULL);
	mu_assert_notnull (snapshot, "collect exact callsite snapshot");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_CALL_SITE_INTERFACES,
		"callsite snapshot capability is present");
	mu_assert_eq (snapshot->num_call_site_interfaces, 1, "one exact callsite interface");
	RAnalCallSiteInterfaceSnapshot *call = &snapshot->call_site_interfaces[0];
	mu_assert_eq (call->instruction_addr, 0x8010, "raw call instruction identity");
	mu_assert_eq (call->target_addr, 0x9000, "raw direct target identity");
	mu_assert_notnull (call->calling_convention, "exact callsite calling convention is present");
	mu_assert_streq (call->calling_convention, "exactcall", "exact callsite calling convention");
	mu_assert_eq (call->num_arguments, 1, "one exact call argument");
	mu_assert_eq (call->arguments[0].index, 0, "exact call argument order");
	RRegItem *rdi = r_reg_get (anal->reg, "rdi", -1);
	mu_assert_notnull (rdi, "resolve full-width call argument carrier");
	mu_assert_eq (call->arguments[0].storage.offset,
		(ut64)(rdi->offset / 8), "full-width call argument register");
	r_unref (rdi);
	mu_assert_eq (call->arguments[0].storage.size, 8, "full-width call argument size");
	mu_assert_eq (call->result_kind, R_ANAL_SNAPSHOT_RETURN_VOID, "void call result contract");
	// Completeness describes the prototype, not the call instruction. The xref
	// establishes which callee is reached, so the argument and result carriers
	// resolved from that callee's signature are exactly as good as the
	// signature itself, and a call site is complete exactly when both resolved.
	mu_assert_true (call->complete,
		"an xref-derived callsite reports the prototype it recovered");
	mu_assert_false (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_CALL_SITE_INTERFACES,
		"xref-derived callsite cannot mint exact authority");

	ut64 revision = snapshot->revision_identity;
	callee->is_variadic = true;
	r_anal_function_bump_dirty_epoch (callee);
	RAnalFunctionSnapshot *variadic = r_anal_function_snapshot_collect_bounded (anal, caller, NULL);
	mu_assert_notnull (variadic, "collect variadic callsite snapshot");
	mu_assert_true (variadic->call_site_interfaces[0].variadic,
		"the callsite records that the callee is variadic");
	mu_assert_true (variadic->call_site_interfaces[0].complete,
		"a variadic callee still places its fixed arguments and its result");
	mu_assert_false (variadic->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_CALL_SITE_INTERFACES,
		"variadic callsite omits exact capability");
	mu_assert_neq (variadic->revision_identity, revision,
		"callsite contract mutation changes caller snapshot revision");
	r_anal_function_snapshot_free (variadic);
	callee->is_variadic = false;
	r_anal_function_bump_dirty_epoch (callee);

	// ...and not otherwise: a prototype the convention cannot place leaves the
	// arguments unresolved, and the callsite says so.
	RAnalFunctionParam unplaceable_argument = {
		.name = "second",
		.type = "int64_t",
	};
	arguments = r_list_new ();
	mu_assert_notnull (arguments, "create unplaceable callsite arguments");
	mu_assert_true (r_list_append (arguments, &argument), "append first unplaceable argument");
	mu_assert_true (r_list_append (arguments, &unplaceable_argument),
		"append second unplaceable argument");
	signature.params = arguments;
	mu_assert_true (r_anal_function_set_signature (anal, callee, &signature),
		"apply a prototype the one-register convention cannot place");
	r_list_free (arguments);
	RAnalFunctionSnapshot *incomplete = r_anal_function_snapshot_collect_bounded (anal, caller, NULL);
	mu_assert_notnull (incomplete, "collect unplaceable-argument callsite snapshot");
	mu_assert_eq (incomplete->num_call_site_interfaces, 1, "one unplaceable callsite");
	mu_assert_eq (incomplete->call_site_interfaces[0].num_arguments, 2,
		"the unplaceable prototype still reports both arguments");
	mu_assert_false (incomplete->call_site_interfaces[0].complete,
		"an argument the convention cannot place leaves the callsite incomplete");
	mu_assert_false (incomplete->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_CALL_SITE_INTERFACES,
		"incomplete callsite omits exact capability");
	r_anal_function_snapshot_free (incomplete);
	arguments = r_list_new ();
	mu_assert_notnull (arguments, "recreate placeable callsite arguments");
	mu_assert_true (r_list_append (arguments, &argument), "reappend placeable argument");
	signature.params = arguments;
	mu_assert_true (r_anal_function_set_signature (anal, callee, &signature),
		"restore the placeable callee prototype");
	r_list_free (arguments);
	RAnalFunction *second_callee = r_anal_create_function (
		anal, "callsite_callee_ambiguous", 0x9100, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (second_callee, "create ambiguous second callee");
	RAnalBlock *second_block = r_anal_create_block (anal, 0x9100, 1);
	mu_assert_notnull (second_block, "create ambiguous second callee block");
	r_anal_function_add_block (second_callee, second_block);
	r_unref (second_block);
	arguments = r_list_new ();
	mu_assert_notnull (arguments, "recreate ambiguous callsite arguments");
	mu_assert_true (r_list_append (arguments, &argument), "append ambiguous callsite argument");
	signature.params = arguments;
	mu_assert_true (r_anal_function_set_signature (anal, second_callee, &signature),
		"apply second exact callee signature");
	r_list_free (arguments);
	mu_assert_true (r_anal_xrefs_setf (
		anal, caller, 0x8010, 0x9100, R_ANAL_REF_TYPE_CALL),
		"record ambiguous raw callsite target");
	RAnalFunctionSnapshot *ambiguous = r_anal_function_snapshot_collect_bounded (anal, caller, NULL);
	mu_assert_notnull (ambiguous, "collect ambiguous raw callsite snapshot");
	mu_assert_eq (ambiguous->num_call_site_interfaces, 2,
		"ambiguous raw address preserves both generic source facts");
	mu_assert_eq (ambiguous->call_site_interfaces[0].instruction_addr,
		ambiguous->call_site_interfaces[1].instruction_addr,
		"ambiguous source facts retain their shared raw instruction");
	mu_assert_false (ambiguous->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_CALL_SITE_INTERFACES,
		"ambiguous raw callsite omits exact-set capability");
	r_anal_function_snapshot_free (ambiguous);
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}

bool test_r_anal_function_snapshot_rejects_inexact_stack_resources(void) {
	RCore *core = snapshot_test_core_new ();
	RAnal *anal = core? core->anal: NULL;
	mu_assert_notnull (anal, "create stack-resource analysis");
	r_anal_use (anal, "x86");
	r_anal_set_bits (anal, 64);
	mu_assert_true (r_anal_cc_set (anal, "rax stackcc(rdi)"), "seed stack-resource calling convention");

	RAnalFunction *fcn = r_anal_create_function (
		anal, "stack_snapshot", 0x7080, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "create stack-resource function");
	mu_assert_true (snapshot_test_ensure_block (anal, fcn, 1),
		"back stack-resource snapshot with exact bytes");
	RAnalFunctionParam parameter = {
		.name = "value",
		.type = "int64_t",
	};
	RList *parameters = r_list_new ();
	mu_assert_notnull (parameters, "create stack-resource parameter list");
	mu_assert_true (r_list_append (parameters, &parameter), "append stack-resource parameter");
	RAnalFunctionSignature signature = {
		.ret_type = "int64_t",
		.callconv = "stackcc",
		.params = parameters,
	};
	mu_assert_true (r_anal_function_set_signature (anal, fcn, &signature), "apply stack-resource signature");
	mu_assert_true (set_function_type_link (anal, fcn->name, fcn->addr),
		"link stack-resource signature by address");
	r_list_free (parameters);

	RAnalVar *first = r_anal_function_set_var (
		fcn, -8, R_ANAL_VAR_KIND_BPV, "int64_t", 8, false, "first_slot");
	RAnalVar *second = r_anal_function_set_var (
		fcn, -4, R_ANAL_VAR_KIND_BPV, "int32_t", 4, false, "overlap_slot");
	mu_assert_notnull (first, "create first overlapping slot");
	mu_assert_notnull (second, "create second overlapping slot");
	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect overlapping resource snapshot");
	mu_assert_false (snapshot->function_interface.stack_resources_complete,
		"overlapping resources on one base are incomplete");
	// The frame extent is a claim of the stack slot roles, not of the
	// interface: slots that overlap cannot prove they do not, so the roles lose
	// their exactness while the carriers recovered without reference to the
	// frame keep theirs.
	mu_assert_false (snapshot->function_interface.stack_slot_roles_complete,
		"overlap rejects the exact frame extent claim");
	mu_assert_false (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES,
		"overlap omits exact stack-slot-role capability");
	mu_assert_true (snapshot->function_interface.complete,
		"overlap leaves the parameter and return carriers certified");
	mu_assert_true (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE,
		"overlap keeps the exact-interface capability the frame does not decide");
	mu_assert_eq (snapshot->function_interface.num_parameters, 1,
		"overlap still reports the recovered parameter");
	mu_assert_streq (snapshot->function_interface.parameters[0].storage.name, "rdi",
		"overlap still names the parameter carrier it recovered");
	mu_assert_eq (snapshot->function_interface.return_kind,
		R_ANAL_SNAPSHOT_RETURN_REGISTER, "overlap still reports the result carrier");
	RRegItem *rax = r_reg_get (anal->reg, "rax", -1);
	mu_assert_notnull (rax, "resolve overlap result carrier");
	mu_assert_eq (snapshot->function_interface.return_storage.offset,
		(ut64)(rax->offset / 8),
		"overlap still reports the canonical result carrier");
	r_unref (rax);
	r_anal_function_snapshot_free (snapshot);

	mu_assert_true (r_anal_var_delete (anal, second), "remove overlapping resource");
	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_BP, "not_a_register"),
		"make BP base identity unknown");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect unknown-base resource snapshot");
	RAnalFcnSlot *unknown = find_stack_slot (&snapshot->context, "first_slot");
	mu_assert_notnull (unknown, "unknown-base resource stays in immutable snapshot");
	mu_assert_null (unknown->base_name, "unknown base has no exact register name");
	mu_assert_false (snapshot->function_interface.stack_resources_complete,
		"unknown base rejects complete stack resources");
	r_anal_function_snapshot_free (snapshot);

	mu_assert_true (r_reg_alias_setname (anal->reg, R_REG_ALIAS_BP, "rbp"), "restore BP identity");
	r_anal_var_set_type (anal, first, "missing_stack_resource_type");
	snapshot = r_anal_function_snapshot_collect_bounded (anal, fcn, NULL);
	mu_assert_notnull (snapshot, "collect unknown-size resource snapshot");
	RAnalFcnSlot *unknown_size = find_stack_slot (&snapshot->context, "first_slot");
	mu_assert_notnull (unknown_size, "unknown-size resource stays in immutable snapshot");
	mu_assert_eq (unknown_size->size, 0, "unknown type does not invent a resource size");
	mu_assert_false (snapshot->function_interface.stack_resources_complete,
		"unknown size rejects complete stack resources");
	r_anal_function_snapshot_free (snapshot);
	r_core_free (core);
	mu_end;
}


static bool test_dwarf5_exact_stack_homes(const RAnalFunctionSnapshot *snapshot) {
	const RAnalFunctionInterfaceSnapshot *interface = &snapshot->function_interface;
	if (interface->num_parameters != 2 || !interface->stack_slot_roles_complete
		|| !interface->complete
		|| !(snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES)
		|| !(snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE)) {
		return false;
	}
	const char *expected[] = { "rdi", "rsi" };
	bool seen[] = { false, false };
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (snapshot->context.fcn_slots, iter, slot) {
		if (slot->role != R_ANAL_FCN_SLOT_HOME || slot->arg_index < 0
			|| slot->arg_index >= 2) {
			continue;
		}
		const RAnalSnapshotParameter *parameter =
			&interface->parameters[slot->arg_index];
		if (!slot->home_reg || strcmp (slot->home_reg, expected[slot->arg_index])
			|| strcmp (slot->home_reg, r_str_get (parameter->storage.name))
			|| slot->home_reg_offset != parameter->storage.offset
			|| slot->home_reg_size != parameter->storage.size) {
			return false;
		}
		seen[slot->arg_index] = true;
	}
	return seen[0] && seen[1];
}

static bool test_dwarf5_inexact_stack_homes(const RAnalFunctionSnapshot *snapshot) {
	const RAnalFunctionInterfaceSnapshot *interface = &snapshot->function_interface;
	if (interface->stack_slot_roles_complete || interface->complete
		|| (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES)
		|| (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE)) {
		return false;
	}
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (snapshot->context.fcn_slots, iter, slot) {
		if (slot->role == R_ANAL_FCN_SLOT_ARG) {
			return true;
		}
	}
	return false;
}

static bool snapshot_probe(RAnal *a, ut64 addr, bool (*predicate)(const RAnalFunctionSnapshot *)) {
	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_take (a, addr, NULL);
	if (!snapshot) {
		return false;
	}
	const bool result = predicate (snapshot);
	r_anal_function_snapshot_free (snapshot);
	return result;
}

static bool test_dwarf5_function_type_links(void) {
	mu_assert_true (r_anal_use (anal, "x86"), "Couldn't load x86 analysis profile");
	mu_assert_true (r_anal_set_bits (anal, 64), "Couldn't select x86-64 analysis");
	mu_assert_true (r_anal_cc_set (anal, "rax amd64(rdi,rsi,rdx,rcx,r8,r9)"),
		"Couldn't seed the fixture calling convention");
	sdb_reset (anal->sdb_types);

	RBinFileOptions opt = {
		.baseaddr = 0x400000,
	};
	bool res = r_bin_open (bin, "bins/elf/dwarf5_line_cl", &opt);
	mu_assert ("dwarf5_line_cl binary could not be opened", res);
	RBinFile *bf = r_bin_cur (bin);
	mu_assert_notnull (bf, "Couldn't get current bin file");
	mu_assert_true (bf->bo->baddr_shift > 0, "DWARF5 fixture was not relocated");
	ut64 shift = (ut64)bf->bo->baddr_shift;
	ut64 foo_addr = 0x1140 + shift;
	ut64 main_addr = 0x11c0 + shift;

	sdb_set (anal->sdb_types, "reserved_type", "func", 0);
	sdb_set (anal->sdb_types, "func.reserved_type.ret", "void", 0);
	sdb_set (anal->sdb_types, "func.reserved_type.args", "0", 0);
	mu_assert_true (sdb_setf (anal->sdb_types, "reserved_type", 0,
		"fcnlink.%08" PFMT64x, foo_addr), "preexisting conflicting function link");

	RVecDwarfAbbrevDecl *abbrevs = r_bin_dwarf_parse_abbrev (bf, MODE);
	mu_assert_notnull (abbrevs, "Couldn't parse DWARF5 abbreviations");
	RBinDwarfDebugInfo *info = r_bin_dwarf_parse_info (bf, abbrevs, MODE);
	mu_assert_notnull (info, "Couldn't parse DWARF5 indexed info");
	RAnalDwarfContext ctx = {
		.info = info,
		.loc = NULL,
	};
	r_anal_dwarf_process_info (anal, &ctx);

	Sdb *dwarf_sdb = sdb_ns (anal->sdb, "dwarf", 0);
	mu_assert_notnull (dwarf_sdb, "No dwarf function information in db");
	const char *typed_main = sdb_const_get (dwarf_sdb, "fcn.main.typed_name", NULL);
	mu_assert_notnull (typed_main, "Missing typed name for DWARF5 main");
	const char *first_record = sdb_const_get (dwarf_sdb, "fcn.main.arg.0", NULL);
	const char *second_record = sdb_const_get (dwarf_sdb, "fcn.main.arg.1", NULL);
	mu_assert_true (first_record && r_str_startswith (first_record, "dwarf-stack-home-v1,0,b,"),
		"First formal stores one exact versioned home record");
	mu_assert_true (second_record && r_str_startswith (second_record, "dwarf-stack-home-v1,1,b,"),
		"Second formal stores one exact versioned home record");
	mu_assert_null (sdb_const_get (dwarf_sdb, "fcn.main.arg.0.exact", NULL),
		"Exact authority has no independent side key");
	mu_assert_null (sdb_const_get (dwarf_sdb, "fcn.main.arg.0.ordinal", NULL),
		"Formal ordinal has no independent side key");
	char *saved_first_record = strdup (first_record);
	mu_assert_notnull (saved_first_record, "Copy exact formal record for refusal tests");
	char *main_link = test_function_type_link_at (anal->sdb_types, main_addr);
	mu_assert_notnull (main_link, "Missing exact link for complete DWARF5 main prototype");
	mu_assert_streq (main_link, typed_main, "complete prototype linked at relocated low_pc");
	free (main_link);
	mu_assert_null (r_type_link_at (anal->sdb_types, main_addr),
		"Function signature must not occupy the data type link namespace");
	char *foo_link = test_function_type_link_at (anal->sdb_types, foo_addr);
	mu_assert_streq (foo_link, "reserved_type", "conflicting address link is preserved");
	free (foo_link);

	sdb_set (anal->sdb_types, "wrong_name", "func", 0);
	sdb_set (anal->sdb_types, "func.wrong_name.ret", "uint8_t", 0);
	sdb_set (anal->sdb_types, "func.wrong_name.args", "0", 0);
	RAnalFunction *fcn = r_anal_create_function (anal, "wrong_name", main_addr, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "Couldn't create analysis function for linked signature lookup");
	fcn->callconv = r_str_constpool_get (&anal->constpool, "amd64");
	RAnalFunctionSignature *signature = r_anal_function_get_signature (fcn);
	mu_assert_notnull (signature, "Couldn't resolve address-linked function signature");
	mu_assert_streq (signature->ret_type, "int", "address-linked signature wins over function name");
	mu_assert_eq (r_list_length (signature->params), 2, "DWARF5 main parameter count");
	r_anal_function_signature_free (signature);

	RAnalBlock *block = r_anal_create_block (anal, main_addr, 1);
	mu_assert_notnull (block, "Couldn't create DWARF5 main snapshot block");
	r_anal_function_add_block (fcn, block);
	r_unref (block);
	io->va = true;
	r_io_bind (io, &anal->iob);
	mu_assert_notnull (r_io_open_at (io, "malloc://1", R_PERM_R, 0, main_addr),
		"Couldn't map exact snapshot bytes at DWARF5 main");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	RAnalVar *first = r_anal_function_get_var_byname (fcn, "a");
	RAnalVar *second = r_anal_function_get_var_byname (fcn, "v");
	mu_assert_notnull (first, "Couldn't integrate first DWARF5 formal");
	mu_assert_notnull (second, "Couldn't integrate second DWARF5 formal");
	mu_assert_eq (first->argnum, 0, "First exact formal keeps its DWARF ordinal");
	mu_assert_eq (second->argnum, 1, "Second exact formal keeps its DWARF ordinal");
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_exact_stack_homes),
		"Exact DWARF formals become complete ABI stack homes");
	const st64 saved_bp_off = fcn->bp_off;
	const int saved_maxstack = fcn->maxstack;
	fcn->bp_off++;
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Changed BP basis invalidates exact DWARF stack homes");
	fcn->bp_off = saved_bp_off;
	fcn->maxstack++;
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Changed maximum-stack basis invalidates exact DWARF stack homes");
	fcn->maxstack = saved_maxstack;
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_exact_stack_homes),
		"Restored exact frame state restores source-offset validation");

	mu_assert_true (r_anal_function_rename (fcn, "renamed_dwarf_entry"),
		"Couldn't rename DWARF-backed function");
	mu_assert_true (r_anal_var_rename (anal, first, "renamed_first"),
		"Couldn't rename first DWARF-backed formal");
	mu_assert_true (r_anal_var_rename (anal, second, "renamed_second"),
		"Couldn't rename second DWARF-backed formal");
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_exact_stack_homes),
		"Names do not supply stack-home authority");

	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0",
		"dwarf-stack-home-v1,0,b,-8,YQ==,aW50,extra", 0),
		"Install malformed marked formal record");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Malformed marked records revoke prior exact formal proof");
	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0",
		"dwarf-stack-home-v1,0,b,-16,YQ==,aW50", 0),
		"Install canonical forged marked formal record");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Canonical marked records without parser provenance cannot mint homes");
	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0", saved_first_record, 0),
		"Restore exact formal after malformed-record refusal");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	first = r_anal_function_get_var_byname (fcn, "a");
	second = r_anal_function_get_var_byname (fcn, "v");
	mu_assert_notnull (first, "Couldn't restore first exact formal");
	mu_assert_notnull (second, "Couldn't restore second exact formal");
	r_anal_var_set_type (anal, first, first->type);
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Absent private formal proof refuses exact stack-slot roles");
	char *legacy_record = r_str_newf ("%s,%c,%" PFMT64d ",%s",
		first->name, first->kind, (st64)first->delta + fcn->bp_off, first->type);
	mu_assert_notnull (legacy_record, "Build advisory legacy formal record");
	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0", legacy_record, 0),
		"Install advisory legacy formal record");
	free (legacy_record);
	mu_assert_true (sdb_num_set (dwarf_sdb, "fcn.main.arg.0.exact", 1, 0),
		"Install forged legacy exact side key");
	mu_assert_true (sdb_num_set (dwarf_sdb, "fcn.main.arg.0.ordinal", 0, 0),
		"Install forged legacy ordinal side key");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Legacy records and forged side keys cannot mint exact homes");
	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0", saved_first_record, 0),
		"Restore exact formal record");
	sdb_unset (dwarf_sdb, "fcn.main.arg.0.exact", 0);
	sdb_unset (dwarf_sdb, "fcn.main.arg.0.ordinal", 0);
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	first = r_anal_function_get_var_byname (fcn, "a");
	second = r_anal_function_get_var_byname (fcn, "v");
	mu_assert_notnull (first, "Couldn't reintegrate first exact formal");
	mu_assert_notnull (second, "Couldn't reintegrate second exact formal");
	first->argnum = 2;
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Out-of-range formal ordinal refuses exact stack-slot roles");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	first = r_anal_function_get_var_byname (fcn, "a");
	mu_assert_notnull (first, "Couldn't restore exact formal before type mutation");
	r_anal_var_set_type (anal, first, "char *");
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Mismatched formal type refuses exact stack-slot roles");

	const char first_kind = first->kind;
	const int first_delta = first->delta;
	const char second_kind = second->kind;
	const int second_delta = second->delta;
	mu_assert_true (r_anal_var_delete (anal, first),
		"Remove first source home before name-collision regression");
	mu_assert_true (r_anal_var_delete (anal, second),
		"Remove second source home before name-collision regression");
	RRegItem *rdi = r_reg_get (anal->reg, "rdi", -1);
	RRegItem *rsi = r_reg_get (anal->reg, "rsi", -1);
	mu_assert_notnull (rdi, "Resolve first ABI register");
	mu_assert_notnull (rsi, "Resolve second ABI register");
	mu_assert_notnull (r_anal_function_set_var (fcn, rdi->index,
		R_ANAL_VAR_KIND_REG, "int", 8, true, "a"),
		"Create first register formal with the source name");
	mu_assert_notnull (r_anal_function_set_var (fcn, rsi->index,
		R_ANAL_VAR_KIND_REG, "char **", 8, true, "v"),
		"Create second register formal with the source name");
	r_unref (rdi);
	r_unref (rsi);
	RAnalVar *first_home = r_anal_function_set_var (fcn, first_delta,
		first_kind, "uint64_t", 8, false, "var_first_home");
	RAnalVar *second_home = r_anal_function_set_var (fcn, second_delta,
		second_kind, "uint64_t", 8, false, "var_second_home");
	mu_assert_notnull (first_home, "Create first heuristic stack resource");
	mu_assert_notnull (second_home, "Create second heuristic stack resource");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_streq (first_home->type, "int",
		"Exact first formal replaces the heuristic home type");
	mu_assert_streq (second_home->type, "char const **",
		"Exact second formal replaces the heuristic home type");
	mu_assert_true (first_home->isarg && second_home->isarg,
		"Exact formal records promote existing resources to argument homes");
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_exact_stack_homes),
		"Exact stack homes survive source-name collisions with ABI register formals");
	free (saved_first_record);

	r_bin_dwarf_free_debug_info (info);
	RVecDwarfAbbrevDecl_free (abbrevs);
	mu_end;
}
































static bool test_dwarf5_exact_stack_homes(const RAnalFunctionSnapshot *snapshot) {
	const RAnalFunctionInterfaceSnapshot *interface = &snapshot->function_interface;
	if (interface->num_parameters != 2 || !interface->stack_slot_roles_complete
		|| !interface->complete
		|| !(snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES)
		|| !(snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE)) {
		return false;
	}
	const char *expected[] = { "rdi", "rsi" };
	bool seen[] = { false, false };
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (snapshot->context.fcn_slots, iter, slot) {
		if (slot->role != R_ANAL_FCN_SLOT_HOME || slot->arg_index < 0
			|| slot->arg_index >= 2) {
			continue;
		}
		const RAnalSnapshotParameter *parameter =
			&interface->parameters[slot->arg_index];
		if (!slot->home_reg || strcmp (slot->home_reg, expected[slot->arg_index])
			|| strcmp (slot->home_reg, r_str_get (parameter->storage.name))
			|| slot->home_reg_offset != parameter->storage.offset
			|| slot->home_reg_size != parameter->storage.size) {
			return false;
		}
		seen[slot->arg_index] = true;
	}
	return seen[0] && seen[1];
}

static bool test_dwarf5_inexact_stack_homes(const RAnalFunctionSnapshot *snapshot) {
	const RAnalFunctionInterfaceSnapshot *interface = &snapshot->function_interface;
	if (interface->stack_slot_roles_complete || interface->complete
		|| (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES)
		|| (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE)) {
		return false;
	}
	RListIter *iter;
	RAnalFcnSlot *slot;
	r_list_foreach (snapshot->context.fcn_slots, iter, slot) {
		if (slot->role == R_ANAL_FCN_SLOT_ARG) {
			return true;
		}
	}
	return false;
}

static bool snapshot_probe(RAnal *a, ut64 addr, bool (*predicate)(const RAnalFunctionSnapshot *)) {
	RAnalFunctionSnapshot *snapshot = r_anal_function_snapshot_take (a, addr, NULL);
	if (!snapshot) {
		return false;
	}
	const bool result = predicate (snapshot);
	r_anal_function_snapshot_free (snapshot);
	return result;
}

static bool test_dwarf5_function_type_links(void) {
	mu_assert_true (r_anal_use (anal, "x86"), "Couldn't load x86 analysis profile");
	mu_assert_true (r_anal_set_bits (anal, 64), "Couldn't select x86-64 analysis");
	mu_assert_true (r_anal_cc_set (anal, "rax amd64(rdi,rsi,rdx,rcx,r8,r9)"),
		"Couldn't seed the fixture calling convention");
	sdb_reset (anal->sdb_types);

	RBinFileOptions opt = {
		.baseaddr = 0x400000,
	};
	bool res = r_bin_open (bin, "bins/elf/dwarf5_line_cl", &opt);
	mu_assert ("dwarf5_line_cl binary could not be opened", res);
	RBinFile *bf = r_bin_cur (bin);
	mu_assert_notnull (bf, "Couldn't get current bin file");
	mu_assert_true (bf->bo->baddr_shift > 0, "DWARF5 fixture was not relocated");
	ut64 shift = (ut64)bf->bo->baddr_shift;
	ut64 foo_addr = 0x1140 + shift;
	ut64 main_addr = 0x11c0 + shift;

	sdb_set (anal->sdb_types, "reserved_type", "func", 0);
	sdb_set (anal->sdb_types, "func.reserved_type.ret", "void", 0);
	sdb_set (anal->sdb_types, "func.reserved_type.args", "0", 0);
	mu_assert_true (sdb_setf (anal->sdb_types, "reserved_type", 0,
		"fcnlink.%08" PFMT64x, foo_addr), "preexisting conflicting function link");

	RVecDwarfAbbrevDecl *abbrevs = r_bin_dwarf_parse_abbrev (bf, MODE);
	mu_assert_notnull (abbrevs, "Couldn't parse DWARF5 abbreviations");
	RBinDwarfDebugInfo *info = r_bin_dwarf_parse_info (bf, abbrevs, MODE);
	mu_assert_notnull (info, "Couldn't parse DWARF5 indexed info");
	RAnalDwarfContext ctx = {
		.info = info,
		.loc = NULL,
	};
	r_anal_dwarf_process_info (anal, &ctx);

	Sdb *dwarf_sdb = sdb_ns (anal->sdb, "dwarf", 0);
	mu_assert_notnull (dwarf_sdb, "No dwarf function information in db");
	const char *typed_main = sdb_const_get (dwarf_sdb, "fcn.main.typed_name", NULL);
	mu_assert_notnull (typed_main, "Missing typed name for DWARF5 main");
	const char *first_record = sdb_const_get (dwarf_sdb, "fcn.main.arg.0", NULL);
	const char *second_record = sdb_const_get (dwarf_sdb, "fcn.main.arg.1", NULL);
	mu_assert_true (first_record && r_str_startswith (first_record, "dwarf-stack-home-v1,0,b,"),
		"First formal stores one exact versioned home record");
	mu_assert_true (second_record && r_str_startswith (second_record, "dwarf-stack-home-v1,1,b,"),
		"Second formal stores one exact versioned home record");
	mu_assert_null (sdb_const_get (dwarf_sdb, "fcn.main.arg.0.exact", NULL),
		"Exact authority has no independent side key");
	mu_assert_null (sdb_const_get (dwarf_sdb, "fcn.main.arg.0.ordinal", NULL),
		"Formal ordinal has no independent side key");
	char *saved_first_record = strdup (first_record);
	mu_assert_notnull (saved_first_record, "Copy exact formal record for refusal tests");
	char *main_link = test_function_type_link_at (anal->sdb_types, main_addr);
	mu_assert_notnull (main_link, "Missing exact link for complete DWARF5 main prototype");
	mu_assert_streq (main_link, typed_main, "complete prototype linked at relocated low_pc");
	free (main_link);
	mu_assert_null (r_type_link_at (anal->sdb_types, main_addr),
		"Function signature must not occupy the data type link namespace");
	char *foo_link = test_function_type_link_at (anal->sdb_types, foo_addr);
	mu_assert_streq (foo_link, "reserved_type", "conflicting address link is preserved");
	free (foo_link);

	sdb_set (anal->sdb_types, "wrong_name", "func", 0);
	sdb_set (anal->sdb_types, "func.wrong_name.ret", "uint8_t", 0);
	sdb_set (anal->sdb_types, "func.wrong_name.args", "0", 0);
	RAnalFunction *fcn = r_anal_create_function (anal, "wrong_name", main_addr, R_ANAL_FCN_TYPE_FCN, NULL);
	mu_assert_notnull (fcn, "Couldn't create analysis function for linked signature lookup");
	fcn->callconv = r_str_constpool_get (&anal->constpool, "amd64");
	RAnalFunctionSignature *signature = r_anal_function_get_signature (fcn);
	mu_assert_notnull (signature, "Couldn't resolve address-linked function signature");
	mu_assert_streq (signature->ret_type, "int", "address-linked signature wins over function name");
	mu_assert_eq (r_list_length (signature->params), 2, "DWARF5 main parameter count");
	r_anal_function_signature_free (signature);

	RAnalBlock *block = r_anal_create_block (anal, main_addr, 1);
	mu_assert_notnull (block, "Couldn't create DWARF5 main snapshot block");
	r_anal_function_add_block (fcn, block);
	r_unref (block);
	io->va = true;
	r_io_bind (io, &anal->iob);
	mu_assert_notnull (r_io_open_at (io, "malloc://1", R_PERM_R, 0, main_addr),
		"Couldn't map exact snapshot bytes at DWARF5 main");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	RAnalVar *first = r_anal_function_get_var_byname (fcn, "a");
	RAnalVar *second = r_anal_function_get_var_byname (fcn, "v");
	mu_assert_notnull (first, "Couldn't integrate first DWARF5 formal");
	mu_assert_notnull (second, "Couldn't integrate second DWARF5 formal");
	mu_assert_eq (first->argnum, 0, "First exact formal keeps its DWARF ordinal");
	mu_assert_eq (second->argnum, 1, "Second exact formal keeps its DWARF ordinal");
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_exact_stack_homes),
		"Exact DWARF formals become complete ABI stack homes");
	const st64 saved_bp_off = fcn->bp_off;
	const int saved_maxstack = fcn->maxstack;
	fcn->bp_off++;
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Changed BP basis invalidates exact DWARF stack homes");
	fcn->bp_off = saved_bp_off;
	fcn->maxstack++;
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Changed maximum-stack basis invalidates exact DWARF stack homes");
	fcn->maxstack = saved_maxstack;
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_exact_stack_homes),
		"Restored exact frame state restores source-offset validation");

	mu_assert_true (r_anal_function_rename (fcn, "renamed_dwarf_entry"),
		"Couldn't rename DWARF-backed function");
	mu_assert_true (r_anal_var_rename (anal, first, "renamed_first"),
		"Couldn't rename first DWARF-backed formal");
	mu_assert_true (r_anal_var_rename (anal, second, "renamed_second"),
		"Couldn't rename second DWARF-backed formal");
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_exact_stack_homes),
		"Names do not supply stack-home authority");

	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0",
		"dwarf-stack-home-v1,0,b,-8,YQ==,aW50,extra", 0),
		"Install malformed marked formal record");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Malformed marked records revoke prior exact formal proof");
	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0",
		"dwarf-stack-home-v1,0,b,-16,YQ==,aW50", 0),
		"Install canonical forged marked formal record");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Canonical marked records without parser provenance cannot mint homes");
	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0", saved_first_record, 0),
		"Restore exact formal after malformed-record refusal");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	first = r_anal_function_get_var_byname (fcn, "a");
	second = r_anal_function_get_var_byname (fcn, "v");
	mu_assert_notnull (first, "Couldn't restore first exact formal");
	mu_assert_notnull (second, "Couldn't restore second exact formal");
	r_anal_var_set_type (anal, first, first->type);
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Absent private formal proof refuses exact stack-slot roles");
	char *legacy_record = r_str_newf ("%s,%c,%" PFMT64d ",%s",
		first->name, first->kind, (st64)first->delta + fcn->bp_off, first->type);
	mu_assert_notnull (legacy_record, "Build advisory legacy formal record");
	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0", legacy_record, 0),
		"Install advisory legacy formal record");
	free (legacy_record);
	mu_assert_true (sdb_num_set (dwarf_sdb, "fcn.main.arg.0.exact", 1, 0),
		"Install forged legacy exact side key");
	mu_assert_true (sdb_num_set (dwarf_sdb, "fcn.main.arg.0.ordinal", 0, 0),
		"Install forged legacy ordinal side key");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Legacy records and forged side keys cannot mint exact homes");
	mu_assert_true (sdb_set (dwarf_sdb, "fcn.main.arg.0", saved_first_record, 0),
		"Restore exact formal record");
	sdb_unset (dwarf_sdb, "fcn.main.arg.0.exact", 0);
	sdb_unset (dwarf_sdb, "fcn.main.arg.0.ordinal", 0);
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	first = r_anal_function_get_var_byname (fcn, "a");
	second = r_anal_function_get_var_byname (fcn, "v");
	mu_assert_notnull (first, "Couldn't reintegrate first exact formal");
	mu_assert_notnull (second, "Couldn't reintegrate second exact formal");
	first->argnum = 2;
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Out-of-range formal ordinal refuses exact stack-slot roles");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	first = r_anal_function_get_var_byname (fcn, "a");
	mu_assert_notnull (first, "Couldn't restore exact formal before type mutation");
	r_anal_var_set_type (anal, first, "char *");
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_inexact_stack_homes),
		"Mismatched formal type refuses exact stack-slot roles");

	const char first_kind = first->kind;
	const int first_delta = first->delta;
	const char second_kind = second->kind;
	const int second_delta = second->delta;
	mu_assert_true (r_anal_var_delete (anal, first),
		"Remove first source home before name-collision regression");
	mu_assert_true (r_anal_var_delete (anal, second),
		"Remove second source home before name-collision regression");
	RRegItem *rdi = r_reg_get (anal->reg, "rdi", -1);
	RRegItem *rsi = r_reg_get (anal->reg, "rsi", -1);
	mu_assert_notnull (rdi, "Resolve first ABI register");
	mu_assert_notnull (rsi, "Resolve second ABI register");
	mu_assert_notnull (r_anal_function_set_var (fcn, rdi->index,
		R_ANAL_VAR_KIND_REG, "int", 8, true, "a"),
		"Create first register formal with the source name");
	mu_assert_notnull (r_anal_function_set_var (fcn, rsi->index,
		R_ANAL_VAR_KIND_REG, "char **", 8, true, "v"),
		"Create second register formal with the source name");
	r_unref (rdi);
	r_unref (rsi);
	RAnalVar *first_home = r_anal_function_set_var (fcn, first_delta,
		first_kind, "uint64_t", 8, false, "var_first_home");
	RAnalVar *second_home = r_anal_function_set_var (fcn, second_delta,
		second_kind, "uint64_t", 8, false, "var_second_home");
	mu_assert_notnull (first_home, "Create first heuristic stack resource");
	mu_assert_notnull (second_home, "Create second heuristic stack resource");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_streq (first_home->type, "int",
		"Exact first formal replaces the heuristic home type");
	mu_assert_streq (second_home->type, "char const **",
		"Exact second formal replaces the heuristic home type");
	mu_assert_true (first_home->isarg && second_home->isarg,
		"Exact formal records promote existing resources to argument homes");
	mu_assert_true (snapshot_probe (
		anal, main_addr, test_dwarf5_exact_stack_homes),
		"Exact stack homes survive source-name collisions with ABI register formals");
	free (saved_first_record);

	r_bin_dwarf_free_debug_info (info);
	RVecDwarfAbbrevDecl_free (abbrevs);
	mu_end;
}


static bool test_set_function_type_link(RAnal *anal, const char *type_name, ut64 addr) {
	if (!anal->sdb_types || R_STR_ISEMPTY (type_name)) {
		return false;
	}
	if (r_type_func_exist (anal->sdb_types, type_name)) {
		return r_anal_function_type_link_set (anal, type_name, addr);
	}
	return r_anal_types_set_link (anal, type_name, addr)
		|| r_anal_types_set_link_offset (anal, type_name, addr);
}

static bool test_dwarf3_abstract_origin_prototype_join(void) {
	r_str_ncpy (anal->config->arch, "x86", sizeof (anal->config->arch));
	anal->config->bits = 64;
	sdb_reset (anal->sdb_types);
	RBinFileOptions opt = { 0 };
	mu_assert_true (r_bin_open (bin, "bins/elf/dwarf3_cpp.elf", &opt),
		"dwarf3_cpp.elf binary could not be opened");
	RBinFile *bf = r_bin_cur (bin);
	mu_assert_notnull (bf, "Couldn't get current dwarf3_cpp.elf bin file");
	RVecDwarfAbbrevDecl *abbrevs = r_bin_dwarf_parse_abbrev (bf, MODE);
	mu_assert_notnull (abbrevs, "Couldn't parse DWARF3 abbreviations");
	RBinDwarfDebugInfo *info = r_bin_dwarf_parse_info (bf, abbrevs, MODE);
	mu_assert_notnull (info, "Couldn't parse DWARF3 debug info");
	mu_assert_eq (RVecDwarfCompUnit_length (info->comp_units), 1,
		"Expected one DWARF3 compilation unit");
	RBinDwarfCompUnit *unit = RVecDwarfCompUnit_at (info->comp_units, 0);
	RBinDwarfDie *concrete = test_find_die_at (unit, 0x39c);
	RBinDwarfDie *concrete_formal = test_find_die_at (unit, 0x3c0);
	RBinDwarfDie *origin_decl = test_find_die_at (unit, 0x6d);
	RBinDwarfDie *foreign_formal = test_find_die_at (unit, 0x314);
	RBinDwarfDie *missing_concrete = test_find_die_at (unit, 0x329);
	RBinDwarfDie *missing_origin_decl = test_find_die_at (unit, 0x8a);
	RBinDwarfDie *dog_origin_decl = test_find_die_at (unit, 0x14c);
	mu_assert_notnull (concrete, "Missing concrete constructor DIE");
	mu_assert_notnull (concrete_formal, "Missing concrete constructor formal");
	mu_assert_notnull (origin_decl, "Missing constructor origin declaration");
	mu_assert_notnull (foreign_formal, "Missing foreign abstract formal");
	mu_assert_notnull (missing_concrete, "Missing concrete destructor DIE");
	mu_assert_notnull (missing_origin_decl, "Missing destructor origin declaration");
	mu_assert_notnull (dog_origin_decl, "Missing Dog constructor origin declaration");
	RBinDwarfAttrValue *origin = test_find_attr (concrete, DW_AT_abstract_origin);
	RBinDwarfAttrValue *formal_origin = test_find_attr (
		concrete_formal, DW_AT_abstract_origin);
	RBinDwarfAttrValue *high_pc = test_find_attr (concrete, DW_AT_high_pc);
	RBinDwarfAttrValue *concrete_linkage = test_find_attr (
		concrete, DW_AT_MIPS_linkage_name);
	RBinDwarfAttrValue *abstract_linkage = test_find_attr (
		origin_decl, DW_AT_MIPS_linkage_name);
	RBinDwarfAttrValue *origin_mutable = test_find_attr (
		origin_decl, DW_AT_decl_line);
	RBinDwarfAttrValue *prototyped = test_find_attr (
		origin_decl, DW_AT_decl_column);
	RBinDwarfAttrValue *missing_prototyped = test_find_attr (
		missing_origin_decl, DW_AT_decl_column);
	RBinDwarfAttrValue *dog_prototyped = test_find_attr (
		dog_origin_decl, DW_AT_decl_column);
	mu_assert_notnull (origin, "Missing concrete abstract origin");
	mu_assert_notnull (formal_origin, "Missing formal abstract origin");
	mu_assert_notnull (high_pc, "Missing concrete high_pc");
	mu_assert_notnull (concrete_linkage, "Missing concrete linkage identity");
	mu_assert_notnull (abstract_linkage, "Missing abstract linkage identity");
	mu_assert_streq (concrete_linkage->string.content, "_ZN4BirdC2Ev",
		"Fixture uses an Itanium base-constructor instance");
	mu_assert_streq (abstract_linkage->string.content, "_ZN4BirdC4Ev",
		"Fixture origin uses an Itanium unified-constructor identity");
	mu_assert_notnull (origin_mutable, "Missing mutable origin declaration attribute");
	mu_assert_notnull (prototyped, "Missing mutable constructor declaration attribute");
	mu_assert_notnull (missing_prototyped,
		"Missing mutable destructor declaration attribute");
	mu_assert_notnull (dog_prototyped,
		"Missing mutable Dog constructor declaration attribute");
	RBinDwarfAttrValue saved_prototyped = *prototyped;
	prototyped->attr_name = DW_AT_prototyped;
	prototyped->attr_form = DW_FORM_flag;
	prototyped->kind = DW_AT_KIND_FLAG;
	prototyped->flag = true;
	RBinDwarfAttrValue saved_dog_prototyped = *dog_prototyped;
	dog_prototyped->attr_name = DW_AT_prototyped;
	dog_prototyped->attr_form = DW_FORM_flag;
	dog_prototyped->kind = DW_AT_KIND_FLAG;
	dog_prototyped->flag = true;
	RAnalDwarfContext ctx = {
		.info = info,
		.loc = NULL,
	};
	const ut64 concrete_addr = 0x130e;
	const ut64 dog_concrete_addr = 0x126e;

	const ut64 saved_origin_ref = origin->reference;
	origin->reference = concrete->offset;
	r_anal_dwarf_process_info (anal, &ctx);
	char *link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link, "Cyclic abstract origin must not create an exact link");
	free (link);
	origin->reference = UT64_MAX;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link, "Unresolved abstract origin must not create an exact link");
	free (link);
	origin->reference = concrete_formal->offset;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link, "Wrong-tag abstract origin must not create an exact link");
	free (link);
	origin->reference = saved_origin_ref;

	const ut64 saved_formal_origin_ref = formal_origin->reference;
	formal_origin->reference = foreign_formal->offset;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link, "Foreign formal origin must not create an exact link");
	free (link);
	formal_origin->reference = saved_formal_origin_ref;

	RBinDwarfAttrValue saved_high_pc = *high_pc;
	high_pc->attr_name = DW_AT_MIPS_linkage_name;
	high_pc->attr_form = DW_FORM_string;
	high_pc->kind = DW_AT_KIND_STRING;
	high_pc->string.content = concrete_linkage->string.content;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"Duplicate concrete identities must not create an exact link");
	free (link);
	*high_pc = saved_high_pc;
	const char *saved_concrete_linkage = concrete_linkage->string.content;
	concrete_linkage->string.content = "_ZN3DogC2Ev";
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"Unrelated concrete and abstract linkage identities must be refused");
	free (link);
	concrete_linkage->string.content = saved_concrete_linkage;
	high_pc->attr_name = DW_AT_name;
	high_pc->attr_form = DW_FORM_string;
	high_pc->kind = DW_AT_KIND_STRING;
	high_pc->string.content = "ConflictingConcreteName";
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"Conflicting concrete and abstract source names must be refused");
	free (link);
	*high_pc = saved_high_pc;

	const ut64 saved_foreign_offset = foreign_formal->offset;
	foreign_formal->offset = origin_decl->offset;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"Duplicate CU DIE offsets must refuse exact membership authority");
	free (link);
	foreign_formal->offset = saved_foreign_offset;

	RBinDwarfAttrValue saved_origin_mutable = *origin_mutable;
	origin_mutable->attr_name = DW_AT_high_pc;
	origin_mutable->attr_form = DW_FORM_data4;
	origin_mutable->kind = DW_AT_KIND_CONSTANT;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"Address-bearing abstract origins must not create an exact link");
	free (link);
	*origin_mutable = saved_origin_mutable;

	origin_mutable->attr_name = DW_AT_declaration;
	origin_mutable->attr_form = DW_FORM_data1;
	origin_mutable->kind = DW_AT_KIND_CONSTANT;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"Malformed abstract declaration flags must not create an exact link");
	free (link);
	*origin_mutable = saved_origin_mutable;

	RBinDwarfDie *concrete_terminator = test_find_subtree_terminator (unit, concrete);
	mu_assert_notnull (concrete_terminator, "Missing concrete subtree terminator");
	const ut64 saved_terminator_abbrev = concrete_terminator->abbrev_code;
	concrete_terminator->abbrev_code = 1;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"A later CU terminator cannot close an unterminated concrete subtree");
	free (link);
	concrete_terminator->abbrev_code = saved_terminator_abbrev;

	const ut64 saved_high_pc_name = high_pc->attr_name;
	high_pc->attr_name = DW_AT_ranges;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link, "Ranges-based concrete authority must be refused");
	free (link);
	high_pc->attr_name = saved_high_pc_name;

	RBinDwarfAttrValue saved_missing_prototyped = *missing_prototyped;
	missing_prototyped->attr_name = DW_AT_prototyped;
	missing_prototyped->attr_form = DW_FORM_flag;
	missing_prototyped->kind = DW_AT_KIND_FLAG;
	missing_prototyped->flag = true;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, 0x134a);
	mu_assert_null (link,
		"Concrete formals missing from the abstract prototype must be refused");
	free (link);
	*missing_prototyped = saved_missing_prototyped;

	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_notnull (link,
		"Exact concrete-to-abstract formal bijection must create an address link");
	char *first_link = strdup (link);
	mu_assert_notnull (first_link, "Copy exact abstract-origin link");
	free (link);
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_streq (link, first_link,
		"Repeated abstract-origin import keeps the exact address link stable");
	free (link);
	mu_assert_true (test_set_function_type_link (
		anal, first_link, concrete_addr),
		"Repeat the exact link through the ordinary mutation path");
	origin->reference = UT64_MAX;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_streq (link, first_link,
		"An identical ordinary write clears parser ownership");
	free (link);
	char link_key[SDB_MAX_KEY];
	snprintf (link_key, sizeof (link_key),
		"fcnlink.%08" PFMT64x, concrete_addr);
	mu_assert_true (sdb_unset (anal->sdb_types, link_key, 0),
		"Remove the ordinary link before restoring parser ownership");
	origin->reference = saved_origin_ref;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_notnull (link, "Restore parser-owned address link");
	free (link);

	origin->reference = UT64_MAX;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"A refused generation revokes its prior parser-owned address link");
	free (link);
	mu_assert_true (sdb_set (anal->sdb_types, "foreign_dwarf_signature", "func", 0),
		"Seed foreign function type");
	mu_assert_true (sdb_setf (anal->sdb_types, "foreign_dwarf_signature", 0,
		"fcnlink.%08" PFMT64x, concrete_addr),
		"Seed foreign address link");
	Sdb *dwarf_sdb = sdb_ns (anal->sdb, "dwarf", 0);
	mu_assert_notnull (dwarf_sdb, "Missing DWARF namespace for forged marker test");
	mu_assert_true (sdb_setf (dwarf_sdb, "foreign_dwarf_signature", 0,
		"exact.fcnlink.%08" PFMT64x, concrete_addr),
		"Forge the retired public ownership marker");
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_streq (link, "foreign_dwarf_signature",
		"A forged public marker cannot delete a foreign address link");
	free (link);
	origin->reference = saved_origin_ref;
	r_anal_dwarf_process_info (anal, &ctx);
	link = test_function_type_link_at (anal->sdb_types, dog_concrete_addr);
	mu_assert_null (link,
		"A conflicting desired link rolls back every certifying sibling link");
	free (link);
	free (first_link);
	*prototyped = saved_prototyped;
	*dog_prototyped = saved_dog_prototyped;
	r_bin_dwarf_free_debug_info (info);
	RVecDwarfAbbrevDecl_free (abbrevs);
	mu_end;
}

static bool test_dwarf3_exact_frame_pointer_authority(void) {
	mu_assert_true (r_anal_use (anal, "x86"), "Load x86 analysis profile");
	mu_assert_true (r_anal_set_bits (anal, 64), "Select x86-64 analysis");
	sdb_reset (anal->sdb_types);
	RBinFileOptions opt = { 0 };
	mu_assert_true (r_bin_open (bin, "bins/elf/dwarf3_cpp.elf", &opt),
		"dwarf3_cpp.elf binary could not be opened");
	RBinFile *bf = r_bin_cur (bin);
	mu_assert_notnull (bf, "Couldn't get current dwarf3_cpp.elf bin file");
	RVecDwarfAbbrevDecl *abbrevs = r_bin_dwarf_parse_abbrev (bf, MODE);
	mu_assert_notnull (abbrevs, "Couldn't parse DWARF3 abbreviations");
	RBinDwarfDebugInfo *info = r_bin_dwarf_parse_info (bf, abbrevs, MODE);
	mu_assert_notnull (info, "Couldn't parse DWARF3 debug info");
	RBinDwarfCompUnit *unit = RVecDwarfCompUnit_at (info->comp_units, 0);
	mu_assert_notnull (unit, "Missing DWARF3 compilation unit");
	RBinDwarfDie *concrete = test_find_die_at (unit, 0x39c);
	RBinDwarfDie *origin_decl = test_find_die_at (unit, 0x6d);
	RBinDwarfDie *dog_concrete = test_find_die_at (unit, 0x48d);
	RBinDwarfDie *dog_origin_decl = test_find_die_at (unit, 0x14c);
	mu_assert_notnull (concrete, "Missing concrete constructor DIE");
	mu_assert_notnull (origin_decl, "Missing abstract constructor declaration");
	mu_assert_notnull (dog_concrete, "Missing second concrete constructor DIE");
	mu_assert_notnull (dog_origin_decl, "Missing second abstract constructor declaration");
	RBinDwarfAttrValue *origin = test_find_attr (concrete, DW_AT_abstract_origin);
	RBinDwarfAttrValue *frame_base = test_find_attr (concrete, DW_AT_frame_base);
	RBinDwarfAttrValue *high_pc = test_find_attr (concrete, DW_AT_high_pc);
	RBinDwarfAttrValue *prototyped = test_find_attr (origin_decl, DW_AT_decl_column);
	RBinDwarfAttrValue *origin_mutable = test_find_attr (origin_decl, DW_AT_decl_line);
	RBinDwarfAttrValue *dog_low_pc = test_find_attr (dog_concrete, DW_AT_low_pc);
	RBinDwarfAttrValue *dog_frame_base = test_find_attr (dog_concrete, DW_AT_frame_base);
	RBinDwarfAttrValue *dog_prototyped = test_find_attr (dog_origin_decl, DW_AT_decl_column);
	mu_assert_notnull (origin, "Missing concrete abstract origin");
	mu_assert_notnull (frame_base, "Missing concrete frame base");
	mu_assert_notnull (high_pc, "Missing concrete high_pc");
	mu_assert_notnull (prototyped, "Missing mutable abstract declaration attribute");
	mu_assert_notnull (origin_mutable, "Missing second mutable abstract attribute");
	mu_assert_notnull (dog_low_pc, "Missing second concrete low_pc");
	mu_assert_notnull (dog_frame_base, "Missing second concrete frame base");
	mu_assert_notnull (dog_prototyped, "Missing second mutable declaration attribute");
	RBinDwarfAttrValue saved_prototyped = *prototyped;
	prototyped->attr_name = DW_AT_prototyped;
	prototyped->attr_form = DW_FORM_flag;
	prototyped->kind = DW_AT_KIND_FLAG;
	prototyped->flag = true;
	RBinDwarfAttrValue saved_dog_prototyped = *dog_prototyped;
	dog_prototyped->attr_name = DW_AT_prototyped;
	dog_prototyped->attr_form = DW_FORM_flag;
	dog_prototyped->kind = DW_AT_KIND_FLAG;
	dog_prototyped->flag = true;
	RBinDwarfAttrValue saved_frame_base = *frame_base;
	RBinDwarfAttrValue saved_origin_mutable = *origin_mutable;
	RBinDwarfAttrValue saved_high_pc = *high_pc;
	RBinDwarfAttrValue saved_dog_low_pc = *dog_low_pc;
	RBinDwarfAttrValue saved_dog_frame_base = *dog_frame_base;
	ut8 direct_bp[] = { DW_OP_reg6 };
	ut8 direct_sp[] = { DW_OP_reg7 };
	ut8 compound[] = { DW_OP_reg6, DW_OP_reg7 };
	frame_base->kind = DW_AT_KIND_BLOCK;
	frame_base->block.data = direct_bp;
	frame_base->block.length = sizeof (direct_bp);
	RAnalDwarfContext ctx = {
		.info = info,
		.loc = NULL,
	};
	const ut64 concrete_addr = 0x130e;
	r_anal_dwarf_process_info (anal, &ctx);
	RAnalDwarfFramePointerProof *proof = test_current_frame_pointer_proof (
		anal, concrete_addr);
	mu_assert_notnull (proof,
		"Direct concrete RBP frame base publishes exact private authority");
	mu_assert_streq (proof->reg_name, "rbp", "Exact frame pointer uses canonical RBP identity");
	mu_assert_eq (proof->size, 8, "Exact frame pointer carries full register width");
	mu_assert_eq (proof->dwarf_reg_num, 6,
		"Exact frame pointer retains the direct DWARF register ordinal");
	const ut64 exact_offset = proof->offset;
	proof->offset = UT64_MAX;
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Stale profile geometry invalidates the private proof");
	Sdb *dwarf_sdb = sdb_ns (anal->sdb, "dwarf", 0);
	mu_assert_notnull (dwarf_sdb, "Missing parsed DWARF namespace for rebind tests");
	ut64 type_epoch = r_anal_types_dirty_epoch (anal);
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_eq (r_anal_types_dirty_epoch (anal), type_epoch + 1,
		"Geometry rebind bumps the type epoch exactly once");
	proof = test_current_frame_pointer_proof (anal, concrete_addr);
	mu_assert_notnull (proof, "Rebound frame-pointer proof is current");
	mu_assert_eq (proof->offset, exact_offset,
		"Rebind restores canonical register coordinates");

	proof->offset = UT64_MAX;
	proof->dwarf_reg_num = 7;
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_eq (proof->offset, UT64_MAX,
		"A raw stack-pointer ordinal cannot partially rebind geometry");
	proof->dwarf_reg_num = 6;
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Restored raw frame-pointer ordinal rebinds exactly");

	proof->offset = UT64_MAX;
	anal->config->bits = 32;
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_eq (proof->offset, UT64_MAX,
		"A mismatched profile leaves stale geometry unchanged");
	anal->config->bits = 64;
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Restored analysis profile rebinds frame authority");

	char *owned_link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_notnull (owned_link, "Missing owned link for rebind mutations");
	proof->offset = UT64_MAX;
	mu_assert_true (sdb_setf (anal->sdb_types, "foreign_frame_link", 0,
		"fcnlink.%08" PFMT64x, concrete_addr),
		"Mutate the live function link without changing private ownership");
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_eq (proof->offset, UT64_MAX,
		"A mismatched live link leaves stale geometry unchanged");
	mu_assert_true (sdb_setf (anal->sdb_types, owned_link, 0,
		"fcnlink.%08" PFMT64x, concrete_addr), "Restore the exact owned link");
	free (owned_link);
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Restored owned link rebinds frame authority");

	proof->offset = UT64_MAX;
	proof->generation--;
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_eq (proof->offset, UT64_MAX,
		"A stale proof generation leaves geometry unchanged");
	proof->generation = R_ANAL_PRIV (anal)->dwarf_function_link_generation;
	r_anal_dwarf_integrate_functions (anal, flags, dwarf_sdb);
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Restored proof generation rebinds frame authority");

	frame_base->attr_name = DW_AT_decl_line;
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Absent direct frame base publishes no proof");
	origin_mutable->attr_name = DW_AT_frame_base;
	origin_mutable->attr_form = DW_FORM_block1;
	origin_mutable->kind = DW_AT_KIND_BLOCK;
	origin_mutable->block.data = direct_bp;
	origin_mutable->block.length = sizeof (direct_bp);
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Abstract-only frame base publishes no proof");
	*origin_mutable = saved_origin_mutable;
	*frame_base = saved_frame_base;
	frame_base->kind = DW_AT_KIND_BLOCK;
	frame_base->block.data = compound;
	frame_base->block.length = sizeof (compound);
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Compound frame base publishes no proof");
	frame_base->block.data = direct_sp;
	frame_base->block.length = sizeof (direct_sp);
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Direct stack-pointer frame base publishes no proof");
	frame_base->block.data = direct_bp;
	frame_base->block.length = sizeof (direct_bp);
	high_pc->attr_name = DW_AT_frame_base;
	high_pc->attr_form = DW_FORM_block1;
	high_pc->kind = DW_AT_KIND_BLOCK;
	high_pc->block.data = direct_bp;
	high_pc->block.length = sizeof (direct_bp);
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Duplicate direct frame-base attributes publish no proof");
	*high_pc = saved_high_pc;
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Restored direct frame base republishes proof");
	anal->config->bits = 32;
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Changed analysis profile invalidates proof");
	anal->config->bits = 64;
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Restored analysis profile revalidates proof");

	char *link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_notnull (link, "Missing parser-owned frame-pointer function link");
	mu_assert_true (test_set_function_type_link (anal, link, concrete_addr),
		"Ordinary identical write replaces parser ownership");
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Ordinary replacement invalidates parser proof");
	char link_key[SDB_MAX_KEY];
	snprintf (link_key, sizeof (link_key),
		"fcnlink.%08" PFMT64x, concrete_addr);
	mu_assert_true (sdb_unset (anal->sdb_types, link_key, 0),
		"Remove ordinary link before parser reimport");
	free (link);
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Parser reimport restores owned proof");
	const ut64 saved_origin_ref = origin->reference;
	origin->reference = UT64_MAX;
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Failed reparse cannot retain stale proof");
	origin->reference = saved_origin_ref;
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Valid reparse restores exact proof");

	dog_low_pc->address = concrete_addr;
	dog_frame_base->kind = DW_AT_KIND_BLOCK;
	dog_frame_base->block.data = direct_bp;
	dog_frame_base->block.length = sizeof (direct_bp);
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Duplicate function address fails frame authority closed");
	*dog_low_pc = saved_dog_low_pc;
	*dog_frame_base = saved_dog_frame_base;
	r_anal_dwarf_process_info (anal, &ctx);
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Unique function address restores frame proof");

	RAnalPriv *priv = R_ANAL_PRIV (anal);
	RAnalDwarfFunctionLinkAuthority *authority = ht_up_find (
		priv->dwarf_function_link_authority, concrete_addr, NULL);
	proof = ht_up_find (
		priv->dwarf_frame_pointer_proofs, concrete_addr, NULL);
	mu_assert_notnull (authority, "Missing private function-link authority");
	mu_assert_notnull (proof, "Missing private frame-pointer proof");
	priv->dwarf_function_link_generation = UT64_MAX;
	authority->generation = UT64_MAX;
	proof->generation = UT64_MAX;
	mu_assert_notnull (test_current_frame_pointer_proof (anal, concrete_addr),
		"Wrap-adjacent generation starts current");
	RAnalDwarfContext failed_ctx = { 0 };
	r_anal_dwarf_process_info (anal, &failed_ctx);
	mu_assert_null (test_current_frame_pointer_proof (anal, concrete_addr),
		"Generation saturation poisons frame authority");
	link = test_function_type_link_at (anal->sdb_types, concrete_addr);
	mu_assert_null (link,
		"Failed parse revokes saturated owned link instead of laundering it");
	free (link);

	*frame_base = saved_frame_base;
	*prototyped = saved_prototyped;
	*dog_prototyped = saved_dog_prototyped;
	r_bin_dwarf_free_debug_info (info);
	RVecDwarfAbbrevDecl_free (abbrevs);
	mu_end;
}
