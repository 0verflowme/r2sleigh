/* radare2 - LGPL - Copyright 2025 - r2sleigh project */

#include <r_anal.h>
#include <r_core.h>
#include <r_lib.h>
#include <r_version.h>
#include <r_util/r_json.h>
#include <r_util/r_num.h>
#include <r_util/r_str.h>
#include <r_util/r_type.h>
#include <sdb/ht_up.h>
#include <ctype.h>
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

/* FFI declarations for r2sleigh Rust library */
typedef struct R2ILContext R2ILContext;
typedef struct R2ILBlock R2ILBlock;

/* Context management */
extern R2ILContext *r2il_arch_init(const char *arch);
extern void r2il_free(R2ILContext *ctx);
extern int r2il_is_loaded(const R2ILContext *ctx);
extern const char *r2il_arch_name(const R2ILContext *ctx);
extern const char *r2il_error(const R2ILContext *ctx);

/* Lifting */
extern R2ILBlock *r2il_lift(R2ILContext *ctx, const unsigned char *bytes, size_t len, unsigned long long addr);
extern R2ILBlock *r2il_lift_block(R2ILContext *ctx, const unsigned char *bytes, size_t len, unsigned long long addr, unsigned int block_size);
extern void r2il_block_rewrite_layout(R2ILBlock *block, unsigned long long addr, unsigned int size);
extern R2ILBlock *r2il_block_new_branch(unsigned long long addr, unsigned int size, unsigned long long target, unsigned int target_size);
extern void r2il_set_semantic_metadata_enabled(R2ILContext *ctx, bool enabled);
extern void r2il_block_free(R2ILBlock *block);
extern int r2il_block_validate(R2ILContext *ctx, const R2ILBlock *block);
extern void r2il_block_set_switch_info(R2ILBlock *block, unsigned long long switch_addr,
    unsigned long long min_val, unsigned long long max_val, unsigned long long default_target,
    const unsigned long long *case_values, const unsigned long long *case_targets, size_t num_cases);

/* Block inspection */
extern size_t r2il_block_op_count(const R2ILBlock *block);
extern unsigned int r2il_block_size(const R2ILBlock *block);
extern unsigned long long r2il_block_addr(const R2ILBlock *block);
extern unsigned int r2il_block_type(const R2ILBlock *block);
extern unsigned long long r2il_block_jump(const R2ILBlock *block);
extern unsigned long long r2il_block_fail(const R2ILBlock *block);
extern bool r2il_block_has_trailing_indirect_branch(const R2ILBlock *block);

/* ESIL/mnemonic */
extern char *r2il_block_to_esil(const R2ILContext *ctx, const R2ILBlock *block);
extern char *r2il_block_mnemonic(const R2ILContext *ctx, const unsigned char *bytes, size_t len, unsigned long long addr);
extern char *r2il_block_op_json_named(const R2ILContext *ctx, const R2ILBlock *block, size_t index);
extern void r2il_string_free(char *s);

/* Typed analysis */
extern char *r2il_block_regs_read(const R2ILContext *ctx, const R2ILBlock *block);
extern char *r2il_block_regs_write(const R2ILContext *ctx, const R2ILBlock *block);
extern char *r2il_block_mem_access(const R2ILContext *ctx, const R2ILBlock *block);
extern char *r2il_block_varnodes(const R2ILContext *ctx, const R2ILBlock *block);

/* SSA analysis (instruction-level) */
extern char *r2il_block_to_ssa_json(const R2ILContext *ctx, const R2ILBlock *block);
extern char *r2il_block_defuse_json(const R2ILContext *ctx, const R2ILBlock *block);

/* SSA analysis (function-level) */
extern char *r2ssa_function_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks);
extern char *r2ssa_function_opt_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks);
extern char *r2ssa_defuse_function_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks);
extern char *r2ssa_domtree_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks);
extern char *r2ssa_backward_slice_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks, const char *var_name);
extern char *r2taint_function_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks);
extern char *r2taint_function_summary_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks);
extern char *r2taint_sources_sinks_json(const char *json);

/* Symbolic execution */
extern char *r2sym_function(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks, unsigned long long entry_addr);
extern char *r2sym_paths(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks, unsigned long long entry_addr);
extern char *r2sym_explore_to(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks,
	unsigned long long entry_addr, unsigned long long target_addr);
extern char *r2sym_solve_to(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks,
	unsigned long long entry_addr, unsigned long long target_addr);
extern int r2sym_set_symbol_map_json(const char *json);
extern int r2sym_merge_is_enabled(void);
extern void r2sym_merge_set_enabled(int enabled);

/* Decompiler */
extern char *r2dec_function_with_context(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks,
                                          const char *func_name, const char *func_names_json,
                                          const char *strings_json, const char *symbols_json,
                                          const char *external_context_json);

/* CFG */
extern char *r2cfg_function_ascii(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks);
extern char *r2cfg_function_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks);
extern char *r2il_get_reg_profile(const R2ILContext *ctx);

/* radare2 Deep Integration */
extern int r2sleigh_analyze_fcn(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks, unsigned long long fcn_addr);
extern char *r2sleigh_analyze_fcn_annotations(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks, unsigned long long fcn_addr);
extern char *r2sleigh_recover_vars(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks, unsigned long long fcn_addr);
extern char *r2sleigh_get_data_refs(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks, unsigned long long fcn_addr);
extern char *r2sleigh_infer_signature_cc_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks,
	unsigned long long fcn_addr, const char *fcn_name);
extern char *r2sleigh_infer_type_writeback_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks,
	unsigned long long fcn_addr, const char *fcn_name, const char *external_context_json);
extern char *r2sleigh_infer_type_writeback_json_ex(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks,
	unsigned long long fcn_addr, const char *fcn_name, const char *external_context_json,
	size_t interproc_iter, size_t interproc_max_iters, int interproc_converged, const char *interproc_scope_json);
extern char *r2sleigh_get_direct_call_targets_json(const R2ILContext *ctx, const R2ILBlock **blocks, size_t num_blocks,
	unsigned long long fcn_addr, const char *fcn_name);
extern int r2sleigh_alias_function_analysis_artifact_cache(const R2ILContext *ctx, const R2ILBlock **blocks,
	size_t num_blocks, unsigned long long fcn_addr, const char *fcn_name,
	const char *source_external_context_json, const char *target_external_context_json);
/* Per-architecture context (lazy init)
 *
 * WARNING: These globals are NOT thread-safe. This plugin assumes
 * single-threaded radare2 usage. If radare2 becomes multi-threaded,
 * this code must be updated with proper synchronization (e.g., mutex).
 */
static R2ILContext *sleigh_ctx = NULL;
static char *sleigh_arch = NULL;
static char *sleigh_arch_override = NULL;

typedef struct {
	bool has_state;
	char *mode;
	ut64 function_addr;
	ut64 entry_addr;
	ut64 target_addr;
	char *result_json;
} SymStateCache;

static SymStateCache sym_state_cache = {0};
static RVecAnalRef *sleigh_get_data_refs(RAnal *anal, RAnalFunction *fcn);
static int collect_data_refs_from_json(RAnal *anal, RAnalFunction *fcn, const char *json, RVecAnalRef *refs, bool apply_to_anal);

typedef RAnalFcnContext *(*SleighFunctionContextCollectFn)(RAnal *anal, RAnalFunction *fcn);
typedef void (*SleighFunctionContextFreeFn)(RAnalFcnContext *ctx);

typedef struct {
	bool resolved;
	bool available;
	bool warned;
	SleighFunctionContextCollectFn collect;
	SleighFunctionContextFreeFn free;
} SleighFunctionContextApi;

static SleighFunctionContextApi sleigh_function_context_api = {0};

typedef enum {
	SLEIGH_MODE_FULL = 0,
	SLEIGH_MODE_BALANCED = 1,
	SLEIGH_MODE_FAST = 2,
} SleighMode;

typedef struct {
	size_t contiguous_run;
	size_t small_values;
	size_t num_cases;
	size_t unique_targets;
	size_t inverse_outliers;
} SwitchScore;

typedef struct {
	ut64 addr;
	unsigned depth;
} SwitchQueueEntry;

typedef enum {
	SLEIGH_TYPE_WRITEBACK_OFF = 0,
	SLEIGH_TYPE_WRITEBACK_BALANCED = 1,
	SLEIGH_TYPE_WRITEBACK_AGGRESSIVE = 2,
} SleighTypeWritebackMode;

typedef struct {
	ut64 addr;
	ut64 key;
	ut64 payload_hash;
	ut64 dep_hash;
	ut64 applied_hash;
	char *payload_json;
} TypeWritebackCacheEntry;

typedef struct {
	ut64 addr;
	ut64 key;
	ut64 payload_hash;
	int ref_count;
} DataRefCacheEntry;

static TypeWritebackCacheEntry *type_writeback_cache = NULL;
static size_t type_writeback_cache_count = 0;
static size_t type_writeback_cache_capacity = 0;
static HtUP *type_writeback_cache_index = NULL;
static DataRefCacheEntry *data_ref_cache = NULL;
static size_t data_ref_cache_count = 0;
static size_t data_ref_cache_capacity = 0;
static HtUP *data_ref_cache_index = NULL;

typedef struct {
	ut64 key;
	bool imported;
} StructDeclMemoEntry;

static StructDeclMemoEntry *struct_decl_memo = NULL;
static size_t struct_decl_memo_count = 0;
static size_t struct_decl_memo_capacity = 0;

/* Minimum bytes to pass to libsla (it reads ahead for variable-length instructions) */
#define SLEIGH_MIN_BYTES 16
#define SLEIGH_LIFT_BLOCK_MAX_ALLOC (1024 * 1024)
#define SLEIGH_TAINT_MAX_BLOCKS 200
#define SLEIGH_SIG_WRITEBACK_MAX_BLOCKS 200
#define SLEIGH_SIG_WRITEBACK_GLOBAL_MAX_FCNS 128
#define SLEIGH_SIG_MIN_CONFIDENCE 70
#define SLEIGH_CC_MIN_CONFIDENCE 80
#define SLEIGH_TYPE_MIN_CONF_DEFAULT 85
#define SLEIGH_TYPE_RENAME_MIN_CONF_DEFAULT 93
#define SLEIGH_TYPE_STRUCT_MIN_CONF_DEFAULT 85
#define SLEIGH_TYPE_INTERPROC_MAX_ITERS_DEFAULT 12
#define SLEIGH_TYPE_MAX_BLOCKS_DEFAULT 500
#define SLEIGH_TYPE_WRITEBACK_GLOBAL_MAX_FCNS 128
#define SLEIGH_TYPE_GLOBAL_MAX_LINKS_DEFAULT 128
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
} BlockArray;

static char *build_type_interproc_scope_json(
	RCore *core,
	RAnal *anal,
	R2ILContext *ctx,
	RAnalFunction *fcn,
	const BlockArray *blocks
);

static bool warm_type_payload_cache_for_function(
	RCore *core,
	RAnal *anal,
	R2ILContext *ctx,
	RAnalFunction *fcn,
	int max_iters,
	ut64 **seen_addrs,
	size_t *seen_count,
	size_t *seen_cap
);

static RVecAnalRef *get_function_call_refs(RCore *core, RAnal *anal, RAnalFunction *fcn);
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
}

static void block_array_push(BlockArray *arr, R2ILBlock *block) {
	if (arr->count >= arr->capacity) {
		arr->capacity = arr->capacity ? arr->capacity * 2 : 8;
		arr->blocks = realloc (arr->blocks, arr->capacity * sizeof (R2ILBlock *));
	}
	arr->blocks[arr->count++] = block;
}

static void block_array_free(BlockArray *arr) {
	size_t i;
	for (i = 0; i < arr->count; i++) {
		r2il_block_free (arr->blocks[i]);
	}
	free (arr->blocks);
	arr->blocks = NULL;
	arr->count = 0;
	arr->capacity = 0;
}

static ut64 sleigh_hash_mix(ut64 hash, ut64 value) {
	hash ^= value + 0x9e3779b97f4a7c15ULL + (hash << 6) + (hash >> 2);
	return hash;
}

static ut64 compute_block_array_hash(const BlockArray *blocks) {
	size_t i;
	ut64 hash = 0xcbf29ce484222325ULL;

	if (!blocks) {
		return 0;
	}
	hash = sleigh_hash_mix (hash, blocks->count);
	for (i = 0; i < blocks->count; i++) {
		const R2ILBlock *block = blocks->blocks[i];
		hash = sleigh_hash_mix (hash, r2il_block_addr (block));
		hash = sleigh_hash_mix (hash, r2il_block_size (block));
		hash = sleigh_hash_mix (hash, r2il_block_op_count (block));
		hash = sleigh_hash_mix (hash, r2il_block_type (block));
		hash = sleigh_hash_mix (hash, r2il_block_jump (block));
		hash = sleigh_hash_mix (hash, r2il_block_fail (block));
	}
	return hash;
}

static ut64 compute_xref_cache_key(RAnalFunction *fcn, const BlockArray *blocks, SleighMode mode) {
	ut64 key = fcn? fcn->addr: 0;
	int bb_count = (fcn && fcn->bbs)? r_list_length (fcn->bbs): 0;
	int linear_size = fcn? r_anal_function_linear_size (fcn): 0;

	key = sleigh_hash_mix (key, (ut64)bb_count);
	key = sleigh_hash_mix (key, (ut64)linear_size);
	key = sleigh_hash_mix (key, compute_block_array_hash (blocks));
	key = sleigh_hash_mix (key, (ut64)mode);
	return key;
}

static const char *function_context_var_kind_name(bool is_register) {
	if (is_register) {
		return "register";
	}
	return "stack";
}

static const char *function_context_stack_base_name(RAnalFcnSlotBase base, const char *base_name) {
	if (base_name) {
		return base_name;
	}
	switch (base) {
	case R_ANAL_FCN_BASE_BP:
		return "bp";
	case R_ANAL_FCN_BASE_SP:
		return "sp";
	default:
		return NULL;
	}
}

static const char *function_context_stack_slot_role_name(RAnalFcnSlotRole role) {
	switch (role) {
	case R_ANAL_FCN_SLOT_LOCAL:
		return "local";
	case R_ANAL_FCN_SLOT_ARG:
		return "stack_arg";
	case R_ANAL_FCN_SLOT_HOME:
		return "param_home";
	case R_ANAL_FCN_SLOT_UNKNOWN:
	default:
		return "unknown";
	}
}

static const char *base_type_kind_name(RAnalBaseTypeKind kind) {
	switch (kind) {
	case R_ANAL_BASE_TYPE_KIND_STRUCT:
		return "struct";
	case R_ANAL_BASE_TYPE_KIND_UNION:
		return "union";
	case R_ANAL_BASE_TYPE_KIND_ENUM:
		return "enum";
	case R_ANAL_BASE_TYPE_KIND_TYPEDEF:
		return "typedef";
	case R_ANAL_BASE_TYPE_KIND_ATOMIC:
		return "atomic";
	default:
		return "atomic";
	}
}

static void append_function_context_base_type(PJ *pj, const RAnalBaseType *type) {
	if (!pj || !type || R_STR_ISEMPTY (type->name)) {
		return;
	}
	pj_o (pj);
	pj_ks (pj, "kind", base_type_kind_name (type->kind));
	pj_ks (pj, "name", type->name);
	if (type->type) {
		pj_ks (pj, "type", type->type);
	}
	if (type->size) {
		pj_ki (pj, "size_bits", (ut64)type->size);
	}
	if (type->kind == R_ANAL_BASE_TYPE_KIND_STRUCT || type->kind == R_ANAL_BASE_TYPE_KIND_UNION) {
		pj_k (pj, "members");
		pj_a (pj);
		if (type->kind == R_ANAL_BASE_TYPE_KIND_STRUCT) {
			RAnalStructMember *member;
			R_VEC_FOREACH (&type->struct_data.members, member) {
				pj_o (pj);
				pj_ks (pj, "name", member->name);
				pj_ks (pj, "type", member->type? member->type: "void *");
				pj_ki (pj, "offset", (ut64)member->offset);
				if (member->size) {
					pj_ki (pj, "size_bits", (ut64)member->size);
				}
				pj_end (pj);
			}
		} else {
			RAnalUnionMember *member;
			R_VEC_FOREACH (&type->union_data.members, member) {
				pj_o (pj);
				pj_ks (pj, "name", member->name);
				pj_ks (pj, "type", member->type? member->type: "void *");
				pj_ki (pj, "offset", (ut64)member->offset);
				if (member->size) {
					pj_ki (pj, "size_bits", (ut64)member->size);
				}
				pj_end (pj);
			}
		}
		pj_end (pj);
	} else if (type->kind == R_ANAL_BASE_TYPE_KIND_ENUM) {
		pj_k (pj, "variants");
		pj_a (pj);
		RAnalEnumCase *cas;
		R_VEC_FOREACH (&type->enum_data.cases, cas) {
			pj_o (pj);
			pj_ks (pj, "name", cas->name);
			pj_ki (pj, "value", cas->val);
			pj_end (pj);
		}
		pj_end (pj);
	}
	pj_end (pj);
}

static char *sleigh_collect_external_context_json(RAnal *anal, RAnalFunction *fcn) {
	if (!anal || !fcn) {
		return strdup ("{}");
	}
	if (!sleigh_function_context_api.available || !sleigh_function_context_api.collect || !sleigh_function_context_api.free) {
		return strdup ("{}");
	}
	RAnalFcnContext *ctx = sleigh_function_context_api.collect (anal, fcn);
	RList *base_types = r_anal_types_baselist (anal);

	PJ *pj = pj_new ();
	if (!pj) {
		r_list_free (base_types);
		sleigh_function_context_api.free (ctx);
		return strdup ("{}");
	}

	pj_o (pj);
	pj_k (pj, "signature");
	pj_o (pj);
	if (fcn->name) {
		pj_ks (pj, "name", fcn->name);
	}
	if (ctx && ctx->signature && ctx->signature->ret_type) {
		pj_ks (pj, "ret", ctx->signature->ret_type);
	}
	if (ctx && ctx->signature && ctx->signature->callconv) {
		pj_ks (pj, "callconv", ctx->signature->callconv);
	}
	if (ctx && ctx->signature && ctx->signature->noreturn) {
		pj_kb (pj, "noreturn", true);
	}
	pj_k (pj, "params");
	pj_a (pj);
	RListIter *iter;
	RAnalFunctionParam *param;
	if (ctx && ctx->signature && ctx->signature->params) {
		r_list_foreach (ctx->signature->params, iter, param) {
			pj_o (pj);
			if (param->name) {
				pj_ks (pj, "name", param->name);
			}
			if (param->type) {
				pj_ks (pj, "type", param->type);
			}
			pj_end (pj);
		}
	}
	pj_end (pj);
	pj_end (pj);

	pj_k (pj, "vars");
	pj_a (pj);
	RAnalFcnRegArg *reg_arg;
	if (ctx && ctx->reg_args) {
		r_list_foreach (ctx->reg_args, iter, reg_arg) {
			pj_o (pj);
			pj_ks (pj, "kind", function_context_var_kind_name (true));
			if (reg_arg->name) {
				pj_ks (pj, "name", reg_arg->name);
			}
			if (reg_arg->type) {
				pj_ks (pj, "type", reg_arg->type);
			}
			if (reg_arg->reg) {
				pj_ks (pj, "reg", reg_arg->reg);
			}
			if (reg_arg->arg_index >= 0) {
				pj_ki (pj, "param_index", (ut64)reg_arg->arg_index);
				pj_kb (pj, "is_arg", true);
			}
			pj_end (pj);
		}
	}
	RAnalFcnSlot *slot;
	if (ctx && ctx->slots) {
		r_list_foreach (ctx->slots, iter, slot) {
			const char *base = function_context_stack_base_name (slot->base, slot->base_name);
			const bool is_arg = slot->role == R_ANAL_FCN_SLOT_ARG
				|| slot->role == R_ANAL_FCN_SLOT_HOME;
		pj_o (pj);
			pj_ks (pj, "kind", function_context_var_kind_name (false));
			if (slot->name) {
				pj_ks (pj, "name", slot->name);
			}
			if (slot->type) {
				pj_ks (pj, "type", slot->type);
			}
			if (base) {
				pj_ks (pj, "base", base);
			}
			pj_ks (pj, "role", function_context_stack_slot_role_name (slot->role));
			pj_kb (pj, "is_arg", is_arg);
			pj_ki (pj, "offset", slot->offset);
			if (slot->arg_index >= 0) {
				pj_ki (pj, "param_index", (ut64)slot->arg_index);
			}
			if (slot->arg_name) {
				pj_ks (pj, "param_name", slot->arg_name);
			}
			if (slot->home_reg) {
				pj_ks (pj, "source_reg", slot->home_reg);
			}
			pj_end (pj);
		}
	}
	pj_end (pj);

	pj_k (pj, "base_types");
	pj_a (pj);
	RAnalBaseType *type;
	if (base_types) {
		r_list_foreach (base_types, iter, type) {
			append_function_context_base_type (pj, type);
		}
	}
	pj_end (pj);
	pj_end (pj);

	char *json = pj_drain (pj);
	r_list_free (base_types);
	sleigh_function_context_api.free (ctx);
	return json? json: strdup ("{}");
}

static bool sleigh_resolve_function_context_api(void) {
	if (sleigh_function_context_api.resolved) {
		return sleigh_function_context_api.available;
	}
	sleigh_function_context_api.resolved = true;
	sleigh_function_context_api.collect = (SleighFunctionContextCollectFn)dlsym (RTLD_DEFAULT, "r_anal_function_context_collect");
	sleigh_function_context_api.free = (SleighFunctionContextFreeFn)dlsym (RTLD_DEFAULT, "r_anal_function_context_free");
	sleigh_function_context_api.available = sleigh_function_context_api.collect && sleigh_function_context_api.free;
	return sleigh_function_context_api.available;
}

static void sleigh_report_missing_function_context_api(void) {
	if (sleigh_function_context_api.warned) {
		return;
	}
	sleigh_function_context_api.warned = true;
	const char *msg =
		"r2sleigh: incompatible radare2 runtime: missing typed function-context API "
		"(r_anal_function_context_collect / r_anal_function_context_free). "
		"Use the matching radare2 build or upgrade the installed radare2.";
	fprintf (stderr, "%s\n", msg);
	R_LOG_ERROR ("%s", msg);
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

static void type_writeback_cache_clear(void) {
	size_t i;
	for (i = 0; i < type_writeback_cache_count; i++) {
		free (type_writeback_cache[i].payload_json);
	}
	free (type_writeback_cache);
	type_writeback_cache = NULL;
	type_writeback_cache_count = 0;
	type_writeback_cache_capacity = 0;
	ht_up_free (type_writeback_cache_index);
	type_writeback_cache_index = NULL;
}

static void data_ref_cache_clear(void) {
	free (data_ref_cache);
	data_ref_cache = NULL;
	data_ref_cache_count = 0;
	data_ref_cache_capacity = 0;
	ht_up_free (data_ref_cache_index);
	data_ref_cache_index = NULL;
}

static void struct_decl_memo_clear(void) {
	free (struct_decl_memo);
	struct_decl_memo = NULL;
	struct_decl_memo_count = 0;
	struct_decl_memo_capacity = 0;
}

static bool struct_decl_memo_get(ut64 key, bool *imported) {
	size_t i;
	for (i = 0; i < struct_decl_memo_count; i++) {
		if (struct_decl_memo[i].key == key) {
			if (imported) {
				*imported = struct_decl_memo[i].imported;
			}
			return true;
		}
	}
	return false;
}

static void struct_decl_memo_put(ut64 key, bool imported) {
	size_t i;
	StructDeclMemoEntry *next;

	for (i = 0; i < struct_decl_memo_count; i++) {
		if (struct_decl_memo[i].key == key) {
			struct_decl_memo[i].imported = imported;
			return;
		}
	}

	if (struct_decl_memo_count >= struct_decl_memo_capacity) {
		size_t new_capacity = struct_decl_memo_capacity ? struct_decl_memo_capacity * 2 : 256;
		next = realloc (struct_decl_memo, new_capacity * sizeof (StructDeclMemoEntry));
		if (!next) {
			return;
		}
		struct_decl_memo = next;
		struct_decl_memo_capacity = new_capacity;
	}

	struct_decl_memo[struct_decl_memo_count].key = key;
	struct_decl_memo[struct_decl_memo_count].imported = imported;
	struct_decl_memo_count++;
}

static DataRefCacheEntry *data_ref_cache_get(ut64 addr) {
	size_t i;
	bool found = false;
	void *encoded_index;

	if (data_ref_cache_index) {
		encoded_index = ht_up_find (data_ref_cache_index, addr, &found);
		if (found) {
			size_t idx_plus_one = (size_t)encoded_index;
			if (idx_plus_one > 0) {
				size_t idx = idx_plus_one - 1;
				if (idx < data_ref_cache_count && data_ref_cache[idx].addr == addr) {
					return &data_ref_cache[idx];
				}
			}
		}
	}

	for (i = 0; i < data_ref_cache_count; i++) {
		if (data_ref_cache[i].addr == addr) {
			if (data_ref_cache_index) {
				ht_up_insert (data_ref_cache_index, addr, (void *)(size_t)(i + 1));
			}
			return &data_ref_cache[i];
		}
	}
	return NULL;
}

static bool data_ref_cache_put(ut64 addr, ut64 key, ut64 payload_hash, int ref_count) {
	DataRefCacheEntry *entry = data_ref_cache_get (addr);
	DataRefCacheEntry *next;

	if (entry) {
		entry->key = key;
		entry->payload_hash = payload_hash;
		entry->ref_count = ref_count;
		return true;
	}

	if (data_ref_cache_count >= data_ref_cache_capacity) {
		size_t new_capacity = data_ref_cache_capacity ? data_ref_cache_capacity * 2 : 256;
		next = realloc (data_ref_cache, new_capacity * sizeof (DataRefCacheEntry));
		if (!next) {
			return false;
		}
		data_ref_cache = next;
		data_ref_cache_capacity = new_capacity;
	}

	data_ref_cache[data_ref_cache_count].addr = addr;
	data_ref_cache[data_ref_cache_count].key = key;
	data_ref_cache[data_ref_cache_count].payload_hash = payload_hash;
	data_ref_cache[data_ref_cache_count].ref_count = ref_count;
	if (!data_ref_cache_index) {
		data_ref_cache_index = ht_up_new0 ();
	}
	if (data_ref_cache_index) {
		ht_up_insert (data_ref_cache_index, addr, (void *)(size_t)(data_ref_cache_count + 1));
	}
	data_ref_cache_count++;
	return true;
}

static TypeWritebackCacheEntry *type_writeback_cache_get(ut64 addr) {
	size_t i;
	bool found = false;
	void *encoded_index;

	if (type_writeback_cache_index) {
		encoded_index = ht_up_find (type_writeback_cache_index, addr, &found);
		if (found) {
			size_t idx_plus_one = (size_t)encoded_index;
			if (idx_plus_one > 0) {
				size_t idx = idx_plus_one - 1;
				if (idx < type_writeback_cache_count && type_writeback_cache[idx].addr == addr) {
					return &type_writeback_cache[idx];
				}
			}
		}
	}

	for (i = 0; i < type_writeback_cache_count; i++) {
		if (type_writeback_cache[i].addr == addr) {
			if (type_writeback_cache_index) {
				ht_up_insert (type_writeback_cache_index, addr, (void *)(size_t)(i + 1));
			}
			return &type_writeback_cache[i];
		}
	}
	return NULL;
}

static bool is_caller_propagation_ref_type(RAnalRefType type);

static bool type_writeback_cache_put(ut64 addr, ut64 key, ut64 dep_hash, ut64 payload_hash, ut64 applied_hash, const char *payload_json) {
	TypeWritebackCacheEntry *entry = type_writeback_cache_get (addr);
	TypeWritebackCacheEntry *next;
	char *payload_dup = payload_json? strdup (payload_json): NULL;

	if (entry) {
		free (entry->payload_json);
		entry->key = key;
		entry->payload_hash = payload_hash;
		entry->dep_hash = dep_hash;
		entry->applied_hash = applied_hash;
		entry->payload_json = payload_dup;
		return true;
	}

	if (type_writeback_cache_count >= type_writeback_cache_capacity) {
		size_t new_capacity = type_writeback_cache_capacity ? type_writeback_cache_capacity * 2 : 256;
		next = realloc (type_writeback_cache, new_capacity * sizeof (TypeWritebackCacheEntry));
		if (!next) {
			free (payload_dup);
			return false;
		}
		type_writeback_cache = next;
		type_writeback_cache_capacity = new_capacity;
	}

	type_writeback_cache[type_writeback_cache_count].addr = addr;
	type_writeback_cache[type_writeback_cache_count].key = key;
	type_writeback_cache[type_writeback_cache_count].payload_hash = payload_hash;
	type_writeback_cache[type_writeback_cache_count].dep_hash = dep_hash;
	type_writeback_cache[type_writeback_cache_count].applied_hash = applied_hash;
	type_writeback_cache[type_writeback_cache_count].payload_json = payload_dup;
	if (!type_writeback_cache_index) {
		type_writeback_cache_index = ht_up_new0 ();
	}
	if (type_writeback_cache_index) {
		ht_up_insert (type_writeback_cache_index, addr, (void *)(size_t)(type_writeback_cache_count + 1));
	}
	type_writeback_cache_count++;
	return true;
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
	size_t *out_bb_size
) {
	size_t bb_size;
	size_t read_len;
	ut8 *buf;

	R_RETURN_VAL_IF_FAIL (anal && bb && out_buf && out_len && out_bb_size, false);

	if (!bb->size) {
		return false;
	}
	if ((ut64)bb->size > (ut64)SLEIGH_LIFT_BLOCK_MAX_ALLOC) {
		R_LOG_ERROR (
			"r2sleigh: refusing to allocate %"PFMT64u" bytes for block at 0x%"PFMT64x,
			(ut64)bb->size,
			bb->addr
		);
		return false;
	}

	bb_size = (size_t)bb->size;
	read_len = R_MAX (bb_size, (size_t)SLEIGH_MIN_BYTES);
	buf = calloc (1, read_len);
	if (!buf) {
		return false;
	}
	if (!anal->iob.read_at (anal->iob.io, bb->addr, buf, bb_size)) {
		free (buf);
		return false;
	}

	*out_buf = buf;
	*out_len = read_len;
	*out_bb_size = bb_size;
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

static RAnalFunction *resolve_function_target(RCore *core, RAnal *anal, const char *target_arg) {
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
	return r_anal_get_fcn_in (anal, target_addr, R_ANAL_FCN_TYPE_ANY);
}

static char *build_sym_symbol_map_json(RCore *core) {
	if (!core) {
		return strdup ("{}");
	}

	PJ *pj = pj_new ();
	if (!pj) {
		return strdup ("{}");
	}
	pj_o (pj);

	/* aflj: [{addr:0x...,name:"..."}] */
	char *aflj = r_core_cmd_str (core, "aflj");
	if (aflj && aflj[0] == '[') {
		RJson *root = r_json_parse (aflj);
		if (root && root->type == R_JSON_ARRAY) {
			RJson *elem;
			for (elem = root->children.first; elem; elem = elem->next) {
				if (elem->type != R_JSON_OBJECT) {
					continue;
				}
				const RJson *addr = r_json_get (elem, "addr");
				const RJson *name = r_json_get (elem, "name");
				if (addr && name && addr->type == R_JSON_INTEGER && name->type == R_JSON_STRING && name->str_value) {
					char key[32];
					snprintf (key, sizeof (key), "0x%llx", (unsigned long long)addr->num.u_value);
					pj_ks (pj, key, name->str_value);
				}
			}
			r_json_free (root);
		}
	}
	free (aflj);

	/* fs *;fj: include import/plt flags such as sym.imp.memcpy */
	char *fj = r_core_cmd_str (core, "fs *;fj");
	if (fj && fj[0] == '[') {
		RJson *root = r_json_parse (fj);
		if (root && root->type == R_JSON_ARRAY) {
			RJson *elem;
			for (elem = root->children.first; elem; elem = elem->next) {
				if (elem->type != R_JSON_OBJECT) {
					continue;
				}
				const RJson *addr = r_json_get (elem, "addr");
				const RJson *name = r_json_get (elem, "name");
				if (addr && name && addr->type == R_JSON_INTEGER && name->type == R_JSON_STRING && name->str_value) {
					char key[32];
					snprintf (key, sizeof (key), "0x%llx", (unsigned long long)addr->num.u_value);
					pj_ks (pj, key, name->str_value);
				}
			}
			r_json_free (root);
		}
	}
	free (fj);

	pj_end (pj);
	return pj_drain (pj);
}

static bool ssa_var_to_reg_name(const char *ssa_name, char *out, size_t out_size) {
	if (!ssa_name || !out || out_size == 0) {
		return false;
	}

	const char *suffix = strrchr (ssa_name, '_');
	size_t len = suffix ? (size_t)(suffix - ssa_name) : strlen (ssa_name);
	if (len == 0 || len >= out_size) {
		return false;
	}

	char base[128];
	if (len >= sizeof (base)) {
		return false;
	}
	memcpy (base, ssa_name, len);
	base[len] = '\0';

	if (r_str_startswith (base, "const:") ||
		r_str_startswith (base, "tmp:") ||
		r_str_startswith (base, "ram:") ||
		r_str_startswith (base, "space")) {
		return false;
	}

	const char *name = base;
	if (r_str_startswith (base, "reg:")) {
		name = base + 4;
	}

	r_str_ncpy (out, name, out_size);
	return out[0] != '\0';
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

static void add_ssa_reg_values(RAnal *anal, const RJson *array, RVecRArchValue *vec, int access) {
	size_t i;

	if (!anal || !array || array->type != R_JSON_ARRAY || !vec) {
		return;
	}

	for (i = 0; i < array->children.count; i++) {
		const RJson *item = r_json_item (array, i);
		if (!item || item->type != R_JSON_STRING || !item->str_value) {
			continue;
		}

		char regbuf[64];
		if (!ssa_var_to_reg_name (item->str_value, regbuf, sizeof (regbuf))) {
			continue;
		}

		RRegItem *reg = r_reg_get (anal->reg, regbuf, -1);
		if (!reg) {
			char alt[64];
			r_str_ncpy (alt, regbuf, sizeof (alt));
			r_str_case (alt, false);
			reg = r_reg_get (anal->reg, alt, -1);
		}
		if (!reg) {
			char alt[64];
			r_str_ncpy (alt, regbuf, sizeof (alt));
			r_str_case (alt, true);
			reg = r_reg_get (anal->reg, alt, -1);
		}
		if (!reg || !reg->name || vec_has_reg (vec, reg->name)) {
			continue;
		}

		RArchValue value = {0};
		value.type = R_ANAL_VAL_REG;
		value.reg = reg->name;
		value.access = access;
		RVecRArchValue_push_back (vec, &value);
	}
}

static void add_memory_archvalue(RAnal *anal, const RJson *mem_access, RVecRArchValue *vec, int access) {
	if (!anal || !mem_access || mem_access->type != R_JSON_OBJECT || !vec) {
		return;
	}

	const RJson *type = r_json_get (mem_access, "type");
	const RJson *size = r_json_get (mem_access, "size");
	const RJson *addr = r_json_get (mem_access, "addr_detail");
	if (!addr || addr->type != R_JSON_OBJECT) {
		const RJson *addr_alt = r_json_get (mem_access, "addr");
		if (addr_alt && addr_alt->type == R_JSON_OBJECT) {
			addr = addr_alt;
		}
	}

	if (!type || !type->str_value || !size) {
		return;
	}

	RArchValue value = {0};
	value.type = R_ANAL_VAL_MEM;
	value.access = access;

	// Set memory size and reference
	value.memref = (size->type == R_JSON_INTEGER) ? size->num.u_value : 1;

	// Parse address information
	if (addr && addr->type == R_JSON_OBJECT) {
		const RJson *addr_space = r_json_get (addr, "space");
		const RJson *addr_offset = r_json_get (addr, "offset");
		const RJson *addr_name = r_json_get (addr, "name");

		if (addr_space && addr_space->str_value &&
			r_str_casecmp (addr_space->str_value, "register") == 0 &&
			addr_name && addr_name->str_value) {
			// Register-based memory access
			RRegItem *reg = r_reg_get (anal->reg, addr_name->str_value, -1);
			if (!reg) {
				char alt[64];
				r_str_ncpy (alt, addr_name->str_value, sizeof (alt));
				r_str_case (alt, false);
				reg = r_reg_get (anal->reg, alt, -1);
			}
			if (!reg) {
				char alt[64];
				r_str_ncpy (alt, addr_name->str_value, sizeof (alt));
				r_str_case (alt, true);
				reg = r_reg_get (anal->reg, alt, -1);
			}
			if (reg && reg->name) {
				value.reg = reg->name;
			}
			value.base = 0; // Will be calculated by radare2 from register
			value.delta = (addr_offset && addr_offset->type == R_JSON_INTEGER) ? addr_offset->num.s_value : 0;
		} else if (addr_offset && addr_offset->type == R_JSON_INTEGER) {
			// Absolute memory access
			value.reg = NULL;
			value.base = addr_offset->num.u_value;
			value.delta = 0;
		}
	}

	if (!value.reg) {
		const RJson *stack_base = r_json_get (mem_access, "stack_base");
		const RJson *stack_offset = r_json_get (mem_access, "stack_offset");
		if (stack_base && stack_base->str_value) {
			RRegItem *reg = r_reg_get (anal->reg, stack_base->str_value, -1);
			if (!reg) {
				char alt[64];
				r_str_ncpy (alt, stack_base->str_value, sizeof (alt));
				r_str_case (alt, false);
				reg = r_reg_get (anal->reg, alt, -1);
			}
			if (!reg) {
				char alt[64];
				r_str_ncpy (alt, stack_base->str_value, sizeof (alt));
				r_str_case (alt, true);
				reg = r_reg_get (anal->reg, alt, -1);
			}
			if (reg && reg->name) {
				value.reg = reg->name;
				value.base = 0;
				value.delta = (stack_offset && stack_offset->type == R_JSON_INTEGER)
					? stack_offset->num.s_value
					: 0;
			}
		}
	}

	RVecRArchValue_push_back (vec, &value);
}

static void add_immediate_archvalue(const RJson *varnode, RVecRArchValue *vec, int access) {
	if (!varnode || varnode->type != R_JSON_OBJECT || !vec) {
		return;
	}

	const RJson *space = r_json_get (varnode, "space");
	const RJson *offset = r_json_get (varnode, "offset");

	if (!space || !space->str_value || !offset) {
		return;
	}

	// Only create immediate values for constant space
	if (r_str_casecmp (space->str_value, "const") != 0) {
		return;
	}

	RArchValue value = {0};
	value.type = R_ANAL_VAL_IMM;
	value.access = access;
	value.imm = (offset->type == R_JSON_INTEGER) ? offset->num.s_value : 0;

	RVecRArchValue_push_back (vec, &value);
}

static void fill_op_values_enhanced(RAnal *anal, RAnalOp *op, R2ILContext *ctx, const R2ILBlock *block) {
	if (!anal || !op || !ctx || !block) {
		return;
	}

	op->direction = 0;

	// Get memory accesses
	char *mem_json = r2il_block_mem_access (ctx, block);
	if (mem_json) {
		RJson *mem_root = r_json_parse (mem_json);
		if (mem_root && mem_root->type == R_JSON_ARRAY) {
			size_t i;
			for (i = 0; i < mem_root->children.count; i++) {
				const RJson *mem_access = r_json_item (mem_root, i);
				if (mem_access) {
					const RJson *type = r_json_get (mem_access, "type");
					if (type && type->str_value) {
						int access = R_PERM_R;
						bool is_store = !strcmp (type->str_value, "store");
						if (is_store) {
							access = R_PERM_W;
							op->direction |= R_ANAL_OP_DIR_WRITE;
						} else if (!strcmp (type->str_value, "load")) {
							op->direction |= R_ANAL_OP_DIR_READ;
						}
						add_memory_archvalue (anal, mem_access, is_store ? &op->dsts : &op->srcs, access);
					}

					const RJson *stack = r_json_get (mem_access, "stack");
					const RJson *stack_offset = r_json_get (mem_access, "stack_offset");
					if (stack && stack->type == R_JSON_BOOLEAN && stack->num.u_value && !op->stackop) {
						if (type && type->str_value) {
							if (!strcmp (type->str_value, "store")) {
								op->stackop = R_ANAL_STACK_SET;
							} else if (!strcmp (type->str_value, "load")) {
								op->stackop = R_ANAL_STACK_GET;
							}
						}
						if (stack_offset && stack_offset->type == R_JSON_INTEGER) {
							op->stackptr = stack_offset->num.s_value;
						}
					}
				}
			}
		}
		r_json_free (mem_root);
		r2il_string_free (mem_json);
	}
	if (op->direction == 0) {
		op->direction = R_ANAL_OP_DIR_READ;
	}

	// Get all varnodes to find immediate values
	char *vars_json = r2il_block_varnodes (ctx, block);
	if (vars_json) {
		RJson *vars_root = r_json_parse (vars_json);
		if (vars_root && vars_root->type == R_JSON_ARRAY) {
			size_t i;
			for (i = 0; i < vars_root->children.count; i++) {
				const RJson *varnode = r_json_item (vars_root, i);
				if (varnode) {
					add_immediate_archvalue (varnode, &op->srcs, R_PERM_R);
				}
			}
		}
		r_json_free (vars_root);
		r2il_string_free (vars_json);
	}

	// Still add SSA register values for def-use analysis
	char *defuse_json = r2il_block_defuse_json (ctx, block);
	if (defuse_json) {
		RJson *root = r_json_parse (defuse_json);
		if (root && root->type == R_JSON_OBJECT) {
			const RJson *inputs = r_json_get (root, "inputs");
			const RJson *outputs = r_json_get (root, "outputs");
			add_ssa_reg_values (anal, inputs, &op->srcs, R_PERM_R);
			add_ssa_reg_values (anal, outputs, &op->dsts, R_PERM_W);
		}
		r_json_free (root);
		r2il_string_free (defuse_json);
	}
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
	ut64 from;
	ut64 to;
} EdgePair;

typedef struct {
	EdgePair *items;
	size_t count;
	size_t capacity;
} EdgeSet;

typedef struct {
	ut64 *updated_callers;
	size_t updated_callers_count;
	size_t updated_callers_capacity;
	char **sample_callees;
	size_t sample_callees_count;
	size_t sample_callees_capacity;
	int prop_callees_triggered;
	int prop_callers_considered;
	int prop_callers_updated;
	int prop_callers_dedup_skipped;
	int prop_callers_missing_fcn;
	int prop_type_match_failures;
	int prop_afva_failures;
} CallerPropagationState;

typedef struct {
	int readback_fail;
	int ret_mismatch;
	int argc_mismatch;
	int argtype_mismatch;
	int callconv_mismatch;
} ConsistencyReasonCounters;

typedef enum {
	WRITEBACK_APPLY_NONE = 0,
	WRITEBACK_APPLY_API,
	WRITEBACK_APPLY_CMD,
} WritebackApplyPath;

typedef struct {
	WritebackApplyPath path;
	bool already_applied;
	bool api_verify_fail;
	bool cmd_fallback_attempted;
	bool cmd_apply_fail;
	char detail[256];
} WritebackApplyResult;

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

static void caller_propagation_state_init(CallerPropagationState *state) {
	if (!state) {
		return;
	}
	memset (state, 0, sizeof (*state));
}

static void caller_propagation_state_fini(CallerPropagationState *state) {
	if (!state) {
		return;
	}
	free (state->updated_callers);
	free_string_array (state->sample_callees, state->sample_callees_count);
	memset (state, 0, sizeof (*state));
}

static bool ut64_array_contains(const ut64 *items, size_t count, ut64 value) {
	size_t i;
	for (i = 0; i < count; i++) {
		if (items[i] == value) {
			return true;
		}
	}
	return false;
}

static bool ut64_sorted_contains(const ut64 *items, size_t count, ut64 value) {
	size_t lo = 0;
	size_t hi = count;
	while (lo < hi) {
		size_t mid = lo + ((hi - lo) / 2);
		ut64 cur = items[mid];
		if (cur == value) {
			return true;
		}
		if (cur < value) {
			lo = mid + 1;
		} else {
			hi = mid;
		}
	}
	return false;
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
	"memcpy",
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

static bool parse_ssa_target_addr(const char *src, ut64 *out) {
	char buf[128];
	const char *payload;
	const char *end;
	size_t len;
	char *tail = NULL;
	unsigned long long value;

	if (!src || !out) {
		return false;
	}

	if (r_str_startswith (src, "const:")) {
		payload = src + 6;
	} else if (r_str_startswith (src, "ram:")) {
		payload = src + 4;
	} else {
		return false;
	}

	end = strchr (payload, '_');
	len = end ? (size_t)(end - payload) : strlen (payload);
	if (!len || len >= sizeof (buf)) {
		return false;
	}
	memcpy (buf, payload, len);
	buf[len] = '\0';

	errno = 0;
	value = strtoull (buf, &tail, 16);
	if (errno != 0 || !tail || *tail != '\0') {
		return false;
	}

	*out = (ut64)value;
	return true;
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

static char *clean_call_name(const char *raw) {
	char *name;
	char *at;
	size_t len;

	if (!raw || !*raw) {
		return NULL;
	}

	name = strdup (raw);
	if (!name) {
		return NULL;
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
		return NULL;
	}
	return name;
}

static char *resolve_call_target_name(RCore *core, RAnal *anal, const RJson *hit_op) {
	const RJson *j_sources;
	const RJson *j_src;
	ut64 addr = 0;
	const char *raw_name = NULL;
	char *cleaned = NULL;

	if (!core || !anal || !hit_op || hit_op->type != R_JSON_OBJECT) {
		return NULL;
	}

	j_sources = r_json_get (hit_op, "sources");
	if (!j_sources || j_sources->type != R_JSON_ARRAY) {
		return NULL;
	}
	j_src = j_sources->children.first;
	if (!j_src || j_src->type != R_JSON_STRING || !j_src->str_value) {
		return NULL;
	}
	if (!parse_ssa_target_addr (j_src->str_value, &addr)) {
		return NULL;
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
		return NULL;
	}

	cleaned = clean_call_name (raw_name);
	return cleaned;
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

static void edge_set_init(EdgeSet *set) {
	if (!set) {
		return;
	}
	set->items = NULL;
	set->count = 0;
	set->capacity = 0;
}

static void edge_set_free(EdgeSet *set) {
	if (!set) {
		return;
	}
	free (set->items);
	set->items = NULL;
	set->count = 0;
	set->capacity = 0;
}

static bool edge_set_has(const EdgeSet *set, ut64 from, ut64 to) {
	size_t i;
	if (!set) {
		return false;
	}
	for (i = 0; i < set->count; i++) {
		if (set->items[i].from == from && set->items[i].to == to) {
			return true;
		}
	}
	return false;
}

static bool edge_set_add(EdgeSet *set, ut64 from, ut64 to) {
	EdgePair *next;

	if (!set) {
		return false;
	}
	if (edge_set_has (set, from, to)) {
		return true;
	}

	if (set->count >= set->capacity) {
		size_t new_capacity = set->capacity ? (set->capacity * 2) : 8;
		next = realloc (set->items, new_capacity * sizeof (EdgePair));
		if (!next) {
			return false;
		}
		set->items = next;
		set->capacity = new_capacity;
	}

	set->items[set->count].from = from;
	set->items[set->count].to = to;
	set->count++;
	return true;
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

static bool line_has_prefix(const char *line, size_t len, const char *prefix) {
	size_t prefix_len;

	if (!line || !prefix) {
		return false;
	}

	prefix_len = strlen (prefix);
	if (len < prefix_len) {
		return false;
	}
	return !strncmp (line, prefix, prefix_len);
}

static bool is_sla_managed_line(const char *line, size_t len) {
	if (!line) {
		return false;
	}
	while (len > 0 && (*line == ' ' || *line == '\t')) {
		line++;
		len--;
	}
	return line_has_prefix (line, len, SLEIGH_COMMENT_PREFIX_TAINT)
		|| line_has_prefix (line, len, SLEIGH_COMMENT_PREFIX_TAINT_RISK);
}

static bool is_sla_line_with_prefix(const char *line, size_t len, const char *prefix) {

	if (!line) {
		return false;
	}
	while (len > 0 && (*line == ' ' || *line == '\t')) {
		line++;
		len--;
	}
	return line_has_prefix (line, len, prefix);
}

static bool append_bytes(char **buf, size_t *len, size_t *cap, const char *src, size_t src_len) {
	char *next;

	if (!buf || !len || !cap || !src) {
		return false;
	}
	if (*len + src_len + 1 > *cap) {
		size_t new_cap = *cap ? *cap : 64;
		while (*len + src_len + 1 > new_cap) {
			new_cap *= 2;
		}
		next = realloc (*buf, new_cap);
		if (!next) {
			return false;
		}
		*buf = next;
		*cap = new_cap;
	}
	memcpy (*buf + *len, src, src_len);
	*len += src_len;
	(*buf)[*len] = '\0';
	return true;
}

static char *strip_sla_lines(const char *existing_comment, const char *prefix, bool all_managed) {
	const char *cursor;
	char *out = NULL;
	size_t out_len = 0;
	size_t out_cap = 0;
	bool first = true;

	if (!existing_comment || !*existing_comment) {
		return strdup ("");
	}

	cursor = existing_comment;
	while (*cursor) {
		const char *line_start = cursor;
		const char *line_end = strchr (cursor, '\n');
		size_t line_len = line_end ? (size_t)(line_end - line_start) : strlen (line_start);
		bool should_strip = all_managed
			? is_sla_managed_line (line_start, line_len)
			: is_sla_line_with_prefix (line_start, line_len, prefix);

		if (!should_strip) {
			if (!first) {
				append_bytes (&out, &out_len, &out_cap, "\n", 1);
			}
			append_bytes (&out, &out_len, &out_cap, line_start, line_len);
			first = false;
		}

		if (!line_end) {
			break;
		}
			cursor = line_end + 1;
	}

	if (!out) {
		return strdup ("");
	}
	return out;
}

static char *merge_sla_line(const char *existing_comment, const char *line_to_add, const char *prefix) {
	char *cleaned;
	char *merged;
	size_t cleaned_len;
	size_t line_len;

	if (!line_to_add || !*line_to_add) {
		return strip_sla_lines (existing_comment, prefix, false);
	}

	cleaned = strip_sla_lines (existing_comment, prefix, false);
	if (!cleaned) {
		return NULL;
	}
	if (!*cleaned) {
		free (cleaned);
		return strdup (line_to_add);
	}

	cleaned_len = strlen (cleaned);
	line_len = strlen (line_to_add);
	merged = malloc (cleaned_len + 1 + line_len + 1);
	if (!merged) {
		free (cleaned);
		return NULL;
	}
	memcpy (merged, cleaned, cleaned_len);
	merged[cleaned_len] = '\n';
	memcpy (merged + cleaned_len + 1, line_to_add, line_len);
	merged[cleaned_len + 1 + line_len] = '\0';
	free (cleaned);
	return merged;
}

static void set_sla_comment_line_with_prefix(RAnal *anal, ut64 addr, const char *line, const char *prefix) {
	const char *existing;
	char *updated;

	if (!anal) {
		return;
	}

	existing = r_meta_get_string (anal, R_META_TYPE_COMMENT, addr);
	updated = line
		? merge_sla_line (existing, line, prefix)
		: strip_sla_lines (existing, prefix, false);
	if (!updated) {
		return;
	}

	if (*updated) {
		r_meta_set_string (anal, R_META_TYPE_COMMENT, addr, updated);
	} else {
		r_meta_del (anal, R_META_TYPE_COMMENT, addr, 1);
	}
	free (updated);
}

static void set_sla_taint_comment_line(RAnal *anal, ut64 addr, const char *taint_line) {
	set_sla_comment_line_with_prefix (anal, addr, taint_line, SLEIGH_COMMENT_PREFIX_TAINT);
}

static void set_sla_taint_risk_comment_line(RAnal *anal, ut64 addr, const char *risk_line) {
	set_sla_comment_line_with_prefix (anal, addr, risk_line, SLEIGH_COMMENT_PREFIX_TAINT_RISK);
}

static void clear_taint_function_artifacts(RAnal *anal, RCore *core, const RAnalFunction *fcn, const BlockArray *blocks) {
	size_t i;
	char glob[128];
	char risk_glob[128];

	if (!anal || !fcn || !blocks) {
		return;
	}

	if (core && core->flags) {
		snprintf (glob, sizeof (glob), "sla.taint.fcn_%"PFMT64x".*", fcn->addr);
		r_flag_unset_glob (core->flags, glob);
		snprintf (risk_glob, sizeof (risk_glob), "sla.taint.risk.*.fcn_%"PFMT64x, fcn->addr);
		r_flag_unset_glob (core->flags, risk_glob);
	}

	for (i = 0; i < blocks->count; i++) {
		ut64 block_addr = r2il_block_addr (blocks->blocks[i]);
		set_sla_comment_line_with_prefix (anal, block_addr, NULL, SLEIGH_COMMENT_PREFIX_TAINT);
		set_sla_comment_line_with_prefix (anal, block_addr, NULL, SLEIGH_COMMENT_PREFIX_TAINT_RISK);
	}
	set_sla_comment_line_with_prefix (anal, fcn->addr, NULL, SLEIGH_COMMENT_PREFIX_TAINT);
	set_sla_comment_line_with_prefix (anal, fcn->addr, NULL, SLEIGH_COMMENT_PREFIX_TAINT_RISK);
}

static size_t write_semantic_comments_for_function(RAnal *anal, const R2ILContext *ctx,
		const BlockArray *blocks, ut64 fcn_addr, bool enabled) {
	size_t i;
	size_t emitted = 0;
	char *json = NULL;
	RJson *root = NULL;
	const RJson *item;
	bool parsed_annotation_array = false;

	if (!anal || !blocks) {
		return 0;
	}

	/* Always clear stale semantic lines first to keep writeback idempotent. */
	set_sla_comment_line_with_prefix (anal, fcn_addr, NULL, SLEIGH_COMMENT_PREFIX_SEMANTIC);
	for (i = 0; i < blocks->count; i++) {
		set_sla_comment_line_with_prefix (anal, r2il_block_addr (blocks->blocks[i]),
			NULL, SLEIGH_COMMENT_PREFIX_SEMANTIC);
	}

	if (!enabled || !ctx || blocks->count == 0) {
		return 0;
	}

	json = r2sleigh_analyze_fcn_annotations (ctx,
		(const R2ILBlock **)blocks->blocks, blocks->count, fcn_addr);
	if (!json || !*json) {
		R_LOG_DEBUG ("r2sleigh: semantic annotation generation returned empty payload for fcn=0x%"PFMT64x, fcn_addr);
		goto cleanup;
	}

	root = r_json_parse (json);
	if (!root || root->type != R_JSON_ARRAY) {
		R_LOG_DEBUG ("r2sleigh: semantic annotation JSON parse/type failure for fcn=0x%"PFMT64x, fcn_addr);
		goto cleanup;
	}
	parsed_annotation_array = true;

	for (item = root->children.first; item; item = item->next) {
		const RJson *j_addr;
		const RJson *j_comment;

		if (item->type != R_JSON_OBJECT) {
			continue;
		}
		j_addr = r_json_get (item, "addr");
		j_comment = r_json_get (item, "comment");
		if (!j_addr || j_addr->type != R_JSON_INTEGER
			|| !j_comment || j_comment->type != R_JSON_STRING
			|| !j_comment->str_value || !*j_comment->str_value) {
			continue;
		}
		set_sla_comment_line_with_prefix (anal, (ut64)j_addr->num.u_value,
			j_comment->str_value, SLEIGH_COMMENT_PREFIX_SEMANTIC);
		emitted++;
	}

cleanup:
	r_json_free (root);
	r2il_string_free (json);
	if (enabled && parsed_annotation_array && emitted == 0) {
		set_sla_comment_line_with_prefix (anal, fcn_addr, "sla: analyzed",
			SLEIGH_COMMENT_PREFIX_SEMANTIC);
		emitted = 1;
	}
	return emitted;
}

static bool has_xref(RAnal *anal, ut64 from, ut64 to, RAnalRefType type) {
	RVecAnalRef *refs;
	size_t i;
	size_t len;

	if (!anal) {
		return false;
	}
	refs = r_anal_xrefs_get (anal, to);
	if (!refs) {
		return false;
	}

	len = RVecAnalRef_length (refs);
	for (i = 0; i < len; i++) {
		RAnalRef *ref = RVecAnalRef_at (refs, i);
		if (ref && ref->at == from && ref->addr == to && ref->type == type) {
			return true;
		}
	}

	return false;
}

static bool maybe_add_taint_xref(RAnal *anal, EdgeSet *seen, ut64 from, ut64 to, RAnalRefType type, int *added_count) {
	if (!anal || !seen || !from || !to) {
		return false;
	}
	if (edge_set_has (seen, from, to)) {
		return false;
	}
	if (!edge_set_add (seen, from, to)) {
		return false;
	}
	if (has_xref (anal, from, to, type)) {
		return false;
	}
	if (r_anal_xrefs_set (anal, from, to, type)) {
		if (added_count) {
			(*added_count)++;
		}
		return true;
	}
	return false;
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

static int cmp_ut64_asc(const void *a, const void *b) {
	const ut64 lhs = *(const ut64 *)a;
	const ut64 rhs = *(const ut64 *)b;
	return (lhs > rhs) - (lhs < rhs);
}

static bool block_has_usable_switch_op(const RAnalBlock *bb) {
	return bb && bb->switch_op && bb->switch_op != (const RAnalSwitchOp *)UT64_MAX;
}

static bool parse_case_flag_for_switch(const char *name, ut64 switch_addr, bool *is_default, ut64 *case_value) {
	char prefix[64];
	char default_prefix[64];
	const char *suffix;
	char *endptr = NULL;
	unsigned long long parsed;

	if (!name || !*name) {
		return false;
	}

	snprintf (prefix, sizeof (prefix), "case.0x%"PFMT64x".", switch_addr);
	if (r_str_startswith (name, prefix)) {
		suffix = name + strlen (prefix);
		if (!*suffix) {
			return false;
		}
		parsed = strtoull (suffix, &endptr, 10);
		if (endptr == suffix || (endptr && *endptr)) {
			return false;
		}
		if (is_default) {
			*is_default = false;
		}
		if (case_value) {
			*case_value = (ut64)parsed;
		}
		return true;
	}

	snprintf (default_prefix, sizeof (default_prefix), "case.default.0x%"PFMT64x, switch_addr);
	if (!strcmp (name, default_prefix)) {
		if (is_default) {
			*is_default = true;
		}
		if (case_value) {
			*case_value = UT64_MAX;
		}
		return true;
	}

	return false;
}

static bool synthesize_switch_info_from_case_flags(
	RAnal *anal,
	RAnalFunction *fcn,
	RAnalBlock *bb,
	ut64 switch_addr,
	R2ILBlock *block
) {
	RListIter *iter;
	RAnalBlock *candidate;
	unsigned long long *case_values = NULL;
	unsigned long long *case_targets = NULL;
	size_t ncases = 0;
	size_t capacity = 0;
	ut64 min_val = ULLONG_MAX;
	ut64 max_val = 0;
	ut64 default_target = 0;
	bool any_case = false;

	if (!anal || !fcn || !bb || !block || switch_addr == UT64_MAX || !anal->flb.get_at) {
		return false;
	}

	r_list_foreach (fcn->bbs, iter, candidate) {
		RFlagItem *flag;
		bool is_default = false;
		ut64 case_value = UT64_MAX;
		unsigned long long *next_values;
		unsigned long long *next_targets;

		if (!candidate || candidate->addr == bb->addr) {
			continue;
		}

		flag = anal->flb.get_at (anal->flb.f, candidate->addr, false);
		if (!flag || !flag->name || !parse_case_flag_for_switch (flag->name, switch_addr, &is_default, &case_value)) {
			continue;
		}

		if (is_default) {
			default_target = candidate->addr;
			continue;
		}

		if (ncases >= capacity) {
			size_t new_capacity = capacity ? (capacity * 2) : 8;
			next_values = realloc (case_values, new_capacity * sizeof (unsigned long long));
			if (!next_values) {
				free (case_values);
				free (case_targets);
				return false;
			}
			next_targets = realloc (case_targets, new_capacity * sizeof (unsigned long long));
			if (!next_targets) {
				free (next_values);
				free (case_targets);
				return false;
			}
			case_values = next_values;
			case_targets = next_targets;
			capacity = new_capacity;
		}

		case_values[ncases] = case_value;
		case_targets[ncases] = candidate->addr;
		min_val = R_MIN (min_val, case_value);
		max_val = R_MAX (max_val, case_value);
		ncases++;
		any_case = true;
	}

	if (!any_case || ncases < 2) {
		free (case_values);
		free (case_targets);
		return false;
	}

	r2il_block_set_switch_info (block, switch_addr, min_val, max_val, default_target, case_values, case_targets, ncases);
	free (case_values);
	free (case_targets);
	return true;
}

static bool parse_switch_table_addr_from_comment(const char *comment, ut64 *table_addr) {
	const char *needle;
	char *endptr = NULL;
	unsigned long long parsed;

	if (!comment || !table_addr) {
		return false;
	}

	needle = strstr (comment, "at 0x");
	if (!needle) {
		return false;
	}
	needle += 5;
	parsed = strtoull (needle, &endptr, 16);
	if (endptr == needle || !parsed || parsed == ULLONG_MAX) {
		return false;
	}

	*table_addr = (ut64)parsed;
	return true;
}

static bool recover_switch_table_addr_from_op(const RAnalOp *op, ut64 *table_addr) {
	if (!op || !table_addr) {
		return false;
	}
	if (op->disp != 0 && op->disp != UT64_MAX) {
		*table_addr = op->disp;
		return true;
	}
	if (op->ptr > 0 && op->ptr != ST64_MAX) {
		*table_addr = (ut64)op->ptr;
		return true;
	}
	if (parse_switch_table_addr_from_comment (op->mnemonic, table_addr)) {
		return true;
	}
	return false;
}

static ut64 find_last_block_op_addr(RAnal *anal, RAnalBlock *bb, const ut8 *buf, size_t buf_sz) {
	ut64 last_addr = UT64_MAX;
	size_t off = 0;

	if (!anal || !bb || !buf || !buf_sz) {
		return UT64_MAX;
	}

	while (off < bb->size && off < buf_sz) {
		RAnalOp op = {0};
		int len = r_anal_op (anal, &op, bb->addr + off, buf + off, (int)(buf_sz - off), R_ARCH_OP_MASK_BASIC);
		r_anal_op_fini (&op);
		if (len < 1) {
			len = 1;
		}
		last_addr = bb->addr + off;
		off += (size_t)len;
	}

	return last_addr;
}

static ut64 find_switch_search_start(RAnalFunction *fcn, RAnalBlock *bb) {
	RListIter *iter;
	RAnalBlock *candidate;
	ut64 best = bb ? bb->addr : UT64_MAX;

	if (!fcn || !bb) {
		return UT64_MAX;
	}

	r_list_foreach (fcn->bbs, iter, candidate) {
		if (!candidate || candidate->addr == bb->addr) {
			continue;
		}
		if (candidate->jump != bb->addr && candidate->fail != bb->addr) {
			continue;
		}
		if (candidate->jump == UT64_MAX || candidate->fail == UT64_MAX) {
			continue;
		}
		best = candidate->addr;
		break;
	}

	return best;
}

static bool recover_missing_delta_switch_op(RAnal *anal, RAnalFunction *fcn, RAnalBlock *bb) {
	ut8 *buf = NULL;
	size_t bb_size;
	size_t to_read;
	ut64 jmp_addr;
	ut64 table_addr;
	ut64 search_start;
	ut64 table_size = 0;
	ut64 default_case = UT64_MAX;
	st64 start_casenum_shift = 0;
	RAnalOp jmp_op = {0};
	int jmp_len;
	bool ok = false;

	if (!anal || !fcn || !bb || block_has_usable_switch_op (bb) || bb->size < 2) {
		return false;
	}

	if (!read_block_bytes_for_lifting (anal, bb, &buf, &to_read, &bb_size)) {
		return false;
	}

	jmp_addr = find_last_block_op_addr (anal, bb, buf, to_read);
	if (jmp_addr == UT64_MAX || jmp_addr < bb->addr) {
		free (buf);
		return false;
	}

	jmp_len = r_anal_op (
		anal,
		&jmp_op,
		jmp_addr,
		buf + (jmp_addr - bb->addr),
		(int)(to_read - (jmp_addr - bb->addr)),
		R_ARCH_OP_MASK_BASIC | R_ARCH_OP_MASK_DISASM
	);
	if (jmp_len < 1) {
		r_anal_op_fini (&jmp_op);
		free (buf);
		return false;
	}

	{
		const ut32 jmp_type = jmp_op.type & R_ANAL_OP_TYPE_MASK;
		if (jmp_type != R_ANAL_OP_TYPE_RJMP && jmp_type != R_ANAL_OP_TYPE_UJMP) {
			r_anal_op_fini (&jmp_op);
			free (buf);
			return false;
		}
	}
	if (!recover_switch_table_addr_from_op (&jmp_op, &table_addr)) {
		r_anal_op_fini (&jmp_op);
		free (buf);
		return false;
	}

	ok = try_get_jmptbl_info (
		anal,
		fcn,
		jmp_addr,
		bb,
		&table_size,
		&default_case,
		&start_casenum_shift
	);
	if (!ok) {
		search_start = find_switch_search_start (fcn, bb);
		if (search_start == UT64_MAX) {
			search_start = bb->addr;
		}
		ok = try_get_delta_jmptbl_info (
			anal,
			fcn,
			jmp_addr,
			search_start,
			&table_size,
			&default_case,
			&start_casenum_shift
		);
	}
	if (!ok || !table_size || table_size > 0x1000) {
		r_anal_op_fini (&jmp_op);
		free (buf);
		return false;
	}

	ok = r_anal_jmptbl_walk (
		anal,
		fcn,
		bb,
		0,
		jmp_addr,
		start_casenum_shift,
		table_addr,
		table_addr,
		4,
		table_size,
		default_case,
		false
	);
	r_anal_op_fini (&jmp_op);
	free (buf);
	return ok && block_has_usable_switch_op (bb) && bb->switch_op->cases;
}

static void recover_missing_switch_ops(RAnal *anal, RAnalFunction *fcn) {
	RListIter *iter;
	RAnalBlock *bb;

	if (!anal || !fcn) {
		return;
	}

	r_list_foreach (fcn->bbs, iter, bb) {
		recover_missing_delta_switch_op (anal, fcn, bb);
	}
}

static bool switch_score_is_better(SwitchScore candidate, SwitchScore current) {
	if (candidate.contiguous_run != current.contiguous_run) {
		return candidate.contiguous_run > current.contiguous_run;
	}
	if (candidate.small_values != current.small_values) {
		return candidate.small_values > current.small_values;
	}
	if (candidate.num_cases != current.num_cases) {
		return candidate.num_cases > current.num_cases;
	}
	if (candidate.unique_targets != current.unique_targets) {
		return candidate.unique_targets > current.unique_targets;
	}
	return candidate.inverse_outliers > current.inverse_outliers;
}

static size_t leading_contiguous_run_len(ut64 *values, size_t nvalues) {
	size_t i;
	ut64 expected;
	if (!values || !nvalues) {
		return 0;
	}
	expected = values[0];
	for (i = 1; i < nvalues; i++) {
		if (values[i] != expected + 1) {
			return i;
		}
		expected = values[i];
	}
	return nvalues;
}

static SwitchScore score_switch_op(const RAnalSwitchOp *switch_op) {
	SwitchScore score = {0};
	RListIter *iter;
	RAnalCaseOp *case_op;
	size_t ncases;
	size_t i;
	ut64 *values = NULL;
	ut64 *targets = NULL;

	if (!switch_op || switch_op == (const RAnalSwitchOp *)UT64_MAX || !switch_op->cases) {
		return score;
	}

	ncases = r_list_length(switch_op->cases);
	if (!ncases) {
		return score;
	}

	values = calloc(ncases, sizeof(ut64));
	targets = calloc(ncases, sizeof(ut64));
	if (!values || !targets) {
		free(values);
		free(targets);
		return score;
	}

	i = 0;
	r_list_foreach (switch_op->cases, iter, case_op) {
		values[i] = case_op->value;
		targets[i] = case_op->jump;
		i++;
	}

	qsort(values, ncases, sizeof(ut64), cmp_ut64_asc);
	qsort(targets, ncases, sizeof(ut64), cmp_ut64_asc);

	{
		size_t unique_values = 0;
		size_t unique_targets = 0;
		ut64 last = UT64_MAX;
		for (i = 0; i < ncases; i++) {
			if (!unique_values || values[i] != last) {
				values[unique_values++] = values[i];
				last = values[i];
			}
		}
		last = UT64_MAX;
		for (i = 0; i < ncases; i++) {
			if (!unique_targets || targets[i] != last) {
				targets[unique_targets++] = targets[i];
				last = targets[i];
			}
		}
		score.contiguous_run = leading_contiguous_run_len(values, unique_values);
		for (i = 0; i < unique_values; i++) {
			if (values[i] <= 0xff) {
				score.small_values++;
			}
		}
		score.num_cases = ncases;
		score.unique_targets = unique_targets;
		score.inverse_outliers = unique_values >= score.contiguous_run
			? SIZE_MAX - (unique_values - score.contiguous_run)
			: SIZE_MAX;
	}

	free(values);
	free(targets);
	return score;
}

static bool queue_contains_addr(const SwitchQueueEntry *queue, size_t nqueue, ut64 addr) {
	size_t i;
	for (i = 0; i < nqueue; i++) {
		if (queue[i].addr == addr) {
			return true;
		}
	}
	return false;
}

static void queue_push_unique(SwitchQueueEntry *queue, size_t capacity, size_t *nqueue, ut64 addr, unsigned depth) {
	if (!queue || !nqueue || addr == UT64_MAX || *nqueue >= capacity) {
		return;
	}
	if (queue_contains_addr(queue, *nqueue, addr)) {
		return;
	}
	queue[*nqueue].addr = addr;
	queue[*nqueue].depth = depth;
	(*nqueue)++;
}

static RAnalBlock *find_best_switch_metadata_block(RAnal *anal, RAnalFunction *fcn, RAnalBlock *start) {
	SwitchQueueEntry queue[512];
	size_t head = 0;
	size_t nqueue = 0;
	RAnalBlock *best = start;
	SwitchScore best_score;

	if (!anal || !fcn || !block_has_usable_switch_op(start) || !start->switch_op->cases) {
		return start;
	}

	best_score = score_switch_op(start->switch_op);
	queue_push_unique(queue, R_ARRAY_SIZE(queue), &nqueue, start->addr, 0);

	while (head < nqueue) {
		RAnalBlock *bb = r_anal_function_bbget_in(anal, fcn, queue[head].addr);
		unsigned depth = queue[head].depth;
		RListIter *iter;
		RAnalCaseOp *case_op;
		head++;

		if (!bb) {
			continue;
		}

		if (block_has_usable_switch_op(bb) && bb->switch_op->cases) {
			SwitchScore candidate_score = score_switch_op(bb->switch_op);
			if (switch_score_is_better(candidate_score, best_score)) {
				best = bb;
				best_score = candidate_score;
			}
		}

		if (depth >= 6) {
			continue;
		}

		queue_push_unique(queue, R_ARRAY_SIZE(queue), &nqueue, bb->jump, depth + 1);
		queue_push_unique(queue, R_ARRAY_SIZE(queue), &nqueue, bb->fail, depth + 1);
		if (block_has_usable_switch_op(bb) && bb->switch_op->cases) {
			r_list_foreach (bb->switch_op->cases, iter, case_op) {
				queue_push_unique(queue, R_ARRAY_SIZE(queue), &nqueue, case_op->jump, depth + 1);
			}
		}
	}

	return best;
}

static bool block_belongs_to_function(RAnalBlock *bb, RAnalFunction *fcn) {
	return bb && fcn && r_list_contains (bb->fcns, fcn);
}

static RAnalBlock *function_block_at_exact(RAnal *anal, RAnalFunction *fcn, ut64 addr) {
	RAnalBlock *bb;
	RListIter *iter;

	if (!anal || !fcn || addr == UT64_MAX || !addr) {
		return NULL;
	}

	bb = r_anal_get_block_at (anal, addr);
	if (bb && block_belongs_to_function (bb, fcn)) {
		return bb;
	}

	r_list_foreach (fcn->bbs, iter, bb) {
		if (bb && bb->addr == addr) {
			return bb;
		}
	}

	return NULL;
}

static void split_missing_switch_case_targets(RAnal *anal, RAnalFunction *fcn) {
	RListIter *iter;
	RAnalBlock *bb;
	ut64 *targets = NULL;
	size_t ntargets = 0;
	size_t capacity = 0;

	if (!anal || !fcn) {
		return;
	}

	r_list_foreach (fcn->bbs, iter, bb) {
		RAnalBlock *switch_bb = find_best_switch_metadata_block(anal, fcn, bb);
		RListIter *case_iter;
		RAnalCaseOp *case_op;

		if (!block_has_usable_switch_op(switch_bb) || !switch_bb->switch_op->cases) {
			continue;
		}

		r_list_foreach (switch_bb->switch_op->cases, case_iter, case_op) {
			bool seen = false;
			ut64 target = case_op ? case_op->jump : UT64_MAX;
			size_t i;

			if (target == UT64_MAX || !target) {
				continue;
			}
			for (i = 0; i < ntargets; i++) {
				if (targets[i] == target) {
					seen = true;
					break;
				}
			}
			if (seen) {
				continue;
			}
			if (ntargets >= capacity) {
				size_t new_capacity = capacity ? (capacity * 2) : 32;
				ut64 *next = realloc (targets, new_capacity * sizeof (ut64));
				if (!next) {
					free (targets);
					return;
				}
				targets = next;
				capacity = new_capacity;
			}
			targets[ntargets++] = target;
		}
	}

	for (size_t i = 0; i < ntargets; i++) {
		ut64 target = targets[i];
		RAnalBlock *at = function_block_at_exact (anal, fcn, target);
		RAnalBlock *containing;
		RAnalBlock *split;

		if (at) {
			continue;
		}

		at = r_anal_get_block_at (anal, target);
		if (at && !block_belongs_to_function (at, fcn)) {
			r_anal_function_add_block (fcn, at);
			continue;
		}

		containing = r_anal_get_block_at (anal, target);
		if (!containing) {
			containing = r_anal_bb_from_offset (anal, target);
		}
		if (!containing) {
			continue;
		}
		if (containing->addr == target) {
			if (!block_belongs_to_function (containing, fcn)) {
				r_anal_function_add_block (fcn, containing);
			}
			continue;
		}

		split = r_anal_block_split (containing, target);
		if (split) {
			if (!block_belongs_to_function (split, fcn)) {
				r_anal_function_add_block (fcn, split);
			}
			r_unref (split);
		}
	}

	free (targets);
}

static bool block_has_linear_direct_jump(const RAnalBlock *bb) {
	return bb && bb->jump != UT64_MAX && bb->fail == UT64_MAX;
}

static size_t healed_layout_size(const RAnalBlock *bb, size_t fallback_size) {
	ut64 span;

	if (!block_has_linear_direct_jump (bb) || bb->jump <= bb->addr) {
		return fallback_size;
	}

	span = bb->jump - bb->addr;
	if (!span || span > fallback_size) {
		return fallback_size;
	}

	return (size_t)span;
}

static bool lifted_block_needs_heal(const RAnalBlock *bb, const R2ILBlock *block) {
	if (!bb || !block) {
		return false;
	}
	if (!block_has_linear_direct_jump (bb)) {
		return false;
	}
	if (r2il_block_op_count (block) == 0) {
		return true;
	}
	if (r2il_block_has_trailing_indirect_branch (block)) {
		return true;
	}
	return r2il_block_type (block) == R_ANAL_OP_TYPE_UJMP && r2il_block_jump (block) == 0;
}

static ut64 chase_invalid_split_jump_chain(RAnal *anal, RAnalFunction *fcn, ut64 addr) {
	size_t depth = 0;
	ut64 cur = addr;

	while (cur != UT64_MAX && cur && depth++ < 8) {
		RAnalBlock *bb = r_anal_function_bbget_at (anal, fcn, cur);
		if (!bb || bb->addr != cur) {
			break;
		}
		if (!block_has_linear_direct_jump (bb)) {
			break;
		}
		if (bb->size > 4 && bb->ninstr > 1) {
			break;
		}
		cur = bb->jump;
	}

	return cur;
}

static bool function_has_direct_predecessor_reference(RAnalFunction *fcn, ut64 addr) {
	RListIter *iter;
	RAnalBlock *bb;

	if (!fcn || addr == UT64_MAX || !addr) {
		return false;
	}

	r_list_foreach (fcn->bbs, iter, bb) {
		if (!bb || bb->addr == addr) {
			continue;
		}
		if ((bb->jump == addr || bb->fail == addr)
			&& (bb->size > 4 || !block_has_linear_direct_jump (bb))) {
			return true;
		}
	}

	return false;
}

static R2ILBlock *try_lift_prefix_healed_block(
	R2ILContext *ctx,
	RAnalBlock *bb,
	const ut8 *buf,
	size_t to_read,
	size_t bb_size
) {
	size_t logical_size;
	size_t prefix_size = bb_size;

	if (!ctx || !bb || !buf || bb_size <= 4) {
		return NULL;
	}

	logical_size = healed_layout_size (bb, bb_size);
	while (prefix_size > 4) {
		R2ILBlock *candidate;
		prefix_size--;
		candidate = r2il_lift_block (ctx, buf, to_read, bb->addr, prefix_size);
		if (!candidate) {
			continue;
		}
		if (r2il_block_op_count (candidate) == 0
			|| r2il_block_type (candidate) == R_ANAL_OP_TYPE_UJMP
			|| r2il_block_has_trailing_indirect_branch (candidate)) {
			r2il_block_free (candidate);
			continue;
		}
		r2il_block_rewrite_layout (candidate, bb->addr, (unsigned int)logical_size);
		return candidate;
	}

	return NULL;
}

static R2ILBlock *try_lift_suffix_healed_block(
	R2ILContext *ctx,
	RAnalBlock *bb,
	const ut8 *buf,
	size_t to_read,
	size_t bb_size
) {
	size_t delta;
	size_t max_delta;
	size_t logical_size;

	if (!ctx || !bb || !buf || bb_size < 2 || to_read < 2) {
		return NULL;
	}

	logical_size = healed_layout_size (bb, bb_size);
	max_delta = R_MIN (bb_size - 1, 8);
	for (delta = 1; delta <= max_delta; delta++) {
		R2ILBlock *candidate;
		if (delta >= to_read) {
			break;
		}
		candidate = r2il_lift_block (
			ctx,
			buf + delta,
			to_read - delta,
			bb->addr + delta,
			(unsigned int)(bb_size - delta)
		);
		if (!candidate) {
			continue;
		}
		if (r2il_block_op_count (candidate) == 0
			|| r2il_block_type (candidate) == R_ANAL_OP_TYPE_UJMP
			|| r2il_block_has_trailing_indirect_branch (candidate)) {
			r2il_block_free (candidate);
			continue;
		}
		r2il_block_rewrite_layout (candidate, bb->addr, (unsigned int)logical_size);
		return candidate;
	}

	return NULL;
}

static R2ILBlock *make_split_padding_alias_block(RAnal *anal, RAnalFunction *fcn, RAnalBlock *bb) {
	ut64 target;

	if (!anal || !fcn || !bb || !block_has_linear_direct_jump (bb)) {
		return NULL;
	}
	if (!function_has_direct_predecessor_reference (fcn, bb->addr)) {
		return NULL;
	}

	target = chase_invalid_split_jump_chain (anal, fcn, bb->jump);
	if (target == UT64_MAX || !target || target == bb->addr) {
		return NULL;
	}

	return r2il_block_new_branch (
		bb->addr,
		(unsigned int)bb->size,
		target,
		(unsigned int)R_MAX (1, anal->config ? anal->config->bits / 8 : 8)
	);
}

static R2ILBlock *lift_function_block_healed(
	RAnal *anal,
	RAnalFunction *fcn,
	R2ILContext *ctx,
	RAnalBlock *bb,
	const ut8 *buf,
	size_t to_read,
	size_t bb_size
) {
	R2ILBlock *block;

	block = r2il_lift_block (ctx, buf, to_read, bb->addr, (unsigned int)bb_size);
	if (block && !lifted_block_needs_heal (bb, block)) {
		return block;
	}
	if (block) {
		r2il_block_free (block);
	}

	if (block_has_linear_direct_jump (bb)) {
		block = try_lift_prefix_healed_block (ctx, bb, buf, to_read, bb_size);
		if (block) {
			return block;
		}

		block = try_lift_suffix_healed_block (ctx, bb, buf, to_read, bb_size);
		if (block) {
			return block;
		}

		block = make_split_padding_alias_block (anal, fcn, bb);
		if (block) {
			return block;
		}
	}

	return NULL;
}

/* Lift all basic blocks of a function */
static bool lift_function_blocks(RAnal *anal, RAnalFunction *fcn, R2ILContext *ctx, BlockArray *out) {
	R_RETURN_VAL_IF_FAIL (anal && fcn && ctx && out, false);

	RListIter *iter;
	RAnalBlock *bb;

	block_array_init (out);
	recover_missing_switch_ops (anal, fcn);
	split_missing_switch_case_targets (anal, fcn);

	r_list_foreach (fcn->bbs, iter, bb) {
		ut8 *buf = NULL;
		size_t bb_size = 0;
		size_t to_read = 0;

		if (!read_block_bytes_for_lifting (anal, bb, &buf, &to_read, &bb_size)) {
			R_LOG_ERROR ("r2sleigh: failed to read block at 0x%"PFMT64x, bb->addr);
			continue;
		}

		/* Lift entire basic block (multiple instructions) */
		R2ILBlock *block = lift_function_block_healed (anal, fcn, ctx, bb, buf, to_read, bb_size);
		if (block) {
			/* Check if this block has switch info from radare2's analysis */
			RAnalBlock *switch_bb = find_best_switch_metadata_block(anal, fcn, bb);
			if (block_has_usable_switch_op(switch_bb) && switch_bb->switch_op->cases) {
				size_t num_cases = r_list_length (switch_bb->switch_op->cases);
				if (num_cases > 0) {
					unsigned long long *case_values = malloc (num_cases * sizeof (unsigned long long));
					unsigned long long *case_targets = malloc (num_cases * sizeof (unsigned long long));
					if (case_values && case_targets) {
						RListIter *case_iter;
						RAnalCaseOp *case_op;
						size_t i = 0;
						unsigned long long observed_min = ULLONG_MAX;
						unsigned long long observed_max = 0;
						r_list_foreach (switch_bb->switch_op->cases, case_iter, case_op) {
							case_values[i] = case_op->value;
							case_targets[i] = case_op->jump;
							observed_min = R_MIN (observed_min, case_op->value);
							observed_max = R_MAX (observed_max, case_op->value);
							i++;
						}

						unsigned long long min_val = switch_bb->switch_op->min_val;
						unsigned long long max_val = switch_bb->switch_op->max_val;
						int range_invalid = min_val > max_val;
						if (!range_invalid) {
							for (size_t case_idx = 0; case_idx < num_cases; case_idx++) {
								const unsigned long long value = case_values[case_idx];
								if (value < min_val || value > max_val) {
									range_invalid = 1;
									break;
								}
							}
						}
						if (range_invalid) {
							min_val = observed_min;
							max_val = observed_max;
						}

						r2il_block_set_switch_info (block,
							switch_bb->switch_op->addr,
							min_val,
							max_val,
							switch_bb->switch_op->def_val,
							case_values, case_targets, num_cases);
					}
					free (case_values);
					free (case_targets);
				}
			} else if (r2il_block_has_trailing_indirect_branch (block)) {
				ut64 switch_addr = find_last_block_op_addr (anal, bb, buf, to_read);
				(void)synthesize_switch_info_from_case_flags (anal, fcn, bb, switch_addr, block);
			}

			if (!r2il_block_validate (ctx, block)) {
				const char *err = r2il_error (ctx);
				if (err && *err) {
					R_LOG_ERROR ("r2sleigh: invalid block at 0x%"PFMT64x": %s", bb->addr, err);
				} else {
					R_LOG_ERROR ("r2sleigh: invalid block at 0x%"PFMT64x, bb->addr);
				}
				r2il_block_free (block);
				free (buf);
				continue;
			}
			block_array_push (out, block);
		}
		free (buf);
		}

	return out->count > 0;
}

static SleighMode cfg_get_mode_default_balanced(RAnal *anal) {
	RCore *core;
	RConfigNode *node;
	const char *mode;

	if (!anal || !anal->config) {
		return SLEIGH_MODE_BALANCED;
	}
	core = anal->coreb.core;
	if (!core || !core->config) {
		return SLEIGH_MODE_BALANCED;
	}
	node = r_config_node_get (core->config, "anal.sla.mode");
	if (!node) {
		return SLEIGH_MODE_BALANCED;
	}
	mode = r_config_get (core->config, "anal.sla.mode");
	if (!mode || !*mode) {
		return SLEIGH_MODE_BALANCED;
	}
	if (!strcasecmp (mode, "full")) {
		return SLEIGH_MODE_FULL;
	}
	if (!strcasecmp (mode, "fast")) {
		return SLEIGH_MODE_FAST;
	}
	if (!strcasecmp (mode, "balanced")) {
		return SLEIGH_MODE_BALANCED;
	}
	return SLEIGH_MODE_BALANCED;
}

static bool sleigh_mode_is_fast(RAnal *anal) {
	return cfg_get_mode_default_balanced (anal) == SLEIGH_MODE_FAST;
}

static SleighMode sleigh_mode_effective_for_post_analysis(RAnal *anal) {
	SleighMode mode = cfg_get_mode_default_balanced (anal);
	return mode == SLEIGH_MODE_FAST ? SLEIGH_MODE_FAST : SLEIGH_MODE_FULL;
}

static void ensure_default_string_config(RAnal *anal, const char *key, const char *desc, const char *value) {
	RCore *core;
	RConfigNode *node;

	if (!anal || !key || !*key || !value) {
		return;
	}
	core = anal->coreb.core;
	if (!core || !core->config) {
		return;
	}

	node = r_config_node_get (core->config, key);
	if (!node) {
		bool was_locked = core->config->lock;
		if (was_locked) {
			core->config->lock = false;
		}
		node = r_config_set (core->config, key, value);
		if (was_locked) {
			core->config->lock = true;
		}
	}
	if (node && desc && *desc) {
		r_config_node_desc (node, desc);
	}
}

static void ensure_default_int_config(RAnal *anal, const char *key, const char *desc, ut64 value) {
	RCore *core;
	RConfigNode *node;

	if (!anal || !key || !*key) {
		return;
	}
	core = anal->coreb.core;
	if (!core || !core->config) {
		return;
	}

	node = r_config_node_get (core->config, key);
	if (!node) {
		bool was_locked = core->config->lock;
		if (was_locked) {
			core->config->lock = false;
		}
		node = r_config_set_i (core->config, key, value);
		if (was_locked) {
			core->config->lock = true;
		}
	}
	if (node && desc && *desc) {
		r_config_node_desc (node, desc);
	}
}

static SleighTypeWritebackMode cfg_get_type_writeback_mode_default_balanced(RAnal *anal) {
	RCore *core;
	const char *mode;

	if (!anal) {
		return SLEIGH_TYPE_WRITEBACK_BALANCED;
	}
	core = anal->coreb.core;
	if (!core || !core->config) {
		return SLEIGH_TYPE_WRITEBACK_BALANCED;
	}
	mode = r_config_get (core->config, "anal.sla.type.writeback");
	if (!mode || !*mode) {
		return SLEIGH_TYPE_WRITEBACK_BALANCED;
	}
	if (!strcasecmp (mode, "off")) {
		return SLEIGH_TYPE_WRITEBACK_OFF;
	}
	if (!strcasecmp (mode, "aggressive")) {
		return SLEIGH_TYPE_WRITEBACK_AGGRESSIVE;
	}
	return SLEIGH_TYPE_WRITEBACK_BALANCED;
}

static int cfg_get_int_clamped(RAnal *anal, const char *key, int default_value, int min_value, int max_value) {
	RCore *core;
	RConfigNode *node;
	ut64 raw;

	if (!anal) {
		return default_value;
	}
	core = anal->coreb.core;
	if (!core || !core->config) {
		return default_value;
	}
	node = r_config_node_get (core->config, key);
	if (!node) {
		return default_value;
	}
	raw = r_config_get_i (core->config, key);
	if ((int)raw < min_value) {
		return min_value;
	}
	if ((int)raw > max_value) {
		return max_value;
	}
	return (int)raw;
}

static int cfg_get_type_min_conf(RAnal *anal) {
	return cfg_get_int_clamped (anal, "anal.sla.type.min_conf",
		SLEIGH_TYPE_MIN_CONF_DEFAULT, 1, 100);
}

static int cfg_get_type_rename_min_conf(RAnal *anal) {
	return cfg_get_int_clamped (anal, "anal.sla.type.rename_min_conf",
		SLEIGH_TYPE_RENAME_MIN_CONF_DEFAULT, 1, 100);
}

static int cfg_get_type_struct_min_conf(RAnal *anal) {
	return cfg_get_int_clamped (anal, "anal.sla.type.struct_min_conf",
		SLEIGH_TYPE_STRUCT_MIN_CONF_DEFAULT, 1, 100);
}

static int cfg_get_type_interproc_max_iters(RAnal *anal) {
	return cfg_get_int_clamped (anal, "anal.sla.type.interproc.max_iters",
		SLEIGH_TYPE_INTERPROC_MAX_ITERS_DEFAULT, 1, 256);
}

static int cfg_get_type_max_blocks(RAnal *anal) {
	return cfg_get_int_clamped (anal, "anal.sla.type.max_blocks",
		SLEIGH_TYPE_MAX_BLOCKS_DEFAULT, 1, 4096);
}

static int cfg_get_type_global_max_links(RAnal *anal) {
	return cfg_get_int_clamped (anal, "anal.sla.type.global.max_links",
		SLEIGH_TYPE_GLOBAL_MAX_LINKS_DEFAULT, 1, 4096);
}

static bool cfg_get_type_cache_enabled(RAnal *anal) {
	return cfg_get_int_clamped (anal, "anal.sla.type.cache", 1, 0, 1) != 0;
}

static void ensure_sleigh_default_configs(RAnal *anal) {
	ensure_default_string_config (anal, "anal.sla.mode",
		"analysis profile for r2sleigh: full|balanced|fast", "balanced");
	ensure_default_string_config (anal, "anal.sla.type.writeback",
		"type write-back policy: off|balanced|aggressive", "balanced");
	ensure_default_int_config (anal, "anal.sla.type.min_conf",
		"minimum confidence for type apply", SLEIGH_TYPE_MIN_CONF_DEFAULT);
	ensure_default_int_config (anal, "anal.sla.type.rename_min_conf",
		"minimum confidence for variable rename apply", SLEIGH_TYPE_RENAME_MIN_CONF_DEFAULT);
	ensure_default_int_config (anal, "anal.sla.type.struct_min_conf",
		"minimum confidence for struct declaration import", SLEIGH_TYPE_STRUCT_MIN_CONF_DEFAULT);
	ensure_default_int_config (anal, "anal.sla.type.interproc.max_iters",
		"maximum interprocedural propagation iterations", SLEIGH_TYPE_INTERPROC_MAX_ITERS_DEFAULT);
	ensure_default_int_config (anal, "anal.sla.type.max_blocks",
		"maximum basic blocks for type write-back inference", SLEIGH_TYPE_MAX_BLOCKS_DEFAULT);
	ensure_default_int_config (anal, "anal.sla.type.global.max_links",
		"maximum global type links applied per function payload", SLEIGH_TYPE_GLOBAL_MAX_LINKS_DEFAULT);
	ensure_default_int_config (anal, "anal.sla.type.cache",
		"cache unchanged function type payloads across repeated aaaa runs", 1);
}

static void configure_context_runtime_options(RAnal *anal, R2ILContext *ctx) {
	if (!ctx) {
		return;
	}
	r2il_set_semantic_metadata_enabled (ctx, !sleigh_mode_is_fast (anal));
}

R2ILContext *get_context(RAnal *anal) {
	if (!anal || !anal->config || !anal->config->arch[0]) {
		return NULL;
	}
	ensure_sleigh_default_configs (anal);
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
	} else if (!strcmp (arch, "mips")) {
	        /* Simple heuristic for MIPS (assuming default is 32be/le) */
	        /* Note: This is partial, better use manual override for complex variants */
		sleigh_arch_str = "mips"; /* Placeholder - mapped often to general mips */
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
		r2il_free (sleigh_ctx);
		sleigh_ctx = NULL;
	}
	free (sleigh_arch);
	sleigh_arch = NULL;
	sym_state_cache_clear ();
	data_ref_cache_clear ();
	type_writeback_cache_clear ();
	struct_decl_memo_clear ();

	/* Initialize new context */
	sleigh_ctx = r2il_arch_init (sleigh_arch_str);
	if (!sleigh_ctx) {
		/* Optional-arch builds are expected to miss some backends; stay silent
		 * so unsupported architectures fall back to other anal plugins. */
		R_LOG_DEBUG ("r2sleigh: backend unavailable for %s", sleigh_arch_str);
		return NULL;
	}

	if (!r2il_is_loaded (sleigh_ctx)) {
		const char *err = r2il_error (sleigh_ctx);
		if (err && *err) {
			R_LOG_DEBUG ("r2sleigh: %s", err);
		}
		r2il_free (sleigh_ctx);
		sleigh_ctx = NULL;
		return NULL;
	}

	sleigh_arch = strdup (sleigh_arch_str);

	/* Set register profile from Sleigh definitions */
	char *profile = r2il_get_reg_profile (sleigh_ctx);
	if (profile) {
		r_anal_set_reg_profile (anal, profile);
		r2il_string_free (profile);
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
	ut8 buf[SLEIGH_MIN_BYTES];
	int use_len = len;
	const ut8 *use_data = data;

	if (len < SLEIGH_MIN_BYTES) {
		memset (buf, 0, sizeof (buf));
		memcpy (buf, data, len);
		use_data = buf;
		use_len = SLEIGH_MIN_BYTES;
	}

	R2ILBlock *block = r2il_lift (sleigh_ctx, use_data, use_len, addr);
	if (!block) {
		return -1;
	}

	op->addr = addr;
	op->size = r2il_block_size (block);
	op->type = r2il_block_type (block);
	ut64 jump_addr = r2il_block_jump (block);
	if (jump_addr != 0) {
		op->jump = jump_addr;
	}
	ut64 fail_addr = r2il_block_fail (block);
	if (fail_addr != 0) {
		op->fail = fail_addr;
	}

	if (mask & R_ARCH_OP_MASK_DISASM) {
		char *mnem = r2il_block_mnemonic (ctx, use_data, use_len, addr);
		if (mnem) {
			op->mnemonic = strdup (mnem);
			r2il_string_free (mnem);
		}
	}

	if (mask & R_ARCH_OP_MASK_ESIL) {
		char *esil = r2il_block_to_esil (ctx, block);
		if (esil) {
			r_strbuf_set (&op->esil, esil);
			r2il_string_free (esil);
		}
	}

	if (mask & R_ARCH_OP_MASK_VAL) {
		RVecRArchValue_clear (&op->srcs);
		RVecRArchValue_clear (&op->dsts);
		fill_op_values_enhanced (anal, op, ctx, block);
	}

	r2il_block_free (block);
	return op->size;
}

static bool sleigh_init(RAnal *anal) {
	if (!sleigh_resolve_function_context_api ()) {
		sleigh_report_missing_function_context_api ();
		return false;
	}
	/* Lazy init - context created on first use. */
	ensure_sleigh_default_configs (anal);
	/* Prime context early so register aliases are available before aa/aaa passes. */
	(void)get_context (anal);
	return true;
}

static bool sleigh_fini(RAnal *anal) {
	(void)anal;
	if (sleigh_ctx) {
		r2il_free (sleigh_ctx);
		sleigh_ctx = NULL;
	}
	free (sleigh_arch);
	sleigh_arch = NULL;
	sym_state_cache_clear ();
	data_ref_cache_clear ();
	type_writeback_cache_clear ();
	struct_decl_memo_clear ();
	return true;
}

static void append_pszj_string_to_pj(RCore *core, PJ *pj, ut64 addr) {
	if (!core || !pj || !addr) {
		return;
	}
	if (!r_io_map_get_at (core->io, addr)) {
		return;
	}

	char *pszj = r_core_cmd_strf (core, "pszj @ 0x%"PFMT64x, addr);
	if (!pszj || pszj[0] != '{') {
		free (pszj);
		return;
	}

	RJson *root = r_json_parse (pszj);
	if (root && root->type == R_JSON_OBJECT) {
		const RJson *str = r_json_get (root, "string");
		const RJson *len = r_json_get (root, "length");
		const RJson *section = r_json_get (root, "section");
		if (str && len
			&& str->type == R_JSON_STRING
			&& len->type == R_JSON_INTEGER
			&& str->str_value
			&& section
			&& section->type == R_JSON_STRING
			&& section->str_value
			&& strcmp (section->str_value, "unknown")
			&& len->num.u_value > 0) {
			char addr_str[32];
			snprintf (addr_str, sizeof (addr_str), "0x%llx", (unsigned long long)addr);
			pj_ks (pj, addr_str, str->str_value);
		}
		r_json_free (root);
	}

	free (pszj);
}

static void extend_string_map_with_function_ptr_strings(RCore *core, RAnalFunction *fcn, PJ *pj) {
	if (!core || !fcn || !pj) {
		return;
	}

	char *pdfj = r_core_cmd_strf (core, "pdfj @ 0x%"PFMT64x, fcn->addr);
	if (!pdfj || pdfj[0] != '{') {
		free (pdfj);
		return;
	}

	RJson *root = r_json_parse (pdfj);
	if (root && root->type == R_JSON_OBJECT) {
		const RJson *ops = r_json_get (root, "ops");
		if (ops && ops->type == R_JSON_ARRAY) {
			RJson *elem;
			for (elem = ops->children.first; elem; elem = elem->next) {
				if (elem->type != R_JSON_OBJECT) {
					continue;
				}
				const RJson *ptr = r_json_get (elem, "ptr");
				if (ptr && ptr->type == R_JSON_INTEGER && ptr->num.u_value) {
					append_pszj_string_to_pj (core, pj, (ut64)ptr->num.u_value);
				}
			}
		}
		r_json_free (root);
	}

	free (pdfj);
}

static char *sleigh_cmd(RAnal *anal, const char *cmd) {
	bool is_sla_ns = r_str_startswith (cmd, "sla");
	bool is_sym_ns = r_str_startswith (cmd, "sym");
	if (!is_sla_ns && !is_sym_ns) {
		return NULL;
	}

	RCore *core = anal->coreb.core;
	RCons *cons = core ? core->cons : NULL;

	if (cmd[3] == '?') {
		if (cons) {
			r_cons_println (cons, "| a:sla        - Show r2sleigh status");
			r_cons_println (cons, "| a:sla.info   - Show current architecture info");
			r_cons_println (cons, "| a:sla.arch [name] - Get/Set Sleigh architecture manually");
			r_cons_println (cons, "| a:sla.json   - Dump r2il ops as JSON for current instruction");
			r_cons_println (cons, "| a:sla.regs   - Show registers read/written by instruction");
			r_cons_println (cons, "| a:sla.opvals - Show analysis srcs/dsts for current instruction");
			r_cons_println (cons, "| a:sla.mem    - Show memory accesses by instruction");
			r_cons_println (cons, "| a:sla.vars   - Show all varnodes used by instruction");
			r_cons_println (cons, "| a:sla.ssa    - Show SSA form of instruction");
			r_cons_println (cons, "| a:sla.defuse - Show def-use analysis of instruction");
			r_cons_println (cons, "| a:sla.types  - Dump inferred type write-back payload for current function");
			r_cons_println (cons, "| a:sla.ssa.func - Show function SSA with phi nodes");
				r_cons_println (cons, "| a:sla.ssa.func.opt - Show optimized function SSA");
				r_cons_println (cons, "| a:sla.defuse.func - Show function-wide def-use analysis");
				r_cons_println (cons, "| a:sla.dom    - Show dominator tree for current function");
				r_cons_println (cons, "| a:sla.slice <var> - Backward slice from variable (e.g. rax_3)");
				r_cons_println (cons, "| a:sla.sym    - Symbolic execution summary for current function");
				r_cons_println (cons, "| a:sla.sym.paths - Explore paths in current function");
			r_cons_println (cons, "| a:sla.sym.merge [on|off] - Toggle symbolic state merging");
			r_cons_println (cons, "| a:sla.taint  - Taint analysis for current function");
			r_cons_println (cons, "| a:sla.dec [name|addr] - Decompile function (current by default)");
			r_cons_println (cons, "| a:sla.cfg    - Show ASCII CFG for current function");
			r_cons_println (cons, "| a:sla.cfg.json - Show CFG as JSON for current function");
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

	if (is_sym_ns && (!strncmp (cmd, "sym.explore", 11) || !strncmp (cmd, "sym.solve", 9))) {
		bool is_explore = r_str_startswith (cmd, "sym.explore");
		size_t prefix_len = is_explore ? 11 : 9;
		const char *arg = skip_cmd_spaces (cmd + prefix_len);
		ut64 target = 0;
		R2ILContext *ctx;
		RAnalFunction *fcn;
		BlockArray blocks;
		char *result = NULL;
		bool rust_owned = true;

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
		fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup("");
		}
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}
		char *sym_map_json = build_sym_symbol_map_json (core);
		if (sym_map_json) {
			r2sym_set_symbol_map_json (sym_map_json);
			free (sym_map_json);
		}

		if (is_explore) {
			result = r2sym_explore_to (ctx, (const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr, target);
		} else {
			result = r2sym_solve_to (ctx, (const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr, target);
		}
		if (!result) {
			rust_owned = false;
			result = strdup ("{\"error\":\"symbolic execution failed\"}");
		}

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}
		if (result && !sym_result_has_error (result)) {
			sym_state_cache_update (is_explore ? "explore" : "solve", fcn->addr, fcn->addr, target, result);
		}

		if (rust_owned) {
			r2il_string_free (result);
		} else {
			free (result);
		}
		block_array_free (&blocks);
		return strdup("");
	}

	if (!strncmp (cmd, "sla.arch", 8)) {
		const char *arg = cmd + 8;
		if (*arg == ' ') {
			arg++; // skip space
			while (*arg == ' ') arg++;
			if (*arg) {
				/* Set override */
				free (sleigh_arch_override);
				sleigh_arch_override = strdup (arg);
				/* Force context reload on next use */
				if (sleigh_ctx) {
					r2il_free (sleigh_ctx);
					sleigh_ctx = NULL;
				}
				free (sleigh_arch);
				sleigh_arch = NULL;
				if (cons) {
					r_cons_printf (cons, "r2sleigh: architecture set to '%s' (reload deferred)\n", sleigh_arch_override);
				}
			}
		} else {
			/* Get current */
			R2ILContext *ctx = get_context (anal);
			const char *name = ctx ? r2il_arch_name (ctx) : NULL;
			if (cons) {
				if (name) {
					r_cons_printf (cons, "%s\n", name);
				} else {
					r_cons_println (cons, "none");
				}
			}
		}
		return strdup("");
	}

	if (!strcmp (cmd, "sla") || !strcmp (cmd, "sla.info")) {
		R2ILContext *ctx = get_context (anal);
		if (ctx) {
			const char *name = r2il_arch_name (ctx);
			if (cons) {
				r_cons_printf (cons, "sla: loaded architecture '%s'\n", name ? name : "unknown");
			}
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

		ut8 buf[SLEIGH_MIN_BYTES];
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = r2il_lift (ctx, buf, sizeof (buf), addr);
		if (!block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		size_t count = r2il_block_op_count (block);
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
				char *json = r2il_block_op_json_named (ctx, block, i);
				if (json && cons) {
					r_cons_printf (cons, "  %s%s\n", json, (i + 1 < count) ? "," : "");
					r2il_string_free (json);
				}
			}
		}
		if (cons) {
			r_cons_println (cons, "]");
		}

		r2il_block_free (block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.regs")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES];
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = r2il_lift (ctx, buf, sizeof (buf), addr);
		if (!block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *read_json = r2il_block_regs_read (ctx, block);
		char *write_json = r2il_block_regs_write (ctx, block);

		if (cons) {
			r_cons_printf (cons, "{\"read\":%s,\"write\":%s}\n",
				read_json ? read_json : "[]",
				write_json ? write_json : "[]");
		}

		r2il_string_free (read_json);
		r2il_string_free (write_json);
		r2il_block_free (block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.opvals")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES];
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = r2il_lift (ctx, buf, sizeof (buf), addr);
		if (!block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		RVecRArchValue srcs;
		RVecRArchValue dsts;
		RVecRArchValue_init (&srcs);
		RVecRArchValue_init (&dsts);

		char *defuse_json = r2il_block_defuse_json (ctx, block);
		if (defuse_json) {
			RJson *root = r_json_parse (defuse_json);
			if (root && root->type == R_JSON_OBJECT) {
				const RJson *inputs = r_json_get (root, "inputs");
				const RJson *outputs = r_json_get (root, "outputs");
				add_ssa_reg_values (anal, inputs, &srcs, R_PERM_R);
				add_ssa_reg_values (anal, outputs, &dsts, R_PERM_W);
			}
			r_json_free (root);
			r2il_string_free (defuse_json);
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
		r2il_block_free (block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.mem")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES];
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = r2il_lift (ctx, buf, sizeof (buf), addr);
		if (!block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *mem_json = r2il_block_mem_access (ctx, block);
		if (cons && mem_json) {
			r_cons_printf (cons, "%s\n", mem_json);
		}

		r2il_string_free (mem_json);
		r2il_block_free (block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.vars")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES];
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = r2il_lift (ctx, buf, sizeof (buf), addr);
		if (!block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *vars_json = r2il_block_varnodes (ctx, block);
		if (cons && vars_json) {
			r_cons_printf (cons, "%s\n", vars_json);
		}

		r2il_string_free (vars_json);
		r2il_block_free (block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.ssa")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES];
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = r2il_lift (ctx, buf, sizeof (buf), addr);
		if (!block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *ssa_json = r2il_block_to_ssa_json (ctx, block);
		if (cons && ssa_json) {
			r_cons_printf (cons, "%s\n", ssa_json);
		}

		r2il_string_free (ssa_json);
		r2il_block_free (block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.defuse")) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		ut64 addr = core->addr;
		ut8 buf[SLEIGH_MIN_BYTES];
		if (!anal->iob.read_at (anal->iob.io, addr, buf, sizeof (buf))) {
			R_LOG_ERROR ("r2sleigh: failed to read bytes at 0x%"PFMT64x, addr);
			return strdup("");
		}

		R2ILBlock *block = r2il_lift (ctx, buf, sizeof (buf), addr);
		if (!block) {
			R_LOG_ERROR ("r2sleigh: lift failed");
			return strdup("");
		}

		char *defuse_json = r2il_block_defuse_json (ctx, block);
		if (cons && defuse_json) {
			r_cons_printf (cons, "%s\n", defuse_json);
		}

		r2il_string_free (defuse_json);
		r2il_block_free (block);
		return strdup("");
	}

	if (!strcmp (cmd, "sla.types")) {
		R2ILContext *ctx = get_context (anal);
		RAnalFunction *fcn;
		BlockArray blocks;
		char *external_context_json = NULL;
		char *interproc_scope_json = NULL;
		char *result = NULL;
		ut64 *seen_addrs = NULL;
		size_t seen_count = 0;
		size_t seen_cap = 0;
		int interproc_max_iters = cfg_get_type_interproc_max_iters (anal);

		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup ("");
		}

		fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		if (!fcn) {
			R_LOG_ERROR ("r2sleigh: no function at current address");
			return strdup ("");
		}
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup ("");
		}

		external_context_json = sleigh_collect_external_context_json (anal, fcn);
		if (!external_context_json || (external_context_json[0] != '{' && external_context_json[0] != '[')) {
			free (external_context_json);
			external_context_json = strdup ("{}");
		}

		warm_type_payload_cache_for_function (core, anal, ctx, fcn, interproc_max_iters,
			&seen_addrs, &seen_count, &seen_cap);
		interproc_scope_json = build_type_interproc_scope_json (core, anal, ctx, fcn, &blocks);
		result = r2sleigh_infer_type_writeback_json_ex (ctx,
			(const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr, fcn->name,
			external_context_json,
			1, interproc_max_iters, 1, interproc_scope_json? interproc_scope_json: "{}");
		if (cons) {
			if (result && *result) {
				r_cons_printf (cons, "%s\n", result);
			} else {
				r_cons_println (cons, "{}");
			}
		}
		if (result) {
			r2il_string_free (result);
		}
		free (seen_addrs);
		free (interproc_scope_json);
		free (external_context_json);
		block_array_free (&blocks);
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
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}

		/* Get function SSA */
		char *result = r2ssa_function_json (ctx, (const R2ILBlock **)blocks.blocks, blocks.count);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		r2il_string_free (result);
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

		char *result = r2ssa_function_opt_json (ctx, (const R2ILBlock **)blocks.blocks, blocks.count);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		r2il_string_free (result);
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
		char *result = r2ssa_defuse_function_json (ctx, (const R2ILBlock **)blocks.blocks, blocks.count);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		r2il_string_free (result);
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
		char *result = r2ssa_domtree_json (ctx, (const R2ILBlock **)blocks.blocks, blocks.count);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		r2il_string_free (result);
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
				r_cons_println (cons, "Usage: a:sla.slice <var_name>");
				r_cons_println (cons, "Example: a:sla.slice rax_3");
				r_cons_println (cons, "         a:sla.slice zf_1");
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
		char *result = r2ssa_backward_slice_json (ctx, (const R2ILBlock **)blocks.blocks, blocks.count, arg);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		r2il_string_free (result);
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
				r2sym_merge_set_enabled (1);
			} else if (!strcmp (arg, "off") || !strcmp (arg, "0") || !strcmp (arg, "false")) {
				r2sym_merge_set_enabled (0);
			} else if (cons) {
				r_cons_println (cons, "Usage: a:sla.sym.merge [on|off]");
				return strdup("");
			}
		} else {
			int enabled = r2sym_merge_is_enabled ();
			r2sym_merge_set_enabled (!enabled);
		}

		if (cons) {
			r_cons_printf (cons, "sym merge: %s\n", r2sym_merge_is_enabled () ? "on" : "off");
		}
		return strdup("");
	}

	if (!strcmp (cmd, "sla.sym") || !strcmp (cmd, "sla.sym.paths")) {
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
		char *sym_map_json = build_sym_symbol_map_json (core);
		if (sym_map_json) {
			r2sym_set_symbol_map_json (sym_map_json);
			free (sym_map_json);
		}

		/* Call symbolic execution */
		char *result;
		if (!strcmp (cmd, "sla.sym.paths")) {
			result = r2sym_paths (ctx, (const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr);
		} else {
			result = r2sym_function (ctx, (const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr);
		}

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		r2il_string_free (result);
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

		char *result = r2taint_function_json (ctx, (const R2ILBlock **)blocks.blocks, blocks.count);

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		r2il_string_free (result);
		block_array_free (&blocks);
		return strdup("");
	}

	if (!strncmp (cmd, "sla.dec", 7)) {
		R2ILContext *ctx = get_context (anal);
		if (!ctx) {
			R_LOG_ERROR ("r2sleigh: no context");
			return strdup("");
		}

		const char *target_arg = skip_cmd_spaces (cmd + 7);
		RAnalFunction *fcn = NULL;
		if (target_arg && *target_arg) {
			fcn = resolve_function_target (core, anal, target_arg);
		} else {
			fcn = r_anal_get_fcn_in (anal, core->addr, R_ANAL_FCN_TYPE_ANY);
		}

		if (!fcn) {
			if (target_arg && *target_arg) {
				if (cons) {
					r_cons_printf (cons,
						"/* r2dec: function target '%s' not found. It may be inlined or stripped. Try 'afl' or 'a:sla.dec 0xADDR'. */\n",
						target_arg);
				}
			} else {
				R_LOG_ERROR ("r2sleigh: no function at current address");
			}
			return strdup("");
		}

		/* Lift all blocks */
		BlockArray blocks;
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			R_LOG_ERROR ("r2sleigh: failed to lift function blocks");
			return strdup("");
		}

		/* Gather function names from r2 */
		char *func_names_json = NULL;
		char *strings_json = NULL;
		char *symbols_json = NULL;
		char *external_context_json = NULL;

		/* Get function list as JSON and convert to our format */
		/* aflj returns [{addr:0x401000,name:"main"}, ...] */
		char *aflj = r_core_cmd_str (core, "aflj");
		if (aflj && aflj[0] == '[') {
			/* Convert to {addr: name} format */
			PJ *pj = pj_new ();
			pj_o (pj);
			/* Parse the array manually */
			RJson *root = r_json_parse (aflj);
			if (root && root->type == R_JSON_ARRAY) {
				RJson *elem;
				for (elem = root->children.first; elem; elem = elem->next) {
					if (elem->type == R_JSON_OBJECT) {
						const RJson *addr = r_json_get (elem, "addr");
						const RJson *name = r_json_get (elem, "name");
						if (addr && name && addr->type == R_JSON_INTEGER && name->type == R_JSON_STRING) {
							char addr_str[32];
							snprintf (addr_str, sizeof(addr_str), "0x%llx", (unsigned long long)addr->num.u_value);
							pj_ks (pj, addr_str, name->str_value);
						}
					}
				}
				r_json_free (root);
			}
			pj_end (pj);
			func_names_json = pj_drain (pj);
		}
		free (aflj);

		/* Get strings: izj returns [{vaddr:0x402000,string:"Hello"}, ...] */
		char *izj = r_core_cmd_str (core, "izj");
		if (izj && izj[0] == '[') {
			PJ *pj = pj_new ();
			pj_o (pj);
			RJson *root = r_json_parse (izj);
			if (root && root->type == R_JSON_ARRAY) {
				RJson *elem;
				for (elem = root->children.first; elem; elem = elem->next) {
					if (elem->type == R_JSON_OBJECT) {
						const RJson *vaddr = r_json_get (elem, "vaddr");
						const RJson *str = r_json_get (elem, "string");
						if (vaddr && str && vaddr->type == R_JSON_INTEGER && str->type == R_JSON_STRING) {
							ut64 addr = (ut64)vaddr->num.u_value;
							if (!r_io_is_valid_offset (core->io, addr, 0)) {
								continue;
							}
							char addr_str[32];
							snprintf (addr_str, sizeof(addr_str), "0x%llx", (unsigned long long)addr);
							pj_ks (pj, addr_str, str->str_value);
						}
					}
				}
				r_json_free (root);
			}
			extend_string_map_with_function_ptr_strings (core, fcn, pj);
			pj_end (pj);
			strings_json = pj_drain (pj);
		}
		free (izj);

		/* Get global symbols/flags: fj returns [{name:"sym.foo",offset:0x401000}, ...] */
		/* Use 'fs *;fj' to get flags from all flagspaces (including relocs) */
		char *fj = r_core_cmd_str (core, "fs *;fj");
		if (fj && fj[0] == '[') {
			PJ *pj = pj_new ();
			pj_o (pj);
			RJson *root = r_json_parse (fj);
			if (root && root->type == R_JSON_ARRAY) {
				RJson *elem;
				for (elem = root->children.first; elem; elem = elem->next) {
					if (elem->type == R_JSON_OBJECT) {
						const RJson *offset = r_json_get (elem, "addr");
						const RJson *name = r_json_get (elem, "name");
						if (offset && name && offset->type == R_JSON_INTEGER && name->type == R_JSON_STRING) {
							/* Skip strings (already in strings_json), sections, and low-signal linker/locator symbols */
							const char *n = name->str_value;
							if (n && strncmp (n, "str.", 4) != 0
							    && strncmp (n, "section.", 8) != 0
							    && strncmp (n, "loc.", 4) != 0
							    && strcmp (n, "obj.__TMC_END__") != 0
							    && strcmp (n, "obj.__FRAME_END__") != 0
							    && strcmp (n, "obj.__dso_handle") != 0
							    && strcmp (n, "obj.completed.0") != 0) {
								char addr_str[32];
								snprintf (addr_str, sizeof (addr_str), "0x%llx", (unsigned long long)offset->num.u_value);
								pj_ks (pj, addr_str, n);
							}
						}
					}
				}
				r_json_free (root);
			}
			pj_end (pj);
			symbols_json = pj_drain (pj);
		}
		free (fj);

			external_context_json = sleigh_collect_external_context_json (anal, fcn);
			if (!external_context_json || (external_context_json[0] != '{' && external_context_json[0] != '[')) {
				free (external_context_json);
				external_context_json = strdup ("{}");
			}

			/* Decompile with context */
			char *result = r2dec_function_with_context (ctx, (const R2ILBlock **)blocks.blocks, blocks.count,
			                                             fcn->name, func_names_json, strings_json, symbols_json,
			                                             external_context_json);

		if (cons) {
			if (result && result[0]) {
				r_cons_printf (cons, "%s\n", result);
			} else {
				const char *fname = (fcn && fcn->name) ? fcn->name : "unknown";
				r_cons_printf (cons, "/* r2dec fallback: empty decompilation output for %s */\n", fname);
			}
		}

		if (result) {
			r2il_string_free (result);
		}
		free (func_names_json);
		free (strings_json);
			free (symbols_json);
			free (external_context_json);
			block_array_free (&blocks);
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
		char *result;
		if (!strcmp (cmd, "sla.cfg.json")) {
			result = r2cfg_function_json (ctx, (const R2ILBlock **)blocks.blocks, blocks.count);
		} else {
			result = r2cfg_function_ascii (ctx, (const R2ILBlock **)blocks.blocks, blocks.count);
		}

		if (cons && result) {
			r_cons_printf (cons, "%s\n", result);
		}

		r2il_string_free (result);
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

	R2ILContext *ctx = get_context (anal);
	if (!ctx) {
		return false;
	}

	if (sleigh_mode_is_fast (anal)) {
		return true;
	}

	BlockArray blocks;
	ut64 cache_key;
	if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
		return false;
	}

	size_t semantic_comments_emitted = write_semantic_comments_for_function (
		anal, ctx, &blocks, fcn->addr, true);
	R_LOG_DEBUG ("r2sleigh: semantic comments fcn=0x%"PFMT64x" enabled=%d emitted=%zu",
		fcn->addr, 1, semantic_comments_emitted);

	cache_key = compute_xref_cache_key (fcn, &blocks, sleigh_mode_effective_for_post_analysis (anal));
	if (!data_ref_cache_get (fcn->addr) || data_ref_cache_get (fcn->addr)->key != cache_key) {
		char *xref_json = r2sleigh_get_data_refs (ctx,
			(const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr);
		if (xref_json && *xref_json) {
			int ref_count = collect_data_refs_from_json (anal, fcn, xref_json, NULL, true);
			data_ref_cache_put (fcn->addr, cache_key, r_str_hash64 (xref_json), ref_count);
		}
		r2il_string_free (xref_json);
	}

	block_array_free (&blocks);
	return true;
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
	if (sleigh_mode_is_fast (anal)) {
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

	char *json = r2sleigh_recover_vars (ctx,
		(const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr);

	block_array_free (&blocks);

	if (!json || !*json) {
		r2il_string_free (json);
		return NULL;
	}

	/* Parse JSON and create RList of RAnalVarProt */
	RList *vars = r_list_newf ((RListFree)var_prot_free);
	if (!vars) {
		r2il_string_free (json);
		return NULL;
	}

	RJson *root = r_json_parse (json);
	if (!root || root->type != R_JSON_ARRAY) {
		r2il_string_free (json);
		r_list_free (vars);
		return NULL;
	}

	const RJson *item;
	for (item = root->children.first; item; item = item->next) {
		if (item->type != R_JSON_OBJECT) {
			continue;
		}

		const RJson *j_name = r_json_get (item, "name");
		const RJson *j_kind = r_json_get (item, "kind");
		const RJson *j_delta = r_json_get (item, "delta");
		const RJson *j_type = r_json_get (item, "type");
		const RJson *j_isarg = r_json_get (item, "isarg");
		const RJson *j_reg = r_json_get (item, "reg");

		if (!j_name || !j_kind || !j_delta || !j_type) {
			continue;
		}

		RAnalVarProt *prot = R_NEW0 (RAnalVarProt);
		if (!prot) {
			continue;
		}

		prot->name = strdup (j_name->str_value ? j_name->str_value : "");
		prot->type = strdup (j_type->str_value ? j_type->str_value : "int64_t");
		prot->delta = (st64)j_delta->num.s_value;
		prot->isarg = j_isarg && j_isarg->type == R_JSON_BOOLEAN && j_isarg->num.u_value;

		/* Parse kind: "r" = register, "s" = stack, "b" = bp-relative */
		if (j_kind->str_value) {
			switch (j_kind->str_value[0]) {
			case 'r':
				/* Register-based argument: use r_reg_get to find index */
				if (j_reg && j_reg->str_value && anal->reg) {
					/* Try uppercase version (Sleigh uses uppercase reg names) */
					char *upper_reg = strdup (j_reg->str_value);
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
						ri = r_reg_get (anal->reg, j_reg->str_value, R_REG_TYPE_GPR);
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

	r_json_free (root);
	r2il_string_free (json);

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

static void ensure_literal_ref_target_map(RAnal *anal, ut64 to_addr) {
	RCore *core;
	RIOMap *map;
	int fd;
	char map_name[64];

	if (!anal || !to_addr) {
		return;
	}
	core = anal->coreb.core;
	if (!core || !core->io) {
		return;
	}
	if (r_io_map_get_at (core->io, to_addr)) {
		return;
	}
	fd = r_io_fd_get_current (core->io);
	if (fd < 0) {
		return;
	}
	map = r_io_map_add (core->io, fd, R_PERM_R, 0, to_addr, 1);
	if (!map) {
		return;
	}
	snprintf (map_name, sizeof (map_name), "sla.literal.%"PFMT64x, to_addr);
	r_io_map_set_name (map, map_name);
}

static int collect_data_refs_from_json(
	RAnal *anal,
	RAnalFunction *fcn,
	const char *json,
	RVecAnalRef *refs,
	bool apply_to_anal
) {
	RJson *root;
	const RJson *item;
	int added = 0;
	char *json_copy;

	if (!anal || !json || !*json) {
		return 0;
	}

	json_copy = strdup (json);
	if (!json_copy) {
		return 0;
	}
	root = r_json_parse (json_copy);
	if (!root || root->type != R_JSON_ARRAY) {
		free (json_copy);
		r_json_free (root);
		return 0;
	}

	for (item = root->children.first; item; item = item->next) {
		const RJson *j_from;
		const RJson *j_to;
		const RJson *j_type;
		ut64 from_addr;
		ut64 to_addr;
		RAnalRefType ref_type;

		if (item->type != R_JSON_OBJECT) {
			continue;
		}
		j_from = r_json_get (item, "from");
		j_to = r_json_get (item, "to");
		j_type = r_json_get (item, "type");
		if (!j_from || !j_to) {
			continue;
		}

		from_addr = (ut64)j_from->num.u_value;
		to_addr = (ut64)j_to->num.u_value;
		if (fcn && to_addr >= fcn->addr && to_addr < fcn->addr + r_anal_function_linear_size (fcn)) {
			continue;
		}
		ref_type = data_ref_type_from_json (anal, to_addr, j_type? j_type->str_value: NULL);
		if (apply_to_anal && ref_type == R_ANAL_REF_TYPE_DATA) {
			ensure_literal_ref_target_map (anal, to_addr);
		}

		if (refs) {
			RAnalRef ref = {
				.at = from_addr,
				.addr = to_addr,
				.type = ref_type,
			};
			RVecAnalRef_push_back (refs, &ref);
		}
		if (apply_to_anal && r_anal_xrefs_set (anal, from_addr, to_addr, ref_type)) {
			added++;
		} else if (!apply_to_anal) {
			added++;
		}
	}

	r_json_free (root);
	free (json_copy);
	return added;
}

/* Called during reference analysis (aar) */
static RVecAnalRef *sleigh_get_data_refs(RAnal *anal, RAnalFunction *fcn) {
	if (!fcn || !anal) {
		return NULL;
	}
	if (sleigh_mode_is_fast (anal)) {
		return NULL;
	}

	R2ILContext *ctx = get_context (anal);
	if (!ctx) {
		return NULL;
	}

	BlockArray blocks;
	ut64 cache_key;
	if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
		return NULL;
	}
	cache_key = compute_xref_cache_key (fcn, &blocks, sleigh_mode_effective_for_post_analysis (anal));

	char *json = r2sleigh_get_data_refs (ctx,
		(const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr);

	if (!json || !*json) {
		r2il_string_free (json);
		block_array_free (&blocks);
		return NULL;
	}

	/* Parse JSON and create RVecAnalRef */
	RVecAnalRef *refs = RVecAnalRef_new ();
	if (!refs) {
		r2il_string_free (json);
		block_array_free (&blocks);
		return NULL;
	}
	int ref_count = collect_data_refs_from_json (anal, fcn, json, refs, true);
	data_ref_cache_put (fcn->addr, cache_key, r_str_hash64 (json), ref_count);
	r2il_string_free (json);
	block_array_free (&blocks);

	if (RVecAnalRef_empty (refs)) {
		RVecAnalRef_free (refs);
		return NULL;
	}

	return refs;
}

static bool is_signature_writeback_arch_supported (const char *arch_name) {
	return arch_name && *arch_name;
}

static bool is_type_writeback_arch_supported (const char *arch_name) {
	return arch_name && *arch_name;
}

static bool is_callconv_writeback_arch_supported (const char *arch_name) {
	return arch_name
		&& (!strcmp (arch_name, "x86") || !strcmp (arch_name, "x86-64")
		|| !strcmp (arch_name, "x86_64") || !strcmp (arch_name, "x64")
		|| !strcmp (arch_name, "amd64"));
}

static bool is_x64_signature_arch (const char *arch_name) {
	return arch_name
		&& (!strcmp (arch_name, "x86-64")
		|| !strcmp (arch_name, "x86_64")
		|| !strcmp (arch_name, "x64")
		|| !strcmp (arch_name, "amd64"));
}

static const RJson *json_next_object (const RJson *item) {
	const RJson *cur = item;
	while (cur && cur->type != R_JSON_OBJECT) {
		cur = cur->next;
	}
	return cur;
}

static int json_array_object_count(const RJson *array_root);
static bool json_is_string_with_value(const RJson *value);
static bool is_caller_propagation_ref_type (RAnalRefType type);

static char *normalize_compare_string (const char *s) {
	size_t len;
	char *out;
	size_t i;
	size_t j = 0;

	if (!s) {
		return strdup ("");
	}
	len = strlen (s);
	out = malloc (len + 1);
	if (!out) {
		return strdup ("");
	}
	for (i = 0; i < len; i++) {
		unsigned char ch = (unsigned char)s[i];
		if (isspace (ch) || ch == ';') {
			continue;
		}
		out[j++] = (char)tolower (ch);
	}
	out[j] = '\0';
	return out;
}

static bool strings_match_normalized (const char *a, const char *b) {
	char *na = normalize_compare_string (a);
	char *nb = normalize_compare_string (b);
	bool match;
	if (!na || !nb) {
		free (na);
		free (nb);
		return false;
	}
	match = !strcmp (na, nb);
	free (na);
	free (nb);
	return match;
}

static void remove_substring_inplace(char *s, const char *needle) {
	size_t needle_len;
	char *hit;

	if (!s || !needle || !*needle) {
		return;
	}
	needle_len = strlen (needle);
	hit = strstr (s, needle);
	while (hit) {
		memmove (hit, hit + needle_len, strlen (hit + needle_len) + 1);
		hit = strstr (s, needle);
	}
}

static char *normalize_type_for_compare(const char *s, bool long_is_i64) {
	char *normalized;
	size_t i;
	size_t stars = 0;
	size_t base_len = 0;
	char *base;
	const char *mapped;
	char *out;
	size_t mapped_len;

	normalized = normalize_compare_string (s);
	if (!normalized) {
		return strdup ("");
	}

	remove_substring_inplace (normalized, "const");
	remove_substring_inplace (normalized, "volatile");
	remove_substring_inplace (normalized, "restrict");
	remove_substring_inplace (normalized, "register");
	remove_substring_inplace (normalized, "struct");
	remove_substring_inplace (normalized, "union");
	remove_substring_inplace (normalized, "enum");
	remove_substring_inplace (normalized, "class");

	base = malloc (strlen (normalized) + 1);
	if (!base) {
		free (normalized);
		return strdup ("");
	}
	for (i = 0; normalized[i]; i++) {
		if (normalized[i] == '*') {
			stars++;
		} else {
			base[base_len++] = normalized[i];
		}
	}
	base[base_len] = '\0';

	if (!strcmp (base, "signed") || !strcmp (base, "signedint")
			|| !strcmp (base, "int") || !strcmp (base, "int32_t")) {
		mapped = "int32_t";
	} else if (!strcmp (base, "long") || !strcmp (base, "longint")) {
		mapped = long_is_i64 ? "int64_t" : "long";
	} else if (!strcmp (base, "longlong") || !strcmp (base, "longlongint")
			|| !strcmp (base, "int64_t") || !strcmp (base, "__int64")) {
		mapped = "int64_t";
	} else if (!strcmp (base, "short") || !strcmp (base, "shortint")
			|| !strcmp (base, "int16_t")) {
		mapped = "int16_t";
	} else if (!strcmp (base, "void")) {
		mapped = "void";
	} else {
		mapped = base;
	}

	mapped_len = strlen (mapped);
	out = malloc (mapped_len + stars + 1);
	if (!out) {
		free (base);
		free (normalized);
		return strdup ("");
	}
	memcpy (out, mapped, mapped_len);
	for (i = 0; i < stars; i++) {
		out[mapped_len + i] = '*';
	}
	out[mapped_len + stars] = '\0';

	free (base);
	free (normalized);
	return out;
}

static bool types_match_canonical(const char *a, const char *b, bool long_is_i64) {
	char *na = normalize_type_for_compare (a, long_is_i64);
	char *nb = normalize_type_for_compare (b, long_is_i64);
	bool match;

	if (!na || !nb) {
		free (na);
		free (nb);
		return false;
	}
	match = !strcmp (na, nb);
	free (na);
	free (nb);
	return match;
}

static void write_reason_msg(char *buf, size_t buf_sz, const char *fmt, ...) {
	va_list ap;
	if (!buf || !buf_sz) {
		return;
	}
	va_start (ap, fmt);
	vsnprintf (buf, buf_sz, fmt, ap);
	va_end (ap);
}

static bool verify_signature_type_db_ex(RAnal *anal, RAnalFunction *fcn, const RJson *sig_root, char *reason, size_t reason_sz) {
	const RJson *j_expected_ret;
	const RJson *j_expected_params;
	const RJson *j_expected_arch;
	char *typed_name = NULL;
	const char *actual_ret;
	const RJson *expected_param;
	bool long_is_i64 = false;
	int expected_count;
	int actual_count;
	int i;

	if (reason && reason_sz) {
		reason[0] = '\0';
	}
	if (!anal || !fcn || !fcn->name || !sig_root || sig_root->type != R_JSON_OBJECT) {
		write_reason_msg (reason, reason_sz, "invalid verification inputs");
		return false;
	}
	j_expected_ret = r_json_get (sig_root, "ret_type");
	j_expected_params = r_json_get (sig_root, "params");
	j_expected_arch = r_json_get (sig_root, "arch");
	if (!j_expected_ret || j_expected_ret->type != R_JSON_STRING
			|| !j_expected_ret->str_value
			|| !j_expected_params || j_expected_params->type != R_JSON_ARRAY) {
		write_reason_msg (reason, reason_sz, "missing ret_type/params in payload");
		return false;
	}
	if (j_expected_arch && j_expected_arch->type == R_JSON_STRING && j_expected_arch->str_value) {
		long_is_i64 = is_x64_signature_arch (j_expected_arch->str_value);
	}

	typed_name = r_type_func_name (anal->sdb_types, fcn->name);
	if (!typed_name) {
		write_reason_msg (reason, reason_sz, "typed name missing in type db for %s", fcn->name);
		return false;
	}
	actual_ret = r_type_func_ret (anal->sdb_types, typed_name);
	if (!actual_ret || !types_match_canonical (j_expected_ret->str_value, actual_ret, long_is_i64)) {
		write_reason_msg (reason, reason_sz, "return mismatch expected=%s actual=%s",
			j_expected_ret->str_value, actual_ret? actual_ret: "<missing>");
		free (typed_name);
		return false;
	}

	expected_count = json_array_object_count (j_expected_params);
	actual_count = r_type_func_args_count (anal->sdb_types, typed_name);
	if (expected_count == 0 && actual_count == 1) {
		char *actual_arg0 = r_type_func_args_type (anal->sdb_types, typed_name, 0);
		if (actual_arg0 && types_match_canonical (actual_arg0, "void", long_is_i64)) {
			actual_count = 0;
		}
		free (actual_arg0);
	}
	if (expected_count != actual_count) {
		write_reason_msg (reason, reason_sz, "argc mismatch expected=%d actual=%d",
			expected_count, actual_count);
		free (typed_name);
		return false;
	}

	expected_param = json_next_object (j_expected_params->children.first);
	for (i = 0; i < expected_count; i++) {
		const RJson *j_expected_type;
		char *actual_type;
		bool match;

		if (!expected_param || expected_param->type != R_JSON_OBJECT) {
			write_reason_msg (reason, reason_sz, "malformed expected param entry at index %d", i);
			free (typed_name);
			return false;
		}
		j_expected_type = r_json_get (expected_param, "type");
		if (!j_expected_type || j_expected_type->type != R_JSON_STRING
				|| !j_expected_type->str_value) {
			write_reason_msg (reason, reason_sz, "missing expected arg type at index %d", i);
			free (typed_name);
			return false;
		}
		actual_type = r_type_func_args_type (anal->sdb_types, typed_name, i);
		match = actual_type
			&& types_match_canonical (j_expected_type->str_value, actual_type, long_is_i64);
		if (!match) {
			write_reason_msg (reason, reason_sz, "arg[%d] type mismatch expected=%s actual=%s",
				i, j_expected_type->str_value, actual_type? actual_type: "<missing>");
			free (actual_type);
			free (typed_name);
			return false;
		}
		free (actual_type);
		expected_param = json_next_object (expected_param->next);
	}
	if (expected_param) {
		write_reason_msg (reason, reason_sz, "unexpected trailing expected param entry");
		free (typed_name);
		return false;
	}
	free (typed_name);
	return true;
}

static bool verify_callconv_apply(RAnal *anal, ut64 fcn_addr, const char *cc_name) {
	RAnalFunction *target_fcn;

	if (!anal || !cc_name || !*cc_name) {
		return false;
	}
	target_fcn = r_anal_get_fcn_in (anal, fcn_addr, 0);
	if (!target_fcn || !target_fcn->callconv || !*target_fcn->callconv) {
		return false;
	}
	return strings_match_normalized (target_fcn->callconv, cc_name);
}

static bool verify_practical_signature_consistency (
	RAnal *anal,
	RAnalFunction *fcn,
	const RJson *sig_root,
	bool check_signature,
	bool check_callconv,
	bool *afij_signature_drift,
	ConsistencyReasonCounters *reason_counters
);

static bool apply_inferred_signature_typed(
	RAnal *anal,
	RAnalFunction *fcn,
	const RJson *sig_root,
	char *reason,
	size_t reason_sz
) {
	const RJson *j_expected_ret;
	const RJson *j_expected_params;
	const RJson *j_expected_callconv;
	RAnalFunctionSignature input = {0};
	RList *param_list = NULL;
	bool ok = false;
	int param_count = 0;
	int i = 0;
	const RJson *expected_param;

	if (reason && reason_sz) {
		reason[0] = '\0';
	}
	if (!anal || !fcn || !sig_root || sig_root->type != R_JSON_OBJECT) {
		write_reason_msg (reason, reason_sz, "invalid typed signature payload");
		return false;
	}

	j_expected_ret = r_json_get (sig_root, "ret_type");
	j_expected_params = r_json_get (sig_root, "params");
	j_expected_callconv = r_json_get (sig_root, "callconv");
	if (!json_is_string_with_value (j_expected_ret) || !j_expected_params || j_expected_params->type != R_JSON_ARRAY) {
		write_reason_msg (reason, reason_sz, "missing typed ret_type/params in payload");
		return false;
	}

	param_count = json_array_object_count (j_expected_params);
	if (param_count > 0) {
		param_list = r_list_newf (free);
		if (!param_list) {
			write_reason_msg (reason, reason_sz, "oom allocating typed signature params");
			return false;
		}
	}
	expected_param = json_next_object (j_expected_params->children.first);
	while (expected_param && i < param_count) {
		const RJson *j_expected_type = r_json_get (expected_param, "type");
		const RJson *j_expected_name = r_json_get (expected_param, "name");

		if (!json_is_string_with_value (j_expected_type)) {
			write_reason_msg (reason, reason_sz, "missing typed arg type at index %d", i);
			r_list_free (param_list);
			return false;
		}
		RAnalFunctionSignatureParam *param = R_NEW0 (RAnalFunctionSignatureParam);
		if (!param) {
			write_reason_msg (reason, reason_sz, "oom allocating typed signature param at index %d", i);
			r_list_free (param_list);
			return false;
		}
		param->type = (char *)j_expected_type->str_value;
		param->name = json_is_string_with_value (j_expected_name)? (char *)j_expected_name->str_value: NULL;
		r_list_append (param_list, param);
		expected_param = json_next_object (expected_param->next);
		i++;
	}
	if (expected_param || i != param_count) {
		write_reason_msg (reason, reason_sz, "typed param count mismatch while materializing payload");
		r_list_free (param_list);
		return false;
	}

	input.ret_type = (char *)j_expected_ret->str_value;
	input.callconv = json_is_string_with_value (j_expected_callconv)? (char *)j_expected_callconv->str_value: NULL;
	input.params = param_list;
	input.noreturn = fcn->is_noreturn;
	ok = r_anal_function_set_signature (anal, fcn, &input);
	r_list_free (param_list);
	if (!ok) {
		write_reason_msg (reason, reason_sz, "typed signature apply failed");
	}
	return ok;
}

static WritebackApplyResult apply_inferred_signature(
	RAnal *anal,
	RCore *core,
	RAnalFunction *fcn,
	const char *signature,
	const RJson *sig_root
) {
	WritebackApplyResult res = {0};
	int rc;

	if (!anal || !fcn || !signature || !*signature || !sig_root) {
		return res;
	}
	if (verify_signature_type_db_ex (anal, fcn, sig_root, res.detail, sizeof (res.detail))) {
		res.already_applied = true;
		if (!res.detail[0]) {
			write_reason_msg (res.detail, sizeof (res.detail), "signature already matches");
		}
		return res;
	}
	if (verify_practical_signature_consistency (anal, fcn, sig_root, true, false, NULL, NULL)) {
		res.already_applied = true;
		write_reason_msg (res.detail, sizeof (res.detail), "practical signature already matches");
		return res;
	}
	rc = apply_inferred_signature_typed (anal, fcn, sig_root, res.detail, sizeof (res.detail))? 1: 0;
	if (rc > 0) {
		if (verify_signature_type_db_ex (anal, fcn, sig_root, res.detail, sizeof (res.detail))
				|| verify_practical_signature_consistency (anal, fcn, sig_root, true, false, NULL, NULL)) {
			res.path = WRITEBACK_APPLY_API;
			return res;
		}
	}
	if (rc <= 0 && !res.detail[0]) {
		write_reason_msg (res.detail, sizeof (res.detail), "typed signature apply rc=%d", rc);
	}
	res.api_verify_fail = true;
	if (!core) {
		return res;
	}
	res.cmd_fallback_attempted = true;
	if (R_STR_ISEMPTY (signature)) {
		res.cmd_apply_fail = true;
		return res;
	}
	r_core_cmdf_at (core, fcn->addr, "afs %s", signature);
	if (verify_signature_type_db_ex (anal, fcn, sig_root, res.detail, sizeof (res.detail))
			|| verify_practical_signature_consistency (anal, fcn, sig_root, true, false, NULL, NULL)) {
		res.path = WRITEBACK_APPLY_CMD;
		return res;
	}
	res.cmd_apply_fail = true;
	return res;
}

static WritebackApplyResult apply_inferred_callconv (RAnal *anal, RCore *core, RAnalFunction *fcn, const char *cc_name) {
	WritebackApplyResult res = {0};
	const char *pooled_cc = NULL;

	if (!anal || !fcn || !cc_name || !*cc_name) {
		return res;
	}
	if (verify_callconv_apply (anal, fcn->addr, cc_name)) {
		res.already_applied = true;
		write_reason_msg (res.detail, sizeof (res.detail), "callconv already matches");
		return res;
	}
	if (r_anal_cc_exist (anal, cc_name)) {
		pooled_cc = r_str_constpool_get (&anal->constpool, cc_name);
		if (pooled_cc) {
			fcn->callconv = pooled_cc;
			if (verify_callconv_apply (anal, fcn->addr, cc_name)) {
				res.path = WRITEBACK_APPLY_API;
				return res;
			}
		}
	}
	res.api_verify_fail = true;
	if (!core) {
		return res;
	}
	res.cmd_fallback_attempted = true;
	r_core_cmdf_at (core, fcn->addr, "afc %s", cc_name);
	if (verify_callconv_apply (anal, fcn->addr, cc_name)) {
		res.path = WRITEBACK_APPLY_CMD;
		return res;
	}
	res.cmd_apply_fail = true;
	return res;
}

typedef struct {
	int vars_considered;
	int vars_applied;
	int vars_hint_only;
	int vars_skipped_low_conf;
	int vars_skipped_conflict;
	int vars_api_verify_fail;
	int vars_cmd_fallback_attempted;
	int vars_cmd_apply_fail;
	int renames_considered;
	int renames_applied;
	int renames_skipped_low_conf;
	int renames_skipped_conflict;
	int rename_generated_guard_skips;
	int structs_considered;
	int structs_imported;
	int structs_skipped_low_conf;
	int structs_import_fail;
	int global_links_considered;
	int global_links_applied;
	int global_links_skipped_low_conf;
	int global_links_conflict_skip;
	int global_links_existing_preserved;
	int global_links_fail;
	int payload_parse_failures;
	int payload_missing;
	int cache_hits;
	int cache_misses;
	int cache_invalidates;
	int cache_updates;
	int type_fcns_skipped_arch;
	int type_fcns_skipped_size;
	int fixpoint_iters;
	int fixpoint_converged;
	int fixpoint_queue_pushes;
	int fixpoint_queue_pops;
	int fixpoint_requeues;
	char fixpoint_stop_reason[16];
} TypeWritebackCounters;

static bool json_is_string_with_value(const RJson *value) {
	return value && value->type == R_JSON_STRING && value->str_value && *value->str_value;
}

static int confidence_threshold_for_mode(int base, SleighTypeWritebackMode mode, int aggressive_delta) {
	if (mode == SLEIGH_TYPE_WRITEBACK_OFF) {
		return 101;
	}
	if (mode == SLEIGH_TYPE_WRITEBACK_AGGRESSIVE) {
		return R_MAX (1, base - aggressive_delta);
	}
	return base;
}

static bool is_opaque_placeholder_type_name(const char *type_name) {
	char *normalized;
	bool opaque = false;

	if (!type_name || !*type_name) {
		return false;
	}
	normalized = normalize_compare_string (type_name);
	if (!normalized) {
		return false;
	}
	if (strstr (normalized, "type_0x")) {
		opaque = true;
	}
	free (normalized);
	return opaque;
}

static bool is_generic_type_name(const char *type_name) {
	char *normalized;
	bool generic;

	if (!type_name || !*type_name) {
		return true;
	}
	if (is_opaque_placeholder_type_name (type_name)) {
		return true;
	}
	normalized = normalize_compare_string (type_name);
	if (!normalized) {
		return true;
	}
	generic = !strcmp (normalized, "void*")
		|| !strcmp (normalized, "char*")
		|| !strcmp (normalized, "int")
		|| !strcmp (normalized, "unsigned")
		|| !strcmp (normalized, "long")
		|| !strcmp (normalized, "unsignedlong")
		|| !strcmp (normalized, "unknown")
		|| !strncmp (normalized, "int", 3)
		|| !strncmp (normalized, "uint", 4)
		|| !strncmp (normalized, "byte[", 5);
	free (normalized);
	return generic;
}

static bool is_generated_var_name(const char *name) {
	const char *p;
	if (!name || !*name) {
		return true;
	}
	if (!strncmp (name, "arg", 3)) {
		p = name + 3;
		if (*p) {
			while (*p) {
				if (!isdigit ((unsigned char)*p)) {
					break;
				}
				p++;
			}
			if (!*p) {
				return true;
			}
		}
	}
	return !strncmp (name, "var_", 4)
		|| !strncmp (name, "local_", 6)
		|| !strncmp (name, "stack_", 6)
		|| !strncmp (name, "arg_", 4);
}

static int resolve_reg_index(RAnal *anal, const char *reg_name) {
	char *upper_reg;
	RRegItem *ri;
	int index = -1;

	if (!anal || !anal->reg || !reg_name || !*reg_name) {
		return -1;
	}
	upper_reg = strdup (reg_name);
	if (upper_reg) {
		char *p;
		for (p = upper_reg; *p; p++) {
			*p = toupper ((unsigned char)*p);
		}
	}
	ri = upper_reg? r_reg_get (anal->reg, upper_reg, R_REG_TYPE_GPR): NULL;
	if (!ri) {
		ri = r_reg_get (anal->reg, reg_name, R_REG_TYPE_GPR);
	}
	if (ri) {
		index = ri->index;
		r_unref (ri);
	}
	free (upper_reg);
	return index;
}

static RAnalVar *lookup_var_for_candidate(RAnal *anal, RAnalFunction *fcn, const char *name, char kind, int delta, const char *reg_name) {
	RAnalVar *var = NULL;
	int resolved_delta = delta;

	if (!fcn) {
		return NULL;
	}
	if (name && *name) {
		var = r_anal_function_get_var_byname (fcn, name);
		if (var) {
			return var;
		}
	}
	if (kind == R_ANAL_VAR_KIND_REG && reg_name && *reg_name) {
		int reg_index = resolve_reg_index (anal, reg_name);
		if (reg_index >= 0) {
			resolved_delta = reg_index;
		}
	}
	if (kind == R_ANAL_VAR_KIND_REG || kind == R_ANAL_VAR_KIND_BPV || kind == R_ANAL_VAR_KIND_SPV) {
		return r_anal_function_get_var (fcn, kind, resolved_delta);
	}
	return NULL;
}

static bool verify_var_type_applied(RAnalVar *var, const char *expected_type) {
	if (!var || !expected_type || !*expected_type || !var->type || !*var->type) {
		return false;
	}
	return strings_match_normalized (var->type, expected_type);
}

static bool verify_var_rename_applied(RAnalVar *var, const char *expected_name) {
	if (!var || !expected_name || !*expected_name || !var->name || !*var->name) {
		return false;
	}
	return !strcmp (var->name, expected_name);
}

static bool is_composite_type_kind(RTypeKind kind) {
	return kind == R_TYPE_STRUCT || kind == R_TYPE_UNION || kind == R_TYPE_ENUM;
}

static bool type_name_is_materialized(RAnal *anal, const char *type_name) {
	RTypeKind kind;
	ut64 bitsize;

	if (!anal || !anal->sdb_types || !type_name || !*type_name) {
		return false;
	}
	kind = r_type_kind (anal->sdb_types, type_name);
	bitsize = r_type_get_bitsize (anal->sdb_types, type_name);
	return bitsize > 0 || is_composite_type_kind (kind);
}

static const char *canonicalize_type_name_for_apply(const char *type_name, char *buf, size_t buf_sz) {
	const char *trim_start;
	const char *trim_end;
	size_t len;
	char *star;

	if (!type_name || !buf || buf_sz < 8) {
		return type_name;
	}
	trim_start = type_name;
	while (*trim_start && isspace ((unsigned char)*trim_start)) {
		trim_start++;
	}
	trim_end = trim_start + strlen (trim_start);
	while (trim_end > trim_start && isspace ((unsigned char)trim_end[-1])) {
		trim_end--;
	}
	len = (size_t)(trim_end - trim_start);
	if (len >= buf_sz) {
		len = buf_sz - 1;
	}
	memcpy (buf, trim_start, len);
	buf[len] = '\0';
	if (!buf[0]) {
		return type_name;
	}
	while (!strncmp (buf, "type.", 5)) {
		memmove (buf, buf + 5, strlen (buf + 5) + 1);
	}
	if (!strncmp (buf, "struct.", 7)) {
		memmove (buf + strlen ("struct "), buf + 7, strlen (buf + 7) + 1);
		memcpy (buf, "struct ", strlen ("struct "));
	} else if (!strncmp (buf, "union.", 6)) {
		memmove (buf + strlen ("union "), buf + 6, strlen (buf + 6) + 1);
		memcpy (buf, "union ", strlen ("union "));
	} else if (!strncmp (buf, "enum.", 5)) {
		memmove (buf + strlen ("enum "), buf + 5, strlen (buf + 5) + 1);
		memcpy (buf, "enum ", strlen ("enum "));
	}
	if (!strncmp (buf, "struct type.", 12)) {
		memmove (buf + strlen ("struct "), buf + 12, strlen (buf + 12) + 1);
		memcpy (buf, "struct ", strlen ("struct "));
	} else if (!strncmp (buf, "union type.", 11)) {
		memmove (buf + strlen ("union "), buf + 11, strlen (buf + 11) + 1);
		memcpy (buf, "union ", strlen ("union "));
	} else if (!strncmp (buf, "enum type.", 10)) {
		memmove (buf + strlen ("enum "), buf + 10, strlen (buf + 10) + 1);
		memcpy (buf, "enum ", strlen ("enum "));
	}
	star = strchr (buf, '*');
	if (star && star > buf && star[-1] != ' ') {
		size_t prefix = (size_t)(star - buf);
		if (prefix + 2 < buf_sz) {
			memmove (star + 1, star, strlen (star) + 1);
			star[0] = ' ';
		}
	}
	return buf;
}

static bool apply_struct_decl_candidate(RAnal *anal, RCore *core, const char *name, const char *decl) {
	bool imported;
	char *errmsg = NULL;
	ut64 memo_key;
	bool memo_result = false;

	if (!anal || !name || !*name || !decl || !*decl) {
		return false;
	}
	if (type_name_is_materialized (anal, name)) {
		return true;
	}
	memo_key = r_str_hash64 (name);
	memo_key ^= (r_str_hash64 (decl) << 1);
	if (struct_decl_memo_get (memo_key, &memo_result)) {
		return memo_result;
	}
	imported = r_anal_import_c_decls (anal, decl, &errmsg);
	free (errmsg);
	if (imported && type_name_is_materialized (anal, name)) {
		struct_decl_memo_put (memo_key, true);
		return true;
	}
	if (!core) {
		struct_decl_memo_put (memo_key, false);
		return false;
	}
	r_core_cmdf (core, "td %s", decl);
	imported = type_name_is_materialized (anal, name);
	struct_decl_memo_put (memo_key, imported);
	return imported;
}

static bool candidate_type_has_known_struct(RAnal *anal, const char *type_name) {
	const char *struct_kw;
	const char *name_start;
	char name_buf[192];
	char *normalized = NULL;
	size_t name_len;
	size_t i = 0;
	char canonical_type[192];
	const char *candidate_type;

	if (!anal || !type_name || !*type_name) {
		return false;
	}
	candidate_type = canonicalize_type_name_for_apply (type_name, canonical_type, sizeof (canonical_type));
	struct_kw = strstr (candidate_type, "struct ");
	if (!struct_kw) {
		struct_kw = strstr (candidate_type, "struct.");
	}
	if (!struct_kw) {
		normalized = normalize_compare_string (candidate_type);
		if (!normalized) {
			return false;
		}
		remove_substring_inplace (normalized, "const");
		remove_substring_inplace (normalized, "volatile");
		remove_substring_inplace (normalized, "restrict");
		remove_substring_inplace (normalized, "register");
		name_len = strlen (normalized);
		while (name_len > 0 && normalized[name_len - 1] == '*') {
			normalized[--name_len] = '\0';
		}
		if (!*normalized) {
			free (normalized);
			return false;
		}
		if (!strcmp (normalized, "void")
				|| !strcmp (normalized, "bool")
				|| !strcmp (normalized, "char")
				|| !strcmp (normalized, "signedchar")
				|| !strcmp (normalized, "unsignedchar")
				|| !strcmp (normalized, "short")
				|| !strcmp (normalized, "unsignedshort")
				|| !strcmp (normalized, "int")
				|| !strcmp (normalized, "unsigned")
				|| !strcmp (normalized, "unsignedint")
				|| !strcmp (normalized, "long")
				|| !strcmp (normalized, "unsignedlong")
				|| !strcmp (normalized, "longlong")
				|| !strcmp (normalized, "unsignedlonglong")
				|| !strcmp (normalized, "float")
				|| !strcmp (normalized, "double")
				|| !strcmp (normalized, "size_t")
				|| !strncmp (normalized, "int", 3)
				|| !strncmp (normalized, "uint", 4)) {
			free (normalized);
			return true;
		}
		if (name_len >= sizeof (name_buf)) {
			name_len = sizeof (name_buf) - 1;
		}
		memcpy (name_buf, normalized, name_len);
		name_buf[name_len] = '\0';
		free (normalized);
		return type_name_is_materialized (anal, name_buf);
	}
	name_start = struct_kw + strlen (!strncmp (struct_kw, "struct.", 7)? "struct.": "struct ");
	while (*name_start && isspace ((unsigned char)*name_start)) {
		name_start++;
	}
	if (!strncmp (name_start, "type.", 5)) {
		name_start += 5;
	}
	while (name_start[i] && i + 1 < sizeof (name_buf)) {
		char ch = name_start[i];
		if (!(isalnum ((unsigned char)ch) || ch == '_')) {
			break;
		}
		name_buf[i] = ch;
		i++;
	}
	name_buf[i] = '\0';
	if (!name_buf[0]) {
		return false;
	}
	return type_name_is_materialized (anal, name_buf);
}

static bool apply_var_type_candidate(
	RAnal *anal,
	RCore *core,
	RAnalFunction *fcn,
	RAnalVar *var,
	const char *candidate_name,
	const char *candidate_type,
	TypeWritebackCounters *counters
) {
	char *existing_type = NULL;
	bool api_ok = false;
	char canonical_type[192];
	const char *apply_type;

	if (!anal || !fcn || !var || !candidate_type || !*candidate_type) {
		return false;
	}
	(void)core;
	(void)candidate_name;
	apply_type = canonicalize_type_name_for_apply (candidate_type, canonical_type, sizeof (canonical_type));
	if (!apply_type || !*apply_type) {
		return false;
	}

	if (var->type && *var->type) {
		existing_type = strdup (var->type);
	}
	if (existing_type && !is_generic_type_name (existing_type) && is_generic_type_name (apply_type)) {
		if (counters) {
			counters->vars_skipped_conflict++;
		}
		free (existing_type);
		return false;
	}
	free (existing_type);

	if (!candidate_type_has_known_struct (anal, apply_type)) {
		if (counters) {
			counters->vars_skipped_conflict++;
		}
		return false;
	}

	r_anal_var_set_type (anal, var, apply_type);
	api_ok = verify_var_type_applied (var, apply_type);
	if (api_ok) {
		return true;
	}
	if (counters) {
		counters->vars_api_verify_fail++;
	}
	/* Keep API-only var type apply. The command fallback can emit noisy
	 * "unknown type ..." logs repeatedly on large analyses. */
	return false;
}

static bool apply_var_rename_candidate(
	RAnal *anal,
	RCore *core,
	RAnalFunction *fcn,
	RAnalVar *var,
	const char *old_name,
	const char *new_name
) {
	if (!anal || !fcn || !var || !old_name || !*old_name || !new_name || !*new_name) {
		return false;
	}
	if (!is_generated_var_name (var->name)) {
		return false;
	}
	if (r_anal_var_rename (anal, var, new_name) && verify_var_rename_applied (var, new_name)) {
		return true;
	}
	if (!core) {
		return false;
	}
	r_core_cmdf_at (core, fcn->addr, "afvn %s %s", old_name, new_name);
	var = r_anal_function_get_var_byname (fcn, new_name);
	return verify_var_rename_applied (var, new_name);
}

static bool apply_global_type_link_candidate(RAnal *anal, RCore *core, ut64 addr, const char *type_name, TypeWritebackCounters *tc) {
	char *existing = NULL;
	int rc;
	char canonical_type[192];
	const char *apply_type;
	if (!anal || !type_name || !*type_name || !addr) {
		return false;
	}
	(void)core;
	apply_type = canonicalize_type_name_for_apply (type_name, canonical_type, sizeof (canonical_type));
	if (!apply_type || !*apply_type) {
		return false;
	}
	if (is_opaque_placeholder_type_name (apply_type) || !candidate_type_has_known_struct (anal, apply_type)) {
		if (tc) {
			tc->global_links_conflict_skip++;
		}
		return false;
	}
	existing = r_type_link_at (anal->sdb_types, addr);
	if (existing && *existing && !strings_match_normalized (existing, apply_type)) {
		if (!is_generic_type_name (existing)) {
			if (tc) {
				tc->global_links_conflict_skip++;
				tc->global_links_existing_preserved++;
			}
			free (existing);
			return false;
		}
	}
	free (existing);
	rc = r_type_set_link (anal->sdb_types, apply_type, addr);
	if (rc > 0) {
		return true;
	}
	rc = r_type_link_offset (anal->sdb_types, apply_type, addr);
	if (rc > 0) {
		return true;
	}
	/* Keep API-only type links. Command fallback (`tl`) floods logs with
	 * per-address unknown-type errors when a type cannot be resolved. */
	return false;
}

static ut64 compute_type_cache_key(
	RAnalFunction *fcn,
	const char *external_context_json,
	ut64 dep_hash,
	SleighTypeWritebackMode mode,
	int min_conf,
	int rename_min_conf,
	int struct_min_conf,
	int max_iters
) {
	ut64 key = 0;
	int bb_count = (fcn && fcn->bbs)? r_list_length (fcn->bbs): 0;
	int linear_size = fcn? r_anal_function_linear_size (fcn): 0;
	key ^= fcn? fcn->addr: 0;
	key ^= ((ut64)bb_count << 32);
	key ^= (ut64)linear_size;
	key ^= ((ut64)mode << 56);
	key ^= ((ut64)(min_conf & 0xff) << 8);
	key ^= ((ut64)(rename_min_conf & 0xff) << 16);
	key ^= ((ut64)(struct_min_conf & 0xff) << 24);
	key ^= ((ut64)(max_iters & 0xffff) << 40);
	key ^= dep_hash;
	key ^= r_str_hash64 (external_context_json? external_context_json: "");
	return key;
}

static bool refs_have_caller_propagation_refs(RVecAnalRef *refs) {
	size_t i;
	size_t len;
	if (!refs) {
		return false;
	}
	len = RVecAnalRef_length (refs);
	for (i = 0; i < len; i++) {
		RAnalRef *ref = RVecAnalRef_at (refs, i);
		if (ref && is_caller_propagation_ref_type (ref->type)) {
			return true;
		}
	}
	return false;
}

static RVecAnalRef *get_function_call_refs(RCore *core, RAnal *anal, RAnalFunction *fcn) {
	RVecAnalRef *refs = NULL;
	if (anal && fcn) {
		refs = r_anal_function_get_refs (fcn);
		if (refs_have_caller_propagation_refs (refs)) {
			return refs;
		}
		RVecAnalRef_free (refs);
	}
	if (core && fcn) {
		refs = r_core_anal_fcn_get_calls (core, fcn);
		if (refs_have_caller_propagation_refs (refs)) {
			return refs;
		}
		RVecAnalRef_free (refs);
	}
	return NULL;
}

static ut64 compute_callee_dependency_hash(RCore *core, RAnal *anal, RAnalFunction *fcn) {
	RVecAnalRef *refs;
	ut64 dep_hash = 0;
	size_t i;
	size_t len;

	if (!anal || !fcn) {
		return 0;
	}
	/* First pass: no cached applications yet, so dependency hash cannot change. */
	if (type_writeback_cache_count == 0) {
		return 0;
	}
	refs = get_function_call_refs (core, anal, fcn);
	if (!refs) {
		return 0;
	}
	len = RVecAnalRef_length (refs);
	for (i = 0; i < len; i++) {
		RAnalRef *ref = RVecAnalRef_at (refs, i);
		RAnalFunction *callee_fcn;
		TypeWritebackCacheEntry *entry;
		if (!ref || !is_caller_propagation_ref_type (ref->type)) {
			continue;
		}
		callee_fcn = r_anal_get_fcn_in (anal, ref->addr, 0);
		if (!callee_fcn) {
			continue;
		}
		entry = type_writeback_cache_get (callee_fcn->addr);
		if (entry) {
			dep_hash ^= entry->payload_hash;
		}
	}
	RVecAnalRef_free (refs);
	return dep_hash;
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

static ut64 *collect_type_interproc_direct_targets_from_blocks(
	R2ILContext *ctx,
	const BlockArray *blocks,
	ut64 fcn_addr,
	const char *fcn_name,
	size_t *out_count
) {
	char *targets_json = NULL;
	RJson *root = NULL;
	RJson *item;
	ut64 *targets = NULL;
	size_t count = 0;
	size_t cap = 0;

	if (out_count) {
		*out_count = 0;
	}
	if (!ctx || !blocks || !blocks->blocks || blocks->count == 0) {
		return NULL;
	}
	targets_json = r2sleigh_get_direct_call_targets_json (ctx,
		(const R2ILBlock **)blocks->blocks, blocks->count, fcn_addr, fcn_name);
	if (!targets_json || !*targets_json) {
		r2il_string_free (targets_json);
		return NULL;
	}
	root = r_json_parse (targets_json);
	if (!root || root->type != R_JSON_ARRAY) {
		r_json_free (root);
		r2il_string_free (targets_json);
		return NULL;
	}
	for (item = root->children.first; item; item = item->next) {
		if (!item || item->type != R_JSON_INTEGER) {
			continue;
		}
		append_unique_ut64 (&targets, &count, &cap, item->num.u_value);
	}
	r_json_free (root);
	r2il_string_free (targets_json);
	if (out_count) {
		*out_count = count;
	}
	return targets;
}

static char *build_type_interproc_scope_json_from_targets(
	RCore *core,
	RAnal *anal,
	const ut64 *targets,
	size_t target_count
) {
	PJ *pj;
	ut64 *seen_addrs = NULL;
	size_t seen_count = 0;
	size_t seen_cap = 0;
	size_t i;
	char *out;

	if (!anal || !targets || target_count == 0) {
		return strdup ("{}");
	}
	pj = pj_new ();
	if (!pj) {
		return strdup ("{}");
	}

	pj_o (pj);
	pj_ks (pj, "phase", "fixpoint");
	pj_k (pj, "payloads");
	pj_a (pj);
	for (i = 0; i < target_count; i++) {
		RAnalFunction *callee_fcn;
		TypeWritebackCacheEntry *entry;
		ut64 target = targets[i];
		if (!target) {
			continue;
		}
		callee_fcn = r_anal_get_fcn_in (anal, target, 0);
		if (!callee_fcn || !append_unique_ut64 (&seen_addrs, &seen_count, &seen_cap, callee_fcn->addr)) {
			continue;
		}
		entry = type_writeback_cache_get (callee_fcn->addr);
		if (entry && entry->payload_json && *entry->payload_json) {
			pj_j (pj, entry->payload_json);
		}
	}
	pj_end (pj);

	free (seen_addrs);
	seen_addrs = NULL;
	seen_count = 0;
	seen_cap = 0;

	pj_k (pj, "seeds");
	pj_a (pj);
	for (i = 0; i < target_count; i++) {
		ut64 seed_addr = targets[i];
		char *seed_name;
		if (!seed_addr || !append_unique_ut64 (&seen_addrs, &seen_count, &seen_cap, seed_addr)) {
			continue;
		}
		seed_name = resolve_interproc_seed_name (core, anal, seed_addr);
		if (!seed_name || !*seed_name) {
			free (seed_name);
			continue;
		}
		pj_o (pj);
		pj_kn (pj, "id", seed_addr);
		pj_ks (pj, "name", seed_name);
		pj_end (pj);
		free (seed_name);
	}
	pj_end (pj);
	pj_end (pj);

	out = strdup (pj_string (pj));
	pj_free (pj);
	free (seen_addrs);
	return out? out: strdup ("{}");
}

static bool warm_type_payload_cache_for_function(
	RCore *core,
	RAnal *anal,
	R2ILContext *ctx,
	RAnalFunction *fcn,
	int max_iters,
	ut64 **seen_addrs,
	size_t *seen_count,
	size_t *seen_cap
) {
	ut64 *direct_targets = NULL;
	size_t direct_target_count = 0;
	size_t i;
	BlockArray blocks;
	char *external_context_json = NULL;
	char *interproc_scope_json = NULL;
	char *payload_json = NULL;
	ut64 payload_hash = 0;
	bool ok = false;
	TypeWritebackCacheEntry *entry;

	if (!core || !anal || !ctx || !fcn) {
		return false;
	}
	if (!append_unique_ut64 (seen_addrs, seen_count, seen_cap, fcn->addr)) {
		return true;
	}
	entry = type_writeback_cache_get (fcn->addr);
	if (entry && entry->payload_json && *entry->payload_json) {
		return true;
	}
	if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
		return false;
	}

	direct_targets = collect_type_interproc_direct_targets_from_blocks (
		ctx, &blocks, fcn->addr, fcn->name, &direct_target_count);
	for (i = 0; i < direct_target_count; i++) {
		RAnalFunction *callee_fcn = r_anal_get_fcn_in (anal, direct_targets[i], 0);
		if (!callee_fcn || callee_fcn->addr == fcn->addr) {
			continue;
		}
		warm_type_payload_cache_for_function (core, anal, ctx, callee_fcn, max_iters,
			seen_addrs, seen_count, seen_cap);
	}
	external_context_json = sleigh_collect_external_context_json (anal, fcn);
	if (!external_context_json || (external_context_json[0] != '{' && external_context_json[0] != '[')) {
		free (external_context_json);
		external_context_json = strdup ("{}");
	}
	interproc_scope_json = build_type_interproc_scope_json_from_targets (
		core, anal, direct_targets, direct_target_count);
	payload_json = r2sleigh_infer_type_writeback_json_ex (ctx,
		(const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr, fcn->name,
		external_context_json? external_context_json: "{}",
		1, max_iters, 1, interproc_scope_json? interproc_scope_json: "{}");
	if (payload_json && *payload_json) {
		payload_hash = r_str_hash64 (payload_json);
		ok = type_writeback_cache_put (fcn->addr, 0, 0, payload_hash, 0, payload_json);
	}

	r2il_string_free (payload_json);
	free (interproc_scope_json);
	free (external_context_json);
	free (direct_targets);
	block_array_free (&blocks);
	return ok;
}

static char *build_type_interproc_scope_json(
	RCore *core,
	RAnal *anal,
	R2ILContext *ctx,
	RAnalFunction *fcn,
	const BlockArray *blocks
) {
	ut64 *direct_targets = NULL;
	size_t direct_target_count = 0;
	char *scope_json;

	if (!anal || !ctx || !fcn || !blocks) {
		return strdup ("{}");
	}
	direct_targets = collect_type_interproc_direct_targets_from_blocks (
		ctx, blocks, fcn->addr, fcn->name, &direct_target_count);
	scope_json = build_type_interproc_scope_json_from_targets (
		core, anal, direct_targets, direct_target_count);
	free (direct_targets);
	return scope_json;
}

static int ut64_cmp_asc(const void *a, const void *b) {
	ut64 av = *(const ut64 *)a;
	ut64 bv = *(const ut64 *)b;
	if (av < bv) {
		return -1;
	}
	if (av > bv) {
		return 1;
	}
	return 0;
}

static bool queue_addr_if_eligible(
	ut64 addr,
	const ut64 *eligible_addrs,
	size_t eligible_count,
	ut64 **queue,
	size_t *queue_count,
	size_t *queue_cap,
	bool *is_new
) {
	bool already;
	if (is_new) {
		*is_new = false;
	}
	if (!addr || !ut64_sorted_contains (eligible_addrs, eligible_count, addr)) {
		return false;
	}
	already = ut64_array_contains (*queue, *queue_count, addr);
	if (!append_unique_ut64 (queue, queue_count, queue_cap, addr)) {
		return false;
	}
	if (!already && is_new) {
		*is_new = true;
	}
	return true;
}

static void enqueue_fixpoint_neighbors(
	RAnal *anal,
	RAnalFunction *fcn,
	const ut64 *eligible_addrs,
	size_t eligible_count,
	ut64 **queue,
	size_t *queue_count,
	size_t *queue_cap,
	TypeWritebackCounters *tc,
	bool requeue_phase
) {
	RVecAnalRef *xrefs;
	RVecAnalRef *refs;
	size_t i;
	size_t len;
	bool inserted;

	if (!anal || !fcn || !eligible_addrs || !queue || !queue_count || !queue_cap) {
		return;
	}

	xrefs = r_anal_xrefs_get (anal, fcn->addr);
	if (xrefs) {
		len = RVecAnalRef_length (xrefs);
		for (i = 0; i < len; i++) {
			RAnalRef *ref = RVecAnalRef_at (xrefs, i);
			RAnalFunction *caller_fcn;
			if (!ref || !ref->at || !is_caller_propagation_ref_type (ref->type)) {
				continue;
			}
			caller_fcn = r_anal_get_fcn_in (anal, ref->at, 0);
			if (!caller_fcn) {
				continue;
			}
			inserted = false;
			queue_addr_if_eligible (caller_fcn->addr, eligible_addrs, eligible_count, queue, queue_count, queue_cap, &inserted);
			if (inserted && tc) {
				tc->fixpoint_queue_pushes++;
				if (requeue_phase) {
					tc->fixpoint_requeues++;
				}
			}
		}
		RVecAnalRef_free (xrefs);
	}

	refs = get_function_call_refs (NULL, anal, fcn);
	if (refs) {
		len = RVecAnalRef_length (refs);
		for (i = 0; i < len; i++) {
			RAnalRef *ref = RVecAnalRef_at (refs, i);
			RAnalFunction *callee_fcn;
			if (!ref || !is_caller_propagation_ref_type (ref->type)) {
				continue;
			}
			callee_fcn = r_anal_get_fcn_in (anal, ref->addr, 0);
			if (!callee_fcn) {
				continue;
			}
			inserted = false;
			queue_addr_if_eligible (callee_fcn->addr, eligible_addrs, eligible_count, queue, queue_count, queue_cap, &inserted);
			if (inserted && tc) {
				tc->fixpoint_queue_pushes++;
				if (requeue_phase) {
					tc->fixpoint_requeues++;
				}
			}
		}
		RVecAnalRef_free (refs);
	}
}

static bool is_caller_propagation_ref_type (RAnalRefType type) {
	RAnalRefType masked = R_ANAL_REF_TYPE_MASK (type);
	return masked == R_ANAL_REF_TYPE_CALL
		|| masked == R_ANAL_REF_TYPE_CODE
		|| masked == R_ANAL_REF_TYPE_JUMP;
}

static inline bool string_has_opaque_type_marker(const char *type) {
	return type && strstr (type, "type_0x");
}

static bool function_has_opaque_type_markers(RAnalFunction *fcn) {
	RAnalFunctionSignature *signature;
	RListIter *iter;
	RAnalFunctionParam *param;
	if (!fcn) {
		return false;
	}
	signature = r_anal_function_get_signature (fcn);
	if (!signature) {
		return false;
	}
	if (string_has_opaque_type_marker (signature->ret_type)) {
		r_anal_function_signature_free (signature);
		return true;
	}
	if (signature->params) {
		r_list_foreach (signature->params, iter, param) {
			if (param && string_has_opaque_type_marker (param->type)) {
				r_anal_function_signature_free (signature);
				return true;
			}
		}
	}
	r_anal_function_signature_free (signature);
	return false;
}

static bool run_caller_type_match (RAnal *anal, RCore *core, RAnalFunction *caller_fcn) {
	if (!anal || !caller_fcn || !core) {
		return false;
	}
	/* Avoid flooding logs with "unknown type struct type_0x..." from opaque DB placeholders. */
	if (function_has_opaque_type_markers (caller_fcn)) {
		return true;
	}
	r_anal_type_match (anal, caller_fcn);
	return true;
}

static bool run_caller_afva (RCore *core, RAnalFunction *caller_fcn) {
	if (!core || !caller_fcn) {
		return false;
	}
	r_core_recover_vars (core, caller_fcn, false);
	return true;
}

static void caller_propagation_record_sample(
	CallerPropagationState *state,
	const char *callee_name,
	bool prioritize
) {
	size_t i;
	size_t last;
	char *dup;

	if (!state || !callee_name || !*callee_name) {
		return;
	}
	for (i = 0; i < state->sample_callees_count; i++) {
		if (!strcmp (state->sample_callees[i], callee_name)) {
			return;
		}
	}
	if (state->sample_callees_count < SLEIGH_CALLER_PROP_SAMPLE_MAX) {
		append_unique_string (&state->sample_callees, &state->sample_callees_count,
			&state->sample_callees_capacity, callee_name);
		return;
	}
	if (!prioritize || state->sample_callees_count == 0) {
		return;
	}
	dup = strdup (callee_name);
	if (!dup) {
		return;
	}
	last = state->sample_callees_count - 1;
	free (state->sample_callees[last]);
	state->sample_callees[last] = dup;
}

static void propagate_signature_to_direct_callers(
	RAnal *anal,
	RCore *core,
	ut64 callee_addr,
	const char *callee_name,
	CallerPropagationState *state,
	bool prioritize_sample
) {
	RVecAnalRef *refs;
	ut64 *callee_callers = NULL;
	size_t callee_callers_count = 0;
	size_t callee_callers_capacity = 0;
	size_t i;
	size_t len;

	if (!anal || !core || !state || !callee_addr) {
		return;
	}
	refs = r_anal_xrefs_get (anal, callee_addr);
	if (!refs) {
		return;
	}

	state->prop_callees_triggered++;
	caller_propagation_record_sample (state, callee_name, prioritize_sample);

	len = RVecAnalRef_length (refs);
	for (i = 0; i < len; i++) {
		RAnalRef *ref = RVecAnalRef_at (refs, i);
		if (callee_callers_count >= SLEIGH_CALLER_PROP_MAX_PER_CALLEE) {
			break;
		}
		if (!ref || !ref->at || !is_caller_propagation_ref_type (ref->type)) {
			continue;
		}
		append_unique_ut64 (&callee_callers, &callee_callers_count, &callee_callers_capacity, ref->at);
	}

	for (i = 0; i < callee_callers_count; i++) {
		ut64 caller_site = callee_callers[i];
		RAnalFunction *caller_fcn;
		ut64 caller_addr;

		if (state->updated_callers_count >= SLEIGH_CALLER_PROP_MAX_TOTAL) {
			break;
		}

		state->prop_callers_considered++;
		caller_fcn = r_anal_get_fcn_in (anal, caller_site, 0);
		if (!caller_fcn) {
			state->prop_callers_missing_fcn++;
			continue;
		}
		caller_addr = caller_fcn->addr;
		if (ut64_array_contains (state->updated_callers, state->updated_callers_count, caller_addr)) {
			state->prop_callers_dedup_skipped++;
			continue;
		}
		if (!append_unique_ut64 (&state->updated_callers, &state->updated_callers_count,
				&state->updated_callers_capacity, caller_addr)) {
			continue;
		}
		if (!run_caller_type_match (anal, core, caller_fcn)) {
			state->prop_type_match_failures++;
		}
		if (!run_caller_afva (core, caller_fcn)) {
			state->prop_afva_failures++;
		}
		state->prop_callers_updated++;
	}

	free (callee_callers);
}

static char *format_sample_callees(char **sample_callees, size_t sample_count) {
	RStrBuf sb;
	char *out;
	size_t i;

	if (!sample_callees || sample_count == 0) {
		return strdup ("-");
	}
	r_strbuf_init (&sb);
	for (i = 0; i < sample_count; i++) {
		if (i > 0) {
			r_strbuf_append (&sb, ",");
		}
		r_strbuf_append (&sb, sample_callees[i]);
	}
	out = strdup (R_STRBUF_SAFEGET (&sb));
	r_strbuf_fini (&sb);
	return out ? out : strdup ("-");
}

static int json_array_object_count(const RJson *array_root) {
	const RJson *obj;
	int count = 0;

	if (!array_root || array_root->type != R_JSON_ARRAY) {
		return 0;
	}
	obj = json_next_object (array_root->children.first);
	while (obj) {
		count++;
		obj = json_next_object (obj->next);
	}
	return count;
}

static bool verify_practical_signature_consistency (
	RAnal *anal,
	RAnalFunction *fcn,
	const RJson *sig_root,
	bool check_signature,
	bool check_callconv,
	bool *afij_signature_drift,
	ConsistencyReasonCounters *reason_counters
) {
	bool ok = true;
	bool reason_readback_fail = false;
	bool reason_ret_mismatch = false;
	bool reason_argc_mismatch = false;
	bool reason_argtype_mismatch = false;
	bool reason_callconv_mismatch = false;
	const RJson *j_expected_signature;
	const RJson *j_expected_ret;
	const RJson *j_expected_params;
	const RJson *j_expected_callconv;
	const RJson *j_expected_arch;
	RAnalFunctionSignature *current_signature = NULL;
	bool long_is_i64 = false;

	if (afij_signature_drift) {
		*afij_signature_drift = false;
	}
	if (!anal || !fcn || !sig_root || sig_root->type != R_JSON_OBJECT) {
		if (reason_counters) {
			reason_counters->readback_fail++;
		}
		return false;
	}

	j_expected_signature = r_json_get (sig_root, "signature");
	j_expected_ret = r_json_get (sig_root, "ret_type");
	j_expected_params = r_json_get (sig_root, "params");
	j_expected_callconv = r_json_get (sig_root, "callconv");
	j_expected_arch = r_json_get (sig_root, "arch");
	if (j_expected_arch && j_expected_arch->type == R_JSON_STRING && j_expected_arch->str_value) {
		long_is_i64 = is_x64_signature_arch (j_expected_arch->str_value);
	}
	if ((check_signature || check_callconv) && ok) {
		current_signature = r_anal_function_get_signature (fcn);
		if (!current_signature) {
			reason_readback_fail = true;
			ok = false;
		}
	}
	if (check_signature) {
		const RJson *expected_param;
		int expected_count;
		int actual_count = 0;
		RListIter *iter;
		RAnalFunctionParam *actual_param;

		if (ok) {
			if (!j_expected_ret || j_expected_ret->type != R_JSON_STRING
					|| !current_signature
					|| R_STR_ISEMPTY (current_signature->ret_type)) {
				reason_readback_fail = true;
				ok = false;
			} else if (!types_match_canonical (j_expected_ret->str_value, current_signature->ret_type, long_is_i64)) {
				reason_ret_mismatch = true;
				ok = false;
			}

			if (!j_expected_params || j_expected_params->type != R_JSON_ARRAY) {
				reason_readback_fail = true;
				ok = false;
			} else {
				expected_count = json_array_object_count (j_expected_params);
				actual_count = current_signature && current_signature->params
					? (int)r_list_length (current_signature->params)
					: 0;
				if (expected_count != actual_count) {
					reason_argc_mismatch = true;
					ok = false;
				}
				expected_param = json_next_object (j_expected_params->children.first);
				iter = (current_signature && current_signature->params)
					? current_signature->params->head
					: NULL;
				actual_param = iter? iter->data: NULL;
				while (expected_param && actual_param && ok) {
					const RJson *j_expected_type = r_json_get (expected_param, "type");

					if (!j_expected_type || j_expected_type->type != R_JSON_STRING
							|| R_STR_ISEMPTY (actual_param->type)) {
						reason_readback_fail = true;
						ok = false;
						break;
					}
					if (!types_match_canonical (j_expected_type->str_value, actual_param->type, long_is_i64)) {
						reason_argtype_mismatch = true;
						ok = false;
						break;
					}
					expected_param = json_next_object (expected_param->next);
					iter = iter? iter->n: NULL;
					actual_param = iter? iter->data: NULL;
				}
				if ((expected_param || actual_param) && ok) {
					reason_argc_mismatch = true;
					ok = false;
				}
			}
		}
	}

	if (check_callconv) {
		if (ok && j_expected_callconv && j_expected_callconv->type == R_JSON_STRING
				&& j_expected_callconv->str_value && *j_expected_callconv->str_value) {
			if (!current_signature
					|| R_STR_ISEMPTY (current_signature->callconv)
					|| !strings_match_normalized (j_expected_callconv->str_value, current_signature->callconv)) {
				reason_callconv_mismatch = true;
				ok = false;
			}
		}
	}

	if (check_signature && afij_signature_drift) {
		if (!j_expected_signature || j_expected_signature->type != R_JSON_STRING
				|| !j_expected_signature->str_value || !*j_expected_signature->str_value) {
			*afij_signature_drift = false;
		} else if (!current_signature || R_STR_ISEMPTY (current_signature->signature)) {
			*afij_signature_drift = true;
		} else if (!strings_match_normalized (j_expected_signature->str_value, current_signature->signature)) {
			*afij_signature_drift = true;
		}
	}

	if (reason_counters) {
		if (reason_readback_fail) {
			reason_counters->readback_fail++;
		}
		if (reason_ret_mismatch) {
			reason_counters->ret_mismatch++;
		}
		if (reason_argc_mismatch) {
			reason_counters->argc_mismatch++;
		}
		if (reason_argtype_mismatch) {
			reason_counters->argtype_mismatch++;
		}
		if (reason_callconv_mismatch) {
			reason_counters->callconv_mismatch++;
		}
	}
	r_anal_function_signature_free (current_signature);
	return ok;
}

static bool apply_type_writeback_payload(
	RAnal *anal,
	RCore *core,
	RAnalFunction *fcn,
	const RJson *payload_root,
	SleighTypeWritebackMode wb_mode,
	int min_conf,
	int rename_min_conf,
	int struct_min_conf,
	int global_max_links,
	TypeWritebackCounters *tc
) {
	const RJson *j_structs;
	const RJson *j_vars;
	const RJson *j_renames;
	const RJson *j_links;
	const RJson *item;
	bool changed = false;
	int global_applied_this_payload = 0;
	int type_apply_threshold = confidence_threshold_for_mode (min_conf, wb_mode, 10);
	int rename_apply_threshold = confidence_threshold_for_mode (rename_min_conf, wb_mode, 8);
	int struct_apply_threshold = confidence_threshold_for_mode (struct_min_conf, wb_mode, 10);

	if (!anal || !fcn || !payload_root || payload_root->type != R_JSON_OBJECT) {
		return false;
	}
	if (wb_mode == SLEIGH_TYPE_WRITEBACK_OFF) {
		return false;
	}

	j_structs = r_json_get (payload_root, "struct_decls");
	if (j_structs && j_structs->type == R_JSON_ARRAY) {
		for (item = json_next_object (j_structs->children.first); item; item = json_next_object (item->next)) {
			const RJson *j_name = r_json_get (item, "name");
			const RJson *j_decl = r_json_get (item, "decl");
			const RJson *j_conf = r_json_get (item, "confidence");
			int confidence = j_conf && j_conf->type == R_JSON_INTEGER? (int)j_conf->num.u_value: 0;
			if (tc) {
				tc->structs_considered++;
			}
			if (!json_is_string_with_value (j_name) || !json_is_string_with_value (j_decl)) {
				continue;
			}
			if (confidence < struct_apply_threshold) {
				if (tc) {
					tc->structs_skipped_low_conf++;
				}
				continue;
			}
			if (apply_struct_decl_candidate (anal, core, j_name->str_value, j_decl->str_value)) {
				if (tc) {
					tc->structs_imported++;
				}
				changed = true;
			} else if (tc) {
				tc->structs_import_fail++;
			}
		}
	}

	j_vars = r_json_get (payload_root, "var_type_candidates");
	if (j_vars && j_vars->type == R_JSON_ARRAY) {
		for (item = json_next_object (j_vars->children.first); item; item = json_next_object (item->next)) {
			const RJson *j_name = r_json_get (item, "name");
			const RJson *j_kind = r_json_get (item, "kind");
			const RJson *j_delta = r_json_get (item, "delta");
			const RJson *j_type = r_json_get (item, "type");
			const RJson *j_reg = r_json_get (item, "reg");
			const RJson *j_conf = r_json_get (item, "confidence");
			const RJson *j_isarg = r_json_get (item, "isarg");
			const RJson *j_size = r_json_get (item, "size");
			int confidence = j_conf && j_conf->type == R_JSON_INTEGER? (int)j_conf->num.u_value: 0;
			int delta = j_delta && j_delta->type == R_JSON_INTEGER? (int)j_delta->num.s_value: 0;
			int size = j_size && j_size->type == R_JSON_INTEGER? (int)j_size->num.u_value: 0;
			bool isarg = j_isarg && j_isarg->type == R_JSON_BOOLEAN && j_isarg->num.u_value;
			char kind = (j_kind && j_kind->type == R_JSON_STRING && j_kind->str_value && *j_kind->str_value)
				? j_kind->str_value[0]
				: R_ANAL_VAR_KIND_SPV;
			const char *reg_name = json_is_string_with_value (j_reg)? j_reg->str_value: NULL;
			const char *candidate_name = json_is_string_with_value (j_name)? j_name->str_value: NULL;
			const char *candidate_type = json_is_string_with_value (j_type)? j_type->str_value: NULL;
			char canonical_candidate_type[192];
			const char *apply_type = NULL;
			RAnalVar *var;

			if (tc) {
				tc->vars_considered++;
			}
			if (!candidate_name || !candidate_type || !*candidate_name || !*candidate_type) {
				continue;
			}
			apply_type = canonicalize_type_name_for_apply (candidate_type, canonical_candidate_type, sizeof (canonical_candidate_type));
			if (!apply_type || !*apply_type || !candidate_type_has_known_struct (anal, apply_type)) {
				if (tc) {
					tc->vars_skipped_conflict++;
				}
				continue;
			}
			if (confidence < type_apply_threshold) {
				if (tc) {
					if (confidence + 10 >= type_apply_threshold) {
						tc->vars_hint_only++;
					} else {
						tc->vars_skipped_low_conf++;
					}
				}
				continue;
			}

			if (kind == R_ANAL_VAR_KIND_REG && reg_name && *reg_name) {
				int reg_index = resolve_reg_index (anal, reg_name);
				if (reg_index >= 0) {
					delta = reg_index;
				}
			}
			var = lookup_var_for_candidate (anal, fcn, candidate_name, kind, delta, reg_name);
			if (!var && confidence >= 95) {
				var = r_anal_function_set_var (fcn, delta, kind, apply_type,
					size > 0? size: 4, isarg, candidate_name);
			}
			if (!var) {
				if (tc) {
					tc->vars_skipped_conflict++;
				}
				continue;
			}
			if (apply_var_type_candidate (anal, core, fcn, var, candidate_name, candidate_type, tc)) {
				if (tc) {
					tc->vars_applied++;
				}
				changed = true;
			}
		}
	}

	j_renames = r_json_get (payload_root, "var_rename_candidates");
	if (j_renames && j_renames->type == R_JSON_ARRAY) {
		for (item = json_next_object (j_renames->children.first); item; item = json_next_object (item->next)) {
			const RJson *j_name = r_json_get (item, "name");
			const RJson *j_target = r_json_get (item, "target_name");
			const RJson *j_conf = r_json_get (item, "confidence");
			const char *old_name = json_is_string_with_value (j_name)? j_name->str_value: NULL;
			const char *new_name = json_is_string_with_value (j_target)? j_target->str_value: NULL;
			int confidence = j_conf && j_conf->type == R_JSON_INTEGER? (int)j_conf->num.u_value: 0;
			RAnalVar *var;

			if (tc) {
				tc->renames_considered++;
			}
			if (!old_name || !new_name || !*old_name || !*new_name) {
				continue;
			}
			if (confidence < rename_apply_threshold) {
				if (tc) {
					tc->renames_skipped_low_conf++;
				}
				continue;
			}
			var = r_anal_function_get_var_byname (fcn, old_name);
			if (!var) {
				if (tc) {
					tc->renames_skipped_conflict++;
				}
				continue;
			}
			if (!is_generated_var_name (var->name)) {
				if (tc) {
					tc->rename_generated_guard_skips++;
					tc->renames_skipped_conflict++;
				}
				continue;
			}
			if (apply_var_rename_candidate (anal, core, fcn, var, old_name, new_name)) {
				if (tc) {
					tc->renames_applied++;
				}
				changed = true;
			} else if (tc) {
				tc->renames_skipped_conflict++;
			}
		}
	}

	j_links = r_json_get (payload_root, "global_type_links");
	if (j_links && j_links->type == R_JSON_ARRAY) {
		ut64 *seen_addrs = NULL;
		size_t seen_count = 0;
		size_t seen_cap = 0;
		for (item = json_next_object (j_links->children.first); item; item = json_next_object (item->next)) {
			const RJson *j_addr = r_json_get (item, "addr");
			const RJson *j_type = r_json_get (item, "type");
			const RJson *j_conf = r_json_get (item, "confidence");
			ut64 addr = j_addr && j_addr->type == R_JSON_INTEGER? (ut64)j_addr->num.u_value: 0;
			int confidence = j_conf && j_conf->type == R_JSON_INTEGER? (int)j_conf->num.u_value: 0;
			if (tc) {
				tc->global_links_considered++;
			}
			if (!addr || !json_is_string_with_value (j_type)) {
				continue;
			}
			if (ut64_array_contains (seen_addrs, seen_count, addr)) {
				continue;
			}
			if (confidence < type_apply_threshold) {
				if (tc) {
					tc->global_links_skipped_low_conf++;
				}
				continue;
			}
			if (global_applied_this_payload >= global_max_links) {
				if (tc) {
					tc->global_links_skipped_low_conf++;
				}
				continue;
			}
			if (is_opaque_placeholder_type_name (j_type->str_value)
					|| !candidate_type_has_known_struct (anal, j_type->str_value)) {
				if (tc) {
					tc->global_links_conflict_skip++;
				}
				continue;
			}
			append_unique_ut64 (&seen_addrs, &seen_count, &seen_cap, addr);
			if (apply_global_type_link_candidate (anal, core, addr, j_type->str_value, tc)) {
				if (tc) {
					tc->global_links_applied++;
				}
				global_applied_this_payload++;
				changed = true;
			} else if (tc) {
				tc->global_links_fail++;
			}
		}
		free (seen_addrs);
	}

	return changed;
}

/* Eligibility/priority callback: score > 0 = eligible with priority, < 0 = ineligible */
static int sleigh_eligible(RAnal *anal) {
	R2ILContext *ctx = get_context (anal);
	return ctx ? 10 : -1;
}

/* Called at end of aaaa for global post-analysis passes */
static bool sleigh_post_analysis(RAnal *anal) {
	R2ILContext *ctx = get_context (anal);
	RCore *core;
	int xrefs_added = 0;
	int xref_cache_hits = 0;
	int xref_recomputes = 0;
	int xref_dirty_queued = 0;
	int taint_comments = 0;
	int taint_flags = 0;
	int taint_xrefs = 0;
	int taint_parse_failures = 0;
	int taint_fcns_eligible = 0;
	int taint_fcns_skipped = 0;
	int taint_sink_hits = 0;
	int taint_risk_critical = 0;
	int taint_risk_high = 0;
	int taint_risk_medium = 0;
	int taint_risk_low = 0;
	int sig_fcns_considered = 0;
	int sig_fcns_skipped_arch = 0;
	int sig_fcns_skipped_size = 0;
	int sig_parse_failures = 0;
	int sig_cmd_failures = 0;
	int sig_skipped_low_conf = 0;
	int cc_skipped_arch = 0;
	int cc_skipped_low_conf = 0;
	int cc_missing_payload = 0;
	int sig_signatures_updated = 0;
	int sig_cc_updated = 0;
	int sig_api_apply_ok = 0;
	int sig_api_verify_fail = 0;
	int sig_cmd_fallback_attempted = 0;
	int sig_cmd_apply_ok = 0;
	int sig_cmd_apply_fail = 0;
	int cc_api_apply_ok = 0;
	int cc_api_verify_fail = 0;
	int cc_cmd_fallback_attempted = 0;
	int cc_cmd_apply_ok = 0;
	int cc_cmd_apply_fail = 0;
	int consistency_verified = 0;
	int consistency_ok = 0;
	int consistency_mismatch = 0;
	int afij_signature_drift = 0;
	ConsistencyReasonCounters consistency_reasons = {0};
	TypeWritebackCounters type_wb = {0};
	CallerPropagationState prop_state;
	size_t semantic_comments_total = 0;
	int best_sink_rank = 1000;
	ut64 best_sink_addr = 0;
	ut64 focus_callee_addr = 0;
	char *best_sink_label = NULL;
	char *sample_callees = NULL;
	const char *arch_name = NULL;
	bool sig_arch_supported = false;
	bool cc_arch_supported = false;
	bool type_arch_supported = false;
	SleighMode post_mode = sleigh_mode_effective_for_post_analysis (anal);
	SleighTypeWritebackMode type_wb_mode = cfg_get_type_writeback_mode_default_balanced (anal);
	int type_min_conf = cfg_get_type_min_conf (anal);
	int type_rename_min_conf = cfg_get_type_rename_min_conf (anal);
	int type_struct_min_conf = cfg_get_type_struct_min_conf (anal);
	int type_max_iters = cfg_get_type_interproc_max_iters (anal);
	int type_max_blocks = cfg_get_type_max_blocks (anal);
	int type_global_max_links = cfg_get_type_global_max_links (anal);
	bool type_cache_enabled = cfg_get_type_cache_enabled (anal);
	bool semantic_comments_enabled = false;
	bool taint_enabled = post_mode != SLEIGH_MODE_FAST;
	bool sigwrite_enabled = post_mode != SLEIGH_MODE_FAST;
	bool type_writeback_enabled = sigwrite_enabled && type_wb_mode != SLEIGH_TYPE_WRITEBACK_OFF;
	bool sigverify_enabled = false;
	ut64 *type_eligible_addrs = NULL;
	size_t type_eligible_count = 0;
	size_t type_eligible_cap = 0;
	ut64 *changed_type_fcns = NULL;
	size_t changed_type_count = 0;
	size_t changed_type_cap = 0;

	struct_decl_memo_clear ();
	if (!ctx) {
		return false;
	}
	core = anal->coreb.core;
	arch_name = r2il_arch_name (ctx);
	sig_arch_supported = is_signature_writeback_arch_supported (arch_name);
	cc_arch_supported = is_callconv_writeback_arch_supported (arch_name);
	type_arch_supported = is_type_writeback_arch_supported (arch_name);
	if (core) {
		RAnalFunction *focus_fcn = r_anal_get_fcn_in (anal, core->addr, 0);
		if (focus_fcn) {
			focus_callee_addr = focus_fcn->addr;
		}
	}

	int num_fcns = r_list_length (anal->fcns);
	bool xref_enabled = post_mode != SLEIGH_MODE_FAST;
	bool sigwrite_focus_only = sigwrite_enabled && num_fcns > SLEIGH_SIG_WRITEBACK_GLOBAL_MAX_FCNS;
	bool type_writeback_focus_only = type_writeback_enabled && num_fcns > SLEIGH_TYPE_WRITEBACK_GLOBAL_MAX_FCNS;
	if (num_fcns == 0) {
		struct_decl_memo_clear ();
		return true;
	}
	caller_propagation_state_init (&prop_state);
	if (!xref_enabled) {
		R_LOG_INFO ("r2sleigh: post-analysis running in fast mode");
	}

	RListIter *iter;
	RAnalFunction *fcn;
	r_list_foreach (anal->fcns, iter, fcn) {
		int bb_count = (fcn && fcn->bbs) ? r_list_length (fcn->bbs) : 0;
		bool sig_scope_eligible = !sigwrite_focus_only || (focus_callee_addr && fcn && fcn->addr == focus_callee_addr);
		bool type_scope_eligible = !type_writeback_focus_only || (focus_callee_addr && fcn && fcn->addr == focus_callee_addr);
		bool taint_eligible = taint_enabled && bb_count <= SLEIGH_TAINT_MAX_BLOCKS;
		bool sig_eligible = sigwrite_enabled && sig_arch_supported && core
			&& bb_count <= SLEIGH_SIG_WRITEBACK_MAX_BLOCKS && sig_scope_eligible;
		bool type_eligible = type_writeback_enabled && type_arch_supported && core
			&& bb_count <= type_max_blocks && type_scope_eligible;
		bool semantic_for_fcn = false;
		bool need_blocks = taint_eligible || sig_eligible || type_eligible;
		const char *fcn_name = (fcn && fcn->name) ? fcn->name : "unknown";
		BlockArray blocks;

		if (taint_enabled) {
			if (taint_eligible) {
				taint_fcns_eligible++;
			} else {
				taint_fcns_skipped++;
			}
		}
		if (type_eligible) {
			append_unique_ut64 (&type_eligible_addrs, &type_eligible_count, &type_eligible_cap, fcn->addr);
		}
		if (type_writeback_enabled) {
			if (!type_arch_supported || !core) {
				type_wb.type_fcns_skipped_arch++;
			} else if (bb_count > type_max_blocks) {
				type_wb.type_fcns_skipped_size++;
			}
		}

		if (!fcn || !need_blocks) {
			continue;
		}
		if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
			continue;
		}

		if (semantic_for_fcn) {
			semantic_comments_total += write_semantic_comments_for_function (
				anal, ctx, &blocks, fcn->addr, semantic_for_fcn);
		}

		/* Remove previous auto-generated taint artifacts only when taint sweep is active. */
		if (taint_enabled) {
			clear_taint_function_artifacts (anal, core, fcn, &blocks);
		}

		if (taint_eligible) {
			char *taint_json = r2taint_function_summary_json (ctx,
				(const R2ILBlock **)blocks.blocks, blocks.count);
			if (taint_json && *taint_json) {
				RJson *taint_root = r_json_parse (taint_json);
				if (!taint_root || taint_root->type != R_JSON_OBJECT) {
					taint_parse_failures++;
					R_LOG_WARN ("r2sleigh: taint post-analysis parse failed for %s @ 0x%"PFMT64x,
						fcn_name, fcn->addr);
					r_json_free (taint_root);
				} else {
					const RJson *j_sources = r_json_get (taint_root, "sources");
					const RJson *j_sink_hits = r_json_get (taint_root, "sink_hits");
					TaintSourceMap source_map;
					TaintSummaryMap summaries;
					EdgeSet seen_edges;

					taint_source_map_init (&source_map);
					taint_summary_map_init (&summaries);
					edge_set_init (&seen_edges);

					if (j_sources && j_sources->type == R_JSON_ARRAY) {
						const RJson *src_item;
						for (src_item = j_sources->children.first; src_item; src_item = src_item->next) {
							const RJson *j_block;
							const RJson *j_labels;
							const RJson *label;
							ut64 src_block;

							if (src_item->type != R_JSON_OBJECT) {
								continue;
							}
							j_block = r_json_get (src_item, "block");
							j_labels = r_json_get (src_item, "labels");
							if (!j_block || !j_labels || j_labels->type != R_JSON_ARRAY) {
								continue;
							}
							src_block = (ut64)j_block->num.u_value;
							for (label = j_labels->children.first; label; label = label->next) {
								if (label->type == R_JSON_STRING && label->str_value) {
									taint_source_map_add (&source_map, label->str_value, src_block);
								}
							}
						}
					}

					if (!j_sink_hits || j_sink_hits->type != R_JSON_ARRAY) {
						taint_parse_failures++;
						R_LOG_WARN ("r2sleigh: taint sink_hits missing/invalid for %s @ 0x%"PFMT64x,
							fcn_name, fcn->addr);
					} else {
						const RJson *hit_item;
						for (hit_item = j_sink_hits->children.first; hit_item; hit_item = hit_item->next) {
							const RJson *j_block;
							const RJson *j_op;
							const RJson *j_tainted_vars;
							const RJson *tv_item;
							const char *op_name = NULL;
							char **sink_labels = NULL;
							size_t sink_label_count = 0;
							size_t sink_label_cap = 0;
							size_t li;
							ut64 sink_block;
							bool is_call_sink = false;
							bool had_primary_sources = false;
							bool added_nonself = false;

							if (hit_item->type != R_JSON_OBJECT) {
								continue;
							}

							j_block = r_json_get (hit_item, "block");
							j_op = r_json_get (hit_item, "op");
							j_tainted_vars = r_json_get (hit_item, "tainted_vars");
							if (!j_block || !j_tainted_vars || j_tainted_vars->type != R_JSON_ARRAY) {
								continue;
							}
							sink_block = (ut64)j_block->num.u_value;

							if (j_op && j_op->type == R_JSON_OBJECT) {
								const RJson *j_op_name = r_json_get (j_op, "op");
								if (j_op_name && j_op_name->type == R_JSON_STRING && j_op_name->str_value) {
									op_name = j_op_name->str_value;
								}
							}
							is_call_sink = op_name && (!strcmp (op_name, "Call") || !strcmp (op_name, "CallInd"));

							for (tv_item = j_tainted_vars->children.first; tv_item; tv_item = tv_item->next) {
								const RJson *j_labels;
								const RJson *label;
								if (tv_item->type != R_JSON_OBJECT) {
									continue;
								}
								j_labels = r_json_get (tv_item, "labels");
								if (!j_labels || j_labels->type != R_JSON_ARRAY) {
									continue;
								}
								for (label = j_labels->children.first; label; label = label->next) {
									if (label->type != R_JSON_STRING || !label->str_value) {
										continue;
									}
									if (is_noisy_taint_label (label->str_value)) {
										continue;
									}
									append_unique_string (&sink_labels, &sink_label_count, &sink_label_cap, label->str_value);
								}
							}

							taint_sink_hits++;
							TaintBlockSummary *summary = taint_summary_map_get_or_add (&summaries, sink_block);
							if (summary) {
								summary->hits++;
								if (is_call_sink) {
									summary->call_hits++;
								}
								if (op_name && !strcmp (op_name, "Store")) {
									summary->store_hits++;
								}
								if (is_call_sink && j_op && j_op->type == R_JSON_OBJECT) {
									char *call_name = resolve_call_target_name (core, anal, j_op);
									if (call_name) {
										taint_summary_add_call_name (summary, call_name);
										free (call_name);
									}
								}
							}

							if (sink_label_count == 0) {
								free_string_array (sink_labels, sink_label_count);
								continue;
							}

							if (summary) {
								for (li = 0; li < sink_label_count; li++) {
									taint_summary_add_label (summary, sink_labels[li]);
								}
							}

							for (li = 0; li < sink_label_count; li++) {
								const TaintLabelSource *srcs = taint_source_map_find (&source_map, sink_labels[li]);
								size_t si;
								if (!srcs || srcs->count == 0) {
									continue;
								}
								had_primary_sources = true;
								for (si = 0; si < srcs->count; si++) {
									ut64 src_block = srcs->blocks[si];
									if (src_block == sink_block) {
										continue;
									}
									if (maybe_add_taint_xref (anal, &seen_edges, src_block, sink_block, R_ANAL_REF_TYPE_DATA, &taint_xrefs)) {
										added_nonself = true;
									}
								}
							}

							if (had_primary_sources && !added_nonself && sink_block != fcn->addr) {
								maybe_add_taint_xref (anal, &seen_edges, fcn->addr, sink_block, R_ANAL_REF_TYPE_DATA, &taint_xrefs);
							}

							free_string_array (sink_labels, sink_label_count);
						}
					}

					size_t si;
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
					for (si = 0; si < summaries.count; si++) {
						TaintBlockSummary *summary = &summaries.items[si];
						char *comment = format_taint_summary_comment (summary);
						size_t li;
						if (summary->hits > 0 || summary->call_hits > 0 || summary->store_hits > 0) {
							function_meaningful = true;
							function_call_hits += summary->call_hits;
							function_store_hits += summary->store_hits;
							for (li = 0; li < summary->ncall_names; li++) {
								append_unique_string (&function_call_names, &function_ncall_names, &function_call_name_cap, summary->call_names[li]);
								if (is_dangerous_sink (summary->call_names[li])) {
									function_has_dangerous_call = true;
								}
							}
						}
						if (comment && *comment) {
							set_sla_taint_comment_line (anal, summary->addr, comment);
							taint_comments++;

							if (core && core->flags) {
								char flag_name[160];
								snprintf (flag_name, sizeof (flag_name),
									"sla.taint.fcn_%"PFMT64x".blk_%"PFMT64x, fcn->addr, summary->addr);
								if (r_flag_set (core->flags, flag_name, summary->addr, 1)) {
									taint_flags++;
								}
							}
						}

						if (summary->labels && summary->nlabels > 0) {
							int rank = label_rank (summary->labels[0]);

							for (li = 0; li < summary->nlabels; li++) {
								append_unique_string (&function_labels, &function_nlabels, &function_label_cap, summary->labels[li]);
							}

							if (rank < best_sink_rank) {
								free (best_sink_label);
								best_sink_label = strdup (summary->labels[0]);
								best_sink_addr = summary->addr;
								best_sink_rank = rank;
							}
						}
						free (comment);
					}
					{
						TaintRiskLevel risk_level = classify_taint_risk (
							function_meaningful,
							function_has_dangerous_call,
							function_call_hits,
							function_store_hits
						);
						char *risk_comment = format_taint_risk_comment (
							risk_level,
							function_call_names,
							function_ncall_names,
							function_call_hits,
							function_store_hits,
							function_labels,
							function_nlabels
						);

						switch (risk_level) {
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

						if (risk_comment && *risk_comment) {
							set_sla_taint_risk_comment_line (anal, fcn->addr, risk_comment);
							taint_comments++;
						}
						free (risk_comment);

						if (risk_level != TAINT_RISK_NONE && core && core->flags) {
							char generic_risk_flag[192];
							char risk_flag[192];
							snprintf (generic_risk_flag, sizeof (generic_risk_flag),
								"sla.taint.risk.fcn_%"PFMT64x, fcn->addr);
							if (r_flag_set (core->flags, generic_risk_flag, fcn->addr, 1)) {
								taint_flags++;
							}
							snprintf (risk_flag, sizeof (risk_flag),
								"sla.taint.risk.%s.fcn_%"PFMT64x,
								taint_risk_level_flag_name (risk_level), fcn->addr);
							if (r_flag_set (core->flags, risk_flag, fcn->addr, 1)) {
								taint_flags++;
							}
						}
					}
					free_string_array (function_call_names, function_ncall_names);
					free_string_array (function_labels, function_nlabels);

					edge_set_free (&seen_edges);
					taint_summary_map_free (&summaries);
					taint_source_map_free (&source_map);
					r_json_free (taint_root);
				}
			}
			r2il_string_free (taint_json);
		}

		if (!sigwrite_enabled && !type_writeback_enabled) {
			/* Signature writeback explicitly disabled for this run. */
		} else if (!core) {
			if (sigwrite_enabled) {
				sig_fcns_skipped_arch++;
			}
		} else if (bb_count > SLEIGH_SIG_WRITEBACK_MAX_BLOCKS && !type_eligible) {
			sig_fcns_skipped_size++;
		} else {
			char *payload_json = NULL;
			RJson *payload_root = NULL;
			char *external_context_json = NULL;
			char *interproc_scope_json = NULL;
			const RJson *j_signature;
			const RJson *j_callconv;
			const RJson *j_confidence;
			const RJson *j_callconv_confidence;
			WritebackApplyResult sig_apply = {0};
			WritebackApplyResult cc_apply = {0};
			int confidence = 0;
			int cc_confidence = 0;
			bool signature_applied = false;
			bool cc_applied = false;
			bool signature_drift = false;
			bool type_payload_changed = false;
			bool signature_part_eligible = bb_count <= SLEIGH_SIG_WRITEBACK_MAX_BLOCKS;
			bool signature_arch_eligible = sig_arch_supported;
			bool callconv_arch_eligible = cc_arch_supported;
			bool sig_metrics_eligible = signature_arch_eligible && signature_part_eligible;
			ut64 cache_key = 0;
			ut64 payload_hash = 0;
			ut64 dep_hash = 0;
			ut64 prev_payload_hash = 0;
			bool summary_changed = false;
			bool had_cached_payload = false;
			sig_fcns_considered++;
			if (!signature_part_eligible) {
				sig_fcns_skipped_size++;
			}
			if (!signature_arch_eligible) {
				sig_fcns_skipped_arch++;
			}

			external_context_json = sleigh_collect_external_context_json (anal, fcn);
			if (!external_context_json || (external_context_json[0] != '{' && external_context_json[0] != '[')) {
				free (external_context_json);
				external_context_json = strdup ("{}");
			}

			if (type_cache_enabled && type_writeback_enabled) {
				TypeWritebackCacheEntry *cache_entry;
				dep_hash = compute_callee_dependency_hash (core, anal, fcn);
				cache_key = compute_type_cache_key (fcn, external_context_json,
					dep_hash, type_wb_mode, type_min_conf,
					type_rename_min_conf, type_struct_min_conf, type_max_iters);
				cache_entry = type_writeback_cache_get (fcn->addr);
				if (cache_entry && cache_entry->key == cache_key) {
					type_wb.cache_hits++;
					free (external_context_json);
					block_array_free (&blocks);
					continue;
				}
				type_wb.cache_misses++;
				if (cache_entry) {
					had_cached_payload = true;
					prev_payload_hash = cache_entry->payload_hash;
					type_wb.cache_invalidates++;
				}
			}

			interproc_scope_json = build_type_interproc_scope_json (core, anal, ctx, fcn, &blocks);
			payload_json = r2sleigh_infer_type_writeback_json_ex (ctx,
				(const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr, fcn->name,
				external_context_json? external_context_json: "{}",
				1, type_max_iters, 1, interproc_scope_json? interproc_scope_json: "{}");
			free (interproc_scope_json);
			interproc_scope_json = NULL;
			if (!payload_json || !*payload_json) {
				if (sig_metrics_eligible) {
					sig_parse_failures++;
				}
				type_wb.payload_missing++;
				r2il_string_free (payload_json);
			} else {
				payload_hash = r_str_hash64 (payload_json);
				summary_changed = !had_cached_payload || prev_payload_hash != payload_hash;
				char *payload_json_for_parse = strdup (payload_json);
				payload_root = r_json_parse (payload_json_for_parse? payload_json_for_parse: payload_json);
				if (!payload_root || payload_root->type != R_JSON_OBJECT) {
					if (sig_metrics_eligible) {
						sig_parse_failures++;
					}
					type_wb.payload_parse_failures++;
					r_json_free (payload_root);
					free (payload_json_for_parse);
					r2il_string_free (payload_json);
				} else {
					j_signature = r_json_get (payload_root, "signature");
					j_callconv = r_json_get (payload_root, "callconv");
					j_confidence = r_json_get (payload_root, "confidence");
					j_callconv_confidence = r_json_get (payload_root, "callconv_confidence");
					if (j_confidence && j_confidence->type == R_JSON_INTEGER) {
						confidence = (int)j_confidence->num.u_value;
					}
					if (j_callconv_confidence && j_callconv_confidence->type == R_JSON_INTEGER) {
						cc_confidence = (int)j_callconv_confidence->num.u_value;
					}

					if (signature_arch_eligible && signature_part_eligible
							&& j_signature && j_signature->type == R_JSON_STRING
							&& j_signature->str_value && *j_signature->str_value) {
						if (confidence < SLEIGH_SIG_MIN_CONFIDENCE) {
							sig_skipped_low_conf++;
						} else {
							sig_apply = apply_inferred_signature (anal, core, fcn, j_signature->str_value, payload_root);
							if (sig_apply.api_verify_fail) {
								sig_api_verify_fail++;
							}
							if (sig_apply.cmd_fallback_attempted) {
								sig_cmd_fallback_attempted++;
							}
							if (sig_apply.cmd_apply_fail) {
								sig_cmd_apply_fail++;
							}
							if (sig_apply.path == WRITEBACK_APPLY_API) {
								sig_api_apply_ok++;
								sig_signatures_updated++;
								signature_applied = true;
							} else if (sig_apply.path == WRITEBACK_APPLY_CMD) {
								sig_cmd_apply_ok++;
								sig_signatures_updated++;
								signature_applied = true;
							}
						}
						if (signature_applied) {
							propagate_signature_to_direct_callers (anal, core, fcn->addr, fcn_name,
								&prop_state, focus_callee_addr && fcn->addr == focus_callee_addr);
						} else if (!sig_apply.already_applied && confidence >= SLEIGH_SIG_MIN_CONFIDENCE) {
							sig_cmd_failures++;
							R_LOG_WARN ("r2sleigh: signature write-back failed for %s @ 0x%"PFMT64x" reason=%s sig=%.160s",
								fcn_name, fcn->addr, sig_apply.detail[0]? sig_apply.detail: "unknown",
								j_signature->str_value);
						}
					} else {
						if (sig_metrics_eligible) {
							sig_parse_failures++;
						}
					}

					if (signature_part_eligible
							&& j_callconv && j_callconv->type == R_JSON_STRING
							&& j_callconv->str_value && *j_callconv->str_value) {
						if (!callconv_arch_eligible) {
							cc_skipped_arch++;
						} else if (cc_confidence < SLEIGH_CC_MIN_CONFIDENCE) {
							cc_skipped_low_conf++;
						} else {
							cc_apply = apply_inferred_callconv (anal, core, fcn, j_callconv->str_value);
							if (cc_apply.api_verify_fail) {
								cc_api_verify_fail++;
							}
							if (cc_apply.cmd_fallback_attempted) {
								cc_cmd_fallback_attempted++;
							}
							if (cc_apply.cmd_apply_fail) {
								cc_cmd_apply_fail++;
							}
							if (cc_apply.path == WRITEBACK_APPLY_API) {
								cc_api_apply_ok++;
								sig_cc_updated++;
								cc_applied = true;
							} else if (cc_apply.path == WRITEBACK_APPLY_CMD) {
								cc_cmd_apply_ok++;
								sig_cc_updated++;
								cc_applied = true;
							}
						}
						if (callconv_arch_eligible && !cc_applied && !cc_apply.already_applied
								&& cc_confidence >= SLEIGH_CC_MIN_CONFIDENCE) {
							sig_cmd_failures++;
							R_LOG_WARN ("r2sleigh: calling-convention write-back failed for %s @ 0x%"PFMT64x,
								fcn_name, fcn->addr);
						}
					} else if (signature_part_eligible) {
						cc_missing_payload++;
					}

					if (type_eligible && type_writeback_enabled) {
						type_payload_changed = apply_type_writeback_payload (
							anal, core, fcn, payload_root, type_wb_mode,
							type_min_conf, type_rename_min_conf, type_struct_min_conf,
							type_global_max_links, &type_wb);
						if (type_payload_changed) {
							append_unique_ut64 (&changed_type_fcns, &changed_type_count, &changed_type_cap, fcn->addr);
							run_caller_type_match (anal, core, fcn);
							run_caller_afva (core, fcn);
							propagate_signature_to_direct_callers (anal, core, fcn->addr, fcn_name,
								&prop_state, focus_callee_addr && fcn->addr == focus_callee_addr);
						}
					}
					if ((signature_applied || cc_applied) && type_writeback_enabled) {
						append_unique_ut64 (&changed_type_fcns, &changed_type_count, &changed_type_cap, fcn->addr);
					}

					if (signature_part_eligible && sigverify_enabled && (signature_applied || cc_applied)) {
						consistency_verified++;
							if (verify_practical_signature_consistency (
									anal, fcn, payload_root, signature_applied, cc_applied,
									&signature_drift, &consistency_reasons)) {
							consistency_ok++;
						} else {
							consistency_mismatch++;
						}
						if (signature_drift) {
							afij_signature_drift++;
						}
					}

					if (type_cache_enabled && type_writeback_enabled) {
						ut64 applied_hash = type_payload_changed? payload_hash: 0;
						if (type_writeback_cache_put (fcn->addr, cache_key, dep_hash, payload_hash, applied_hash, payload_json)) {
							type_wb.cache_updates++;
						}
					}
					if (summary_changed || signature_applied || cc_applied || type_payload_changed) {
						append_unique_ut64 (&changed_type_fcns, &changed_type_count, &changed_type_cap, fcn->addr);
					}
					if (signature_applied || cc_applied || type_payload_changed) {
						char *post_external_context_json = sleigh_collect_external_context_json (anal, fcn);
						if (!post_external_context_json || (post_external_context_json[0] != '{' && post_external_context_json[0] != '[')) {
							free (post_external_context_json);
							post_external_context_json = strdup ("{}");
						}
						r2sleigh_alias_function_analysis_artifact_cache (ctx,
							(const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr, fcn->name,
							external_context_json? external_context_json: "{}",
							post_external_context_json? post_external_context_json: "{}");
						free (post_external_context_json);
					}
					r_json_free (payload_root);
					free (payload_json_for_parse);
					r2il_string_free (payload_json);
				}
			}
			free (interproc_scope_json);
			free (external_context_json);
		}

		block_array_free (&blocks);
	}

	if (xref_enabled) {
		ut64 *xref_queue = NULL;
		size_t xref_queue_count = 0;
		size_t xref_queue_cap = 0;
		RListIter *xref_iter;
		RAnalFunction *xref_fcn;

		r_list_foreach (anal->fcns, xref_iter, xref_fcn) {
			if (!xref_fcn) {
				continue;
			}
			if (data_ref_cache_get (xref_fcn->addr)) {
				xref_cache_hits++;
			}
			append_unique_ut64 (&xref_queue, &xref_queue_count, &xref_queue_cap, xref_fcn->addr);
			xref_dirty_queued++;
		}

		while (xref_queue_count > 0) {
			ut64 faddr = xref_queue[--xref_queue_count];
			RAnalFunction *xref_fcn_cur = r_anal_get_fcn_in (anal, faddr, 0);
			BlockArray xref_blocks;
			char *xref_json;
			ut64 cache_key;
			int ref_count;

			if (!xref_fcn_cur) {
				continue;
			}
			if (!lift_function_blocks (anal, xref_fcn_cur, ctx, &xref_blocks)) {
				continue;
			}
			cache_key = compute_xref_cache_key (xref_fcn_cur, &xref_blocks, post_mode);
			xref_json = r2sleigh_get_data_refs (ctx,
				(const R2ILBlock **)xref_blocks.blocks, xref_blocks.count, xref_fcn_cur->addr);
			if (!xref_json || !*xref_json) {
				r2il_string_free (xref_json);
				block_array_free (&xref_blocks);
				continue;
			}

			ref_count = collect_data_refs_from_json (anal, xref_fcn_cur, xref_json, NULL, true);
			xrefs_added += ref_count;
			xref_recomputes++;
			data_ref_cache_put (xref_fcn_cur->addr, cache_key, r_str_hash64 (xref_json), ref_count);
			r2il_string_free (xref_json);
			block_array_free (&xref_blocks);
		}
		free (xref_queue);
	}

	if (type_eligible_count > 1) {
		qsort (type_eligible_addrs, type_eligible_count, sizeof (ut64), ut64_cmp_asc);
	}

	if (type_writeback_enabled) {
		ut64 *queue = NULL;
		size_t queue_count = 0;
		size_t queue_cap = 0;
		size_t i;
		int iter_idx = 1;
		bool converged = true;
		if (changed_type_count > 0 && type_eligible_count > 0) {
			for (i = 0; i < changed_type_count; i++) {
				RAnalFunction *changed_fcn = r_anal_get_fcn_in (anal, changed_type_fcns[i], 0);
				if (!changed_fcn) {
					continue;
				}
				enqueue_fixpoint_neighbors (anal, changed_fcn,
					type_eligible_addrs, type_eligible_count,
					&queue, &queue_count, &queue_cap, &type_wb, false);
			}
		}
		while (queue_count > 0 && iter_idx < type_max_iters) {
			ut64 *current = queue;
			size_t current_count = queue_count;
			iter_idx++;
			type_wb.fixpoint_iters = iter_idx;
			qsort (current, current_count, sizeof (ut64), ut64_cmp_asc);
			queue = NULL;
			queue_count = 0;
			queue_cap = 0;

			for (i = 0; i < current_count; i++) {
				ut64 faddr = current[i];
				RAnalFunction *fcn = r_anal_get_fcn_in (anal, faddr, 0);
				int bb_count;
				BlockArray blocks;
				char *external_context_json = NULL;
				char *interproc_scope_json = NULL;
				char *payload_json = NULL;
				RJson *payload_root = NULL;
				bool type_changed = false;
				bool sig_or_cc_changed = false;
				bool summary_changed = false;
				ut64 payload_hash = 0;
				ut64 dep_hash = 0;
				ut64 cache_key = 0;
				ut64 prev_payload_hash = 0;
				bool had_cached_payload = false;
				type_wb.fixpoint_queue_pops++;
				if (!fcn) {
					continue;
				}
				bb_count = (fcn->bbs)? r_list_length (fcn->bbs): 0;
				if (bb_count > type_max_blocks) {
					type_wb.type_fcns_skipped_size++;
					continue;
				}
				if (!lift_function_blocks (anal, fcn, ctx, &blocks)) {
					continue;
				}

				external_context_json = sleigh_collect_external_context_json (anal, fcn);
				if (!external_context_json || (external_context_json[0] != '{' && external_context_json[0] != '[')) {
					free (external_context_json);
					external_context_json = strdup ("{}");
				}

				if (type_cache_enabled) {
					TypeWritebackCacheEntry *cache_entry;
					dep_hash = compute_callee_dependency_hash (core, anal, fcn);
					cache_key = compute_type_cache_key (fcn, external_context_json,
						dep_hash, type_wb_mode, type_min_conf,
						type_rename_min_conf, type_struct_min_conf, type_max_iters);
					cache_entry = type_writeback_cache_get (fcn->addr);
					if (cache_entry && cache_entry->key == cache_key) {
						type_wb.cache_hits++;
						free (external_context_json);
						block_array_free (&blocks);
						continue;
					}
					type_wb.cache_misses++;
					if (cache_entry) {
						had_cached_payload = true;
						prev_payload_hash = cache_entry->payload_hash;
						type_wb.cache_invalidates++;
					}
				}

				interproc_scope_json = build_type_interproc_scope_json (core, anal, ctx, fcn, &blocks);
				payload_json = r2sleigh_infer_type_writeback_json_ex (ctx,
					(const R2ILBlock **)blocks.blocks, blocks.count, fcn->addr, fcn->name,
					external_context_json? external_context_json: "{}",
					(size_t)iter_idx, (size_t)type_max_iters, 0,
					interproc_scope_json? interproc_scope_json: "{}");
				free (interproc_scope_json);
				interproc_scope_json = NULL;
				if (!payload_json || !*payload_json) {
					type_wb.payload_missing++;
					r2il_string_free (payload_json);
					free (external_context_json);
					block_array_free (&blocks);
					continue;
				}
				payload_hash = r_str_hash64 (payload_json);
				summary_changed = !had_cached_payload || prev_payload_hash != payload_hash;
				char *payload_json_for_parse = strdup (payload_json);
				payload_root = r_json_parse (payload_json_for_parse? payload_json_for_parse: payload_json);
				if (!payload_root || payload_root->type != R_JSON_OBJECT) {
					type_wb.payload_parse_failures++;
					r_json_free (payload_root);
					free (payload_json_for_parse);
					r2il_string_free (payload_json);
					free (external_context_json);
					block_array_free (&blocks);
					continue;
				}

				if (sig_arch_supported && bb_count <= SLEIGH_SIG_WRITEBACK_MAX_BLOCKS) {
					const RJson *j_sig = r_json_get (payload_root, "signature");
					const RJson *j_cc = r_json_get (payload_root, "callconv");
					const RJson *j_conf = r_json_get (payload_root, "confidence");
					const RJson *j_cc_conf = r_json_get (payload_root, "callconv_confidence");
					int conf = (j_conf && j_conf->type == R_JSON_INTEGER)? (int)j_conf->num.u_value: 0;
					int cc_conf = (j_cc_conf && j_cc_conf->type == R_JSON_INTEGER)? (int)j_cc_conf->num.u_value: 0;
					if (j_sig && j_sig->type == R_JSON_STRING && j_sig->str_value && *j_sig->str_value
							&& conf >= SLEIGH_SIG_MIN_CONFIDENCE) {
						WritebackApplyResult wa = apply_inferred_signature (anal, core, fcn, j_sig->str_value, payload_root);
						if (wa.path != WRITEBACK_APPLY_NONE) {
							sig_or_cc_changed = true;
							sig_signatures_updated++;
						}
					}
					if (j_cc && j_cc->type == R_JSON_STRING && j_cc->str_value && *j_cc->str_value
							&& cc_conf >= SLEIGH_CC_MIN_CONFIDENCE) {
						if (!cc_arch_supported) {
							cc_skipped_arch++;
						} else {
						WritebackApplyResult wa = apply_inferred_callconv (anal, core, fcn, j_cc->str_value);
						if (wa.path != WRITEBACK_APPLY_NONE) {
							sig_or_cc_changed = true;
							sig_cc_updated++;
						}
						}
					} else {
						cc_missing_payload++;
					}
				}

				type_changed = apply_type_writeback_payload (anal, core, fcn, payload_root, type_wb_mode,
					type_min_conf, type_rename_min_conf, type_struct_min_conf,
					type_global_max_links, &type_wb);
				if (type_changed || sig_or_cc_changed) {
					run_caller_type_match (anal, core, fcn);
					run_caller_afva (core, fcn);
				}
				if (summary_changed || type_changed || sig_or_cc_changed) {
					enqueue_fixpoint_neighbors (anal, fcn,
						type_eligible_addrs, type_eligible_count,
						&queue, &queue_count, &queue_cap, &type_wb, true);
				}
				if (type_cache_enabled) {
					ut64 applied_hash = (type_changed || sig_or_cc_changed)? payload_hash: 0;
					if (type_writeback_cache_put (fcn->addr, cache_key, dep_hash, payload_hash, applied_hash, payload_json)) {
						type_wb.cache_updates++;
					}
				}
				r_json_free (payload_root);
				free (payload_json_for_parse);
				r2il_string_free (payload_json);
				free (interproc_scope_json);
				free (external_context_json);
				block_array_free (&blocks);
			}
			free (current);
		}
		if (queue_count == 0) {
			converged = true;
			snprintf (type_wb.fixpoint_stop_reason, sizeof (type_wb.fixpoint_stop_reason), "queue_empty");
		} else {
			converged = false;
			snprintf (type_wb.fixpoint_stop_reason, sizeof (type_wb.fixpoint_stop_reason), "max_iters");
		}
		free (queue);
		if (type_wb.fixpoint_iters == 0) {
			type_wb.fixpoint_iters = 1;
		}
		type_wb.fixpoint_converged = converged? 1: 0;
	}

	R_LOG_INFO ("r2sleigh: post-analysis added %d xrefs", xrefs_added);
	R_LOG_INFO ("r2sleigh: post-analysis taint enabled=%d eligible=%d skipped=%d comments=%d flags=%d xrefs=%d sink_hits=%d parse_failures=%d",
		taint_enabled? 1: 0, taint_fcns_eligible, taint_fcns_skipped, taint_comments, taint_flags, taint_xrefs,
		taint_sink_hits, taint_parse_failures);
	R_LOG_INFO ("r2sleigh: post-analysis risk summary: critical=%d high=%d medium=%d low=%d",
		taint_risk_critical, taint_risk_high, taint_risk_medium, taint_risk_low);
	R_LOG_INFO ("r2sleigh: post-analysis semantic comments enabled=%d emitted=%zu",
		semantic_comments_enabled? 1: 0, semantic_comments_total);
	R_LOG_INFO ("r2sleigh: signature write-back enabled=%d verify=%d considered=%d skipped_arch=%d skipped_size=%d parse_failures=%d command_failures=%d signatures_updated=%d cc_updated=%d sig_low_conf_skips=%d cc_low_conf_skips=%d cc_skipped_arch=%d cc_missing_payload=%d consistency_verified=%d consistency_ok=%d consistency_mismatch=%d afij_signature_drift=%d consistency_readback_fail=%d consistency_ret_mismatch=%d consistency_argc_mismatch=%d consistency_argtype_mismatch=%d consistency_callconv_mismatch=%d",
		sigwrite_enabled? 1: 0, sigverify_enabled? 1: 0, sig_fcns_considered, sig_fcns_skipped_arch, sig_fcns_skipped_size, sig_parse_failures,
		sig_cmd_failures, sig_signatures_updated, sig_cc_updated, sig_skipped_low_conf,
		cc_skipped_low_conf, cc_skipped_arch, cc_missing_payload, consistency_verified, consistency_ok, consistency_mismatch,
		afij_signature_drift, consistency_reasons.readback_fail,
		consistency_reasons.ret_mismatch, consistency_reasons.argc_mismatch,
		consistency_reasons.argtype_mismatch, consistency_reasons.callconv_mismatch);
	R_LOG_INFO ("r2sleigh: signature write-back apply-path sig_api_apply_ok=%d sig_api_verify_fail=%d sig_cmd_fallback_attempted=%d sig_cmd_apply_ok=%d sig_cmd_apply_fail=%d cc_api_apply_ok=%d cc_api_verify_fail=%d cc_cmd_fallback_attempted=%d cc_cmd_apply_ok=%d cc_cmd_apply_fail=%d cc_missing_payload=%d",
		sig_api_apply_ok, sig_api_verify_fail, sig_cmd_fallback_attempted,
		sig_cmd_apply_ok, sig_cmd_apply_fail, cc_api_apply_ok,
		cc_api_verify_fail, cc_cmd_fallback_attempted,
		cc_cmd_apply_ok, cc_cmd_apply_fail, cc_missing_payload);
	if (!type_wb.fixpoint_stop_reason[0]) {
		snprintf (type_wb.fixpoint_stop_reason, sizeof (type_wb.fixpoint_stop_reason),
			type_writeback_enabled? "queue_empty": "off");
	}
	R_LOG_INFO ("r2sleigh: post-analysis summary fcns=%d xref_cache_hits=%d xref_recomputes=%d xref_dirty_queued=%d type_queue_pops=%d type_fixpoint_converged=%d",
		num_fcns, xref_cache_hits, xref_recomputes, xref_dirty_queued,
		type_wb.fixpoint_queue_pops, type_wb.fixpoint_converged);
	R_LOG_INFO ("r2sleigh: type write-back enabled=%d mode=%d vars_considered=%d vars_applied=%d vars_hint_only=%d vars_low_conf=%d vars_conflict=%d vars_api_verify_fail=%d vars_cmd_fallback_attempted=%d vars_cmd_apply_fail=%d renames_considered=%d renames_applied=%d renames_low_conf=%d renames_conflict=%d rename_generated_guard_skips=%d structs_considered=%d structs_imported=%d structs_low_conf=%d structs_import_fail=%d global_links_considered=%d global_links_applied=%d global_links_low_conf=%d global_links_conflict_skip=%d global_links_existing_preserved=%d global_links_fail=%d payload_missing=%d payload_parse_failures=%d cache_hits=%d cache_misses=%d cache_invalidates=%d cache_updates=%d type_skipped_arch=%d type_skipped_size=%d fixpoint_iters=%d fixpoint_converged=%d fixpoint_queue_pushes=%d fixpoint_queue_pops=%d fixpoint_requeues=%d fixpoint_stop=%s",
		type_writeback_enabled? 1: 0, (int)type_wb_mode,
		type_wb.vars_considered, type_wb.vars_applied, type_wb.vars_hint_only,
		type_wb.vars_skipped_low_conf, type_wb.vars_skipped_conflict,
		type_wb.vars_api_verify_fail, type_wb.vars_cmd_fallback_attempted, type_wb.vars_cmd_apply_fail,
		type_wb.renames_considered, type_wb.renames_applied,
		type_wb.renames_skipped_low_conf, type_wb.renames_skipped_conflict,
		type_wb.rename_generated_guard_skips,
		type_wb.structs_considered, type_wb.structs_imported,
		type_wb.structs_skipped_low_conf, type_wb.structs_import_fail,
		type_wb.global_links_considered, type_wb.global_links_applied,
		type_wb.global_links_skipped_low_conf, type_wb.global_links_conflict_skip,
		type_wb.global_links_existing_preserved, type_wb.global_links_fail,
		type_wb.payload_missing, type_wb.payload_parse_failures,
		type_wb.cache_hits, type_wb.cache_misses, type_wb.cache_invalidates, type_wb.cache_updates,
		type_wb.type_fcns_skipped_arch, type_wb.type_fcns_skipped_size,
		type_wb.fixpoint_iters, type_wb.fixpoint_converged,
		type_wb.fixpoint_queue_pushes, type_wb.fixpoint_queue_pops, type_wb.fixpoint_requeues,
		type_wb.fixpoint_stop_reason);
	R_LOG_INFO ("r2sleigh: type write-back fixpoint iters=%d converged=%d queue_pushes=%d queue_pops=%d requeues=%d stop=%s type_skipped_arch=%d type_skipped_size=%d global_links_conflict_skip=%d global_links_existing_preserved=%d",
		type_wb.fixpoint_iters, type_wb.fixpoint_converged,
		type_wb.fixpoint_queue_pushes, type_wb.fixpoint_queue_pops, type_wb.fixpoint_requeues,
		type_wb.fixpoint_stop_reason,
		type_wb.type_fcns_skipped_arch, type_wb.type_fcns_skipped_size,
		type_wb.global_links_conflict_skip, type_wb.global_links_existing_preserved);
	sample_callees = format_sample_callees (prop_state.sample_callees, prop_state.sample_callees_count);
	R_LOG_INFO ("r2sleigh: caller propagation prop_callees_triggered=%d prop_callers_considered=%d prop_callers_updated=%d prop_callers_dedup_skipped=%d prop_callers_missing_fcn=%d prop_type_match_failures=%d prop_afva_failures=%d sample_callees=%s",
		prop_state.prop_callees_triggered,
		prop_state.prop_callers_considered, prop_state.prop_callers_updated,
		prop_state.prop_callers_dedup_skipped, prop_state.prop_callers_missing_fcn,
		prop_state.prop_type_match_failures, prop_state.prop_afva_failures,
		sample_callees ? sample_callees : "-");
	free (sample_callees);
	caller_propagation_state_fini (&prop_state);
	free (type_eligible_addrs);
	free (changed_type_fcns);
	struct_decl_memo_clear ();
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
};

#ifndef R2_PLUGIN_INCORE
R_API RLibStruct radare_plugin = {
	.type = R_LIB_TYPE_ANAL,
	.data = &r_anal_plugin_sleigh,
	.version = R2_VERSION,
	.abiversion = R2_ABIVERSION
};
#endif
