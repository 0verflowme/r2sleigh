
/* Content hash of one function's analysis, for artifact staleness.
 *
 * This used to build a whole function snapshot and read its revision
 * identity back out, which meant radare2 depended on r2sleigh's capture to
 * answer a question about its own stored artifacts. It hashes radare2's state
 * directly instead. Every input the old hash folded in was derived from these
 * same facts, so a change that mattered still changes the hash; hashing the
 * inputs rather than the derivations is the more conservative direction.
 *
 * The value is not stable across versions. Bumping the salt below invalidates
 * every stored artifact revision once, which is the intended way to force a
 * recapture after the hashed inputs change. */
#define FUNCTION_CONTEXT_HASH_SALT 2ULL

static ut64 context_hash_mix(ut64 hash, ut64 value) {
	hash ^= value;
	return hash * 0x100000001b3ULL;
}

static ut64 context_hash_string(ut64 hash, const char *string) {
	if (!string) {
		return context_hash_mix (hash, 0xffffffffffffffffULL);
	}
	const unsigned char *p = (const unsigned char *)string;
	while (*p) {
		hash = context_hash_mix (hash, (ut64)*p++);
	}
	return context_hash_mix (hash, 0);
}

R_API ut64 r_anal_function_context_hash(RAnal *anal, RAnalFunction *fcn) {
	R_RETURN_VAL_IF_FAIL (anal && fcn, 0);
	ut64 hash = 0xcbf29ce484222325ULL;
	hash = context_hash_mix (hash, FUNCTION_CONTEXT_HASH_SALT);
	hash = context_hash_mix (hash, fcn->addr);
	hash = context_hash_mix (hash, (ut64)r_anal_function_linear_size (fcn));
	hash = context_hash_mix (hash, (ut64)fcn->maxstack);
	hash = context_hash_mix (hash, (ut64)fcn->bits);
	hash = context_hash_mix (hash, (ut64)fcn->type);
	hash = context_hash_string (hash, fcn->name);
	hash = context_hash_string (hash, fcn->callconv);
	if (anal->config) {
		hash = context_hash_string (hash, anal->config->arch);
		hash = context_hash_string (hash, anal->config->cpu);
		hash = context_hash_mix (hash, (ut64)anal->config->bits);
		hash = context_hash_mix (hash, anal->config->big_endian? 1: 0);
	}
	RListIter *iter;
	RAnalBlock *block;
	r_list_foreach (fcn->bbs, iter, block) {
		if (!block) {
			continue;
		}
		hash = context_hash_mix (hash, block->addr);
		hash = context_hash_mix (hash, (ut64)block->size);
		hash = context_hash_mix (hash, block->jump);
		hash = context_hash_mix (hash, block->fail);
		if (block->switch_op) {
			hash = context_hash_mix (hash, block->switch_op->addr);
			hash = context_hash_mix (hash, block->switch_op->def_val);
			RListIter *case_iter;
			RAnalCaseOp *case_op;
			r_list_foreach (block->switch_op->cases, case_iter, case_op) {
				if (case_op) {
					hash = context_hash_mix (hash, case_op->value);
					hash = context_hash_mix (hash, case_op->jump);
				}
			}
		}
	}
	RAnalFcnVarsCache cache = {0};
	r_anal_function_vars_cache_init_readonly (anal, &cache, fcn);
	RAnalVar **var_it;
	R_VEC_FOREACH (cache.rvars, var_it) {
		RAnalVar *var = *var_it;
		if (var) {
			hash = context_hash_string (hash, var->name);
			hash = context_hash_string (hash, var->type);
			hash = context_hash_mix (hash, (ut64)(st64)var->delta);
		}
	}
	R_VEC_FOREACH (cache.bvars, var_it) {
		RAnalVar *var = *var_it;
		if (var) {
			hash = context_hash_string (hash, var->name);
			hash = context_hash_string (hash, var->type);
			hash = context_hash_mix (hash, (ut64)(st64)var->delta);
		}
	}
	R_VEC_FOREACH (cache.svars, var_it) {
		RAnalVar *var = *var_it;
		if (var) {
			hash = context_hash_string (hash, var->name);
			hash = context_hash_string (hash, var->type);
			hash = context_hash_mix (hash, (ut64)(st64)var->delta);
		}
	}
	r_anal_function_vars_cache_fini (&cache);
	// Deliberately not the dirty epochs. This is a hash of what the analysis
	// *says*, not of how many times it has been touched: every caller that
	// stores it also stores the two epochs and checks them separately, so
	// folding them in here would make a revision differ from itself after any
	// mutation that left the content alone -- including the artifact publish
	// whose result the caller is about to verify.
	hash = context_hash_mix (hash, r_anal_types_context_hash (anal));
	return hash? hash: 1;
}
