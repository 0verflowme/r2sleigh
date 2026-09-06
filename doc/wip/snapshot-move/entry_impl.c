/* Content hash of one function's analysis, under the core lock.
 *
 * Callers store this next to an artifact and compare it later to find out
 * whether the analysis has moved underneath them. It used to be answered by
 * capturing a whole function snapshot and reading one field out of it; the
 * capture now lives in the r2sleigh plugin, and radare2 answers its own
 * question from its own state. */
R_API bool r_core_function_context_hash(RCore *core, ut64 function_addr, ut64 *out_hash, const char **reason) {
	R_RETURN_VAL_IF_FAIL (core && core->anal && core->lock && out_hash, false);
	bool result = false;
	r_th_lock_enter (core->lock);
	if (reason) {
		*reason = NULL;
	}
	if (core_snapshot_io_is_debug (core->io)) {
		if (reason) {
			*reason = "a revision is not taken from a debug-backed target";
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
	*out_hash = r_anal_function_context_hash (core->anal, fcn);
	r_th_lock_leave (core->anal->lock);
	result = *out_hash != 0;
beach:
	r_th_lock_leave (core->lock);
	return result;
}