
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
