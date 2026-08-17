/* Serializes a borrowed radare2 function snapshot into the flat wire format.
 *
 * This replaces the accessor table: instead of radare2 exposing a callback per
 * field so r2source can walk the snapshot lazily, the snapshot is read once
 * here and handed over as one buffer. The reads themselves are the same ones the
 * accessors performed, so this is a re-shaping of existing logic rather than new
 * interpretation of the snapshot.
 *
 * Field order must match r2source::snapshot_wire::encode_snapshot exactly. That
 * order is asserted by decoding what this writes, so a mismatch fails a test
 * rather than producing a buffer the parser silently misreads. */

#include "snapshot_wire.h"

#include <r_anal.h>

/* radare2 reports byte order with these two tags rather than a boolean. */
#define WALK_ENDIAN_LITTLE 0x4321u
#define WALK_ENDIAN_BIG 0x1234u

/* Wire discriminants for SourceEndianness. */
#define WALK_WIRE_ENDIAN_LITTLE 0
#define WALK_WIRE_ENDIAN_BIG 1

/* Wire discriminants for AdvisorySuccessorKind, matching the order the Rust
 * enum declares. */
#define WALK_SUCCESSOR_DIRECT 0
#define WALK_SUCCESSOR_FALLTHROUGH 1
#define WALK_SUCCESSOR_SWITCH_CASE 2
#define WALK_SUCCESSOR_SWITCH_DEFAULT 3

/* Largest single block this producer will serialize. A block longer than this
 * is refused rather than truncated, since a short read would encode different
 * instructions than the function contains. */
#define WALK_BLOCK_BYTES_MAX (16u << 20)

/* Longest identifier the snapshot will hand back. Names longer than this are a
 * refusal rather than a truncation: a truncated register or type name would
 * decode into a different entity. */
#define WALK_NAME_MAX 512

static bool walk_string(R2SleighWireWriter *writer, bool (*get)(const RAnalFunctionSnapshot *,
		char *, size_t), const RAnalFunctionSnapshot *snapshot) {
	char name[WALK_NAME_MAX];
	if (!get (snapshot, name, sizeof (name))) {
		return false;
	}
	r2sleigh_wire_string (writer, name);
	return true;
}

static bool walk_machine_profile(R2SleighWireWriter *writer,
		const RAnalFunctionSnapshot *snapshot, const RAnalFunctionSnapshotView *view) {
	if (!walk_string (writer, r_anal_function_snapshot_arch_id, snapshot)
		|| !walk_string (writer, r_anal_function_snapshot_cpu_id, snapshot)) {
		return false;
	}
	if (view->bits < 0) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)view->bits);
	switch (view->endian) {
	case WALK_ENDIAN_LITTLE:
		r2sleigh_wire_u8 (writer, WALK_WIRE_ENDIAN_LITTLE);
		break;
	case WALK_ENDIAN_BIG:
		r2sleigh_wire_u8 (writer, WALK_WIRE_ENDIAN_BIG);
		break;
	default:
		/* An unrecognized order is refused: guessing it would reinterpret
		 * every value in the snapshot. */
		return false;
	}
	return true;
}

static bool walk_successor(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot,
		size_t block_index, size_t successor_index) {
	RAnalSnapshotSuccessorView view = {0};
	if (!r_anal_function_snapshot_successor_view (snapshot, block_index, successor_index,
			&view)) {
		return false;
	}
	uint8_t kind;
	switch (view.kind) {
	case R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT:
		kind = WALK_SUCCESSOR_DIRECT;
		break;
	case R_ANAL_SNAPSHOT_SUCCESSOR_FALLTHROUGH:
		kind = WALK_SUCCESSOR_FALLTHROUGH;
		break;
	case R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_CASE:
		kind = WALK_SUCCESSOR_SWITCH_CASE;
		break;
	case R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_DEFAULT:
		kind = WALK_SUCCESSOR_SWITCH_DEFAULT;
		break;
	default:
		return false;
	}
	r2sleigh_wire_u8 (writer, kind);
	r2sleigh_wire_u64 (writer, view.target_addr);
	/* A case value belongs to a labelled case and to nothing else, so presence
	 * follows the kind rather than being reported separately. */
	if (kind == WALK_SUCCESSOR_SWITCH_CASE) {
		r2sleigh_wire_bool (writer, true);
		r2sleigh_wire_u64 (writer, view.case_value);
	} else {
		r2sleigh_wire_bool (writer, false);
	}
	r2sleigh_wire_bool (writer, view.external? true: false);
	return true;
}

static bool walk_block(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot,
		size_t index) {
	RAnalSnapshotBlockView view = {0};
	if (!r_anal_function_snapshot_block_view (snapshot, index, &view)) {
		return false;
	}
	r2sleigh_wire_u64 (writer, view.addr);
	if (view.size == 0 || view.size > WALK_BLOCK_BYTES_MAX) {
		return false;
	}
	ut8 *bytes = malloc ((size_t)view.size);
	if (!bytes) {
		return false;
	}
	if (!r_anal_function_snapshot_block_bytes (snapshot, index, 0, bytes, (size_t)view.size)) {
		free (bytes);
		return false;
	}
	r2sleigh_wire_bytes (writer, bytes, (size_t)view.size);
	free (bytes);
	if (view.num_successors > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)view.num_successors);
	for (size_t i = 0; i < view.num_successors; i++) {
		if (!walk_successor (writer, snapshot, index, i)) {
			return false;
		}
	}
	/* radare2 reports no switch as a zero address, which is not a valid
	 * instruction address inside a block. */
	if (view.switch_addr) {
		r2sleigh_wire_bool (writer, true);
		r2sleigh_wire_u64 (writer, view.switch_addr);
	} else {
		r2sleigh_wire_bool (writer, false);
	}
	return true;
}

static bool walk_image(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot,
		const RAnalFunctionSnapshotView *view) {
	r2sleigh_wire_u64 (writer, view->function_addr);
	if (view->num_blocks == 0 || view->num_blocks > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)view->num_blocks);
	for (size_t i = 0; i < view->num_blocks; i++) {
		if (!walk_block (writer, snapshot, i)) {
			return false;
		}
	}
	if (view->num_external_exits > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)view->num_external_exits);
	for (size_t i = 0; i < view->num_external_exits; i++) {
		ut64 target = 0;
		if (!r_anal_function_snapshot_external_exit (snapshot, i, &target)) {
			return false;
		}
		r2sleigh_wire_u64 (writer, target);
	}
	r2sleigh_wire_u64 (writer, (uint64_t)view->total_source_bytes);
	return true;
}

static bool walk_presentation(R2SleighWireWriter *writer,
		const RAnalFunctionSnapshot *snapshot) {
	if (!walk_string (writer, r_anal_function_snapshot_function_name, snapshot)) {
		return false;
	}
	/* Presentation names exist only alongside an interface, and must match its
	 * parameter count exactly. Without one the list is absent, not empty-looking. */
	RAnalFunctionInterfaceSnapshotView interface = {0};
	if (!r_anal_function_snapshot_interface_view (snapshot, &interface)) {
		r2sleigh_wire_u32 (writer, 0);
		return true;
	}
	if (interface.num_parameters > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)interface.num_parameters);
	for (size_t i = 0; i < interface.num_parameters; i++) {
		char name[WALK_NAME_MAX];
		if (!r_anal_function_snapshot_parameter_name (snapshot, i, name, sizeof (name))) {
			return false;
		}
		r2sleigh_wire_string (writer, name);
	}
	return true;
}

bool r2sleigh_wire_write_snapshot_prefix(R2SleighWireWriter *writer, const void *snapshot) {
	if (!writer || !snapshot) {
		return false;
	}
	const RAnalFunctionSnapshot *source = snapshot;
	RAnalFunctionSnapshotView view = {0};
	if (!r_anal_function_snapshot_view (source, &view)) {
		return false;
	}
	if (!walk_machine_profile (writer, source, &view)) {
		return false;
	}
	r2sleigh_wire_u64 (writer, view.function_addr);
	if (!walk_presentation (writer, source)) {
		return false;
	}
	if (!walk_image (writer, source, &view)) {
		return false;
	}
	return r2sleigh_wire_writer_ok (writer);
}
