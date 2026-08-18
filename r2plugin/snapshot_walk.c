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
	/* The reference capture refuses a case value on any kind but a labelled
	 * case, so a stray one is a disagreement rather than something to drop. */
	if (kind != WALK_SUCCESSOR_SWITCH_CASE && view.case_value != 0) {
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
	/* Absence of a switch is UT64_MAX, not zero: zero is a legitimate address
	 * and treating the sentinel as present made every block claim a dispatch it
	 * does not have. A present address must also fall inside the block. */
	if (view.switch_addr == UT64_MAX) {
		r2sleigh_wire_bool (writer, false);
	} else {
		if (view.switch_addr < view.addr || view.switch_addr >= view.addr + view.size) {
			return false;
		}
		r2sleigh_wire_bool (writer, true);
		r2sleigh_wire_u64 (writer, view.switch_addr);
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
	RAnalFunctionSnapshotView top = {0};
	RAnalFunctionInterfaceSnapshotView interface = {0};
	if (!r_anal_function_snapshot_view (snapshot, &top)
		|| (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE) == 0
		|| !r_anal_function_snapshot_interface_view (snapshot, &interface)) {
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

/* Wire discriminants shared with r2source::snapshot_wire. */
#define WALK_SPACE_REGISTER 1
#define WALK_RESULT_VOID 0
#define WALK_RESULT_REGISTER 1
#define WALK_CARRIER_FULL 0
#define WALK_CARRIER_LOW_BITS 1
#define WALK_TYPE_SIGNED 0
#define WALK_TYPE_UNSIGNED 1
#define WALK_TYPE_POINTER 2
#define WALK_TYPE_STRUCT 3
#define WALK_BASE_FRAME_POINTER 0
#define WALK_BASE_STACK_POINTER 1
#define WALK_ROLE_UNCLASSIFIED 0
#define WALK_ROLE_LOCAL 1
#define WALK_ROLE_PARAMETER_HOME 2
#define WALK_GROWTH_LOWER 0
#define WALK_GROWTH_HIGHER 1
#define WALK_MECHANISM_STACKED 0

#define WALK_INTERFACE_PLAIN 0
#define WALK_INTERFACE_EXACT_SLOTS 1
#define WALK_INTERFACE_LOGICAL 2
#define WALK_INTERFACE_EXACT_BOTH 3

/* One bit per captured field, in the order r2source declares them. */
#define WALK_CAPTURED_BOUNDED_IMAGE (1u << 0)
#define WALK_CAPTURED_INTERFACE (1u << 1)
#define WALK_CAPTURED_EXACT_TYPES (1u << 2)
#define WALK_CAPTURED_EXACT_SLOT_ROLES (1u << 3)
#define WALK_CAPTURED_RETURN_ADDRESS (1u << 4)
#define WALK_CAPTURED_STACK_POINTER (1u << 5)
#define WALK_CAPTURED_FRAME_POINTER (1u << 6)
#define WALK_CAPTURED_RETURN_MECHANISM (1u << 7)
#define WALK_CAPTURED_STACK_ALLOCATION (1u << 8)

static void walk_storage(R2SleighWireWriter *writer,
		const RAnalSnapshotRegisterStorageView *storage) {
	/* Every storage a snapshot reports is a register; the wire's other spaces
	 * exist for values this transport never carries. */
	r2sleigh_wire_u8 (writer, WALK_SPACE_REGISTER);
	r2sleigh_wire_u64 (writer, storage->offset);
	r2sleigh_wire_u32 (writer, storage->size);
}

static void walk_optional_storage(R2SleighWireWriter *writer, bool present,
		const RAnalSnapshotRegisterStorageView *storage) {
	r2sleigh_wire_bool (writer, present);
	if (present) {
		walk_storage (writer, storage);
	}
}

static bool walk_carrier(R2SleighWireWriter *writer,
		const RAnalSnapshotCarrierProjection *carrier) {
	switch (carrier->kind) {
	case R_ANAL_SNAPSHOT_CARRIER_FULL:
		r2sleigh_wire_u8 (writer, WALK_CARRIER_FULL);
		break;
	case R_ANAL_SNAPSHOT_CARRIER_LOW_BITS:
		r2sleigh_wire_u8 (writer, WALK_CARRIER_LOW_BITS);
		break;
	default:
		/* The kind decides whether a value is the whole register or a
		 * truncation of it, so an invalid one is refused. */
		return false;
	}
	r2sleigh_wire_u64 (writer, carrier->offset_bits);
	r2sleigh_wire_u64 (writer, carrier->size_bits);
	return true;
}

static bool walk_result_kind(R2SleighWireWriter *writer, RAnalSnapshotReturnKind kind,
		const RAnalSnapshotRegisterStorageView *storage) {
	switch (kind) {
	case R_ANAL_SNAPSHOT_RETURN_VOID:
		r2sleigh_wire_u8 (writer, WALK_RESULT_VOID);
		return true;
	case R_ANAL_SNAPSHOT_RETURN_REGISTER:
		r2sleigh_wire_u8 (writer, WALK_RESULT_REGISTER);
		walk_storage (writer, storage);
		return true;
	default:
		/* UNKNOWN is not void: it means radare2 did not determine the result. */
		return false;
	}
}

static bool walk_call_site(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot,
		size_t index) {
	RAnalCallSiteInterfaceSnapshotView view = {0};
	if (!r_anal_function_snapshot_call_site_view (snapshot, index, &view)) {
		return false;
	}
	r2sleigh_wire_u64 (writer, view.instruction_addr);
	r2sleigh_wire_u64 (writer, view.target_addr);
	/* An incomplete site described the call but not what it takes or returns,
	 * which is a different fact from a call that takes nothing. */
	if (!view.complete) {
		r2sleigh_wire_bool (writer, false);
		return true;
	}
	r2sleigh_wire_bool (writer, true);
	char cc[WALK_NAME_MAX];
	if (!r_anal_function_snapshot_call_site_calling_convention (snapshot, index, cc,
			sizeof (cc))) {
		return false;
	}
	r2sleigh_wire_string (writer, cc);
	if (view.num_arguments > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)view.num_arguments);
	for (size_t i = 0; i < view.num_arguments; i++) {
		RAnalSnapshotParameterView argument = {0};
		if (!r_anal_function_snapshot_call_argument_view (snapshot, index, i, &argument)) {
			return false;
		}
		r2sleigh_wire_u32 (writer, argument.index);
		walk_storage (writer, &argument.storage);
	}
	r2sleigh_wire_bool (writer, view.variadic);
	r2sleigh_wire_bool (writer, view.noreturn);
	return walk_result_kind (writer, view.result_kind, &view.result_storage);
}

static bool walk_stack_slot(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot,
		size_t index) {
	RAnalSnapshotStackSlotView view = {0};
	if (!r_anal_function_snapshot_stack_slot_view (snapshot, index, &view)) {
		return false;
	}
	switch (view.base) {
	case R_ANAL_FCN_BASE_BP:
		r2sleigh_wire_u8 (writer, WALK_BASE_FRAME_POINTER);
		break;
	case R_ANAL_FCN_BASE_SP:
		r2sleigh_wire_u8 (writer, WALK_BASE_STACK_POINTER);
		break;
	default:
		/* A named base has no wire counterpart, and coercing it to SP would
		 * place the slot against a register it is not measured from. */
		return false;
	}
	RAnalSnapshotRegisterStorageView base_storage = {
		.name_length = view.base_name_length,
		.offset = view.base_offset,
		.size = view.base_size,
	};
	walk_storage (writer, &base_storage);
	if (!view.offset_valid) {
		return false;
	}
	r2sleigh_wire_i64 (writer, view.offset);
	r2sleigh_wire_u32 (writer, view.size);
	switch (view.role) {
	case R_ANAL_FCN_SLOT_LOCAL:
		r2sleigh_wire_u8 (writer, WALK_ROLE_LOCAL);
		break;
	case R_ANAL_FCN_SLOT_HOME:
		if (view.arg_index < 0) {
			return false;
		}
		r2sleigh_wire_u8 (writer, WALK_ROLE_PARAMETER_HOME);
		r2sleigh_wire_u32 (writer, (uint32_t)view.arg_index);
		RAnalSnapshotRegisterStorageView home = {
			.name_length = view.home_reg_length,
			.offset = view.home_reg_offset,
			.size = view.home_reg_size,
		};
		walk_storage (writer, &home);
		break;
	default:
		/* ARG and UNKNOWN carry no home authority, so both stay
		 * unclassified rather than being promoted to a parameter home. */
		r2sleigh_wire_u8 (writer, WALK_ROLE_UNCLASSIFIED);
		break;
	}
	return true;
}

static bool walk_type_graph(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot) {
	RAnalSnapshotTypeGraphView graph = {0};
	if (!r_anal_function_snapshot_type_graph_view (snapshot, &graph) || !graph.complete) {
		return false;
	}
	if (graph.num_types == 0 || graph.num_types > UINT32_MAX
		|| graph.num_aggregates > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)graph.num_types);
	for (size_t i = 0; i < graph.num_types; i++) {
		RAnalSnapshotType type = {0};
		if (!r_anal_function_snapshot_type_view (snapshot, i, &type)) {
			return false;
		}
		r2sleigh_wire_u32 (writer, type.id);
		switch (type.kind) {
		case R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER:
			r2sleigh_wire_u8 (writer, WALK_TYPE_SIGNED);
			break;
		case R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER:
			r2sleigh_wire_u8 (writer, WALK_TYPE_UNSIGNED);
			break;
		case R_ANAL_SNAPSHOT_TYPE_POINTER:
			r2sleigh_wire_u8 (writer, WALK_TYPE_POINTER);
			r2sleigh_wire_u32 (writer, type.target_type_id);
			break;
		case R_ANAL_SNAPSHOT_TYPE_STRUCT:
			r2sleigh_wire_u8 (writer, WALK_TYPE_STRUCT);
			r2sleigh_wire_u32 (writer, type.aggregate_id);
			break;
		default:
			/* Signedness and indirection are not recoverable elsewhere. */
			return false;
		}
		r2sleigh_wire_u64 (writer, type.size_bits);
		r2sleigh_wire_u64 (writer, type.align_bits);
	}
	r2sleigh_wire_u32 (writer, (uint32_t)graph.num_aggregates);
	for (size_t i = 0; i < graph.num_aggregates; i++) {
		RAnalSnapshotAggregateLayoutView aggregate = {0};
		if (!r_anal_function_snapshot_aggregate_view (snapshot, i, &aggregate)
			|| !aggregate.complete) {
			return false;
		}
		r2sleigh_wire_u32 (writer, aggregate.id);
		r2sleigh_wire_u32 (writer, aggregate.type_id);
		r2sleigh_wire_u64 (writer, aggregate.size_bits);
		r2sleigh_wire_u64 (writer, aggregate.align_bits);
		char name[WALK_NAME_MAX];
		if (!r_anal_function_snapshot_aggregate_name (snapshot, i, name, sizeof (name))) {
			return false;
		}
		r2sleigh_wire_string (writer, name);
		if (aggregate.num_members > UINT32_MAX) {
			return false;
		}
		r2sleigh_wire_u32 (writer, (uint32_t)aggregate.num_members);
		for (size_t member = 0; member < aggregate.num_members; member++) {
			RAnalSnapshotAggregateMemberView view = {0};
			if (!r_anal_function_snapshot_aggregate_member_view (snapshot, i, member,
					&view)) {
				return false;
			}
			r2sleigh_wire_u32 (writer, view.member_id);
			r2sleigh_wire_u32 (writer, view.type_id);
			r2sleigh_wire_u64 (writer, view.offset_bits);
			r2sleigh_wire_u64 (writer, view.size_bits);
			char member_name[WALK_NAME_MAX];
			if (!r_anal_function_snapshot_aggregate_member_name (snapshot, i, member,
					member_name, sizeof (member_name))) {
				return false;
			}
			r2sleigh_wire_string (writer, member_name);
		}
	}
	return true;
}

static bool walk_interface(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot,
		const RAnalFunctionSnapshotView *top, const RAnalFunctionInterfaceSnapshotView *view) {
	const bool exact_types = (top->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES) != 0;
	const bool exact_slots = (top->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES) != 0;
	uint8_t variant = WALK_INTERFACE_PLAIN;
	if (exact_types && exact_slots) {
		variant = WALK_INTERFACE_EXACT_BOTH;
	} else if (exact_types) {
		variant = WALK_INTERFACE_LOGICAL;
	} else if (exact_slots) {
		variant = WALK_INTERFACE_EXACT_SLOTS;
	}
	r2sleigh_wire_u8 (writer, variant);

	const uint64_t revision = top->revision_identity;
	uint8_t revision_bytes[8];
	for (unsigned i = 0; i < 8; i++) {
		revision_bytes[i] = (uint8_t)((revision >> (8 * i)) & 0xff);
	}
	r2sleigh_wire_bytes (writer, revision_bytes, sizeof (revision_bytes));

	char cc[WALK_NAME_MAX];
	if (!r_anal_function_snapshot_interface_calling_convention (snapshot, cc, sizeof (cc))) {
		return false;
	}
	r2sleigh_wire_string (writer, cc);

	if (view->num_parameters > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)view->num_parameters);
	for (size_t i = 0; i < view->num_parameters; i++) {
		RAnalSnapshotParameterView parameter = {0};
		if (!r_anal_function_snapshot_parameter_view (snapshot, i, &parameter)) {
			return false;
		}
		r2sleigh_wire_u32 (writer, parameter.index);
		walk_storage (writer, &parameter.storage);
	}
	if (!walk_result_kind (writer, view->return_kind, &view->return_storage)) {
		return false;
	}

	const bool has_slots = (top->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_SLOTS) != 0;
	const size_t num_slots = has_slots? top->num_stack_slots: 0;
	if (num_slots > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)num_slots);
	for (size_t i = 0; i < num_slots; i++) {
		if (!walk_stack_slot (writer, snapshot, i)) {
			return false;
		}
	}

	/* Logical values and the type graph travel together: without exact types
	 * there are no logical values to describe. */
	if (exact_types) {
		r2sleigh_wire_u32 (writer, (uint32_t)view->num_parameters);
		for (size_t i = 0; i < view->num_parameters; i++) {
			RAnalSnapshotParameterView parameter = {0};
			if (!r_anal_function_snapshot_parameter_view (snapshot, i, &parameter)) {
				return false;
			}
			r2sleigh_wire_u32 (writer, parameter.logical_type_id);
			if (!walk_carrier (writer, &parameter.carrier)) {
				return false;
			}
		}
		if (view->return_kind == R_ANAL_SNAPSHOT_RETURN_REGISTER) {
			r2sleigh_wire_bool (writer, true);
			r2sleigh_wire_u32 (writer, view->return_type_id);
			if (!walk_carrier (writer, &view->return_carrier)) {
				return false;
			}
		} else {
			r2sleigh_wire_bool (writer, false);
		}
		r2sleigh_wire_bool (writer, true);
		if (!walk_type_graph (writer, snapshot)) {
			return false;
		}
	} else {
		r2sleigh_wire_u32 (writer, 0);
		r2sleigh_wire_bool (writer, false);
		r2sleigh_wire_bool (writer, false);
	}

	r2sleigh_wire_bool (writer, view->stack_pointer_preserved_across_calls);
	r2sleigh_wire_bool (writer, view->frame_pointer_preserved_across_calls);

	const bool has_return_address = (top->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE) != 0;
	const bool has_stack_pointer = (top->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE) != 0;
	walk_optional_storage (writer, has_return_address, &view->return_address_storage);
	walk_optional_storage (writer, has_stack_pointer, &view->stack_pointer_storage);

	RAnalSnapshotRegisterStorageView frame = {0};
	const bool has_frame = (top->capabilities
			& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE) != 0
		&& r_anal_function_snapshot_interface_frame_pointer_storage (snapshot, &frame);
	walk_optional_storage (writer, has_frame, &frame);

	if (top->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM) {
		RAnalSnapshotReturnMechanismView mechanism = {0};
		if (!r_anal_function_snapshot_interface_return_mechanism (snapshot, &mechanism)
			|| mechanism.kind != R_ANAL_SNAPSHOT_RETURN_MECHANISM_STACK) {
			return false;
		}
		/* The address width is not in the view: it follows the machine, the
		 * same way the accessor transport derives it. */
		if (top->bits <= 0 || top->bits % 8 != 0) {
			return false;
		}
		r2sleigh_wire_bool (writer, true);
		r2sleigh_wire_u8 (writer, WALK_MECHANISM_STACKED);
		r2sleigh_wire_i64 (writer, mechanism.entry_sp_offset);
		r2sleigh_wire_u32 (writer, mechanism.slot_size);
		if (mechanism.exit_sp_delta < 0) {
			return false;
		}
		r2sleigh_wire_u32 (writer, (uint32_t)mechanism.exit_sp_delta);
		r2sleigh_wire_u32 (writer, (uint32_t)(top->bits / 8));
	} else {
		r2sleigh_wire_bool (writer, false);
	}

	if (top->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT) {
		RAnalSnapshotStackAllocationContractView contract = {0};
		if (!r_anal_function_snapshot_interface_stack_allocation_contract (snapshot,
				&contract)) {
			return false;
		}
		r2sleigh_wire_bool (writer, true);
		switch (contract.growth) {
		case R_ANAL_SNAPSHOT_STACK_GROWTH_LOWER:
			r2sleigh_wire_u8 (writer, WALK_GROWTH_LOWER);
			break;
		case R_ANAL_SNAPSHOT_STACK_GROWTH_HIGHER:
			r2sleigh_wire_u8 (writer, WALK_GROWTH_HIGHER);
			break;
		default:
			/* NONE means no contract, not a third direction. */
			return false;
		}
		r2sleigh_wire_u32 (writer, contract.implicit_active_sp_bytes);
	} else {
		r2sleigh_wire_bool (writer, false);
	}
	return true;
}

bool r2sleigh_wire_write_snapshot(R2SleighWireWriter *writer, const void *snapshot) {
	if (!r2sleigh_wire_write_snapshot_prefix (writer, snapshot)) {
		return false;
	}
	const RAnalFunctionSnapshot *source = snapshot;
	RAnalFunctionSnapshotView top = {0};
	if (!r_anal_function_snapshot_view (source, &top)) {
		return false;
	}
	const bool has_calls = (top.capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_CALL_SITE_INTERFACES) != 0;
	const size_t num_calls = has_calls? top.num_call_site_interfaces: 0;
	if (num_calls > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)num_calls);
	for (size_t i = 0; i < num_calls; i++) {
		if (!walk_call_site (writer, source, i)) {
			return false;
		}
	}

	/* The revision identity must be present: it is what binds every part of
	 * this buffer to one capture. */
	if (top.revision_identity == 0) {
		return false;
	}
	uint8_t revision_bytes[8];
	for (unsigned i = 0; i < 8; i++) {
		revision_bytes[i] = (uint8_t)((top.revision_identity >> (8 * i)) & 0xff);
	}
	r2sleigh_wire_bytes (writer, revision_bytes, sizeof (revision_bytes));

	/* An interface exists only when radare2 minted exact-interface authority.
	 * The view answering is not enough: a thunk has a readable view that carries
	 * no recovered prototype, and treating it as one refuses the whole
	 * snapshot over a return kind radare2 never determined. */
	RAnalFunctionInterfaceSnapshotView interface = {0};
	const bool has_interface = (top.capabilities
			& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE) != 0
		&& r_anal_function_snapshot_interface_view (source, &interface);
	r2sleigh_wire_bool (writer, has_interface);
	if (has_interface && !walk_interface (writer, source, &top, &interface)) {
		return false;
	}

	/* Machine roles repeat the return-address and stack-pointer carriers the
	 * interface names, so a consumer without an interface still knows them. */
	const bool has_return_address = (top.capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE) != 0;
	const bool has_stack_pointer = (top.capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE) != 0;
	/* The machine carriers are collected independently of any recovered
	 * prototype, so they are reported whenever radare2 resolved them. Gating
	 * them on an exact interface withheld the carriers from exactly the
	 * functions that have no interface and most need them. */
	RAnalFunctionInterfaceSnapshotView carriers = {0};
	const bool carriers_read = r_anal_function_snapshot_interface_view (source, &carriers);
	walk_optional_storage (writer, carriers_read && has_return_address,
		&carriers.return_address_storage);
	walk_optional_storage (writer, carriers_read && has_stack_pointer,
		&carriers.stack_pointer_storage);

	/* The convention's candidate slots describe where a caller would leave
	 * arguments and the result. They are emitted whether or not a prototype was
	 * recovered, because a consumer recovering parameters from machine code has
	 * nothing to intersect against without them. */
	RAnalFunctionInterfaceSnapshotView convention = {0};
	const bool slots_known = r_anal_function_snapshot_interface_view (source, &convention)
		&& convention.convention_slots_known;
	const size_t num_slots = slots_known? convention.num_convention_argument_slots: 0;
	if (num_slots > UINT32_MAX) {
		return false;
	}
	char convention_name[WALK_NAME_MAX] = {0};
	if (slots_known
		&& !r_anal_function_snapshot_interface_calling_convention (source, convention_name,
			sizeof (convention_name))) {
		return false;
	}
	r2sleigh_wire_string (writer, convention_name);
	r2sleigh_wire_u32 (writer, (uint32_t)num_slots);
	for (size_t i = 0; i < num_slots; i++) {
		RAnalSnapshotRegisterStorageView slot = {0};
		if (!r_anal_function_snapshot_convention_argument_slot (source, i, &slot)) {
			return false;
		}
		walk_storage (writer, &slot);
	}
	walk_optional_storage (writer, slots_known && convention.convention_result_slot.size != 0,
		&convention.convention_result_slot);

	uint16_t captured = 0;
	if (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_OWNED_BOUNDED_FUNCTION_IMAGE) {
		captured |= WALK_CAPTURED_BOUNDED_IMAGE;
	}
	if (has_interface) {
		captured |= WALK_CAPTURED_INTERFACE;
	}
	/* Every remaining flag describes something the interface carries, so with
	 * no interface there is nothing to have captured. Deriving them from the
	 * capabilities alone claimed storages that no part of the buffer holds. */
	if (has_interface) {
		if (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES) {
			captured |= WALK_CAPTURED_EXACT_TYPES;
		}
		if (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES) {
			captured |= WALK_CAPTURED_EXACT_SLOT_ROLES;
		}
		if (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE) {
			captured |= WALK_CAPTURED_RETURN_ADDRESS;
		}
		if (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE) {
			captured |= WALK_CAPTURED_STACK_POINTER;
		}
		if (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE) {
			captured |= WALK_CAPTURED_FRAME_POINTER;
		}
		if (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM) {
			captured |= WALK_CAPTURED_RETURN_MECHANISM;
		}
		if (top.capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT) {
			captured |= WALK_CAPTURED_STACK_ALLOCATION;
		}
	}
	r2sleigh_wire_u16 (writer, captured);

	/* Diagnostics carry the same capture identity, matching the accessor
	 * transport's own choice rather than inventing a second one. */
	r2sleigh_wire_u64 (writer, top.revision_identity);
	return r2sleigh_wire_writer_ok (writer);
}
