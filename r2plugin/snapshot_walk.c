/* Serializes an owned radare2 function snapshot into the flat wire format.
 *
 * radare2 used to publish the snapshot as an opaque handle behind an accessor
 * per field, and this file called them. It now publishes the struct itself, so
 * the reads below are field reads. Nothing about the wire format changed: the
 * same values are written in the same order, including where the old accessors
 * had a contract worth preserving rather than tidying.
 *
 * The one such contract is string absence. Every accessor copied through
 * r_str_get, so a NULL string arrived as an empty one and returned success;
 * only a string too long for the caller's buffer was a refusal. walk_bounded
 * keeps exactly that distinction, because the reader asserts this format byte
 * for byte and would notice an absent string that used to be an empty one.
 *
 * Field order must match r2source::snapshot_wire::encode_snapshot exactly. That
 * order is asserted by decoding what this writes, so a mismatch fails a test
 * rather than producing a buffer the parser silently misreads. */

#include "snapshot_wire.h"

#include <r_anal.h>
/* The walker reads the snapshot's fields rather than calling an accessor per
 * field, so it needs the struct itself. It comes from the capture that now
 * lives here, on the plugin's side of the boundary. */
#include "snapshot_capture.h"

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

/* An absent string is an empty one; an over-long string is a refusal. */
static const char *walk_bounded(const char *string) {
	const char *text = r_str_get (string);
	return strlen (text) < WALK_NAME_MAX? text: NULL;
}

static bool walk_string(R2SleighWireWriter *writer, const char *string) {
	const char *text = walk_bounded (string);
	if (!text) {
		return false;
	}
	r2sleigh_wire_string (writer, text);
	return true;
}

static size_t walk_num_stack_slots(const RAnalFunctionSnapshot *snapshot) {
	return snapshot->context.fcn_slots
		? (size_t)r_list_length (snapshot->context.fcn_slots): 0;
}

static const RAnalFcnSlot *walk_stack_slot_at(const RAnalFunctionSnapshot *snapshot,
		size_t index) {
	if (!snapshot->context.fcn_slots || index > INT_MAX
		|| index >= (size_t)r_list_length (snapshot->context.fcn_slots)) {
		return NULL;
	}
	return r_list_get_n (snapshot->context.fcn_slots, (int)index);
}

static bool walk_machine_profile(R2SleighWireWriter *writer,
		const RAnalFunctionSnapshot *snapshot) {
	if (!walk_string (writer, snapshot->arch_id)
		|| !walk_string (writer, snapshot->cpu_id)) {
		return false;
	}
	if (snapshot->bits < 0) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)snapshot->bits);
	switch (snapshot->endian) {
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

static bool walk_successor(R2SleighWireWriter *writer,
		const RAnalSnapshotSuccessor *successor) {
	uint8_t kind;
	switch (successor->kind) {
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
	if (kind != WALK_SUCCESSOR_SWITCH_CASE && successor->case_value != 0) {
		return false;
	}
	r2sleigh_wire_u8 (writer, kind);
	r2sleigh_wire_u64 (writer, successor->target_addr);
	/* A case value belongs to a labelled case and to nothing else, so presence
	 * follows the kind rather than being reported separately. */
	if (kind == WALK_SUCCESSOR_SWITCH_CASE) {
		r2sleigh_wire_bool (writer, true);
		r2sleigh_wire_u64 (writer, successor->case_value);
	} else {
		r2sleigh_wire_bool (writer, false);
	}
	r2sleigh_wire_bool (writer, successor->external? true: false);
	return true;
}

static bool walk_block(R2SleighWireWriter *writer, const RAnalSnapshotBlock *block) {
	r2sleigh_wire_u64 (writer, block->addr);
	if (block->size == 0 || block->size > WALK_BLOCK_BYTES_MAX || !block->bytes) {
		return false;
	}
	/* The snapshot owns these bytes, so they are written from where they sit. */
	r2sleigh_wire_bytes (writer, block->bytes, (size_t)block->size);
	if (block->num_successors > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)block->num_successors);
	for (size_t i = 0; i < block->num_successors; i++) {
		if (!walk_successor (writer, &block->successors[i])) {
			return false;
		}
	}
	/* Absence of a switch is UT64_MAX, not zero: zero is a legitimate address
	 * and treating the sentinel as present made every block claim a dispatch it
	 * does not have. A present address must also fall inside the block. */
	if (block->switch_addr == UT64_MAX) {
		r2sleigh_wire_bool (writer, false);
	} else {
		if (block->switch_addr < block->addr
			|| block->switch_addr >= block->addr + block->size) {
			return false;
		}
		r2sleigh_wire_bool (writer, true);
		r2sleigh_wire_u64 (writer, block->switch_addr);
	}
	return true;
}

static bool walk_image(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot) {
	const RAnalFunctionImageSnapshot *image = &snapshot->image;
	r2sleigh_wire_u64 (writer, snapshot->function_addr);
	if (image->num_blocks == 0 || image->num_blocks > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)image->num_blocks);
	for (size_t i = 0; i < image->num_blocks; i++) {
		if (!walk_block (writer, &image->blocks[i])) {
			return false;
		}
	}
	if (image->num_external_exits > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)image->num_external_exits);
	for (size_t i = 0; i < image->num_external_exits; i++) {
		r2sleigh_wire_u64 (writer, image->external_exits[i]);
	}
	if (image->num_string_literals > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)image->num_string_literals);
	for (size_t i = 0; i < image->num_string_literals; i++) {
		const RAnalSnapshotStringLiteral *literal = &image->string_literals[i];
		const char *text = walk_bounded (literal->text);
		if (!text) {
			return false;
		}
		r2sleigh_wire_u64 (writer, literal->addr);
		r2sleigh_wire_string (writer, text);
	}
	if (image->num_data_symbols > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)image->num_data_symbols);
	for (size_t i = 0; i < image->num_data_symbols; i++) {
		const RAnalSnapshotDataSymbol *symbol = &image->data_symbols[i];
		const char *name = walk_bounded (symbol->name);
		if (!name) {
			return false;
		}
		r2sleigh_wire_u64 (writer, symbol->addr);
		r2sleigh_wire_string (writer, name);
		/* Absent and empty are different facts about a symbol's type, so
		 * the optional form carries NULL through rather than "". */
		r2sleigh_wire_optional_string (writer, symbol->type_name);
	}
	if (image->num_code_pointer_tables > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)image->num_code_pointer_tables);
	for (size_t i = 0; i < image->num_code_pointer_tables; i++) {
		const RAnalSnapshotCodePointerTable *table = &image->code_pointer_tables[i];
		if (table->num_targets > UINT32_MAX) {
			return false;
		}
		r2sleigh_wire_u64 (writer, table->addr);
		r2sleigh_wire_u32 (writer, table->entry_size);
		r2sleigh_wire_u32 (writer, (uint32_t)table->num_targets);
		for (size_t t = 0; t < table->num_targets; t++) {
			r2sleigh_wire_u64 (writer, table->targets[t]);
		}
	}
	r2sleigh_wire_u64 (writer, (uint64_t)image->total_source_bytes);
	return true;
}

#define WALK_BASE_FRAME_POINTER 0
#define WALK_BASE_STACK_POINTER 1

// The prototype radare2 recovered, which is the only place a spelling like
// size_t survives; the interface carries where values live, not what they are.
static bool walk_signature_body(R2SleighWireWriter *writer,
		const RAnalFunctionSignature *signature) {
	const size_t num_parameters = signature->params
		? (size_t)r_list_length (signature->params): 0;
	if (num_parameters > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_bool (writer, true);
	r2sleigh_wire_optional_string (writer, walk_bounded (signature->ret_type));
	r2sleigh_wire_optional_string (writer, walk_bounded (signature->callconv));
	r2sleigh_wire_bool (writer, signature->noreturn);
	r2sleigh_wire_u32 (writer, (uint32_t)num_parameters);
	for (size_t i = 0; i < num_parameters; i++) {
		const RAnalFunctionParam *param = r_list_get_n (signature->params, (int)i);
		r2sleigh_wire_optional_string (writer, param? walk_bounded (param->name): NULL);
		r2sleigh_wire_optional_string (writer, param? walk_bounded (param->type): NULL);
	}
	return true;
}

static const RAnalFunctionSignature *walk_own_signature(
		const RAnalFunctionSnapshot *snapshot) {
	if (!(snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_SIGNATURE)) {
		return NULL;
	}
	return snapshot->context.signature;
}

/* A call site names a callee; the prototype belongs to the callee record the
 * context carries, matched on the pair of addresses the site was collected at. */
static const RAnalFunctionSignature *walk_call_site_signature(
		const RAnalFunctionSnapshot *snapshot, size_t index) {
	if (index >= snapshot->num_call_site_interfaces || !snapshot->context.callees) {
		return NULL;
	}
	const RAnalCallSiteInterfaceSnapshot *call = &snapshot->call_site_interfaces[index];
	RListIter *iter;
	RAnalFcnCallee *callee;
	r_list_foreach (snapshot->context.callees, iter, callee) {
		if (callee && callee->call_addr == call->instruction_addr
			&& callee->addr == call->target_addr) {
			return callee->signature;
		}
	}
	return NULL;
}

static bool walk_signature(R2SleighWireWriter *writer,
		const RAnalFunctionSnapshot *snapshot) {
	const RAnalFunctionSignature *signature = walk_own_signature (snapshot);
	if (!signature) {
		r2sleigh_wire_bool (writer, false);
		return true;
	}
	return walk_signature_body (writer, signature);
}

/* The prototype of each function this one calls, keyed by the name the call
 * renders with. A callee named twice is written once: the prototype belongs to
 * the callee, not to the site. */
static bool walk_callee_signatures(R2SleighWireWriter *writer,
		const RAnalFunctionSnapshot *snapshot) {
	size_t written = 0;
	for (size_t pass = 0; pass < 2; pass++) {
		if (pass == 1) {
			if (written > UINT32_MAX) {
				return false;
			}
			r2sleigh_wire_u32 (writer, (uint32_t)written);
			written = 0;
		}
		for (size_t i = 0; i < snapshot->num_call_site_interfaces; i++) {
			const RAnalFunctionSignature *signature = walk_call_site_signature (snapshot, i);
			const char *name = walk_bounded (
				snapshot->call_site_interfaces[i].target_name);
			if (!signature || !name || !*name) {
				continue;
			}
			bool seen = false;
			for (size_t j = 0; j < i && !seen; j++) {
				const char *earlier = walk_bounded (
					snapshot->call_site_interfaces[j].target_name);
				seen = earlier && !strcmp (earlier, name);
			}
			if (seen) {
				continue;
			}
			if (pass == 0) {
				written++;
				continue;
			}
			r2sleigh_wire_string (writer, name);
			if (!walk_signature_body (writer, signature)) {
				return false;
			}
			written++;
		}
	}
	return true;
}

// a named base has no wire counterpart, so a slot measured from one is skipped
static bool walk_stack_slot_base_tag(int base, uint8_t *out) {
	switch (base) {
	case R_ANAL_FCN_BASE_BP:
		if (out) {
			*out = WALK_BASE_FRAME_POINTER;
		}
		return true;
	case R_ANAL_FCN_BASE_SP:
		if (out) {
			*out = WALK_BASE_STACK_POINTER;
		}
		return true;
	default:
		return false;
	}
}

static bool walk_presentation(R2SleighWireWriter *writer,
		const RAnalFunctionSnapshot *snapshot) {
	if (!walk_string (writer, snapshot->function_name)) {
		return false;
	}
	/* Presentation names exist only alongside an interface, and must match its
	 * parameter count exactly. Without one the list is absent, not empty-looking. */
	const RAnalFunctionInterfaceSnapshot *interface = &snapshot->function_interface;
	if ((snapshot->capabilities
			& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE) == 0) {
		r2sleigh_wire_u32 (writer, 0);
		r2sleigh_wire_u32 (writer, 0);
		if (!walk_signature (writer, snapshot)) {
			return false;
		}
		return walk_callee_signatures (writer, snapshot);
	}
	if (interface->num_parameters > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)interface->num_parameters);
	for (size_t i = 0; i < interface->num_parameters; i++) {
		if (!walk_string (writer, interface->parameters[i].name)) {
			return false;
		}
	}
	/* A slot the source named is keyed by where it sits, because the interface
	 * sorts its inventory and a position here would name the wrong slot. */
	const size_t num_stack_slots = walk_num_stack_slots (snapshot);
	size_t named = 0;
	for (size_t i = 0; i < num_stack_slots; i++) {
		const RAnalFcnSlot *slot = walk_stack_slot_at (snapshot, i);
		if (!slot) {
			return false;
		}
		if (!slot->offset_valid || !walk_stack_slot_base_tag (slot->base, NULL)) {
			continue;
		}
		const char *name = walk_bounded (slot->name);
		if (!name || !*name) {
			continue;
		}
		named++;
	}
	if (named > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)named);
	for (size_t i = 0; i < num_stack_slots; i++) {
		const RAnalFcnSlot *slot = walk_stack_slot_at (snapshot, i);
		uint8_t base_tag = 0;
		if (!slot) {
			return false;
		}
		if (!slot->offset_valid || !walk_stack_slot_base_tag (slot->base, &base_tag)) {
			continue;
		}
		const char *name = walk_bounded (slot->name);
		if (!name || !*name) {
			continue;
		}
		const char *type = walk_bounded (slot->type);
		r2sleigh_wire_u8 (writer, base_tag);
		r2sleigh_wire_i64 (writer, slot->offset);
		r2sleigh_wire_string (writer, name);
		r2sleigh_wire_optional_string (writer, type && *type? type: NULL);
	}
	if (!walk_signature (writer, snapshot)) {
		return false;
	}
	return walk_callee_signatures (writer, snapshot);
}

bool r2sleigh_wire_write_snapshot_prefix(R2SleighWireWriter *writer, const void *snapshot) {
	if (!writer || !snapshot) {
		return false;
	}
	const RAnalFunctionSnapshot *source = snapshot;
	if (!walk_machine_profile (writer, source)) {
		return false;
	}
	r2sleigh_wire_u64 (writer, source->function_addr);
	if (!walk_presentation (writer, source)) {
		return false;
	}
	if (!walk_image (writer, source)) {
		return false;
	}
	return r2sleigh_wire_writer_ok (writer);
}

/* Wire discriminants shared with r2source::snapshot_wire. */
#define WALK_SPACE_REGISTER 1
#define WALK_CALL_TRANSFER_CALL 0
#define WALK_CALL_TRANSFER_TAIL_JUMP 1
#define WALK_CALL_TRANSFER_TAIL_SLOT 2
#define WALK_RESULT_VOID 0
#define WALK_RESULT_REGISTER 1
#define WALK_CARRIER_FULL 0
#define WALK_CARRIER_LOW_BITS 1
#define WALK_TYPE_SIGNED 0
#define WALK_TYPE_UNSIGNED 1
#define WALK_TYPE_POINTER 2
#define WALK_TYPE_STRUCT 3
#define WALK_TYPE_VOID 4
#define WALK_TYPE_CODE 5
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
		const RAnalSnapshotRegisterStorage *storage) {
	/* Every storage a snapshot reports is a register; the wire's other spaces
	 * exist for values this transport never carries. */
	r2sleigh_wire_u8 (writer, WALK_SPACE_REGISTER);
	r2sleigh_wire_u64 (writer, storage->offset);
	r2sleigh_wire_u32 (writer, storage->size);
}

static void walk_optional_storage(R2SleighWireWriter *writer, bool present,
		const RAnalSnapshotRegisterStorage *storage) {
	r2sleigh_wire_bool (writer, present);
	if (present) {
		walk_storage (writer, storage);
	}
}

/* A role carrier is written with the register's name beside its storage.
 * radare2 reports the offset into its own register arena, which has nothing to
 * do with the offset the Sleigh architecture gives the same register, so the
 * name is what the consumer resolves; the offset alone would name a different
 * register or none at all. An empty name is written when radare2 cannot spell
 * the register, and the consumer treats that as no carrier rather than as a
 * carrier at a wrong offset. */
static void walk_named_optional_storage(R2SleighWireWriter *writer, bool present,
		const RAnalSnapshotRegisterStorage *storage) {
	r2sleigh_wire_bool (writer, present);
	if (!present) {
		return;
	}
	walk_storage (writer, storage);
	const char *name = walk_bounded (storage->name);
	r2sleigh_wire_string (writer, name? name: "");
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
		const RAnalSnapshotRegisterStorage *storage) {
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

static bool walk_call_site(R2SleighWireWriter *writer,
		const RAnalCallSiteInterfaceSnapshot *call) {
	r2sleigh_wire_u64 (writer, call->instruction_addr);
	r2sleigh_wire_u64 (writer, call->target_addr);
	/* Written before the completeness branch: a site radare2 could not give a
	 * prototype for still has a target, and the target still has a name. */
	if (!walk_string (writer, call->target_name)) {
		return false;
	}
	/* How control gets there. A jump that leaves the function for another
	 * one is a call whose return is this function's, and a jump through a
	 * relocated slot is the same with the slot standing for the callee; the
	 * consumer has to see the difference to match the site to the machine. */
	switch (call->transfer) {
	case R_ANAL_CALL_TRANSFER_CALL:
		r2sleigh_wire_u8 (writer, WALK_CALL_TRANSFER_CALL);
		break;
	case R_ANAL_CALL_TRANSFER_TAIL_JUMP:
		r2sleigh_wire_u8 (writer, WALK_CALL_TRANSFER_TAIL_JUMP);
		break;
	case R_ANAL_CALL_TRANSFER_TAIL_SLOT:
		r2sleigh_wire_u8 (writer, WALK_CALL_TRANSFER_TAIL_SLOT);
		break;
	default:
		/* A transfer this side cannot name is one the consumer would
		 * misread as a call. */
		return false;
	}
	/* An incomplete site described the call but not what it takes or returns,
	 * which is a different fact from a call that takes nothing. */
	if (!call->complete) {
		r2sleigh_wire_bool (writer, false);
		return true;
	}
	r2sleigh_wire_bool (writer, true);
	if (!walk_string (writer, call->calling_convention)) {
		return false;
	}
	if (call->num_arguments > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)call->num_arguments);
	for (size_t i = 0; i < call->num_arguments; i++) {
		const RAnalSnapshotParameter *argument = &call->arguments[i];
		r2sleigh_wire_u32 (writer, argument->index);
		walk_storage (writer, &argument->storage);
	}
	r2sleigh_wire_bool (writer, call->variadic);
	r2sleigh_wire_bool (writer, call->noreturn);
	return walk_result_kind (writer, call->result_kind, &call->result_storage);
}

static bool walk_stack_slot(R2SleighWireWriter *writer, const RAnalFcnSlot *slot, bool exact_types) {
	uint8_t base_tag = 0;
	if (!walk_stack_slot_base_tag (slot->base, &base_tag)) {
		return false;
	}
	r2sleigh_wire_u8 (writer, base_tag);
	const RAnalSnapshotRegisterStorage base_storage = {
		.name = slot->base_name,
		.offset = slot->base_offset,
		.size = slot->base_size,
	};
	walk_storage (writer, &base_storage);
	if (!slot->offset_valid) {
		return false;
	}
	r2sleigh_wire_i64 (writer, slot->offset);
	r2sleigh_wire_u32 (writer, slot->size);
	switch (slot->role) {
	case R_ANAL_FCN_SLOT_LOCAL:
		r2sleigh_wire_u8 (writer, WALK_ROLE_LOCAL);
		break;
	case R_ANAL_FCN_SLOT_HOME:
		if (slot->arg_index < 0) {
			return false;
		}
		r2sleigh_wire_u8 (writer, WALK_ROLE_PARAMETER_HOME);
		r2sleigh_wire_u32 (writer, (uint32_t)slot->arg_index);
		const RAnalSnapshotRegisterStorage home = {
			.name = slot->home_reg,
			.offset = slot->home_reg_offset,
			.size = slot->home_reg_size,
		};
		walk_storage (writer, &home);
		break;
	default:
		/* ARG and UNKNOWN carry no home authority, so both stay
		 * unclassified rather than being promoted to a parameter home. */
		r2sleigh_wire_u8 (writer, WALK_ROLE_UNCLASSIFIED);
		break;
	}
	/* The slot's node in the type graph travels only with the graph: without
	 * exact types there is no graph for the id to index. */
	r2sleigh_wire_u32 (writer, exact_types
		? slot->logical_type_id: R_ANAL_SNAPSHOT_TYPE_ID_INVALID);
	return true;
}

static bool walk_type_graph(R2SleighWireWriter *writer, const RAnalFunctionSnapshot *snapshot) {
	const RAnalSnapshotTypeGraph *graph = &snapshot->type_graph;
	if (!graph->complete) {
		return false;
	}
	/* A function that mentions no type has an empty type graph, and that is a
	 * complete description of what it uses rather than a missing one. Refusing
	 * here rejected the whole snapshot, so a function as small as a lone `ret`
	 * could not be decompiled at all. */
	if (graph->num_types > UINT32_MAX || graph->num_aggregates > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)graph->num_types);
	for (size_t i = 0; i < graph->num_types; i++) {
		const RAnalSnapshotType *type = &graph->types[i];
		r2sleigh_wire_u32 (writer, type->id);
		switch (type->kind) {
		case R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER:
			r2sleigh_wire_u8 (writer, WALK_TYPE_SIGNED);
			break;
		case R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER:
			r2sleigh_wire_u8 (writer, WALK_TYPE_UNSIGNED);
			break;
		case R_ANAL_SNAPSHOT_TYPE_POINTER:
			r2sleigh_wire_u8 (writer, WALK_TYPE_POINTER);
			r2sleigh_wire_u32 (writer, type->target_type_id);
			break;
		case R_ANAL_SNAPSHOT_TYPE_STRUCT:
			r2sleigh_wire_u8 (writer, WALK_TYPE_STRUCT);
			r2sleigh_wire_u32 (writer, type->aggregate_id);
			break;
		case R_ANAL_SNAPSHOT_TYPE_VOID:
			r2sleigh_wire_u8 (writer, WALK_TYPE_VOID);
			break;
		case R_ANAL_SNAPSHOT_TYPE_CODE:
			r2sleigh_wire_u8 (writer, WALK_TYPE_CODE);
			break;
		default:
			/* Signedness and indirection are not recoverable elsewhere. */
			return false;
		}
		r2sleigh_wire_u64 (writer, type->size_bits);
		r2sleigh_wire_u64 (writer, type->align_bits);
	}
	r2sleigh_wire_u32 (writer, (uint32_t)graph->num_aggregates);
	for (size_t i = 0; i < graph->num_aggregates; i++) {
		const RAnalSnapshotAggregateLayout *aggregate = &graph->aggregates[i];
		if (!aggregate->complete) {
			return false;
		}
		r2sleigh_wire_u32 (writer, aggregate->id);
		r2sleigh_wire_u32 (writer, aggregate->type_id);
		r2sleigh_wire_u64 (writer, aggregate->size_bits);
		r2sleigh_wire_u64 (writer, aggregate->align_bits);
		if (!walk_string (writer, aggregate->name)) {
			return false;
		}
		if (aggregate->num_members > UINT32_MAX) {
			return false;
		}
		r2sleigh_wire_u32 (writer, (uint32_t)aggregate->num_members);
		for (size_t member = 0; member < aggregate->num_members; member++) {
			const RAnalSnapshotAggregateMember *field = &aggregate->members[member];
			r2sleigh_wire_u32 (writer, field->member_id);
			r2sleigh_wire_u32 (writer, field->type_id);
			r2sleigh_wire_u64 (writer, field->offset_bits);
			r2sleigh_wire_u64 (writer, field->size_bits);
			if (!walk_string (writer, field->name)) {
				return false;
			}
		}
	}
	return true;
}

static bool walk_interface(R2SleighWireWriter *writer,
		const RAnalFunctionSnapshot *snapshot) {
	const RAnalFunctionInterfaceSnapshot *interface = &snapshot->function_interface;
	const bool exact_types = (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES) != 0;
	const bool exact_slots = (snapshot->capabilities
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

	const uint64_t revision = snapshot->revision_identity;
	uint8_t revision_bytes[8];
	for (unsigned i = 0; i < 8; i++) {
		revision_bytes[i] = (uint8_t)((revision >> (8 * i)) & 0xff);
	}
	r2sleigh_wire_bytes (writer, revision_bytes, sizeof (revision_bytes));

	if (!walk_string (writer, interface->calling_convention)) {
		return false;
	}

	if (interface->num_parameters > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)interface->num_parameters);
	for (size_t i = 0; i < interface->num_parameters; i++) {
		const RAnalSnapshotParameter *parameter = &interface->parameters[i];
		r2sleigh_wire_u32 (writer, parameter->index);
		walk_storage (writer, &parameter->storage);
	}
	if (!walk_result_kind (writer, interface->return_kind, &interface->return_storage)) {
		return false;
	}

	const bool has_slots = (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_SLOTS) != 0;
	const size_t num_slots = has_slots? walk_num_stack_slots (snapshot): 0;
	if (num_slots > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)num_slots);
	for (size_t i = 0; i < num_slots; i++) {
		const RAnalFcnSlot *slot = walk_stack_slot_at (snapshot, i);
		if (!slot || !walk_stack_slot (writer, slot, exact_types)) {
			return false;
		}
	}

	/* Logical values and the type graph travel together: without exact types
	 * there are no logical values to describe. */
	if (exact_types) {
		r2sleigh_wire_u32 (writer, (uint32_t)interface->num_parameters);
		for (size_t i = 0; i < interface->num_parameters; i++) {
			const RAnalSnapshotParameter *parameter = &interface->parameters[i];
			r2sleigh_wire_u32 (writer, parameter->logical_type_id);
			if (!walk_carrier (writer, &parameter->carrier)) {
				return false;
			}
		}
		if (interface->return_kind == R_ANAL_SNAPSHOT_RETURN_REGISTER) {
			r2sleigh_wire_bool (writer, true);
			r2sleigh_wire_u32 (writer, interface->return_type_id);
			if (!walk_carrier (writer, &interface->return_carrier)) {
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

	r2sleigh_wire_bool (writer, interface->stack_pointer_preserved_across_calls);
	r2sleigh_wire_bool (writer, interface->frame_pointer_preserved_across_calls);
	if (r_sys_getenv_asbool ("R2SLEIGH_DEBUG_MERGES")) {
		eprintf ("R2WIREPRESERVE sp=%d fp=%d params=%zu convention=%zu\n",
			interface->stack_pointer_preserved_across_calls,
			interface->frame_pointer_preserved_across_calls,
			interface->num_parameters,
			strlen (r_str_get (interface->calling_convention)));
	}

	const bool has_return_address = (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE) != 0;
	const bool has_stack_pointer = (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE) != 0;
	walk_named_optional_storage (writer, has_return_address,
		&interface->return_address_storage);
	walk_named_optional_storage (writer, has_stack_pointer,
		&interface->stack_pointer_storage);

	const bool has_frame = (snapshot->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE) != 0;
	walk_named_optional_storage (writer, has_frame, &snapshot->frame_pointer_storage);

	if (snapshot->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM) {
		const RAnalSnapshotReturnMechanismView *mechanism = &snapshot->return_mechanism;
		if (mechanism->kind != R_ANAL_SNAPSHOT_RETURN_MECHANISM_STACK) {
			return false;
		}
		/* The address width is not in the mechanism: it follows the machine,
		 * the same way the accessor transport derived it. */
		if (snapshot->bits <= 0 || snapshot->bits % 8 != 0) {
			return false;
		}
		r2sleigh_wire_bool (writer, true);
		r2sleigh_wire_u8 (writer, WALK_MECHANISM_STACKED);
		r2sleigh_wire_i64 (writer, mechanism->entry_sp_offset);
		r2sleigh_wire_u32 (writer, mechanism->slot_size);
		if (mechanism->exit_sp_delta < 0) {
			return false;
		}
		r2sleigh_wire_u32 (writer, (uint32_t)mechanism->exit_sp_delta);
		r2sleigh_wire_u32 (writer, (uint32_t)(snapshot->bits / 8));
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
	const RAnalFunctionInterfaceSnapshot *interface = &source->function_interface;
	const bool has_calls = (source->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_CALL_SITE_INTERFACES) != 0;
	const size_t num_calls = has_calls? source->num_call_site_interfaces: 0;
	if (num_calls > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)num_calls);
	for (size_t i = 0; i < num_calls; i++) {
		if (!walk_call_site (writer, &source->call_site_interfaces[i])) {
			return false;
		}
	}

	/* The revision identity must be present: it is what binds every part of
	 * this buffer to one capture. */
	if (source->revision_identity == 0) {
		return false;
	}
	uint8_t revision_bytes[8];
	for (unsigned i = 0; i < 8; i++) {
		revision_bytes[i] = (uint8_t)((source->revision_identity >> (8 * i)) & 0xff);
	}
	r2sleigh_wire_bytes (writer, revision_bytes, sizeof (revision_bytes));

	/* And this function's own payload identity, which the capture identity
	 * above is deliberately not: a callee carries the root's revision so a
	 * consumer can tell the bodies were read together, and its own content
	 * hash so the same callee under two callers is recognisably one body. */
	if (source->content_identity == 0) {
		return false;
	}
	uint8_t content_bytes[8];
	for (unsigned i = 0; i < 8; i++) {
		content_bytes[i] = (uint8_t)((source->content_identity >> (8 * i)) & 0xff);
	}
	r2sleigh_wire_bytes (writer, content_bytes, sizeof (content_bytes));

	/* An interface exists only when radare2 minted exact-interface authority.
	 * The struct being readable is not enough: a thunk has a readable interface
	 * that carries no recovered prototype, and treating it as one refuses the
	 * whole snapshot over a return kind radare2 never determined. */
	const bool has_interface = (source->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE) != 0;
	r2sleigh_wire_bool (writer, has_interface);
	if (has_interface && !walk_interface (writer, source)) {
		return false;
	}

	/* Machine roles repeat the return-address and stack-pointer carriers the
	 * interface names, so a consumer without an interface still knows them.
	 * They are collected independently of any recovered prototype, so they are
	 * reported whenever radare2 resolved them. Gating them on an exact
	 * interface withheld the carriers from exactly the functions that have no
	 * interface and most need them. */
	const bool has_return_address = (source->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE) != 0;
	const bool has_stack_pointer = (source->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE) != 0;
	walk_named_optional_storage (writer, has_return_address,
		&interface->return_address_storage);
	walk_named_optional_storage (writer, has_stack_pointer,
		&interface->stack_pointer_storage);
	if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT) {
		const RAnalSnapshotStackAllocationContractView *contract =
			&source->stack_allocation_contract;
		r2sleigh_wire_bool (writer, true);
		switch (contract->growth) {
		case R_ANAL_SNAPSHOT_STACK_GROWTH_LOWER:
			r2sleigh_wire_u8 (writer, WALK_GROWTH_LOWER);
			break;
		case R_ANAL_SNAPSHOT_STACK_GROWTH_HIGHER:
			r2sleigh_wire_u8 (writer, WALK_GROWTH_HIGHER);
			break;
		default:
			return false;
		}
		r2sleigh_wire_u32 (writer, contract->implicit_active_sp_bytes);
	} else {
		r2sleigh_wire_bool (writer, false);
	}

	/* Whether a call leaves those carriers alone. radare2 determines this from
	 * the calling convention and records it even when it never linked a
	 * signature -- its own comment says so -- and the interface block above is
	 * withheld for exactly those functions, so it travels here instead. Without
	 * it a function that calls loses every entry-relative fact about its frame:
	 * no stack roots, and so no certificate that a slot is its own. The
	 * interface is always readable, so this is always present. */
	r2sleigh_wire_bool (writer, true);
	r2sleigh_wire_bool (writer, interface->stack_pointer_preserved_across_calls);
	r2sleigh_wire_bool (writer, interface->frame_pointer_preserved_across_calls);

	/* The convention's candidate slots describe where a caller would leave
	 * arguments and the result. They are emitted whether or not a prototype was
	 * recovered, because a consumer recovering parameters from machine code has
	 * nothing to intersect against without them. */
	const bool slots_known = interface->convention_slots_known;
	const size_t num_slots = slots_known? interface->num_convention_argument_slots: 0;
	if (num_slots > UINT32_MAX) {
		return false;
	}
	const char *convention_name = "";
	if (slots_known) {
		convention_name = walk_bounded (interface->calling_convention);
		if (!convention_name) {
			return false;
		}
	}
	r2sleigh_wire_string (writer, convention_name);
	r2sleigh_wire_u32 (writer, (uint32_t)num_slots);
	for (size_t i = 0; i < num_slots; i++) {
		walk_storage (writer, &interface->convention_argument_slots[i]);
	}
	walk_optional_storage (writer,
		slots_known && interface->convention_result_slot.size != 0,
		&interface->convention_result_slot);

	uint16_t captured = 0;
	if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_OWNED_BOUNDED_FUNCTION_IMAGE) {
		captured |= WALK_CAPTURED_BOUNDED_IMAGE;
	}
	if (has_interface) {
		captured |= WALK_CAPTURED_INTERFACE;
	}
	/* Every remaining flag describes something the interface carries, so with
	 * no interface there is nothing to have captured. Deriving them from the
	 * capabilities alone claimed storages that no part of the buffer holds. */
	if (has_interface) {
		if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES) {
			captured |= WALK_CAPTURED_EXACT_TYPES;
		}
		if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES) {
			captured |= WALK_CAPTURED_EXACT_SLOT_ROLES;
		}
		if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE) {
			captured |= WALK_CAPTURED_RETURN_ADDRESS;
		}
		if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE) {
			captured |= WALK_CAPTURED_STACK_POINTER;
		}
		if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE) {
			captured |= WALK_CAPTURED_FRAME_POINTER;
		}
		if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM) {
			captured |= WALK_CAPTURED_RETURN_MECHANISM;
		}
	}
	if (source->capabilities & R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT) {
		captured |= WALK_CAPTURED_STACK_ALLOCATION;
	}
	r2sleigh_wire_u16 (writer, captured);

	/* Diagnostics carry the same capture identity, matching the accessor
	 * transport's own choice rather than inventing a second one. */
	r2sleigh_wire_u64 (writer, source->revision_identity);

	/* Each callee is a whole snapshot with its own string table, so it decodes
	 * by the same reader that decodes this one and nothing about it depends on
	 * where it sits in this buffer. They carry no callees of their own, so this
	 * nests exactly one level. */
	const size_t num_callees = (source->capabilities
		& R_ANAL_FUNCTION_SNAPSHOT_CAP_CALLEE_SNAPSHOTS)? source->num_callee_snapshots: 0;
	if (num_callees > UINT32_MAX) {
		return false;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)num_callees);
	for (size_t i = 0; i < num_callees; i++) {
		const RAnalFunctionSnapshot *callee = source->callee_snapshots
			? source->callee_snapshots[i]: NULL;
		if (!callee) {
			return false;
		}
		R2SleighWireWriter *nested = r2sleigh_wire_writer_new ();
		if (!nested) {
			return false;
		}
		size_t nested_len = 0;
		uint8_t *nested_buffer = r2sleigh_wire_write_snapshot (nested, callee)
			? r2sleigh_wire_writer_finish (nested, &nested_len): NULL;
		r2sleigh_wire_writer_free (nested);
		if (!nested_buffer) {
			return false;
		}
		r2sleigh_wire_bytes (writer, nested_buffer, nested_len);
		free (nested_buffer);
	}
	return r2sleigh_wire_writer_ok (writer);
}
