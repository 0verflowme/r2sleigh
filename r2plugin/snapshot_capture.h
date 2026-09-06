/* r2sleigh's capture of one radare2 function.
 *
 * The capture is r2sleigh policy: which facts to take from radare2's analysis,
 * at what granularity, and with what proof marking. radare2 does not need any
 * of that inside radare2, so it lives here and runs against radare2's public
 * API. What the fork still has to provide is the locking discipline its own
 * mutators observe, which is what makes a coherent read possible at all. */

#ifndef R2SLEIGH_SNAPSHOT_CAPTURE_H

#include <r_anal.h>
#include <r_core.h>

#define R2SLEIGH_SNAPSHOT_CAPTURE_H
#define R_ANAL_DYNCC_STACK_PREFIX '\1'
#define R_ANAL_DYNCC_REVSTACK_PREFIX '\2'
#define R_ANAL_DYNCC_REGSET_SIZE 256
#define R_ANAL_DYNCC_NAME_SIZE 32
#define R_ANAL_DYNCC_MAX_ROLES 16
#define R_ANAL_DYNCC_MAX_HOMES 8
#define R_ANAL_DYNCC_GROUP_SIZE 256
#define R_ANAL_CC_STACK_POP_UNKNOWN (-1)
#define R_ANAL_SNAPSHOT_TYPE_ID_INVALID UT32_MAX
typedef ut32 RAnalSnapshotTypeId;
#define IMAGE_REFUSE(why) do { refusal = (why); goto fail; } while (0)
#define SNAPSHOT_REFUSE(why) do { refusal = (why); goto fail; } while (0)
#define SNAPSHOT_MAX_CODE_POINTER_TABLES 16
#define SNAPSHOT_MAX_CODE_POINTER_TABLE_ENTRIES 256
#define SNAPSHOT_MAX_CALLEE_SNAPSHOTS 4
#define DB anal->sdb_cc
#define R_ANAL_FUNCTION_SNAPSHOT_LIMITS_VERSION 4

typedef struct {
	RAnal *anal;
	RList *types;
	Sdb *seen;
	bool fail_closed;
	bool valid;
} TypeSnapshotCloneContext;

typedef struct {
	ut64 xor_hash;
	ut64 sum_hash;
	ut64 count;
} TypeContextLinkHash;

typedef struct r_anal_dyn_cc_slice_t {
	const char *p;
	ut16 len;
} RAnalDynCCSlice;

typedef struct r_anal_dyn_cc_loc_t {
	RAnalDynCCSlice text;
	bool indexed;
	char prefix;
	int index;
} RAnalDynCCLoc;

typedef struct r_anal_dyn_cc_homes_t {
	RAnalDynCCLoc homes[R_ANAL_DYNCC_MAX_HOMES];
	int home_count;
} RAnalDynCCHomes;

typedef struct {
	RAnalVar *var;
	int order;
} FunctionArgOrder;

typedef enum {
	BASE_TYPE_APPEND_OK,
	BASE_TYPE_APPEND_SKIPPED,
	BASE_TYPE_APPEND_ERROR,
} BaseTypeAppendResult;

typedef enum {
	R_ANAL_CC_RETURN_MECHANISM_NONE = 0,
	R_ANAL_CC_RETURN_MECHANISM_STACK,
} RAnalCCReturnMechanismKind;

typedef struct r_anal_cc_return_mechanism_t {
	RAnalCCReturnMechanismKind kind;
	st64 entry_sp_offset;
	ut32 slot_size;
	st64 exit_sp_delta;
} RAnalCCReturnMechanism;

typedef enum {
	R_ANAL_CC_STACK_GROWTH_NONE = 0,
	R_ANAL_CC_STACK_GROWTH_LOWER,
	R_ANAL_CC_STACK_GROWTH_HIGHER,
} RAnalCCStackGrowth;

typedef struct r_anal_cc_stack_allocation_contract_t {
	// A full-width SP move in this direction grants the callee exclusive use
	// of the half-open interval between the entry and moved SP until exact
	// restoration. The red zone is the exact convention-owned interval that is
	// available without moving SP.
	RAnalCCStackGrowth growth;
	ut32 red_zone_bytes;
} RAnalCCStackAllocationContract;

typedef struct r_anal_fcn_slot_t {
	char *name;
	char *type;
	RAnalFcnSlotBase base;
	char *base_name;
	ut64 base_offset;
	ut32 base_size;
	st64 offset;
	ut32 size;
	bool offset_valid;
	RAnalFcnSlotRole role;
	int arg_index;
	char *home_reg;
	ut64 home_reg_offset;
	ut32 home_reg_size;
	/* The slot's declared type as a node of the function's type graph, or
	 * R_ANAL_SNAPSHOT_TYPE_ID_INVALID when the graph does not carry it. */
	ut32 logical_type_id;
	/* Whether the variable's type came from a DWARF record for this slot.
	 * Only a declared type is exact; radare2's own inference is evidence. */
	bool dwarf_declared;
} RAnalFcnSlot;

typedef struct r_anal_fcn_callee_t {
	ut64 call_addr;
	ut64 addr;
	char *name;
	RAnalFcnCalleeLinkage linkage;
	RAnalFunctionSignature *signature;
	RAnalCallTransfer transfer;
} RAnalFcnCallee;

typedef struct r_anal_fcn_context_t {
	RAnalFunctionSignature *signature;
	// Authoritative owner of immutable stack-resource declarations.
	RList *fcn_slots; // RList<RAnalFcnSlot *>
	RList *callees; // RList<RAnalFcnCallee *>
	ut64 function_dirty_epoch;
	ut64 type_dirty_epoch;
} RAnalFcnContext;

typedef struct r_anal_function_snapshot_t RAnalFunctionSnapshot;
typedef bool (*RAnalFunctionSnapshotCallback)(const RAnalFunctionSnapshot *snapshot, void *user);
#define R_ANAL_FUNCTION_SNAPSHOT_API 1
#define R_ANAL_FUNCTION_SNAPSHOT_SCHEMA_VERSION 19
typedef enum {
	R_ANAL_FUNCTION_SNAPSHOT_CAP_SIGNATURE = 1ULL << 0,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_SLOTS = 1ULL << 2,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_CALLEES = 1ULL << 3,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_TYPES = 1ULL << 4,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_REVISION = 1ULL << 6,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_INTERFACE = 1ULL << 7,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_CALL_SITE_INTERFACES = 1ULL << 8,
	// Reserved for a future machine-derived callsite identity source. Xrefs
	// and callee metadata must never mint this capability.
	R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_CALL_SITE_INTERFACES = 1ULL << 9,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FUNCTION_TYPES = 1ULL << 10,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_SLOT_ROLES = 1ULL << 11,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_RETURN_ADDRESS_STORAGE = 1ULL << 12,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_STACK_POINTER_STORAGE = 1ULL << 13,
	// Bytes are exact reads owned by the snapshot. CFG/successor metadata is
	// advisory until a trusted decoder independently validates it.
	R_ANAL_FUNCTION_SNAPSHOT_CAP_OWNED_BOUNDED_FUNCTION_IMAGE = 1ULL << 14,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_RETURN_MECHANISM = 1ULL << 15,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_FRAME_POINTER_STORAGE = 1ULL << 16,
	R_ANAL_FUNCTION_SNAPSHOT_CAP_EXACT_STACK_ALLOCATION_CONTRACT = 1ULL << 17,
	// The snapshot carries snapshots of the functions it calls directly, taken
	// in the same locked transaction. A consumer that reasons across a call
	// needs the callee's body, and one snapshot per call cannot supply it.
	R_ANAL_FUNCTION_SNAPSHOT_CAP_CALLEE_SNAPSHOTS = 1ULL << 18,
} RAnalFunctionSnapshotCapability;

typedef struct r_anal_snapshot_register_storage_t {
	char *name;
	ut64 offset;
	ut32 size;
} RAnalSnapshotRegisterStorage;

typedef enum {
	R_ANAL_SNAPSHOT_TYPE_INVALID = 0,
	R_ANAL_SNAPSHOT_TYPE_SIGNED_INTEGER,
	R_ANAL_SNAPSHOT_TYPE_UNSIGNED_INTEGER,
	R_ANAL_SNAPSHOT_TYPE_POINTER,
	R_ANAL_SNAPSHOT_TYPE_STRUCT,
	/* An object the graph does not describe, and code. Neither has a size or
	 * a layout; each exists only to be pointed at, which is how `void *` and
	 * a function pointer are placed without inventing what they point to. */
	R_ANAL_SNAPSHOT_TYPE_VOID,
	R_ANAL_SNAPSHOT_TYPE_CODE,
	/* An aggregate whose members all begin at its start. */
	R_ANAL_SNAPSHOT_TYPE_UNION,
} RAnalSnapshotTypeKind;

typedef enum {
	R_ANAL_SNAPSHOT_CARRIER_INVALID = 0,
	R_ANAL_SNAPSHOT_CARRIER_FULL,
	R_ANAL_SNAPSHOT_CARRIER_LOW_BITS,
} RAnalSnapshotCarrierProjectionKind;

typedef struct r_anal_snapshot_carrier_projection_t {
	RAnalSnapshotCarrierProjectionKind kind;
	ut64 offset_bits;
	ut64 size_bits;
} RAnalSnapshotCarrierProjection;

typedef struct r_anal_snapshot_parameter_t {
	ut32 index;
	char *name;
	RAnalSnapshotRegisterStorage storage;
	RAnalSnapshotTypeId logical_type_id;
	RAnalSnapshotCarrierProjection carrier;
} RAnalSnapshotParameter;

typedef enum {
	R_ANAL_SNAPSHOT_RETURN_UNKNOWN = 0,
	R_ANAL_SNAPSHOT_RETURN_VOID,
	R_ANAL_SNAPSHOT_RETURN_REGISTER,
} RAnalSnapshotReturnKind;

typedef enum {
	R_ANAL_SNAPSHOT_RETURN_ARITY_UNKNOWN = 0,
	R_ANAL_SNAPSHOT_RETURN_ARITY_VOID,
	R_ANAL_SNAPSHOT_RETURN_ARITY_VALUE,
} RAnalSnapshotReturnArity;

typedef enum {
	R_ANAL_SNAPSHOT_RETURN_MECHANISM_NONE = 0,
	R_ANAL_SNAPSHOT_RETURN_MECHANISM_STACK,
} RAnalSnapshotReturnMechanismKind;

typedef struct r_anal_snapshot_return_mechanism_view_t {
	RAnalSnapshotReturnMechanismKind kind;
	st64 entry_sp_offset;
	ut32 slot_size;
	st64 exit_sp_delta;
} RAnalSnapshotReturnMechanismView;

typedef enum {
	R_ANAL_SNAPSHOT_STACK_GROWTH_NONE = 0,
	R_ANAL_SNAPSHOT_STACK_GROWTH_LOWER,
	R_ANAL_SNAPSHOT_STACK_GROWTH_HIGHER,
} RAnalSnapshotStackGrowth;

typedef struct r_anal_snapshot_stack_allocation_contract_view_t {
	RAnalSnapshotStackGrowth growth;
	ut32 implicit_active_sp_bytes;
} RAnalSnapshotStackAllocationContractView;

typedef struct r_anal_function_interface_snapshot_t {
	char *calling_convention;
	RAnalSnapshotParameter *parameters;
	size_t num_parameters;
	RAnalSnapshotReturnKind return_kind;
	RAnalSnapshotRegisterStorage return_storage;
	// Register consumed by the lifted return: LR/RA on link-register targets,
	// otherwise PC after the stack return address has been loaded.
	RAnalSnapshotRegisterStorage return_address_storage;
	// Full-width architectural stack pointer resolved from the typed SP role,
	// independently of whether the function declares SP-relative stack slots.
	RAnalSnapshotRegisterStorage stack_pointer_storage;
	bool variadic;
	bool noreturn;
	bool stack_resources_complete;
	bool stack_slot_roles_complete;
	bool complete;
	RAnalSnapshotTypeId return_type_id;
	RAnalSnapshotCarrierProjection return_carrier;
	bool logical_types_complete;
	// The calling convention states that a callee restores these carriers, so a
	// consumer can establish that they survive a call rather than assuming it.
	bool stack_pointer_preserved_across_calls;
	bool frame_pointer_preserved_across_calls;
	// Registers the calling convention would use for arguments and the result,
	// in convention order. These come from the convention itself rather than
	// from any recovered prototype, so they are present even when no signature
	// was recovered, and they say where a caller *would* leave a value, not
	// that the function takes one.
	RAnalSnapshotRegisterStorage *convention_argument_slots;
	size_t num_convention_argument_slots;
	RAnalSnapshotRegisterStorage convention_result_slot;
	bool convention_slots_known;
} RAnalFunctionInterfaceSnapshot;

typedef struct r_anal_call_site_interface_snapshot_t {
	ut64 instruction_addr;
	ut64 target_addr;
	// What the target is called. A consumer that renders the call has no other
	// way to spell it, and rediscovering the name would mean handing out the
	// RAnal this snapshot exists to replace.
	char *target_name;
	char *calling_convention;
	RAnalSnapshotParameter *arguments;
	size_t num_arguments;
	RAnalSnapshotReturnKind result_kind;
	RAnalSnapshotRegisterStorage result_storage;
	bool variadic;
	bool noreturn;
	bool complete;
	RAnalCallTransfer transfer;
} RAnalCallSiteInterfaceSnapshot;

typedef struct r_anal_snapshot_type_t {
	RAnalSnapshotTypeId id;
	RAnalSnapshotTypeKind kind;
	ut64 size_bits;
	ut64 align_bits;
	RAnalSnapshotTypeId target_type_id;
	ut32 aggregate_id;
} RAnalSnapshotType;

typedef struct r_anal_snapshot_aggregate_member_t {
	ut32 member_id;
	RAnalSnapshotTypeId type_id;
	ut64 offset_bits;
	ut64 size_bits;
	char *name;
} RAnalSnapshotAggregateMember;

typedef struct r_anal_snapshot_aggregate_layout_t {
	ut32 id;
	RAnalSnapshotTypeId type_id;
	ut64 size_bits;
	ut64 align_bits;
	char *name;
	RAnalSnapshotAggregateMember *members;
	size_t num_members;
	bool complete;
} RAnalSnapshotAggregateLayout;

typedef struct r_anal_snapshot_type_graph_t {
	RAnalSnapshotType *types;
	size_t num_types;
	RAnalSnapshotAggregateLayout *aggregates;
	size_t num_aggregates;
	bool complete;
} RAnalSnapshotTypeGraph;

typedef enum {
	R_ANAL_SNAPSHOT_SUCCESSOR_DIRECT = 0,
	R_ANAL_SNAPSHOT_SUCCESSOR_FALLTHROUGH,
	R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_CASE,
	R_ANAL_SNAPSHOT_SUCCESSOR_SWITCH_DEFAULT,
} RAnalSnapshotSuccessorKind;

typedef struct r_anal_snapshot_successor_t {
	RAnalSnapshotSuccessorKind kind;
	ut64 target_addr;
	ut64 case_value;
	bool external;
} RAnalSnapshotSuccessor;

typedef struct r_anal_snapshot_block_t {
	ut64 addr;
	ut64 size;
	ut8 *bytes;
	RAnalSnapshotSuccessor *successors;
	size_t num_successors;
	// Exact indirect-branch instruction address, or UT64_MAX without a switch.
	ut64 switch_addr;
} RAnalSnapshotBlock;

typedef struct r_anal_snapshot_string_literal_t {
	ut64 addr;
	char *text;
} RAnalSnapshotStringLiteral;

typedef struct r_anal_snapshot_data_symbol_t {
	ut64 addr;
	char *name;
	char *type_name;
} RAnalSnapshotDataSymbol;

typedef struct r_anal_snapshot_code_pointer_table_t {
	ut64 addr;
	ut32 entry_size;
	ut64 *targets;
	size_t num_targets;
} RAnalSnapshotCodePointerTable;

typedef struct r_anal_function_image_snapshot_t {
	ut64 entry_addr;
	RAnalSnapshotBlock *blocks;
	size_t num_blocks;
	ut64 *external_exits;
	size_t num_external_exits;
	RAnalSnapshotStringLiteral *string_literals;
	size_t num_string_literals;
	RAnalSnapshotDataSymbol *data_symbols;
	size_t num_data_symbols;
	RAnalSnapshotCodePointerTable *code_pointer_tables;
	size_t num_code_pointer_tables;
	size_t total_source_bytes;
} RAnalFunctionImageSnapshot;

typedef struct r_anal_function_snapshot_view_t {
	ut64 capabilities;
	ut64 function_addr;
	int bits;
	ut32 endian;
	size_t arch_id_length;
	size_t cpu_id_length;
	size_t function_name_length;
	size_t num_call_site_interfaces;
	size_t num_stack_slots;
	// Stable diagnostic/cache identity of the owned payload, never proof authority.
	ut64 revision_identity;
	// Identity of this function's own payload rather than of the capture it
	// arrived in. Equal to revision_identity for the function asked for, and
	// its own hash for a callee collected beside it.
	ut64 content_identity;
	size_t num_blocks;
	size_t num_external_exits;
	size_t num_string_literals;
	size_t num_data_symbols;
	size_t total_source_bytes;
	size_t num_callee_snapshots;
	size_t num_code_pointer_tables;
} RAnalFunctionSnapshotView;

typedef struct r_anal_snapshot_block_view_t {
	ut64 addr;
	ut64 size;
	size_t num_successors;
	ut64 switch_addr;
} RAnalSnapshotBlockView;

typedef struct r_anal_snapshot_string_literal_view_t {
	ut64 addr;
} RAnalSnapshotStringLiteralView;

typedef struct r_anal_snapshot_data_symbol_view_t {
	ut64 addr;
	size_t name_length;
	size_t type_name_length;
} RAnalSnapshotDataSymbolView;

typedef struct r_anal_snapshot_successor_view_t {
	RAnalSnapshotSuccessorKind kind;
	ut64 target_addr;
	ut64 case_value;
	bool external;
} RAnalSnapshotSuccessorView;

typedef struct r_anal_snapshot_register_storage_view_t {
	ut64 offset;
	ut32 size;
} RAnalSnapshotRegisterStorageView;

typedef struct r_anal_snapshot_parameter_view_t {
	ut32 index;
	size_t name_length;
	RAnalSnapshotRegisterStorageView storage;
	RAnalSnapshotTypeId logical_type_id;
	RAnalSnapshotCarrierProjection carrier;
} RAnalSnapshotParameterView;

typedef struct r_anal_function_interface_snapshot_view_t {
	size_t calling_convention_length;
	size_t num_parameters;
	RAnalSnapshotReturnKind return_kind;
	RAnalSnapshotRegisterStorageView return_storage;
	RAnalSnapshotRegisterStorageView return_address_storage;
	RAnalSnapshotRegisterStorageView stack_pointer_storage;
	RAnalSnapshotTypeId return_type_id;
	RAnalSnapshotCarrierProjection return_carrier;
	bool stack_pointer_preserved_across_calls;
	bool frame_pointer_preserved_across_calls;
	size_t num_convention_argument_slots;
	RAnalSnapshotRegisterStorageView convention_result_slot;
	bool convention_slots_known;
} RAnalFunctionInterfaceSnapshotView;

typedef struct r_anal_call_site_interface_snapshot_view_t {
	ut64 instruction_addr;
	ut64 target_addr;
	size_t num_arguments;
	RAnalSnapshotReturnKind result_kind;
	RAnalSnapshotRegisterStorageView result_storage;
	bool variadic;
	bool noreturn;
	bool complete;
} RAnalCallSiteInterfaceSnapshotView;

typedef struct r_anal_snapshot_type_graph_view_t {
	size_t num_types;
	size_t num_aggregates;
	bool complete;
} RAnalSnapshotTypeGraphView;

typedef struct r_anal_snapshot_aggregate_layout_view_t {
	ut32 id;
	RAnalSnapshotTypeId type_id;
	ut64 size_bits;
	ut64 align_bits;
	size_t num_members;
	bool complete;
} RAnalSnapshotAggregateLayoutView;

typedef struct r_anal_snapshot_aggregate_member_view_t {
	ut32 member_id;
	RAnalSnapshotTypeId type_id;
	ut64 offset_bits;
	ut64 size_bits;
} RAnalSnapshotAggregateMemberView;

typedef struct r_anal_snapshot_stack_slot_view_t {
	RAnalFcnSlotBase base;
	ut64 base_offset;
	ut32 base_size;
	st64 offset;
	ut32 size;
	bool offset_valid;
	RAnalFcnSlotRole role;
	int arg_index;
	ut64 home_reg_offset;
	ut32 home_reg_size;
} RAnalSnapshotStackSlotView;

typedef enum {
	R_ANAL_SNAPSHOT_STACK_SLOT_STRING_NAME = 0,
	R_ANAL_SNAPSHOT_STACK_SLOT_STRING_TYPE,
	R_ANAL_SNAPSHOT_STACK_SLOT_STRING_BASE_NAME,
	R_ANAL_SNAPSHOT_STACK_SLOT_STRING_HOME_REGISTER,
} RAnalSnapshotStackSlotStringKind;

typedef struct r_anal_snapshot_signature_view_t {
	size_t num_parameters;
	bool noreturn;
	RAnalSnapshotReturnArity return_arity;
} RAnalSnapshotSignatureView;

typedef enum {
	R_ANAL_SNAPSHOT_SIGNATURE_STRING_RETURN_TYPE = 0,
	R_ANAL_SNAPSHOT_SIGNATURE_STRING_CALLING_CONVENTION,
	R_ANAL_SNAPSHOT_SIGNATURE_STRING_PARAMETER_TYPE,
	R_ANAL_SNAPSHOT_SIGNATURE_STRING_PARAMETER_NAME,
} RAnalSnapshotSignatureStringKind;

typedef enum {
	R_ANAL_SNAPSHOT_INTERFACE_STORAGE_RETURN = 0,
	R_ANAL_SNAPSHOT_INTERFACE_STORAGE_RETURN_ADDRESS,
	R_ANAL_SNAPSHOT_INTERFACE_STORAGE_STACK_POINTER,
	R_ANAL_SNAPSHOT_INTERFACE_STORAGE_FRAME_POINTER,
} RAnalSnapshotInterfaceStorageKind;

typedef struct r_anal_snapshot_code_pointer_table_view_t {
	ut64 addr;
	ut32 entry_size;
	size_t num_targets;
} RAnalSnapshotCodePointerTableView;

typedef struct r_anal_function_snapshot_limits_t {
	ut32 struct_size;
	ut32 reserved;
	size_t max_base_types;
	size_t max_base_type_children;
	size_t max_base_type_string_bytes;
	size_t max_function_blocks;
	size_t max_block_source_bytes;
	size_t max_function_source_bytes;
	size_t max_function_successors;
	size_t max_context_items;
	size_t max_context_string_bytes;
	size_t max_interface_parameters;
	size_t max_call_sites;
	size_t max_call_site_parameters;
	size_t max_total_call_site_parameters;
	size_t max_interface_string_bytes;
	size_t max_type_graph_types;
	size_t max_type_graph_aggregates;
	size_t max_type_graph_members;
	size_t max_total_owned_bytes;
} RAnalFunctionSnapshotLimits;

typedef enum {
	FCN_TRANSFER_NONE = 0,
	// `jmp target`, the target spelled in the instruction
	FCN_TRANSFER_DIRECT_JUMP,
	// `jmp [slot]` or `br reg`, the target read from somewhere
	FCN_TRANSFER_VALUE_JUMP,
} FcnContextTransferKind;

typedef enum {
	SNAPSHOT_TERMINAL_SEQUENTIAL,
	SNAPSHOT_TERMINAL_DIRECT,
	// The block ends by transferring control somewhere the analysis did not
	// resolve, so any successor recorded for it is not supported by the
	// instruction.
	SNAPSHOT_TERMINAL_UNKNOWN_EXIT,
	SNAPSHOT_TERMINAL_REJECT,
} SnapshotTerminalFlow;

typedef struct {
	const RList *base_types;
	RAnalSnapshotTypeGraph *graph;
	const RAnalBaseType **aggregate_sources;
	size_t type_capacity;
	size_t aggregate_capacity;
	ut64 pointer_bits;
	// Plain char has no signedness in C: each target picks one. Absent when the
	// target's choice is not known here, so plain char stays unresolved rather
	// than being assigned a signedness it may not have.
	RAnalSnapshotTypeKind char_kind;
	bool char_kind_known;
} SnapshotTypeGraphBuilder;

typedef enum {
	SNAPSHOT_TYPE_GRAPH_UNSUPPORTED = 0,
	SNAPSHOT_TYPE_GRAPH_VALID,
	SNAPSHOT_TYPE_GRAPH_NO_MEMORY,
} SnapshotTypeGraphResult;

typedef enum {
	SNAPSHOT_STORAGE_INVALID = 0,
	SNAPSHOT_STORAGE_VALID,
	SNAPSHOT_STORAGE_NO_MEMORY,
} SnapshotStorageResult;

typedef struct {
	bool valid;
	RAnalSnapshotTypeKind kind;
	ut64 required_bits;
} SnapshotIntegerSyntax;

typedef struct {
	size_t base_types;
	size_t children;
	size_t string_bytes;
} RAnalTypeSnapshotBudget;

typedef struct {
	RAnal *anal;
	Sdb *seen;
	RAnalTypeSnapshotBudget budget;
	const RAnalFunctionSnapshotLimits *limits;
} TypeSnapshotPreflightContext;

typedef struct {
	Sdb *type_db;
	RList *base_types;
	const RAnalFunctionSnapshotLimits *limits;
	size_t base_type_count;
	size_t string_bytes;
	bool valid;
} SnapshotTypeResolverCapture;

typedef struct r_anal_dyn_cc_seq_t {
	RAnalDynCCLoc locs[R_ANAL_CC_MAXARG];
	int count;
} RAnalDynCCSeq;

typedef struct r_anal_dyn_cc_role_t {
	char tag;
	int arg;
	RAnalDynCCLoc loc;
} RAnalDynCCRole;

typedef struct r_anal_dyn_cc_t {
	RAnalDynCCHomes args[R_ANAL_CC_MAXARG];
	int arg_count;
	bool arg_tail;
	RAnalDynCCLoc arg_tail_loc;
	RAnalDynCCSlice arg_ref;
	RAnalDynCCHomes fpargs[R_ANAL_CC_MAXARG];
	int fparg_count;
	RAnalDynCCSlice fparg_ref;
	RAnalDynCCHomes rets[R_ANAL_CC_MAXARG];
	int ret_count;
	RAnalDynCCSlice ret_ref;
	int stack_pop;
	RAnalDynCCSlice clobbers;
	RAnalDynCCSlice preserves;
	RAnalDynCCRole roles[R_ANAL_DYNCC_MAX_ROLES];
	int role_count;
} RAnalDynCC;





























































































/* Calling-convention shapes the capture reads. Private to radare2 before
 * the move; they describe what a convention says, which is the capture's
 * business rather than radare2's to publish. */




/* The snapshot types, retired from r_anal.h. They describe r2sleigh's
 * view of a function, so every radare2 translation unit was parsing a
 * description of something it never touched. */

/* Refusal and bound macros the capture uses, file-local in radare2 before the
 * move. The two code-pointer-table bounds are deliberately duplicated rather
 * than shared: radare2's own image code still enforces them, and a shared
 * header between the two would put this file back inside radare2. */
/* radare2's calling-convention helpers spell the sdb handle this way. */

/* Types the capture owns: file-local in radare2 before the move, so they
 * travel with the code that uses them rather than staying in a header no
 * radare2 translation unit needs any more. */
// Inclusive limits for owned data collected into a function snapshot.
// String/JSON byte limits include each terminating NUL byte.

struct r_anal_function_snapshot_t {
	ut32 schema_version;
	ut32 struct_size;
	ut64 capabilities;
	RAnalFcnContext context;
	// Logical return arity from a recovered signature or an exact loader role.
	RAnalSnapshotReturnArity return_arity;
	ut64 function_addr;
	ut64 function_size;
	int bits;
	ut32 endian;
	st64 maxstack;
	char *arch_id;
	char *cpu_id;
	char *function_name;
	RList *base_types; // RList<RAnalBaseType *>
	ut64 type_context_hash;
	RAnalFunctionInterfaceSnapshot function_interface;
	RAnalSnapshotReturnMechanismView return_mechanism;
	RAnalSnapshotRegisterStorage frame_pointer_storage;
	RAnalSnapshotStackAllocationContractView stack_allocation_contract;
	RAnalCallSiteInterfaceSnapshot *call_site_interfaces;
	size_t num_call_site_interfaces;
	ut64 revision_identity;
	// Identity of this function's own captured payload, which the capture
	// identity above deliberately is not: a callee inherits the root's
	// revision so a consumer can tell the bodies were read together, and that
	// makes the same callee under two callers carry two identities. A cache
	// keyed on the capture therefore never hits for the one case a callee
	// cache exists to serve.
	ut64 content_identity;
	RAnalSnapshotTypeGraph type_graph;
	RAnalFunctionImageSnapshot image;
	// Snapshots of the functions this one calls directly, collected in the same
	// locked transaction so the set describes one state of the analysis rather
	// than several. Bounded and one level deep: a consumer that reasons across a
	// call needs the callee's body, not the whole program.
	RAnalFunctionSnapshot **callee_snapshots;
	size_t num_callee_snapshots;
};










/* Capture one function as an owned, immutable snapshot, or NULL with *reason
 * set. Takes the core lock and then anal->lock, so the walk sees one state.
 * Refuses on a debug-backed target, where the bytes under a function are not
 * stable enough to prove anything about. */
RAnalFunctionSnapshot *r2sleigh_function_snapshot_take(RCore *core, ut64 function_addr, const char **reason);

/* Release a snapshot and everything it owns. Safe on NULL. */
void r2sleigh_function_snapshot_free(RAnalFunctionSnapshot *snapshot);

#endif
