#include "snapshot_wire.h"

#include <stdlib.h>
#include <string.h>

typedef struct {
	uint8_t *data;
	size_t len;
	size_t cap;
} WireBuf;

typedef struct {
	char **items;
	size_t len;
	size_t cap;
} WireStrings;

struct r2sleigh_wire_writer_t {
	WireBuf payload;
	WireStrings strings;
	bool ok;
};

static bool buf_reserve(WireBuf *buf, size_t extra) {
	if (buf->len + extra <= buf->cap) {
		return true;
	}
	size_t want = buf->cap ? buf->cap * 2 : 256;
	while (want < buf->len + extra) {
		size_t next = want * 2;
		if (next < want) {
			return false;
		}
		want = next;
	}
	uint8_t *grown = realloc (buf->data, want);
	if (!grown) {
		return false;
	}
	buf->data = grown;
	buf->cap = want;
	return true;
}

static void buf_push(R2SleighWireWriter *writer, const uint8_t *data, size_t len) {
	if (!writer->ok) {
		return;
	}
	if (!buf_reserve (&writer->payload, len)) {
		writer->ok = false;
		return;
	}
	if (len) {
		memcpy (writer->payload.data + writer->payload.len, data, len);
		writer->payload.len += len;
	}
}

R2SleighWireWriter *r2sleigh_wire_writer_new(void) {
	R2SleighWireWriter *writer = calloc (1, sizeof (*writer));
	if (writer) {
		writer->ok = true;
	}
	return writer;
}

void r2sleigh_wire_writer_free(R2SleighWireWriter *writer) {
	if (!writer) {
		return;
	}
	for (size_t i = 0; i < writer->strings.len; i++) {
		free (writer->strings.items[i]);
	}
	free (writer->strings.items);
	free (writer->payload.data);
	free (writer);
}

bool r2sleigh_wire_writer_ok(const R2SleighWireWriter *writer) {
	return writer && writer->ok;
}

void r2sleigh_wire_u8(R2SleighWireWriter *writer, uint8_t value) {
	buf_push (writer, &value, 1);
}

void r2sleigh_wire_bool(R2SleighWireWriter *writer, bool value) {
	r2sleigh_wire_u8 (writer, value? 1: 0);
}

void r2sleigh_wire_u16(R2SleighWireWriter *writer, uint16_t value) {
	uint8_t out[2] = { (uint8_t)(value & 0xff), (uint8_t)((value >> 8) & 0xff) };
	buf_push (writer, out, sizeof (out));
}

void r2sleigh_wire_u32(R2SleighWireWriter *writer, uint32_t value) {
	uint8_t out[4];
	for (unsigned i = 0; i < 4; i++) {
		out[i] = (uint8_t)((value >> (8 * i)) & 0xff);
	}
	buf_push (writer, out, sizeof (out));
}

void r2sleigh_wire_u64(R2SleighWireWriter *writer, uint64_t value) {
	uint8_t out[8];
	for (unsigned i = 0; i < 8; i++) {
		out[i] = (uint8_t)((value >> (8 * i)) & 0xff);
	}
	buf_push (writer, out, sizeof (out));
}

void r2sleigh_wire_i64(R2SleighWireWriter *writer, int64_t value) {
	/* Two's complement on the wire, matching the Rust side's `as` cast. */
	r2sleigh_wire_u64 (writer, (uint64_t)value);
}

void r2sleigh_wire_bytes(R2SleighWireWriter *writer, const uint8_t *data, size_t len) {
	if (!writer || !writer->ok) {
		return;
	}
	if (len > 0xffffffffu || (!data && len)) {
		writer->ok = false;
		return;
	}
	r2sleigh_wire_u32 (writer, (uint32_t)len);
	buf_push (writer, data, len);
}

static bool strings_reserve(WireStrings *strings) {
	if (strings->len < strings->cap) {
		return true;
	}
	size_t want = strings->cap ? strings->cap * 2 : 16;
	char **grown = realloc (strings->items, want * sizeof (char *));
	if (!grown) {
		return false;
	}
	strings->items = grown;
	strings->cap = want;
	return true;
}

/* Interning is a linear scan. A snapshot's string count is small and dominated
 * by repeats, so this keeps the table minimal without a hash table. */
static bool intern(R2SleighWireWriter *writer, const char *value, uint32_t *out) {
	for (size_t i = 0; i < writer->strings.len; i++) {
		if (!strcmp (writer->strings.items[i], value)) {
			*out = (uint32_t)i;
			return true;
		}
	}
	if (writer->strings.len >= R2SLEIGH_SNAPSHOT_WIRE_NO_STRING) {
		return false;
	}
	if (!strings_reserve (&writer->strings)) {
		return false;
	}
	char *copy = strdup (value);
	if (!copy) {
		return false;
	}
	writer->strings.items[writer->strings.len] = copy;
	*out = (uint32_t)writer->strings.len;
	writer->strings.len++;
	return true;
}

void r2sleigh_wire_string(R2SleighWireWriter *writer, const char *value) {
	if (!writer || !writer->ok) {
		return;
	}
	uint32_t id = 0;
	if (!value || !intern (writer, value, &id)) {
		writer->ok = false;
		return;
	}
	r2sleigh_wire_u32 (writer, id);
}

void r2sleigh_wire_optional_string(R2SleighWireWriter *writer, const char *value) {
	if (!value) {
		r2sleigh_wire_u32 (writer, R2SLEIGH_SNAPSHOT_WIRE_NO_STRING);
		return;
	}
	r2sleigh_wire_string (writer, value);
}

uint8_t *r2sleigh_wire_writer_finish(R2SleighWireWriter *writer, size_t *out_len) {
	if (!writer || !writer->ok || !out_len) {
		return NULL;
	}
	size_t table_bytes = 0;
	for (size_t i = 0; i < writer->strings.len; i++) {
		size_t len = strlen (writer->strings.items[i]);
		if (len > 0xffffffffu) {
			return NULL;
		}
		table_bytes += 4 + len;
	}
	if (table_bytes > 0xffffffffu || writer->payload.len > 0xffffffffu) {
		return NULL;
	}
	size_t total = R2SLEIGH_SNAPSHOT_WIRE_HEADER_BYTES + table_bytes + writer->payload.len;
	uint8_t *out = malloc (total);
	if (!out) {
		return NULL;
	}
	size_t at = 0;
	const uint32_t header[6] = {
		R2SLEIGH_SNAPSHOT_WIRE_MAGIC,
		R2SLEIGH_SNAPSHOT_WIRE_FORMAT_VERSION,
		(uint32_t)writer->strings.len,
		(uint32_t)table_bytes,
		(uint32_t)writer->payload.len,
		0 /* reserved, must stay zero */
	};
	for (unsigned word = 0; word < 6; word++) {
		for (unsigned i = 0; i < 4; i++) {
			out[at++] = (uint8_t)((header[word] >> (8 * i)) & 0xff);
		}
	}
	for (size_t i = 0; i < writer->strings.len; i++) {
		const char *value = writer->strings.items[i];
		uint32_t len = (uint32_t)strlen (value);
		for (unsigned b = 0; b < 4; b++) {
			out[at++] = (uint8_t)((len >> (8 * b)) & 0xff);
		}
		if (len) {
			memcpy (out + at, value, len);
			at += len;
		}
	}
	if (writer->payload.len) {
		memcpy (out + at, writer->payload.data, writer->payload.len);
		at += writer->payload.len;
	}
	*out_len = total;
	return out;
}
