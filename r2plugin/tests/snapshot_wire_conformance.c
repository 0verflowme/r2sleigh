/* Pins the compatibility producer's v1 framing and primitive payload order.
 * r2source owns the current writer and accepts this older framing through its
 * explicit v1 migration path. */

#include "../snapshot_wire.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;

static void check(bool cond, const char *what) {
	if (!cond) {
		fprintf (stderr, "FAIL: %s\n", what);
		failures++;
	}
}

/* Payload: u8 0x7f, bool true, u16 0xbeef, u32 0xdeadbeef, u64, i64 -2,
 * bytes {1,2,3}, string "rsp", string "rsp" again, string "rbp",
 * optional_string absent. Two table entries, three references. */
static const uint8_t expected[] = {
	/* header */
	0x57, 0x53, 0x32, 0x52, /* magic "R2SW" little-endian */
	0x01, 0x00, 0x00, 0x00, /* format version 1 */
	0x02, 0x00, 0x00, 0x00, /* two interned strings */
	0x0e, 0x00, 0x00, 0x00, /* table bytes: 2 * (4 + 3) */
	0x2f, 0x00, 0x00, 0x00, /* payload bytes: 47 */
	0x00, 0x00, 0x00, 0x00, /* reserved */
	/* string table */
	0x03, 0x00, 0x00, 0x00, 'r', 's', 'p',
	0x03, 0x00, 0x00, 0x00, 'r', 'b', 'p',
	/* payload */
	0x7f,
	0x01,
	0xef, 0xbe,
	0xef, 0xbe, 0xad, 0xde,
	0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01,
	0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
	0x03, 0x00, 0x00, 0x00, 0x01, 0x02, 0x03,
	0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00,
	0x01, 0x00, 0x00, 0x00,
	0xff, 0xff, 0xff, 0xff
};

int main(void) {
	R2SleighWireWriter *writer = r2sleigh_wire_writer_new ();
	check (writer != NULL, "writer allocates");
	if (!writer) {
		return 1;
	}
	const uint8_t run[3] = { 1, 2, 3 };
	r2sleigh_wire_u8 (writer, 0x7f);
	r2sleigh_wire_bool (writer, true);
	r2sleigh_wire_u16 (writer, 0xbeef);
	r2sleigh_wire_u32 (writer, 0xdeadbeefu);
	r2sleigh_wire_u64 (writer, 0x0123456789abcdefull);
	r2sleigh_wire_i64 (writer, -2);
	r2sleigh_wire_bytes (writer, run, sizeof (run));
	r2sleigh_wire_string (writer, "rsp");
	r2sleigh_wire_string (writer, "rsp");
	r2sleigh_wire_string (writer, "rbp");
	r2sleigh_wire_optional_string (writer, NULL);
	check (r2sleigh_wire_writer_ok (writer), "no write failed");

	size_t len = 0;
	uint8_t *buffer = r2sleigh_wire_writer_finish (writer, &len);
	check (buffer != NULL, "finish emits a buffer");
	if (buffer) {
		check (len == sizeof (expected), "buffer length matches the vector");
		if (len == sizeof (expected)) {
			for (size_t i = 0; i < len; i++) {
				if (buffer[i] != expected[i]) {
					fprintf (stderr, "FAIL: byte %zu is 0x%02x, expected 0x%02x\n",
						i, buffer[i], expected[i]);
					failures++;
					break;
				}
			}
		}
		free (buffer);
	}
	r2sleigh_wire_writer_free (writer);

	/* A NULL required string must fail the writer rather than emit a hole. */
	writer = r2sleigh_wire_writer_new ();
	if (writer) {
		r2sleigh_wire_string (writer, NULL);
		check (!r2sleigh_wire_writer_ok (writer), "a NULL required string fails the writer");
		size_t ignored = 0;
		check (r2sleigh_wire_writer_finish (writer, &ignored) == NULL,
			"a failed writer emits no buffer");
		r2sleigh_wire_writer_free (writer);
	}

	if (failures) {
		fprintf (stderr, "%d snapshot wire conformance failure(s)\n", failures);
		return 1;
	}
	printf ("snapshot wire conformance ok\n");
	return 0;
}
