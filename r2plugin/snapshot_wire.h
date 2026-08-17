/* Flat snapshot wire writer.
 *
 * Producer side of the transport that replaces the accessor table. radare2
 * serializes one function snapshot into a single self-describing buffer instead
 * of implementing a callback per field, so the C boundary carries one buffer
 * rather than 67 entry points and 31 struct sizes kept in lockstep.
 *
 * The encoding is owned by r2source::snapshot_wire; this writer must stay
 * byte-identical to it. Both sides assert the same framing in their conformance
 * tests, so drift in either direction fails a test rather than producing a
 * buffer the other side misreads. */

#ifndef R2SLEIGH_SNAPSHOT_WIRE_H
#define R2SLEIGH_SNAPSHOT_WIRE_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define R2SLEIGH_SNAPSHOT_WIRE_MAGIC 0x52325357u
#define R2SLEIGH_SNAPSHOT_WIRE_FORMAT_VERSION 1u
#define R2SLEIGH_SNAPSHOT_WIRE_HEADER_BYTES 24u

/* Reference written for an absent optional string. */
#define R2SLEIGH_SNAPSHOT_WIRE_NO_STRING 0xffffffffu

typedef struct r2sleigh_wire_writer_t R2SleighWireWriter;

/* Create an empty writer, or NULL when out of memory. */
R2SleighWireWriter *r2sleigh_wire_writer_new(void);

/* Release a writer and everything it owns. Safe on NULL. */
void r2sleigh_wire_writer_free(R2SleighWireWriter *writer);

/* Every writer call records failure in the writer rather than returning it, so
 * a long serialization reads as straight-line code. Check once at the end. */
bool r2sleigh_wire_writer_ok(const R2SleighWireWriter *writer);

void r2sleigh_wire_u8(R2SleighWireWriter *writer, uint8_t value);
void r2sleigh_wire_bool(R2SleighWireWriter *writer, bool value);
void r2sleigh_wire_u16(R2SleighWireWriter *writer, uint16_t value);
void r2sleigh_wire_u32(R2SleighWireWriter *writer, uint32_t value);
void r2sleigh_wire_u64(R2SleighWireWriter *writer, uint64_t value);
void r2sleigh_wire_i64(R2SleighWireWriter *writer, int64_t value);

/* Length-prefixed byte run. A NULL pointer with length zero is an empty run. */
void r2sleigh_wire_bytes(R2SleighWireWriter *writer, const uint8_t *data, size_t len);

/* Intern a string and write its table reference. NULL is rejected; use
 * r2sleigh_wire_optional_string for a value that may be absent. */
void r2sleigh_wire_string(R2SleighWireWriter *writer, const char *value);

/* Intern an optional string; NULL writes the reference no entry uses. */
void r2sleigh_wire_optional_string(R2SleighWireWriter *writer, const char *value);

/* Emit the finished buffer: header, string table, payload. Ownership passes to
 * the caller, which must free it. Returns NULL if any write failed, so a
 * partially serialized snapshot can never reach the boundary. */
uint8_t *r2sleigh_wire_writer_finish(R2SleighWireWriter *writer, size_t *out_len);

#endif
