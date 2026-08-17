//! Flat wire encoding for one borrowed radare2 function snapshot.
//!
//! The accessor-table transport requires radare2 to implement one callback per
//! field so this crate can walk a snapshot lazily, which makes the C boundary
//! large and forces both sides to keep every struct size in step. This module
//! is the transport that replaces it: radare2 serializes a snapshot once into a
//! single self-describing buffer, and this crate parses it.
//!
//! The format is deliberately dull. Every integer is little-endian, every
//! string lives in one table and is referenced by index, and the header carries
//! the byte extents of both sections so a reader can reject a truncated or
//! mismatched buffer before interpreting a single record.
//!
//! This module owns the primitives only. Record layouts for the snapshot's own
//! parts are built on top of them.

use std::collections::BTreeMap;

/// Identifies a buffer as this transport before anything else is read.
pub const SNAPSHOT_WIRE_MAGIC: u32 = 0x5232_5357; // "R2SW"

/// Format revision. Owned by this crate, and bumped only when the encoding
/// changes; it is not radare2's ABI version, which moves for unrelated reasons.
pub const SNAPSHOT_WIRE_FORMAT_VERSION: u32 = 1;

/// Bytes of fixed header preceding the string table.
pub const SNAPSHOT_WIRE_HEADER_BYTES: usize = 24;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SnapshotWireError {
    /// The buffer is shorter than the fixed header.
    HeaderTruncated,
    /// The leading magic is not this transport.
    BadMagic(u32),
    /// The producer wrote a format revision this reader does not implement.
    UnsupportedVersion(u32),
    /// A section extent in the header does not fit the buffer.
    SectionOutOfBounds,
    /// A read asked for more bytes than the payload has left.
    PayloadTruncated,
    /// A string index has no entry in the table.
    UnknownString(u32),
    /// A string table entry is not valid UTF-8, or contains an interior NUL.
    InvalidString(u32),
    /// The payload had bytes left over after the reader finished.
    TrailingPayload(usize),
    /// A value did not fit the width the record declares for it.
    ValueTooWide,
}

impl std::fmt::Display for SnapshotWireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "snapshot wire decode failed: {self:?}")
    }
}

impl std::error::Error for SnapshotWireError {}

/// Builds one snapshot buffer.
///
/// Strings are interned, so a name repeated across records costs one table
/// entry and a four-byte reference at each use.
#[derive(Debug, Default)]
pub struct SnapshotWireWriter {
    payload: Vec<u8>,
    strings: Vec<String>,
    interned: BTreeMap<String, u32>,
}

impl SnapshotWireWriter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn u8(&mut self, value: u8) {
        self.payload.push(value);
    }

    pub fn bool(&mut self, value: bool) {
        self.u8(u8::from(value));
    }

    pub fn u16(&mut self, value: u16) {
        self.payload.extend_from_slice(&value.to_le_bytes());
    }

    pub fn u32(&mut self, value: u32) {
        self.payload.extend_from_slice(&value.to_le_bytes());
    }

    pub fn u64(&mut self, value: u64) {
        self.payload.extend_from_slice(&value.to_le_bytes());
    }

    pub fn i64(&mut self, value: i64) {
        self.payload.extend_from_slice(&value.to_le_bytes());
    }

    /// Write a length-prefixed byte run, for block bytes and opaque identities.
    pub fn bytes(&mut self, value: &[u8]) -> Result<(), SnapshotWireError> {
        let len = u32::try_from(value.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        self.u32(len);
        self.payload.extend_from_slice(value);
        Ok(())
    }

    /// Intern a string and write its table reference.
    pub fn string(&mut self, value: &str) -> Result<(), SnapshotWireError> {
        let id = self.intern(value)?;
        self.u32(id);
        Ok(())
    }

    /// Intern an optional string; absence is a reference no entry uses.
    pub fn optional_string(&mut self, value: Option<&str>) -> Result<(), SnapshotWireError> {
        match value {
            Some(value) => self.string(value),
            None => {
                self.u32(u32::MAX);
                Ok(())
            }
        }
    }

    fn intern(&mut self, value: &str) -> Result<u32, SnapshotWireError> {
        if let Some(id) = self.interned.get(value) {
            return Ok(*id);
        }
        let id = u32::try_from(self.strings.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        if id == u32::MAX {
            return Err(SnapshotWireError::ValueTooWide);
        }
        self.strings.push(value.to_string());
        self.interned.insert(value.to_string(), id);
        Ok(id)
    }

    /// Emit the finished buffer: header, string table, payload.
    pub fn finish(self) -> Result<Vec<u8>, SnapshotWireError> {
        let mut table = Vec::new();
        let count = u32::try_from(self.strings.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        for value in &self.strings {
            let len = u32::try_from(value.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
            table.extend_from_slice(&len.to_le_bytes());
            table.extend_from_slice(value.as_bytes());
        }
        let table_bytes = u32::try_from(table.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        let payload_bytes =
            u32::try_from(self.payload.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        let mut out = Vec::with_capacity(SNAPSHOT_WIRE_HEADER_BYTES + table.len() + self.payload.len());
        out.extend_from_slice(&SNAPSHOT_WIRE_MAGIC.to_le_bytes());
        out.extend_from_slice(&SNAPSHOT_WIRE_FORMAT_VERSION.to_le_bytes());
        out.extend_from_slice(&count.to_le_bytes());
        out.extend_from_slice(&table_bytes.to_le_bytes());
        out.extend_from_slice(&payload_bytes.to_le_bytes());
        out.extend_from_slice(&0u32.to_le_bytes()); // reserved, must stay zero
        debug_assert_eq!(out.len(), SNAPSHOT_WIRE_HEADER_BYTES);
        out.extend_from_slice(&table);
        out.extend_from_slice(&self.payload);
        Ok(out)
    }
}

/// Reads one snapshot buffer.
///
/// Every accessor is bounds-checked against the payload extent the header
/// declared, so a truncated buffer fails at the first short read rather than
/// yielding a plausible-looking record.
#[derive(Debug)]
pub struct SnapshotWireReader<'a> {
    strings: Vec<&'a str>,
    payload: &'a [u8],
    cursor: usize,
}

impl<'a> SnapshotWireReader<'a> {
    pub fn new(buffer: &'a [u8]) -> Result<Self, SnapshotWireError> {
        if buffer.len() < SNAPSHOT_WIRE_HEADER_BYTES {
            return Err(SnapshotWireError::HeaderTruncated);
        }
        let word = |at: usize| {
            u32::from_le_bytes([buffer[at], buffer[at + 1], buffer[at + 2], buffer[at + 3]])
        };
        let magic = word(0);
        if magic != SNAPSHOT_WIRE_MAGIC {
            return Err(SnapshotWireError::BadMagic(magic));
        }
        let version = word(4);
        if version != SNAPSHOT_WIRE_FORMAT_VERSION {
            return Err(SnapshotWireError::UnsupportedVersion(version));
        }
        let count = word(8) as usize;
        let table_bytes = word(12) as usize;
        let payload_bytes = word(16) as usize;
        if word(20) != 0 {
            return Err(SnapshotWireError::UnsupportedVersion(version));
        }
        let table_start = SNAPSHOT_WIRE_HEADER_BYTES;
        let table_end = table_start
            .checked_add(table_bytes)
            .ok_or(SnapshotWireError::SectionOutOfBounds)?;
        let payload_end = table_end
            .checked_add(payload_bytes)
            .ok_or(SnapshotWireError::SectionOutOfBounds)?;
        if payload_end != buffer.len() {
            return Err(SnapshotWireError::SectionOutOfBounds);
        }
        let mut strings = Vec::with_capacity(count);
        let table = &buffer[table_start..table_end];
        let mut at = 0usize;
        for index in 0..count {
            let id = u32::try_from(index).map_err(|_| SnapshotWireError::SectionOutOfBounds)?;
            if at + 4 > table.len() {
                return Err(SnapshotWireError::SectionOutOfBounds);
            }
            let len = u32::from_le_bytes([table[at], table[at + 1], table[at + 2], table[at + 3]])
                as usize;
            at += 4;
            let end = at
                .checked_add(len)
                .ok_or(SnapshotWireError::SectionOutOfBounds)?;
            if end > table.len() {
                return Err(SnapshotWireError::SectionOutOfBounds);
            }
            let text =
                std::str::from_utf8(&table[at..end]).map_err(|_| SnapshotWireError::InvalidString(id))?;
            if text.contains('\0') {
                return Err(SnapshotWireError::InvalidString(id));
            }
            strings.push(text);
            at = end;
        }
        if at != table.len() {
            return Err(SnapshotWireError::SectionOutOfBounds);
        }
        Ok(Self {
            strings,
            payload: &buffer[table_end..payload_end],
            cursor: 0,
        })
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], SnapshotWireError> {
        let end = self
            .cursor
            .checked_add(len)
            .ok_or(SnapshotWireError::PayloadTruncated)?;
        if end > self.payload.len() {
            return Err(SnapshotWireError::PayloadTruncated);
        }
        let slice = &self.payload[self.cursor..end];
        self.cursor = end;
        Ok(slice)
    }

    pub fn u8(&mut self) -> Result<u8, SnapshotWireError> {
        Ok(self.take(1)?[0])
    }

    pub fn bool(&mut self) -> Result<bool, SnapshotWireError> {
        Ok(self.u8()? != 0)
    }

    pub fn u16(&mut self) -> Result<u16, SnapshotWireError> {
        let bytes = self.take(2)?;
        Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
    }

    pub fn u32(&mut self) -> Result<u32, SnapshotWireError> {
        let bytes = self.take(4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    pub fn u64(&mut self) -> Result<u64, SnapshotWireError> {
        let bytes = self.take(8)?;
        let mut value = [0u8; 8];
        value.copy_from_slice(bytes);
        Ok(u64::from_le_bytes(value))
    }

    pub fn i64(&mut self) -> Result<i64, SnapshotWireError> {
        Ok(self.u64()? as i64)
    }

    pub fn bytes(&mut self) -> Result<&'a [u8], SnapshotWireError> {
        let len = self.u32()? as usize;
        self.take(len)
    }

    pub fn string(&mut self) -> Result<&'a str, SnapshotWireError> {
        let id = self.u32()?;
        self.strings
            .get(id as usize)
            .copied()
            .ok_or(SnapshotWireError::UnknownString(id))
    }

    pub fn optional_string(&mut self) -> Result<Option<&'a str>, SnapshotWireError> {
        let id = self.u32()?;
        if id == u32::MAX {
            return Ok(None);
        }
        self.strings
            .get(id as usize)
            .copied()
            .map(Some)
            .ok_or(SnapshotWireError::UnknownString(id))
    }

    /// Assert the producer and reader agreed on the record set exactly.
    pub fn finish(self) -> Result<(), SnapshotWireError> {
        let left = self.payload.len() - self.cursor;
        if left == 0 {
            Ok(())
        } else {
            Err(SnapshotWireError::TrailingPayload(left))
        }
    }
}


// ---------------------------------------------------------------------------
// Record layouts
//
// Each part of a snapshot gets one encode/decode pair here. Decoding rebuilds
// the same in-crate value the accessor walk produced, so the parser is a drop-in
// replacement for that pass rather than a second, parallel representation.
// ---------------------------------------------------------------------------

use crate::{DiagnosticIdentity, FunctionIdentity, MachineProfile, SourceEndianness};

const ENDIAN_LITTLE: u8 = 0;
const ENDIAN_BIG: u8 = 1;

pub(crate) fn write_machine_profile(
    writer: &mut SnapshotWireWriter,
    profile: &MachineProfile,
) -> Result<(), SnapshotWireError> {
    writer.string(profile.arch_id())?;
    writer.string(profile.cpu_id())?;
    writer.u32(profile.bits());
    writer.u8(match profile.endianness() {
        SourceEndianness::Little => ENDIAN_LITTLE,
        SourceEndianness::Big => ENDIAN_BIG,
    });
    Ok(())
}

pub(crate) fn read_machine_profile(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<MachineProfile, SnapshotWireError> {
    let arch_id = reader.string()?;
    let cpu_id = reader.string()?;
    let bits = reader.u32()?;
    let endianness = match reader.u8()? {
        ENDIAN_LITTLE => SourceEndianness::Little,
        ENDIAN_BIG => SourceEndianness::Big,
        // An unrecognized discriminant is refused rather than defaulted: a
        // guessed byte order would silently reinterpret every value.
        _ => return Err(SnapshotWireError::ValueTooWide),
    };
    Ok(MachineProfile {
        arch_id: arch_id.into(),
        cpu_id: cpu_id.into(),
        bits,
        endianness,
    })
}

pub(crate) fn write_function_identity(
    writer: &mut SnapshotWireWriter,
    identity: &FunctionIdentity,
) {
    writer.u64(identity.address());
}

pub(crate) fn read_function_identity(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<FunctionIdentity, SnapshotWireError> {
    Ok(FunctionIdentity {
        address: reader.u64()?,
    })
}

pub(crate) fn write_diagnostic_identity(
    writer: &mut SnapshotWireWriter,
    identity: DiagnosticIdentity,
) {
    writer.u64(identity.value());
}

pub(crate) fn read_diagnostic_identity(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<DiagnosticIdentity, SnapshotWireError> {
    Ok(DiagnosticIdentity(reader.u64()?))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitives_round_trip_in_written_order() {
        let mut writer = SnapshotWireWriter::new();
        writer.u8(0x7f);
        writer.bool(true);
        writer.bool(false);
        writer.u16(0xbeef);
        writer.u32(0xdead_beef);
        writer.u64(0x0123_4567_89ab_cdef);
        writer.i64(-2);
        writer.bytes(&[1, 2, 3]).expect("bytes");
        writer.string("rdi").expect("string");
        writer.optional_string(None).expect("absent");
        writer.optional_string(Some("len")).expect("present");
        let buffer = writer.finish().expect("finish");

        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(reader.u8().expect("u8"), 0x7f);
        assert!(reader.bool().expect("true"));
        assert!(!reader.bool().expect("false"));
        assert_eq!(reader.u16().expect("u16"), 0xbeef);
        assert_eq!(reader.u32().expect("u32"), 0xdead_beef);
        assert_eq!(reader.u64().expect("u64"), 0x0123_4567_89ab_cdef);
        assert_eq!(reader.i64().expect("i64"), -2);
        assert_eq!(reader.bytes().expect("bytes"), &[1, 2, 3]);
        assert_eq!(reader.string().expect("string"), "rdi");
        assert_eq!(reader.optional_string().expect("absent"), None);
        assert_eq!(reader.optional_string().expect("present"), Some("len"));
        reader.finish().expect("consumed exactly");
    }

    #[test]
    fn repeated_strings_share_one_table_entry() {
        let mut writer = SnapshotWireWriter::new();
        for _ in 0..8 {
            writer.string("rsp").expect("string");
        }
        writer.string("rbp").expect("string");
        let buffer = writer.finish().expect("finish");
        // two entries in the table, nine references in the payload
        assert_eq!(u32::from_le_bytes([buffer[8], buffer[9], buffer[10], buffer[11]]), 2);
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        for _ in 0..8 {
            assert_eq!(reader.string().expect("string"), "rsp");
        }
        assert_eq!(reader.string().expect("string"), "rbp");
        reader.finish().expect("consumed exactly");
    }

    #[test]
    fn a_truncated_buffer_is_rejected_rather_than_read_short() {
        let mut writer = SnapshotWireWriter::new();
        writer.u64(1);
        let buffer = writer.finish().expect("finish");
        for len in 0..buffer.len() {
            assert!(
                SnapshotWireReader::new(&buffer[..len]).is_err(),
                "prefix of {len} bytes must not parse"
            );
        }
    }

    #[test]
    fn a_foreign_or_future_buffer_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u32(7);
        let good = writer.finish().expect("finish");

        let mut bad_magic = good.clone();
        bad_magic[0] ^= 0xff;
        assert!(matches!(
            SnapshotWireReader::new(&bad_magic),
            Err(SnapshotWireError::BadMagic(_))
        ));

        let mut bad_version = good.clone();
        bad_version[4] = bad_version[4].wrapping_add(1);
        assert!(matches!(
            SnapshotWireReader::new(&bad_version),
            Err(SnapshotWireError::UnsupportedVersion(_))
        ));

        let mut reserved_set = good;
        reserved_set[20] = 1;
        assert!(SnapshotWireReader::new(&reserved_set).is_err());
    }

    #[test]
    fn an_unknown_string_reference_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u32(3); // no string was interned, so id 3 cannot resolve
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(matches!(
            reader.string(),
            Err(SnapshotWireError::UnknownString(3))
        ));
    }

    #[test]
    fn payload_left_unread_is_reported_rather_than_ignored() {
        let mut writer = SnapshotWireWriter::new();
        writer.u32(1);
        writer.u32(2);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(reader.u32().expect("first"), 1);
        assert!(matches!(
            reader.finish(),
            Err(SnapshotWireError::TrailingPayload(4))
        ));
    }

    #[test]
    fn reading_past_the_payload_fails_at_the_short_read() {
        let mut writer = SnapshotWireWriter::new();
        writer.u16(9);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(reader.u16().expect("u16"), 9);
        assert!(matches!(
            reader.u32(),
            Err(SnapshotWireError::PayloadTruncated)
        ));
    }

    #[test]
    fn machine_profile_round_trips_both_byte_orders() {
        for endianness in [SourceEndianness::Little, SourceEndianness::Big] {
            let profile = MachineProfile {
                arch_id: "x86".into(),
                cpu_id: "x86-64".into(),
                bits: 64,
                endianness,
            };
            let mut writer = SnapshotWireWriter::new();
            write_machine_profile(&mut writer, &profile).expect("write");
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_machine_profile(&mut reader).expect("read"), profile);
            reader.finish().expect("consumed exactly");
        }
    }

    #[test]
    fn an_unknown_byte_order_is_refused_not_defaulted() {
        let mut writer = SnapshotWireWriter::new();
        writer.string("x86").expect("arch");
        writer.string("x86-64").expect("cpu");
        writer.u32(64);
        writer.u8(9);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_machine_profile(&mut reader).is_err());
    }

    #[test]
    fn identities_round_trip() {
        let function = FunctionIdentity { address: 0x1000_07c0 };
        let diagnostic = DiagnosticIdentity(0xfeed_face_dead_beef);
        let mut writer = SnapshotWireWriter::new();
        write_function_identity(&mut writer, &function);
        write_diagnostic_identity(&mut writer, diagnostic);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(read_function_identity(&mut reader).expect("fn"), function);
        assert_eq!(
            read_diagnostic_identity(&mut reader).expect("diag"),
            diagnostic
        );
        reader.finish().expect("consumed exactly");
    }
}
