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

use crate::contracts::{CanonicalStorageId, CanonicalStorageSpace, SourceMachineRoles};
use crate::{
    CapturedSourceFields, DiagnosticIdentity, FunctionIdentity, FunctionPresentation,
    MachineProfile, SourceEndianness,
};

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


const SPACE_RAM: u8 = 0;
const SPACE_REGISTER: u8 = 1;
const SPACE_UNIQUE: u8 = 2;
const SPACE_CONSTANT: u8 = 3;
const SPACE_CUSTOM: u8 = 4;
const SPACE_UNKNOWN: u8 = 5;

pub(crate) fn write_storage(writer: &mut SnapshotWireWriter, storage: CanonicalStorageId) {
    match storage.space {
        CanonicalStorageSpace::Ram => writer.u8(SPACE_RAM),
        CanonicalStorageSpace::Register => writer.u8(SPACE_REGISTER),
        CanonicalStorageSpace::Unique => writer.u8(SPACE_UNIQUE),
        CanonicalStorageSpace::Constant => writer.u8(SPACE_CONSTANT),
        CanonicalStorageSpace::Custom(index) => {
            writer.u8(SPACE_CUSTOM);
            writer.u32(index);
        }
        CanonicalStorageSpace::Unknown => writer.u8(SPACE_UNKNOWN),
    }
    writer.u64(storage.offset);
    writer.u32(storage.size);
}

pub(crate) fn read_storage(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<CanonicalStorageId, SnapshotWireError> {
    let space = match reader.u8()? {
        SPACE_RAM => CanonicalStorageSpace::Ram,
        SPACE_REGISTER => CanonicalStorageSpace::Register,
        SPACE_UNIQUE => CanonicalStorageSpace::Unique,
        SPACE_CONSTANT => CanonicalStorageSpace::Constant,
        SPACE_CUSTOM => CanonicalStorageSpace::Custom(reader.u32()?),
        SPACE_UNKNOWN => CanonicalStorageSpace::Unknown,
        // An unknown space is refused: mapping it onto a known one would move a
        // value into an address space it never lived in.
        _ => return Err(SnapshotWireError::ValueTooWide),
    };
    Ok(CanonicalStorageId {
        space,
        offset: reader.u64()?,
        size: reader.u32()?,
    })
}

pub(crate) fn write_optional_storage(
    writer: &mut SnapshotWireWriter,
    storage: Option<CanonicalStorageId>,
) {
    match storage {
        Some(storage) => {
            writer.bool(true);
            write_storage(writer, storage);
        }
        None => writer.bool(false),
    }
}

pub(crate) fn read_optional_storage(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<Option<CanonicalStorageId>, SnapshotWireError> {
    if reader.bool()? {
        Ok(Some(read_storage(reader)?))
    } else {
        Ok(None)
    }
}

pub(crate) fn write_presentation(
    writer: &mut SnapshotWireWriter,
    presentation: &FunctionPresentation,
) -> Result<(), SnapshotWireError> {
    writer.string(presentation.display_name())?;
    let count = u32::try_from(presentation.parameter_names().len())
        .map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(count);
    for name in presentation.parameter_names() {
        writer.string(name)?;
    }
    Ok(())
}

pub(crate) fn read_presentation(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<FunctionPresentation, SnapshotWireError> {
    let display_name = reader.string()?;
    let count = reader.u32()? as usize;
    let mut parameter_names = Vec::with_capacity(count.min(1024));
    for _ in 0..count {
        parameter_names.push(Box::<str>::from(reader.string()?));
    }
    Ok(FunctionPresentation {
        display_name: display_name.into(),
        parameter_names: parameter_names.into_boxed_slice(),
    })
}

// One bit per captured field, so adding a field costs a bit rather than a byte
// and an unset bit can never be mistaken for a set one.
const CAPTURED_BOUNDED_IMAGE: u16 = 1 << 0;
const CAPTURED_INTERFACE: u16 = 1 << 1;
const CAPTURED_EXACT_TYPES: u16 = 1 << 2;
const CAPTURED_EXACT_STACK_SLOT_ROLES: u16 = 1 << 3;
const CAPTURED_RETURN_ADDRESS: u16 = 1 << 4;
const CAPTURED_STACK_POINTER: u16 = 1 << 5;
const CAPTURED_FRAME_POINTER: u16 = 1 << 6;
const CAPTURED_RETURN_MECHANISM: u16 = 1 << 7;
const CAPTURED_STACK_ALLOCATION: u16 = 1 << 8;
const CAPTURED_KNOWN_BITS: u16 = CAPTURED_BOUNDED_IMAGE
    | CAPTURED_INTERFACE
    | CAPTURED_EXACT_TYPES
    | CAPTURED_EXACT_STACK_SLOT_ROLES
    | CAPTURED_RETURN_ADDRESS
    | CAPTURED_STACK_POINTER
    | CAPTURED_FRAME_POINTER
    | CAPTURED_RETURN_MECHANISM
    | CAPTURED_STACK_ALLOCATION;

pub(crate) fn write_captured_fields(writer: &mut SnapshotWireWriter, fields: CapturedSourceFields) {
    let mut mask = 0u16;
    let mut set = |bit: u16, present: bool| {
        if present {
            mask |= bit;
        }
    };
    set(CAPTURED_BOUNDED_IMAGE, fields.bounded_function_image);
    set(CAPTURED_INTERFACE, fields.function_interface);
    set(CAPTURED_EXACT_TYPES, fields.exact_function_types);
    set(CAPTURED_EXACT_STACK_SLOT_ROLES, fields.exact_stack_slot_roles);
    set(CAPTURED_RETURN_ADDRESS, fields.return_address_storage);
    set(CAPTURED_STACK_POINTER, fields.stack_pointer_storage);
    set(CAPTURED_FRAME_POINTER, fields.frame_pointer_storage);
    set(CAPTURED_RETURN_MECHANISM, fields.return_mechanism);
    set(CAPTURED_STACK_ALLOCATION, fields.stack_allocation_contract);
    writer.u16(mask);
}

pub(crate) fn read_captured_fields(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<CapturedSourceFields, SnapshotWireError> {
    let mask = reader.u16()?;
    // A bit this reader does not know means the producer captured something it
    // cannot represent, so the snapshot is refused rather than silently
    // downgraded to the fields it does understand.
    if mask & !CAPTURED_KNOWN_BITS != 0 {
        return Err(SnapshotWireError::ValueTooWide);
    }
    Ok(CapturedSourceFields {
        bounded_function_image: mask & CAPTURED_BOUNDED_IMAGE != 0,
        function_interface: mask & CAPTURED_INTERFACE != 0,
        exact_function_types: mask & CAPTURED_EXACT_TYPES != 0,
        exact_stack_slot_roles: mask & CAPTURED_EXACT_STACK_SLOT_ROLES != 0,
        return_address_storage: mask & CAPTURED_RETURN_ADDRESS != 0,
        stack_pointer_storage: mask & CAPTURED_STACK_POINTER != 0,
        frame_pointer_storage: mask & CAPTURED_FRAME_POINTER != 0,
        return_mechanism: mask & CAPTURED_RETURN_MECHANISM != 0,
        stack_allocation_contract: mask & CAPTURED_STACK_ALLOCATION != 0,
    })
}

pub(crate) fn write_machine_roles(writer: &mut SnapshotWireWriter, roles: &SourceMachineRoles) {
    write_optional_storage(writer, roles.return_address_storage());
    write_optional_storage(writer, roles.stack_pointer_storage());
}

pub(crate) fn read_machine_roles(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceMachineRoles, SnapshotWireError> {
    let return_address_storage = read_optional_storage(reader)?;
    let stack_pointer_storage = read_optional_storage(reader)?;
    // new() revalidates the register constraint, so a buffer cannot mint roles
    // the in-crate constructor would have rejected.
    SourceMachineRoles::new(return_address_storage, stack_pointer_storage)
        .map_err(|_| SnapshotWireError::ValueTooWide)
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

    #[test]
    fn every_storage_space_round_trips() {
        let spaces = [
            CanonicalStorageSpace::Ram,
            CanonicalStorageSpace::Register,
            CanonicalStorageSpace::Unique,
            CanonicalStorageSpace::Constant,
            CanonicalStorageSpace::Custom(7),
            CanonicalStorageSpace::Unknown,
        ];
        for space in spaces {
            let storage = CanonicalStorageId { space, offset: 0x38, size: 8 };
            let mut writer = SnapshotWireWriter::new();
            write_storage(&mut writer, storage);
            write_optional_storage(&mut writer, None);
            write_optional_storage(&mut writer, Some(storage));
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_storage(&mut reader).expect("storage"), storage);
            assert_eq!(read_optional_storage(&mut reader).expect("absent"), None);
            assert_eq!(
                read_optional_storage(&mut reader).expect("present"),
                Some(storage)
            );
            reader.finish().expect("consumed exactly");
        }
    }

    #[test]
    fn an_unknown_storage_space_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u8(200);
        writer.u64(0);
        writer.u32(8);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_storage(&mut reader).is_err());
    }

    #[test]
    fn presentation_round_trips_including_no_parameters() {
        for names in [Vec::new(), vec!["arr", "idx", "len"]] {
            let presentation = FunctionPresentation {
                display_name: "safe_array_access".into(),
                parameter_names: names
                    .iter()
                    .map(|name| Box::<str>::from(*name))
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            };
            let mut writer = SnapshotWireWriter::new();
            write_presentation(&mut writer, &presentation).expect("write");
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_presentation(&mut reader).expect("read"), presentation);
            reader.finish().expect("consumed exactly");
        }
    }

    #[test]
    fn captured_fields_round_trip_each_flag_independently() {
        let mut fields = CapturedSourceFields {
            bounded_function_image: true,
            function_interface: false,
            exact_function_types: true,
            exact_stack_slot_roles: false,
            return_address_storage: true,
            stack_pointer_storage: true,
            frame_pointer_storage: false,
            return_mechanism: true,
            stack_allocation_contract: false,
        };
        for _ in 0..2 {
            let mut writer = SnapshotWireWriter::new();
            write_captured_fields(&mut writer, fields);
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_captured_fields(&mut reader).expect("read"), fields);
            reader.finish().expect("consumed exactly");
            // flip every flag and round-trip the complement too
            fields = CapturedSourceFields {
                bounded_function_image: !fields.bounded_function_image,
                function_interface: !fields.function_interface,
                exact_function_types: !fields.exact_function_types,
                exact_stack_slot_roles: !fields.exact_stack_slot_roles,
                return_address_storage: !fields.return_address_storage,
                stack_pointer_storage: !fields.stack_pointer_storage,
                frame_pointer_storage: !fields.frame_pointer_storage,
                return_mechanism: !fields.return_mechanism,
                stack_allocation_contract: !fields.stack_allocation_contract,
            };
        }
    }

    #[test]
    fn a_captured_field_this_reader_does_not_know_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u16(CAPTURED_KNOWN_BITS | (1 << 12));
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_captured_fields(&mut reader).is_err());
    }

    #[test]
    fn machine_roles_round_trip_and_revalidate() {
        let sp = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0x20,
            size: 8,
        };
        let roles = SourceMachineRoles::new(Some(sp), Some(sp)).expect("roles");
        let mut writer = SnapshotWireWriter::new();
        write_machine_roles(&mut writer, &roles);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(read_machine_roles(&mut reader).expect("read"), roles);
        reader.finish().expect("consumed exactly");

        // a role in a non-register space must not survive the crossing
        let mut writer = SnapshotWireWriter::new();
        write_optional_storage(
            &mut writer,
            Some(CanonicalStorageId {
                space: CanonicalStorageSpace::Ram,
                offset: 0,
                size: 8,
            }),
        );
        write_optional_storage(&mut writer, None);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_machine_roles(&mut reader).is_err());
    }
}
