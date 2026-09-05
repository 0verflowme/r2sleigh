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
use std::sync::Arc;

/// Identifies a buffer as this transport before anything else is read.
pub const SNAPSHOT_WIRE_MAGIC: u32 = 0x5232_5357; // "R2SW"

/// Format revision. Owned by this crate, and bumped only when the encoding
/// changes; it is not radare2's ABI version, which moves for unrelated reasons.
pub const SNAPSHOT_WIRE_FORMAT_VERSION: u32 = 9;
const SNAPSHOT_WIRE_MIN_FORMAT_VERSION: u32 = 1;

/// Bytes of fixed header preceding the string table.
pub const SNAPSHOT_WIRE_HEADER_BYTES: usize = 24;

#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// A tag names a case this schema does not define; `record` says which record it came from.
    UnknownDiscriminant { record: &'static str, tag: u64 },
    /// The bytes decoded but the contract refused them; `contract` names the constructor that said no and `reason` says what it objected to.
    RejectedContract {
        contract: &'static str,
        reason: String,
    },
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
        let count =
            u32::try_from(self.strings.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        for value in &self.strings {
            let len = u32::try_from(value.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
            table.extend_from_slice(&len.to_le_bytes());
            table.extend_from_slice(value.as_bytes());
        }
        let table_bytes =
            u32::try_from(table.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        let payload_bytes =
            u32::try_from(self.payload.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        let mut out =
            Vec::with_capacity(SNAPSHOT_WIRE_HEADER_BYTES + table.len() + self.payload.len());
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
    format_version: u32,
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
        if !(SNAPSHOT_WIRE_MIN_FORMAT_VERSION..=SNAPSHOT_WIRE_FORMAT_VERSION).contains(&version) {
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
            let text = std::str::from_utf8(&table[at..end])
                .map_err(|_| SnapshotWireError::InvalidString(id))?;
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
            format_version: version,
            strings,
            payload: &buffer[table_end..payload_end],
            cursor: 0,
        })
    }

    pub const fn format_version(&self) -> u32 {
        self.format_version
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

use crate::contracts::{
    CanonicalStorageId, CanonicalStorageSpace, SourceAbiClass, SourceAbiParameterSpec,
    SourceAggregateLayout, SourceAggregateMember, SourceCallArgumentSpec,
    SourceCallPreservedCarriers, SourceCallResult, SourceCarrierKind, SourceCarrierProjection,
    SourceConventionSlots, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
    SourceMachineRoles, SourceRegisterName, SourceReturnMechanism, SourceRoleRegisterNames,
    SourceStackAllocationContract, SourceStackGrowth, SourceStackSlotRole, SourceStackSlotSpec,
    SourceType, SourceTypeGraph, SourceTypeKind, StackAddressBase,
};
use crate::{
    AdvisoryCallPrototype, AdvisoryCallSite, AdvisoryCallTransfer, AdvisorySuccessor,
    AdvisorySuccessorKind, CapturedSourceFields, DiagnosticIdentity, FunctionIdentity,
    FunctionPresentation, MachineProfile, OwnedFunctionBlock, OwnedFunctionImage,
    OwnedFunctionSnapshot, SnapshotValidationError, SourceCodePointerTable, SourceDataObject,
    SourceEndianness, SourceSignatureParameter, SourceSignaturePresentation, SourceStackSlotName,
};

const ENDIAN_LITTLE: u8 = 0;
const ENDIAN_BIG: u8 = 1;

const ABI_UNKNOWN: u8 = 0;
const ABI_OTHER: u8 = 1;
const ABI_MICROSOFT: u8 = 2;
const ABI_MICROSOFT_X64: u8 = 3;
const ABI_SYSTEM_V: u8 = 4;
const ABI_SYSTEM_V_AMD64: u8 = 5;
const ABI_AAPCS: u8 = 6;
const ABI_AAPCS64: u8 = 7;
const ABI_RISCV32: u8 = 8;
const ABI_RISCV64: u8 = 9;
const ABI_CDECL: u8 = 10;
const ABI_STDCALL: u8 = 11;
const ABI_FASTCALL: u8 = 12;
const ABI_THISCALL: u8 = 13;
const ABI_VECTORCALL: u8 = 14;

fn write_abi_class(writer: &mut SnapshotWireWriter, abi_class: SourceAbiClass) {
    writer.u8(match abi_class {
        SourceAbiClass::Unknown => ABI_UNKNOWN,
        SourceAbiClass::Other => ABI_OTHER,
        SourceAbiClass::Microsoft => ABI_MICROSOFT,
        SourceAbiClass::MicrosoftX64 => ABI_MICROSOFT_X64,
        SourceAbiClass::SystemV => ABI_SYSTEM_V,
        SourceAbiClass::SystemVAMD64 => ABI_SYSTEM_V_AMD64,
        SourceAbiClass::Aapcs => ABI_AAPCS,
        SourceAbiClass::Aapcs64 => ABI_AAPCS64,
        SourceAbiClass::RiscV32 => ABI_RISCV32,
        SourceAbiClass::RiscV64 => ABI_RISCV64,
        SourceAbiClass::Cdecl => ABI_CDECL,
        SourceAbiClass::Stdcall => ABI_STDCALL,
        SourceAbiClass::Fastcall => ABI_FASTCALL,
        SourceAbiClass::Thiscall => ABI_THISCALL,
        SourceAbiClass::Vectorcall => ABI_VECTORCALL,
    });
}

fn read_abi_class(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceAbiClass, SnapshotWireError> {
    match reader.u8()? {
        ABI_UNKNOWN => Ok(SourceAbiClass::Unknown),
        ABI_OTHER => Ok(SourceAbiClass::Other),
        ABI_MICROSOFT => Ok(SourceAbiClass::Microsoft),
        ABI_MICROSOFT_X64 => Ok(SourceAbiClass::MicrosoftX64),
        ABI_SYSTEM_V => Ok(SourceAbiClass::SystemV),
        ABI_SYSTEM_V_AMD64 => Ok(SourceAbiClass::SystemVAMD64),
        ABI_AAPCS => Ok(SourceAbiClass::Aapcs),
        ABI_AAPCS64 => Ok(SourceAbiClass::Aapcs64),
        ABI_RISCV32 => Ok(SourceAbiClass::RiscV32),
        ABI_RISCV64 => Ok(SourceAbiClass::RiscV64),
        ABI_CDECL => Ok(SourceAbiClass::Cdecl),
        ABI_STDCALL => Ok(SourceAbiClass::Stdcall),
        ABI_FASTCALL => Ok(SourceAbiClass::Fastcall),
        ABI_THISCALL => Ok(SourceAbiClass::Thiscall),
        ABI_VECTORCALL => Ok(SourceAbiClass::Vectorcall),
        tag => Err(SnapshotWireError::UnknownDiscriminant {
            record: "source ABI class",
            tag: u64::from(tag),
        }),
    }
}

fn read_recorded_abi_class(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<Option<SourceAbiClass>, SnapshotWireError> {
    // Version 2 briefly recorded both the spelling and a derived ABI class.
    // Later formats keep the spelling as the sole transported fact and let
    // SourceAbiClass classify it once at the source contract boundary.
    (reader.format_version() == 2)
        .then(|| read_abi_class(reader))
        .transpose()
}

fn verify_recorded_abi_class(
    recorded: Option<SourceAbiClass>,
    classified: SourceAbiClass,
    contract: &'static str,
) -> Result<(), SnapshotWireError> {
    if recorded.is_some_and(|recorded| recorded != classified) {
        return Err(SnapshotWireError::RejectedContract {
            contract,
            reason: "calling-convention spelling and typed ABI class disagree".to_string(),
        });
    }
    Ok(())
}

pub fn write_machine_profile(
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

pub fn read_machine_profile(
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
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "machine endianness",
                tag: u64::from(tag),
            });
        }
    };
    Ok(MachineProfile {
        arch_id: arch_id.into(),
        cpu_id: cpu_id.into(),
        bits,
        endianness,
    })
}

pub fn write_function_identity(writer: &mut SnapshotWireWriter, identity: &FunctionIdentity) {
    writer.u64(identity.address());
}

pub fn read_function_identity(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<FunctionIdentity, SnapshotWireError> {
    Ok(FunctionIdentity {
        address: reader.u64()?,
    })
}

pub fn write_diagnostic_identity(writer: &mut SnapshotWireWriter, identity: DiagnosticIdentity) {
    writer.u64(identity.value());
}

pub fn read_diagnostic_identity(
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

pub fn write_storage(writer: &mut SnapshotWireWriter, storage: CanonicalStorageId) {
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

pub fn read_storage(
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
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "storage space",
                tag: u64::from(tag),
            });
        }
    };
    Ok(CanonicalStorageId {
        space,
        offset: reader.u64()?,
        size: reader.u32()?,
    })
}

pub fn write_optional_storage(
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

pub fn read_optional_storage(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<Option<CanonicalStorageId>, SnapshotWireError> {
    if reader.bool()? {
        Ok(Some(read_storage(reader)?))
    } else {
        Ok(None)
    }
}

/// A role carrier, written with the register spelling that survives the trip.
///
/// The offset beside it is stated in the producer's own register numbering,
/// which is not the numbering the lifted architecture uses for the same
/// register. The name is what the consumer resolves; the offset is carried only
/// so an older consumer keeps reading what it always read.
fn write_named_optional_storage(
    writer: &mut SnapshotWireWriter,
    storage: Option<CanonicalStorageId>,
    name: Option<SourceRegisterName>,
    format_version: u32,
) -> Result<(), SnapshotWireError> {
    write_optional_storage(writer, storage);
    if storage.is_some() && format_version >= 5 {
        writer.string(name.as_ref().map_or("", SourceRegisterName::as_str))?;
    }
    Ok(())
}

fn read_named_optional_storage(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<(Option<CanonicalStorageId>, Option<SourceRegisterName>), SnapshotWireError> {
    let storage = read_optional_storage(reader)?;
    if storage.is_some() && reader.format_version() >= 5 {
        let name = SourceRegisterName::new(reader.string()?);
        return Ok((storage, name));
    }
    Ok((storage, None))
}

pub fn write_presentation(
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
    let slots = u32::try_from(presentation.stack_slot_names().len())
        .map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(slots);
    for slot_name in presentation.stack_slot_names() {
        writer.u8(match slot_name.base() {
            StackAddressBase::FramePointer => BASE_FRAME_POINTER,
            StackAddressBase::StackPointer => BASE_STACK_POINTER,
        });
        writer.i64(slot_name.offset());
        writer.string(slot_name.name())?;
        writer.optional_string(slot_name.type_spelling())?;
    }
    write_signature_presentation(writer, presentation.signature())?;
    let callees = u32::try_from(presentation.callee_signatures().len())
        .map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(callees);
    for (name, signature) in presentation.callee_signatures() {
        writer.string(name)?;
        write_signature_presentation(writer, Some(signature))?;
    }
    Ok(())
}

fn write_signature_presentation(
    writer: &mut SnapshotWireWriter,
    signature: Option<&SourceSignaturePresentation>,
) -> Result<(), SnapshotWireError> {
    let Some(signature) = signature else {
        writer.bool(false);
        return Ok(());
    };
    writer.bool(true);
    writer.optional_string(signature.return_type())?;
    writer.optional_string(signature.calling_convention())?;
    writer.bool(signature.noreturn());
    let count =
        u32::try_from(signature.parameters().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(count);
    for parameter in signature.parameters() {
        writer.optional_string(parameter.name())?;
        writer.optional_string(parameter.type_spelling())?;
    }
    Ok(())
}

fn read_signature_presentation(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<Option<SourceSignaturePresentation>, SnapshotWireError> {
    if !reader.bool()? {
        return Ok(None);
    }
    let return_type = reader.optional_string()?.map(str::to_string);
    let calling_convention = reader.optional_string()?.map(str::to_string);
    let noreturn = reader.bool()?;
    let count = reader.u32()? as usize;
    let mut parameters = Vec::with_capacity(count.min(1024));
    for _ in 0..count {
        let name = reader.optional_string()?.map(str::to_string);
        let type_spelling = reader.optional_string()?.map(str::to_string);
        parameters.push(SourceSignatureParameter::new(name, type_spelling));
    }
    Ok(Some(SourceSignaturePresentation::new(
        return_type,
        calling_convention,
        noreturn,
        parameters,
    )))
}

pub fn read_presentation(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<FunctionPresentation, SnapshotWireError> {
    let display_name = reader.string()?;
    let count = reader.u32()? as usize;
    let mut parameter_names = Vec::with_capacity(count.min(1024));
    for _ in 0..count {
        parameter_names.push(Box::<str>::from(reader.string()?));
    }
    let slot_count = reader.u32()? as usize;
    let mut stack_slot_names = Vec::with_capacity(slot_count.min(4096));
    for _ in 0..slot_count {
        let base = match reader.u8()? {
            BASE_FRAME_POINTER => StackAddressBase::FramePointer,
            BASE_STACK_POINTER => StackAddressBase::StackPointer,
            tag => {
                return Err(SnapshotWireError::UnknownDiscriminant {
                    record: "stack slot name base",
                    tag: u64::from(tag),
                });
            }
        };
        let offset = reader.i64()?;
        let name = reader.string()?.to_string();
        let type_spelling = reader.optional_string()?.map(str::to_string);
        stack_slot_names
            .push(SourceStackSlotName::new(base, offset, name).with_type_spelling(type_spelling));
    }
    let signature = read_signature_presentation(reader)?;
    let callee_count = reader.u32()? as usize;
    let mut callee_signatures = Vec::with_capacity(callee_count.min(4096));
    for _ in 0..callee_count {
        let name = Box::<str>::from(reader.string()?);
        let Some(signature) = read_signature_presentation(reader)? else {
            return Err(SnapshotWireError::RejectedContract {
                contract: "SourceSignaturePresentation",
                reason: "the record carried no signature".to_string(),
            });
        };
        callee_signatures.push((name, signature));
    }
    Ok(FunctionPresentation {
        display_name: display_name.into(),
        parameter_names: parameter_names.into_boxed_slice(),
        stack_slot_names: stack_slot_names.into_boxed_slice(),
        signature,
        callee_signatures: callee_signatures.into_boxed_slice(),
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

pub fn write_captured_fields(writer: &mut SnapshotWireWriter, fields: CapturedSourceFields) {
    let mut mask = 0u16;
    let mut set = |bit: u16, present: bool| {
        if present {
            mask |= bit;
        }
    };
    set(CAPTURED_BOUNDED_IMAGE, fields.bounded_function_image);
    set(CAPTURED_INTERFACE, fields.function_interface);
    set(CAPTURED_EXACT_TYPES, fields.exact_function_types);
    set(
        CAPTURED_EXACT_STACK_SLOT_ROLES,
        fields.exact_stack_slot_roles,
    );
    set(CAPTURED_RETURN_ADDRESS, fields.return_address_storage);
    set(CAPTURED_STACK_POINTER, fields.stack_pointer_storage);
    set(CAPTURED_FRAME_POINTER, fields.frame_pointer_storage);
    set(CAPTURED_RETURN_MECHANISM, fields.return_mechanism);
    set(CAPTURED_STACK_ALLOCATION, fields.stack_allocation_contract);
    writer.u16(mask);
}

pub fn read_captured_fields(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<CapturedSourceFields, SnapshotWireError> {
    let mask = reader.u16()?;
    // A bit this reader does not know means the producer captured something it
    // cannot represent, so the snapshot is refused rather than silently
    // downgraded to the fields it does understand.
    if mask & !CAPTURED_KNOWN_BITS != 0 {
        return Err(SnapshotWireError::UnknownDiscriminant {
            record: "captured fields",
            tag: u64::from(mask & !CAPTURED_KNOWN_BITS),
        });
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

pub fn write_machine_roles(
    writer: &mut SnapshotWireWriter,
    roles: &SourceMachineRoles,
) -> Result<(), SnapshotWireError> {
    write_machine_roles_for_format(writer, roles, SNAPSHOT_WIRE_FORMAT_VERSION)
}

fn write_machine_roles_for_format(
    writer: &mut SnapshotWireWriter,
    roles: &SourceMachineRoles,
    format_version: u32,
) -> Result<(), SnapshotWireError> {
    let names = roles.role_register_names();
    write_named_optional_storage(
        writer,
        roles.return_address_storage(),
        names.return_address().and_then(SourceRegisterName::new),
        format_version,
    )?;
    write_named_optional_storage(
        writer,
        roles.stack_pointer_storage(),
        names.stack_pointer().and_then(SourceRegisterName::new),
        format_version,
    )?;
    if format_version >= 3 {
        match roles.stack_allocation_contract() {
            Some(contract) => {
                writer.bool(true);
                write_stack_allocation(writer, &contract);
            }
            None => writer.bool(false),
        }
    }
    // Whether a call leaves the frame carriers alone. A convention fact, and it
    // travels with the roles rather than with the interface because the source
    // publishes it for functions whose interface it withholds -- which are the
    // functions that need it.
    if format_version >= 4 {
        match roles.call_preserved_carriers() {
            Some(carriers) => {
                writer.bool(true);
                writer.bool(carriers.stack_pointer());
                writer.bool(carriers.frame_pointer());
            }
            None => writer.bool(false),
        }
    }
    Ok(())
}

pub fn read_machine_roles(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceMachineRoles, SnapshotWireError> {
    read_machine_roles_with_legacy_contract(reader, None)
}

fn read_machine_roles_with_legacy_contract(
    reader: &mut SnapshotWireReader<'_>,
    legacy_contract: Option<SourceStackAllocationContract>,
) -> Result<SourceMachineRoles, SnapshotWireError> {
    let (return_address_storage, return_address_name) = read_named_optional_storage(reader)?;
    let (stack_pointer_storage, stack_pointer_name) = read_named_optional_storage(reader)?;
    let contract = if reader.format_version() >= 3 {
        if reader.bool()? {
            Some(read_stack_allocation(reader)?)
        } else {
            None
        }
    } else {
        legacy_contract
    };
    let carriers = if reader.format_version() >= 4 && reader.bool()? {
        Some(SourceCallPreservedCarriers::new(
            reader.bool()?,
            reader.bool()?,
        ))
    } else {
        None
    };
    // new() revalidates the register constraint, so a buffer cannot mint roles
    // the in-crate constructor would have rejected.
    let mut roles = SourceMachineRoles::new(return_address_storage, stack_pointer_storage)
        .map_err(|error| SnapshotWireError::RejectedContract {
            contract: "SourceMachineRoles::new",
            reason: format!("{error:?}"),
        })?;
    if let Some(contract) = contract {
        roles = roles
            .with_stack_allocation_contract(contract)
            .map_err(|error| SnapshotWireError::RejectedContract {
                contract: "SourceMachineRoles::with_stack_allocation_contract",
                reason: format!("{error:?}"),
            })?;
    }
    if let Some(carriers) = carriers {
        roles = roles.with_call_preserved_carriers(carriers);
    }
    Ok(roles.with_role_register_names(SourceRoleRegisterNames::new(
        return_address_name.as_ref().map(SourceRegisterName::as_str),
        stack_pointer_name.as_ref().map(SourceRegisterName::as_str),
        None,
    )))
}

pub fn write_convention_slots(
    writer: &mut SnapshotWireWriter,
    slots: &SourceConventionSlots,
) -> Result<(), SnapshotWireError> {
    write_convention_slots_for_format(writer, slots, SNAPSHOT_WIRE_FORMAT_VERSION)
}

fn write_convention_slots_for_format(
    writer: &mut SnapshotWireWriter,
    slots: &SourceConventionSlots,
    format_version: u32,
) -> Result<(), SnapshotWireError> {
    let count =
        u32::try_from(slots.argument_slots().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.string(slots.calling_convention())?;
    if format_version == 2 {
        write_abi_class(writer, slots.abi_class());
    }
    writer.u32(count);
    for storage in slots.argument_slots() {
        write_storage(writer, *storage);
    }
    write_optional_storage(writer, slots.result_slot());
    Ok(())
}

pub fn read_convention_slots(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceConventionSlots, SnapshotWireError> {
    let calling_convention = reader.string()?.to_string();
    let recorded_abi_class = read_recorded_abi_class(reader)?;
    let count = reader.u32()? as usize;
    let mut argument_slots = Vec::with_capacity(count.min(64));
    for _ in 0..count {
        argument_slots.push(read_storage(reader)?);
    }
    let result_slot = read_optional_storage(reader)?;
    // new() revalidates, so a buffer cannot mint candidate slots the in-crate
    // constructor would have rejected.
    let slots = SourceConventionSlots::new(calling_convention, argument_slots, result_slot)
        .map_err(|error| SnapshotWireError::RejectedContract {
            contract: "SourceConventionSlots::new",
            reason: format!("{error:?}"),
        })?;
    verify_recorded_abi_class(
        recorded_abi_class,
        slots.abi_class(),
        "SourceConventionSlots ABI class",
    )?;
    Ok(slots)
}

const SUCCESSOR_DIRECT: u8 = 0;
const SUCCESSOR_FALLTHROUGH: u8 = 1;
const SUCCESSOR_SWITCH_CASE: u8 = 2;
const SUCCESSOR_SWITCH_DEFAULT: u8 = 3;

pub fn write_successor(writer: &mut SnapshotWireWriter, successor: &AdvisorySuccessor) {
    writer.u8(match successor.kind() {
        AdvisorySuccessorKind::Direct => SUCCESSOR_DIRECT,
        AdvisorySuccessorKind::Fallthrough => SUCCESSOR_FALLTHROUGH,
        AdvisorySuccessorKind::SwitchCase => SUCCESSOR_SWITCH_CASE,
        AdvisorySuccessorKind::SwitchDefault => SUCCESSOR_SWITCH_DEFAULT,
    });
    writer.u64(successor.target());
    match successor.case_value() {
        Some(value) => {
            writer.bool(true);
            writer.u64(value);
        }
        None => writer.bool(false),
    }
    writer.bool(successor.is_external());
}

pub fn read_successor(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<AdvisorySuccessor, SnapshotWireError> {
    let kind = match reader.u8()? {
        SUCCESSOR_DIRECT => AdvisorySuccessorKind::Direct,
        SUCCESSOR_FALLTHROUGH => AdvisorySuccessorKind::Fallthrough,
        SUCCESSOR_SWITCH_CASE => AdvisorySuccessorKind::SwitchCase,
        SUCCESSOR_SWITCH_DEFAULT => AdvisorySuccessorKind::SwitchDefault,
        // Edge kind decides control flow, so an unknown one is refused rather
        // than folded into a direct edge.
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "successor kind",
                tag: u64::from(tag),
            });
        }
    };
    let target = reader.u64()?;
    let case_value = if reader.bool()? {
        Some(reader.u64()?)
    } else {
        None
    };
    let external = reader.bool()?;
    Ok(AdvisorySuccessor {
        kind,
        target,
        case_value,
        external,
    })
}

pub fn write_block(
    writer: &mut SnapshotWireWriter,
    block: &OwnedFunctionBlock,
) -> Result<(), SnapshotWireError> {
    writer.u64(block.address());
    writer.bytes(block.bytes())?;
    let count =
        u32::try_from(block.successors().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(count);
    for successor in block.successors() {
        write_successor(writer, successor);
    }
    match block.switch_instruction() {
        Some(address) => {
            writer.bool(true);
            writer.u64(address);
        }
        None => writer.bool(false),
    }
    Ok(())
}

pub fn read_block(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<OwnedFunctionBlock, SnapshotWireError> {
    let address = reader.u64()?;
    let bytes: Arc<[u8]> = Arc::from(reader.bytes()?);
    let count = reader.u32()? as usize;
    let mut successors = Vec::with_capacity(count.min(4096));
    for _ in 0..count {
        successors.push(read_successor(reader)?);
    }
    let switch_instruction = if reader.bool()? {
        Some(reader.u64()?)
    } else {
        None
    };
    Ok(OwnedFunctionBlock {
        address,
        bytes,
        successors: successors.into_boxed_slice(),
        switch_instruction,
    })
}

pub fn write_image(
    writer: &mut SnapshotWireWriter,
    image: &OwnedFunctionImage,
) -> Result<(), SnapshotWireError> {
    write_image_for_format(writer, image, SNAPSHOT_WIRE_FORMAT_VERSION)
}

fn write_image_for_format(
    writer: &mut SnapshotWireWriter,
    image: &OwnedFunctionImage,
    format_version: u32,
) -> Result<(), SnapshotWireError> {
    writer.u64(image.entry_address());
    let blocks =
        u32::try_from(image.blocks().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(blocks);
    for block in image.blocks() {
        write_block(writer, block)?;
    }
    let exits =
        u32::try_from(image.external_exits().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(exits);
    for exit in image.external_exits() {
        writer.u64(*exit);
    }
    let literals = u32::try_from(image.string_literals().len())
        .map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(literals);
    for (addr, text) in image.string_literals() {
        writer.u64(*addr);
        writer.string(text)?;
    }
    let symbols =
        u32::try_from(image.data_symbols().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(symbols);
    for object in image.data_symbols() {
        writer.u64(object.address());
        writer.string(object.name())?;
        if format_version >= 8 {
            writer.optional_string(object.type_spelling())?;
        }
    }
    let tables = u32::try_from(image.code_pointer_tables().len())
        .map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(tables);
    for table in image.code_pointer_tables() {
        writer.u64(table.address());
        writer.u32(table.entry_size());
        let targets =
            u32::try_from(table.targets().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
        writer.u32(targets);
        for target in table.targets() {
            writer.u64(*target);
        }
    }
    let total =
        u64::try_from(image.total_source_bytes()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u64(total);
    Ok(())
}

pub fn read_image(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<OwnedFunctionImage, SnapshotWireError> {
    let entry_address = reader.u64()?;
    let block_count = reader.u32()? as usize;
    let mut blocks = Vec::with_capacity(block_count.min(4096));
    for _ in 0..block_count {
        blocks.push(read_block(reader)?);
    }
    let exit_count = reader.u32()? as usize;
    let mut external_exits = Vec::with_capacity(exit_count.min(4096));
    for _ in 0..exit_count {
        external_exits.push(reader.u64()?);
    }
    let literal_count = reader.u32()? as usize;
    let mut string_literals = Vec::with_capacity(literal_count.min(4096));
    for _ in 0..literal_count {
        let addr = reader.u64()?;
        string_literals.push((addr, reader.string()?.to_string()));
    }
    let symbol_count = reader.u32()? as usize;
    let mut data_symbols = Vec::with_capacity(symbol_count.min(4096));
    for _ in 0..symbol_count {
        let addr = reader.u64()?;
        let name = reader.string()?;
        let type_spelling = if reader.format_version() >= 8 {
            reader.optional_string()?
        } else {
            None
        };
        data_symbols.push(SourceDataObject::new(addr, name, type_spelling));
    }
    let table_count = reader.u32()? as usize;
    let mut code_pointer_tables = Vec::with_capacity(table_count.min(64));
    for _ in 0..table_count {
        let address = reader.u64()?;
        let entry_size = reader.u32()?;
        let target_count = reader.u32()? as usize;
        let mut targets = Vec::with_capacity(target_count.min(1024));
        for _ in 0..target_count {
            targets.push(reader.u64()?);
        }
        code_pointer_tables.push(SourceCodePointerTable::new(address, entry_size, targets));
    }
    let total_source_bytes =
        usize::try_from(reader.u64()?).map_err(|_| SnapshotWireError::ValueTooWide)?;
    Ok(OwnedFunctionImage {
        entry_address,
        blocks: blocks.into_boxed_slice(),
        external_exits: external_exits.into_boxed_slice(),
        string_literals: string_literals.into_boxed_slice(),
        data_symbols: data_symbols.into_boxed_slice(),
        code_pointer_tables: code_pointer_tables.into_boxed_slice(),
        total_source_bytes,
    })
}

const RESULT_VOID: u8 = 0;
const RESULT_REGISTER: u8 = 1;

pub fn write_call_result(writer: &mut SnapshotWireWriter, result: &SourceCallResult) {
    match result {
        SourceCallResult::Void => writer.u8(RESULT_VOID),
        SourceCallResult::Register { storage } => {
            writer.u8(RESULT_REGISTER);
            write_storage(writer, *storage);
        }
    }
}

pub fn read_call_result(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceCallResult, SnapshotWireError> {
    match reader.u8()? {
        RESULT_VOID => Ok(SourceCallResult::Void),
        RESULT_REGISTER => Ok(SourceCallResult::Register {
            storage: read_storage(reader)?,
        }),
        // Void and a register result are not interchangeable, so an unknown tag
        // is refused rather than treated as void.
        tag => Err(SnapshotWireError::UnknownDiscriminant {
            record: "call result",
            tag: u64::from(tag),
        }),
    }
}

pub fn write_call_prototype(
    writer: &mut SnapshotWireWriter,
    prototype: &AdvisoryCallPrototype,
) -> Result<(), SnapshotWireError> {
    writer.string(&prototype.calling_convention)?;
    let count =
        u32::try_from(prototype.arguments.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(count);
    for argument in prototype.arguments.iter() {
        writer.u32(argument.index());
        write_storage(writer, argument.storage());
    }
    writer.bool(prototype.variadic);
    writer.bool(prototype.noreturn);
    write_call_result(writer, &prototype.result);
    Ok(())
}

pub fn read_call_prototype(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<AdvisoryCallPrototype, SnapshotWireError> {
    let calling_convention = reader.string()?.to_string();
    let count = reader.u32()? as usize;
    let mut arguments = Vec::with_capacity(count.min(256));
    for _ in 0..count {
        let index = reader.u32()?;
        let storage = read_storage(reader)?;
        arguments.push(SourceCallArgumentSpec::new(index, storage));
    }
    let variadic = reader.bool()?;
    let noreturn = reader.bool()?;
    let result = read_call_result(reader)?;
    Ok(AdvisoryCallPrototype {
        calling_convention,
        arguments: arguments.into_boxed_slice(),
        variadic,
        noreturn,
        result,
    })
}

const CALL_TRANSFER_CALL: u8 = 0;
const CALL_TRANSFER_TAIL_JUMP: u8 = 1;
const CALL_TRANSFER_TAIL_SLOT: u8 = 2;

pub fn write_call_site(
    writer: &mut SnapshotWireWriter,
    site: &AdvisoryCallSite,
) -> Result<(), SnapshotWireError> {
    writer.u64(site.instruction_address());
    writer.u64(site.target_address());
    writer.string(site.target_name().unwrap_or(""))?;
    writer.u8(match site.transfer() {
        AdvisoryCallTransfer::Call => CALL_TRANSFER_CALL,
        AdvisoryCallTransfer::TailJump => CALL_TRANSFER_TAIL_JUMP,
        AdvisoryCallTransfer::TailSlot => CALL_TRANSFER_TAIL_SLOT,
    });
    // Absence is meaningful here: radare2 described the call but not what it
    // takes or returns, which is not the same as an empty prototype.
    match site.prototype() {
        Some(prototype) => {
            writer.bool(true);
            write_call_prototype(writer, prototype)?;
        }
        None => writer.bool(false),
    }
    Ok(())
}

pub fn read_call_site(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<AdvisoryCallSite, SnapshotWireError> {
    let instruction_address = reader.u64()?;
    let target_address = reader.u64()?;
    let target_name = reader.string()?;
    // Before version 7 every site radare2 reported was a call instruction, so
    // an older buffer says so without carrying the byte.
    let transfer = if reader.format_version() >= 7 {
        match reader.u8()? {
            CALL_TRANSFER_CALL => AdvisoryCallTransfer::Call,
            CALL_TRANSFER_TAIL_JUMP => AdvisoryCallTransfer::TailJump,
            CALL_TRANSFER_TAIL_SLOT => AdvisoryCallTransfer::TailSlot,
            tag => {
                return Err(SnapshotWireError::UnknownDiscriminant {
                    record: "call transfer",
                    tag: u64::from(tag),
                });
            }
        }
    } else {
        AdvisoryCallTransfer::Call
    };
    let prototype = if reader.bool()? {
        Some(read_call_prototype(reader)?)
    } else {
        None
    };
    Ok(AdvisoryCallSite {
        instruction_address,
        target_address,
        transfer,
        target_name: (!target_name.is_empty()).then(|| target_name.to_string()),
        prototype,
    })
}

const CARRIER_FULL: u8 = 0;
const CARRIER_LOW_BITS: u8 = 1;

pub fn write_carrier(writer: &mut SnapshotWireWriter, carrier: SourceCarrierProjection) {
    writer.u8(match carrier.kind() {
        SourceCarrierKind::Full => CARRIER_FULL,
        SourceCarrierKind::LowBits => CARRIER_LOW_BITS,
    });
    writer.u64(carrier.offset_bits());
    writer.u64(carrier.size_bits());
}

pub fn read_carrier(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceCarrierProjection, SnapshotWireError> {
    let kind = match reader.u8()? {
        CARRIER_FULL => SourceCarrierKind::Full,
        CARRIER_LOW_BITS => SourceCarrierKind::LowBits,
        // The kind decides whether a value is the whole carrier or a truncation
        // of it, so an unknown one is refused rather than widened.
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "carrier kind",
                tag: u64::from(tag),
            });
        }
    };
    let offset_bits = reader.u64()?;
    let size_bits = reader.u64()?;
    Ok(SourceCarrierProjection::new(kind, offset_bits, size_bits))
}

pub fn write_logical_value(writer: &mut SnapshotWireWriter, value: SourceLogicalValue) {
    writer.u32(value.type_id());
    write_carrier(writer, value.carrier());
}

pub fn read_logical_value(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceLogicalValue, SnapshotWireError> {
    let type_id = reader.u32()?;
    let carrier = read_carrier(reader)?;
    Ok(SourceLogicalValue::new(type_id, carrier))
}

pub fn write_abi_parameter(writer: &mut SnapshotWireWriter, parameter: &SourceAbiParameterSpec) {
    writer.u32(parameter.index());
    write_storage(writer, parameter.storage());
}

pub fn read_abi_parameter(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceAbiParameterSpec, SnapshotWireError> {
    let index = reader.u32()?;
    let storage = read_storage(reader)?;
    Ok(SourceAbiParameterSpec::new(index, storage))
}

pub fn write_function_return(writer: &mut SnapshotWireWriter, kind: &SourceFunctionReturn) {
    match kind {
        SourceFunctionReturn::Void => writer.u8(RESULT_VOID),
        SourceFunctionReturn::Register { storage } => {
            writer.u8(RESULT_REGISTER);
            write_storage(writer, *storage);
        }
    }
}

pub fn read_function_return(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceFunctionReturn, SnapshotWireError> {
    match reader.u8()? {
        RESULT_VOID => Ok(SourceFunctionReturn::Void),
        RESULT_REGISTER => Ok(SourceFunctionReturn::Register {
            storage: read_storage(reader)?,
        }),
        tag => Err(SnapshotWireError::UnknownDiscriminant {
            record: "function return",
            tag: u64::from(tag),
        }),
    }
}

const TYPE_SIGNED: u8 = 0;
const TYPE_UNSIGNED: u8 = 1;
const TYPE_POINTER: u8 = 2;
const TYPE_STRUCT: u8 = 3;
const TYPE_VOID: u8 = 4;
const TYPE_CODE: u8 = 5;

pub fn write_type(writer: &mut SnapshotWireWriter, source_type: &SourceType) {
    writer.u32(source_type.id());
    match source_type.kind() {
        SourceTypeKind::SignedInteger => writer.u8(TYPE_SIGNED),
        SourceTypeKind::UnsignedInteger => writer.u8(TYPE_UNSIGNED),
        SourceTypeKind::Pointer { target_type_id } => {
            writer.u8(TYPE_POINTER);
            writer.u32(target_type_id);
        }
        SourceTypeKind::Struct { aggregate_id } => {
            writer.u8(TYPE_STRUCT);
            writer.u32(aggregate_id);
        }
        SourceTypeKind::Void => writer.u8(TYPE_VOID),
        SourceTypeKind::Code => writer.u8(TYPE_CODE),
    }
    writer.u64(source_type.size_bits());
    writer.u64(source_type.align_bits());
}

pub fn read_type(reader: &mut SnapshotWireReader<'_>) -> Result<SourceType, SnapshotWireError> {
    let id = reader.u32()?;
    let kind = match reader.u8()? {
        TYPE_SIGNED => SourceTypeKind::SignedInteger,
        TYPE_UNSIGNED => SourceTypeKind::UnsignedInteger,
        TYPE_POINTER => SourceTypeKind::Pointer {
            target_type_id: reader.u32()?,
        },
        TYPE_STRUCT => SourceTypeKind::Struct {
            aggregate_id: reader.u32()?,
        },
        TYPE_VOID => SourceTypeKind::Void,
        TYPE_CODE => SourceTypeKind::Code,
        // Signedness and indirection are not recoverable from anything else in
        // the record, so an unknown kind is refused.
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "type kind",
                tag: u64::from(tag),
            });
        }
    };
    let size_bits = reader.u64()?;
    let align_bits = reader.u64()?;
    Ok(SourceType::new(id, kind, size_bits, align_bits))
}

pub fn write_aggregate_member(
    writer: &mut SnapshotWireWriter,
    member: &SourceAggregateMember,
) -> Result<(), SnapshotWireError> {
    writer.u32(member.member_id());
    writer.u32(member.type_id());
    writer.u64(member.offset_bits());
    writer.u64(member.size_bits());
    writer.string(member.name())
}

pub fn read_aggregate_member(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceAggregateMember, SnapshotWireError> {
    let member_id = reader.u32()?;
    let type_id = reader.u32()?;
    let offset_bits = reader.u64()?;
    let size_bits = reader.u64()?;
    let name = reader.string()?.to_string();
    Ok(SourceAggregateMember::new(
        member_id,
        type_id,
        offset_bits,
        size_bits,
        name,
    ))
}

pub fn write_aggregate(
    writer: &mut SnapshotWireWriter,
    aggregate: &SourceAggregateLayout,
) -> Result<(), SnapshotWireError> {
    writer.u32(aggregate.id());
    writer.u32(aggregate.type_id());
    writer.u64(aggregate.size_bits());
    writer.u64(aggregate.align_bits());
    writer.string(aggregate.name())?;
    let count =
        u32::try_from(aggregate.members().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(count);
    for member in aggregate.members() {
        write_aggregate_member(writer, member)?;
    }
    Ok(())
}

pub fn read_aggregate(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceAggregateLayout, SnapshotWireError> {
    let id = reader.u32()?;
    let type_id = reader.u32()?;
    let size_bits = reader.u64()?;
    let align_bits = reader.u64()?;
    let name = reader.string()?.to_string();
    let count = reader.u32()? as usize;
    let mut members = Vec::with_capacity(count.min(4096));
    for _ in 0..count {
        members.push(read_aggregate_member(reader)?);
    }
    Ok(SourceAggregateLayout::new(
        id, type_id, size_bits, align_bits, name, members,
    ))
}

pub fn write_type_graph(
    writer: &mut SnapshotWireWriter,
    graph: &SourceTypeGraph,
) -> Result<(), SnapshotWireError> {
    let types = u32::try_from(graph.types().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(types);
    for source_type in graph.types() {
        write_type(writer, source_type);
    }
    let aggregates =
        u32::try_from(graph.aggregates().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(aggregates);
    for aggregate in graph.aggregates() {
        write_aggregate(writer, aggregate)?;
    }
    Ok(())
}

pub fn read_type_graph(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceTypeGraph, SnapshotWireError> {
    let type_count = reader.u32()? as usize;
    let mut types = Vec::with_capacity(type_count.min(4096));
    for _ in 0..type_count {
        types.push(read_type(reader)?);
    }
    let aggregate_count = reader.u32()? as usize;
    let mut aggregates = Vec::with_capacity(aggregate_count.min(4096));
    for _ in 0..aggregate_count {
        aggregates.push(read_aggregate(reader)?);
    }
    // new() revalidates dense ids, sizes and member bounds, so a buffer cannot
    // mint a graph the in-crate constructor would have rejected. Every
    // downstream projection resolves type identities against this graph, so it
    // is the last place that may accept something unchecked.
    SourceTypeGraph::new(types, aggregates).map_err(|error| SnapshotWireError::RejectedContract {
        contract: "SourceTypeGraph::new",
        reason: format!("{error:?}"),
    })
}

const GROWTH_LOWER: u8 = 0;
const GROWTH_HIGHER: u8 = 1;

pub fn write_stack_allocation(
    writer: &mut SnapshotWireWriter,
    contract: &SourceStackAllocationContract,
) {
    writer.u8(match contract.growth() {
        SourceStackGrowth::LowerAddresses => GROWTH_LOWER,
        SourceStackGrowth::HigherAddresses => GROWTH_HIGHER,
    });
    writer.u32(contract.implicit_active_sp_bytes());
}

pub fn read_stack_allocation(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceStackAllocationContract, SnapshotWireError> {
    let growth = match reader.u8()? {
        GROWTH_LOWER => SourceStackGrowth::LowerAddresses,
        GROWTH_HIGHER => SourceStackGrowth::HigherAddresses,
        // Growth direction decides which side of the entry SP the callee owns,
        // so a guess would hand out the wrong interval.
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "stack growth",
                tag: u64::from(tag),
            });
        }
    };
    let implicit = reader.u32()?;
    Ok(SourceStackAllocationContract::with_implicit_active_sp_bytes(growth, implicit))
}

const MECHANISM_STACKED: u8 = 0;

pub fn write_return_mechanism(writer: &mut SnapshotWireWriter, mechanism: &SourceReturnMechanism) {
    match mechanism {
        SourceReturnMechanism::Stacked {
            stack_offset,
            slot_size_bytes,
            stack_pointer_delta_bytes,
            address_size_bytes,
        } => {
            writer.u8(MECHANISM_STACKED);
            writer.i64(*stack_offset);
            writer.u32(*slot_size_bytes);
            writer.u32(*stack_pointer_delta_bytes);
            writer.u32(*address_size_bytes);
        }
    }
}

pub fn read_return_mechanism(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceReturnMechanism, SnapshotWireError> {
    match reader.u8()? {
        MECHANISM_STACKED => Ok(SourceReturnMechanism::Stacked {
            stack_offset: reader.i64()?,
            slot_size_bytes: reader.u32()?,
            stack_pointer_delta_bytes: reader.u32()?,
            address_size_bytes: reader.u32()?,
        }),
        tag => Err(SnapshotWireError::UnknownDiscriminant {
            record: "return mechanism",
            tag: u64::from(tag),
        }),
    }
}

const BASE_FRAME_POINTER: u8 = 0;
const BASE_STACK_POINTER: u8 = 1;
const ROLE_UNCLASSIFIED: u8 = 0;
const ROLE_LOCAL: u8 = 1;
const ROLE_PARAMETER_HOME: u8 = 2;

pub fn write_stack_slot(writer: &mut SnapshotWireWriter, slot: &SourceStackSlotSpec) {
    writer.u8(match slot.base() {
        StackAddressBase::FramePointer => BASE_FRAME_POINTER,
        StackAddressBase::StackPointer => BASE_STACK_POINTER,
    });
    write_storage(writer, slot.base_storage());
    writer.i64(slot.offset());
    writer.u32(slot.size_bytes());
    match slot.role() {
        SourceStackSlotRole::UnclassifiedResource => writer.u8(ROLE_UNCLASSIFIED),
        SourceStackSlotRole::Local => writer.u8(ROLE_LOCAL),
        SourceStackSlotRole::ParameterHome {
            parameter_index,
            home_storage,
        } => {
            writer.u8(ROLE_PARAMETER_HOME);
            writer.u32(parameter_index);
            write_storage(writer, home_storage);
        }
    }
    // The slot's node in the type graph, or the invalid id when it has none.
    writer.u32(slot.logical_type().unwrap_or(u32::MAX));
}

pub fn read_stack_slot(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceStackSlotSpec, SnapshotWireError> {
    let base = match reader.u8()? {
        BASE_FRAME_POINTER => StackAddressBase::FramePointer,
        BASE_STACK_POINTER => StackAddressBase::StackPointer,
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "stack slot base",
                tag: u64::from(tag),
            });
        }
    };
    let base_storage = read_storage(reader)?;
    let offset = reader.i64()?;
    let size_bytes = reader.u32()?;
    // Role carries authority: a parameter home is not interchangeable with an
    // unclassified resource, so each is rebuilt through its own constructor.
    let slot = match reader.u8()? {
        ROLE_UNCLASSIFIED => SourceStackSlotSpec::new(base, base_storage, offset, size_bytes),
        ROLE_LOCAL => SourceStackSlotSpec::new_local(base, base_storage, offset, size_bytes),
        ROLE_PARAMETER_HOME => {
            let parameter_index = reader.u32()?;
            let home_storage = read_storage(reader)?;
            SourceStackSlotSpec::new_parameter_home(
                base,
                base_storage,
                offset,
                size_bytes,
                parameter_index,
                home_storage,
            )
        }
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "stack slot role",
                tag: u64::from(tag),
            });
        }
    };
    // A slot's declared type is a node of the function's type graph from
    // format 9 on; the invalid id says the graph does not carry it.
    let logical_type = if reader.format_version() >= 9 {
        let id = reader.u32()?;
        (id != u32::MAX).then_some(id)
    } else {
        None
    };
    Ok(match logical_type {
        Some(type_id) => slot.with_logical_type(type_id),
        None => slot,
    })
}

// Which base constructor the producer used. The choice is not derivable from
// the field values alone: it decides whether the interface claims exact stack
// slot roles and exact logical types, which is authority, not presentation.
const INTERFACE_PLAIN: u8 = 0;
const INTERFACE_EXACT_SLOTS: u8 = 1;
const INTERFACE_LOGICAL: u8 = 2;
const INTERFACE_EXACT_BOTH: u8 = 3;

pub fn write_interface(
    writer: &mut SnapshotWireWriter,
    interface: &SourceFunctionInterface,
) -> Result<(), SnapshotWireError> {
    write_interface_for_format(writer, interface, SNAPSHOT_WIRE_FORMAT_VERSION, None)
}

fn write_interface_for_format(
    writer: &mut SnapshotWireWriter,
    interface: &SourceFunctionInterface,
    format_version: u32,
    legacy_stack_allocation: Option<SourceStackAllocationContract>,
) -> Result<(), SnapshotWireError> {
    let exact_types = interface.type_graph().is_some();
    let exact_slots = interface.stack_slot_roles_complete();
    writer.u8(match (exact_types, exact_slots) {
        (true, true) => INTERFACE_EXACT_BOTH,
        (true, false) => INTERFACE_LOGICAL,
        (false, true) => INTERFACE_EXACT_SLOTS,
        (false, false) => INTERFACE_PLAIN,
    });
    writer.bytes(interface.revision_identity())?;
    writer.string(interface.calling_convention())?;
    if format_version == 2 {
        write_abi_class(writer, interface.abi_class());
    }

    let parameters =
        u32::try_from(interface.parameters().len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(parameters);
    for parameter in interface.parameters() {
        write_abi_parameter(writer, parameter);
    }
    write_function_return(writer, &interface.return_kind());

    let slots = u32::try_from(interface.stack_slots().len())
        .map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(slots);
    for slot in interface.stack_slots() {
        write_stack_slot(writer, slot);
    }

    let logical = u32::try_from(interface.parameter_logical_values().len())
        .map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(logical);
    for value in interface.parameter_logical_values() {
        write_logical_value(writer, *value);
    }
    match interface.return_logical_value() {
        Some(value) => {
            writer.bool(true);
            write_logical_value(writer, value);
        }
        None => writer.bool(false),
    }
    match interface.type_graph() {
        Some(graph) => {
            writer.bool(true);
            write_type_graph(writer, graph)?;
        }
        None => writer.bool(false),
    }

    writer.bool(interface.stack_pointer_preserved_across_calls());
    writer.bool(interface.frame_pointer_preserved_across_calls());
    let role_names = interface.role_register_names();
    write_named_optional_storage(
        writer,
        interface.return_address_storage(),
        role_names
            .return_address()
            .and_then(SourceRegisterName::new),
        format_version,
    )?;
    write_named_optional_storage(
        writer,
        interface.stack_pointer_storage(),
        role_names.stack_pointer().and_then(SourceRegisterName::new),
        format_version,
    )?;
    write_named_optional_storage(
        writer,
        interface.frame_pointer_storage(),
        role_names.frame_pointer().and_then(SourceRegisterName::new),
        format_version,
    )?;
    match interface.return_mechanism() {
        Some(mechanism) => {
            writer.bool(true);
            write_return_mechanism(writer, &mechanism);
        }
        None => writer.bool(false),
    }
    if format_version < 3 {
        match legacy_stack_allocation {
            Some(contract) => {
                writer.bool(true);
                write_stack_allocation(writer, &contract);
            }
            None => writer.bool(false),
        }
    }
    Ok(())
}

/// Rebuild an interface through the same constructor and builder order the
/// accessor walk uses, so a decoded interface is the one that walk would have
/// produced rather than a lookalike assembled from the same fields.
/// Decode one interface record.
///
/// Legacy v1/v2 stack-allocation authority cannot be represented by a modern
/// `SourceFunctionInterface`; it migrates to `SourceMachineRoles` only while
/// decoding the containing whole snapshot. A standalone legacy record that
/// carries that authority is therefore refused instead of silently dropping
/// it.
pub fn read_interface(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<SourceFunctionInterface, SnapshotWireError> {
    let (interface, legacy_stack_allocation) = read_interface_record(reader)?;
    if legacy_stack_allocation.is_some() {
        return Err(SnapshotWireError::RejectedContract {
            contract: "legacy interface stack allocation",
            reason: "decode the whole snapshot to migrate this fact to SourceMachineRoles"
                .to_string(),
        });
    }
    Ok(interface)
}

fn read_interface_record(
    reader: &mut SnapshotWireReader<'_>,
) -> Result<
    (
        SourceFunctionInterface,
        Option<SourceStackAllocationContract>,
    ),
    SnapshotWireError,
> {
    let variant = reader.u8()?;
    let revision = reader.bytes()?.to_vec();
    let calling_convention = reader.string()?.to_string();
    let recorded_abi_class = read_recorded_abi_class(reader)?;

    let parameter_count = reader.u32()? as usize;
    let mut parameters = Vec::with_capacity(parameter_count.min(256));
    for _ in 0..parameter_count {
        parameters.push(read_abi_parameter(reader)?);
    }
    let return_kind = read_function_return(reader)?;

    let slot_count = reader.u32()? as usize;
    let mut stack_slots = Vec::with_capacity(slot_count.min(4096));
    for _ in 0..slot_count {
        stack_slots.push(read_stack_slot(reader)?);
    }

    let logical_count = reader.u32()? as usize;
    let mut logical_parameters = Vec::with_capacity(logical_count.min(256));
    for _ in 0..logical_count {
        logical_parameters.push(read_logical_value(reader)?);
    }
    let return_logical = if reader.bool()? {
        Some(read_logical_value(reader)?)
    } else {
        None
    };
    let type_graph = if reader.bool()? {
        Some(read_type_graph(reader)?)
    } else {
        None
    };

    let stack_pointer_preserved = reader.bool()?;
    let frame_pointer_preserved = reader.bool()?;
    let (return_address_storage, return_address_name) = read_named_optional_storage(reader)?;
    let (stack_pointer_storage, stack_pointer_name) = read_named_optional_storage(reader)?;
    let (frame_pointer_storage, frame_pointer_name) = read_named_optional_storage(reader)?;
    let return_mechanism = if reader.bool()? {
        Some(read_return_mechanism(reader)?)
    } else {
        None
    };
    let legacy_stack_allocation = if reader.format_version() < 3 && reader.bool()? {
        Some(read_stack_allocation(reader)?)
    } else {
        None
    };

    let mut interface = match variant {
        INTERFACE_EXACT_BOTH => SourceFunctionInterface::new_exact_with_logical_types(
            revision,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
            logical_parameters,
            return_logical,
            type_graph,
        ),
        INTERFACE_LOGICAL => SourceFunctionInterface::new_with_logical_types(
            revision,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
            logical_parameters,
            return_logical,
            type_graph,
        ),
        INTERFACE_EXACT_SLOTS => SourceFunctionInterface::new_exact(
            revision,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
        ),
        INTERFACE_PLAIN => SourceFunctionInterface::new(
            revision,
            calling_convention,
            parameters,
            return_kind,
            stack_slots,
        ),
        tag => {
            return Err(SnapshotWireError::UnknownDiscriminant {
                record: "interface shape",
                tag: u64::from(tag),
            });
        }
    }
    .map_err(|error| SnapshotWireError::RejectedContract {
        contract: "SourceFunctionInterface::new",
        reason: format!("{error:?}"),
    })?;
    verify_recorded_abi_class(
        recorded_abi_class,
        interface.abi_class(),
        "SourceFunctionInterface ABI class",
    )?;

    interface =
        interface.with_preserved_call_carriers(stack_pointer_preserved, frame_pointer_preserved);
    interface = interface.with_role_register_names(SourceRoleRegisterNames::new(
        return_address_name.as_ref().map(SourceRegisterName::as_str),
        stack_pointer_name.as_ref().map(SourceRegisterName::as_str),
        frame_pointer_name.as_ref().map(SourceRegisterName::as_str),
    ));
    if let Some(storage) = return_address_storage {
        interface = interface
            .with_return_address_storage(storage)
            .map_err(|error| SnapshotWireError::RejectedContract {
                contract: "SourceFunctionInterface::with_return_address_storage",
                reason: format!("{error:?}"),
            })?;
    }
    if let Some(storage) = stack_pointer_storage {
        interface = interface
            .with_stack_pointer_storage(storage)
            .map_err(|error| SnapshotWireError::RejectedContract {
                contract: "SourceFunctionInterface::with_stack_pointer_storage",
                reason: format!("{error:?}"),
            })?;
    }
    if let Some(storage) = frame_pointer_storage {
        interface = interface
            .with_frame_pointer_storage(storage)
            .map_err(|error| SnapshotWireError::RejectedContract {
                contract: "SourceFunctionInterface::with_frame_pointer_storage",
                reason: format!("{error:?}"),
            })?;
    }
    if let Some(SourceReturnMechanism::Stacked {
        stack_offset,
        slot_size_bytes,
        stack_pointer_delta_bytes,
        address_size_bytes,
    }) = return_mechanism
    {
        interface = interface
            .with_exact_stacked_return(
                stack_offset,
                slot_size_bytes,
                stack_pointer_delta_bytes,
                address_size_bytes,
            )
            .map_err(|error| SnapshotWireError::RejectedContract {
                contract: "SourceFunctionInterface::with_exact_stacked_return",
                reason: format!("{error:?}"),
            })?;
    }
    Ok((interface, legacy_stack_allocation))
}

/// Serialize one whole snapshot into a single buffer.
///
/// This is the producer side of the transport: radare2 writes exactly this and
/// nothing else crosses the boundary.
pub fn encode_snapshot(snapshot: &OwnedFunctionSnapshot) -> Result<Vec<u8>, SnapshotWireError> {
    encode_snapshot_set(snapshot, &[])
}

/// Encode one snapshot together with the snapshots of what it calls.
///
/// Each callee is a whole buffer of its own, so it decodes by the same reader
/// and nothing about it depends on where it sits in this one.
pub fn encode_snapshot_set(
    snapshot: &OwnedFunctionSnapshot,
    callees: &[OwnedFunctionSnapshot],
) -> Result<Vec<u8>, SnapshotWireError> {
    encode_snapshot_parts(snapshot, callees, snapshot.source_revision_identity())
}

/// Encode one body as a cache key: every field it carries, with the capture
/// tag replaced by this function's own content identity.
///
/// The tag is the reason a plain re-encoding cannot key a callee. A callee
/// collected beside a root inherits the *root's* revision identity, so the
/// same body reached from two callers serializes to two different buffers and
/// a byte-exact key never matches the one case a callee cache exists to serve.
/// Radare2 records what the body's own tag would have been as its content
/// identity, and this writes that in the tag's place.
///
/// Substituting is safe in the direction that matters. Every other field is
/// still written and still compared byte for byte, so two different bodies are
/// still told apart by the bytes that describe them; the substituted field is
/// a hash *of those same bytes*, so it adds no claim the rest of the buffer
/// does not already make. On a radare2 that predates the content identity the
/// two are equal and this degrades to the plain encoding, which is a key that
/// misses rather than one that is wrong.
pub fn encode_snapshot_cache_key(
    snapshot: &OwnedFunctionSnapshot,
) -> Result<Vec<u8>, SnapshotWireError> {
    encode_snapshot_parts(snapshot, &[], snapshot.source_content_identity())
}

fn encode_snapshot_parts(
    snapshot: &OwnedFunctionSnapshot,
    callees: &[OwnedFunctionSnapshot],
    revision_identity: &[u8],
) -> Result<Vec<u8>, SnapshotWireError> {
    let mut writer = SnapshotWireWriter::new();
    write_machine_profile(&mut writer, snapshot.machine())?;
    write_function_identity(&mut writer, snapshot.function());
    write_presentation(&mut writer, snapshot.presentation())?;
    write_image(&mut writer, snapshot.image())?;
    let calls = u32::try_from(snapshot.advisory_calls().len())
        .map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(calls);
    for site in snapshot.advisory_calls() {
        write_call_site(&mut writer, site)?;
    }
    writer.bytes(revision_identity)?;
    writer.bytes(snapshot.source_content_identity())?;
    match snapshot.function_interface() {
        Some(interface) => {
            writer.bool(true);
            write_interface(&mut writer, interface)?;
        }
        None => writer.bool(false),
    }
    write_machine_roles(&mut writer, snapshot.machine_roles())?;
    write_convention_slots(&mut writer, snapshot.convention_slots())?;
    write_captured_fields(&mut writer, snapshot.captured_fields());
    write_diagnostic_identity(&mut writer, snapshot.diagnostic_identity());
    let count = u32::try_from(callees.len()).map_err(|_| SnapshotWireError::ValueTooWide)?;
    writer.u32(count);
    for callee in callees {
        let nested = encode_snapshot(callee)?;
        writer.bytes(&nested)?;
    }
    writer.finish()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SnapshotDecodeError {
    Wire(SnapshotWireError),
    /// The decoded parts did not satisfy the snapshot's own validation, so no
    /// source authority is minted from them.
    Validation(SnapshotValidationError),
}

impl std::fmt::Display for SnapshotDecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Wire(error) => write!(f, "{error}"),
            Self::Validation(error) => write!(f, "snapshot validation failed: {error:?}"),
        }
    }
}

impl std::error::Error for SnapshotDecodeError {}

impl From<SnapshotWireError> for SnapshotDecodeError {
    fn from(error: SnapshotWireError) -> Self {
        Self::Wire(error)
    }
}

/// Parse one whole snapshot from a buffer.
///
/// The parts go through `from_captured_parts`, the same private mint the
/// accessor walk uses, so a buffer cannot assemble source authority the
/// in-crate constructor would refuse.
/// Decode one snapshot and the snapshots of the functions it calls.
///
/// The callees ride inside the same buffer, each as a whole snapshot with its
/// own string table, so they decode by this same reader and carry no callees of
/// their own.
pub fn decode_snapshot_set(
    buffer: &[u8],
) -> Result<(OwnedFunctionSnapshot, Vec<OwnedFunctionSnapshot>), SnapshotDecodeError> {
    decode_snapshot_inner(buffer)
}

pub fn decode_snapshot(buffer: &[u8]) -> Result<OwnedFunctionSnapshot, SnapshotDecodeError> {
    decode_snapshot_inner(buffer).map(|(snapshot, _)| snapshot)
}

fn decode_snapshot_inner(
    buffer: &[u8],
) -> Result<(OwnedFunctionSnapshot, Vec<OwnedFunctionSnapshot>), SnapshotDecodeError> {
    let mut reader = SnapshotWireReader::new(buffer)?;
    let machine = read_machine_profile(&mut reader)?;
    let function = read_function_identity(&mut reader)?;
    let presentation = read_presentation(&mut reader)?;
    let image = read_image(&mut reader)?;
    let call_count = reader.u32()? as usize;
    let mut advisory_calls = Vec::with_capacity(call_count.min(4096));
    for _ in 0..call_count {
        advisory_calls.push(read_call_site(&mut reader)?);
    }
    let source_revision_identity: Box<[u8]> = Box::from(reader.bytes()?);
    let source_content_identity: Option<Box<[u8]>> = if reader.format_version() >= 6 {
        Some(Box::from(reader.bytes()?))
    } else {
        None
    };
    let (function_interface, legacy_stack_allocation) = if reader.bool()? {
        let (interface, contract) = read_interface_record(&mut reader)?;
        (Some(interface), contract)
    } else {
        (None, None)
    };
    let machine_roles =
        read_machine_roles_with_legacy_contract(&mut reader, legacy_stack_allocation)?;
    let convention_slots = read_convention_slots(&mut reader)?;
    let captured_fields = read_captured_fields(&mut reader)?;
    let diagnostics = read_diagnostic_identity(&mut reader)?;
    let callee_count = reader.u32()? as usize;
    let mut callees = Vec::with_capacity(callee_count.min(64));
    for _ in 0..callee_count {
        let nested = reader.bytes()?;
        let (callee, nested_callees) = decode_snapshot_inner(nested)?;
        // One level. A callee that carried callees of its own would make the
        // set's shape depend on the program rather than on what was asked for.
        if !nested_callees.is_empty() {
            return Err(SnapshotDecodeError::Wire(
                SnapshotWireError::RejectedContract {
                    contract: "callee snapshot set depth",
                    reason: "a callee carried callees of its own".to_string(),
                },
            ));
        }
        callees.push(callee);
    }
    reader.finish()?;
    let snapshot = OwnedFunctionSnapshot::from_captured_parts(
        machine,
        function,
        presentation,
        image,
        advisory_calls.into_boxed_slice(),
        source_revision_identity,
        function_interface,
        machine_roles,
        convention_slots,
        captured_fields,
        diagnostics,
    )
    .map_err(SnapshotDecodeError::Validation)?;
    // The mint defaults the content identity to the revision, which is right
    // for a root and wrong for a callee: the capture overwrote the callee's
    // revision with the root's, and only the wire carries what its own was.
    let snapshot = match source_content_identity {
        Some(identity) => snapshot.with_source_content_identity(identity),
        None => snapshot,
    };
    Ok((snapshot, callees))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn image_with_data_object(object: SourceDataObject) -> OwnedFunctionImage {
        OwnedFunctionImage {
            entry_address: 0x1000,
            blocks: Box::new([]),
            external_exits: Box::new([]),
            string_literals: Box::new([]),
            data_symbols: Box::new([object]),
            code_pointer_tables: Box::new([]),
            total_source_bytes: 0,
        }
    }

    #[test]
    fn v8_data_object_type_round_trips_with_its_structural_address() {
        let image = image_with_data_object(SourceDataObject::new(
            0x7000,
            "global_counter",
            Some("int32_t"),
        ));
        let mut writer = SnapshotWireWriter::new();
        write_image(&mut writer, &image).expect("write typed data object");
        let buffer = writer.finish().expect("finish typed data object");
        let mut reader = SnapshotWireReader::new(&buffer).expect("typed data header");
        let decoded = read_image(&mut reader).expect("read typed data object");
        assert_eq!(decoded.data_symbols(), image.data_symbols());
        assert_eq!(decoded.data_symbols()[0].address(), 0x7000);
        assert_eq!(decoded.data_symbols()[0].type_spelling(), Some("int32_t"));
    }

    #[test]
    fn v7_data_object_decodes_without_inventing_a_type() {
        let image = image_with_data_object(SourceDataObject::new(
            0x7000,
            "global_counter",
            Some("int32_t"),
        ));
        let mut writer = SnapshotWireWriter::new();
        write_image_for_format(&mut writer, &image, 7).expect("write v7 data object");
        let mut buffer = writer.finish().expect("finish v7 data object");
        buffer[4..8].copy_from_slice(&7u32.to_le_bytes());
        let mut reader = SnapshotWireReader::new(&buffer).expect("v7 data header");
        let decoded = read_image(&mut reader).expect("read v7 data object");
        assert_eq!(decoded.data_symbols()[0].address(), 0x7000);
        assert_eq!(decoded.data_symbols()[0].name(), "global_counter");
        assert_eq!(decoded.data_symbols()[0].type_spelling(), None);
    }

    #[test]
    fn a_pointer_table_round_trips_with_every_target() {
        let mut writer = SnapshotWireWriter::new();
        let image = OwnedFunctionImage {
            entry_address: 0x1000,
            blocks: Box::new([]),
            external_exits: Box::new([]),
            string_literals: Box::new([]),
            data_symbols: Box::new([]),
            code_pointer_tables: Box::new([SourceCodePointerTable::new(
                0xc000,
                8,
                vec![0x6c8, 0x6e8, 0x708],
            )]),
            total_source_bytes: 0,
        };
        write_image(&mut writer, &image).expect("write");
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        let decoded = read_image(&mut reader).expect("read");
        assert_eq!(decoded.code_pointer_tables(), image.code_pointer_tables());
    }

    #[test]
    fn a_callee_snapshot_rides_inside_its_caller_and_decodes_alone() {
        let root = sample_snapshot(None);
        let callee = sample_snapshot(None);
        let buffer = encode_snapshot_set(&root, std::slice::from_ref(&callee)).expect("encode set");
        let (decoded_root, decoded_callees) = decode_snapshot_set(&buffer).expect("decode set");
        assert_eq!(decoded_root.function().address(), root.function().address());
        assert_eq!(decoded_callees.len(), 1);
        assert_eq!(
            decoded_callees[0].function().address(),
            callee.function().address()
        );
        // The plain decoder still reads the same buffer and simply drops them.
        assert!(decode_snapshot(&buffer).is_ok());
    }

    #[test]
    fn a_slot_name_round_trips_keyed_by_where_the_slot_sits() {
        let mut writer = SnapshotWireWriter::new();
        let presentation = FunctionPresentation {
            display_name: "process_string".into(),
            parameter_names: Box::new([]),
            callee_signatures: Box::new([]),
            signature: Some(SourceSignaturePresentation::new(
                Some("int"),
                Some("apcs"),
                false,
                [SourceSignatureParameter::new(Some("s"), Some("char *"))],
            )),
            stack_slot_names: Box::new([SourceStackSlotName::new(
                StackAddressBase::StackPointer,
                -40,
                "len",
            )
            .with_type_spelling(Some("size_t"))]),
        };
        write_presentation(&mut writer, &presentation).expect("write");
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(read_presentation(&mut reader).expect("read"), presentation);
    }

    #[test]
    fn an_unknown_discriminant_names_the_record_it_was_read_from() {
        let mut writer = SnapshotWireWriter::new();
        writer.string("x86").expect("arch");
        writer.string("x86-64").expect("cpu");
        writer.u32(64);
        writer.u8(0x5a);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(
            read_machine_profile(&mut reader),
            Err(SnapshotWireError::UnknownDiscriminant {
                record: "machine endianness",
                tag: 0x5a,
            })
        );
    }

    #[test]
    fn a_contract_that_refuses_a_decoded_record_names_itself() {
        let mut writer = SnapshotWireWriter::new();
        writer.u32(1);
        writer.u32(0);
        writer.u8(TYPE_POINTER);
        writer.u32(7);
        writer.u64(64);
        writer.u64(64);
        writer.u32(0);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        // The reason travels with the refusal, so match the contract and read
        // the reason rather than pinning its wording.
        let Err(SnapshotWireError::RejectedContract { contract, reason }) =
            read_type_graph(&mut reader)
        else {
            panic!("a type graph the constructor refuses must be refused here too");
        };
        assert_eq!(contract, "SourceTypeGraph::new");
        assert!(
            !reason.is_empty(),
            "a refusal has to say what it objected to"
        );
    }

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
        assert_eq!(
            u32::from_le_bytes([buffer[8], buffer[9], buffer[10], buffer[11]]),
            2
        );
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        for _ in 0..8 {
            assert_eq!(reader.string().expect("string"), "rsp");
        }
        assert_eq!(reader.string().expect("string"), "rbp");
        reader.finish().expect("consumed exactly");
    }

    #[test]
    fn version_one_convention_slots_are_migrated_through_the_source_classifier() {
        let mut writer = SnapshotWireWriter::new();
        writer.string("amd64").expect("convention");
        writer.u32(0);
        write_optional_storage(&mut writer, None);
        let mut buffer = writer.finish().expect("finish");
        buffer[4..8].copy_from_slice(&1u32.to_le_bytes());

        let mut reader = SnapshotWireReader::new(&buffer).expect("version one header");
        let slots = read_convention_slots(&mut reader).expect("legacy convention slots");
        reader.finish().expect("consumed exactly");
        assert_eq!(slots.calling_convention(), "amd64");
        assert_eq!(slots.abi_class(), SourceAbiClass::SystemVAMD64);
    }

    #[test]
    fn version_two_refuses_a_typed_abi_tag_that_disagrees_with_the_spelling() {
        let mut writer = SnapshotWireWriter::new();
        writer.string("amd64").expect("convention");
        write_abi_class(&mut writer, SourceAbiClass::MicrosoftX64);
        writer.u32(0);
        write_optional_storage(&mut writer, None);
        let mut buffer = writer.finish().expect("finish");
        buffer[4..8].copy_from_slice(&2u32.to_le_bytes());

        let mut reader = SnapshotWireReader::new(&buffer).expect("version two header");
        assert!(matches!(
            read_convention_slots(&mut reader),
            Err(SnapshotWireError::RejectedContract { .. })
        ));
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
        let function = FunctionIdentity {
            address: 0x1000_07c0,
        };
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
            let storage = CanonicalStorageId {
                space,
                offset: 0x38,
                size: 8,
            };
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
                stack_slot_names: Box::new([]),
                signature: None,
                callee_signatures: Box::new([]),
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
        write_machine_roles(&mut writer, &roles).expect("machine roles encode");
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

    fn sample_successor(kind: AdvisorySuccessorKind, case_value: Option<u64>) -> AdvisorySuccessor {
        AdvisorySuccessor {
            kind,
            target: 0x1000,
            case_value,
            external: false,
        }
    }

    #[test]
    fn every_successor_kind_round_trips() {
        let kinds = [
            (AdvisorySuccessorKind::Direct, None),
            (AdvisorySuccessorKind::Fallthrough, None),
            (AdvisorySuccessorKind::SwitchCase, Some(7)),
            (AdvisorySuccessorKind::SwitchDefault, None),
        ];
        for (kind, case_value) in kinds {
            let successor = sample_successor(kind, case_value);
            let mut writer = SnapshotWireWriter::new();
            write_successor(&mut writer, &successor);
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_successor(&mut reader).expect("read"), successor);
            reader.finish().expect("consumed exactly");
        }
    }

    #[test]
    fn an_unknown_successor_kind_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u8(77);
        writer.u64(0x1000);
        writer.bool(false);
        writer.bool(false);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_successor(&mut reader).is_err());
    }

    #[test]
    fn a_whole_function_image_round_trips() {
        let image = OwnedFunctionImage {
            string_literals: Box::new([(0x1000_2bbc, "secret123".to_string())]),
            data_symbols: Box::new([]),
            code_pointer_tables: Box::new([]),
            entry_address: 0x1000_07c0,
            blocks: vec![
                OwnedFunctionBlock {
                    address: 0x1000_07c0,
                    bytes: Arc::from(&[0x55u8, 0x48, 0x89, 0xe5][..]),
                    successors: vec![
                        sample_successor(AdvisorySuccessorKind::Direct, None),
                        sample_successor(AdvisorySuccessorKind::Fallthrough, None),
                    ]
                    .into_boxed_slice(),
                    switch_instruction: None,
                },
                OwnedFunctionBlock {
                    address: 0x1000_07dc,
                    bytes: Arc::from(&[0x5du8, 0xc3][..]),
                    successors: Box::new([]),
                    switch_instruction: Some(0x1000_07d5),
                },
            ]
            .into_boxed_slice(),
            external_exits: vec![0x2000, 0x3000].into_boxed_slice(),
            total_source_bytes: 6,
        };
        let mut writer = SnapshotWireWriter::new();
        write_image(&mut writer, &image).expect("write");
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(read_image(&mut reader).expect("read"), image);
        reader.finish().expect("consumed exactly");
    }

    #[test]
    fn an_image_truncated_mid_block_is_refused() {
        let image = OwnedFunctionImage {
            string_literals: Box::new([(0x1000_2bbc, "secret123".to_string())]),
            data_symbols: Box::new([]),
            code_pointer_tables: Box::new([]),
            entry_address: 0x40,
            blocks: vec![OwnedFunctionBlock {
                address: 0x40,
                bytes: Arc::from(&[0x90u8][..]),
                successors: Box::new([]),
                switch_instruction: None,
            }]
            .into_boxed_slice(),
            external_exits: Box::new([]),
            total_source_bytes: 1,
        };
        let mut writer = SnapshotWireWriter::new();
        write_image(&mut writer, &image).expect("write");
        let mut buffer = writer.finish().expect("finish");
        // drop the trailing byte-count word and re-declare the payload extent
        buffer.truncate(buffer.len() - 8);
        let shorter = (u32::from_le_bytes([buffer[16], buffer[17], buffer[18], buffer[19]]) - 8)
            .to_le_bytes();
        buffer[16..20].copy_from_slice(&shorter);
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_image(&mut reader).is_err());
    }

    #[test]
    fn a_call_site_round_trips_with_and_without_a_prototype() {
        let storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0x38,
            size: 8,
        };
        let with_prototype = AdvisoryCallSite {
            instruction_address: 0x1000_0741,
            target_address: 0x1000_1980,
            transfer: AdvisoryCallTransfer::Call,
            target_name: Some("sym.imp.strcmp".to_string()),
            prototype: Some(AdvisoryCallPrototype {
                calling_convention: "amd64".to_string(),
                arguments: vec![
                    SourceCallArgumentSpec::new(0, storage),
                    SourceCallArgumentSpec::new(1, storage),
                ]
                .into_boxed_slice(),
                variadic: true,
                noreturn: false,
                result: SourceCallResult::Register { storage },
            }),
        };
        // A site radare2 could not give a prototype for still has a target, and
        // the target still has a name: the two travel independently.
        let without = AdvisoryCallSite {
            instruction_address: 0x1000_0757,
            target_address: 0x1000_1986,
            transfer: AdvisoryCallTransfer::Call,
            target_name: Some("sym.imp.malloc".to_string()),
            prototype: None,
        };
        let unnamed = AdvisoryCallSite {
            instruction_address: 0x1000_0763,
            target_address: 0x1000_1992,
            transfer: AdvisoryCallTransfer::Call,
            target_name: None,
            prototype: None,
        };
        // A tail transfer is the same record with a different way in: a jump
        // to the callee's entry, or a jump through a relocated slot, in which
        // case the target address is the slot.
        let tail_jump = AdvisoryCallSite {
            instruction_address: 0x1000_0770,
            target_address: 0x1000_1a00,
            transfer: AdvisoryCallTransfer::TailJump,
            target_name: Some("sym.func.10001a00".to_string()),
            prototype: None,
        };
        let tail_slot = AdvisoryCallSite {
            instruction_address: 0x1000_42b0,
            target_address: 0x1000_8010,
            transfer: AdvisoryCallTransfer::TailSlot,
            target_name: Some("strcoll".to_string()),
            prototype: None,
        };
        for site in [with_prototype, without, unnamed, tail_jump, tail_slot] {
            let mut writer = SnapshotWireWriter::new();
            write_call_site(&mut writer, &site).expect("write");
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_call_site(&mut reader).expect("read"), site);
            reader.finish().expect("consumed exactly");
        }
    }

    #[test]
    fn a_void_result_round_trips_and_an_unknown_tag_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        write_call_result(&mut writer, &SourceCallResult::Void);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(
            read_call_result(&mut reader).expect("read"),
            SourceCallResult::Void
        );

        let mut writer = SnapshotWireWriter::new();
        writer.u8(9);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_call_result(&mut reader).is_err());
    }

    #[test]
    fn carriers_and_logical_values_round_trip() {
        for kind in [SourceCarrierKind::Full, SourceCarrierKind::LowBits] {
            let carrier = SourceCarrierProjection::new(kind, 0, 32);
            let value = SourceLogicalValue::new(4, carrier);
            let mut writer = SnapshotWireWriter::new();
            write_carrier(&mut writer, carrier);
            write_logical_value(&mut writer, value);
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_carrier(&mut reader).expect("carrier"), carrier);
            assert_eq!(read_logical_value(&mut reader).expect("value"), value);
            reader.finish().expect("consumed exactly");
        }
    }

    #[test]
    fn an_unknown_carrier_kind_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u8(5);
        writer.u64(0);
        writer.u64(32);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_carrier(&mut reader).is_err());
    }

    #[test]
    fn abi_parameters_and_return_kinds_round_trip() {
        let storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0x38,
            size: 8,
        };
        let parameter = SourceAbiParameterSpec::new(2, storage);
        for kind in [
            SourceFunctionReturn::Void,
            SourceFunctionReturn::Register { storage },
        ] {
            let mut writer = SnapshotWireWriter::new();
            write_abi_parameter(&mut writer, &parameter);
            write_function_return(&mut writer, &kind);
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_abi_parameter(&mut reader).expect("param"), parameter);
            assert_eq!(read_function_return(&mut reader).expect("return"), kind);
            reader.finish().expect("consumed exactly");
        }
    }

    fn sample_graph() -> SourceTypeGraph {
        SourceTypeGraph::new(
            vec![
                SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
                SourceType::new(2, SourceTypeKind::Struct { aggregate_id: 0 }, 64, 32),
            ],
            vec![SourceAggregateLayout::new(
                0,
                2,
                64,
                32,
                "Point".to_string(),
                vec![
                    SourceAggregateMember::new(0, 0, 0, 32, "x".to_string()),
                    SourceAggregateMember::new(1, 0, 32, 32, "y".to_string()),
                ],
            )],
        )
        .expect("graph")
    }

    #[test]
    fn a_struct_may_hold_a_pointer_to_its_own_kind() {
        // `struct state { int a; int b; long c; struct state *next; }` is
        // ordinary C. Refusing it refused every function that mentions it.
        let graph = SourceTypeGraph::new(
            vec![
                SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::SignedInteger, 64, 64),
                SourceType::new(2, SourceTypeKind::Struct { aggregate_id: 0 }, 192, 64),
                SourceType::new(3, SourceTypeKind::Pointer { target_type_id: 2 }, 64, 64),
            ],
            vec![SourceAggregateLayout::new(
                0,
                2,
                192,
                64,
                "state".to_string(),
                vec![
                    SourceAggregateMember::new(0, 0, 0, 32, "a".to_string()),
                    SourceAggregateMember::new(1, 0, 32, 32, "b".to_string()),
                    SourceAggregateMember::new(2, 1, 64, 64, "c".to_string()),
                    SourceAggregateMember::new(3, 3, 128, 64, "next".to_string()),
                ],
            )],
        )
        .expect("a struct with a pointer member is a valid type graph");
        assert_eq!(graph.aggregates()[0].members().len(), 4);
    }

    #[test]
    fn a_type_graph_with_aggregates_round_trips() {
        let graph = sample_graph();
        let mut writer = SnapshotWireWriter::new();
        write_type_graph(&mut writer, &graph).expect("write");
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(read_type_graph(&mut reader).expect("read"), graph);
        reader.finish().expect("consumed exactly");
    }

    #[test]
    fn a_graph_the_constructor_would_reject_is_refused() {
        // ids must be dense from zero; this buffer declares one type with id 3
        let mut writer = SnapshotWireWriter::new();
        writer.u32(1);
        write_type(
            &mut writer,
            &SourceType::new(3, SourceTypeKind::SignedInteger, 32, 32),
        );
        writer.u32(0);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_type_graph(&mut reader).is_err());
    }

    #[test]
    fn an_unknown_type_kind_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u32(0);
        writer.u8(200);
        writer.u64(32);
        writer.u64(32);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_type(&mut reader).is_err());
    }

    #[test]
    fn stack_allocation_and_return_mechanism_round_trip() {
        for growth in [
            SourceStackGrowth::LowerAddresses,
            SourceStackGrowth::HigherAddresses,
        ] {
            let contract = SourceStackAllocationContract::with_implicit_active_sp_bytes(growth, 8);
            let mechanism = SourceReturnMechanism::Stacked {
                stack_offset: -8,
                slot_size_bytes: 8,
                stack_pointer_delta_bytes: 8,
                address_size_bytes: 8,
            };
            let mut writer = SnapshotWireWriter::new();
            write_stack_allocation(&mut writer, &contract);
            write_return_mechanism(&mut writer, &mechanism);
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(
                read_stack_allocation(&mut reader).expect("contract"),
                contract
            );
            assert_eq!(
                read_return_mechanism(&mut reader).expect("mechanism"),
                mechanism
            );
            reader.finish().expect("consumed exactly");
        }
    }

    #[test]
    fn an_unknown_growth_direction_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u8(9);
        writer.u32(0);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_stack_allocation(&mut reader).is_err());
    }

    #[test]
    fn every_stack_slot_role_round_trips() {
        let storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0x30,
            size: 8,
        };
        let slots = [
            SourceStackSlotSpec::new(StackAddressBase::FramePointer, storage, -16, 8),
            SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, storage, -8, 4),
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                storage,
                -24,
                8,
                1,
                storage,
            ),
        ];
        for slot in slots {
            let mut writer = SnapshotWireWriter::new();
            write_stack_slot(&mut writer, &slot);
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            assert_eq!(read_stack_slot(&mut reader).expect("read"), slot);
            reader.finish().expect("consumed exactly");
        }
    }

    fn reg(offset: u64, size: u32) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size,
        }
    }

    /// Every type must be reachable from the ids an interface uses, so the
    /// interface fixtures use a graph with nothing spare in it.
    fn reachable_graph() -> SourceTypeGraph {
        SourceTypeGraph::new(
            vec![
                SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32),
                SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
            ],
            Vec::new(),
        )
        .expect("graph")
    }

    #[test]
    fn every_interface_variant_round_trips() {
        let params = vec![
            SourceAbiParameterSpec::new(0, reg(0x38, 8)),
            SourceAbiParameterSpec::new(1, reg(0x30, 8)),
        ];
        let slots = vec![SourceStackSlotSpec::new_local(
            StackAddressBase::FramePointer,
            reg(0x20, 8),
            -8,
            4,
        )];
        let logical = vec![
            SourceLogicalValue::new(
                1,
                SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
            ),
            SourceLogicalValue::new(
                1,
                SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
            ),
        ];
        let interfaces = vec![
            SourceFunctionInterface::new(
                vec![1u8, 2, 3],
                "amd64",
                params.clone(),
                SourceFunctionReturn::Void,
                slots.clone(),
            )
            .expect("plain"),
            SourceFunctionInterface::new_exact(
                vec![1u8, 2, 3],
                "amd64",
                params.clone(),
                SourceFunctionReturn::Register { storage: reg(0, 8) },
                slots.clone(),
            )
            .expect("exact slots"),
            SourceFunctionInterface::new_with_logical_types(
                vec![4u8, 5],
                "amd64",
                params.clone(),
                SourceFunctionReturn::Register { storage: reg(0, 8) },
                slots.clone(),
                logical.clone(),
                Some(logical[0]),
                Some(reachable_graph()),
            )
            .expect("logical"),
            SourceFunctionInterface::new_exact_with_logical_types(
                vec![6u8],
                "amd64",
                params,
                SourceFunctionReturn::Register { storage: reg(0, 8) },
                slots,
                logical.clone(),
                Some(logical[1]),
                Some(reachable_graph()),
            )
            .expect("exact both"),
        ];
        for interface in interfaces {
            let mut writer = SnapshotWireWriter::new();
            write_interface(&mut writer, &interface).expect("write");
            let buffer = writer.finish().expect("finish");
            let mut reader = SnapshotWireReader::new(&buffer).expect("header");
            let decoded = read_interface(&mut reader).expect("read");
            reader.finish().expect("consumed exactly");
            assert_eq!(decoded, interface);
        }
    }

    #[test]
    fn the_optional_interface_tail_round_trips() {
        let interface = SourceFunctionInterface::new_exact(
            vec![9u8],
            "amd64",
            vec![SourceAbiParameterSpec::new(0, reg(0x38, 8))],
            SourceFunctionReturn::Register { storage: reg(0, 8) },
            Vec::new(),
        )
        .expect("base")
        .with_preserved_call_carriers(true, true)
        .with_return_address_storage(reg(0x10, 8))
        .expect("return address")
        .with_stack_pointer_storage(reg(0x20, 8))
        .expect("stack pointer")
        .with_frame_pointer_storage(reg(0x28, 8))
        .expect("frame pointer")
        .with_exact_stacked_return(0, 8, 8, 8)
        .expect("stacked return");
        let roles = SourceMachineRoles::new(Some(reg(0x10, 8)), Some(reg(0x20, 8)))
            .and_then(|roles| {
                roles.with_stack_allocation_contract(
                    SourceStackAllocationContract::with_implicit_active_sp_bytes(
                        SourceStackGrowth::LowerAddresses,
                        8,
                    ),
                )
            })
            .expect("allocation");

        let mut writer = SnapshotWireWriter::new();
        write_interface(&mut writer, &interface).expect("write");
        write_machine_roles(&mut writer, &roles).expect("machine roles encode");
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        let decoded = read_interface(&mut reader).expect("read");
        let decoded_roles = read_machine_roles(&mut reader).expect("read roles");
        reader.finish().expect("consumed exactly");
        assert_eq!(decoded, interface);
        assert!(decoded.stack_pointer_preserved_across_calls());
        assert!(decoded.frame_pointer_preserved_across_calls());
        assert_eq!(decoded.frame_pointer_storage(), Some(reg(0x28, 8)));
        assert!(decoded.return_mechanism().is_some());
        assert_eq!(decoded_roles, roles);
    }

    #[test]
    fn standalone_legacy_interface_refuses_stack_allocation_authority() {
        let stack_pointer = reg(0x20, 8);
        let interface = SourceFunctionInterface::new_exact(
            vec![9u8],
            "amd64",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("legacy interface");
        let contract = SourceStackAllocationContract::with_implicit_active_sp_bytes(
            SourceStackGrowth::LowerAddresses,
            8,
        );

        for format_version in [1, 2] {
            let mut writer = SnapshotWireWriter::new();
            write_interface_for_format(&mut writer, &interface, format_version, Some(contract))
                .expect("legacy interface record");
            let mut buffer = writer.finish().expect("finish");
            buffer[4..8].copy_from_slice(&format_version.to_le_bytes());
            let mut reader = SnapshotWireReader::new(&buffer).expect("legacy header");

            let Err(SnapshotWireError::RejectedContract {
                contract: rejected_contract,
                reason,
            }) = read_interface(&mut reader)
            else {
                panic!("standalone legacy allocation authority must be refused");
            };
            assert_eq!(rejected_contract, "legacy interface stack allocation");
            assert_eq!(
                reason,
                "decode the whole snapshot to migrate this fact to SourceMachineRoles"
            );
        }
    }

    #[test]
    fn an_unknown_interface_variant_is_refused() {
        let mut writer = SnapshotWireWriter::new();
        writer.u8(200);
        writer.bytes(&[1]).expect("revision");
        writer.string("amd64").expect("cc");
        writer.u32(0);
        write_function_return(&mut writer, &SourceFunctionReturn::Void);
        writer.u32(0);
        writer.u32(0);
        writer.bool(false);
        writer.bool(false);
        writer.bool(false);
        writer.bool(false);
        write_optional_storage(&mut writer, None);
        write_optional_storage(&mut writer, None);
        write_optional_storage(&mut writer, None);
        writer.bool(false);
        writer.bool(false);
        let buffer = writer.finish().expect("finish");
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert!(read_interface(&mut reader).is_err());
    }

    fn sample_snapshot(
        function_interface: Option<SourceFunctionInterface>,
    ) -> OwnedFunctionSnapshot {
        let captured_fields = CapturedSourceFields {
            bounded_function_image: true,
            function_interface: function_interface.is_some(),
            exact_function_types: function_interface
                .as_ref()
                .is_some_and(|interface| interface.type_graph().is_some()),
            exact_stack_slot_roles: function_interface
                .as_ref()
                .is_some_and(SourceFunctionInterface::stack_slot_roles_complete),
            return_address_storage: false,
            stack_pointer_storage: false,
            frame_pointer_storage: false,
            return_mechanism: false,
            stack_allocation_contract: false,
        };
        OwnedFunctionSnapshot::from_captured_parts(
            MachineProfile {
                arch_id: "x86".into(),
                cpu_id: "x86-64".into(),
                bits: 64,
                endianness: SourceEndianness::Little,
            },
            FunctionIdentity {
                address: 0x1000_07c0,
            },
            FunctionPresentation {
                display_name: "safe_array_access".into(),
                // presentation names must match the interface's parameter count,
                // and must be absent entirely when there is no interface
                stack_slot_names: Box::new([]),
                signature: None,
                callee_signatures: Box::new([]),
                parameter_names: match function_interface.as_ref() {
                    Some(interface) => (0..interface.parameters().len())
                        .map(|index| Box::<str>::from(format!("arg{index}").as_str()))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    None => Box::new([]),
                },
            },
            OwnedFunctionImage {
                string_literals: Box::new([]),
                data_symbols: Box::new([]),
                code_pointer_tables: Box::new([]),
                entry_address: 0x1000_07c0,
                blocks: vec![OwnedFunctionBlock {
                    address: 0x1000_07c0,
                    bytes: Arc::from(&[0x55u8, 0x48, 0x89, 0xe5, 0x5d, 0xc3][..]),
                    successors: Box::new([]),
                    switch_instruction: None,
                }]
                .into_boxed_slice(),
                external_exits: Box::new([]),
                total_source_bytes: 6,
            },
            Box::new([]),
            vec![0xabu8, 0xcd].into_boxed_slice(),
            function_interface,
            SourceMachineRoles::new(None, None).expect("roles"),
            SourceConventionSlots::new("", [], None).expect("empty convention slots"),
            captured_fields,
            DiagnosticIdentity(0x1234),
        )
        .expect("snapshot")
    }

    fn encode_legacy_snapshot_with_stack_contract(
        snapshot: &OwnedFunctionSnapshot,
        format_version: u32,
        contract: SourceStackAllocationContract,
    ) -> Vec<u8> {
        assert!(matches!(format_version, 1 | 2));
        let mut writer = SnapshotWireWriter::new();
        write_machine_profile(&mut writer, snapshot.machine()).expect("machine");
        write_function_identity(&mut writer, snapshot.function());
        write_presentation(&mut writer, snapshot.presentation()).expect("presentation");
        write_image_for_format(&mut writer, snapshot.image(), format_version).expect("image");
        writer.u32(snapshot.advisory_calls().len() as u32);
        for site in snapshot.advisory_calls() {
            write_call_site(&mut writer, site).expect("call site");
        }
        writer
            .bytes(snapshot.source_revision_identity())
            .expect("revision");
        let interface = snapshot
            .function_interface()
            .expect("legacy allocation contract was interface-owned");
        writer.bool(true);
        write_interface_for_format(&mut writer, interface, format_version, Some(contract))
            .expect("legacy interface");
        write_machine_roles_for_format(&mut writer, snapshot.machine_roles(), format_version)
            .expect("machine roles encode");
        write_convention_slots_for_format(&mut writer, snapshot.convention_slots(), format_version)
            .expect("legacy convention slots");
        let mut captured = snapshot.captured_fields();
        captured.stack_allocation_contract = true;
        write_captured_fields(&mut writer, captured);
        write_diagnostic_identity(&mut writer, snapshot.diagnostic_identity());
        writer.u32(0);
        let mut buffer = writer.finish().expect("legacy snapshot");
        buffer[4..8].copy_from_slice(&format_version.to_le_bytes());
        buffer
    }

    #[test]
    fn whole_v1_and_v2_snapshots_migrate_interface_stack_allocation_to_machine_roles() {
        let stack_pointer = reg(0x20, 8);
        let interface = SourceFunctionInterface::new_exact(
            vec![0xab, 0xcd],
            "amd64",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(stack_pointer))
        .expect("legacy exact interface");
        let base = sample_snapshot(None);
        let roles = SourceMachineRoles::new(None, Some(stack_pointer)).expect("machine roles");
        let captured = CapturedSourceFields {
            bounded_function_image: true,
            function_interface: true,
            exact_function_types: false,
            exact_stack_slot_roles: true,
            return_address_storage: false,
            stack_pointer_storage: true,
            frame_pointer_storage: false,
            return_mechanism: false,
            stack_allocation_contract: false,
        };
        let snapshot = OwnedFunctionSnapshot::from_captured_parts(
            base.machine().clone(),
            *base.function(),
            base.presentation().clone(),
            base.image().clone(),
            base.advisory_calls().to_vec().into_boxed_slice(),
            base.source_revision_identity().into(),
            Some(interface),
            roles,
            base.convention_slots().clone(),
            captured,
            base.diagnostic_identity(),
        )
        .expect("legacy source snapshot");
        let contract = SourceStackAllocationContract::with_implicit_active_sp_bytes(
            SourceStackGrowth::LowerAddresses,
            8,
        );

        for format_version in [1, 2] {
            let buffer =
                encode_legacy_snapshot_with_stack_contract(&snapshot, format_version, contract);
            let decoded = decode_snapshot(&buffer).expect("legacy whole snapshot");
            assert_eq!(decoded.function_interface(), snapshot.function_interface());
            assert_eq!(
                decoded.machine_roles().stack_pointer_storage(),
                Some(stack_pointer)
            );
            assert_eq!(
                decoded.machine_roles().stack_allocation_contract(),
                Some(contract)
            );
            assert!(decoded.captured_fields().has_stack_allocation_contract());
        }
    }

    fn assert_same_parts(decoded: &OwnedFunctionSnapshot, original: &OwnedFunctionSnapshot) {
        assert_eq!(decoded.machine(), original.machine());
        assert_eq!(decoded.function(), original.function());
        assert_eq!(decoded.presentation(), original.presentation());
        assert_eq!(decoded.image(), original.image());
        assert_eq!(decoded.advisory_calls(), original.advisory_calls());
        assert_eq!(
            decoded.source_revision_identity(),
            original.source_revision_identity()
        );
        assert_eq!(decoded.function_interface(), original.function_interface());
        assert_eq!(decoded.machine_roles(), original.machine_roles());
        assert_eq!(decoded.captured_fields(), original.captured_fields());
        assert_eq!(
            decoded.diagnostic_identity(),
            original.diagnostic_identity()
        );
    }

    #[test]
    fn a_whole_snapshot_round_trips_part_for_part() {
        let interface = SourceFunctionInterface::new_exact_with_logical_types(
            vec![0xabu8, 0xcd],
            "amd64",
            vec![
                SourceAbiParameterSpec::new(0, reg(0x38, 8)),
                SourceAbiParameterSpec::new(1, reg(0x30, 8)),
            ],
            SourceFunctionReturn::Register { storage: reg(0, 8) },
            Vec::new(),
            vec![
                SourceLogicalValue::new(
                    1,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
                SourceLogicalValue::new(
                    1,
                    SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
                ),
            ],
            Some(SourceLogicalValue::new(
                1,
                SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
            )),
            Some(reachable_graph()),
        )
        .expect("interface");

        for snapshot in [sample_snapshot(None), sample_snapshot(Some(interface))] {
            let buffer = encode_snapshot(&snapshot).expect("encode");
            let decoded = decode_snapshot(&buffer).expect("decode");
            assert_same_parts(&decoded, &snapshot);
            // encoding the decoded snapshot must reproduce the same bytes, so
            // the format has no room for two spellings of one snapshot
            assert_eq!(encode_snapshot(&decoded).expect("re-encode"), buffer);
        }
    }

    #[test]
    fn a_snapshot_buffer_truncated_anywhere_is_refused() {
        let snapshot = sample_snapshot(None);
        let buffer = encode_snapshot(&snapshot).expect("encode");
        for len in 0..buffer.len() {
            assert!(
                decode_snapshot(&buffer[..len]).is_err(),
                "prefix of {len} bytes must not decode"
            );
        }
    }

    #[test]
    fn trailing_bytes_after_a_snapshot_are_refused() {
        let snapshot = sample_snapshot(None);
        let mut buffer = encode_snapshot(&snapshot).expect("encode");
        let payload = u32::from_le_bytes([buffer[16], buffer[17], buffer[18], buffer[19]]) + 4;
        buffer[16..20].copy_from_slice(&payload.to_le_bytes());
        buffer.extend_from_slice(&[0, 0, 0, 0]);
        assert!(decode_snapshot(&buffer).is_err());
    }

    /// Pin the current Rust writer's framing and primitive payload order.
    ///
    /// ABI spelling is classified once here instead of reimplemented across
    /// the FFI boundary.
    #[test]
    fn the_current_writer_vector_is_byte_stable() {
        let mut writer = SnapshotWireWriter::new();
        writer.u8(0x7f);
        writer.bool(true);
        writer.u16(0xbeef);
        writer.u32(0xdead_beef);
        writer.u64(0x0123_4567_89ab_cdef);
        writer.i64(-2);
        writer.bytes(&[1, 2, 3]).expect("bytes");
        writer.string("rsp").expect("rsp");
        writer.string("rsp").expect("rsp again");
        writer.string("rbp").expect("rbp");
        writer.optional_string(None).expect("absent");
        let buffer = writer.finish().expect("finish");

        let mut expected = Vec::new();
        expected.extend_from_slice(&SNAPSHOT_WIRE_MAGIC.to_le_bytes());
        expected.extend_from_slice(&SNAPSHOT_WIRE_FORMAT_VERSION.to_le_bytes());
        expected.extend_from_slice(&2u32.to_le_bytes()); // interned strings
        expected.extend_from_slice(&14u32.to_le_bytes()); // table bytes
        expected.extend_from_slice(&47u32.to_le_bytes()); // payload bytes
        expected.extend_from_slice(&0u32.to_le_bytes()); // reserved
        expected.extend_from_slice(&3u32.to_le_bytes());
        expected.extend_from_slice(b"rsp");
        expected.extend_from_slice(&3u32.to_le_bytes());
        expected.extend_from_slice(b"rbp");
        expected.push(0x7f);
        expected.push(0x01);
        expected.extend_from_slice(&0xbeefu16.to_le_bytes());
        expected.extend_from_slice(&0xdead_beefu32.to_le_bytes());
        expected.extend_from_slice(&0x0123_4567_89ab_cdefu64.to_le_bytes());
        expected.extend_from_slice(&(-2i64).to_le_bytes());
        expected.extend_from_slice(&3u32.to_le_bytes());
        expected.extend_from_slice(&[1, 2, 3]);
        expected.extend_from_slice(&0u32.to_le_bytes());
        expected.extend_from_slice(&0u32.to_le_bytes());
        expected.extend_from_slice(&1u32.to_le_bytes());
        expected.extend_from_slice(&u32::MAX.to_le_bytes());

        assert_eq!(buffer, expected);

        // and the reader must accept its own writer's vector
        let mut reader = SnapshotWireReader::new(&buffer).expect("header");
        assert_eq!(reader.u8().expect("u8"), 0x7f);
        assert!(reader.bool().expect("bool"));
        assert_eq!(reader.u16().expect("u16"), 0xbeef);
        assert_eq!(reader.u32().expect("u32"), 0xdead_beef);
        assert_eq!(reader.u64().expect("u64"), 0x0123_4567_89ab_cdef);
        assert_eq!(reader.i64().expect("i64"), -2);
        assert_eq!(reader.bytes().expect("bytes"), &[1, 2, 3]);
        assert_eq!(reader.string().expect("rsp"), "rsp");
        assert_eq!(reader.string().expect("rsp again"), "rsp");
        assert_eq!(reader.string().expect("rbp"), "rbp");
        assert_eq!(reader.optional_string().expect("absent"), None);
        reader.finish().expect("consumed exactly");
    }

    #[test]
    fn a_cache_key_keys_a_body_by_itself_rather_than_by_its_caller() {
        // Two captures of one body differ in exactly one field: the capture
        // tag, which is the caller's. A key that carried it would make the
        // same callee under two callers two different keys, which is the one
        // case a callee cache exists to serve.
        let body = sample_snapshot(None).with_source_content_identity(Box::from(&b"own-body"[..]));
        let key = encode_snapshot_cache_key(&body).expect("encode a cache key");
        let decoded = decode_snapshot(&key).expect("decode the cache key");
        assert_eq!(decoded.source_revision_identity(), b"own-body");
        assert_eq!(decoded.source_content_identity(), b"own-body");
        // Everything else the lift reads is still there and still compared.
        assert_eq!(decoded.function().address(), body.function().address());
        assert_eq!(
            decoded.image().entry_address(),
            body.image().entry_address()
        );
        assert_eq!(decoded.machine().arch_id(), body.machine().arch_id());
        // And it is not simply the plain encoding under another name.
        assert_ne!(
            encode_snapshot(&body).expect("plain encoding"),
            key,
            "the fixture must make the tag and the content differ"
        );
    }

    #[test]
    fn a_callee_keeps_its_own_content_identity_across_the_wire() {
        // The capture gives every callee the root's revision so a consumer can
        // tell the bodies were read together. That is what makes the content
        // identity necessary: without it the same callee under two callers is
        // two identities and a cache keyed on the revision never hits.
        let root = sample_snapshot(None);
        let callee =
            sample_snapshot(None).with_source_content_identity(Box::from(&b"callee-own"[..]));
        assert_ne!(
            callee.source_content_identity(),
            callee.source_revision_identity(),
            "the fixture must make the two differ or it proves nothing"
        );
        let encoded = encode_snapshot_set(&root, std::slice::from_ref(&callee))
            .expect("encode a root and one callee");
        let (decoded_root, decoded_callees) =
            decode_snapshot_set(&encoded).expect("decode the set");
        assert_eq!(
            decoded_root.source_content_identity(),
            root.source_content_identity()
        );
        let [decoded_callee] = decoded_callees.as_slice() else {
            panic!("one callee");
        };
        assert_eq!(decoded_callee.source_content_identity(), &b"callee-own"[..]);
    }
}
