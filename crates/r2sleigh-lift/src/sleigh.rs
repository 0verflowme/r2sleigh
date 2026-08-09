//! Sleigh specification metadata extraction.
//!
//! This module provides utilities for extracting architecture metadata from
//! loaded Sleigh specifications using `libsla`.

use libsla::{AddressSpace, AddressSpaceId, GhidraSleigh, Sleigh};
use r2il::{ArchSpec, Endianness, SpaceId};
use std::collections::{HashMap, HashSet};

use crate::LiftError;
use crate::context::LiftContext;

pub(crate) struct ExtractedSleighArchitecture {
    pub arch: ArchSpec,
    pub space_map: HashMap<AddressSpaceId, SpaceId>,
}

pub(crate) fn extract_address_space_map(
    ctx: &mut LiftContext,
    spaces: &[AddressSpace],
    default_space: AddressSpaceId,
) -> Result<HashMap<AddressSpaceId, SpaceId>, LiftError> {
    let mut saw_default_space = false;
    let mut source_ids = HashSet::new();
    let mut target_ids = HashSet::new();
    let mut space_map = HashMap::new();

    for space in spaces {
        if !source_ids.insert(space.id) {
            return Err(LiftError::Parse(format!(
                "Sleigh address space '{}' repeats source id {}",
                space.name, space.id
            )));
        }
        u64::try_from(space.id.raw_id()).map_err(|_| {
            LiftError::Parse(format!(
                "Sleigh address space '{}' id cannot be encoded by P-code: {}",
                space.name, space.id
            ))
        })?;
        let is_default = space.id == default_space;
        let address_size = u32::try_from(space.address_size).map_err(|_| {
            LiftError::Parse(format!(
                "Sleigh address size for space '{}' does not fit u32: {}",
                space.name, space.address_size
            ))
        })?;
        let word_size = u32::try_from(space.word_size).map_err(|_| {
            LiftError::Parse(format!(
                "Sleigh word size for space '{}' does not fit u32: {}",
                space.name, space.word_size
            ))
        })?;
        if address_size == 0 || word_size == 0 {
            return Err(LiftError::Parse(format!(
                "Sleigh space '{}' has invalid layout: address_size={} word_size={}",
                space.name, address_size, word_size
            )));
        }
        let space_endianness = Endianness::from_big_endian(space.big_endian);
        let space_id = ctx.add_space_with_layout(
            &space.name,
            address_size,
            word_size,
            is_default,
            Some(space_endianness),
        );
        if !target_ids.insert(space_id) {
            return Err(LiftError::Parse(format!(
                "Sleigh address space '{}' aliases already-mapped r2il space {space_id}",
                space.name
            )));
        }
        space_map.insert(space.id, space_id);

        if is_default {
            if saw_default_space {
                return Err(LiftError::Parse(
                    "Sleigh returned the default code space more than once".to_string(),
                ));
            }
            saw_default_space = true;
            ctx.set_addr_size(address_size);
            ctx.set_instruction_endianness(space_endianness);
            ctx.set_memory_endianness(space_endianness);
        }
    }
    if !saw_default_space {
        return Err(LiftError::Parse(
            "Sleigh default code space is absent from its address-space inventory".to_string(),
        ));
    }

    Ok(space_map)
}

pub(crate) fn extract_architecture(
    sleigh: &GhidraSleigh,
    arch_name: &str,
) -> Result<ExtractedSleighArchitecture, LiftError> {
    let mut ctx = LiftContext::new(arch_name);
    let spaces = sleigh.address_spaces();
    let space_map = extract_address_space_map(&mut ctx, &spaces, sleigh.default_code_space().id)?;

    if ctx.get_space("unique").is_none() {
        ctx.add_space("unique", 4, false);
    }

    for (varnode, name) in sleigh.register_name_map() {
        let size = u32::try_from(varnode.size).map_err(|_| {
            LiftError::Parse(format!(
                "Sleigh register '{name}' size does not fit u32: {}",
                varnode.size
            ))
        })?;
        ctx.add_register(&name, varnode.address.offset, size);
    }

    Ok(ExtractedSleighArchitecture {
        arch: ctx.finish(),
        space_map,
    })
}

/// Extract architecture metadata from a loaded GhidraSleigh instance.
///
/// This function extracts:
/// - Endianness
/// - Address spaces (RAM, Register, Unique, etc.)
/// - Register definitions
///
/// # Arguments
///
/// * `sleigh` - A reference to a loaded `GhidraSleigh` instance
/// * `arch_name` - Name to use for the architecture
///
/// # Returns
///
/// An `ArchSpec` containing the extracted metadata, or an error when the
/// Sleigh address-space layout cannot be represented exactly.
///
/// # Example
///
/// ```rust,ignore
/// use libsla::GhidraSleigh;
/// use r2sleigh_lift::sleigh::extract_arch_spec;
///
/// let sleigh = GhidraSleigh::builder()
///     .processor_spec(sleigh_config::processor_x86::PSPEC_X86_64)?
///     .build(sleigh_config::processor_x86::SLA_X86_64)?;
///
/// let spec = extract_arch_spec(&sleigh, "x86-64")?;
/// println!("Registers: {}", spec.registers.len());
/// ```
pub fn extract_arch_spec(sleigh: &GhidraSleigh, arch_name: &str) -> Result<ArchSpec, LiftError> {
    extract_architecture(sleigh, arch_name).map(|extracted| extracted.arch)
}

/// Build an ArchSpec from pre-compiled SLA data.
///
/// This is the primary way to create an ArchSpec for use with r2sleigh.
/// It uses pre-compiled `.sla` files from the `sleigh-config` crate.
///
/// # Arguments
///
/// * `sla_data` - Compiled SLA specification bytes
/// * `pspec_data` - Processor specification bytes
/// * `arch_name` - Name for the architecture
///
/// # Returns
///
/// An `ArchSpec` on success, or an error if loading fails.
///
/// # Example
///
/// ```rust,ignore
/// use r2sleigh_lift::sleigh::build_arch_spec;
///
/// let spec = build_arch_spec(
///     sleigh_config::processor_x86::SLA_X86_64,
///     sleigh_config::processor_x86::PSPEC_X86_64,
///     "x86-64"
/// )?;
/// ```
pub fn build_arch_spec(
    sla_data: &[u8],
    pspec_data: &str,
    arch_name: &str,
) -> Result<ArchSpec, LiftError> {
    let sleigh = GhidraSleigh::builder()
        .processor_spec(pspec_data)
        .map_err(|e| LiftError::Parse(format!("Failed to load processor spec: {}", e)))?
        .build(sla_data)
        .map_err(|e| LiftError::Parse(format!("Failed to load SLA data: {}", e)))?;

    extract_arch_spec(&sleigh, arch_name)
}

/// Metadata about a parsed Sleigh specification.
///
/// This struct provides information about a loaded Sleigh specification
/// that can be useful for debugging and diagnostics.
pub struct SleighInfo {
    /// The architecture specification
    pub spec: ArchSpec,
    /// Number of address spaces defined
    pub space_count: usize,
    /// Number of registers defined
    pub register_count: usize,
}

/// Get detailed information about a loaded Sleigh specification.
pub fn get_sleigh_info(sleigh: &GhidraSleigh, arch_name: &str) -> Result<SleighInfo, LiftError> {
    let spec = extract_arch_spec(sleigh, arch_name)?;
    let register_count = spec.registers.len();
    let space_count = spec.spaces.len();

    Ok(SleighInfo {
        spec,
        space_count,
        register_count,
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_extract_requires_sleigh_config() {
        // This test documents that extraction requires sleigh-config features
        // The actual tests are in the CLI crate with proper feature flags
    }
}
