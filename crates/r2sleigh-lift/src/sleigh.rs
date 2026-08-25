//! Sleigh specification metadata extraction.
//!
//! This module provides utilities for extracting architecture metadata from
//! loaded Sleigh specifications using `libsla`.

use libsla::{AddressSpace, AddressSpaceId, GhidraSleigh, Sleigh};
use r2il::{
    ArchSpec, Endianness, RegisterBitSlice, RegisterProjection, RegisterProjectionDisposition,
    RegisterProjectionRefusal, RegisterStorage, SpaceId,
};
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::LiftError;
use crate::context::LiftContext;

pub(crate) struct ExtractedSleighArchitecture {
    pub arch: ArchSpec,
    pub space_map: HashMap<AddressSpaceId, SpaceId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RegisterGeometryDeclaration {
    storage: RegisterStorage,
    /// `None` means byte significance was not supplied exactly.
    big_endian: Option<bool>,
}

fn register_declaration_endianness(
    declarations: &[RegisterGeometryDeclaration],
) -> Result<bool, RegisterProjectionRefusal> {
    let mut byte_order = None;
    let mut missing = false;
    for declaration in declarations {
        let Some(declared_order) = declaration.big_endian else {
            missing = true;
            continue;
        };
        match byte_order {
            Some(existing) if existing != declared_order => {
                return Err(RegisterProjectionRefusal::ConflictingDeclarations);
            }
            Some(_) => {}
            None => byte_order = Some(declared_order),
        }
    }
    if missing {
        Err(RegisterProjectionRefusal::MissingRegisterEndianness)
    } else {
        byte_order.ok_or(RegisterProjectionRefusal::MissingRegisterEndianness)
    }
}

#[derive(Debug, Clone, Copy)]
struct ValidRegisterGeometry {
    storage: RegisterStorage,
    end: u64,
    big_endian: Result<bool, RegisterProjectionRefusal>,
}

fn component_endianness(
    component: &[ValidRegisterGeometry],
) -> Result<bool, RegisterProjectionRefusal> {
    let mut byte_order = None;
    let mut missing = false;
    for geometry in component {
        match geometry.big_endian {
            Err(RegisterProjectionRefusal::ConflictingDeclarations) => {
                return Err(RegisterProjectionRefusal::ConflictingDeclarations);
            }
            Err(_) => missing = true,
            Ok(order) => match byte_order {
                Some(existing) if existing != order => {
                    return Err(RegisterProjectionRefusal::ConflictingDeclarations);
                }
                Some(_) => {}
                None => byte_order = Some(order),
            },
        }
    }
    if missing {
        Err(RegisterProjectionRefusal::MissingRegisterEndianness)
    } else {
        byte_order.ok_or(RegisterProjectionRefusal::MissingRegisterEndianness)
    }
}

fn component_has_partial_overlap(component: &[ValidRegisterGeometry]) -> bool {
    let mut containing_ends = Vec::<u64>::new();
    for geometry in component {
        while containing_ends
            .last()
            .is_some_and(|end| *end <= geometry.storage.offset)
        {
            containing_ends.pop();
        }
        if containing_ends
            .last()
            .is_some_and(|parent_end| geometry.end > *parent_end)
        {
            return true;
        }
        containing_ends.push(geometry.end);
    }
    false
}

/// Derive name-free register carrier geometry from exact Sleigh byte ranges.
///
/// The input may contain aliases with different display names. It is reduced
/// to one entry per unique storage before any containment decision is made, so
/// neither declaration order nor `RegisterDef::parent` strings can influence
/// the result. Construction is `O(n log n)`: one ordered aggregation and one
/// sorted interval sweep, with no repeated per-register family scan.
fn derive_register_projections(
    declarations: impl IntoIterator<Item = RegisterGeometryDeclaration>,
) -> Vec<RegisterProjection> {
    let mut declarations_by_storage =
        BTreeMap::<RegisterStorage, Vec<RegisterGeometryDeclaration>>::new();
    for declaration in declarations {
        declarations_by_storage
            .entry(declaration.storage)
            .or_default()
            .push(declaration);
    }

    let mut dispositions = BTreeMap::<RegisterStorage, RegisterProjectionDisposition>::new();
    let mut valid = Vec::new();
    for (&storage, declarations) in &declarations_by_storage {
        let Some(end) = storage.checked_end() else {
            dispositions.insert(
                storage,
                RegisterProjectionDisposition::Refused {
                    reason: RegisterProjectionRefusal::InvalidStorageRange,
                },
            );
            continue;
        };
        valid.push(ValidRegisterGeometry {
            storage,
            end,
            big_endian: register_declaration_endianness(declarations),
        });
    }

    // Equal starts put the widest interval first. That makes a valid laminar
    // component's unique maximal carrier its first entry and allows a stack to
    // detect crossings in one pass.
    valid.sort_by(|left, right| {
        left.storage
            .offset
            .cmp(&right.storage.offset)
            .then_with(|| right.end.cmp(&left.end))
            .then_with(|| left.storage.cmp(&right.storage))
    });

    let mut component_start = 0;
    while component_start < valid.len() {
        let mut component_end = valid[component_start].end;
        let mut component_limit = component_start + 1;
        while component_limit < valid.len() && valid[component_limit].storage.offset < component_end
        {
            component_end = component_end.max(valid[component_limit].end);
            component_limit += 1;
        }
        let component = &valid[component_start..component_limit];
        let byte_order = component_endianness(component);
        let refusal = if component_has_partial_overlap(component) {
            Some(RegisterProjectionRefusal::PartialOverlap)
        } else if !component[1..]
            .iter()
            .all(|geometry| component[0].storage.contains(geometry.storage))
        {
            Some(RegisterProjectionRefusal::AmbiguousContainingCarrier)
        } else {
            byte_order.err()
        };

        for geometry in component {
            let disposition = if let Some(reason) = refusal {
                RegisterProjectionDisposition::Refused { reason }
            } else {
                let carrier = component[0];
                let big_endian =
                    byte_order.expect("component refusal already covers missing byte significance");
                let byte_offset = if big_endian {
                    carrier.end - geometry.end
                } else {
                    geometry.storage.offset - carrier.storage.offset
                };
                RegisterProjectionDisposition::Bound {
                    carrier: carrier.storage,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: byte_offset * 8,
                        size_bits: u64::from(geometry.storage.size) * 8,
                    },
                }
            };
            dispositions.insert(geometry.storage, disposition);
        }
        component_start = component_limit;
    }

    declarations_by_storage
        .into_keys()
        .map(|written| RegisterProjection {
            written,
            disposition: dispositions
                .remove(&written)
                .expect("every aggregated register storage has exactly one disposition"),
        })
        .collect()
}

fn validate_extracted_register_geometry(arch: ArchSpec) -> Result<ArchSpec, LiftError> {
    r2il::validate_register_geometry(&arch).map_err(|error| {
        LiftError::Parse(format!(
            "Sleigh register geometry failed canonical r2il validation: {error}"
        ))
    })?;
    Ok(arch)
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
        let space_endianness = if space.big_endian {
            Endianness::Big
        } else {
            Endianness::Little
        };
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

    let register_endianness_by_source_space = spaces
        .iter()
        .map(|space| (space.id, space.big_endian))
        .collect::<HashMap<_, _>>();
    let mut register_geometry = Vec::new();
    for (varnode, name) in sleigh.register_name_map() {
        let size = u32::try_from(varnode.size).map_err(|_| {
            LiftError::Parse(format!(
                "Sleigh register '{name}' size does not fit u32: {}",
                varnode.size
            ))
        })?;
        ctx.add_register(&name, varnode.address.offset, size);
        register_geometry.push(RegisterGeometryDeclaration {
            storage: RegisterStorage {
                offset: varnode.address.offset,
                size,
            },
            big_endian: space_map
                .get(&varnode.address.address_space.id)
                .filter(|target| **target == SpaceId::Register)
                .and_then(|_| {
                    register_endianness_by_source_space
                        .get(&varnode.address.address_space.id)
                        .copied()
                }),
        });
    }
    ctx.arch.register_projections = derive_register_projections(register_geometry);

    let arch = validate_extracted_register_geometry(ctx.finish())?;

    Ok(ExtractedSleighArchitecture { arch, space_map })
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
    use super::*;

    fn declaration(
        offset: u64,
        size: u32,
        big_endian: Option<bool>,
    ) -> RegisterGeometryDeclaration {
        RegisterGeometryDeclaration {
            storage: RegisterStorage { offset, size },
            big_endian,
        }
    }

    fn expected_bound(
        written: RegisterStorage,
        carrier: RegisterStorage,
        lsb_bit_offset: u64,
    ) -> RegisterProjection {
        RegisterProjection {
            written,
            disposition: RegisterProjectionDisposition::Bound {
                carrier,
                slice: RegisterBitSlice {
                    lsb_bit_offset,
                    size_bits: u64::from(written.size) * 8,
                },
            },
        }
    }

    fn assert_named_projection(
        arch: &ArchSpec,
        written_name: &str,
        carrier_name: &str,
        lsb_bit_offset: u64,
    ) {
        let written = arch
            .get_register(written_name)
            .unwrap_or_else(|| panic!("missing embedded register {written_name}"))
            .storage();
        let carrier = arch
            .get_register(carrier_name)
            .unwrap_or_else(|| panic!("missing embedded register {carrier_name}"))
            .storage();
        assert_eq!(
            arch.register_projection(written),
            Some(&expected_bound(written, carrier, lsb_bit_offset)),
            "projection for {written_name}"
        );
    }

    #[test]
    fn invalid_extracted_register_range_is_reported_by_canonical_validator() {
        let mut arch = ArchSpec::new("invalid-register-range");
        arch.add_register(r2il::RegisterDef::new("overflow", u64::MAX, 2));

        let error = validate_extracted_register_geometry(arch)
            .expect_err("an overflowing extracted register range must be rejected");
        let LiftError::Parse(message) = error else {
            panic!("canonical geometry validation must surface as a parse error");
        };
        assert!(message.contains("canonical r2il validation"));
        assert!(message.contains("arch.registers.range.overflow"));
    }

    #[test]
    fn geometry_is_order_independent_and_refuses_unprovable_layouts() {
        let declarations = vec![
            declaration(0, 8, Some(false)),
            declaration(0, 4, Some(false)),
            declaration(1, 1, Some(false)),
            declaration(0, 4, Some(false)),
        ];
        let expected = vec![
            expected_bound(
                RegisterStorage { offset: 0, size: 4 },
                RegisterStorage { offset: 0, size: 8 },
                0,
            ),
            expected_bound(
                RegisterStorage { offset: 0, size: 8 },
                RegisterStorage { offset: 0, size: 8 },
                0,
            ),
            expected_bound(
                RegisterStorage { offset: 1, size: 1 },
                RegisterStorage { offset: 0, size: 8 },
                8,
            ),
        ];
        assert_eq!(derive_register_projections(declarations.clone()), expected);
        assert_eq!(
            derive_register_projections(declarations.into_iter().rev()),
            expected
        );

        let big_endian = derive_register_projections([
            declaration(0, 8, Some(true)),
            declaration(0, 4, Some(true)),
        ]);
        assert_eq!(
            big_endian[0],
            expected_bound(
                RegisterStorage { offset: 0, size: 4 },
                RegisterStorage { offset: 0, size: 8 },
                32,
            )
        );

        let partial = derive_register_projections([
            declaration(0, 8, Some(false)),
            declaration(4, 8, Some(false)),
        ]);
        assert!(partial.iter().all(|projection| {
            projection.disposition
                == RegisterProjectionDisposition::Refused {
                    reason: RegisterProjectionRefusal::PartialOverlap,
                }
        }));

        let non_laminar_component = derive_register_projections([
            declaration(0, 8, Some(false)),
            declaration(4, 8, Some(false)),
            declaration(0, 2, Some(false)),
            declaration(4, 2, Some(false)),
        ]);
        assert!(non_laminar_component.iter().all(|projection| {
            projection.disposition
                == RegisterProjectionDisposition::Refused {
                    reason: RegisterProjectionRefusal::PartialOverlap,
                }
        }));

        for (declarations, reason) in [
            (
                vec![declaration(0, 0, Some(false))],
                RegisterProjectionRefusal::InvalidStorageRange,
            ),
            (
                vec![declaration(0, 8, None)],
                RegisterProjectionRefusal::MissingRegisterEndianness,
            ),
            (
                vec![
                    declaration(0, 8, Some(false)),
                    declaration(0, 8, Some(true)),
                ],
                RegisterProjectionRefusal::ConflictingDeclarations,
            ),
        ] {
            assert_eq!(
                derive_register_projections(declarations)[0].disposition,
                RegisterProjectionDisposition::Refused { reason }
            );
        }

        let mixed_with_missing = vec![
            declaration(0, 8, None),
            declaration(0, 8, Some(false)),
            declaration(0, 8, Some(true)),
        ];
        let mixed_disposition = RegisterProjectionDisposition::Refused {
            reason: RegisterProjectionRefusal::ConflictingDeclarations,
        };
        assert_eq!(
            derive_register_projections(mixed_with_missing.clone())[0].disposition,
            mixed_disposition
        );
        assert_eq!(
            derive_register_projections(mixed_with_missing.into_iter().rev())[0].disposition,
            mixed_disposition
        );
    }

    #[cfg(feature = "x86")]
    #[test]
    fn embedded_x86_64_geometry_is_exact_and_trust_independent() {
        let arbitrary = build_arch_spec(
            sleigh_config::processor_x86::SLA_X86_64,
            sleigh_config::processor_x86::PSPEC_X86_64,
            "caller-label-is-not-policy",
        )
        .expect("analysis-only x86-64 specification");
        let trusted = crate::disasm::Disassembler::from_trusted_profile(
            crate::disasm::TrustedSleighProfile::X86_64,
        )
        .expect("trusted x86-64 specification");
        let mut bytes = [0_u8; 16];
        bytes[..2].copy_from_slice(&[0x31, 0xc0]);
        let trusted_block = trusted
            .lift_genuine_block(&bytes, 0x1000, 2)
            .expect("trusted xor eax, eax lift");
        let arch = &arbitrary;
        let trusted_arch = trusted_block.authority().arch_spec();

        r2il::validate_archspec(arch).expect("complete analysis-only x86-64 ArchSpec");
        r2il::validate_archspec(trusted_arch).expect("complete trusted x86-64 ArchSpec");

        assert_eq!(arch.register_projections, trusted_arch.register_projections);
        assert_named_projection(arch, "RAX", "RAX", 0);
        assert_named_projection(arch, "EAX", "RAX", 0);
        assert_named_projection(arch, "AX", "RAX", 0);
        assert_named_projection(arch, "AL", "RAX", 0);
        assert_named_projection(arch, "AH", "RAX", 8);

        let xmm0 = arch.get_register("XMM0").expect("embedded XMM0").storage();
        assert!(matches!(
            arch.register_projection(xmm0).map(|entry| entry.disposition),
            Some(RegisterProjectionDisposition::Bound { carrier, slice })
                if carrier.contains(xmm0)
                    && slice.size_bits == u64::from(xmm0.size) * 8
        ));

        // Sleigh extraction never supplies parent strings. Geometry remains a
        // separate source-owned table and therefore cannot depend on them.
        assert!(
            arch.registers
                .iter()
                .all(|register| register.parent.is_none())
        );
        let mut changed_display_metadata = arch.clone();
        for register in &mut changed_display_metadata.registers {
            register.parent = Some("deliberately-irrelevant".to_string());
        }
        assert_eq!(
            changed_display_metadata.register_projections,
            arch.register_projections
        );
    }

    #[cfg(feature = "arm")]
    #[test]
    fn embedded_aarch64_geometry_projects_w0_into_x0() {
        let trusted = crate::disasm::Disassembler::from_trusted_profile(
            crate::disasm::TrustedSleighProfile::Aarch64Le,
        )
        .expect("trusted AArch64 specification");
        let mut bytes = [0_u8; 16];
        bytes[..4].copy_from_slice(&[0xe0, 0x03, 0x01, 0x2a]);
        let trusted_block = trusted
            .lift_genuine_block(&bytes, 0x1000, 4)
            .expect("trusted mov w0, w1 lift");
        let arch = trusted_block.authority().arch_spec();

        r2il::validate_archspec(arch).expect("complete trusted AArch64 ArchSpec");

        assert_named_projection(arch, "x0", "x0", 0);
        assert_named_projection(arch, "w0", "x0", 0);
        assert!(
            arch.registers
                .iter()
                .all(|register| register.parent.is_none())
        );
    }
}
