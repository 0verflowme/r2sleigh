use std::fmt::{self, Write as _};
use std::hash::{Hash, Hasher};

use r2il::{ArchSpec, Endianness, R2ILBlock};

#[derive(Clone)]
struct Fnv64Hasher(u64);

impl Default for Fnv64Hasher {
    fn default() -> Self {
        Self(0xcbf29ce484222325)
    }
}

impl Hasher for Fnv64Hasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x100000001b3);
        }
    }
}

struct FnvFmtWriter<'a>(&'a mut Fnv64Hasher);

impl fmt::Write for FnvFmtWriter<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.write(s.as_bytes());
        Ok(())
    }
}

pub fn stable_fnv1a_hash<T: Hash + ?Sized>(value: &T) -> u64 {
    let mut hasher = Fnv64Hasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

pub fn stable_fnv1a_debug_hash<T: std::fmt::Debug + ?Sized>(value: &T) -> u64 {
    let mut hasher = Fnv64Hasher::default();
    let _ = write!(&mut FnvFmtWriter(&mut hasher), "{value:?}");
    hasher.finish()
}

pub fn stable_fnv1a_bytes(bytes: &[u8]) -> u64 {
    let mut hasher = Fnv64Hasher::default();
    hasher.write(bytes);
    hasher.finish()
}

/// Stable identity for an architecture specification.
///
/// `ArchSpec::register_map` is a `HashMap`, so hashing its `Debug` output can
/// vary across independently reconstructed but equivalent specifications. The
/// map is redundant with the ordered register declarations for ordinary
/// construction, but it still affects lookup semantics and is therefore
/// retained here in sorted form.
pub fn stable_arch_hash(arch: Option<&ArchSpec>) -> u64 {
    let Some(arch) = arch else {
        return stable_fnv1a_hash("r2engine-arch-identity-none-v1");
    };
    let endianness = |value: Endianness| match value {
        Endianness::Little => 0_u8,
        Endianness::Big => 1,
        Endianness::Mixed => 2,
        Endianness::Custom => 3,
    };
    let mut register_map = arch
        .register_map
        .iter()
        .map(|(name, offset)| (name.as_str(), *offset))
        .collect::<Vec<_>>();
    register_map.sort_unstable();
    let components = [
        stable_fnv1a_hash(arch.name.as_str()),
        stable_fnv1a_hash(arch.variant.as_str()),
        stable_fnv1a_hash(&arch.big_endian),
        stable_fnv1a_hash(&endianness(arch.instruction_endianness)),
        stable_fnv1a_hash(&endianness(arch.memory_endianness)),
        stable_fnv1a_hash(&arch.addr_size),
        stable_fnv1a_hash(&arch.alignment),
        stable_fnv1a_debug_hash(&arch.spaces),
        stable_fnv1a_debug_hash(&arch.registers),
        stable_fnv1a_hash(&register_map),
        stable_fnv1a_debug_hash(&arch.userops),
        stable_fnv1a_hash(&arch.source_files),
    ];
    stable_fnv1a_hash(&("r2engine-arch-identity-v1", components))
}

pub fn stable_blocks_hash(blocks: &[R2ILBlock]) -> u64 {
    let mut hasher = Fnv64Hasher::default();
    "r2il-blocks-v1".hash(&mut hasher);
    blocks.len().hash(&mut hasher);
    for block in blocks {
        block.addr.hash(&mut hasher);
        block.size.hash(&mut hasher);
        block.ops.len().hash(&mut hasher);
        for op in &block.ops {
            let _ = write!(&mut FnvFmtWriter(&mut hasher), "{op:?}");
        }
        let _ = write!(
            &mut FnvFmtWriter(&mut hasher),
            "{:?}{:?}",
            block.switch_info,
            block.op_metadata
        );
    }
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use r2il::{AddressSpace, ArchSpec, RegisterDef, SpaceId};

    use super::stable_arch_hash;

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("stable-arch-test");
        arch.addr_size = 8;
        arch.alignment = 4;
        arch.add_register(RegisterDef::new("x0", 0, 8));
        arch.add_register(RegisterDef::new("x1", 8, 8));
        arch.add_register(RegisterDef::new("sp", 16, 8));
        arch.add_space(AddressSpace::new(SpaceId::Custom(7), "data", 8));
        arch
    }

    #[test]
    fn architecture_hash_is_independent_of_hash_map_iteration_order() {
        let first = arch();
        let mut reordered = first.clone();
        reordered.register_map = HashMap::new();
        for register in reordered.registers.iter().rev() {
            reordered
                .register_map
                .insert(register.name.clone(), register.offset);
        }

        assert_eq!(
            stable_arch_hash(Some(&first)),
            stable_arch_hash(Some(&reordered))
        );

        reordered.register_map.insert("x0".to_string(), 24);
        assert_ne!(
            stable_arch_hash(Some(&first)),
            stable_arch_hash(Some(&reordered))
        );
        assert_ne!(stable_arch_hash(Some(&first)), stable_arch_hash(None));
    }
}
