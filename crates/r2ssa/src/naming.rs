use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock, RwLock};

use r2il::{ArchSpec, SpaceId, Varnode, select_register_name};

pub type RegisterNameMap = HashMap<(u64, u32), String>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ArchLayoutHashKey {
    ptr_id: usize,
    name: String,
    variant: String,
    addr_size: u32,
    register_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ArchCacheTag {
    name: String,
    variant: String,
    addr_size: u32,
    register_layout_hash: u64,
}

impl ArchCacheTag {
    pub(crate) fn from_arch(arch: &ArchSpec) -> Self {
        let cache_key = ArchLayoutHashKey {
            ptr_id: arch as *const ArchSpec as usize,
            name: arch.name.clone(),
            variant: arch.variant.clone(),
            addr_size: arch.addr_size,
            register_count: arch.registers.len(),
        };
        if let Some(register_layout_hash) = arch_layout_hash_cache()
            .read()
            .expect("arch layout hash cache read lock poisoned")
            .get(&cache_key)
            .copied()
        {
            return Self {
                name: cache_key.name,
                variant: cache_key.variant,
                addr_size: cache_key.addr_size,
                register_layout_hash,
            };
        }

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        for reg in &arch.registers {
            reg.name.hash(&mut hasher);
            reg.offset.hash(&mut hasher);
            reg.size.hash(&mut hasher);
        }
        let register_layout_hash = hasher.finish();
        arch_layout_hash_cache()
            .write()
            .expect("arch layout hash cache write lock poisoned")
            .insert(cache_key.clone(), register_layout_hash);
        Self {
            name: cache_key.name,
            variant: cache_key.variant,
            addr_size: cache_key.addr_size,
            register_layout_hash,
        }
    }
}

fn arch_layout_hash_cache() -> &'static RwLock<HashMap<ArchLayoutHashKey, u64>> {
    static CACHE: OnceLock<RwLock<HashMap<ArchLayoutHashKey, u64>>> = OnceLock::new();
    CACHE.get_or_init(|| RwLock::new(HashMap::new()))
}

fn register_name_map_cache() -> &'static RwLock<HashMap<ArchCacheTag, Arc<RegisterNameMap>>> {
    static CACHE: OnceLock<RwLock<HashMap<ArchCacheTag, Arc<RegisterNameMap>>>> = OnceLock::new();
    CACHE.get_or_init(|| RwLock::new(HashMap::new()))
}

fn build_register_name_map_uncached(arch: &ArchSpec) -> RegisterNameMap {
    let mut names_by_key: HashMap<(u64, u32), Vec<&str>> =
        HashMap::with_capacity(arch.registers.len());
    for reg in &arch.registers {
        names_by_key
            .entry((reg.offset, reg.size))
            .or_default()
            .push(reg.name.as_str());
    }

    names_by_key
        .into_iter()
        .filter_map(|(key, names)| select_register_name(names).map(|name| (key, name)))
        .collect()
}

pub(crate) fn cached_register_name_map(arch: &ArchSpec) -> Arc<RegisterNameMap> {
    let cache_tag = ArchCacheTag::from_arch(arch);

    if let Some(cached) = register_name_map_cache()
        .read()
        .expect("register name cache read lock poisoned")
        .get(&cache_tag)
        .cloned()
    {
        return cached;
    }

    let map = Arc::new(build_register_name_map_uncached(arch));
    register_name_map_cache()
        .write()
        .expect("register name cache write lock poisoned")
        .insert(cache_tag, map.clone());
    map
}

/// Convert a varnode to a variable name.
///
/// For registers:
/// - If a name is found in the map, use the name directly (e.g., "rax")
/// - If no name is found, use "reg:offset" fallback (e.g., "reg:10")
pub fn varnode_to_name(vn: &Varnode, reg_names: Option<&RegisterNameMap>) -> String {
    match vn.space {
        SpaceId::Register => {
            if let Some(map) = reg_names
                && let Some(name) = map.get(&(vn.offset, vn.size))
            {
                return name.clone();
            }
            format!("reg:{:x}", vn.offset)
        }
        SpaceId::Unique => format!("tmp:{:x}", vn.offset),
        SpaceId::Const => format!("const:{:x}", vn.offset),
        SpaceId::Ram => format!("ram:{:x}", vn.offset),
        SpaceId::Custom(id) => format!("space{}:{:x}", id, vn.offset),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_varnode_to_name_without_map() {
        // Register without name map falls back to hex
        let vn = Varnode {
            space: SpaceId::Register,
            offset: 0x10,
            size: 8,
            meta: None,
        };
        assert_eq!(varnode_to_name(&vn, None), "reg:10");
    }

    #[test]
    fn test_varnode_to_name_with_map() {
        // Register with name map uses named register (no prefix)
        let mut map = RegisterNameMap::new();
        map.insert((0x10, 8), "rax".to_string());

        let vn = Varnode {
            space: SpaceId::Register,
            offset: 0x10,
            size: 8,
            meta: None,
        };
        assert_eq!(varnode_to_name(&vn, Some(&map)), "rax");
    }

    #[test]
    fn test_varnode_to_name_map_miss() {
        // Register not in map falls back to hex
        let mut map = RegisterNameMap::new();
        map.insert((0x20, 8), "rbx".to_string());

        let vn = Varnode {
            space: SpaceId::Register,
            offset: 0x10,
            size: 8,
            meta: None,
        };
        assert_eq!(varnode_to_name(&vn, Some(&map)), "reg:10");
    }

    #[test]
    fn test_varnode_to_name_other_spaces() {
        // Test other space types
        let const_vn = Varnode {
            space: SpaceId::Const,
            offset: 0x42,
            size: 4,
            meta: None,
        };
        assert_eq!(varnode_to_name(&const_vn, None), "const:42");

        let tmp_vn = Varnode {
            space: SpaceId::Unique,
            offset: 0x1000,
            size: 8,
            meta: None,
        };
        assert_eq!(varnode_to_name(&tmp_vn, None), "tmp:1000");

        let ram_vn = Varnode {
            space: SpaceId::Ram,
            offset: 0x400000,
            size: 8,
            meta: None,
        };
        assert_eq!(varnode_to_name(&ram_vn, None), "ram:400000");
    }
}
