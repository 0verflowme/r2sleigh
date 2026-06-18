use std::fmt::{self, Write as _};
use std::hash::{Hash, Hasher};

use r2il::R2ILBlock;

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
