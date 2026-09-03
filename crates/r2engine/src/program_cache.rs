//! Prepared SSA, kept for the life of the process and keyed by what built it.
//!
//! Every request arrives as one wire snapshot carrying the function asked for
//! and the bodies of the functions it calls, and the ingress lifted and
//! prepared every one of them on every request. Measured on the DecBench
//! `bzip2recover` build, three identical `pdd` calls on one function in one
//! radare2 session cost `callee_lift` 1.46s, 1.52s and 0.95s for the same
//! three callees, against a `decode` of 50 microseconds. Roughly eighty per
//! cent of a capture was work whose inputs had not changed since the last time
//! it was done.
//!
//! **The key is the input, byte for byte, not a hash of it.** A miss here
//! costs time; a wrong hit renders a body that is not the function's, and
//! nothing downstream would say so. A hash small enough to store is two claims
//! at once -- that it covers every input, and that no two inputs collide --
//! and neither can be checked here. The serialized snapshot *is* the whole
//! input to a lift, by construction of the V2 boundary: there is no second way
//! to reach a source. So holding it and comparing it states the identity
//! exactly instead of asserting it, for a few kilobytes per function and one
//! `memcmp` per lookup against the hundreds of milliseconds it saves.
//!
//! The semantic fingerprint from `r2ssa::stable_ssa_semantic_fingerprint` is
//! recorded beside each entry rather than used as the key, which is the only
//! place it can honestly sit: it is computed *from* the prepared artifact, so
//! it cannot be known until the work it would avoid has been done. What it is
//! good for is saying which semantics an entry holds, which is what a reused
//! artifact is checked against.
//!
//! **What bounds it.** One entry per function address per preparation, replaced
//! rather than added to when that address's input changes. The entry count is
//! therefore the number of distinct function addresses the session has asked
//! about, at most twice over,
//! which is the program's own function count -- a bound the data sets rather
//! than a number picked to be large enough. Nothing is evicted while a session
//! runs, because an eviction policy would have to guess which function a later
//! request wants, and the analysis sweep this exists for asks about all of
//! them.
//!
//! **Why one function map rather than one per binary.** Reuse is gated on the input
//! bytes being identical, and a lift is a function of its input alone, so an
//! entry matching byte for byte returns the artifact that binary's own
//! snapshot would have produced, whichever binary recorded it. The address
//! selects a candidate; the bytes are what makes reusing it sound. A
//! per-binary handle would add a key that changes nothing about which answers
//! are correct.
//!
//! Data object types are different: their scope is the program, while a
//! snapshot and renderer are function-local. The cache therefore also holds a
//! monotone program view keyed by object address. A missing or unplaceable
//! observation cannot displace an accepted source fact, and two accepted types
//! for one address poison that address into an explicit conflict. That makes
//! accidental reuse across program sessions lose precision rather than render
//! the wrong type. The map is bounded by the distinct data addresses observed
//! in the session, which is the data that must clear it.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};

/// One prepared function and the exact bytes it was prepared from.
///
/// Generic in the artifact so the map's own behaviour can be tested without
/// minting lift authority, which needs a real image and a real Sleigh profile.
struct CachedFunction<T> {
    /// The serialized snapshot this artifact was built from. Held whole,
    /// because a hash of it would be a completeness claim nothing can check.
    input: Box<[u8]>,
    /// Semantics of the prepared artifact, for reporting and for the check
    /// that a reused artifact is the one a fresh build would have produced.
    fingerprint: u64,
    artifact: T,
}

/// Which preparation an entry holds, because the same function prepares to two
/// different artifacts depending on why it was captured.
///
/// The function a request asks about is prepared knowing the recovered
/// interfaces of everything it calls, which is what lets a call site describe
/// its arguments. A body captured *as* a callee is prepared alone, since the
/// set is one level deep and it has no callee bodies of its own. Those are two
/// different artifacts for one address, so they are two different keys; a
/// single address key would have each eviction the other's cache miss.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PreparedRole {
    /// Prepared with the interfaces of the functions it calls.
    Root,
    /// Prepared alone, as one callee body inside somebody's capture.
    Callee,
}

/// What the cache has been asked and what it holds, for the timing line.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProgramCacheStats {
    pub entries: usize,
    pub hits: u64,
    pub misses: u64,
    /// Lookups that found the address and refused it because the input had
    /// changed. Worth separating from a first-ever miss: a session full of
    /// these means something is perturbing snapshots between requests, which
    /// is a defect rather than a cold cache.
    pub replacements: u64,
}

struct FunctionCache<T> {
    by_function: BTreeMap<(PreparedRole, u64), CachedFunction<T>>,
    hits: u64,
    misses: u64,
    replacements: u64,
}

impl<T> Default for FunctionCache<T> {
    fn default() -> Self {
        Self {
            by_function: BTreeMap::new(),
            hits: 0,
            misses: 0,
            replacements: 0,
        }
    }
}

impl<T: Clone> FunctionCache<T> {
    fn lookup(&mut self, role: PreparedRole, address: u64, input: &[u8]) -> Option<T> {
        match self.by_function.get(&(role, address)) {
            Some(entry) if entry.input.as_ref() == input => {
                self.hits += 1;
                Some(entry.artifact.clone())
            }
            Some(_) => {
                self.replacements += 1;
                self.misses += 1;
                None
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    fn insert(
        &mut self,
        role: PreparedRole,
        address: u64,
        input: &[u8],
        artifact: T,
        fingerprint: u64,
    ) {
        self.by_function.insert(
            (role, address),
            CachedFunction {
                input: Box::from(input),
                fingerprint,
                artifact,
            },
        );
    }

    fn fingerprint(&self, role: PreparedRole, address: u64) -> Option<u64> {
        self.by_function
            .get(&(role, address))
            .map(|entry| entry.fingerprint)
    }

    fn stats(&self) -> ProgramCacheStats {
        ProgramCacheStats {
            entries: self.by_function.len(),
            hits: self.hits,
            misses: self.misses,
            replacements: self.replacements,
        }
    }
}

#[derive(Default)]
struct ProgramCache {
    functions: FunctionCache<Arc<r2ssa::TrustedSsaArtifact>>,
    data_objects: r2types::ProgramDataObjectTypeFacts,
}

fn program_cache() -> &'static Mutex<ProgramCache> {
    static CACHE: OnceLock<Mutex<ProgramCache>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(ProgramCache::default()))
}

/// A poisoned cache is still a correct cache: every entry is immutable and
/// keyed by the bytes that built it, so a panic mid-insert cannot leave one
/// entry claiming another's input. Recovering the guard is right here, where
/// refusing would turn one panic into a permanently slow process.
fn lock_program_cache() -> MutexGuard<'static, ProgramCache> {
    program_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// The prepared artifact for this function, if one was built from exactly
/// these bytes.
pub fn cached_function_artifact(
    role: PreparedRole,
    address: u64,
    input: &[u8],
) -> Option<Arc<r2ssa::TrustedSsaArtifact>> {
    lock_program_cache().functions.lookup(role, address, input)
}

/// Record a prepared artifact under the bytes that produced it, and return the
/// semantics it was recorded as.
pub fn cache_function_artifact(
    role: PreparedRole,
    address: u64,
    input: &[u8],
    artifact: &Arc<r2ssa::TrustedSsaArtifact>,
) -> u64 {
    let fingerprint = r2ssa::stable_ssa_semantic_fingerprint(artifact.artifact());
    lock_program_cache()
        .functions
        .insert(role, address, input, Arc::clone(artifact), fingerprint);
    fingerprint
}

/// The semantics recorded for this address, if anything is recorded for it.
pub fn cached_function_fingerprint(role: PreparedRole, address: u64) -> Option<u64> {
    lock_program_cache().functions.fingerprint(role, address)
}

pub fn program_cache_stats() -> ProgramCacheStats {
    lock_program_cache().functions.stats()
}

/// Add source-owned observations and return the complete program-scope view.
pub fn cache_program_data_object_types(
    observed: &r2types::ProgramDataObjectTypeFacts,
) -> r2types::ProgramDataObjectTypeFacts {
    let mut cache = lock_program_cache();
    cache.data_objects.absorb(observed);
    cache.data_objects.clone()
}

/// Drop everything, so a caller can measure a cold cache. Production never
/// calls this: an entry is invalidated by its own address being asked for with
/// different bytes, which is the only event that can make one wrong.
pub fn clear_program_cache() {
    *lock_program_cache() = ProgramCache::default();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_same_address_with_the_same_bytes_returns_what_was_stored() {
        let mut cache = FunctionCache::<u32>::default();
        cache.insert(PreparedRole::Root, 0x1000, b"body", 99, 0xfeed);
        assert_eq!(cache.lookup(PreparedRole::Root, 0x1000, b"body"), Some(99));
        assert_eq!(cache.fingerprint(PreparedRole::Root, 0x1000), Some(0xfeed));
        let stats = cache.stats();
        assert_eq!((stats.hits, stats.misses, stats.entries), (1, 0, 1));
    }

    #[test]
    fn the_same_address_with_different_bytes_is_a_replacement_not_a_hit() {
        let mut cache = FunctionCache::<u32>::default();
        cache.insert(PreparedRole::Root, 0x1000, b"first", 99, 0xfeed);
        assert_eq!(cache.lookup(PreparedRole::Root, 0x1000, b"second"), None);
        let stats = cache.stats();
        assert_eq!((stats.hits, stats.replacements), (0, 1));
        // And the replacement is one entry, not two: the address is the key.
        cache.insert(PreparedRole::Root, 0x1000, b"second", 100, 0xbeef);
        assert_eq!(cache.stats().entries, 1);
        assert_eq!(
            cache.lookup(PreparedRole::Root, 0x1000, b"second"),
            Some(100)
        );
        assert_eq!(cache.lookup(PreparedRole::Root, 0x1000, b"first"), None);
    }

    #[test]
    fn one_address_prepared_two_ways_is_two_entries() {
        // A root knows its callees' interfaces and a callee body does not, so
        // storing both under the address alone would make each one evict the
        // other and neither would ever hit.
        let mut cache = FunctionCache::<u32>::default();
        cache.insert(PreparedRole::Root, 0x1000, b"root-capture", 1, 0xaa);
        cache.insert(PreparedRole::Callee, 0x1000, b"callee-body", 2, 0xbb);
        assert_eq!(cache.stats().entries, 2);
        assert_eq!(
            cache.lookup(PreparedRole::Root, 0x1000, b"root-capture"),
            Some(1)
        );
        assert_eq!(
            cache.lookup(PreparedRole::Callee, 0x1000, b"callee-body"),
            Some(2)
        );
        assert_eq!(cache.stats().replacements, 0);
    }

    #[test]
    fn an_unknown_address_is_a_plain_miss() {
        let mut cache = FunctionCache::<u32>::default();
        assert_eq!(cache.lookup(PreparedRole::Root, 0x2000, b"anything"), None);
        let stats = cache.stats();
        assert_eq!((stats.misses, stats.replacements, stats.entries), (1, 0, 0));
    }

    #[test]
    fn a_prefix_of_the_stored_input_is_not_the_stored_input() {
        // The comparison is over the whole buffer. A truncated snapshot that
        // agreed on every byte it had would otherwise reuse a body built from
        // more than it carries.
        let mut cache = FunctionCache::<u32>::default();
        cache.insert(PreparedRole::Root, 0x1000, b"body-and-more", 99, 0xfeed);
        assert_eq!(cache.lookup(PreparedRole::Root, 0x1000, b"body"), None);
        assert_eq!(cache.stats().replacements, 1);
    }

    #[test]
    fn a_data_object_type_survives_the_function_snapshot_that_carried_it() {
        let observed = r2types::ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, Some("int32_t"))],
            64,
            &r2types::ExternalTypeDb::default(),
        );
        let later_snapshot = r2types::ProgramDataObjectTypeFacts::from_radare2(
            [(0x7000, None)],
            64,
            &r2types::ExternalTypeDb::default(),
        );
        let mut cache = ProgramCache::default();
        cache.data_objects.absorb(&observed);
        cache.data_objects.absorb(&later_snapshot);

        assert_eq!(
            cache.data_objects.get(0x7000).map(|fact| &fact.ty),
            Some(&r2types::CTypeLike::i32())
        );
    }
}
