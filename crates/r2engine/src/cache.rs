use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;
use std::sync::{Arc, RwLock};

use serde::{Deserialize, Serialize};

use crate::EngineCacheLayer;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CacheCounters {
    pub hits: u64,
    pub misses: u64,
    pub insertions: u64,
    pub evictions: u64,
}

impl CacheCounters {
    pub fn total_lookups(self) -> u64 {
        self.hits + self.misses
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineSessionCacheMetrics {
    pub analysis: CacheCounters,
}

impl EngineSessionCacheMetrics {
    pub fn total(self) -> CacheCounters {
        self.analysis
    }

    pub fn counters_for_layer(self, layer: EngineCacheLayer) -> CacheCounters {
        match layer {
            EngineCacheLayer::Analysis => self.analysis,
            EngineCacheLayer::MetricsSnapshot => self.total(),
        }
    }
}

pub struct SessionCache<K, V> {
    inner: RwLock<BoundedArcCache<K, V>>,
    counters: RwLock<CacheCounters>,
}

impl<K, V> SessionCache<K, V>
where
    K: Clone + Eq + Hash,
{
    pub fn new(limit: usize) -> Self {
        Self {
            inner: RwLock::new(BoundedArcCache::new(limit)),
            counters: RwLock::new(CacheCounters::default()),
        }
    }

    pub fn get_arc(&self, key: &K) -> Option<Arc<V>> {
        let value = self
            .inner
            .write()
            .expect("engine cache write lock poisoned")
            .get(key);
        let mut counters = self
            .counters
            .write()
            .expect("engine cache counters write lock poisoned");
        if value.is_some() {
            counters.hits += 1;
        } else {
            counters.misses += 1;
        }
        value
    }

    pub fn insert_arc(&self, key: K, value: Arc<V>) -> Arc<V> {
        let result = self
            .inner
            .write()
            .expect("engine cache write lock poisoned")
            .insert_if_absent(key, value);
        let mut counters = self
            .counters
            .write()
            .expect("engine cache counters write lock poisoned");
        if result.inserted {
            counters.insertions += 1;
            counters.evictions += result.evicted_count;
        }
        result.value
    }

    pub fn insert(&self, key: K, value: V) -> Arc<V> {
        self.insert_arc(key, Arc::new(value))
    }

    pub fn counters(&self) -> CacheCounters {
        *self
            .counters
            .read()
            .expect("engine cache counters read lock poisoned")
    }

    pub fn reset_counters(&self) {
        let _ = self.take_counters();
    }

    pub fn take_counters(&self) -> CacheCounters {
        std::mem::take(
            &mut *self
                .counters
                .write()
                .expect("engine cache counters write lock poisoned"),
        )
    }
}

struct BoundedArcCache<K, V> {
    limit: usize,
    entries: HashMap<K, (Arc<V>, u64)>,
    order: BTreeMap<u64, K>,
    next_ticket: u64,
}

struct CacheInsertResult<V> {
    value: Arc<V>,
    inserted: bool,
    evicted_count: u64,
}

impl<K, V> BoundedArcCache<K, V>
where
    K: Clone + Eq + Hash,
{
    fn new(limit: usize) -> Self {
        Self {
            limit,
            entries: HashMap::new(),
            order: BTreeMap::new(),
            next_ticket: 1,
        }
    }

    fn allocate_ticket(&mut self) -> u64 {
        let ticket = self.next_ticket;
        self.next_ticket = self.next_ticket.wrapping_add(1).max(1);
        ticket
    }

    fn get(&mut self, key: &K) -> Option<Arc<V>> {
        let new_ticket = self.allocate_ticket();
        let (value, old_ticket) = self.entries.get_mut(key)?;
        let value = value.clone();
        let previous_ticket = *old_ticket;
        *old_ticket = new_ticket;
        self.order.remove(&previous_ticket);
        self.order.insert(new_ticket, key.clone());
        Some(value)
    }

    fn insert_if_absent(&mut self, key: K, value: Arc<V>) -> CacheInsertResult<V> {
        if self.limit == 0 {
            return CacheInsertResult {
                value,
                inserted: false,
                evicted_count: 0,
            };
        }
        if let Some(value) = self.get(&key) {
            return CacheInsertResult {
                value,
                inserted: false,
                evicted_count: 0,
            };
        }
        let ticket = self.allocate_ticket();
        self.entries
            .insert(key.clone(), (Arc::clone(&value), ticket));
        self.order.insert(ticket, key);
        let mut evicted_count = 0;
        while self.entries.len() > self.limit {
            let Some((_, evicted_key)) = self.order.pop_first() else {
                break;
            };
            if self.entries.remove(&evicted_key).is_some() {
                evicted_count += 1;
            }
        }
        CacheInsertResult {
            value,
            inserted: true,
            evicted_count,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Barrier;
    use std::thread;

    #[test]
    fn concurrent_insert_if_absent_preserves_resident_arc_identity() {
        const THREAD_COUNT: usize = 8;

        let cache = Arc::new(SessionCache::new(4));
        let barrier = Arc::new(Barrier::new(THREAD_COUNT));
        let workers = (0..THREAD_COUNT)
            .map(|value| {
                let cache = Arc::clone(&cache);
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    let candidate = Arc::new(value);
                    barrier.wait();
                    cache.insert_arc(7, candidate)
                })
            })
            .collect::<Vec<_>>();
        let values = workers
            .into_iter()
            .map(|worker| worker.join().expect("cache insert worker"))
            .collect::<Vec<_>>();

        let resident = cache.get_arc(&7).expect("resident cache value");
        assert!(values.iter().all(|value| Arc::ptr_eq(value, &resident)));
        assert_eq!(cache.counters().insertions, 1);
    }
}
