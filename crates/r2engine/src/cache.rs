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
    pub artifacts: CacheCounters,
    pub renders: CacheCounters,
}

impl EngineSessionCacheMetrics {
    pub fn total(self) -> CacheCounters {
        CacheCounters {
            hits: self.analysis.hits + self.artifacts.hits + self.renders.hits,
            misses: self.analysis.misses + self.artifacts.misses + self.renders.misses,
            insertions: self.analysis.insertions
                + self.artifacts.insertions
                + self.renders.insertions,
            evictions: self.analysis.evictions + self.artifacts.evictions + self.renders.evictions,
        }
    }

    pub fn counters_for_layer(self, layer: EngineCacheLayer) -> CacheCounters {
        match layer {
            EngineCacheLayer::Analysis => self.analysis,
            EngineCacheLayer::Artifact => self.artifacts,
            EngineCacheLayer::Render => self.renders,
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
            .insert(key, value);
        let mut counters = self
            .counters
            .write()
            .expect("engine cache counters write lock poisoned");
        counters.insertions += 1;
        counters.evictions += result.evicted_count;
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
        *self
            .counters
            .write()
            .expect("engine cache counters write lock poisoned") = CacheCounters::default();
    }

    pub fn clear_entries(&self) {
        self.inner
            .write()
            .expect("engine cache write lock poisoned")
            .clear();
    }

    pub fn len(&self) -> usize {
        self.inner
            .read()
            .expect("engine cache read lock poisoned")
            .len()
    }
}

impl<K, V> SessionCache<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    pub fn get_cloned(&self, key: &K) -> Option<V> {
        self.get_arc(key).map(|value| (*value).clone())
    }

    pub fn insert_cloned(&self, key: K, value: V) -> V {
        self.insert(key, value).as_ref().clone()
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

    fn clear(&mut self) {
        self.entries.clear();
        self.order.clear();
        self.next_ticket = 1;
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

    fn insert(&mut self, key: K, value: Arc<V>) -> CacheInsertResult<V> {
        if self.limit == 0 {
            return CacheInsertResult {
                value,
                evicted_count: 0,
            };
        }
        let ticket = self.allocate_ticket();
        if let Some((_, old_ticket)) = self.entries.insert(key.clone(), (value.clone(), ticket)) {
            self.order.remove(&old_ticket);
        }
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
            evicted_count,
        }
    }

    fn len(&self) -> usize {
        self.entries.len()
    }
}
