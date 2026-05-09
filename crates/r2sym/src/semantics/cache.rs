use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::{Arc, OnceLock, RwLock};

use r2il::ArchSpec;
use r2ssa::{SSAOp, SsaArtifact};

use crate::sim::{PreparedFunctionScope, SummaryProfile};

use super::artifact::SemanticArtifact;

const SEMANTIC_CACHE_LIMIT: usize = 128;
pub const SEMANTIC_ARTIFACT_SCHEMA_VERSION: u32 = 7;

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SemanticSeedMode {
    Static,
    Replay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SemanticCacheScopeKind {
    Exact,
    CoarseLargeSlice,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SemanticCacheKey {
    pub schema_version: u32,
    pub root_addr: u64,
    pub scope_hash: u64,
    pub arch_hash: u64,
    pub summary_profile: SummaryProfile,
    pub seed_mode: SemanticSeedMode,
    pub replay_seed_fingerprint: u64,
    pub scope_kind: SemanticCacheScopeKind,
}

struct BoundedArcCache<K, V> {
    limit: usize,
    entries: HashMap<K, (Arc<V>, u64)>,
    order: BTreeMap<u64, K>,
    next_ticket: u64,
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

    fn insert(&mut self, key: K, value: Arc<V>) -> Arc<V> {
        if self.limit == 0 {
            return value;
        }
        let ticket = self.allocate_ticket();
        if let Some((_, old_ticket)) = self.entries.insert(key.clone(), (value.clone(), ticket)) {
            self.order.remove(&old_ticket);
        }
        self.order.insert(ticket, key);
        while self.entries.len() > self.limit {
            let Some((_, evicted_key)) = self.order.pop_first() else {
                break;
            };
            self.entries.remove(&evicted_key);
        }
        value
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.entries.len()
    }
}

#[derive(Debug, Clone)]
pub struct SemanticCompilationResult {
    pub artifact: Arc<SemanticArtifact>,
    pub cache_hit: bool,
    pub seed_mode: SemanticSeedMode,
    pub replay_seed_fingerprint: u64,
}

fn hash_debug_value<T: std::fmt::Debug>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    let _ = write!(&mut HasherAdapter(&mut hasher), "{value:?}");
    hasher.finish()
}

struct HasherAdapter<'a>(&'a mut DefaultHasher);

impl std::fmt::Write for HasherAdapter<'_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0.write(s.as_bytes());
        Ok(())
    }
}

fn arch_hash(arch: Option<&ArchSpec>) -> u64 {
    let Some(arch) = arch else {
        return 0;
    };
    let mut hasher = DefaultHasher::new();
    arch.name.hash(&mut hasher);
    arch.variant.hash(&mut hasher);
    arch.big_endian.hash(&mut hasher);
    format!("{:?}", arch.instruction_endianness).hash(&mut hasher);
    format!("{:?}", arch.memory_endianness).hash(&mut hasher);
    arch.addr_size.hash(&mut hasher);
    arch.alignment.hash(&mut hasher);
    for space in &arch.spaces {
        hash_debug_value(space).hash(&mut hasher);
    }
    for register in &arch.registers {
        hash_debug_value(register).hash(&mut hasher);
    }
    for (name, offset) in arch.register_map.iter().collect::<BTreeMap<_, _>>() {
        name.hash(&mut hasher);
        offset.hash(&mut hasher);
    }
    for userop in &arch.userops {
        hash_debug_value(userop).hash(&mut hasher);
    }
    for source_file in &arch.source_files {
        source_file.hash(&mut hasher);
    }
    hasher.finish()
}

fn strip_ssa_version_suffix(name: &str) -> &str {
    name.rsplit_once('_')
        .filter(|(_, version)| !version.is_empty() && version.chars().all(|ch| ch.is_ascii_digit()))
        .map(|(base, _)| base)
        .unwrap_or(name)
}

fn hash_ssa_var_shape<H: Hasher>(hasher: &mut H, var: &r2ssa::SSAVar) {
    strip_ssa_version_suffix(&var.name).hash(hasher);
    var.size.hash(hasher);
}

fn hash_ssa_op_shape<H: Hasher>(hasher: &mut H, op: &SSAOp) {
    std::mem::discriminant(op).hash(hasher);
    if let Some(dst) = op.dst() {
        hash_ssa_var_shape(hasher, dst);
    }
    let sources = op.sources();
    sources.len().hash(hasher);
    for src in sources {
        hash_ssa_var_shape(hasher, src);
    }

    match op {
        SSAOp::Subpiece { offset, .. } => offset.hash(hasher),
        SSAOp::PtrAdd { element_size, .. } | SSAOp::PtrSub { element_size, .. } => {
            element_size.hash(hasher);
        }
        SSAOp::Load { space, .. }
        | SSAOp::Store { space, .. }
        | SSAOp::LoadLinked { space, .. }
        | SSAOp::StoreConditional { space, .. }
        | SSAOp::AtomicCAS { space, .. }
        | SSAOp::LoadGuarded { space, .. }
        | SSAOp::StoreGuarded { space, .. } => {
            space.hash(hasher);
        }
        _ => {}
    }
}

fn ssa_shape_hash(func: &SsaArtifact) -> u64 {
    let mut hasher = DefaultHasher::new();
    for block in func.local_ssa_blocks() {
        block.addr.hash(&mut hasher);
        block.size.hash(&mut hasher);
        block.ops.len().hash(&mut hasher);
        for op in &block.ops {
            hash_ssa_op_shape(&mut hasher, op);
        }
    }
    hasher.finish()
}

fn function_hash(func: &SsaArtifact) -> u64 {
    let mut hasher = DefaultHasher::new();
    func.entry.hash(&mut hasher);
    ssa_shape_hash(func).hash(&mut hasher);
    hasher.finish()
}

pub fn stable_scope_hash(scope: Option<&PreparedFunctionScope>) -> u64 {
    let Some(scope) = scope else {
        return 0;
    };
    let mut hasher = DefaultHasher::new();
    scope.root_id().hash(&mut hasher);
    for function in scope.functions().values() {
        function.id.hash(&mut hasher);
        function.prepared.function().entry.hash(&mut hasher);
        ssa_shape_hash(&function.prepared).hash(&mut hasher);
    }
    hasher.finish()
}

pub(crate) fn semantic_cache_key(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    summary_profile: SummaryProfile,
    seed_mode: SemanticSeedMode,
    replay_seed_fingerprint: u64,
) -> SemanticCacheKey {
    SemanticCacheKey {
        schema_version: SEMANTIC_ARTIFACT_SCHEMA_VERSION,
        root_addr: func.entry,
        scope_hash: if scope.is_some() {
            stable_scope_hash(scope)
        } else {
            function_hash(func)
        },
        arch_hash: arch_hash(arch),
        summary_profile,
        seed_mode,
        replay_seed_fingerprint,
        scope_kind: SemanticCacheScopeKind::Exact,
    }
}

pub(crate) fn coarse_large_slice_cache_key(
    root_addr: u64,
    scope: &PreparedFunctionScope,
    arch: Option<&ArchSpec>,
    summary_profile: SummaryProfile,
    seed_mode: SemanticSeedMode,
    replay_seed_fingerprint: u64,
) -> SemanticCacheKey {
    SemanticCacheKey {
        schema_version: SEMANTIC_ARTIFACT_SCHEMA_VERSION,
        root_addr,
        scope_hash: stable_scope_hash(Some(scope)),
        arch_hash: arch_hash(arch),
        summary_profile,
        seed_mode,
        replay_seed_fingerprint,
        scope_kind: SemanticCacheScopeKind::CoarseLargeSlice,
    }
}

fn semantic_cache() -> &'static RwLock<BoundedArcCache<SemanticCacheKey, SemanticArtifact>> {
    static CACHE: OnceLock<RwLock<BoundedArcCache<SemanticCacheKey, SemanticArtifact>>> =
        OnceLock::new();
    CACHE.get_or_init(|| RwLock::new(BoundedArcCache::new(SEMANTIC_CACHE_LIMIT)))
}

pub(crate) fn lookup_semantic_cache(key: &SemanticCacheKey) -> Option<Arc<SemanticArtifact>> {
    semantic_cache()
        .write()
        .expect("semantic cache write lock poisoned")
        .get(key)
}

pub(crate) fn cache_insert_bounded(
    key: SemanticCacheKey,
    value: Arc<SemanticArtifact>,
) -> Arc<SemanticArtifact> {
    let mut guard = semantic_cache()
        .write()
        .expect("semantic cache write lock poisoned");
    guard.insert(key, value)
}

#[cfg(test)]
mod display_name_tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{InterprocFunctionId, SsaArtifact};

    use crate::sim::{PreparedFunctionScope, ScopedPreparedFunction};

    use super::{
        BoundedArcCache, SEMANTIC_ARTIFACT_SCHEMA_VERSION, SemanticCacheScopeKind,
        SemanticSeedMode, coarse_large_slice_cache_key, semantic_cache_key, stable_scope_hash,
    };

    const RAX: u64 = 0;

    fn test_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", RAX, 8));
        arch
    }

    fn make_const(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    #[test]
    fn bounded_cache_evicts_one_oldest_entry_and_refreshes_recency() {
        let mut cache = BoundedArcCache::new(2);
        cache.insert(1_u64, std::sync::Arc::new("one".to_string()));
        cache.insert(2_u64, std::sync::Arc::new("two".to_string()));
        assert_eq!(cache.get(&1).as_deref().map(String::as_str), Some("one"));

        cache.insert(3_u64, std::sync::Arc::new("three".to_string()));

        assert_eq!(cache.len(), 2);
        assert_eq!(cache.get(&1).as_deref().map(String::as_str), Some("one"));
        assert!(cache.get(&2).is_none());
        assert_eq!(cache.get(&3).as_deref().map(String::as_str), Some("three"));
    }

    #[test]
    fn semantic_cache_keys_use_explicit_schema_version() {
        let func = SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x401000,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&test_arch()),
        )
        .expect("ssa");
        let exact_key = semantic_cache_key(
            &func,
            None,
            Some(&test_arch()),
            crate::sim::SummaryProfile::Default,
            SemanticSeedMode::Static,
            0,
        );
        let coarse_key = coarse_large_slice_cache_key(
            func.entry,
            &PreparedFunctionScope::new(
                0x401000,
                vec![ScopedPreparedFunction {
                    id: InterprocFunctionId(0x401000),
                    name: Some("sym.main".to_string()),
                    prepared: func.clone(),
                }],
            )
            .expect("scope"),
            Some(&test_arch()),
            crate::sim::SummaryProfile::Default,
            SemanticSeedMode::Static,
            0,
        );
        assert_eq!(exact_key.schema_version, SEMANTIC_ARTIFACT_SCHEMA_VERSION);
        assert_eq!(coarse_key.schema_version, SEMANTIC_ARTIFACT_SCHEMA_VERSION);
        assert_eq!(exact_key.replay_seed_fingerprint, 0);
        assert!(matches!(
            exact_key.scope_kind,
            SemanticCacheScopeKind::Exact
        ));
        assert!(matches!(
            coarse_key.scope_kind,
            SemanticCacheScopeKind::CoarseLargeSlice
        ));
    }

    #[test]
    fn semantic_cache_keys_partition_replay_seed_identity() {
        let func = SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: 0x401000,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            Some(&test_arch()),
        )
        .expect("ssa");
        let static_key = semantic_cache_key(
            &func,
            None,
            Some(&test_arch()),
            crate::sim::SummaryProfile::Default,
            SemanticSeedMode::Static,
            0,
        );
        let replay_key_a = semantic_cache_key(
            &func,
            None,
            Some(&test_arch()),
            crate::sim::SummaryProfile::Default,
            SemanticSeedMode::Replay,
            0x11,
        );
        let replay_key_b = semantic_cache_key(
            &func,
            None,
            Some(&test_arch()),
            crate::sim::SummaryProfile::Default,
            SemanticSeedMode::Replay,
            0x22,
        );

        assert_eq!(static_key.seed_mode, SemanticSeedMode::Static);
        assert_eq!(static_key.replay_seed_fingerprint, 0);
        assert_ne!(replay_key_a, replay_key_b);
    }

    fn simple_function(entry: u64) -> SsaArtifact {
        let blocks = vec![R2ILBlock {
            addr: entry,
            size: 1,
            ops: vec![R2ILOp::Return {
                target: make_const(0, 8),
            }],
            switch_info: None,
            op_metadata: Default::default(),
        }];
        SsaArtifact::for_symbolic(&blocks, Some(&test_arch())).expect("ssa")
    }

    #[test]
    fn stable_scope_hash_ignores_non_semantic_names() {
        let root = ScopedPreparedFunction {
            id: InterprocFunctionId(0x1000),
            name: Some("sym.root".to_string()),
            prepared: simple_function(0x1000),
        };
        let helper_named = ScopedPreparedFunction {
            id: InterprocFunctionId(0x2000),
            name: Some("dbg.helper".to_string()),
            prepared: simple_function(0x2000),
        };
        let helper_renamed = ScopedPreparedFunction {
            id: InterprocFunctionId(0x2000),
            name: Some("fcn.2000".to_string()),
            prepared: simple_function(0x2000),
        };

        let left =
            PreparedFunctionScope::new(0x1000, vec![root.clone(), helper_named]).expect("scope");
        let right = PreparedFunctionScope::new(0x1000, vec![root, helper_renamed]).expect("scope");

        assert_eq!(
            stable_scope_hash(Some(&left)),
            stable_scope_hash(Some(&right))
        );
    }
}

#[cfg(test)]
mod tests {
    use r2il::{R2ILBlock, R2ILOp, SpaceId, Varnode};
    use r2ssa::{InterprocFunctionId, SsaArtifact};

    use crate::sim::{PreparedFunctionScope, ScopedPreparedFunction};

    use super::stable_scope_hash;

    fn make_const(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    fn make_leaf(entry: u64) -> SsaArtifact {
        SsaArtifact::for_symbolic(
            &[R2ILBlock {
                addr: entry,
                size: 1,
                ops: vec![R2ILOp::Return {
                    target: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            }],
            None,
        )
        .expect("ssa")
    }

    fn make_scope(root_name: &str, helper_name: &str) -> PreparedFunctionScope {
        PreparedFunctionScope::new(
            0x1000,
            vec![
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x1000),
                    name: Some(root_name.to_string()),
                    prepared: make_leaf(0x1000).with_name(root_name),
                },
                ScopedPreparedFunction {
                    id: InterprocFunctionId(0x2000),
                    name: Some(helper_name.to_string()),
                    prepared: make_leaf(0x2000).with_name(helper_name),
                },
            ],
        )
        .expect("scope")
    }

    #[test]
    fn stable_scope_hash_ignores_display_name_drift() {
        let left = make_scope("sym.worker", "sym.helper");
        let right = make_scope("dbg.worker", "fcn.2000");
        assert_eq!(
            stable_scope_hash(Some(&left)),
            stable_scope_hash(Some(&right))
        );
    }
}
