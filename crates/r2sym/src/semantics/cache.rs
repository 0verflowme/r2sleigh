use std::collections::HashMap;
use std::fmt::Write as _;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::{Arc, OnceLock, RwLock};

use r2il::ArchSpec;
use r2ssa::SsaArtifact;

use crate::sim::{PreparedFunctionScope, SummaryProfile};

use super::artifact::CompiledSemanticArtifact;

const SEMANTIC_CACHE_LIMIT: usize = 128;

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SemanticSeedMode {
    Static,
    Replay,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SemanticCacheKey {
    pub root_addr: u64,
    pub scope_hash: u64,
    pub arch_hash: u64,
    pub summary_profile: SummaryProfile,
    pub seed_mode: SemanticSeedMode,
}

#[derive(Debug, Clone)]
pub(crate) struct SemanticCompilationResult {
    pub artifact: Arc<CompiledSemanticArtifact>,
    pub cache_hit: bool,
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
    arch.map(hash_debug_value).unwrap_or(0)
}

fn function_hash(func: &SsaArtifact) -> u64 {
    let mut hasher = DefaultHasher::new();
    func.entry.hash(&mut hasher);
    hash_debug_value(&func.local_ssa_blocks()).hash(&mut hasher);
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
        function.name.hash(&mut hasher);
        function.prepared.function().entry.hash(&mut hasher);
        hash_debug_value(&function.prepared.local_ssa_blocks()).hash(&mut hasher);
    }
    hasher.finish()
}

pub(crate) fn semantic_cache_key(
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    arch: Option<&ArchSpec>,
    summary_profile: SummaryProfile,
    seed_mode: SemanticSeedMode,
) -> SemanticCacheKey {
    SemanticCacheKey {
        root_addr: func.entry,
        scope_hash: if scope.is_some() {
            stable_scope_hash(scope)
        } else {
            function_hash(func)
        },
        arch_hash: arch_hash(arch),
        summary_profile,
        seed_mode,
    }
}

fn semantic_cache() -> &'static RwLock<HashMap<SemanticCacheKey, Arc<CompiledSemanticArtifact>>> {
    static CACHE: OnceLock<RwLock<HashMap<SemanticCacheKey, Arc<CompiledSemanticArtifact>>>> =
        OnceLock::new();
    CACHE.get_or_init(|| RwLock::new(HashMap::new()))
}

pub(crate) fn lookup_semantic_cache(
    key: &SemanticCacheKey,
) -> Option<Arc<CompiledSemanticArtifact>> {
    semantic_cache()
        .read()
        .expect("semantic cache read lock poisoned")
        .get(key)
        .cloned()
}

pub(crate) fn cache_insert_bounded(
    key: SemanticCacheKey,
    value: Arc<CompiledSemanticArtifact>,
) -> Arc<CompiledSemanticArtifact> {
    let mut guard = semantic_cache()
        .write()
        .expect("semantic cache write lock poisoned");
    if guard.len() >= SEMANTIC_CACHE_LIMIT {
        guard.clear();
    }
    guard.insert(key, value.clone());
    value
}
