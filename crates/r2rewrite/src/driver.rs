//! The fixpoint driver and the per-value result.
//!
//! Every imported node is canonicalised once, children before parents: the
//! importer interns children before parents, so id order is a topological
//! order, and a node visited in id order sees only canonical children. At a
//! node the driver rebuilds it over those children, normalises it, and tries
//! the rules in table order; a rule that fires yields a new term, which is
//! canonicalised the same way, and the loop repeats until no rule fires.
//!
//! Termination and the budget follow from one fact the proof test enforces
//! for every rule: the rewritten term is strictly smaller than the term it
//! replaces, as a tree. Normalisers add no node and are idempotent. So the
//! number of firings while canonicalising a node is at most the tree size of
//! the node's imported term, and that size is the budget. Exceeding it is a
//! rule bug, not a bad input: the node keeps its imported term and the
//! failure is recorded, and nothing refuses.
//!
//! Every container the driver iterates is ordered; the intern map is looked
//! up and never iterated. Two runs over one projection produce identical
//! arenas, and the seal relies on that.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use r2ssa::{
    CanonicalInstructionId, MachineExprId, MachineExprKind, MachineProjection, SsaArtifact,
    StructuredAccessId, ValueId,
};
use serde::Serialize;

use crate::canon::normalize;
use crate::import::{ExpansionPolicy, Import, default_expansion_policy, import_with};
use crate::rules::{RULES, RuleId};
use crate::term::{TermArena, TermId, TermKind};

/// One application of one rule: `to` replaced `from`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct Rewrite {
    pub rule: RuleId,
    pub from: TermId,
    pub to: TermId,
}

/// How many sites a value's canonical term may be rendered at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum Multiplicity {
    /// Once: the term reads something a second rendering would observe again.
    Once,
    /// At any reader: every leaf is a literal or an entry value the function
    /// never redefines, so rendering it twice computes the same value twice.
    Any,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CanonicalValue {
    pub value: ValueId,
    pub base_root: MachineExprId,
    pub canonical: TermId,
    /// Every rewrite that produced `canonical`, copy elisions included, in
    /// application order.
    pub trace: Box<[Rewrite]>,
    /// Instructions other than this value's own that rendering `canonical`
    /// renders: producers expanded into the term whose values the term no
    /// longer reads. The binding plan decides, per instruction, whether that
    /// rendering is admissible at this site.
    pub discharges: BTreeSet<CanonicalInstructionId>,
    pub multiplicity: Multiplicity,
}

/// The canonical term of the cell one structured memory access reads or
/// writes. For a load it is the value's own canonical term; for a store it
/// is the cell's, which has no value. A renderer spelling the access asks
/// here whether the cell is an array element.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CanonicalAccess {
    pub access: StructuredAccessId,
    pub canonical: TermId,
    pub trace: Box<[Rewrite]>,
    /// Instructions rendering `canonical` at the access renders: the address
    /// producers expanded into the term whose values it no longer reads.
    pub discharges: BTreeSet<CanonicalInstructionId>,
}

/// A node whose rewriting exceeded its derived budget.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BudgetFailure {
    pub term: TermId,
    pub budget: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum RewriteError {
    /// The projection names a value the artifact's graph does not have.
    ValueOutOfRange(ValueId),
}

impl std::fmt::Display for RewriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ValueOutOfRange(value) => write!(f, "value {value:?} is not in the graph"),
        }
    }
}

impl std::error::Error for RewriteError {}

#[derive(Debug, Clone)]
pub struct CanonicalRoots {
    arena: TermArena,
    import: Import,
    values: Box<[Option<CanonicalValue>]>,
    accesses: BTreeMap<StructuredAccessId, CanonicalAccess>,
    budget_failures: Vec<BudgetFailure>,
}

impl CanonicalRoots {
    pub fn arena(&self) -> &TermArena {
        &self.arena
    }

    pub fn import(&self) -> &Import {
        &self.import
    }

    pub fn value(&self, value: ValueId) -> Option<&CanonicalValue> {
        self.values.get(value.0 as usize)?.as_ref()
    }

    pub fn values(&self) -> impl Iterator<Item = &CanonicalValue> {
        self.values.iter().flatten()
    }

    pub fn access(&self, access: StructuredAccessId) -> Option<&CanonicalAccess> {
        self.accesses.get(&access)
    }

    pub fn accesses(&self) -> impl Iterator<Item = &CanonicalAccess> {
        self.accesses.values()
    }

    pub fn budget_failures(&self) -> &[BudgetFailure] {
        &self.budget_failures
    }

    /// Every rewrite of every value, keyed by rule id, for measurement.
    pub fn rewrite_counts(&self) -> BTreeMap<RuleId, usize> {
        let mut counts = BTreeMap::new();
        for value in self.values() {
            for rewrite in &value.trace {
                *counts.entry(rewrite.rule).or_insert(0) += 1;
            }
        }
        counts
    }
}

/// Whether the plan may render this term inline at a reader, as an
/// expression. Only an opaque root cannot be: it is rendered by the base
/// path, as a statement of its own.
pub fn renders_inline(arena: &TermArena, id: TermId) -> bool {
    !matches!(arena.term(id).kind, TermKind::Opaque(_))
}

/// The instructions rendering `canonical` in place of `value` renders besides
/// the value's own: every producer expanded into the imported term whose
/// value the canonical term no longer reads. The one function that answers
/// this; construction and the seal both call it.
pub fn discharged_origins(
    import: &Import,
    projection: &MachineProjection,
    arena: &TermArena,
    value: ValueId,
    canonical: TermId,
) -> BTreeSet<CanonicalInstructionId> {
    let Some(imported) = import.value(value) else {
        return BTreeSet::new();
    };
    discharged_from(&imported.substituted, projection, arena, canonical)
}

/// The producers among `substituted` whose values `canonical` no longer
/// reads.
fn discharged_from(
    substituted: &BTreeSet<CanonicalInstructionId>,
    projection: &MachineProjection,
    arena: &TermArena,
    canonical: TermId,
) -> BTreeSet<CanonicalInstructionId> {
    let mut discharged = substituted.clone();
    for leaf in arena.leaves(canonical) {
        if let Some(MachineExprKind::Source { binding, .. }) =
            projection.expr(leaf).map(|expr| expr.kind())
            && let Some(entity) = projection.entity_for_output(binding.value())
        {
            discharged.remove(&entity.producer());
        }
    }
    discharged
}

struct Budget {
    remaining: u64,
    limit: u64,
}

struct BudgetExceeded;

impl Budget {
    fn charge(&mut self) -> Result<(), BudgetExceeded> {
        if self.remaining == 0 {
            return Err(BudgetExceeded);
        }
        self.remaining -= 1;
        Ok(())
    }
}

struct Driver<'a> {
    arena: &'a mut TermArena,
    canonical: HashMap<TermId, TermId>,
    rewrites_at: HashMap<TermId, Vec<Rewrite>>,
}

impl Driver<'_> {
    fn canonicalize_node(
        &mut self,
        id: TermId,
        budget: &mut Budget,
    ) -> Result<TermId, BudgetExceeded> {
        if let Some(done) = self.canonical.get(&id) {
            return Ok(*done);
        }
        let term = self.arena.term(id);
        if term.kind.is_nullary() {
            // A leaf's definition was imported before the leaf was interned,
            // so its nodes precede the leaf and are canonical by now. Point
            // the leaf at the canonical form so rules that match through it
            // see the same shapes they see everywhere else.
            if let Some(definition) = self.arena.definition(id)
                && let Some(canonical) = self.canonical.get(&definition).copied()
            {
                self.arena.define(id, canonical);
            }
            self.canonical.insert(id, id);
            return Ok(id);
        }
        let mut children = Vec::with_capacity(3);
        for child in term.kind.children() {
            children.push(self.canonicalize_node(child, budget)?);
        }
        let rebuilt = self
            .arena
            .intern(term.ty, term.kind.with_children(&children));
        let mut current = normalize(self.arena, rebuilt);
        let mut fired_here = Vec::new();
        loop {
            let mut fired = None;
            for rule in RULES.iter().copied() {
                if let Some(to) = (rule.apply)(self.arena, current) {
                    fired = Some((rule.id, to));
                    break;
                }
            }
            let Some((rule, to)) = fired else {
                break;
            };
            budget.charge()?;
            fired_here.push(Rewrite {
                rule,
                from: current,
                to,
            });
            let to = self.canonicalize_node(to, budget)?;
            current = normalize(self.arena, to);
        }
        if !fired_here.is_empty() {
            self.rewrites_at.insert(id, fired_here);
        }
        self.canonical.insert(id, current);
        self.canonical.insert(current, current);
        Ok(current)
    }
}

/// Canonicalise every value of `projection` under the default expansion
/// policy.
pub fn canonicalize(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
) -> Result<CanonicalRoots, RewriteError> {
    canonicalize_with(artifact, projection, &default_expansion_policy)
}

/// Canonicalise every value of `projection`, asking `policy` whether each
/// read may absorb its producer's term.
pub fn canonicalize_with(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    policy: &ExpansionPolicy<'_>,
) -> Result<CanonicalRoots, RewriteError> {
    let graph = artifact.graph();
    for entity in projection.entities() {
        let value = entity.output().value();
        if graph.value(value).is_none() {
            return Err(RewriteError::ValueOutOfRange(value));
        }
    }
    let mut arena = TermArena::new();
    let import = import_with(artifact, projection, &mut arena, policy);
    // Definitionless constants have no machine entity and therefore no
    // `ImportedValue`, but the binding plan still renders them inline. Give
    // them a stable canonical term in the same dense value table as defined
    // values so every inline disposition can name a `TermId`.
    let mut literal_terms = BTreeMap::<ValueId, (MachineExprId, TermId)>::new();
    for (expr, node) in projection.arena().iter() {
        let MachineExprKind::Constant { binding, value } = node.kind() else {
            continue;
        };
        let term = arena.intern(*node.ty(), TermKind::Literal(*value));
        literal_terms.entry(binding.value()).or_insert((expr, term));
    }
    let imported_len = arena.len();
    let mut driver = Driver {
        arena: &mut arena,
        canonical: HashMap::new(),
        rewrites_at: HashMap::new(),
    };
    let mut budget_failures = Vec::new();
    for index in 0..imported_len {
        let id = TermId::from_index(index);
        if driver.canonical.contains_key(&id) {
            continue;
        }
        let limit = driver.arena.tree_measure(id);
        let mut budget = Budget {
            remaining: limit,
            limit,
        };
        if driver.canonicalize_node(id, &mut budget).is_err() {
            budget_failures.push(BudgetFailure {
                term: id,
                budget: budget.limit,
            });
            driver.canonical.insert(id, id);
        }
    }
    let Driver {
        canonical,
        rewrites_at,
        ..
    } = driver;
    let mut values: Vec<Option<CanonicalValue>> = vec![None; graph.values.len()];
    for imported in import.values() {
        let canonical_term = canonical
            .get(&imported.term)
            .copied()
            .unwrap_or(imported.term);
        let mut trace: Vec<Rewrite> = imported.trace.clone();
        trace.extend(collect_rewrites(&arena, &rewrites_at, imported.term));
        let discharges =
            discharged_origins(&import, projection, &arena, imported.value, canonical_term);
        let multiplicity = if import.is_duplicable(projection, &arena, canonical_term) {
            Multiplicity::Any
        } else {
            Multiplicity::Once
        };
        if let Some(cell) = values.get_mut(imported.value.0 as usize) {
            *cell = Some(CanonicalValue {
                value: imported.value,
                base_root: imported.base_root,
                canonical: canonical_term,
                trace: trace.into_boxed_slice(),
                discharges,
                multiplicity,
            });
        }
    }
    for (value, (base_root, term)) in literal_terms {
        let Some(cell) = values.get_mut(value.0 as usize) else {
            continue;
        };
        if cell.is_some() {
            continue;
        }
        let canonical_term = canonical.get(&term).copied().unwrap_or(term);
        *cell = Some(CanonicalValue {
            value,
            base_root,
            canonical: canonical_term,
            trace: Box::new([]),
            discharges: BTreeSet::new(),
            multiplicity: Multiplicity::Any,
        });
    }
    let mut accesses = BTreeMap::new();
    for imported in import.accesses() {
        let canonical_term = canonical
            .get(&imported.term)
            .copied()
            .unwrap_or(imported.term);
        let mut trace: Vec<Rewrite> = imported.trace.clone();
        trace.extend(collect_rewrites(&arena, &rewrites_at, imported.term));
        let discharges = discharged_from(&imported.substituted, projection, &arena, canonical_term);
        accesses.insert(
            imported.access,
            CanonicalAccess {
                access: imported.access,
                canonical: canonical_term,
                trace: trace.into_boxed_slice(),
                discharges,
            },
        );
    }
    Ok(CanonicalRoots {
        arena,
        import,
        values: values.into_boxed_slice(),
        accesses,
        budget_failures,
    })
}

/// The rewrites applied while canonicalising `root`: those recorded at every
/// node of its imported term, and at every term a recorded rewrite produced,
/// in first-visit order.
fn collect_rewrites(
    arena: &TermArena,
    rewrites_at: &HashMap<TermId, Vec<Rewrite>>,
    root: TermId,
) -> Vec<Rewrite> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        if let Some(rewrites) = rewrites_at.get(&id) {
            for rewrite in rewrites {
                out.push(*rewrite);
                stack.push(rewrite.to);
            }
        }
        let children: Vec<TermId> = arena.term(id).kind.children().collect();
        stack.extend(children.into_iter().rev());
    }
    out
}
