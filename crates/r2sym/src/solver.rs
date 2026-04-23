//! Z3 solver wrapper for constraint solving.
//!
//! This module provides a high-level interface to Z3 for checking
//! path feasibility and extracting concrete values.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::time::Duration;

use z3::ast::{Ast, BV, Bool, Dynamic};
use z3::{AstKind, Context, DeclKind, Model, Params, Solver};

use crate::state::{ConstraintCursorKey, SymState};
use crate::value::SymValue;

/// Result of a satisfiability check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatResult {
    /// The constraints are satisfiable.
    Sat,
    /// The constraints are unsatisfiable.
    Unsat,
    /// The solver could not determine satisfiability (timeout, etc.).
    Unknown,
}

impl From<z3::SatResult> for SatResult {
    fn from(r: z3::SatResult) -> Self {
        match r {
            z3::SatResult::Sat => SatResult::Sat,
            z3::SatResult::Unsat => SatResult::Unsat,
            z3::SatResult::Unknown => SatResult::Unknown,
        }
    }
}

/// Lightweight counters for solver-heavy symbolic execution workflows.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SolverStats {
    /// Number of state satisfiability queries.
    pub sat_queries: usize,
    /// Number of satisfiability queries answered from the cache.
    pub sat_cache_hits: usize,
    /// Number of satisfiability queries that required a solver check.
    pub sat_cache_misses: usize,
    /// Number of model-building solve requests.
    pub solve_calls: usize,
    /// Number of solve calls that returned early from a cached UNSAT result.
    pub solve_unsat_shortcuts: usize,
}

/// A wrapper around Z3's solver with convenience methods.
pub struct SymSolver<'ctx> {
    /// The Z3 context.
    ctx: &'ctx Context,
    /// The user-visible manual solver.
    solver: Solver,
    /// Incremental solver for exact state-cursor queries.
    state_solver: Solver,
    /// Incremental solver for query-local selected constraints.
    selection_solver: Solver,
    /// Scratch solver for sliced one-shot queries.
    scratch_solver: Solver,
    /// Timeout in milliseconds (0 = no timeout).
    timeout_ms: u32,
    /// Memoized satisfiability results for state queries.
    sat_cache: RefCell<HashMap<ConstraintCursorKey, SatResult>>,
    /// Cached dependency and partition analysis for cursor-based states.
    analysis_cache: RefCell<ConstraintAnalysisCache>,
    /// Current assertion stack for the incremental state solver.
    state_session: RefCell<SolverCursorSession>,
    /// Current assertion set for the incremental selection solver.
    selection_session: RefCell<SelectionSolverSession>,
    /// Internal counters used for perf/debug summaries.
    stats: RefCell<SolverStats>,
}

#[derive(Debug, Clone)]
struct SolverCursorSession {
    asserted_stack: Vec<ConstraintCursorKey>,
}

#[derive(Debug, Clone, Default)]
struct SelectionSolverSession {
    asserted_key: Option<ConstraintSelectionKey>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SolverMode {
    ExploreFast,
    QueryDeep,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DependencyAtom(Dynamic);

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct UnsignedInterval {
    min: u64,
    max: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AbstractValueFacts {
    exact: Option<u64>,
    interval: Option<UnsignedInterval>,
    nonzero: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct AbstractFacts {
    unsat: bool,
    values: HashMap<DependencyAtom, AbstractValueFacts>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ConstraintSelectionKey {
    state_key: ConstraintCursorKey,
    full_state: bool,
    partition_ids: Vec<usize>,
}

#[derive(Clone)]
struct ConstraintSelection {
    key: ConstraintSelectionKey,
    constraints: Vec<Bool>,
    abstract_facts: AbstractFacts,
    is_full_state: bool,
}

#[derive(Clone, Default)]
struct ConstraintPartition {
    id: usize,
    constraints: Vec<Bool>,
    atoms: HashSet<DependencyAtom>,
    abstract_facts: AbstractFacts,
}

#[derive(Clone, Default)]
struct StateConstraintAnalysis {
    ground_constraints: Vec<Bool>,
    ground_abstract_facts: AbstractFacts,
    partitions: Vec<ConstraintPartition>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct PartitionSatCacheKey {
    state_key: ConstraintCursorKey,
    partition_id: usize,
}

#[derive(Clone)]
struct CursorConstraintFacts {
    parent: ConstraintCursorKey,
    deps: HashSet<DependencyAtom>,
    abstract_delta: AbstractFacts,
    is_ground: bool,
}

impl Default for CursorConstraintFacts {
    fn default() -> Self {
        Self {
            parent: ConstraintCursorKey::ROOT,
            deps: HashSet::new(),
            abstract_delta: AbstractFacts::default(),
            is_ground: true,
        }
    }
}

#[derive(Default)]
struct ConstraintAnalysisCache {
    cursor_facts: HashMap<ConstraintCursorKey, CursorConstraintFacts>,
    state_cache: HashMap<ConstraintCursorKey, Rc<StateConstraintAnalysis>>,
    ground_sat_cache: HashMap<ConstraintCursorKey, SatResult>,
    partition_sat_cache: HashMap<PartitionSatCacheKey, SatResult>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeepQueryKind {
    Predicate,
    Model,
}

impl Default for SolverCursorSession {
    fn default() -> Self {
        Self {
            asserted_stack: vec![ConstraintCursorKey::ROOT],
        }
    }
}

impl AbstractValueFacts {
    fn update_exact(&mut self, value: u64) {
        if let Some(existing) = self.exact {
            if existing != value {
                self.interval = Some(UnsignedInterval { min: 1, max: 0 });
            }
        } else {
            self.exact = Some(value);
        }
        self.tighten_interval(value, value);
        if value != 0 {
            self.nonzero = true;
        }
    }

    fn tighten_interval(&mut self, min: u64, max: u64) {
        let interval = self.interval.get_or_insert(UnsignedInterval {
            min: 0,
            max: u64::MAX,
        });
        interval.min = interval.min.max(min);
        interval.max = interval.max.min(max);
    }

    fn mark_nonzero(&mut self) {
        self.nonzero = true;
        if let Some(0) = self.exact {
            self.interval = Some(UnsignedInterval { min: 1, max: 0 });
        } else if let Some(interval) = &mut self.interval
            && interval.min == 0
            && interval.max > 0
        {
            interval.min = 1;
        }
    }

    fn is_unsat(&self) -> bool {
        matches!(self.interval, Some(UnsignedInterval { min, max }) if min > max)
    }
}

impl AbstractFacts {
    fn merge(&mut self, other: &Self) {
        if self.unsat || other.unsat {
            self.unsat = true;
            return;
        }
        for (atom, other_facts) in &other.values {
            let facts = self.values.entry(atom.clone()).or_default();
            if let Some(value) = other_facts.exact {
                facts.update_exact(value);
            }
            if let Some(interval) = &other_facts.interval {
                facts.tighten_interval(interval.min, interval.max);
            }
            if other_facts.nonzero {
                facts.mark_nonzero();
            }
            if facts.is_unsat() {
                self.unsat = true;
                return;
            }
        }
    }

    fn record_eq(&mut self, atom: DependencyAtom, value: u64) {
        let facts = self.values.entry(atom).or_default();
        facts.update_exact(value);
        if facts.is_unsat() {
            self.unsat = true;
        }
    }

    fn record_ne(&mut self, atom: DependencyAtom, value: u64) {
        let facts = self.values.entry(atom).or_default();
        if facts.exact == Some(value) {
            self.unsat = true;
            return;
        }
        if value == 0 {
            facts.mark_nonzero();
            if facts.is_unsat() {
                self.unsat = true;
            }
        }
    }

    fn record_min(&mut self, atom: DependencyAtom, value: u64) {
        let facts = self.values.entry(atom).or_default();
        facts.tighten_interval(value, u64::MAX);
        if facts.is_unsat() {
            self.unsat = true;
        }
    }

    fn record_max(&mut self, atom: DependencyAtom, value: u64) {
        let facts = self.values.entry(atom).or_default();
        facts.tighten_interval(0, value);
        if facts.is_unsat() {
            self.unsat = true;
        }
    }
}

impl<'ctx> SymSolver<'ctx> {
    fn configured_solver(timeout_ms: u32) -> Solver {
        let solver = Solver::new();
        if timeout_ms != 0 {
            let mut params = Params::new();
            params.set_u32("timeout", timeout_ms);
            solver.set_params(&params);
        }
        solver
    }

    /// Create a new solver.
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            solver: Self::configured_solver(0),
            state_solver: Self::configured_solver(0),
            selection_solver: Self::configured_solver(0),
            scratch_solver: Self::configured_solver(0),
            timeout_ms: 0,
            sat_cache: RefCell::new(HashMap::new()),
            analysis_cache: RefCell::new(ConstraintAnalysisCache::default()),
            state_session: RefCell::new(SolverCursorSession::default()),
            selection_session: RefCell::new(SelectionSolverSession::default()),
            stats: RefCell::new(SolverStats::default()),
        }
    }

    /// Create a solver with a timeout.
    pub fn with_timeout(ctx: &'ctx Context, timeout: Duration) -> Self {
        let timeout_ms = timeout.as_millis() as u32;

        Self {
            ctx,
            solver: Self::configured_solver(timeout_ms),
            state_solver: Self::configured_solver(timeout_ms),
            selection_solver: Self::configured_solver(timeout_ms),
            scratch_solver: Self::configured_solver(timeout_ms),
            timeout_ms,
            sat_cache: RefCell::new(HashMap::new()),
            analysis_cache: RefCell::new(ConstraintAnalysisCache::default()),
            state_session: RefCell::new(SolverCursorSession::default()),
            selection_session: RefCell::new(SelectionSolverSession::default()),
            stats: RefCell::new(SolverStats::default()),
        }
    }

    /// Get the Z3 context.
    pub fn context(&self) -> &'ctx Context {
        self.ctx
    }

    /// Add a constraint to the solver.
    pub fn assert(&self, constraint: &Bool) {
        self.clear_sat_cache();
        self.solver_assert(constraint);
    }

    /// Add multiple constraints.
    pub fn assert_all(&self, constraints: &[Bool]) {
        if !constraints.is_empty() {
            self.clear_sat_cache();
        }
        self.solver_assert_all(constraints);
    }

    /// Return current solver/cache counters.
    pub fn stats(&self) -> SolverStats {
        self.stats.borrow().clone()
    }

    /// Reset solver/cache counters without touching constraints.
    pub fn clear_stats(&self) {
        *self.stats.borrow_mut() = SolverStats::default();
    }

    /// Drop memoized satisfiability results.
    pub fn clear_sat_cache(&self) {
        self.sat_cache.borrow_mut().clear();
    }

    fn reset_state_solver(&self) {
        self.state_solver.reset();
        if self.timeout_ms != 0 {
            let mut params = Params::new();
            params.set_u32("timeout", self.timeout_ms);
            self.state_solver.set_params(&params);
        }
        *self.state_session.borrow_mut() = SolverCursorSession::default();
    }

    fn reset_scratch_solver(&self) {
        self.scratch_solver.reset();
        if self.timeout_ms != 0 {
            let mut params = Params::new();
            params.set_u32("timeout", self.timeout_ms);
            self.scratch_solver.set_params(&params);
        }
    }

    fn reset_selection_solver(&self) {
        self.selection_solver.reset();
        if self.timeout_ms != 0 {
            let mut params = Params::new();
            params.set_u32("timeout", self.timeout_ms);
            self.selection_solver.set_params(&params);
        }
        *self.selection_session.borrow_mut() = SelectionSolverSession::default();
    }

    fn solver_assert(&self, constraint: &Bool) {
        self.solver.assert(constraint);
    }

    fn solver_assert_all(&self, constraints: &[Bool]) {
        for c in constraints {
            self.solver.assert(c);
        }
    }

    /// Check if the current constraints are satisfiable.
    pub fn check(&self) -> SatResult {
        self.solver.check().into()
    }

    /// Check with additional assumptions (without modifying the solver state).
    pub fn check_assumptions(&self, assumptions: &[Bool]) -> SatResult {
        self.solver.check_assumptions(assumptions).into()
    }

    /// Get the model if the constraints are satisfiable.
    pub fn get_model(&self) -> Option<Model> {
        self.solver.get_model()
    }

    /// Push a new scope (for backtracking).
    pub fn push(&self) {
        self.clear_sat_cache();
        self.solver.push();
    }

    /// Pop a scope.
    pub fn pop(&self, n: u32) {
        self.clear_sat_cache();
        self.solver.pop(n);
    }

    /// Reset the solver.
    pub fn reset(&self) {
        self.clear_sat_cache();
        self.solver.reset();
    }

    fn state_sat_cache_key(&self, state: &SymState<'ctx>) -> ConstraintCursorKey {
        state.constraint_cursor_key()
    }

    fn ensure_state_solver_cursor(&self, state: &SymState<'ctx>) {
        let target_suffix = match state.constraint_suffix_from_cursor(ConstraintCursorKey::ROOT) {
            Some(suffix) => suffix,
            None => {
                self.reset_state_solver();
                return;
            }
        };
        let target_keys: Vec<_> = std::iter::once(ConstraintCursorKey::ROOT)
            .chain(target_suffix.iter().map(|(key, _)| *key))
            .collect();

        let mut session = self.state_session.borrow_mut();
        let common_prefix_len = session
            .asserted_stack
            .iter()
            .zip(target_keys.iter())
            .take_while(|(a, b)| a == b)
            .count();

        if common_prefix_len == 0 {
            drop(session);
            self.reset_state_solver();
            session = self.state_session.borrow_mut();
        } else {
            let current_len = session.asserted_stack.len();
            if current_len > common_prefix_len {
                self.state_solver
                    .pop((current_len - common_prefix_len) as u32);
                session.asserted_stack.truncate(common_prefix_len);
            }
        }

        for (key, constraint) in target_suffix
            .iter()
            .skip(session.asserted_stack.len().saturating_sub(1))
        {
            self.state_solver.push();
            self.state_solver.assert(constraint);
            session.asserted_stack.push(*key);
        }
    }

    fn eval_value_in_model(&self, model: &Model, value: &SymValue<'ctx>) -> Option<u64> {
        let bv = value.to_bv(self.ctx);
        model.eval(&bv, true)?.as_u64()
    }

    fn extract_dependency_atom(expr: &Dynamic) -> Option<DependencyAtom> {
        let is_uninterpreted_leaf = expr.is_const()
            && matches!(
                expr.safe_decl().map(|decl| decl.kind()),
                Ok(DeclKind::UNINTERPRETED)
            );
        if is_uninterpreted_leaf {
            return Some(DependencyAtom(expr.clone()));
        }

        if expr.children().is_empty() && !matches!(expr.kind(), AstKind::Numeral) {
            return Some(DependencyAtom(expr.clone()));
        }

        None
    }

    fn extract_const_u64(expr: &Dynamic) -> Option<u64> {
        expr.as_bv()?.as_u64()
    }

    fn extract_leaf_const_pair(left: &Dynamic, right: &Dynamic) -> Option<(DependencyAtom, u64)> {
        if let (Some(atom), Some(value)) = (
            Self::extract_dependency_atom(left),
            Self::extract_const_u64(right),
        ) {
            return Some((atom, value));
        }
        if let (Some(value), Some(atom)) = (
            Self::extract_const_u64(left),
            Self::extract_dependency_atom(right),
        ) {
            return Some((atom, value));
        }
        None
    }

    fn apply_abstract_constraint(facts: &mut AbstractFacts, expr: &Dynamic, positive: bool) {
        if facts.unsat {
            return;
        }

        if let Some(bool_ast) = expr.as_bool()
            && let Some(value) = bool_ast.as_bool()
        {
            if value != positive {
                facts.unsat = true;
            }
            return;
        }

        let decl = match expr.safe_decl() {
            Ok(decl) => decl,
            Err(_) => return,
        };
        let children = expr.children();

        match (decl.kind(), positive) {
            (DeclKind::AND, true) => {
                for child in &children {
                    Self::apply_abstract_constraint(facts, child, true);
                    if facts.unsat {
                        return;
                    }
                }
            }
            (DeclKind::NOT, _) => {
                if let Some(child) = children.first() {
                    Self::apply_abstract_constraint(facts, child, !positive);
                }
            }
            (DeclKind::EQ, true) if children.len() == 2 => {
                if let Some((atom, value)) =
                    Self::extract_leaf_const_pair(&children[0], &children[1])
                {
                    facts.record_eq(atom, value);
                }
            }
            (DeclKind::EQ, false) if children.len() == 2 => {
                if let Some((atom, value)) =
                    Self::extract_leaf_const_pair(&children[0], &children[1])
                {
                    facts.record_ne(atom, value);
                }
            }
            (DeclKind::ULEQ, true) if children.len() == 2 => {
                if let Some((atom, value)) =
                    Self::extract_leaf_const_pair(&children[0], &children[1])
                {
                    if Self::extract_dependency_atom(&children[0]).is_some() {
                        facts.record_max(atom, value);
                    } else {
                        facts.record_min(atom, value);
                    }
                }
            }
            (DeclKind::UGEQ, true) if children.len() == 2 => {
                if let Some((atom, value)) =
                    Self::extract_leaf_const_pair(&children[0], &children[1])
                {
                    if Self::extract_dependency_atom(&children[0]).is_some() {
                        facts.record_min(atom, value);
                    } else {
                        facts.record_max(atom, value);
                    }
                }
            }
            (DeclKind::ULT, true) if children.len() == 2 => {
                if let Some((atom, value)) =
                    Self::extract_leaf_const_pair(&children[0], &children[1])
                {
                    if Self::extract_dependency_atom(&children[0]).is_some() {
                        if value == 0 {
                            facts.unsat = true;
                        } else {
                            facts.record_max(atom, value - 1);
                        }
                    } else {
                        facts.record_min(atom, value.saturating_add(1));
                    }
                }
            }
            (DeclKind::UGT, true) if children.len() == 2 => {
                if let Some((atom, value)) =
                    Self::extract_leaf_const_pair(&children[0], &children[1])
                {
                    if Self::extract_dependency_atom(&children[0]).is_some() {
                        facts.record_min(atom, value.saturating_add(1));
                    } else if value == 0 {
                        facts.unsat = true;
                    } else {
                        facts.record_max(atom, value - 1);
                    }
                }
            }
            _ => {}
        }
    }

    fn abstract_facts_for_constraints(constraints: &[Bool]) -> AbstractFacts {
        let mut facts = AbstractFacts::default();
        for constraint in constraints {
            Self::apply_abstract_constraint(&mut facts, &Dynamic::from_ast(constraint), true);
            if facts.unsat {
                break;
            }
        }
        facts
    }

    fn abstract_summary_for_value(
        &self,
        facts: &AbstractFacts,
        value: &SymValue<'ctx>,
    ) -> Option<AbstractValueFacts> {
        match value {
            SymValue::Concrete { value, .. } => Some(AbstractValueFacts {
                exact: Some(*value),
                interval: Some(UnsignedInterval {
                    min: *value,
                    max: *value,
                }),
                nonzero: *value != 0,
            }),
            SymValue::Symbolic { ast, .. } => {
                let atom = Self::extract_dependency_atom(&Dynamic::from_ast(ast))?;
                facts.values.get(&atom).cloned()
            }
            SymValue::Unknown { .. } => None,
        }
    }

    fn collect_dynamic_dependencies(
        expr: &Dynamic,
        out: &mut HashSet<DependencyAtom>,
        seen: &mut HashSet<Dynamic>,
    ) {
        if !seen.insert(expr.clone()) {
            return;
        }

        if let Some(bool_ast) = expr.as_bool()
            && bool_ast.as_bool().is_some()
        {
            return;
        }

        if let Some(atom) = Self::extract_dependency_atom(expr) {
            out.insert(atom);
            return;
        }

        let children = expr.children();
        if children.is_empty() {
            if !matches!(expr.kind(), AstKind::Numeral) {
                out.insert(DependencyAtom(expr.clone()));
            }
            return;
        }

        for child in children {
            Self::collect_dynamic_dependencies(&child, out, seen);
        }
    }

    fn expr_dependencies_bool(&self, expr: &Bool) -> HashSet<DependencyAtom> {
        let mut deps = HashSet::new();
        let mut seen = HashSet::new();
        Self::collect_dynamic_dependencies(&Dynamic::from_ast(expr), &mut deps, &mut seen);
        deps
    }

    fn expr_dependencies_bv(&self, expr: &BV) -> HashSet<DependencyAtom> {
        let mut deps = HashSet::new();
        let mut seen = HashSet::new();
        Self::collect_dynamic_dependencies(&Dynamic::from_ast(expr), &mut deps, &mut seen);
        deps
    }

    fn state_constraint_pairs(&self, state: &SymState<'ctx>) -> Vec<(ConstraintCursorKey, Bool)> {
        state
            .constraint_suffix_from_cursor(ConstraintCursorKey::ROOT)
            .unwrap_or_default()
    }

    fn constraint_facts_for_key(
        &self,
        key: ConstraintCursorKey,
        parent: ConstraintCursorKey,
        constraint: &Bool,
    ) -> CursorConstraintFacts {
        if let Some(cached) = self.analysis_cache.borrow().cursor_facts.get(&key) {
            return cached.clone();
        }

        let deps = self.expr_dependencies_bool(constraint);
        let abstract_delta = Self::abstract_facts_for_constraints(std::slice::from_ref(constraint));
        let facts = CursorConstraintFacts {
            parent,
            is_ground: deps.is_empty(),
            deps,
            abstract_delta,
        };
        self.analysis_cache
            .borrow_mut()
            .cursor_facts
            .insert(key, facts.clone());
        facts
    }

    fn ensure_cursor_facts(
        &self,
        state: &SymState<'ctx>,
    ) -> Vec<(
        ConstraintCursorKey,
        ConstraintCursorKey,
        CursorConstraintFacts,
    )> {
        let pairs = self.state_constraint_pairs(state);
        let mut out = Vec::with_capacity(pairs.len());
        let mut parent = ConstraintCursorKey::ROOT;
        for (key, constraint) in pairs {
            let facts = self.constraint_facts_for_key(key, parent, &constraint);
            parent = key;
            out.push((key, facts.parent, facts));
        }
        out
    }

    fn extend_state_constraint_analysis(
        &self,
        base: &StateConstraintAnalysis,
        constraint: &Bool,
        facts: &CursorConstraintFacts,
    ) -> StateConstraintAnalysis {
        let mut next = base.clone();
        if facts.is_ground {
            next.ground_constraints.push(constraint.clone());
            next.ground_abstract_facts.merge(&facts.abstract_delta);
            return next;
        }

        let mut merged_partition = ConstraintPartition {
            id: 0,
            constraints: vec![constraint.clone()],
            atoms: facts.deps.clone(),
            abstract_facts: facts.abstract_delta.clone(),
        };
        let mut first_match = None;
        let mut rebuilt = Vec::with_capacity(next.partitions.len() + 1);
        for partition in next.partitions {
            if partition.atoms.is_disjoint(&facts.deps) {
                rebuilt.push(partition);
                continue;
            }
            if first_match.is_none() {
                first_match = Some(rebuilt.len());
            }
            merged_partition.constraints.extend(partition.constraints);
            merged_partition.atoms.extend(partition.atoms);
            merged_partition
                .abstract_facts
                .merge(&partition.abstract_facts);
        }

        let insert_at = first_match.unwrap_or(rebuilt.len());
        rebuilt.insert(insert_at, merged_partition);
        for (id, partition) in rebuilt.iter_mut().enumerate() {
            partition.id = id;
        }
        next.partitions = rebuilt;
        next
    }

    fn state_constraint_pairs_with_facts(
        &self,
        state: &SymState<'ctx>,
    ) -> Vec<(
        ConstraintCursorKey,
        ConstraintCursorKey,
        Bool,
        CursorConstraintFacts,
    )> {
        self.state_constraint_pairs(state)
            .into_iter()
            .zip(self.ensure_cursor_facts(state))
            .map(|((key, constraint), (fact_key, parent, facts))| {
                debug_assert_eq!(key, fact_key);
                (key, parent, constraint, facts)
            })
            .collect()
    }

    fn distinct_dependency_atom_count(&self, state: &SymState<'ctx>) -> usize {
        let mut atoms = HashSet::new();
        for (_, _, facts) in self.ensure_cursor_facts(state) {
            atoms.extend(facts.deps);
        }
        atoms.len()
    }

    fn state_constraint_analysis(&self, state: &SymState<'ctx>) -> Rc<StateConstraintAnalysis> {
        let cache_key = state.constraint_cursor_key();
        if let Some(cached) = self.analysis_cache.borrow().state_cache.get(&cache_key) {
            return cached.clone();
        }

        let pairs = self.state_constraint_pairs_with_facts(state);
        if pairs.is_empty() {
            let empty = Rc::new(StateConstraintAnalysis::default());
            self.analysis_cache
                .borrow_mut()
                .state_cache
                .insert(cache_key, empty.clone());
            return empty;
        }

        let mut cached_prefix = StateConstraintAnalysis::default();
        let mut start_index = 0usize;
        for (index, (key, _, _, _)) in pairs.iter().enumerate().rev() {
            if let Some(existing) = self.analysis_cache.borrow().state_cache.get(key).cloned() {
                cached_prefix = (*existing).clone();
                start_index = index + 1;
                break;
            }
        }

        let mut current = cached_prefix;
        for (key, _, constraint, facts) in pairs.iter().skip(start_index) {
            current = self.extend_state_constraint_analysis(&current, constraint, facts);
            let cached = Rc::new(current.clone());
            self.analysis_cache
                .borrow_mut()
                .state_cache
                .insert(*key, cached);
        }

        self.analysis_cache
            .borrow()
            .state_cache
            .get(&cache_key)
            .cloned()
            .unwrap_or_else(|| Rc::new(current))
    }

    fn cached_state_constraint_analysis(
        &self,
        state: &SymState<'ctx>,
    ) -> Option<Rc<StateConstraintAnalysis>> {
        self.analysis_cache
            .borrow()
            .state_cache
            .get(&state.constraint_cursor_key())
            .cloned()
    }

    fn should_build_partition_analysis(&self, state: &SymState<'ctx>, kind: DeepQueryKind) -> bool {
        if matches!(kind, DeepQueryKind::Model) {
            return true;
        }

        let constraint_count = state.constraints().len();
        if constraint_count >= 6 {
            return true;
        }
        if constraint_count < 4 {
            return false;
        }

        self.distinct_dependency_atom_count(state) >= 2
    }

    fn analysis_for_mode(
        &self,
        state: &SymState<'ctx>,
        mode: SolverMode,
        kind: DeepQueryKind,
    ) -> Option<Rc<StateConstraintAnalysis>> {
        match mode {
            SolverMode::ExploreFast => self.cached_state_constraint_analysis(state),
            SolverMode::QueryDeep if self.should_build_partition_analysis(state, kind) => {
                Some(self.state_constraint_analysis(state))
            }
            SolverMode::QueryDeep => None,
        }
    }

    fn selection_for_query_with_analysis(
        &self,
        state: &SymState<'ctx>,
        analysis: &StateConstraintAnalysis,
        seed_deps: &HashSet<DependencyAtom>,
    ) -> ConstraintSelection {
        let mut selected = analysis.ground_constraints.clone();
        let mut abstract_facts = analysis.ground_abstract_facts.clone();
        let mut partition_ids = Vec::new();
        if seed_deps.is_empty() {
            let is_full_state = selected.len() == state.constraints().len();
            return ConstraintSelection {
                key: ConstraintSelectionKey {
                    state_key: state.constraint_cursor_key(),
                    full_state: false,
                    partition_ids,
                },
                constraints: selected,
                abstract_facts,
                is_full_state,
            };
        }

        for partition in &analysis.partitions {
            if !partition.atoms.is_disjoint(seed_deps) {
                selected.extend(partition.constraints.iter().cloned());
                abstract_facts.merge(&partition.abstract_facts);
                partition_ids.push(partition.id);
            }
        }

        ConstraintSelection {
            key: ConstraintSelectionKey {
                state_key: state.constraint_cursor_key(),
                full_state: false,
                partition_ids,
            },
            constraints: selected,
            abstract_facts,
            is_full_state: false,
        }
    }

    fn full_selection_from_analysis(
        &self,
        state: &SymState<'ctx>,
        analysis: &StateConstraintAnalysis,
    ) -> ConstraintSelection {
        let mut abstract_facts = analysis.ground_abstract_facts.clone();
        for partition in &analysis.partitions {
            abstract_facts.merge(&partition.abstract_facts);
        }
        ConstraintSelection {
            key: ConstraintSelectionKey {
                state_key: state.constraint_cursor_key(),
                full_state: true,
                partition_ids: Vec::new(),
            },
            constraints: state.constraints().to_vec(),
            abstract_facts,
            is_full_state: true,
        }
    }

    fn full_selection_without_analysis(&self, state: &SymState<'ctx>) -> ConstraintSelection {
        ConstraintSelection {
            key: ConstraintSelectionKey {
                state_key: state.constraint_cursor_key(),
                full_state: true,
                partition_ids: Vec::new(),
            },
            constraints: state.constraints().to_vec(),
            abstract_facts: Self::abstract_facts_for_constraints(state.constraints()),
            is_full_state: true,
        }
    }

    fn selection_is_effectively_full_state(
        &self,
        analysis: &StateConstraintAnalysis,
        selection: &ConstraintSelection,
        total_constraints: usize,
    ) -> bool {
        if selection.is_full_state {
            return true;
        }
        if analysis.partitions.len() <= 1 {
            return true;
        }
        if selection.key.partition_ids.len() == analysis.partitions.len() {
            return true;
        }
        selection.constraints.len().saturating_mul(4) >= total_constraints.saturating_mul(3)
            || (total_constraints > 6
                && selection.constraints.len().saturating_add(2) >= total_constraints)
    }

    fn preferred_selection_for_query(
        &self,
        state: &SymState<'ctx>,
        seed_deps: &HashSet<DependencyAtom>,
        kind: DeepQueryKind,
    ) -> ConstraintSelection {
        let Some(analysis) = self.analysis_for_mode(state, SolverMode::QueryDeep, kind) else {
            return self.full_selection_without_analysis(state);
        };

        let selection = self.selection_for_query_with_analysis(state, &analysis, seed_deps);
        if self.selection_is_effectively_full_state(
            &analysis,
            &selection,
            state.constraints().len(),
        ) {
            self.full_selection_from_analysis(state, &analysis)
        } else {
            selection
        }
    }

    fn ensure_selection_solver(&self, selection: &ConstraintSelection) {
        if self.selection_session.borrow().asserted_key.as_ref() == Some(&selection.key) {
            return;
        }
        self.reset_selection_solver();
        for constraint in &selection.constraints {
            self.selection_solver.assert(constraint);
        }
        self.selection_session.borrow_mut().asserted_key = Some(selection.key.clone());
    }

    fn selection_sat_with_constraint(
        &self,
        selection: &ConstraintSelection,
        constraint: &Bool,
    ) -> SatResult {
        self.ensure_selection_solver(selection);
        self.selection_solver.push();
        self.selection_solver.assert(constraint);
        let result = self.selection_solver.check().into();
        self.selection_solver.pop(1);
        result
    }

    fn selection_find_value(
        &self,
        selection: &ConstraintSelection,
        target: &SymValue<'ctx>,
        constraint: &Bool,
    ) -> Option<u64> {
        self.ensure_selection_solver(selection);
        self.selection_solver.push();
        self.selection_solver.assert(constraint);
        let sat = self.selection_solver.check();
        let out = if sat == z3::SatResult::Sat {
            let model = self.selection_solver.get_model()?;
            self.eval_value_in_model(&model, target)
        } else {
            None
        };
        self.selection_solver.pop(1);
        out
    }

    fn selection_contradicts_constraint(
        &self,
        selection: &ConstraintSelection,
        constraint: &Bool,
    ) -> bool {
        if selection.abstract_facts.unsat {
            return true;
        }
        let mut facts = selection.abstract_facts.clone();
        Self::apply_abstract_constraint(&mut facts, &Dynamic::from_ast(constraint), true);
        facts.unsat
    }

    fn partitioned_state_result(
        &self,
        state: &SymState<'ctx>,
        mode: SolverMode,
        kind: DeepQueryKind,
    ) -> Option<SatResult> {
        let cache_key = state.constraint_cursor_key();
        let analysis = self.analysis_for_mode(state, mode, kind)?;
        if analysis.partitions.len() <= 1 {
            return None;
        }

        if analysis.ground_abstract_facts.unsat {
            return Some(SatResult::Unsat);
        }

        if !analysis.ground_constraints.is_empty() {
            if let Some(cached) = self
                .analysis_cache
                .borrow()
                .ground_sat_cache
                .get(&cache_key)
                .copied()
            {
                match cached {
                    SatResult::Sat => {}
                    other => return Some(other),
                }
            } else {
                self.scratch_assert_constraints(&analysis.ground_constraints);
                let result: SatResult = self.scratch_solver.check().into();
                if matches!(result, SatResult::Sat | SatResult::Unsat) {
                    self.analysis_cache
                        .borrow_mut()
                        .ground_sat_cache
                        .insert(cache_key, result);
                }
                match result {
                    SatResult::Sat => {}
                    other => return Some(other),
                }
            }
        }

        self.scratch_assert_constraints(&analysis.ground_constraints);
        for partition in &analysis.partitions {
            if partition.abstract_facts.unsat {
                return Some(SatResult::Unsat);
            }
            let cache_key = PartitionSatCacheKey {
                state_key: state.constraint_cursor_key(),
                partition_id: partition.id,
            };
            if let Some(cached) = self
                .analysis_cache
                .borrow()
                .partition_sat_cache
                .get(&cache_key)
                .copied()
            {
                match cached {
                    SatResult::Sat => continue,
                    other => return Some(other),
                }
            }

            self.scratch_solver.push();
            for constraint in &partition.constraints {
                self.scratch_solver.assert(constraint);
            }
            let result: SatResult = self.scratch_solver.check().into();
            self.scratch_solver.pop(1);
            if matches!(result, SatResult::Sat | SatResult::Unsat) {
                self.analysis_cache
                    .borrow_mut()
                    .partition_sat_cache
                    .insert(cache_key, result);
            }
            match result {
                SatResult::Sat => {}
                other => return Some(other),
            }
        }
        Some(SatResult::Sat)
    }

    fn scratch_assert_constraints(&self, constraints: &[Bool]) {
        self.reset_scratch_solver();
        for constraint in constraints {
            self.scratch_solver.assert(constraint);
        }
    }

    fn cached_state_sat_result(
        &self,
        cache_key: ConstraintCursorKey,
        mode: SolverMode,
    ) -> Option<SatResult> {
        match self.sat_cache.borrow().get(&cache_key).copied() {
            Some(SatResult::Unknown) if matches!(mode, SolverMode::QueryDeep) => None,
            other => other,
        }
    }

    fn remember_state_sat_result(&self, cache_key: ConstraintCursorKey, result: SatResult) {
        if matches!(result, SatResult::Sat | SatResult::Unsat) {
            self.sat_cache.borrow_mut().insert(cache_key, result);
        }
    }

    fn compute_state_sat_result(
        &self,
        state: &SymState<'ctx>,
        mode: SolverMode,
        kind: DeepQueryKind,
    ) -> SatResult {
        let partitioned = match mode {
            SolverMode::ExploreFast => {
                self.partitioned_state_result(state, mode, DeepQueryKind::Predicate)
            }
            SolverMode::QueryDeep if self.should_build_partition_analysis(state, kind) => {
                self.partitioned_state_result(state, mode, kind)
            }
            SolverMode::QueryDeep => None,
        };
        match partitioned {
            Some(SatResult::Unknown) => {
                self.ensure_state_solver_cursor(state);
                self.state_solver.check().into()
            }
            Some(other) => other,
            None => {
                self.ensure_state_solver_cursor(state);
                self.state_solver.check().into()
            }
        }
    }

    fn state_sat_result(
        &self,
        state: &SymState<'ctx>,
        mode: SolverMode,
        kind: DeepQueryKind,
    ) -> SatResult {
        let cache_key = self.state_sat_cache_key(state);
        if let Some(result) = self.cached_state_sat_result(cache_key, mode) {
            return result;
        }

        let result = self.compute_state_sat_result(state, mode, kind);
        self.remember_state_sat_result(cache_key, result);
        result
    }

    /// Check if a state's path constraints are satisfiable.
    pub fn is_sat(&self, state: &SymState<'ctx>) -> bool {
        self.stats.borrow_mut().sat_queries += 1;

        let cache_key = self.state_sat_cache_key(state);
        if let Some(result) = self.cached_state_sat_result(cache_key, SolverMode::ExploreFast) {
            self.stats.borrow_mut().sat_cache_hits += 1;
            return result == SatResult::Sat;
        }

        self.stats.borrow_mut().sat_cache_misses += 1;
        let result =
            self.compute_state_sat_result(state, SolverMode::ExploreFast, DeepQueryKind::Predicate);
        self.remember_state_sat_result(cache_key, result);
        // Exploration pruning must be conservative. `Unknown` usually means the
        // fast partitioned solver hit a complex bit-vector predicate; treating
        // that as UNSAT drops real paths before the deeper query/model phase can
        // classify them honestly.
        result != SatResult::Unsat
    }

    /// Check whether a state's constraints remain satisfiable with one extra constraint.
    pub fn sat_with_constraint(&self, state: &SymState<'ctx>, constraint: &Bool) -> SatResult {
        if self.state_sat_result(state, SolverMode::QueryDeep, DeepQueryKind::Predicate)
            != SatResult::Sat
        {
            return SatResult::Unsat;
        }
        let seed_deps = self.expr_dependencies_bool(constraint);
        let selected =
            self.preferred_selection_for_query(state, &seed_deps, DeepQueryKind::Predicate);
        if self.selection_contradicts_constraint(&selected, constraint) {
            return SatResult::Unsat;
        }
        match self.selection_sat_with_constraint(&selected, constraint) {
            SatResult::Unknown if !selected.is_full_state => {
                let full = self.full_selection_without_analysis(state);
                if self.selection_contradicts_constraint(&full, constraint) {
                    SatResult::Unsat
                } else {
                    self.selection_sat_with_constraint(&full, constraint)
                }
            }
            other => other,
        }
    }

    /// Get a concrete model for a state's constraints.
    pub fn solve(&self, state: &SymState<'ctx>) -> Option<SymModel<'_>> {
        self.stats.borrow_mut().solve_calls += 1;

        let cache_key = self.state_sat_cache_key(state);
        if matches!(
            self.cached_state_sat_result(cache_key, SolverMode::QueryDeep),
            Some(SatResult::Unsat)
        ) {
            self.stats.borrow_mut().solve_unsat_shortcuts += 1;
            return None;
        }

        if matches!(
            self.partitioned_state_result(state, SolverMode::QueryDeep, DeepQueryKind::Model),
            Some(SatResult::Unsat)
        ) {
            self.remember_state_sat_result(cache_key, SatResult::Unsat);
            self.stats.borrow_mut().solve_unsat_shortcuts += 1;
            return None;
        }

        self.ensure_state_solver_cursor(state);
        let sat_result: SatResult = self.state_solver.check().into();
        let result = if sat_result == SatResult::Sat {
            self.state_solver
                .get_model()
                .map(|m| SymModel::new(self.ctx, m))
        } else {
            None
        };

        self.remember_state_sat_result(cache_key, sat_result);
        result
    }

    /// Check whether one state's path condition implies another's.
    pub fn implies(
        &self,
        antecedent: &SymState<'ctx>,
        consequent: &SymState<'ctx>,
    ) -> Option<bool> {
        if antecedent.constraints_imply_by_prefix(consequent) {
            return Some(true);
        }
        if self.state_sat_result(antecedent, SolverMode::QueryDeep, DeepQueryKind::Predicate)
            != SatResult::Sat
        {
            return Some(true);
        }
        let consequent_not = consequent.path_condition().not();
        let seed_deps = self.expr_dependencies_bool(&consequent_not);
        let selected =
            self.preferred_selection_for_query(antecedent, &seed_deps, DeepQueryKind::Predicate);
        if self.selection_contradicts_constraint(&selected, &consequent_not) {
            return Some(true);
        }
        match match self.selection_sat_with_constraint(&selected, &consequent_not) {
            SatResult::Unknown if !selected.is_full_state => {
                let full = self.full_selection_without_analysis(antecedent);
                if self.selection_contradicts_constraint(&full, &consequent_not) {
                    SatResult::Unsat
                } else {
                    self.selection_sat_with_constraint(&full, &consequent_not)
                }
            }
            other => other,
        } {
            SatResult::Unsat => Some(true),
            SatResult::Sat => Some(false),
            SatResult::Unknown => None,
        }
    }

    /// Evaluate a symbolic value under the current model.
    pub fn eval(&self, value: &SymValue<'ctx>) -> Option<u64> {
        let model = self.get_model()?;
        let bv = value.to_bv(self.ctx);
        let result = model.eval(&bv, true)?;
        result.as_u64()
    }

    /// Find a value that satisfies additional constraints.
    pub fn find_value(
        &self,
        state: &SymState<'ctx>,
        target: &SymValue<'ctx>,
        constraint: &Bool,
    ) -> Option<u64> {
        if self.state_sat_result(state, SolverMode::QueryDeep, DeepQueryKind::Model)
            != SatResult::Sat
        {
            return None;
        }
        let mut seed_deps = self.expr_dependencies_bool(constraint);
        seed_deps.extend(self.expr_dependencies_bv(&target.to_bv(self.ctx)));
        let selected = self.preferred_selection_for_query(state, &seed_deps, DeepQueryKind::Model);
        if self.selection_contradicts_constraint(&selected, constraint) {
            return None;
        }
        let selection_result = self.selection_find_value(&selected, target, constraint);
        if selection_result.is_some() || selected.is_full_state {
            return selection_result;
        }
        let full = self.full_selection_without_analysis(state);
        if self.selection_contradicts_constraint(&full, constraint) {
            return None;
        }
        self.selection_find_value(&full, target, constraint)
    }

    /// Check if two symbolic values can be equal.
    pub fn can_be_equal(
        &self,
        state: &SymState<'ctx>,
        a: &SymValue<'ctx>,
        b: &SymValue<'ctx>,
    ) -> bool {
        // Normalize bit widths before comparison
        let (a_bv, b_bv) = if a.bits() == b.bits() {
            (a.to_bv(self.ctx), b.to_bv(self.ctx))
        } else if a.bits() > b.bits() {
            (
                a.to_bv(self.ctx),
                b.to_bv(self.ctx).zero_ext(a.bits() - b.bits()),
            )
        } else {
            (
                a.to_bv(self.ctx).zero_ext(b.bits() - a.bits()),
                b.to_bv(self.ctx),
            )
        };
        let mut deps = self.expr_dependencies_bv(&a_bv);
        deps.extend(self.expr_dependencies_bv(&b_bv));
        let selection = self.preferred_selection_for_query(state, &deps, DeepQueryKind::Predicate);
        if let (Some(left), Some(right)) = (
            self.abstract_summary_for_value(&selection.abstract_facts, a),
            self.abstract_summary_for_value(&selection.abstract_facts, b),
        ) {
            if let (Some(left_exact), Some(right_exact)) = (left.exact, right.exact) {
                return left_exact == right_exact;
            }
            if let (Some(left_interval), Some(right_interval)) = (left.interval, right.interval)
                && (left_interval.max < right_interval.min
                    || right_interval.max < left_interval.min)
            {
                return false;
            }
        }
        let eq = a_bv.eq(&b_bv);
        matches!(self.sat_with_constraint(state, &eq), SatResult::Sat)
    }

    /// Check if a value can be zero.
    pub fn can_be_zero(&self, state: &SymState<'ctx>, value: &SymValue<'ctx>) -> bool {
        let seed_deps = self.expr_dependencies_bv(&value.to_bv(self.ctx));
        let selection =
            self.preferred_selection_for_query(state, &seed_deps, DeepQueryKind::Predicate);
        if let Some(summary) = self.abstract_summary_for_value(&selection.abstract_facts, value) {
            if summary.exact == Some(0) {
                return true;
            }
            if summary.nonzero {
                return false;
            }
            if let Some(interval) = summary.interval
                && interval.min > 0
            {
                return false;
            }
        }
        let bv = value.to_bv(self.ctx);
        let zero = BV::from_i64(0, value.bits());
        let eq = bv.eq(&zero);
        matches!(self.sat_with_constraint(state, &eq), SatResult::Sat)
    }

    /// Check if a value must be zero (cannot be non-zero).
    pub fn must_be_zero(&self, state: &SymState<'ctx>, value: &SymValue<'ctx>) -> bool {
        let seed_deps = self.expr_dependencies_bv(&value.to_bv(self.ctx));
        let selection =
            self.preferred_selection_for_query(state, &seed_deps, DeepQueryKind::Predicate);
        if let Some(summary) = self.abstract_summary_for_value(&selection.abstract_facts, value) {
            if summary.exact == Some(0) {
                return true;
            }
            if summary.nonzero {
                return false;
            }
            if let Some(interval) = summary.interval
                && interval.min > 0
            {
                return false;
            }
        }
        let bv = value.to_bv(self.ctx);
        let zero = BV::from_i64(0, value.bits());
        let neq = bv.eq(&zero).not();
        matches!(self.sat_with_constraint(state, &neq), SatResult::Unsat)
    }

    /// Get the minimum value for a symbolic expression.
    pub fn minimize(&self, state: &SymState<'ctx>, value: &SymValue<'ctx>) -> Option<u64> {
        if self.state_sat_result(state, SolverMode::QueryDeep, DeepQueryKind::Model)
            != SatResult::Sat
        {
            return None;
        }
        let bv = value.to_bv(self.ctx);
        let seed_deps = self.expr_dependencies_bv(&bv);
        let mut selection =
            self.preferred_selection_for_query(state, &seed_deps, DeepQueryKind::Model);
        if selection.abstract_facts.unsat {
            return None;
        }
        let bits = value.bits();

        if let Some(summary) = self.abstract_summary_for_value(&selection.abstract_facts, value)
            && let Some(exact) = summary.exact
        {
            return Some(exact);
        }

        let max_value = if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };
        let mut lo: u64 = self
            .abstract_summary_for_value(&selection.abstract_facts, value)
            .and_then(|summary| summary.interval.map(|interval| interval.min))
            .unwrap_or(0);
        let mut hi: u64 = self
            .abstract_summary_for_value(&selection.abstract_facts, value)
            .and_then(|summary| summary.interval.map(|interval| interval.max))
            .unwrap_or(max_value);
        let mut result = None;

        while lo <= hi {
            let mid = lo + (hi - lo) / 2;
            let mid_bv = BV::from_u64(mid, bits);
            let constraint = bv.bvule(&mid_bv);

            let mut sat = self.selection_sat_with_constraint(&selection, &constraint);
            if sat == SatResult::Unknown && !selection.is_full_state {
                selection = self.full_selection_without_analysis(state);
                sat = self.selection_sat_with_constraint(&selection, &constraint);
            }

            if sat == SatResult::Sat {
                result = self.selection_find_value(&selection, value, &constraint);
                hi = mid.saturating_sub(1);
            } else {
                lo = mid.saturating_add(1);
            }

            if lo == 0 && hi == u64::MAX {
                break; // Prevent infinite loop
            }
        }

        result
    }

    /// Get the maximum value for a symbolic expression.
    pub fn maximize(&self, state: &SymState<'ctx>, value: &SymValue<'ctx>) -> Option<u64> {
        if self.state_sat_result(state, SolverMode::QueryDeep, DeepQueryKind::Model)
            != SatResult::Sat
        {
            return None;
        }
        let bv = value.to_bv(self.ctx);
        let seed_deps = self.expr_dependencies_bv(&bv);
        let mut selection =
            self.preferred_selection_for_query(state, &seed_deps, DeepQueryKind::Model);
        if selection.abstract_facts.unsat {
            return None;
        }
        let bits = value.bits();

        if let Some(summary) = self.abstract_summary_for_value(&selection.abstract_facts, value)
            && let Some(exact) = summary.exact
        {
            return Some(exact);
        }

        let max_value = if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };
        let mut lo: u64 = self
            .abstract_summary_for_value(&selection.abstract_facts, value)
            .and_then(|summary| summary.interval.map(|interval| interval.min))
            .unwrap_or(0);
        let mut hi: u64 = self
            .abstract_summary_for_value(&selection.abstract_facts, value)
            .and_then(|summary| summary.interval.map(|interval| interval.max))
            .unwrap_or(max_value);
        let mut result = None;

        while lo <= hi {
            let mid = lo + (hi - lo) / 2;
            let mid_bv = BV::from_u64(mid, bits);
            let constraint = bv.bvuge(&mid_bv);

            let mut sat = self.selection_sat_with_constraint(&selection, &constraint);
            if sat == SatResult::Unknown && !selection.is_full_state {
                selection = self.full_selection_without_analysis(state);
                sat = self.selection_sat_with_constraint(&selection, &constraint);
            }

            if sat == SatResult::Sat {
                result = self.selection_find_value(&selection, value, &constraint);
                lo = mid.saturating_add(1);
            } else {
                hi = mid.saturating_sub(1);
            }

            if lo == 0 && hi == u64::MAX {
                break;
            }
        }

        result
    }
}

/// A model (concrete assignment) from the solver.
pub struct SymModel<'ctx> {
    ctx: &'ctx Context,
    model: Model,
}

impl<'ctx> SymModel<'ctx> {
    /// Create a new model wrapper.
    pub fn new(ctx: &'ctx Context, model: Model) -> Self {
        Self { ctx, model }
    }

    /// Evaluate a bitvector in this model.
    pub fn eval_bv(&self, bv: &BV) -> Option<u64> {
        self.model.eval(bv, true)?.as_u64()
    }

    /// Evaluate a symbolic value in this model.
    pub fn eval(&self, value: &SymValue<'ctx>) -> Option<u64> {
        let bv = value.to_bv(self.ctx);
        self.eval_bv(&bv)
    }

    /// Evaluate a symbolic value as a little-endian byte array.
    pub fn eval_bytes(&self, value: &SymValue<'ctx>, size: usize) -> Option<Vec<u8>> {
        if size == 0 {
            return Some(Vec::new());
        }

        let max_bytes = (value.bits() / 8) as usize;
        if max_bytes == 0 {
            return None;
        }
        let size = std::cmp::min(size, max_bytes);

        let bv = value.to_bv(self.ctx);
        let mut bytes = Vec::with_capacity(size);
        for i in 0..size {
            let low = (i as u32) * 8;
            let high = low + 7;
            let byte_bv = bv.extract(high, low);
            let byte = self.model.eval(&byte_bv, true)?.as_u64()? as u8;
            bytes.push(byte);
        }
        Some(bytes)
    }

    /// Evaluate a symbolic value as a UTF-8 string (stops at NUL or max bytes).
    pub fn eval_string(&self, value: &SymValue<'ctx>, max_len: usize) -> Option<String> {
        let bytes = self.eval_bytes(value, max_len)?;
        let mut trimmed = bytes;
        if let Some(pos) = trimmed.iter().position(|b| *b == 0) {
            trimmed.truncate(pos);
        }
        String::from_utf8(trimmed).ok()
    }

    /// Get all concrete values from the model.
    ///
    /// Note: This is a simplified implementation that returns an empty map.
    /// Full model enumeration requires iterating over model constants,
    /// which varies by z3 version.
    pub fn get_values(&self) -> HashMap<String, u64> {
        // In z3 0.12, the API for iterating over model constants is different.
        // For now, return an empty map. Users should call eval() directly
        // with the specific values they want to extract.
        HashMap::new()
    }
}

impl<'ctx> std::fmt::Debug for SymModel<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let values = self.get_values();
        f.debug_struct("SymModel").field("values", &values).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_sat() {
        let ctx = Context::thread_local();
        let solver = SymSolver::new(&ctx);

        // x > 5
        let x = BV::new_const("x", 32);
        let five = BV::from_i64(5, 32);
        let constraint = x.bvugt(&five);

        solver.assert(&constraint);
        assert_eq!(solver.check(), SatResult::Sat);

        let model = solver.get_model().unwrap();
        let x_val = model.eval(&x, true).unwrap().as_u64().unwrap();
        assert!(x_val > 5);
    }

    #[test]
    fn test_unsat() {
        let ctx = Context::thread_local();
        let solver = SymSolver::new(&ctx);

        // x > 5 AND x < 3 (impossible)
        let x = BV::new_const("x", 32);
        let five = BV::from_i64(5, 32);
        let three = BV::from_i64(3, 32);

        solver.assert(&x.bvugt(&five));
        solver.assert(&x.bvult(&three));

        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn test_state_sat() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);

        let x = state.get_register("x");
        let five = SymValue::concrete(5, 32);
        let cond = x.ult(&ctx, &five); // x < 5
        state.add_true_constraint(&cond);

        let solver = SymSolver::new(&ctx);
        assert!(solver.is_sat(&state));
    }

    #[test]
    fn test_state_sat_cache_hit() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        let x = state.get_register("x");
        let five = SymValue::concrete(5, 32);
        let cond = x.ult(&ctx, &five);
        state.add_true_constraint(&cond);

        let solver = SymSolver::new(&ctx);
        assert!(solver.is_sat(&state));
        assert!(solver.is_sat(&state));

        let stats = solver.stats();
        assert_eq!(stats.sat_queries, 2);
        assert_eq!(stats.sat_cache_hits, 1);
        assert_eq!(stats.sat_cache_misses, 1);
    }

    #[test]
    fn test_solve() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);

        let x = state.get_register("x");
        let ten = SymValue::concrete(10, 32);
        let eq = x.eq(&ctx, &ten); // x == 10
        state.add_true_constraint(&eq);

        let solver = SymSolver::new(&ctx);
        let model = solver.solve(&state).unwrap();

        // Evaluate x directly from the model
        let x_value = model.eval(&x);
        assert_eq!(x_value, Some(10));
    }

    #[test]
    fn test_solve_uses_cached_unsat_shortcut() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);

        let x = state.get_register("x");
        let five = SymValue::concrete(5, 32);
        let three = SymValue::concrete(3, 32);
        state.add_true_constraint(&x.ult(&ctx, &three));
        state.add_true_constraint(&x.eq(&ctx, &five));

        let solver = SymSolver::new(&ctx);
        assert!(!solver.is_sat(&state));
        assert!(solver.solve(&state).is_none());

        let stats = solver.stats();
        assert_eq!(stats.solve_calls, 1);
        assert_eq!(stats.solve_unsat_shortcuts, 1);
    }

    #[test]
    fn test_sat_with_constraint_short_circuits_unsat_base_state() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);

        let x = state.get_register("x");
        let y = state.get_register("y");
        state.add_true_constraint(&x.ult(&ctx, &SymValue::concrete(3, 32)));
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(5, 32)));

        let solver = SymSolver::new(&ctx);
        let y_is_zero = y.to_bv(&ctx).eq(BV::from_u64(0, 32));
        assert_eq!(
            solver.sat_with_constraint(&state, &y_is_zero),
            SatResult::Unsat
        );
        assert_eq!(solver.find_value(&state, &y, &y_is_zero), None);
    }

    #[test]
    fn test_find_value_and_extrema_with_irrelevant_constraints() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);

        let x = state.get_register("x");
        let y = state.get_register("y");
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(10, 32)));
        state.constrain_range(&y, 3, 9);

        let solver = SymSolver::new(&ctx);
        let y_is_seven = y.to_bv(&ctx).eq(BV::from_u64(7, 32));
        assert_eq!(solver.find_value(&state, &y, &y_is_seven), Some(7));
        assert_eq!(solver.minimize(&state, &y), Some(3));
        assert_eq!(solver.maximize(&state, &y), Some(9));
    }

    #[test]
    fn test_state_solver_reuses_prefix_cursor() {
        let ctx = Context::thread_local();

        let mut base = SymState::new(&ctx, 0x1000);
        base.make_symbolic("x", 32);

        let x = base.get_register("x");
        base.add_true_constraint(&x.ult(&ctx, &SymValue::concrete(10, 32)));
        let shared_key = base.constraint_cursor_key();

        let mut left = base.fork();
        left.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(1, 32)));
        let left_key = left.constraint_cursor_key();

        let mut right = base.fork();
        right.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(2, 32)));
        let right_key = right.constraint_cursor_key();

        let solver = SymSolver::new(&ctx);
        assert!(solver.is_sat(&left));
        assert_eq!(
            solver.state_session.borrow().asserted_stack,
            vec![ConstraintCursorKey::ROOT, shared_key, left_key]
        );

        assert!(solver.is_sat(&right));
        assert_eq!(
            solver.state_session.borrow().asserted_stack,
            vec![ConstraintCursorKey::ROOT, shared_key, right_key]
        );

        assert!(solver.is_sat(&base));
        assert_eq!(
            solver.state_session.borrow().asserted_stack,
            vec![ConstraintCursorKey::ROOT, shared_key]
        );
    }

    #[test]
    fn test_state_constraint_analysis_partitions_independent_constraints() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);

        let x = state.get_register("x");
        let y = state.get_register("y");
        state.add_true_constraint(&x.ult(&ctx, &SymValue::concrete(5, 32)));
        state.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(42, 32)));

        let solver = SymSolver::new(&ctx);
        let analysis = solver.state_constraint_analysis(&state);
        assert_eq!(analysis.ground_constraints.len(), 0);
        assert_eq!(analysis.partitions.len(), 2);
    }

    #[test]
    fn test_query_selection_drops_unrelated_symbolic_constraints() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("w", 32);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);
        state.make_symbolic("z", 32);

        let w = state.get_register("w");
        let x = state.get_register("x");
        let y = state.get_register("y");
        let z = state.get_register("z");
        state.add_true_constraint(&w.eq(&ctx, &SymValue::concrete(1, 32)));
        state.add_true_constraint(&x.ult(&ctx, &SymValue::concrete(5, 32)));
        state.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(42, 32)));
        state.add_true_constraint(&z.eq(&ctx, &SymValue::concrete(9, 32)));

        let solver = SymSolver::new(&ctx);
        let seed_deps = solver.expr_dependencies_bv(&x.to_bv(&ctx));
        let selected =
            solver.preferred_selection_for_query(&state, &seed_deps, DeepQueryKind::Predicate);

        assert_eq!(selected.constraints.len(), 1);
        let x_is_three = x.to_bv(&ctx).eq(BV::from_u64(3, 32));
        assert_eq!(
            solver.sat_with_constraint(&state, &x_is_three),
            SatResult::Sat
        );
    }

    #[test]
    fn test_query_selection_keeps_ground_constraints() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        let x = state.get_register("x");
        state.add_true_constraint(&x.ult(&ctx, &SymValue::concrete(5, 32)));
        state.add_constraint(Bool::from_bool(false));

        let solver = SymSolver::new(&ctx);
        let seed_deps = solver.expr_dependencies_bv(&x.to_bv(&ctx));
        let selected =
            solver.preferred_selection_for_query(&state, &seed_deps, DeepQueryKind::Predicate);

        assert_eq!(selected.constraints.len(), 2);
        let x_is_three = x.to_bv(&ctx).eq(BV::from_u64(3, 32));
        assert_eq!(
            solver.sat_with_constraint(&state, &x_is_three),
            SatResult::Unsat
        );
    }

    #[test]
    fn test_partitioned_state_result_detects_unsat_component() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);

        let x = state.get_register("x");
        let y = state.get_register("y");
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(1, 32)));
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(2, 32)));
        state.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(9, 32)));

        let solver = SymSolver::new(&ctx);
        assert_eq!(
            solver.partitioned_state_result(&state, SolverMode::QueryDeep, DeepQueryKind::Model),
            Some(SatResult::Unsat)
        );
        assert!(!solver.is_sat(&state));
    }

    #[test]
    fn test_partition_sat_cache_reuses_checked_components() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);

        let x = state.get_register("x");
        let y = state.get_register("y");
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(1, 32)));
        state.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(9, 32)));

        let solver = SymSolver::new(&ctx);
        assert_eq!(
            solver.partitioned_state_result(&state, SolverMode::QueryDeep, DeepQueryKind::Model),
            Some(SatResult::Sat)
        );
        assert_eq!(solver.analysis_cache.borrow().partition_sat_cache.len(), 2);
        assert_eq!(
            solver.partitioned_state_result(&state, SolverMode::QueryDeep, DeepQueryKind::Model),
            Some(SatResult::Sat)
        );
        assert_eq!(solver.analysis_cache.borrow().partition_sat_cache.len(), 2);
    }

    #[test]
    fn test_explore_fast_sat_does_not_build_fresh_partition_analysis() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("w", 32);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);
        state.make_symbolic("z", 32);

        let w = state.get_register("w");
        let x = state.get_register("x");
        let y = state.get_register("y");
        let z = state.get_register("z");
        state.add_true_constraint(&w.eq(&ctx, &SymValue::concrete(1, 32)));
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(2, 32)));
        state.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(3, 32)));
        state.add_true_constraint(&z.eq(&ctx, &SymValue::concrete(4, 32)));

        let solver = SymSolver::new(&ctx);
        assert!(solver.analysis_cache.borrow().state_cache.is_empty());
        assert!(solver.is_sat(&state));
        assert!(solver.analysis_cache.borrow().state_cache.is_empty());
    }

    #[test]
    fn test_query_deep_builds_analysis_after_fast_sat_skips_it() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("w", 32);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);
        state.make_symbolic("z", 32);

        let w = state.get_register("w");
        let x = state.get_register("x");
        let y = state.get_register("y");
        let z = state.get_register("z");
        state.add_true_constraint(&w.eq(&ctx, &SymValue::concrete(1, 32)));
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(2, 32)));
        state.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(3, 32)));
        state.add_true_constraint(&z.eq(&ctx, &SymValue::concrete(4, 32)));

        let solver = SymSolver::new(&ctx);
        assert!(solver.is_sat(&state));
        assert!(solver.analysis_cache.borrow().state_cache.is_empty());

        let x_is_two = x.to_bv(&ctx).eq(BV::from_u64(2, 32));
        assert_eq!(
            solver.sat_with_constraint(&state, &x_is_two),
            SatResult::Sat
        );
        assert!(!solver.analysis_cache.borrow().state_cache.is_empty());
    }

    #[test]
    fn test_selection_solver_reuses_same_selection_key() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        state.make_symbolic("y", 32);
        let x = state.get_register("x");
        let y = state.get_register("y");
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(5, 32)));
        state.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(9, 32)));

        let solver = SymSolver::new(&ctx);
        let selection = solver.preferred_selection_for_query(
            &state,
            &solver.expr_dependencies_bv(&x.to_bv(&ctx)),
            DeepQueryKind::Predicate,
        );
        solver.ensure_selection_solver(&selection);
        let first_key = solver.selection_session.borrow().asserted_key.clone();
        solver.ensure_selection_solver(&selection);
        assert_eq!(solver.selection_session.borrow().asserted_key, first_key);
    }

    #[test]
    fn test_cursor_fact_cache_reuses_dependency_extraction_for_descendants() {
        let ctx = Context::thread_local();

        let mut base = SymState::new(&ctx, 0x1000);
        base.make_symbolic("x", 32);
        let x = base.get_register("x");
        base.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(1, 32)));

        let mut child = base.fork();
        child.make_symbolic("y", 32);
        let y = child.get_register("y");
        child.add_true_constraint(&y.eq(&ctx, &SymValue::concrete(2, 32)));

        let solver = SymSolver::new(&ctx);
        let _ = solver.state_constraint_analysis(&base);
        let cursor_facts_after_base = solver.analysis_cache.borrow().cursor_facts.len();
        assert_eq!(cursor_facts_after_base, 1);

        let _ = solver.state_constraint_analysis(&child);
        let cursor_facts_after_child = solver.analysis_cache.borrow().cursor_facts.len();
        assert_eq!(cursor_facts_after_child, 2);
        assert!(
            solver
                .analysis_cache
                .borrow()
                .state_cache
                .contains_key(&base.constraint_cursor_key())
        );
        assert!(
            solver
                .analysis_cache
                .borrow()
                .state_cache
                .contains_key(&child.constraint_cursor_key())
        );
    }

    #[test]
    fn test_small_connected_query_prefers_full_state_selection() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        let x = state.get_register("x");
        state.add_true_constraint(&x.eq(&ctx, &SymValue::concrete(5, 32)));

        let solver = SymSolver::new(&ctx);
        let selection = solver.preferred_selection_for_query(
            &state,
            &solver.expr_dependencies_bv(&x.to_bv(&ctx)),
            DeepQueryKind::Predicate,
        );
        assert!(selection.is_full_state);
        assert_eq!(selection.constraints.len(), state.constraints().len());
    }

    #[test]
    fn test_multi_component_model_query_keeps_partitioned_selection() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        for name in ["a", "b", "c", "d", "e", "f"] {
            state.make_symbolic(name, 32);
        }

        for (index, name) in ["a", "b", "c", "d", "e"].iter().enumerate() {
            let value = state.get_register(name);
            state.add_true_constraint(&value.eq(&ctx, &SymValue::concrete(index as u64, 32)));
        }

        let f = state.get_register("f");
        state.constrain_range(&f, 3, 9);

        let solver = SymSolver::new(&ctx);
        let selection = solver.preferred_selection_for_query(
            &state,
            &solver.expr_dependencies_bv(&f.to_bv(&ctx)),
            DeepQueryKind::Model,
        );
        assert!(!selection.is_full_state);
        assert!(selection.constraints.len() < state.constraints().len());
        assert_eq!(selection.key.partition_ids.len(), 1);
    }

    #[test]
    fn test_abstract_prefilter_detects_conflicting_eq() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        let x = state.get_register("x");
        state.constrain_eq(&x, 5);

        let solver = SymSolver::new(&ctx);
        let impossible = x.to_bv(&ctx).eq(BV::from_u64(7, 32));
        assert_eq!(
            solver.sat_with_constraint(&state, &impossible),
            SatResult::Unsat
        );
    }

    #[test]
    fn test_abstract_prefilter_uses_range_for_zero_queries() {
        let ctx = Context::thread_local();

        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("x", 32);
        let x = state.get_register("x");
        state.constrain_range(&x, 3, 9);

        let solver = SymSolver::new(&ctx);
        assert!(!solver.can_be_zero(&state, &x));
        assert!(!solver.must_be_zero(&state, &x));
        assert_eq!(solver.minimize(&state, &x), Some(3));
        assert_eq!(solver.maximize(&state, &x), Some(9));
    }
}
