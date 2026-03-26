//! Z3 solver wrapper for constraint solving.
//!
//! This module provides a high-level interface to Z3 for checking
//! path feasibility and extracting concrete values.

use std::cell::RefCell;
use std::collections::HashMap;
use std::time::Duration;

use z3::ast::{Ast, BV, Bool};
use z3::{Context, Model, Params, Solver};

use crate::state::SymState;
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
    /// The underlying Z3 solver.
    solver: Solver,
    /// Timeout in milliseconds (0 = no timeout).
    _timeout_ms: u32,
    /// Memoized satisfiability results for state queries.
    sat_cache: RefCell<HashMap<String, SatResult>>,
    /// Internal counters used for perf/debug summaries.
    stats: RefCell<SolverStats>,
}

impl<'ctx> SymSolver<'ctx> {
    /// Create a new solver.
    pub fn new(ctx: &'ctx Context) -> Self {
        let solver = Solver::new();
        Self {
            ctx,
            solver,
            _timeout_ms: 0,
            sat_cache: RefCell::new(HashMap::new()),
            stats: RefCell::new(SolverStats::default()),
        }
    }

    /// Create a solver with a timeout.
    pub fn with_timeout(ctx: &'ctx Context, timeout: Duration) -> Self {
        let solver = Solver::new();
        let timeout_ms = timeout.as_millis() as u32;

        // Set timeout parameter
        let mut params = Params::new();
        params.set_u32("timeout", timeout_ms);
        solver.set_params(&params);

        Self {
            ctx,
            solver,
            _timeout_ms: timeout_ms,
            sat_cache: RefCell::new(HashMap::new()),
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

    fn state_sat_cache_key(&self, state: &SymState<'ctx>) -> String {
        match state.constraints() {
            [] => "true".to_string(),
            [constraint] => constraint.simplify().to_string(),
            _ => state.path_condition().simplify().to_string(),
        }
    }

    /// Check if a state's path constraints are satisfiable.
    pub fn is_sat(&self, state: &SymState<'ctx>) -> bool {
        self.stats.borrow_mut().sat_queries += 1;

        let cache_key = self.state_sat_cache_key(state);
        if let Some(result) = self.sat_cache.borrow().get(&cache_key).copied() {
            self.stats.borrow_mut().sat_cache_hits += 1;
            return result == SatResult::Sat;
        }

        self.stats.borrow_mut().sat_cache_misses += 1;
        self.solver.push();
        self.solver_assert_all(state.constraints());
        let result = self.check();
        self.solver.pop(1);
        self.sat_cache.borrow_mut().insert(cache_key, result);
        result == SatResult::Sat
    }

    /// Get a concrete model for a state's constraints.
    pub fn solve(&self, state: &SymState<'ctx>) -> Option<SymModel<'_>> {
        self.stats.borrow_mut().solve_calls += 1;

        let cache_key = self.state_sat_cache_key(state);
        if matches!(
            self.sat_cache.borrow().get(&cache_key),
            Some(SatResult::Unsat)
        ) {
            self.stats.borrow_mut().solve_unsat_shortcuts += 1;
            return None;
        }

        self.solver.push();
        self.solver_assert_all(state.constraints());

        let sat_result = self.check();
        let result = if sat_result == SatResult::Sat {
            self.get_model().map(|m| SymModel::new(self.ctx, m))
        } else {
            None
        };

        self.solver.pop(1);
        self.sat_cache.borrow_mut().insert(cache_key, sat_result);
        result
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
        self.solver.push();
        self.solver_assert_all(state.constraints());
        self.solver_assert(constraint);

        let result = if self.check() == SatResult::Sat {
            self.eval(target)
        } else {
            None
        };

        self.solver.pop(1);
        result
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
        let eq = a_bv.eq(&b_bv);

        self.solver.push();
        self.solver_assert_all(state.constraints());
        self.solver_assert(&eq);
        let result = self.check() == SatResult::Sat;
        self.solver.pop(1);

        result
    }

    /// Check if a value can be zero.
    pub fn can_be_zero(&self, state: &SymState<'ctx>, value: &SymValue<'ctx>) -> bool {
        let bv = value.to_bv(self.ctx);
        let zero = BV::from_i64(0, value.bits());
        let eq = bv.eq(&zero);

        self.solver.push();
        self.solver_assert_all(state.constraints());
        self.solver_assert(&eq);
        let result = self.check() == SatResult::Sat;
        self.solver.pop(1);

        result
    }

    /// Check if a value must be zero (cannot be non-zero).
    pub fn must_be_zero(&self, state: &SymState<'ctx>, value: &SymValue<'ctx>) -> bool {
        let bv = value.to_bv(self.ctx);
        let zero = BV::from_i64(0, value.bits());
        let neq = bv.eq(&zero).not();

        self.solver.push();
        self.solver_assert_all(state.constraints());
        self.solver_assert(&neq);
        let result = self.check() == SatResult::Unsat;
        self.solver.pop(1);

        result
    }

    /// Get the minimum value for a symbolic expression.
    pub fn minimize(&self, state: &SymState<'ctx>, value: &SymValue<'ctx>) -> Option<u64> {
        // Binary search for minimum
        self.solver.push();
        self.solver_assert_all(state.constraints());

        let bv = value.to_bv(self.ctx);
        let bits = value.bits();

        // Start with full range
        let mut lo: u64 = 0;
        let mut hi: u64 = if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };
        let mut result = None;

        while lo <= hi {
            let mid = lo + (hi - lo) / 2;
            let mid_bv = BV::from_u64(mid, bits);
            let constraint = bv.bvule(&mid_bv);

            self.solver.push();
            self.solver_assert(&constraint);

            if self.check() == SatResult::Sat {
                result = self.eval(value);
                hi = mid.saturating_sub(1);
            } else {
                lo = mid.saturating_add(1);
            }

            self.solver.pop(1);

            if lo == 0 && hi == u64::MAX {
                break; // Prevent infinite loop
            }
        }

        self.solver.pop(1);
        result
    }

    /// Get the maximum value for a symbolic expression.
    pub fn maximize(&self, state: &SymState<'ctx>, value: &SymValue<'ctx>) -> Option<u64> {
        self.solver.push();
        self.solver_assert_all(state.constraints());

        let bv = value.to_bv(self.ctx);
        let bits = value.bits();

        let mut lo: u64 = 0;
        let mut hi: u64 = if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };
        let mut result = None;

        while lo <= hi {
            let mid = lo + (hi - lo) / 2;
            let mid_bv = BV::from_u64(mid, bits);
            let constraint = bv.bvuge(&mid_bv);

            self.solver.push();
            self.solver_assert(&constraint);

            if self.check() == SatResult::Sat {
                result = self.eval(value);
                lo = mid.saturating_add(1);
            } else {
                hi = mid.saturating_sub(1);
            }

            self.solver.pop(1);

            if lo == 0 && hi == u64::MAX {
                break;
            }
        }

        self.solver.pop(1);
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
}
