use std::collections::{HashMap, VecDeque};

use r2ssa::SSAVar;

use crate::constraint::{Constraint, ConstraintSource, SolverNode};
use crate::lattice::TypeLattice;
use crate::model::{Type, TypeArena, TypeId};

type VarId = usize;
type ConstraintIdx = usize;

#[derive(Debug, Clone)]
pub struct SolverConfig {
    pub max_iterations: usize,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self { max_iterations: 64 }
    }
}

#[derive(Debug, Clone, Default)]
pub struct SolverDiagnostics {
    pub warnings: Vec<String>,
    pub conflicts: Vec<String>,
    pub iterations: usize,
    pub converged: bool,
    pub rewritten_constraints: usize,
    pub var_count: usize,
    pub constraints_processed: usize,
    pub queue_pushes: usize,
    pub queue_pops: usize,
}

#[derive(Debug, Clone)]
pub struct SolvedTypes<K = SSAVar> {
    pub arena: TypeArena,
    pub var_types: HashMap<K, TypeId>,
    pub diagnostics: SolverDiagnostics,
    pub top_id: TypeId,
}

#[derive(Debug, Clone, Copy)]
struct Assignment {
    ty: TypeId,
    priority: u8,
}

#[derive(Debug)]
struct SolverState<K> {
    arena: TypeArena,
    assignments: Vec<Option<Assignment>>,
    vars: Vec<K>,
    diagnostics: SolverDiagnostics,
    join_cache: HashMap<(TypeId, TypeId), TypeId>,
    meet_cache: HashMap<(TypeId, TypeId), TypeId>,
    changed_vars: Vec<VarId>,
}

impl<K: SolverNode> SolverState<K> {
    fn new(arena: TypeArena, vars: Vec<K>) -> Self {
        let var_count = vars.len();
        Self {
            arena,
            assignments: vec![None; var_count],
            vars,
            diagnostics: SolverDiagnostics::default(),
            join_cache: HashMap::new(),
            meet_cache: HashMap::new(),
            changed_vars: Vec::new(),
        }
    }

    fn join_cached(&mut self, a: TypeId, b: TypeId) -> TypeId {
        let key = normalize_pair(a, b);
        if let Some(ty) = self.join_cache.get(&key).copied() {
            return ty;
        }
        let ty = TypeLattice::join(&mut self.arena, a, b);
        self.join_cache.insert(key, ty);
        ty
    }

    fn meet_cached(&mut self, a: TypeId, b: TypeId) -> TypeId {
        let key = normalize_pair(a, b);
        if let Some(ty) = self.meet_cache.get(&key).copied() {
            return ty;
        }
        let ty = TypeLattice::meet(&mut self.arena, a, b);
        self.meet_cache.insert(key, ty);
        ty
    }

    fn assign(&mut self, var: VarId, ty: TypeId, priority: u8) -> bool {
        match self.assignments[var] {
            None => {
                self.assignments[var] = Some(Assignment { ty, priority });
                mark_changed(&mut self.changed_vars, var);
                true
            }
            Some(existing) if priority > existing.priority => {
                if existing.ty != ty {
                    self.diagnostics.conflicts.push(format!(
                        "{} overridden by higher-priority source ({})",
                        self.vars[var].solver_label(),
                        priority
                    ));
                }
                self.assignments[var] = Some(Assignment { ty, priority });
                mark_changed(&mut self.changed_vars, var);
                true
            }
            Some(existing) if priority < existing.priority => false,
            Some(existing) => {
                if existing.ty == ty {
                    return false;
                }
                let joined = self.join_cached(existing.ty, ty);
                if joined != existing.ty {
                    self.assignments[var] = Some(Assignment {
                        ty: joined,
                        priority,
                    });
                    mark_changed(&mut self.changed_vars, var);
                    true
                } else {
                    false
                }
            }
        }
    }

    fn apply_constraint(&mut self, constraint: &CompactConstraint) -> bool {
        let source_priority = constraint.source().priority();

        match constraint {
            CompactConstraint::SetType { var, ty, .. } => self.assign(*var, *ty, source_priority),
            CompactConstraint::Subtype { var, ty, .. } => {
                // An upper bound tightens: the intersection of two bounds is
                // what both allow. Routing it through `assign` would join it
                // back with what is already there, which is the opposite
                // operation and would discard every refinement.
                let Some(existing) = self.assignments[*var] else {
                    return self.assign(*var, *ty, source_priority);
                };
                let tightened = self.meet_cached(existing.ty, *ty);
                if tightened == existing.ty {
                    return false;
                }
                self.assignments[*var] = Some(Assignment {
                    ty: tightened,
                    priority: existing.priority.max(source_priority),
                });
                mark_changed(&mut self.changed_vars, *var);
                true
            }
            CompactConstraint::HasCapability { ptr, elem_ty, .. } => {
                let ptr_ty = self.arena.ptr(*elem_ty);
                self.assign(*ptr, ptr_ty, source_priority)
            }
            CompactConstraint::FieldAccess {
                base_ptr,
                offset,
                field_ty,
                field_name,
                ..
            } => {
                if let Some(existing) = self.assignments[*base_ptr]
                    && field_access_is_noop(
                        &self.arena,
                        existing.ty,
                        *offset,
                        *field_ty,
                        field_name,
                    )
                {
                    return false;
                }

                let mut struct_ty = self.assignments[*base_ptr]
                    .and_then(|assignment| match self.arena.get(assignment.ty) {
                        Type::Ptr(inner) => match self.arena.get(*inner) {
                            Type::Struct(_) => Some(*inner),
                            _ => None,
                        },
                        Type::Struct(_) => Some(assignment.ty),
                        _ => None,
                    })
                    .unwrap_or_else(|| self.arena.struct_anon());

                struct_ty =
                    self.arena
                        .struct_with_field(struct_ty, *offset, field_name.clone(), *field_ty);
                let ptr_ty = self.arena.ptr(struct_ty);

                if let Some(existing) = self.assignments[*base_ptr]
                    && existing.priority == source_priority
                {
                    if existing.ty != ptr_ty {
                        self.assignments[*base_ptr] = Some(Assignment {
                            ty: ptr_ty,
                            priority: existing.priority,
                        });
                        mark_changed(&mut self.changed_vars, *base_ptr);
                        return true;
                    }
                    return false;
                }

                self.assign(*base_ptr, ptr_ty, source_priority)
            }
            CompactConstraint::CallSig {
                args, params, ret, ..
            } => {
                let mut changed = false;
                for (arg, param_ty) in args.iter().zip(params.iter()) {
                    changed |= self.assign(*arg, *param_ty, source_priority);
                }
                if let Some((ret_var, ret_ty)) = ret {
                    changed |= self.assign(*ret_var, *ret_ty, source_priority);
                }
                changed
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeSolver {
    config: SolverConfig,
}

impl TypeSolver {
    pub fn new(config: SolverConfig) -> Self {
        Self { config }
    }

    pub fn solve<K: SolverNode>(
        &self,
        arena: TypeArena,
        constraints: &[Constraint<K>],
    ) -> SolvedTypes<K> {
        solve_worklist(arena, constraints, self.config.max_iterations)
    }
}

#[derive(Debug)]
struct VarInterner<K> {
    ids: HashMap<K, VarId>,
    vars: Vec<K>,
}

impl<K> Default for VarInterner<K> {
    fn default() -> Self {
        Self {
            ids: HashMap::new(),
            vars: Vec::new(),
        }
    }
}

impl<K: SolverNode> VarInterner<K> {
    fn intern(&mut self, var: &K) -> VarId {
        if let Some(id) = self.ids.get(var).copied() {
            return id;
        }
        let id = self.vars.len();
        self.vars.push(var.clone());
        self.ids.insert(var.clone(), id);
        id
    }

    fn len(&self) -> usize {
        self.vars.len()
    }

    fn into_vars(self) -> Vec<K> {
        self.vars
    }
}

#[derive(Debug, Clone)]
enum RawConstraint {
    SetType {
        var: VarId,
        ty: TypeId,
        source: ConstraintSource,
    },
    Equal {
        a: VarId,
        b: VarId,
        source: ConstraintSource,
    },
    Subtype {
        var: VarId,
        ty: TypeId,
        source: ConstraintSource,
    },
    HasCapability {
        ptr: VarId,
        elem_ty: TypeId,
        source: ConstraintSource,
    },
    CallSig {
        target: VarId,
        args: Vec<VarId>,
        params: Vec<TypeId>,
        ret: Option<(VarId, TypeId)>,
        source: ConstraintSource,
    },
    FieldAccess {
        base_ptr: VarId,
        offset: u64,
        field_ty: TypeId,
        field_name: Option<String>,
        source: ConstraintSource,
    },
}

#[derive(Debug, Clone)]
enum CompactConstraint {
    SetType {
        var: VarId,
        ty: TypeId,
        source: ConstraintSource,
    },
    Subtype {
        var: VarId,
        ty: TypeId,
        source: ConstraintSource,
    },
    HasCapability {
        ptr: VarId,
        elem_ty: TypeId,
        source: ConstraintSource,
    },
    CallSig {
        target: VarId,
        args: Vec<VarId>,
        params: Vec<TypeId>,
        ret: Option<(VarId, TypeId)>,
        source: ConstraintSource,
    },
    FieldAccess {
        base_ptr: VarId,
        offset: u64,
        field_ty: TypeId,
        field_name: Option<String>,
        source: ConstraintSource,
    },
}

impl CompactConstraint {
    fn source(&self) -> ConstraintSource {
        match self {
            Self::SetType { source, .. }
            | Self::Subtype { source, .. }
            | Self::HasCapability { source, .. }
            | Self::CallSig { source, .. }
            | Self::FieldAccess { source, .. } => *source,
        }
    }

    fn referenced_vars(&self, out: &mut Vec<VarId>) {
        out.clear();
        match self {
            Self::SetType { var, .. } | Self::Subtype { var, .. } => {
                out.push(*var);
            }
            Self::HasCapability { ptr, .. } => {
                out.push(*ptr);
            }
            Self::FieldAccess { base_ptr, .. } => {
                out.push(*base_ptr);
            }
            Self::CallSig {
                target, args, ret, ..
            } => {
                out.push(*target);
                out.extend(args.iter().copied());
                if let Some((ret_var, _)) = ret {
                    out.push(*ret_var);
                }
            }
        }
        out.sort_unstable();
        out.dedup();
    }
}

#[derive(Debug)]
struct RewrittenConstraints<K> {
    constraints: Vec<CompactConstraint>,
    class_members: Vec<Vec<VarId>>,
    vars: Vec<K>,
}

#[derive(Debug)]
struct VarDsu {
    parent: Vec<VarId>,
    rank: Vec<u16>,
}

impl VarDsu {
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
            rank: vec![0; size],
        }
    }

    fn find(&mut self, v: VarId) -> VarId {
        let parent = self.parent[v];
        if parent == v {
            return v;
        }
        let root = self.find(parent);
        self.parent[v] = root;
        root
    }

    fn union(&mut self, a: VarId, b: VarId) {
        let mut ra = self.find(a);
        let mut rb = self.find(b);
        if ra == rb {
            return;
        }

        if self.rank[ra] < self.rank[rb] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[rb] = ra;
        if self.rank[ra] == self.rank[rb] {
            self.rank[ra] = self.rank[ra].saturating_add(1);
        }
    }
}

fn rewrite_equal_constraints<K: SolverNode>(
    constraints: &[Constraint<K>],
) -> RewrittenConstraints<K> {
    let mut interner = VarInterner::<K>::default();
    let mut raw = Vec::with_capacity(constraints.len());

    for constraint in constraints {
        let compact = match constraint {
            Constraint::SetType { var, ty, source } => RawConstraint::SetType {
                var: interner.intern(var),
                ty: *ty,
                source: *source,
            },
            Constraint::Equal { a, b, source } => RawConstraint::Equal {
                a: interner.intern(a),
                b: interner.intern(b),
                source: *source,
            },
            Constraint::Subtype { var, ty, source } => RawConstraint::Subtype {
                var: interner.intern(var),
                ty: *ty,
                source: *source,
            },
            Constraint::HasCapability {
                ptr,
                elem_ty,
                source,
                ..
            } => RawConstraint::HasCapability {
                ptr: interner.intern(ptr),
                elem_ty: *elem_ty,
                source: *source,
            },
            Constraint::CallSig {
                target,
                args,
                params,
                ret,
                source,
            } => RawConstraint::CallSig {
                target: interner.intern(target),
                args: args.iter().map(|arg| interner.intern(arg)).collect(),
                params: params.clone(),
                ret: ret.as_ref().map(|(var, ty)| (interner.intern(var), *ty)),
                source: *source,
            },
            Constraint::FieldAccess {
                base_ptr,
                offset,
                field_ty,
                field_name,
                source,
            } => RawConstraint::FieldAccess {
                base_ptr: interner.intern(base_ptr),
                offset: *offset,
                field_ty: *field_ty,
                field_name: field_name.clone(),
                source: *source,
            },
        };
        raw.push(compact);
    }

    let mut dsu = VarDsu::new(interner.len());
    for constraint in &raw {
        if let RawConstraint::Equal { a, b, .. } = constraint {
            dsu.union(*a, *b);
        }
    }

    let var_count = interner.len();
    let mut class_members = vec![Vec::new(); var_count];
    for id in 0..var_count {
        let rep = dsu.find(id);
        class_members[rep].push(id);
    }

    let mut rewritten = Vec::with_capacity(raw.len());
    for constraint in raw {
        let compact = match constraint {
            RawConstraint::Equal { source, .. } => {
                let _ = source;
                continue;
            }
            RawConstraint::SetType { var, ty, source } => CompactConstraint::SetType {
                var: dsu.find(var),
                ty,
                source,
            },
            RawConstraint::Subtype { var, ty, source } => CompactConstraint::Subtype {
                var: dsu.find(var),
                ty,
                source,
            },
            RawConstraint::HasCapability {
                ptr,
                elem_ty,
                source,
                ..
            } => CompactConstraint::HasCapability {
                ptr: dsu.find(ptr),
                elem_ty,
                source,
            },
            RawConstraint::CallSig {
                target,
                args,
                params,
                ret,
                source,
            } => CompactConstraint::CallSig {
                target: dsu.find(target),
                args: args.into_iter().map(|arg| dsu.find(arg)).collect(),
                params,
                ret: ret.map(|(var, ty)| (dsu.find(var), ty)),
                source,
            },
            RawConstraint::FieldAccess {
                base_ptr,
                offset,
                field_ty,
                field_name,
                source,
            } => CompactConstraint::FieldAccess {
                base_ptr: dsu.find(base_ptr),
                offset,
                field_ty,
                field_name,
                source,
            },
        };
        rewritten.push(compact);
    }

    RewrittenConstraints {
        constraints: rewritten,
        class_members,
        vars: interner.into_vars(),
    }
}

fn build_adjacency(var_count: usize, constraints: &[CompactConstraint]) -> Vec<Vec<ConstraintIdx>> {
    let mut var_to_constraints = vec![Vec::new(); var_count];
    let mut refs = Vec::new();

    for (idx, constraint) in constraints.iter().enumerate() {
        constraint.referenced_vars(&mut refs);
        for var in &refs {
            var_to_constraints[*var].push(idx);
        }
    }

    var_to_constraints
}

fn solve_worklist<K: SolverNode>(
    arena: TypeArena,
    constraints: &[Constraint<K>],
    max_iterations: usize,
) -> SolvedTypes<K> {
    let rewritten = rewrite_equal_constraints(constraints);
    let adjacency = build_adjacency(rewritten.vars.len(), &rewritten.constraints);
    let var_count = rewritten.vars.len();
    let constraint_count = rewritten.constraints.len();

    let mut state = SolverState::new(arena, rewritten.vars);
    state.diagnostics.rewritten_constraints = constraint_count;
    state.diagnostics.var_count = var_count;

    let mut queue: VecDeque<ConstraintIdx> = (0..constraint_count).collect();
    let mut in_queue = vec![true; constraint_count];
    state.diagnostics.queue_pushes = queue.len();

    while state.diagnostics.iterations < max_iterations && !queue.is_empty() {
        state.diagnostics.iterations = state.diagnostics.iterations.saturating_add(1);
        let wave_len = queue.len();

        for _ in 0..wave_len {
            let Some(c_idx) = queue.pop_front() else {
                break;
            };
            in_queue[c_idx] = false;
            state.diagnostics.queue_pops = state.diagnostics.queue_pops.saturating_add(1);
            state.diagnostics.constraints_processed =
                state.diagnostics.constraints_processed.saturating_add(1);

            state.changed_vars.clear();
            state.apply_constraint(&rewritten.constraints[c_idx]);

            for i in 0..state.changed_vars.len() {
                let var = state.changed_vars[i];
                for dep in &adjacency[var] {
                    if !in_queue[*dep] {
                        in_queue[*dep] = true;
                        queue.push_back(*dep);
                        state.diagnostics.queue_pushes =
                            state.diagnostics.queue_pushes.saturating_add(1);
                    }
                }
            }
        }
    }

    state.diagnostics.converged = queue.is_empty();
    if !state.diagnostics.converged {
        state.diagnostics.warnings.push(format!(
            "type solver reached iteration cap ({})",
            max_iterations
        ));
    }

    materialize_solution(
        state.arena,
        state.assignments,
        rewritten.class_members,
        state.vars,
        state.diagnostics,
    )
}

fn materialize_solution<K: SolverNode>(
    arena: TypeArena,
    assignments: Vec<Option<Assignment>>,
    class_members: Vec<Vec<VarId>>,
    vars: Vec<K>,
    diagnostics: SolverDiagnostics,
) -> SolvedTypes<K> {
    let mut var_types: HashMap<K, TypeId> = HashMap::new();

    for (representative, assignment) in assignments.iter().enumerate() {
        let Some(assignment) = assignment else {
            continue;
        };

        if let Some(members) = class_members.get(representative)
            && !members.is_empty()
        {
            for member in members {
                if let Some(var) = vars.get(*member) {
                    var_types.insert(var.clone(), assignment.ty);
                }
            }
            continue;
        }

        if let Some(var) = vars.get(representative) {
            var_types.insert(var.clone(), assignment.ty);
        }
    }

    let top_id = arena.top();

    SolvedTypes {
        arena,
        var_types,
        diagnostics,
        top_id,
    }
}

fn normalize_pair(a: TypeId, b: TypeId) -> (TypeId, TypeId) {
    if a <= b { (a, b) } else { (b, a) }
}

fn mark_changed(changed_vars: &mut Vec<VarId>, var: VarId) {
    if !changed_vars.contains(&var) {
        changed_vars.push(var);
    }
}

fn field_access_is_noop(
    arena: &TypeArena,
    ty: TypeId,
    offset: u64,
    field_ty: TypeId,
    field_name: &Option<String>,
) -> bool {
    let struct_ty = match arena.get(ty) {
        Type::Ptr(inner) => match arena.get(*inner) {
            Type::Struct(_) => Some(*inner),
            _ => None,
        },
        Type::Struct(_) => Some(ty),
        _ => None,
    };

    let Some(struct_ty) = struct_ty else {
        return false;
    };

    let Type::Struct(shape) = arena.get(struct_ty) else {
        return false;
    };

    let Some(field) = shape.fields.get(&offset) else {
        return false;
    };

    if field.ty != field_ty {
        return false;
    }

    field.name.is_some() || field_name.is_none()
}

#[cfg(test)]
fn solve_reference<K: SolverNode>(
    arena: TypeArena,
    constraints: &[Constraint<K>],
    max_iterations: usize,
) -> SolvedTypes<K> {
    let rewritten = rewrite_equal_constraints(constraints);
    let constraint_count = rewritten.constraints.len();
    let var_count = rewritten.vars.len();

    let mut state = SolverState::new(arena, rewritten.vars);
    state.diagnostics.rewritten_constraints = constraint_count;
    state.diagnostics.var_count = var_count;

    for iter in 0..max_iterations {
        let mut changed = false;
        for constraint in &rewritten.constraints {
            state.diagnostics.constraints_processed =
                state.diagnostics.constraints_processed.saturating_add(1);
            state.changed_vars.clear();
            changed |= state.apply_constraint(constraint);
        }

        state.diagnostics.iterations = iter.saturating_add(1);
        if !changed {
            state.diagnostics.converged = true;
            break;
        }
    }

    if !state.diagnostics.converged {
        state.diagnostics.warnings.push(format!(
            "type solver reached iteration cap ({})",
            max_iterations
        ));
    }

    materialize_solution(
        state.arena,
        state.assignments,
        rewritten.class_members,
        state.vars,
        state.diagnostics,
    )
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::constraint::{Constraint, ConstraintSource, MemoryCapability};
    use crate::model::Signedness;

    fn solved_shapes(solved: &SolvedTypes) -> BTreeMap<String, Type> {
        let mut map = BTreeMap::new();
        for (var, ty_id) in &solved.var_types {
            map.insert(var.display_name(), solved.arena.get(*ty_id).clone());
        }
        map
    }

    fn assert_semantic_equivalence(new: &SolvedTypes, reference: &SolvedTypes) {
        assert_eq!(solved_shapes(new), solved_shapes(reference));
    }

    #[test]
    fn external_constraints_override_inferred() {
        let mut arena = TypeArena::default();
        let inferred = arena.int(32, Signedness::Unsigned);
        let void_ty = arena.unknown_alias("void");
        let external = arena.ptr(void_ty);
        let var = SSAVar::new("RAX", 1, 8);

        let constraints = vec![
            Constraint::SetType {
                var: var.clone(),
                ty: inferred,
                source: ConstraintSource::Inferred,
            },
            Constraint::SetType {
                var: var.clone(),
                ty: external,
                source: ConstraintSource::External,
            },
        ];

        let solved = TypeSolver::new(SolverConfig::default()).solve(arena, &constraints);
        let ty = solved.var_types.get(&var).copied().expect("missing type");
        assert_eq!(solved.arena.get(ty), solved.arena.get(external));
    }

    #[test]
    fn field_access_enriches_named_struct_pointer() {
        let mut arena = TypeArena::default();
        let base = SSAVar::new("obj", 0, 8);
        let field_ty = arena.int(32, Signedness::Signed);
        let named = arena.struct_named_or_existing("DemoStruct");
        let named_ptr = arena.ptr(named);

        let constraints = vec![
            Constraint::SetType {
                var: base.clone(),
                ty: named_ptr,
                source: ConstraintSource::Inferred,
            },
            Constraint::FieldAccess {
                base_ptr: base.clone(),
                offset: 48,
                field_ty,
                field_name: Some("thirteenth".to_string()),
                source: ConstraintSource::Inferred,
            },
        ];

        let solved = TypeSolver::new(SolverConfig::default()).solve(arena, &constraints);
        let ty = solved
            .var_types
            .get(&base)
            .copied()
            .expect("missing base type");
        let Type::Ptr(inner) = solved.arena.get(ty) else {
            panic!("base should remain a pointer");
        };
        let Type::Struct(shape) = solved.arena.get(*inner) else {
            panic!("pointee should be struct");
        };
        assert_eq!(shape.name.as_deref(), Some("DemoStruct"));
        let field = shape.fields.get(&48).expect("offset 48 field missing");
        assert_eq!(field.name.as_deref(), Some("thirteenth"));
    }

    #[test]
    fn equal_chain_closure_propagates_with_low_iteration_cap() {
        let mut arena = TypeArena::default();
        let v0 = SSAVar::new("tmp:0", 0, 8);
        let v1 = SSAVar::new("tmp:1", 0, 8);
        let v2 = SSAVar::new("tmp:2", 0, 8);
        let v3 = SSAVar::new("tmp:3", 0, 8);
        let void_ty = arena.unknown_alias("void");
        let ptr_ty = arena.ptr(void_ty);

        let constraints = vec![
            Constraint::SetType {
                var: v0.clone(),
                ty: ptr_ty,
                source: ConstraintSource::Inferred,
            },
            Constraint::Equal {
                a: v0.clone(),
                b: v1.clone(),
                source: ConstraintSource::Inferred,
            },
            Constraint::Equal {
                a: v1.clone(),
                b: v2.clone(),
                source: ConstraintSource::Inferred,
            },
            Constraint::Equal {
                a: v2.clone(),
                b: v3.clone(),
                source: ConstraintSource::Inferred,
            },
        ];

        let solved = TypeSolver::new(SolverConfig { max_iterations: 1 }).solve(arena, &constraints);
        let t3 = solved
            .var_types
            .get(&v3)
            .copied()
            .expect("v3 should be typed");
        assert_eq!(solved.arena.get(t3), solved.arena.get(ptr_ty));
    }

    #[test]
    fn external_type_pins_equal_class() {
        let mut arena = TypeArena::default();
        let a = SSAVar::new("RAX", 1, 8);
        let b = SSAVar::new("tmp:9", 2, 8);
        let inferred = arena.int(64, Signedness::Unsigned);
        let void_ty = arena.unknown_alias("void");
        let ext = arena.ptr(void_ty);

        let constraints = vec![
            Constraint::SetType {
                var: a.clone(),
                ty: ext,
                source: ConstraintSource::External,
            },
            Constraint::SetType {
                var: b.clone(),
                ty: inferred,
                source: ConstraintSource::Inferred,
            },
            Constraint::Equal {
                a: a.clone(),
                b: b.clone(),
                source: ConstraintSource::Inferred,
            },
        ];

        let solved = TypeSolver::new(SolverConfig::default()).solve(arena, &constraints);
        let ta = solved.var_types.get(&a).copied().expect("a typed");
        let tb = solved.var_types.get(&b).copied().expect("b typed");
        assert_eq!(solved.arena.get(ta), solved.arena.get(ext));
        assert_eq!(solved.arena.get(tb), solved.arena.get(ext));
    }

    #[test]
    fn worklist_matches_reference_solver_on_mixed_constraints() {
        let mut arena = TypeArena::default();
        let mut vars = Vec::new();
        for i in 0..24 {
            vars.push(SSAVar::new(format!("tmp:{:x}", i), 0, 8));
        }

        let i32_ty = arena.int(32, Signedness::Signed);
        let u64_ty = arena.int(64, Signedness::Unsigned);
        let f64_ty = arena.float(64);
        let bool_ty = arena.bool_ty();
        let void_ty = arena.unknown_alias("void");
        let void_ptr = arena.ptr(void_ty);

        let mut constraints = Vec::new();

        for i in 1..vars.len() {
            constraints.push(Constraint::Equal {
                a: vars[i - 1].clone(),
                b: vars[i].clone(),
                source: ConstraintSource::Inferred,
            });
        }

        for (i, var) in vars.iter().enumerate() {
            let source = if i % 7 == 0 {
                ConstraintSource::External
            } else if i % 5 == 0 {
                ConstraintSource::SignatureRegistry
            } else {
                ConstraintSource::Inferred
            };

            let ty = match i % 4 {
                0 => i32_ty,
                1 => u64_ty,
                2 => f64_ty,
                _ => bool_ty,
            };

            constraints.push(Constraint::SetType {
                var: var.clone(),
                ty,
                source,
            });

            if i % 3 == 0 {
                constraints.push(Constraint::Subtype {
                    var: var.clone(),
                    ty: i32_ty,
                    source: ConstraintSource::Inferred,
                });
            }
        }

        constraints.push(Constraint::HasCapability {
            ptr: vars[3].clone(),
            capability: MemoryCapability::Load,
            elem_ty: i32_ty,
            source: ConstraintSource::Inferred,
        });
        constraints.push(Constraint::FieldAccess {
            base_ptr: vars[3].clone(),
            offset: 16,
            field_ty: i32_ty,
            field_name: Some("field_x".to_string()),
            source: ConstraintSource::Inferred,
        });
        constraints.push(Constraint::CallSig {
            target: vars[0].clone(),
            args: vec![vars[1].clone(), vars[2].clone()],
            params: vec![void_ptr, i32_ty],
            ret: Some((vars[4].clone(), u64_ty)),
            source: ConstraintSource::SignatureRegistry,
        });

        let solved_new =
            TypeSolver::new(SolverConfig::default()).solve(arena.clone(), &constraints);
        let solved_ref =
            solve_reference(arena, &constraints, SolverConfig::default().max_iterations);

        assert_semantic_equivalence(&solved_new, &solved_ref);
    }
}
