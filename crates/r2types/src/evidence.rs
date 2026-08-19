//! Types recovered from what the code does, for binaries that carry no types.
//!
//! With debug info the prototype is read; without it every type has to be
//! earned. This module gathers the evidence a prepared function already proves
//! -- the prototype of each callee at each call site, the width of every
//! certified memory access, the identities the SSA form guarantees -- and hands
//! the whole set to the type solver at once. Nothing here decides a type on its
//! own: a value keeps whatever the solved constraint system says, and a value no
//! constraint reaches stays unresolved.
//!
//! The nodes are the values and the memory objects of the prepared artifact
//! rather than SSA variables, because the evidence lives there: a call result is
//! a value, a stack home is an object, and the same solver runs over both.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::constraint::{Constraint, ConstraintSource, SolverNode};
use crate::context::{ExternalStackBase, StackSlotKey};
use crate::convert::{CTypeLike, to_c_type_like};
use crate::facts::FunctionType;
use crate::model::{Signedness, Type, TypeArena, TypeId};
use crate::solver::{SolvedTypes, SolverConfig, TypeSolver};

/// A node of the recovered type graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EvidenceNode {
    /// One SSA value of the prepared graph.
    Value(r2ssa::ValueId),
    /// One memory object: a stack home, a frame object, a heap block.
    Object(r2ssa::ObjectId),
}

impl SolverNode for EvidenceNode {
    fn solver_label(&self) -> String {
        match self {
            Self::Value(value) => format!("value{}", value.0),
            Self::Object(object) => format!("object{}", object.0),
        }
    }
}

/// What the solver concluded, spelled the way the evidence spelled it.
#[derive(Debug, Clone, Default)]
pub struct EvidenceTypes {
    value_types: HashMap<r2ssa::ValueId, CTypeLike>,
    slot_types: BTreeMap<StackSlotKey, CTypeLike>,
}

impl EvidenceTypes {
    pub fn is_empty(&self) -> bool {
        self.value_types.is_empty() && self.slot_types.is_empty()
    }

    pub fn value_type(&self, value: r2ssa::ValueId) -> Option<&CTypeLike> {
        self.value_types.get(&value)
    }

    pub fn stack_slot_types(&self) -> impl Iterator<Item = (&StackSlotKey, &CTypeLike)> {
        self.slot_types.iter()
    }
}

/// Solve the recovered types of one prepared function.
///
/// `callsite_signatures` supplies the prototype of the callee reached from each
/// call site; call sites without one contribute no type evidence rather than a
/// default prototype, because a guessed arity would type arguments that no
/// callee declares.
pub fn solve_evidence_types(
    source: &r2ssa::SsaArtifact,
    callsite_signatures: &BTreeMap<r2ssa::CallSiteId, FunctionType>,
    ptr_bits: u32,
) -> EvidenceTypes {
    let mut builder = EvidenceBuilder::new(source, ptr_bits);
    builder.gather_ssa_identities();
    builder.gather_callee_prototypes(callsite_signatures);
    builder.gather_memory_widths();
    builder.gather_allocation_element_widths(callsite_signatures);

    // Refinement rounds: a type learned in one round decides which operand of an
    // address computation is the pointer, which is new evidence about the width
    // it points at, which is a constraint the next round solves with. Rounds
    // stop as soon as one adds nothing.
    const MAX_REFINEMENT_ROUNDS: usize = 4;
    let mut solved = builder.solve();
    for _ in 0..MAX_REFINEMENT_ROUNDS {
        if !builder.gather_indexed_pointer_bases(&solved) {
            break;
        }
        solved = builder.solve();
    }
    builder.read_back(&solved)
}

/// Interning that keeps the lattice structural and the spelling intact.
///
/// `size_t` and `unsigned long` are one type to the lattice and two names to a
/// reader, and `void *` is the pointer that any object pointer refines, which is
/// the arena's `Top` rather than a distinct pointee. Interning resolves both;
/// the spelling is remembered per assertion so the reader still sees the name
/// the evidence used.
struct SpelledType {
    ty: TypeId,
    spelling: CTypeLike,
}

struct EvidenceBuilder<'a> {
    source: &'a r2ssa::SsaArtifact,
    ptr_bits: u32,
    arena: TypeArena,
    constraints: Vec<Constraint<EvidenceNode>>,
    /// Spellings asserted on a node, kept to name the solved type.
    spellings: Vec<(EvidenceNode, TypeId, CTypeLike)>,
    /// Bounds already asserted, so a refinement round can tell what is new.
    asserted: HashSet<(EvidenceNode, TypeId)>,
    /// Same union-find the solver runs, so a spelling asserted on one member of
    /// an equality class can name the whole class.
    classes: NodeClasses,
}

impl<'a> EvidenceBuilder<'a> {
    fn new(source: &'a r2ssa::SsaArtifact, ptr_bits: u32) -> Self {
        Self {
            source,
            ptr_bits,
            arena: TypeArena::default(),
            constraints: Vec::new(),
            spellings: Vec::new(),
            asserted: HashSet::new(),
            classes: NodeClasses::default(),
        }
    }

    fn value_size(&self, value: r2ssa::ValueId) -> Option<u32> {
        self.source.value_var(value).map(|var| var.size)
    }

    fn value_is_constant(&self, value: r2ssa::ValueId) -> bool {
        self.source
            .value_var(value)
            .is_some_and(r2ssa::SSAVar::is_const)
    }

    fn equate(&mut self, a: r2ssa::ValueId, b: r2ssa::ValueId) {
        // A constant is compatible with every type, and one constant value is
        // shared by every use of that literal. Merging through it would fuse
        // unrelated variables into one class.
        if self.value_is_constant(a) || self.value_is_constant(b) {
            return;
        }
        if self.value_size(a) != self.value_size(b) {
            return;
        }
        let a = EvidenceNode::Value(a);
        let b = EvidenceNode::Value(b);
        self.classes.union(a, b);
        self.constraints.push(Constraint::Equal {
            a,
            b,
            source: ConstraintSource::Inferred,
        });
    }

    fn equate_nodes(&mut self, a: EvidenceNode, b: EvidenceNode) {
        self.classes.union(a, b);
        self.constraints.push(Constraint::Equal {
            a,
            b,
            source: ConstraintSource::Inferred,
        });
    }

    /// Record an upper bound, and report whether it was not already recorded.
    fn bound(
        &mut self,
        node: EvidenceNode,
        spelled: SpelledType,
        source: ConstraintSource,
    ) -> bool {
        if !self.asserted.insert((node, spelled.ty)) {
            return false;
        }
        self.classes.ensure(node);
        self.spellings.push((node, spelled.ty, spelled.spelling));
        // An upper bound, not an assignment: two prototypes that both describe
        // one value must intersect, so the more specific one survives whatever
        // order the worklist reaches them in.
        self.constraints.push(Constraint::Subtype {
            var: node,
            ty: spelled.ty,
            source,
        });
        true
    }

    /// Values the SSA form proves are the same value.
    fn gather_ssa_identities(&mut self) {
        let graph = self.source.graph();
        let mut pairs = Vec::new();
        for inst in &graph.insts {
            let Some(output) = inst.output else {
                continue;
            };
            match &inst.payload {
                r2ssa::InstPayload::Phi { .. } => {
                    for input in &inst.inputs {
                        pairs.push((output, *input));
                    }
                }
                r2ssa::InstPayload::Op(r2ssa::SSAOp::Copy { .. } | r2ssa::SSAOp::New { .. }) => {
                    if let Some(input) = inst.inputs.first() {
                        pairs.push((output, *input));
                    }
                }
                r2ssa::InstPayload::Op(_) => {}
            }
        }
        for (a, b) in pairs {
            self.equate(a, b);
        }
    }

    /// What each callee declares about the values it is handed and returns.
    fn gather_callee_prototypes(
        &mut self,
        callsite_signatures: &BTreeMap<r2ssa::CallSiteId, FunctionType>,
    ) {
        let certificates = self.source.certificates();
        let mut bounds = Vec::new();

        for (call_site, certificate) in &certificates.callsites {
            let Some(signature) = callsite_signatures.get(call_site) else {
                continue;
            };
            for argument in &certificate.argument_certificates {
                let Some(declared) = signature.params.get(argument.index) else {
                    continue;
                };
                if self.value_is_constant(argument.value) {
                    continue;
                }
                bounds.push((EvidenceNode::Value(argument.value), declared.clone()));
            }
        }

        for (value, certificate) in &certificates.call_results {
            let Some(signature) = callsite_signatures.get(&certificate.call_site) else {
                continue;
            };
            // A derived result is some function of the returned value, not the
            // returned value, so the callee's return type does not describe it.
            if !certificate.relation.is_identity() {
                continue;
            }
            bounds.push((EvidenceNode::Value(*value), signature.return_type.clone()));
        }

        for (node, declared) in bounds {
            let Some(spelled) = self.intern_spelled(&declared) else {
                continue;
            };
            self.bound(node, spelled, ConstraintSource::SignatureRegistry);
        }
    }

    /// Every certified access says its address is a pointer and how wide the
    /// thing it points at is, and ties a whole-cell home to the value it holds.
    fn gather_memory_widths(&mut self) {
        let certificates = self.source.certificates();
        let mut address_bounds = Vec::new();
        let mut cell_pairs = Vec::new();

        let scalar_cells = self.scalar_memory_cells();

        for access in certificates.memory_accesses.values() {
            if access.space != r2il::SpaceId::Ram {
                continue;
            }
            if !self.value_is_constant(access.address)
                && let Some(elem) = pointee_type_for_width(access.width)
            {
                address_bounds.push((EvidenceNode::Value(access.address), elem));
            }
            let Some(value) = access.value else {
                continue;
            };
            if !scalar_cells.contains(&access.object) || self.value_is_constant(value) {
                continue;
            }
            cell_pairs.push((
                EvidenceNode::Value(value),
                EvidenceNode::Object(access.object),
            ));
        }

        for (node, elem) in address_bounds {
            let Some(spelled) = self.intern_spelled(&elem) else {
                continue;
            };
            self.bound(node, spelled, ConstraintSource::Inferred);
        }
        for (value, object) in cell_pairs {
            self.equate_nodes(value, object);
        }
    }

    /// The element width of a block the function allocated.
    ///
    /// An allocator declares `void *` because it cannot know; the accesses the
    /// caller makes to the block do know, and a block reached only at one width
    /// is a pointer to that width.
    fn gather_allocation_element_widths(
        &mut self,
        callsite_signatures: &BTreeMap<r2ssa::CallSiteId, FunctionType>,
    ) {
        let certificates = self.source.certificates();
        let mut widths: BTreeMap<r2ssa::CallSiteId, BTreeSet<u32>> = BTreeMap::new();
        for access in certificates.memory_accesses.values() {
            let Some(object) = self.source.objects().object(access.object) else {
                continue;
            };
            if let r2ssa::ObjectKind::HeapAlloc { call_site, .. } = object.kind {
                widths.entry(call_site).or_default().insert(access.width);
            }
        }

        let mut bounds = Vec::new();
        for (value, certificate) in &certificates.call_results {
            if !certificate.relation.is_identity() {
                continue;
            }
            // Only refine what the callee itself declared as a pointer: a call
            // whose prototype is unknown has not been shown to return one.
            let declares_pointer = callsite_signatures
                .get(&certificate.call_site)
                .is_some_and(|signature| matches!(signature.return_type, CTypeLike::Pointer(_)));
            if !declares_pointer {
                continue;
            }
            let Some(widths) = widths.get(&certificate.call_site) else {
                continue;
            };
            let [width] = widths.iter().copied().collect::<Vec<_>>()[..] else {
                continue;
            };
            let Some(elem) = pointee_type_for_width(width) else {
                continue;
            };
            bounds.push((EvidenceNode::Value(*value), elem));
        }

        for (node, elem) in bounds {
            let Some(spelled) = self.intern_spelled(&elem) else {
                continue;
            };
            self.bound(node, spelled, ConstraintSource::Inferred);
        }
    }

    /// Which operand of an address computation is the pointer, once enough is
    /// known to tell, and how wide the thing it points at is.
    ///
    /// `base + index` reaches an element, so the width of the access made
    /// through it is the width of that element. Only a non-constant index is
    /// treated this way: a constant displacement reaches a field of one object,
    /// which says nothing about an element type and would contradict the struct
    /// the field belongs to. Returns whether anything new was learned.
    fn gather_indexed_pointer_bases(&mut self, solved: &SolvedTypes<EvidenceNode>) -> bool {
        let mut discovered = Vec::new();
        for access in self.source.certificates().memory_accesses.values() {
            if access.space != r2il::SpaceId::Ram {
                continue;
            }
            let Some(elem) = pointee_type_for_width(access.width) else {
                continue;
            };
            let Some((left, right)) = self.address_sum_operands(access.address) else {
                continue;
            };
            let left_pointer = self.solved_is_pointer(solved, left);
            let right_pointer = self.solved_is_pointer(solved, right);
            // Exactly one side has been shown to be a pointer; the other is the
            // index. Two pointers, or none, decides nothing.
            let base = match (left_pointer, right_pointer) {
                (true, false) => left,
                (false, true) => right,
                _ => continue,
            };
            let index = if base == left { right } else { left };
            if self.value_is_constant(index) {
                continue;
            }
            discovered.push((EvidenceNode::Value(base), elem));
        }

        let mut added = false;
        for (node, elem) in discovered {
            let Some(spelled) = self.intern_spelled(&elem) else {
                continue;
            };
            added |= self.bound(node, spelled, ConstraintSource::Inferred);
        }
        added
    }

    /// The two operands of an address that is one value plus another.
    fn address_sum_operands(
        &self,
        address: r2ssa::ValueId,
    ) -> Option<(r2ssa::ValueId, r2ssa::ValueId)> {
        let graph = self.source.graph();
        let mut current = address;
        let mut seen = HashSet::new();
        while seen.insert(current) {
            let inst = graph.inst(graph.def_inst(current)?)?;
            match &inst.payload {
                r2ssa::InstPayload::Op(r2ssa::SSAOp::Copy { .. } | r2ssa::SSAOp::New { .. }) => {
                    current = *inst.inputs.first()?;
                }
                r2ssa::InstPayload::Op(
                    r2ssa::SSAOp::IntAdd { .. } | r2ssa::SSAOp::PtrAdd { .. },
                ) => {
                    let [left, right] = inst.inputs[..] else {
                        return None;
                    };
                    return Some((left, right));
                }
                _ => return None,
            }
        }
        None
    }

    fn solved_is_pointer(&self, solved: &SolvedTypes<EvidenceNode>, value: r2ssa::ValueId) -> bool {
        solved
            .var_types
            .get(&EvidenceNode::Value(value))
            .is_some_and(|ty| matches!(solved.arena.get(*ty), Type::Ptr(_)))
    }

    /// Memory objects that hold exactly one value of one width.
    ///
    /// A home that is only ever read and written whole is the storage of one
    /// variable, so its type and the type of every value that passes through it
    /// are the same type. An object touched at more than one width, or narrower
    /// than itself, is an aggregate and is left alone.
    fn scalar_memory_cells(&self) -> HashSet<r2ssa::ObjectId> {
        let certificates = self.source.certificates();
        let mut widths: BTreeMap<r2ssa::ObjectId, BTreeSet<u32>> = BTreeMap::new();
        for access in certificates.memory_accesses.values() {
            if access.space != r2il::SpaceId::Ram {
                continue;
            }
            widths
                .entry(access.object)
                .or_default()
                .insert(access.width);
        }

        let mut cells = HashSet::new();
        for (object, widths) in widths {
            let [width] = widths.iter().copied().collect::<Vec<_>>()[..] else {
                continue;
            };
            let Some(fact) = self.source.objects().object(object) else {
                continue;
            };
            let identified = match fact.kind {
                r2ssa::ObjectKind::StackSlot {
                    space: r2il::SpaceId::Ram,
                    ..
                }
                | r2ssa::ObjectKind::FrameObject {
                    space: r2il::SpaceId::Ram,
                    ..
                } => true,
                // An unidentified region is a bucket, and two addresses that
                // landed in the same bucket are not the same storage. One
                // address expression over one set of SSA values is, so a bucket
                // reached only that way is still one cell.
                r2ssa::ObjectKind::EscapedUnknown {
                    space: r2il::SpaceId::Ram,
                } => self.object_has_single_address_identity(object),
                _ => false,
            };
            if !identified {
                continue;
            }
            if certificates
                .stack_slots
                .get(&object)
                .and_then(|slot| slot.size)
                .is_some_and(|size| size != width)
            {
                continue;
            }
            cells.insert(object);
        }
        cells
    }

    /// Whether every certified access to an object goes through one address.
    fn object_has_single_address_identity(&self, object: r2ssa::ObjectId) -> bool {
        let mut identity: Option<AddressIdentity> = None;
        for access in self.source.certificates().memory_accesses.values() {
            if access.object != object {
                continue;
            }
            let Some(current) = self.address_identity(access.address) else {
                return false;
            };
            match &identity {
                None => identity = Some(current),
                Some(existing) if *existing == current => {}
                Some(_) => return false,
            }
        }
        identity.is_some()
    }

    /// The address expression a value computes, as its operator and operands.
    fn address_identity(&self, address: r2ssa::ValueId) -> Option<AddressIdentity> {
        let graph = self.source.graph();
        let Some(inst) = graph.def_inst(address).and_then(|inst| graph.inst(inst)) else {
            return Some(AddressIdentity::Value(address));
        };
        match &inst.payload {
            r2ssa::InstPayload::Op(op) => Some(AddressIdentity::Computed {
                op: std::mem::discriminant(op),
                inputs: inst.inputs.clone(),
            }),
            r2ssa::InstPayload::Phi { .. } => None,
        }
    }

    fn intern_spelled(&mut self, ty: &CTypeLike) -> Option<SpelledType> {
        let id = self.intern_structural(ty)?;
        Some(SpelledType {
            ty: id,
            spelling: ty.clone(),
        })
    }

    fn intern_structural(&mut self, ty: &CTypeLike) -> Option<TypeId> {
        match ty {
            // `void` as a value type says nothing; as a pointee it is the top of
            // the pointee lattice, which is what `Top` already means.
            CTypeLike::Void | CTypeLike::Unknown | CTypeLike::Function => None,
            CTypeLike::Bool => Some(self.arena.bool_ty()),
            CTypeLike::Int { bits, signedness } => Some(self.arena.int(*bits, *signedness)),
            CTypeLike::Float(bits) => Some(self.arena.float(*bits)),
            CTypeLike::Pointer(inner) => {
                let inner = self
                    .intern_structural(inner)
                    .unwrap_or_else(|| self.arena.top());
                Some(self.arena.ptr(inner))
            }
            CTypeLike::Array(inner, len) => {
                let inner = self.intern_structural(inner)?;
                Some(self.arena.array(inner, *len, None))
            }
            CTypeLike::Struct(name) => Some(self.arena.unknown_alias(format!("struct {name}"))),
            CTypeLike::Union(name) => Some(self.arena.unknown_alias(format!("union {name}"))),
            CTypeLike::Enum(name) => Some(self.arena.unknown_alias(format!("enum {name}"))),
            CTypeLike::Typedef(name) => {
                let resolved = crate::facts::parse_type_like_spec(name, self.ptr_bits)?;
                if matches!(resolved, CTypeLike::Typedef(_)) {
                    return Some(self.arena.unknown_alias(name.clone()));
                }
                self.intern_structural(&resolved)
            }
        }
    }

    fn solve(&self) -> SolvedTypes<EvidenceNode> {
        let solver = TypeSolver::new(SolverConfig::default());
        solver.solve(self.arena.clone(), &self.constraints)
    }

    fn read_back(&mut self, solved: &SolvedTypes<EvidenceNode>) -> EvidenceTypes {
        // A spelling names the solved type only when it is that type. The class
        // carries it because every member of an equality class is one variable.
        let mut class_spellings: HashMap<EvidenceNode, CTypeLike> = HashMap::new();
        for (node, ty, spelling) in &self.spellings {
            if solved.var_types.get(node) != Some(ty) {
                continue;
            }
            let root = self.classes.root(*node);
            match class_spellings.get(&root) {
                None => {
                    class_spellings.insert(root, spelling.clone());
                }
                Some(existing) if existing == spelling => {}
                Some(_) => {
                    // Two names for one type is not a conflict about the type,
                    // but it is no longer evidence for either name.
                    class_spellings.insert(root, CTypeLike::Unknown);
                }
            }
        }

        let mut types = EvidenceTypes::default();
        let mut object_types: HashMap<r2ssa::ObjectId, CTypeLike> = HashMap::new();
        for (node, ty) in &solved.var_types {
            let Some(resolved) = self.spell(solved, &class_spellings, *node, *ty) else {
                continue;
            };
            match node {
                EvidenceNode::Value(value) => {
                    types.value_types.insert(*value, resolved);
                }
                EvidenceNode::Object(object) => {
                    object_types.insert(*object, resolved);
                }
            }
        }

        for (object, ty) in object_types {
            let Some(fact) = self.source.objects().object(object) else {
                continue;
            };
            let (base, offset) = match fact.kind {
                r2ssa::ObjectKind::StackSlot { base, offset, .. }
                | r2ssa::ObjectKind::FrameObject { base, offset, .. } => (base, offset),
                _ => continue,
            };
            types.slot_types.insert(
                StackSlotKey {
                    base: match base {
                        r2ssa::StackAddressBase::FramePointer => ExternalStackBase::FramePointer,
                        r2ssa::StackAddressBase::StackPointer => ExternalStackBase::StackPointer,
                    },
                    offset,
                },
                ty,
            );
        }

        types
    }

    fn spell(
        &mut self,
        solved: &SolvedTypes<EvidenceNode>,
        class_spellings: &HashMap<EvidenceNode, CTypeLike>,
        node: EvidenceNode,
        ty: TypeId,
    ) -> Option<CTypeLike> {
        // A `Bottom` anywhere is contradictory evidence, which is not a type.
        if type_is_unresolved(&solved.arena, ty) {
            return None;
        }
        let root = self.classes.root(node);
        if let Some(spelling) = class_spellings.get(&root)
            && !matches!(spelling, CTypeLike::Unknown)
        {
            return Some(spelling.clone());
        }
        let structural = structural_type_like(&solved.arena, ty);
        (!matches!(structural, CTypeLike::Unknown)).then_some(structural)
    }
}

/// How an address was computed, independent of the name of the result.
#[derive(Debug, Clone, PartialEq, Eq)]
enum AddressIdentity {
    Value(r2ssa::ValueId),
    Computed {
        op: std::mem::Discriminant<r2ssa::SSAOp>,
        inputs: Vec<r2ssa::ValueId>,
    },
}

/// The arena's `Top` pointee is `void`, which is how C spells "points at
/// something this has not been shown to know".
fn structural_type_like(arena: &TypeArena, ty: TypeId) -> CTypeLike {
    match arena.get(ty) {
        Type::Ptr(inner) => {
            let inner = match arena.get(*inner) {
                Type::Top | Type::Bottom => CTypeLike::Void,
                _ => structural_type_like(arena, *inner),
            };
            CTypeLike::Pointer(Box::new(inner))
        }
        _ => to_c_type_like(arena, ty),
    }
}

/// Whether a solved type carries no conclusion, at the top level or inside.
///
/// `Top` is "nothing was learned" and `Bottom` is "two things were learned that
/// cannot both hold"; neither is a type, and a pointer to either is not one.
fn type_is_unresolved(arena: &TypeArena, ty: TypeId) -> bool {
    match arena.get(ty) {
        Type::Top | Type::Bottom => true,
        Type::Ptr(inner) => matches!(arena.get(*inner), Type::Bottom),
        _ => false,
    }
}

/// A pointee known only by the width of the accesses made through it.
fn pointee_type_for_width(width: u32) -> Option<CTypeLike> {
    let bits = width.checked_mul(8)?;
    matches!(bits, 8 | 16 | 32 | 64).then(|| {
        CTypeLike::Pointer(Box::new(CTypeLike::Int {
            bits,
            signedness: Signedness::Unknown,
        }))
    })
}

/// The equality classes the solver will build, mirrored so a spelling asserted
/// on one member can name the class it belongs to.
#[derive(Debug, Default)]
struct NodeClasses {
    parent: HashMap<EvidenceNode, EvidenceNode>,
}

impl NodeClasses {
    fn ensure(&mut self, node: EvidenceNode) {
        self.parent.entry(node).or_insert(node);
    }

    fn root(&mut self, node: EvidenceNode) -> EvidenceNode {
        self.ensure(node);
        let mut current = node;
        while let Some(parent) = self.parent.get(&current).copied()
            && parent != current
        {
            current = parent;
        }
        let root = current;
        let mut walk = node;
        while let Some(parent) = self.parent.insert(walk, root)
            && parent != walk
        {
            walk = parent;
        }
        root
    }

    fn union(&mut self, a: EvidenceNode, b: EvidenceNode) {
        let ra = self.root(a);
        let rb = self.root(b);
        if ra != rb {
            self.parent.insert(rb, ra);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pointee_width_maps_to_addressable_integer_widths() {
        assert_eq!(
            pointee_type_for_width(1),
            Some(CTypeLike::Pointer(Box::new(CTypeLike::Int {
                bits: 8,
                signedness: Signedness::Unknown
            })))
        );
        assert_eq!(pointee_type_for_width(3), None);
        assert_eq!(pointee_type_for_width(0), None);
    }

    #[test]
    fn node_classes_merge_transitively() {
        let mut classes = NodeClasses::default();
        let a = EvidenceNode::Value(r2ssa::ValueId(1));
        let b = EvidenceNode::Value(r2ssa::ValueId(2));
        let c = EvidenceNode::Object(r2ssa::ObjectId(3));
        classes.union(a, b);
        classes.union(b, c);
        assert_eq!(classes.root(a), classes.root(c));
    }

    fn empty_artifact() -> r2ssa::SsaArtifact {
        r2ssa::SsaArtifact::raw(
            &[r2il::R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: Vec::new(),
                switch_info: None,
                op_metadata: Default::default(),
            }],
            None,
        )
        .expect("an empty block prepares")
    }

    #[test]
    fn interning_resolves_a_typedef_to_its_structure() {
        let source = empty_artifact();
        let mut builder = EvidenceBuilder::new(&source, 64);
        let size_t = builder
            .intern_structural(&CTypeLike::Typedef("size_t".to_string()))
            .expect("size_t resolves");
        let unsigned_long = builder
            .intern_structural(&CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Unsigned,
            })
            .expect("uint64 resolves");
        assert_eq!(size_t, unsigned_long);
    }

    #[test]
    fn a_void_pointee_interns_as_the_pointee_top() {
        let source = empty_artifact();
        let mut builder = EvidenceBuilder::new(&source, 64);
        let void_ptr = builder
            .intern_structural(&CTypeLike::Pointer(Box::new(CTypeLike::Void)))
            .expect("void* resolves");
        let top = builder.arena.top();
        let expected = builder.arena.ptr(top);
        assert_eq!(void_ptr, expected);
        assert_eq!(
            structural_type_like(&builder.arena, void_ptr),
            CTypeLike::Pointer(Box::new(CTypeLike::Void))
        );
    }

    #[test]
    fn contradictory_bounds_leave_a_value_unresolved() {
        let mut arena = TypeArena::default();
        let byte = arena.int(8, Signedness::Unknown);
        let byte_ptr = arena.ptr(byte);
        let word = arena.int(64, Signedness::Unsigned);
        let node = EvidenceNode::Value(r2ssa::ValueId(1));

        let constraints = [byte_ptr, word]
            .into_iter()
            .map(|ty| Constraint::Subtype {
                var: node,
                ty,
                source: ConstraintSource::SignatureRegistry,
            })
            .collect::<Vec<_>>();
        let solved = TypeSolver::new(SolverConfig::default()).solve(arena, &constraints);
        let solved_ty = solved.var_types.get(&node).copied().expect("node visited");
        assert!(type_is_unresolved(&solved.arena, solved_ty));
    }

    #[test]
    fn a_tighter_bound_survives_a_looser_one_whatever_the_order() {
        let mut arena = TypeArena::default();
        let top = arena.top();
        let void_ptr = arena.ptr(top);
        let byte = arena.int(8, Signedness::Unknown);
        let byte_ptr = arena.ptr(byte);
        let node = EvidenceNode::Value(r2ssa::ValueId(1));

        for order in [[void_ptr, byte_ptr], [byte_ptr, void_ptr]] {
            let constraints = order
                .into_iter()
                .map(|ty| Constraint::Subtype {
                    var: node,
                    ty,
                    source: ConstraintSource::SignatureRegistry,
                })
                .collect::<Vec<_>>();
            let solved =
                TypeSolver::new(SolverConfig::default()).solve(arena.clone(), &constraints);
            let solved_ty = solved.var_types.get(&node).copied().expect("node typed");
            assert_eq!(
                structural_type_like(&solved.arena, solved_ty),
                CTypeLike::Pointer(Box::new(CTypeLike::Int {
                    bits: 8,
                    signedness: Signedness::Unknown
                }))
            );
        }
    }
}
