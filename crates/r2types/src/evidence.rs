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
use crate::oracle::TypeOracle;
use crate::signedness::{ScalarSignednessEvidence, infer_scalar_signedness};
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

/// Exact ValueId-keyed type evidence projected through the retained source.
///
/// `TypeOracle` predates `ValueId`, so its query accepts an `SSAVar`. This
/// adapter resolves that value only through the exact graph's intern table and
/// then reads the canonical evidence result. It never parses or compares a
/// variable spelling and it refuses synthetic/foreign variables as `Top`.
pub struct SourceEvidenceTypeOracle<'a> {
    source: &'a r2ssa::SsaArtifact,
    external_type_db: &'a crate::ExternalTypeDb,
    arena: TypeArena,
    value_types: BTreeMap<r2ssa::ValueId, TypeId>,
    top: TypeId,
}

impl<'a> SourceEvidenceTypeOracle<'a> {
    pub fn new(
        source: &'a r2ssa::SsaArtifact,
        evidence: &EvidenceTypes,
        external_type_db: &'a crate::ExternalTypeDb,
    ) -> Self {
        let mut arena = TypeArena::default();
        let top = arena.top();
        let value_types = evidence
            .value_types
            .iter()
            .map(|(value, ty)| (*value, intern_render_type(&mut arena, ty)))
            .collect();
        Self {
            source,
            external_type_db,
            arena,
            value_types,
            top,
        }
    }

    fn external_struct_for_type(&self, ty: TypeId) -> Option<&crate::ExternalStruct> {
        let named = match self.arena.get(ty) {
            Type::Struct(shape) => shape.name.as_deref(),
            Type::Ptr(inner) => match self.arena.get(*inner) {
                Type::Struct(shape) => shape.name.as_deref(),
                _ => None,
            },
            _ => None,
        }?;
        self.external_type_db
            .structs
            .get(&named.to_ascii_lowercase())
    }
}

fn intern_render_type(arena: &mut TypeArena, ty: &CTypeLike) -> TypeId {
    match ty {
        CTypeLike::Void => arena.unknown_alias("void"),
        CTypeLike::Bool => arena.bool_ty(),
        CTypeLike::Int { bits, signedness } => arena.int(*bits, *signedness),
        CTypeLike::Float(bits) => arena.float(*bits),
        CTypeLike::Pointer(inner) => {
            let inner = intern_render_type(arena, inner);
            arena.ptr(inner)
        }
        CTypeLike::Array(inner, len) => {
            let inner = intern_render_type(arena, inner);
            arena.array(inner, *len, None)
        }
        CTypeLike::Struct(name) | CTypeLike::Typedef(name) => {
            arena.struct_named_or_existing(name.clone())
        }
        CTypeLike::Union(name) | CTypeLike::Enum(name) => arena.unknown_alias(name.clone()),
        CTypeLike::Function { .. } | CTypeLike::BitVector(_) | CTypeLike::Unknown => arena.top(),
    }
}

impl TypeOracle for SourceEvidenceTypeOracle<'_> {
    fn type_of(&self, var: &r2ssa::SSAVar) -> TypeId {
        self.source
            .graph()
            .value_id_for_var(var)
            .and_then(|value| self.value_types.get(&value).copied())
            .unwrap_or(self.top)
    }

    fn struct_shape(&self, ty: TypeId) -> Option<&crate::StructShape> {
        match self.arena.get(ty) {
            Type::Struct(shape) => Some(shape),
            Type::Ptr(inner) => match self.arena.get(*inner) {
                Type::Struct(shape) => Some(shape),
                _ => None,
            },
            _ => None,
        }
    }

    fn is_pointer(&self, ty: TypeId) -> bool {
        matches!(self.arena.get(ty), Type::Ptr(_))
    }

    fn is_array(&self, ty: TypeId) -> bool {
        matches!(self.arena.get(ty), Type::Array { .. })
    }

    fn field_name(&self, ty: TypeId, offset: u64) -> Option<&str> {
        self.struct_shape(ty)
            .and_then(|shape| shape.fields.get(&offset))
            .and_then(|field| field.name.as_deref())
            .or_else(|| {
                self.external_struct_for_type(ty)
                    .and_then(|st| st.fields.get(&offset))
                    .map(|field| field.name.as_str())
            })
    }

    fn field_name_any(&self, offset: u64) -> Option<&str> {
        let mut matched: Option<&str> = None;
        for st in self.external_type_db.structs.values() {
            let Some(field) = st.fields.get(&offset) else {
                continue;
            };
            match matched {
                None => matched = Some(field.name.as_str()),
                Some(existing) if existing == field.name => {}
                Some(_) => return None,
            }
        }
        matched
    }

    fn field_layout(&self, ty: TypeId, offset: u64) -> Option<crate::ResolvedFieldLayout> {
        self.struct_shape(ty)
            .and_then(|shape| {
                let field = shape.fields.get(&offset)?;
                Some(crate::ResolvedFieldLayout::direct(
                    shape.name.clone(),
                    offset,
                    field.name.clone()?,
                ))
            })
            .or_else(|| {
                let st = self.external_struct_for_type(ty)?;
                let field = st.fields.get(&offset)?;
                Some(crate::ResolvedFieldLayout::direct(
                    Some(st.name.clone()),
                    offset,
                    field.name.clone(),
                ))
            })
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
    builder.gather_scalar_signedness();
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
        self.source.graph().value(value).is_some_and(|graph_value| {
            let Some(bits) = graph_value.var.constant_bits() else {
                return false;
            };
            graph_value.canonical_storage.is_some_and(|storage| {
                storage.space == r2ssa::CanonicalStorageSpace::Constant
                    && storage.offset == bits
                    && storage.size == graph_value.var.size
            })
        })
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

    /// Signed and unsigned machine operations type the values they consume.
    ///
    /// The signedness pass already follows transparent same-width operations.
    /// SSA phi/cell identities are constraints in this builder, so a seed on
    /// either side reaches the same solver class without a second alias model.
    /// Conflicting signed and unsigned uses are both asserted: their meet is
    /// `Bottom`, and readback refuses only that value.
    fn gather_scalar_signedness(&mut self) {
        let inferred = infer_scalar_signedness(
            self.source
                .function()
                .blocks()
                .flat_map(|block| block.ops.iter()),
            std::iter::empty(),
            crate::prepare::prepared_arch_display_name(self.source),
        );
        let mut inferred = inferred.into_iter().collect::<Vec<_>>();
        inferred.sort_by(|(left, _), (right, _)| left.cmp(right));

        for (var, evidence) in inferred {
            let Some(value) = self.source.graph().value_id_for_var(&var) else {
                continue;
            };
            let Some(bits) = var.size.checked_mul(8) else {
                continue;
            };
            if !matches!(bits, 8 | 16 | 32 | 64 | 128) {
                continue;
            }
            for evidence in evidence {
                let signedness = match evidence {
                    ScalarSignednessEvidence::Signed => Signedness::Signed,
                    ScalarSignednessEvidence::Unsigned => Signedness::Unsigned,
                };
                let ty = CTypeLike::Int { bits, signedness };
                let Some(spelled) = self.intern_spelled(&ty) else {
                    continue;
                };
                self.bound(
                    EvidenceNode::Value(value),
                    spelled,
                    ConstraintSource::Inferred,
                );
            }
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
                let elem = self.pointee_with_loaded_signedness(access, elem);
                address_bounds.push((EvidenceNode::Value(access.address), elem.clone()));
                if let Some(parameter) = self.provenance_parameter_value(access) {
                    address_bounds.push((EvidenceNode::Value(parameter), elem));
                }
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

    /// The exact formal parameter at the base of one certified RAM address.
    ///
    /// Affine provenance is the owner of base identity across arithmetic and
    /// proven stack spills. Matching its retained storage back to the source
    /// boundary keeps this keyed by `ValueId`; a positional index alone is not
    /// enough to assert a type on a graph value.
    fn provenance_parameter_value(
        &self,
        access: &r2ssa::MemoryAccessCertificate,
    ) -> Option<r2ssa::ValueId> {
        if access.space != r2il::SpaceId::Ram
            || self
                .source
                .machine_context()
                .memory_space_at(access.block_addr, access.op_index)
                != Some(access.space)
        {
            return None;
        }
        let address = self
            .source
            .addresses()
            .parameter_expression(access.address)?;
        let slot = u32::try_from(address.parameter).ok()?;
        let parameter = self.source.facts().boundaries.parameters.get(&slot)?;
        (parameter.index == slot
            && parameter.index as usize == address.parameter
            && address.parameter_storage == Some(parameter.graph_storage))
        .then_some(parameter.value)
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
            CTypeLike::Void
            | CTypeLike::Unknown
            | CTypeLike::BitVector(_)
            | CTypeLike::Function { .. } => None,
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
                let resolved = crate::parse_c_type_like(name, self.ptr_bits)?;
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
impl EvidenceBuilder<'_> {
    /// Refine a pointee's signedness by how the loaded value is widened.
    ///
    /// The access width says how many bits are read and nothing about what
    /// they mean, so a pointee derived from it alone is `Signedness::Unknown`
    /// and spells `int8_t *` -- a signed pointee asserted from not knowing.
    /// The instruction after the load says which it is: the machine widens a
    /// byte it means as unsigned with a zero extension and one it means as
    /// signed with a sign extension, and that is a fact about the pointee
    /// rather than a reading of the C.
    fn pointee_with_loaded_signedness(
        &self,
        access: &r2ssa::MemoryAccessCertificate,
        elem: CTypeLike,
    ) -> CTypeLike {
        let CTypeLike::Pointer(pointee) = &elem else {
            return elem;
        };
        let CTypeLike::Int {
            bits,
            signedness: Signedness::Unknown,
        } = pointee.as_ref()
        else {
            return elem;
        };
        let Some(value) = access.value else {
            return elem;
        };
        let graph = self.source.graph();
        let mut signedness = None;
        for site in graph.use_sites(value) {
            let Some(inst) = graph.inst(site.inst) else {
                return elem;
            };
            let widened = match &inst.payload {
                r2ssa::InstPayload::Op(r2ssa::SSAOp::IntZExt { .. }) => Signedness::Unsigned,
                r2ssa::InstPayload::Op(r2ssa::SSAOp::IntSExt { .. }) => Signedness::Signed,
                _ => continue,
            };
            match signedness {
                None => signedness = Some(widened),
                // Widened both ways, so the bits are not one or the other.
                Some(seen) if seen != widened => return elem,
                Some(_) => {}
            }
        }
        let Some(signedness) = signedness else {
            return elem;
        };
        CTypeLike::Pointer(Box::new(CTypeLike::Int {
            bits: *bits,
            signedness,
        }))
    }
}

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

    #[test]
    fn memory_and_ssa_evidence_solve_without_callee_signatures() {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.add_register(r2il::RegisterDef::new("rdi", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rsp", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 16, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"evidence-without-callee-signatures".to_vec(),
            "sysv64",
            [r2ssa::SourceAbiParameterSpec::new(0, register(0))],
            r2ssa::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(register(8)))
        .and_then(|interface| interface.with_return_address_storage(register(16)))
        .expect("exact source interface");
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::unique(0x100, 8),
            src: r2il::Varnode::register(0, 8),
        });
        block.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::unique(0x200, 4),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x100, 8),
        });
        let source =
            r2ssa::SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
                .expect("prepared source");
        let parameter = source
            .facts()
            .boundaries
            .parameters
            .get(&0)
            .expect("exact parameter")
            .value;
        let address = source
            .certificates()
            .memory_accesses
            .values()
            .next()
            .expect("certified load")
            .address;

        let solved = solve_evidence_types(&source, &BTreeMap::new(), 64);
        let expected = CTypeLike::Pointer(Box::new(CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Unknown,
        }));
        assert_eq!(solved.value_type(address), Some(&expected));
        assert_eq!(
            solved.value_type(parameter),
            Some(&expected),
            "copy identity must carry memory evidence to the exact entry value"
        );
    }

    #[test]
    fn affine_address_provenance_bootstraps_the_indexed_parameter_base() {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.add_register(r2il::RegisterDef::new("rdi", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rsi", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rsp", 16, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 24, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"indexed-parameter-evidence".to_vec(),
            "sysv64",
            [
                r2ssa::SourceAbiParameterSpec::new(0, register(0)),
                r2ssa::SourceAbiParameterSpec::new(1, register(8)),
            ],
            r2ssa::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(register(16)))
        .and_then(|interface| interface.with_return_address_storage(register(24)))
        .expect("exact source interface");
        let mut block = r2il::R2ILBlock::new(0x1000, 4);
        block.push(r2il::R2ILOp::IntMult {
            dst: r2il::Varnode::unique(0x100, 8),
            a: r2il::Varnode::register(8, 8),
            b: r2il::Varnode::constant(4, 8),
        });
        block.push(r2il::R2ILOp::IntAdd {
            dst: r2il::Varnode::unique(0x108, 8),
            a: r2il::Varnode::register(0, 8),
            b: r2il::Varnode::unique(0x100, 8),
        });
        block.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::unique(0x200, 4),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x108, 8),
        });
        let source =
            r2ssa::SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
                .expect("prepared source");
        let parameter = source.facts().boundaries.parameters[&0].value;
        let index = source.facts().boundaries.parameters[&1].value;
        let access = source
            .certificates()
            .memory_accesses
            .values()
            .next()
            .expect("certified indexed load");
        assert_eq!(
            source
                .addresses()
                .parameter_expression(access.address)
                .map(|address| address.parameter),
            Some(0)
        );

        let solved = solve_evidence_types(&source, &BTreeMap::new(), 64);
        let expected = CTypeLike::Pointer(Box::new(CTypeLike::Int {
            bits: 32,
            signedness: Signedness::Unknown,
        }));
        assert_eq!(solved.value_type(parameter), Some(&expected));
        assert_eq!(
            solved.value_type(index),
            None,
            "the affine index is not a second pointer base"
        );
    }

    #[test]
    fn signed_comparison_types_only_its_exact_parameter_value() {
        let mut arch = r2il::ArchSpec::new("x86-64");
        arch.add_register(r2il::RegisterDef::new("rdi", 0, 8));
        arch.add_register(r2il::RegisterDef::new("rsi", 8, 8));
        arch.add_register(r2il::RegisterDef::new("rsp", 16, 8));
        arch.add_register(r2il::RegisterDef::new("rip", 24, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"signed-parameter-evidence".to_vec(),
            "sysv64",
            [
                r2ssa::SourceAbiParameterSpec::new(0, register(0)),
                r2ssa::SourceAbiParameterSpec::new(1, register(8)),
            ],
            r2ssa::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(register(16)))
        .and_then(|interface| interface.with_return_address_storage(register(24)))
        .expect("exact source interface");
        let mut entry = r2il::R2ILBlock::new(0x1000, 4);
        entry.push(r2il::R2ILOp::IntSLess {
            dst: r2il::Varnode::unique(0x100, 1),
            a: r2il::Varnode::register(0, 8),
            b: r2il::Varnode::constant(10, 8),
        });
        entry.push(r2il::R2ILOp::IntEqual {
            dst: r2il::Varnode::unique(0x108, 1),
            a: r2il::Varnode::register(8, 8),
            b: r2il::Varnode::constant(0, 8),
        });
        entry.push(r2il::R2ILOp::BoolAnd {
            dst: r2il::Varnode::unique(0x110, 1),
            a: r2il::Varnode::unique(0x100, 1),
            b: r2il::Varnode::unique(0x108, 1),
        });
        entry.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x1008, 8),
            cond: r2il::Varnode::unique(0x110, 1),
        });
        let fallthrough = r2il::R2ILBlock::new(0x1004, 4);
        let taken = r2il::R2ILBlock::new(0x1008, 4);
        let source = r2ssa::SsaArtifact::for_decompile_with_interface(
            &[entry, fallthrough, taken],
            Some(&arch),
            interface,
        )
        .expect("prepared source");
        let signed = source.facts().boundaries.parameters[&0].value;
        let untouched = source.facts().boundaries.parameters[&1].value;

        let solved = solve_evidence_types(&source, &BTreeMap::new(), 64);
        assert_eq!(
            solved.value_type(signed),
            Some(&CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            })
        );
        assert_eq!(solved.value_type(untouched), None);

        let machine = CTypeLike::u64();
        let signature = crate::FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Void),
            params: vec![
                crate::FunctionParamSpec {
                    name: "lhs".to_string(),
                    ty: Some(machine.clone()),
                },
                crate::FunctionParamSpec {
                    name: "rhs".to_string(),
                    ty: Some(machine.clone()),
                },
            ],
        };
        let mut facts = crate::FunctionFacts::new(
            crate::FunctionTypeFacts {
                signature_certificate: crate::SignatureCertificate::from_signature(
                    &signature,
                    [crate::SignatureCertificateSource::LocalInference],
                ),
                merged_signature: Some(signature),
                ..crate::FunctionTypeFacts::default()
            },
            None,
        );
        facts.apply_recovered_evidence_types(&source, 64);
        let written = facts
            .type_facts()
            .render_authorized_signature()
            .expect("recovered parameter signature remains render-authorized");
        assert_eq!(
            written.params[0].ty,
            Some(CTypeLike::Int {
                bits: 64,
                signedness: Signedness::Signed,
            })
        );
        assert_eq!(written.params[1].ty, Some(machine));
    }

    #[test]
    fn unsigned_use_after_a_stack_spill_types_the_parameter_and_home() {
        let mut arch = r2il::ArchSpec::new("aarch64");
        arch.add_register(r2il::RegisterDef::new("x1", 8, 8));
        arch.add_register(r2il::RegisterDef::new("sp", 16, 8));
        arch.add_register(r2il::RegisterDef::new("lr", 24, 8));
        let register = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"unsigned-spilled-parameter".to_vec(),
            "aapcs64",
            [r2ssa::SourceAbiParameterSpec::new(0, register(8))],
            r2ssa::SourceFunctionReturn::Void,
            [r2ssa::SourceStackSlotSpec::new_local(
                r2ssa::StackAddressBase::StackPointer,
                register(16),
                -8,
                8,
            )],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(register(16)))
        .and_then(|interface| interface.with_return_address_storage(register(24)))
        .expect("exact source interface");

        let mut entry = r2il::R2ILBlock::new(0x1000, 4);
        entry.push(r2il::R2ILOp::IntSub {
            dst: r2il::Varnode::unique(0x100, 8),
            a: r2il::Varnode::register(16, 8),
            b: r2il::Varnode::constant(8, 8),
        });
        entry.push(r2il::R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x100, 8),
            val: r2il::Varnode::register(8, 8),
        });
        entry.push(r2il::R2ILOp::Load {
            dst: r2il::Varnode::unique(0x108, 8),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::unique(0x100, 8),
        });
        entry.push(r2il::R2ILOp::IntLess {
            dst: r2il::Varnode::unique(0x110, 1),
            a: r2il::Varnode::unique(0x108, 8),
            b: r2il::Varnode::constant(10, 8),
        });
        entry.push(r2il::R2ILOp::CBranch {
            target: r2il::Varnode::constant(0x1008, 8),
            cond: r2il::Varnode::unique(0x110, 1),
        });
        let fallthrough = r2il::R2ILBlock::new(0x1004, 4);
        let taken = r2il::R2ILBlock::new(0x1008, 4);
        let source = r2ssa::SsaArtifact::for_decompile_with_interface(
            &[entry, fallthrough, taken],
            Some(&arch),
            interface,
        )
        .expect("prepared source");
        let parameter = source.facts().boundaries.parameters[&0].value;
        let solved = solve_evidence_types(&source, &BTreeMap::new(), 64);
        let unsigned = CTypeLike::Int {
            bits: 64,
            signedness: Signedness::Unsigned,
        };

        assert_eq!(solved.value_type(parameter), Some(&unsigned));
        assert_eq!(
            solved
                .stack_slot_types()
                .find(|(slot, _)| slot.offset == -8)
                .map(|(_, ty)| ty),
            Some(&unsigned),
            "one scalar memory cell must carry the use-proven type both ways"
        );

        let signed = CTypeLike::Typedef("int64_t".to_string());
        let signature = crate::FunctionSignatureSpec {
            ret_type: Some(CTypeLike::Void),
            params: vec![crate::FunctionParamSpec {
                name: "length".to_string(),
                ty: Some(signed.clone()),
            }],
        };
        let slot = StackSlotKey {
            base: ExternalStackBase::StackPointer,
            offset: -8,
        };
        let mut facts = crate::FunctionFacts::new(
            crate::FunctionTypeFacts {
                signature_certificate: crate::SignatureCertificate::from_signature(
                    &signature,
                    [crate::SignatureCertificateSource::LocalInference],
                ),
                merged_signature: Some(signature),
                stack_slots: BTreeMap::from([(
                    slot,
                    crate::ExternalStackSlotSpec {
                        name: "length_home".to_string(),
                        ty: Some(signed.clone()),
                        role: crate::ExternalStackSlotRole::Local,
                        ..crate::ExternalStackSlotSpec::default()
                    },
                )]),
                visible_bindings: vec![crate::VisibleBinding {
                    name: "length_home".to_string(),
                    ty: Some(signed),
                    kind: crate::VisibleBindingKind::StackObject,
                    stack_slot: Some(slot),
                    param_index: None,
                    source_reg: None,
                }],
                ..crate::FunctionTypeFacts::default()
            },
            None,
        );
        facts.apply_recovered_evidence_types(&source, 64);

        let type_facts = facts.type_facts();
        assert_eq!(
            type_facts
                .merged_signature
                .as_ref()
                .and_then(|signature| signature.params[0].ty.as_ref()),
            Some(&unsigned)
        );
        assert_eq!(
            type_facts
                .stack_slots
                .get(&slot)
                .and_then(|slot| slot.ty.as_ref()),
            Some(&unsigned)
        );
        assert_eq!(type_facts.visible_bindings[0].ty.as_ref(), Some(&unsigned));
    }
}
