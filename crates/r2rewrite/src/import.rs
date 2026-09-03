//! Import of the base machine arena into terms.
//!
//! Every value-producing instruction has one root in the base arena, and that
//! root reads its operands as `Source` leaves: the base arena is one node deep
//! per instruction. A rule that wants to see `(a - b) == 0` therefore has to
//! see through the leaf that names `a - b`. The importer does that once. A
//! leaf is replaced by its producer's term when the producer is modelled and
//! its dispositions are exact -- import establishes that -- and the
//! [`ExpansionPolicy`] says the reader may absorb it; the default policy is
//! [`default_expansion_policy`], one named function so that the binding plan,
//! which asks a neighbouring question, can share or replace it rather than
//! state it a second time. Which producers were expanded is recorded, because
//! rendering the resulting term renders those instructions here, and the
//! accounting has to know.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use r2ssa::{
    CanonicalInstructionId, InductionStep, InstId, MachineArithmeticMode, MachineBitVector,
    MachineCastKind, MachineExprId, MachineExprKind, MachineOvershiftBehavior, MachineProjection,
    MachineSignedness, MachineType, MachineUseDisposition, MachineWriteDisposition, ObjectId,
    ObjectKind, SsaArtifact, StackAddressRoot, StructuredAccessId, UseSite, ValueId,
};

use crate::driver::Rewrite;
use crate::term::{MAX_TERM_WIDTH_BITS, ObjectPlacement, PointerWalk, TermArena, TermId, TermKind};

/// Rule id recorded for a `Copy` root elided at import.
pub const COPY_ELIDE: &str = "copy.elide";

#[derive(Debug, Clone)]
pub struct ImportedValue {
    pub value: ValueId,
    pub base_root: MachineExprId,
    pub producer: CanonicalInstructionId,
    /// The value's own instruction as a term, with expanded producers inside.
    pub term: TermId,
    /// Copy elisions performed while building `term`, in application order.
    pub trace: Vec<Rewrite>,
    /// Producers expanded into `term`, transitively. Rendering `term` renders
    /// these instructions at this value's site.
    pub substituted: BTreeSet<CanonicalInstructionId>,
}

/// The cell one structured memory access reads or writes, as a term.
///
/// A load's cell is its value's own term. A store has no value, so its cell
/// is imported from the typed address leaf the projection interns for it:
/// the `Load` that would read the cell back, which the subscript rules
/// rewrite exactly as they rewrite a read.
#[derive(Debug, Clone)]
pub struct ImportedAccess {
    pub access: StructuredAccessId,
    pub term: TermId,
    pub trace: Vec<Rewrite>,
    pub substituted: BTreeSet<CanonicalInstructionId>,
}

#[derive(Debug, Clone, Default)]
pub struct Import {
    values: Vec<Option<ImportedValue>>,
    accesses: BTreeMap<StructuredAccessId, ImportedAccess>,
    /// Entry values whose storage no instruction of the function writes.
    entry_never_redefined: BTreeSet<ValueId>,
}

impl Import {
    pub fn value(&self, value: ValueId) -> Option<&ImportedValue> {
        self.values.get(value.0 as usize)?.as_ref()
    }

    pub fn values(&self) -> impl Iterator<Item = &ImportedValue> {
        self.values.iter().flatten()
    }

    pub fn access(&self, access: StructuredAccessId) -> Option<&ImportedAccess> {
        self.accesses.get(&access)
    }

    pub fn accesses(&self) -> impl Iterator<Item = &ImportedAccess> {
        self.accesses.values()
    }

    pub fn entry_never_redefined(&self) -> &BTreeSet<ValueId> {
        &self.entry_never_redefined
    }

    /// Whether every read `term` makes is of a literal or of an entry value
    /// the function never redefines, so the term can be rendered at any
    /// number of sites without observing anything twice.
    pub fn is_duplicable(
        &self,
        projection: &MachineProjection,
        arena: &TermArena,
        term: TermId,
    ) -> bool {
        term_is_duplicable(projection, arena, &self.entry_never_redefined, term)
    }
}

/// What the expansion policy is asked about: one read of `value` inside a
/// reader's term, with the producer's own imported term already built.
pub struct ExpansionQuery<'a> {
    pub artifact: &'a SsaArtifact,
    pub projection: &'a MachineProjection,
    pub arena: &'a TermArena,
    /// The value being read.
    pub value: ValueId,
    /// The producer's term, not opaque, with exact write and read
    /// dispositions -- import has already established that, so the policy
    /// answers only whether this reader may absorb it.
    pub producer_term: TermId,
    /// Entry values whose storage no instruction of the function writes.
    pub entry_never_redefined: &'a BTreeSet<ValueId>,
}

/// Whether a read of a value may be replaced by its producer's term inside
/// the reader's term.
///
/// This answers "may this producer's term be expanded into its reader". It is
/// a neighbour of the binding plan's question, "may this value be rendered
/// without a local", and the two coincide today: a value with one reader is
/// expanded here and inlined there, and a term over literals and never
/// redefined entry values is expanded at every reader here and would need
/// [`crate::Multiplicity::Any`] there. It is one named function so that
/// integration can pass the plan's rule in place of this one, or adopt this
/// one, and either way there is one place the answer lives.
pub type ExpansionPolicy<'p> = dyn Fn(&ExpansionQuery<'_>) -> bool + 'p;

/// The default policy: the value has exactly one reader, or the producer's
/// term reads nothing but literals and entry values the function never
/// redefines, so rendering it at every reader computes the same value each
/// time and observes nothing twice.
pub fn default_expansion_policy(query: &ExpansionQuery<'_>) -> bool {
    let single_reader = query.artifact.graph().use_sites(query.value).len() == 1;
    single_reader
        || term_is_duplicable(
            query.projection,
            query.arena,
            query.entry_never_redefined,
            query.producer_term,
        )
}

/// Whether every read `term` makes is of a literal or of an entry value the
/// function never redefines, the term is not opaque, and it reads no memory
/// -- a cell read twice is observed twice, and nothing here proves the two
/// reads see the same store.
pub fn term_is_duplicable(
    projection: &MachineProjection,
    arena: &TermArena,
    entry_never_redefined: &BTreeSet<ValueId>,
    term: TermId,
) -> bool {
    !matches!(arena.term(term).kind, TermKind::Opaque(_))
        && !arena.reads_memory(term)
        && arena
            .leaves(term)
            .into_iter()
            .all(|leaf| leaf_is_duplicable(projection, entry_never_redefined, leaf))
}

/// Whether one base-arena leaf may be read at any number of sites.
///
/// The single statement of the rule. A literal is the same at every site by
/// definition, and an entry value the function never writes is the same at
/// every site because nothing between the sites can change it. Everything else
/// is read once.
fn leaf_is_duplicable(
    projection: &MachineProjection,
    entry_never_redefined: &BTreeSet<ValueId>,
    leaf: MachineExprId,
) -> bool {
    match projection.expr(leaf).map(|expr| expr.kind()) {
        Some(MachineExprKind::Constant { .. }) => true,
        Some(MachineExprKind::Source { binding, .. }) => {
            entry_never_redefined.contains(&binding.value())
        }
        _ => false,
    }
}

/// Whether a base-arena expression reads nothing but literals.
///
/// A neighbour of [`term_is_duplicable`] and deliberately stricter, because it
/// answers a different question. That one asks whether rendering a term twice
/// would observe anything twice, which an entry value the function never
/// writes also satisfies. This one asks whether a value is cheap enough that a
/// reader should spell it instead of naming it, and only a literal is: an
/// expression over two parameters observes nothing twice either, and copying
/// it to three readers is three copies of a real computation rather than a
/// local removed.
pub fn machine_expr_is_literal(projection: &MachineProjection, root: MachineExprId) -> bool {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        let Some(expr) = projection.expr(node) else {
            return false;
        };
        let children = expr.kind().children();
        if children.is_empty() {
            if !matches!(expr.kind(), MachineExprKind::Constant { .. }) {
                return false;
            }
        } else {
            pending.extend(children);
        }
    }
    true
}

/// Entry values whose storage no instruction of the function writes.
fn entry_values_never_redefined(graph: &r2ssa::SsaGraph) -> BTreeSet<ValueId> {
    let mut rewritten_locations = BTreeSet::new();
    for inst in &graph.insts {
        if let Some(storage) = inst
            .output
            .and_then(|output| graph.value(output))
            .and_then(|value| value.canonical_storage)
        {
            rewritten_locations.insert(storage.location());
        }
    }
    graph
        .values
        .iter()
        .filter(|value| graph.def_inst(value.id).is_none())
        .filter(|value| {
            value
                .canonical_storage
                .is_some_and(|storage| !rewritten_locations.contains(&storage.location()))
        })
        .map(|value| value.id)
        .collect()
}

#[derive(Debug, Clone)]
struct RootImport {
    term: TermId,
    trace: Vec<Rewrite>,
    substituted: BTreeSet<CanonicalInstructionId>,
    opaque: bool,
}

struct Importer<'a> {
    artifact: &'a SsaArtifact,
    projection: &'a MachineProjection,
    arena: &'a mut TermArena,
    policy: &'a ExpansionPolicy<'a>,
    roots: HashMap<MachineExprId, RootImport>,
    in_progress: HashSet<MachineExprId>,
    entry_never_redefined: BTreeSet<ValueId>,
    /// Values the machine arena types as an address at some use.
    address_typed: BTreeSet<ValueId>,
    /// Parameters some address reaches memory through, so a pointer rather
    /// than an integer that happens to be a parameter.
    pointer_parameters: BTreeSet<usize>,
    /// One integer-typed source node per value the arena reads, so a
    /// certificate that names a value can be stated over a leaf.
    source_nodes: BTreeMap<ValueId, MachineExprId>,
    /// Walk certificates derived so far; `None` records a value asked about
    /// and found not to walk, and a value being asked about, so that a
    /// counter that is somehow its own pointer does not recurse.
    walks: BTreeMap<ValueId, Option<PointerWalk>>,
}

/// Import under [`default_expansion_policy`].
pub fn import(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    arena: &mut TermArena,
) -> Import {
    import_with(artifact, projection, arena, &default_expansion_policy)
}

/// Import, asking `policy` whether each read may absorb its producer's term.
pub fn import_with(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    arena: &mut TermArena,
    policy: &ExpansionPolicy<'_>,
) -> Import {
    let graph = artifact.graph();
    let entry_never_redefined = entry_values_never_redefined(graph);
    let mut address_typed = BTreeSet::new();
    let mut source_nodes = BTreeMap::new();
    for (id, expr) in projection.arena().iter() {
        let MachineExprKind::Source { binding, .. } = expr.kind() else {
            continue;
        };
        match expr.ty() {
            MachineType::Address { .. } => {
                address_typed.insert(binding.value());
            }
            MachineType::Integer { .. } => {
                source_nodes.entry(binding.value()).or_insert(id);
            }
            MachineType::Bool { .. } => {}
        }
    }
    // A parameter is a pointer because some certified access reads or writes
    // through an address derived from it. Being a parameter proves nothing on
    // its own: `arr_sum(const uint32_t *a, size_t n)` has parameter address
    // provenance for `n` as well as for `a`, and calling both pointers leaves
    // every one-byte access with two candidate bases and no way to choose.
    // Neither does having an object: one is made for every parameter that
    // appears in any address expression, `n` included.
    let pointer_parameters = artifact
        .structured()
        .memory_accesses
        .values()
        .filter_map(|access| artifact.addresses().parameter_expression(access.address))
        .map(|expression| expression.parameter)
        .collect();
    let mut importer = Importer {
        artifact,
        projection,
        arena,
        policy,
        roots: HashMap::new(),
        in_progress: HashSet::new(),
        entry_never_redefined,
        address_typed,
        pointer_parameters,
        source_nodes,
        walks: BTreeMap::new(),
    };
    let mut values: Vec<Option<ImportedValue>> = vec![None; graph.values.len()];
    let mut accesses = BTreeMap::new();
    for entity in projection.entities() {
        let value = entity.output().value();
        let Some(inst) = graph.def_inst(value) else {
            continue;
        };
        let root = importer.import_root(entity.root(), inst);
        if let Some(MachineExprKind::MemoryRead { access, .. }) =
            projection.expr(entity.root()).map(|expr| expr.kind())
        {
            accesses.insert(
                *access,
                ImportedAccess {
                    access: *access,
                    term: root.term,
                    trace: root.trace.clone(),
                    substituted: root.substituted.clone(),
                },
            );
        }
        if let Some(cell) = values.get_mut(value.0 as usize) {
            *cell = Some(ImportedValue {
                value,
                base_root: entity.root(),
                producer: entity.producer(),
                term: root.term,
                trace: root.trace,
                substituted: root.substituted,
            });
        }
    }
    for (access, fact) in &artifact.structured().memory_accesses {
        if !fact.is_write {
            continue;
        }
        if let Some(imported) = importer.import_store_cell(*access, fact) {
            accesses.insert(*access, imported);
        }
    }
    Import {
        values,
        accesses,
        entry_never_redefined: importer.entry_never_redefined,
    }
}

impl Importer<'_> {
    fn import_root(&mut self, root: MachineExprId, inst: InstId) -> RootImport {
        if let Some(done) = self.roots.get(&root) {
            return done.clone();
        }
        let ty = self
            .projection
            .expr(root)
            .map(|expr| *expr.ty())
            .expect("entity root is in the arena");
        let opaque_term = |arena: &mut TermArena| RootImport {
            term: arena.intern(ty, TermKind::Opaque(root)),
            trace: Vec::new(),
            substituted: BTreeSet::new(),
            opaque: true,
        };
        if !self.in_progress.insert(root) {
            // A root reached through its own operands: a call's definition
            // reads the location it defines. Not a term.
            return opaque_term(self.arena);
        }
        let done = if self.dispositions_exact(inst) {
            let kind = self
                .projection
                .expr(root)
                .map(|expr| expr.kind().clone())
                .expect("entity root is in the arena");
            match kind {
                MachineExprKind::Copy { input } => match self.import_expr(input) {
                    Some((term, mut trace, substituted)) => {
                        let from = self.arena.intern(ty, TermKind::Opaque(root));
                        trace.push(Rewrite {
                            rule: COPY_ELIDE,
                            from,
                            to: term,
                        });
                        RootImport {
                            term,
                            trace,
                            substituted,
                            opaque: false,
                        }
                    }
                    None => opaque_term(self.arena),
                },
                _ => match self.import_expr(root) {
                    Some((term, trace, substituted)) => RootImport {
                        term,
                        trace,
                        substituted,
                        opaque: false,
                    },
                    None => opaque_term(self.arena),
                },
            }
        } else {
            opaque_term(self.arena)
        };
        self.in_progress.remove(&root);
        self.roots.insert(root, done.clone());
        done
    }

    /// Whether the plan could render this instruction at all: its write and
    /// every one of its reads have an exact projection. A refused
    /// disposition is a value the renderer refuses, and moving it into an
    /// expression would turn a decline into a generation failure.
    fn dispositions_exact(&self, inst: InstId) -> bool {
        let graph = self.artifact.graph();
        let Some(graph_inst) = graph.inst(inst) else {
            return false;
        };
        if !matches!(
            self.projection.write_disposition(inst),
            Some(MachineWriteDisposition::Exact(_))
        ) {
            return false;
        }
        (0..graph_inst.inputs.len()).all(|input_idx| {
            matches!(
                self.projection.use_disposition(UseSite { inst, input_idx }),
                Some(MachineUseDisposition::Exact(_) | MachineUseDisposition::MemoryAddress(_))
            )
        })
    }

    #[allow(clippy::type_complexity)]
    fn import_expr(
        &mut self,
        id: MachineExprId,
    ) -> Option<(TermId, Vec<Rewrite>, BTreeSet<CanonicalInstructionId>)> {
        let expr = self.projection.expr(id)?;
        let ty = *expr.ty();
        let width = ty.width_bits();
        if width == 0 || width > MAX_TERM_WIDTH_BITS {
            return None;
        }
        let kind = expr.kind().clone();
        let leaf = |arena: &mut TermArena| {
            Some((
                arena.intern(ty, TermKind::Leaf(id)),
                Vec::new(),
                BTreeSet::new(),
            ))
        };
        match kind {
            MachineExprKind::Source { binding, .. } => match self.try_substitute(binding.value()) {
                Some(substituted) => Some(substituted),
                None => {
                    let leaf = leaf(self.arena);
                    if let Some((leaf_id, _, _)) = &leaf {
                        if let Some(definition) = self.definition_of(binding.value()) {
                            self.arena.define(*leaf_id, definition);
                        }
                        self.declare_leaf_facts(*leaf_id, binding.value());
                    }
                    leaf
                }
            },
            MachineExprKind::Constant { value, .. } => {
                match MachineBitVector::new(value.width_bits(), value.bits()) {
                    Some(bits) if value.width_bits() == width => Some((
                        self.arena.intern(ty, TermKind::Literal(bits)),
                        Vec::new(),
                        BTreeSet::new(),
                    )),
                    _ => leaf(self.arena),
                }
            }
            MachineExprKind::Copy { input } => self.import_expr(input),
            MachineExprKind::MemoryRead {
                object,
                address,
                width_bits,
                ..
            } => {
                if width_bits != width {
                    return None;
                }
                let (a, trace, substituted) = self.import_expr(address)?;
                self.place_object(object);
                Some((
                    self.arena.intern(ty, TermKind::Load { object, address: a }),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Phi { .. }
            | MachineExprKind::PopulationCount { .. }
            | MachineExprKind::UnsignedDivide { .. }
            | MachineExprKind::UnsignedRemainder { .. } => None,
            MachineExprKind::Arithmetic {
                op,
                mode,
                left,
                right,
            } => {
                if mode != MachineArithmeticMode::Wrapping {
                    return None;
                }
                let (l, r, trace, substituted) = self.import_pair(left, right)?;
                if self.width_of(l) != width || self.width_of(r) != width {
                    return None;
                }
                Some((
                    self.arena.intern(
                        ty,
                        TermKind::Arithmetic {
                            op,
                            left: l,
                            right: r,
                        },
                    ),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Negate { mode, input } => {
                if mode != MachineArithmeticMode::Wrapping {
                    return None;
                }
                let (x, trace, substituted) = self.import_expr(input)?;
                if self.width_of(x) != width {
                    return None;
                }
                Some((
                    self.arena.intern(ty, TermKind::Negate(x)),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::ArithmeticFlag { op, left, right } => {
                let (l, r, trace, substituted) = self.import_pair(left, right)?;
                if self.width_of(l) != self.width_of(r) {
                    return None;
                }
                Some((
                    self.arena.intern(
                        ty,
                        TermKind::Flag {
                            op,
                            left: l,
                            right: r,
                        },
                    ),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Bitwise { op, left, right } => {
                let (l, r, trace, substituted) = self.import_pair(left, right)?;
                if self.width_of(l) != width || self.width_of(r) != width {
                    return None;
                }
                Some((
                    self.arena.intern(
                        ty,
                        TermKind::Bitwise {
                            op,
                            left: l,
                            right: r,
                        },
                    ),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::BitwiseNot { input } => {
                let (x, trace, substituted) = self.import_expr(input)?;
                if self.width_of(x) != width {
                    return None;
                }
                Some((
                    self.arena.intern(ty, TermKind::BitwiseNot(x)),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::BooleanNot { input } => {
                let (x, trace, substituted) = self.import_expr(input)?;
                if self.width_of(x) != width {
                    return None;
                }
                Some((
                    self.arena.intern(ty, TermKind::BooleanNot(x)),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Boolean { op, left, right } => {
                let (l, r, trace, substituted) = self.import_pair(left, right)?;
                if self.width_of(l) != width || self.width_of(r) != width {
                    return None;
                }
                Some((
                    self.arena.intern(
                        ty,
                        TermKind::Boolean {
                            op,
                            left: l,
                            right: r,
                        },
                    ),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Shift {
                kind,
                overshift,
                value,
                count,
            } => {
                if !matches!(
                    overshift,
                    MachineOvershiftBehavior::Zero | MachineOvershiftBehavior::SignFill
                ) {
                    return None;
                }
                let (v, c, trace, substituted) = self.import_pair(value, count)?;
                if self.width_of(v) != width {
                    return None;
                }
                Some((
                    self.arena.intern(
                        ty,
                        TermKind::Shift {
                            kind,
                            overshift,
                            value: v,
                            count: c,
                        },
                    ),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Compare {
                op,
                interpretation,
                left,
                right,
            } => {
                let (l, r, trace, substituted) = self.import_pair(left, right)?;
                if self.width_of(l) != self.width_of(r) {
                    return None;
                }
                Some((
                    self.arena.intern(
                        ty,
                        TermKind::Compare {
                            op,
                            interpretation,
                            left: l,
                            right: r,
                        },
                    ),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Cast { kind, input } => {
                let (x, trace, substituted) = self.import_expr(input)?;
                let from = self.width_of(x);
                let valid = match kind {
                    MachineCastKind::ZeroExtend | MachineCastKind::SignExtend => from < width,
                    MachineCastKind::Truncate => from > width,
                    MachineCastKind::BitReinterpret => from == width,
                    MachineCastKind::IntegerToAddress | MachineCastKind::AddressToInteger => false,
                };
                if !valid {
                    return None;
                }
                Some((
                    self.arena.intern(ty, TermKind::Cast { kind, input: x }),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Extract { input, lsb_bits } => {
                let (x, trace, substituted) = self.import_expr(input)?;
                let from = self.width_of(x);
                if lsb_bits.checked_add(width).is_none_or(|end| end > from) {
                    return None;
                }
                Some((
                    self.arena
                        .intern(ty, TermKind::Extract { input: x, lsb_bits }),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Concat { high, low } => {
                let (h, l, trace, substituted) = self.import_pair(high, low)?;
                if self.width_of(h).checked_add(self.width_of(l)) != Some(width) {
                    return None;
                }
                Some((
                    self.arena.intern(ty, TermKind::Concat { high: h, low: l }),
                    trace,
                    substituted,
                ))
            }
            MachineExprKind::Select {
                condition,
                if_true,
                if_false,
            } => {
                let (c, mut trace, mut substituted) = self.import_expr(condition)?;
                let (t, trace_t, substituted_t) = self.import_expr(if_true)?;
                let (f, trace_f, substituted_f) = self.import_expr(if_false)?;
                if self.width_of(t) != width || self.width_of(f) != width {
                    return None;
                }
                trace.extend(trace_t);
                trace.extend(trace_f);
                substituted.extend(substituted_t);
                substituted.extend(substituted_f);
                Some((
                    self.arena.intern(
                        ty,
                        TermKind::Select {
                            condition: c,
                            if_true: t,
                            if_false: f,
                        },
                    ),
                    trace,
                    substituted,
                ))
            }
        }
    }

    #[allow(clippy::type_complexity)]
    fn import_pair(
        &mut self,
        left: MachineExprId,
        right: MachineExprId,
    ) -> Option<(
        TermId,
        TermId,
        Vec<Rewrite>,
        BTreeSet<CanonicalInstructionId>,
    )> {
        let (l, mut trace, mut substituted) = self.import_expr(left)?;
        let (r, trace_r, substituted_r) = self.import_expr(right)?;
        trace.extend(trace_r);
        substituted.extend(substituted_r);
        Some((l, r, trace, substituted))
    }

    fn width_of(&self, id: TermId) -> u32 {
        self.arena.term(id).width_bits()
    }

    /// The cell a store writes, as the load that would read it back.
    fn import_store_cell(
        &mut self,
        access: StructuredAccessId,
        fact: &r2ssa::StructuredMemoryAccessFact,
    ) -> Option<ImportedAccess> {
        let node = self.projection.store_address(access)?;
        let site = UseSite {
            inst: access.inst,
            input_idx: 0,
        };
        if !matches!(
            self.projection.use_disposition(site),
            Some(MachineUseDisposition::MemoryAddress(_))
        ) {
            return None;
        }
        let width_bits = fact.width.checked_mul(8)?;
        if width_bits == 0 || width_bits > MAX_TERM_WIDTH_BITS {
            return None;
        }
        let (address, trace, substituted) = self.import_expr(node)?;
        self.place_object(fact.object);
        let ty = MachineType::Integer {
            width_bits,
            signedness: MachineSignedness::Unsigned,
        };
        let term = self.arena.intern(
            ty,
            TermKind::Load {
                object: fact.object,
                address,
            },
        );
        Some(ImportedAccess {
            access,
            term,
            trace,
            substituted,
        })
    }

    /// Record where the object a load reaches is placed, when it is.
    fn place_object(&mut self, object: ObjectId) {
        let Some(fact) = self.artifact.objects().object(object) else {
            return;
        };
        let placement = match fact.kind {
            ObjectKind::StackSlot { base, offset, .. }
            | ObjectKind::FrameObject { base, offset, .. } => {
                ObjectPlacement::Stack(StackAddressRoot { base, offset })
            }
            ObjectKind::Global { address, .. } => ObjectPlacement::Global(address),
            ObjectKind::Parameter { .. }
            | ObjectKind::HeapAlloc { .. }
            | ObjectKind::EscapedUnknown { .. } => return,
        };
        self.arena.place_object(object, placement);
    }

    /// Everything the certificates say about the value a leaf reads, put on
    /// the leaf, because a rule sees the leaf and not the value.
    fn declare_leaf_facts(&mut self, leaf: TermId, value: ValueId) {
        if self.value_is_pointer(value) {
            self.arena.declare_pointer(leaf);
        }
        if let Some(root) = self.stack_root_of(value) {
            self.arena.declare_stack_root(leaf, root);
        }
        if let Some(walk) = self.walk_of(value) {
            self.arena.declare_walk(leaf, walk);
        }
    }

    /// Whether the certificates prove this value is a pointer.
    ///
    /// Two proofs, and each is a use rather than a declaration. The machine
    /// arena types a value as an address exactly where a certified access
    /// reads or writes through it. And the address provenance pass propagates
    /// a parameter base through arithmetic and proven stack spills, so a
    /// value that is a pointer parameter with no index added to it is that
    /// pointer however many stack homes it passed through -- which is what a
    /// `-O0` build does to every parameter before its first use.
    ///
    /// A value with terms added is a pointer too, and is not a *base*: it is
    /// the whole address, and an address that is its own base leaves no index.
    fn value_is_pointer(&self, value: ValueId) -> bool {
        if self.address_typed.contains(&value) {
            return true;
        }
        self.artifact
            .addresses()
            .parameter_expression(value)
            .is_some_and(|expression| {
                expression.terms.is_empty()
                    && self.pointer_parameters.contains(&expression.parameter)
            })
    }

    /// The frame position `value` holds, through the copies that carried it.
    fn stack_root_of(&self, value: ValueId) -> Option<StackAddressRoot> {
        let facts = self.artifact.function().decompile_prep_facts()?;
        let var = &self.artifact.graph().value(value)?.var;
        if let Some(root) = facts.stack_address_root_of(var) {
            return Some(*root);
        }
        let mut current = var;
        for _ in 0..32 {
            let Some(next) = facts.canonical_root_of(current) else {
                break;
            };
            if next == current {
                break;
            }
            current = next;
        }
        facts.stack_address_root_of(current).copied()
    }

    /// The walk certificate of `value`, if it is a pointer carried round a
    /// loop beside a unit counter that starts at zero.
    ///
    /// The pointer's induction fact says it advances by a constant on the
    /// one latch; the counter's says it advances by one on the same latch
    /// from the same header; and the counter starts at zero, so at the header
    /// the pointer is its entry value plus the counter times the stride.
    /// Where several counters qualify the lowest value is the one, so the
    /// answer does not depend on iteration order. A pointer with no counter
    /// beside it has no walk: an index is never invented.
    fn walk_of(&mut self, value: ValueId) -> Option<PointerWalk> {
        if let Some(known) = self.walks.get(&value) {
            return *known;
        }
        self.walks.insert(value, None);
        let derived = self.derive_walk(value);
        self.walks.insert(value, derived);
        derived
    }

    fn derive_walk(&mut self, value: ValueId) -> Option<PointerWalk> {
        let inductions = &self.artifact.structured().inductions;
        let fact = inductions.get(&value)?;
        let InductionStep::AddConst(stride) = fact.step else {
            return None;
        };
        if stride == 0 {
            return None;
        }
        if !self.value_is_pointer(fact.init) {
            return None;
        }
        let graph = self.artifact.graph();
        let starts_at_zero = |init: ValueId| {
            graph
                .value(init)
                .is_some_and(|value| value.var.constant_bits() == Some(0))
        };
        let counter = inductions
            .values()
            .filter(|counter| {
                counter.phi != value
                    && counter.loop_id == fact.loop_id
                    && counter.header == fact.header
                    && counter.latch == fact.latch
                    && counter.width_bits == fact.width_bits
                    && counter.step == InductionStep::AddConst(1)
                    && starts_at_zero(counter.init)
            })
            .map(|counter| counter.phi)
            .min()?;
        let (init, counter_value) = (fact.init, counter);
        let width_bits = fact.width_bits;
        let init = self.leaf_for_value(init, width_bits)?;
        let counter = self.leaf_for_value(counter_value, width_bits)?;
        Some(PointerWalk {
            init,
            counter,
            stride,
        })
    }

    /// A leaf reading `value` by name, with its facts, for a certificate to
    /// be stated over.
    fn leaf_for_value(&mut self, value: ValueId, width_bits: u32) -> Option<TermId> {
        let node = *self.source_nodes.get(&value)?;
        let ty = *self.projection.expr(node)?.ty();
        if ty.width_bits() != width_bits {
            return None;
        }
        let leaf = self.arena.intern(ty, TermKind::Leaf(node));
        if let Some(definition) = self.definition_of(value) {
            self.arena.define(leaf, definition);
        }
        self.declare_leaf_facts(leaf, value);
        Some(leaf)
    }

    /// The producer's term, when it is modelled, for a leaf that keeps
    /// reading the value by name.
    fn definition_of(&mut self, value: ValueId) -> Option<TermId> {
        let graph = self.artifact.graph();
        let entity = self.projection.entity_for_output(value)?;
        let root = entity.root();
        let inst = graph.def_inst(value)?;
        if self.in_progress.contains(&root) {
            return None;
        }
        let imported = self.import_root(root, inst);
        (!imported.opaque).then_some(imported.term)
    }

    /// The producer's term in place of a read of `value`, under the policy in
    /// the module doc; `None` keeps the read as a leaf.
    #[allow(clippy::type_complexity)]
    fn try_substitute(
        &mut self,
        value: ValueId,
    ) -> Option<(TermId, Vec<Rewrite>, BTreeSet<CanonicalInstructionId>)> {
        let graph = self.artifact.graph();
        let entity = self.projection.entity_for_output(value)?;
        let root = entity.root();
        let producer = entity.producer();
        let inst = graph.def_inst(value)?;
        if self.in_progress.contains(&root) {
            return None;
        }
        let imported = self.import_root(root, inst);
        if imported.opaque {
            return None;
        }
        // A load moved into its reader would be read past every store between
        // the two, and nothing here proves none of them writes the cell. The
        // load keeps its own statement and the reader keeps naming it.
        if self.arena.reads_memory(imported.term) {
            return None;
        }
        let query = ExpansionQuery {
            artifact: self.artifact,
            projection: self.projection,
            arena: self.arena,
            value,
            producer_term: imported.term,
            entry_never_redefined: &self.entry_never_redefined,
        };
        if !(self.policy)(&query) {
            return None;
        }
        let mut substituted = imported.substituted;
        substituted.insert(producer);
        Some((imported.term, imported.trace, substituted))
    }
}
