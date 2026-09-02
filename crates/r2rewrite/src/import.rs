//! Import of the base machine arena into terms.
//!
//! Every value-producing instruction has one root in the base arena, and that
//! root reads its operands as `Source` leaves: the base arena is one node deep
//! per instruction. A rule that wants to see `(a - b) == 0` therefore has to
//! see through the leaf that names `a - b`. The importer does that once, by a
//! stated policy: a leaf is replaced by its producer's term when the producer
//! is modelled, its dispositions are exact, and either the value has exactly
//! one reader or its term is duplicable (every leaf a literal or an entry value
//! the function never redefines). Which producers were expanded is recorded,
//! because rendering the resulting term renders those instructions here, and
//! the accounting has to know.

use std::collections::{BTreeSet, HashMap, HashSet};

use r2ssa::{
    CanonicalInstructionId, InstId, MachineArithmeticMode, MachineBitVector, MachineCastKind,
    MachineExprId, MachineExprKind, MachineOvershiftBehavior, MachineProjection,
    MachineUseDisposition, MachineWriteDisposition, SsaArtifact, UseSite, ValueId,
};

use crate::driver::Rewrite;
use crate::term::{MAX_TERM_WIDTH_BITS, TermArena, TermId, TermKind};

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

#[derive(Debug, Clone, Default)]
pub struct Import {
    values: Vec<Option<ImportedValue>>,
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
        arena.leaves(term).into_iter().all(|leaf| {
            match projection.expr(leaf).map(|expr| expr.kind()) {
                Some(MachineExprKind::Constant { .. }) => true,
                Some(MachineExprKind::Source { binding, .. }) => {
                    self.entry_never_redefined.contains(&binding.value())
                }
                _ => false,
            }
        }) && !matches!(arena.term(term).kind, TermKind::Opaque(_))
    }
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
    roots: HashMap<MachineExprId, RootImport>,
    in_progress: HashSet<MachineExprId>,
    entry_never_redefined: BTreeSet<ValueId>,
}

pub fn import(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    arena: &mut TermArena,
) -> Import {
    let graph = artifact.graph();
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
    let entry_never_redefined = graph
        .values
        .iter()
        .filter(|value| graph.def_inst(value.id).is_none())
        .filter(|value| {
            value
                .canonical_storage
                .is_some_and(|storage| !rewritten_locations.contains(&storage.location()))
        })
        .map(|value| value.id)
        .collect();
    let mut importer = Importer {
        artifact,
        projection,
        arena,
        roots: HashMap::new(),
        in_progress: HashSet::new(),
        entry_never_redefined,
    };
    let mut values: Vec<Option<ImportedValue>> = vec![None; graph.values.len()];
    for entity in projection.entities() {
        let value = entity.output().value();
        let Some(inst) = graph.def_inst(value) else {
            continue;
        };
        let root = importer.import_root(entity.root(), inst);
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
    Import {
        values,
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
                None => leaf(self.arena),
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
            MachineExprKind::MemoryRead { .. }
            | MachineExprKind::Phi { .. }
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
        let single_reader = graph.use_sites(value).len() == 1;
        if !single_reader && !self.is_duplicable(imported.term) {
            return None;
        }
        let mut substituted = imported.substituted;
        substituted.insert(producer);
        Some((imported.term, imported.trace, substituted))
    }

    fn is_duplicable(&self, term: TermId) -> bool {
        self.arena.leaves(term).into_iter().all(|leaf| {
            match self.projection.expr(leaf).map(|expr| expr.kind()) {
                Some(MachineExprKind::Constant { .. }) => true,
                Some(MachineExprKind::Source { binding, .. }) => {
                    self.entry_never_redefined.contains(&binding.value())
                }
                _ => false,
            }
        }) && !matches!(self.arena.term(term).kind, TermKind::Opaque(_))
    }
}
