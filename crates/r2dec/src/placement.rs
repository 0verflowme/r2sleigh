//! Pure declaration-placement and reaching-definition analysis.
//!
//! The sealed structured-region tree owns lexical ancestry. The canonical SSA
//! function owns CFG predecessors and dominance. This module joins those facts
//! with the read and write occurrences that survived final AST rewriting, then
//! returns an ephemeral decision. It deliberately retains neither a placement
//! table nor a dominance proof beside the tree that produced the answer.
//!
//! The region walk and occurrence grouping are linear. Must-assignment is a
//! forward bitset analysis over a sorted worklist, with cost
//! `O((bindings / word_bits) * (blocks + edges))` per fixpoint sweep.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{
    BinaryOp, CExpr, CFunction, CStmt, RenderObservationId, RenderObservationNode,
    inspect_render_observations,
};
use crate::binding_plan::{
    BindingId, BindingNameResolution, PlacementRead, PlacementRefusal, ValueDisposition,
};
use crate::structured_region::{RegionId, SealedStructuredRegionArtifact};
use r2ssa::{InstId, SSAFunction, UseSite};

/// Final render-order position of an occurrence after every AST rewrite.
///
/// The final marker walk assigns this monotonically. Equal positions are
/// permitted for one expression: reads are evaluated before its write.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FinalOccurrenceOrder(pub(crate) u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FinalObservationScope {
    Exact {
        region: RegionId,
        order: FinalOccurrenceOrder,
    },
    Ambiguous,
}

/// One binding read that survived all AST rewriting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FinalBindingRead {
    pub(crate) binding: BindingId,
    pub(crate) source: PlacementRead,
    pub(crate) region: RegionId,
    pub(crate) block: u64,
    pub(crate) order: FinalOccurrenceOrder,
}

/// One binding write that survived all AST rewriting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FinalBindingWrite {
    pub(crate) binding: BindingId,
    pub(crate) inst: InstId,
    pub(crate) region: RegionId,
    pub(crate) block: u64,
    pub(crate) order: FinalOccurrenceOrder,
    /// Exact surviving marker that owns this write occurrence.
    pub(crate) observation: RenderObservationId,
    /// Whether this exact occurrence is a statement assignment that C permits
    /// the final emitter to replace with a declaration initializer.
    pub(crate) inline_eligible: bool,
    /// Whether removing this write's statement would lose an effect nothing
    /// else answers for.
    pub(crate) effectful: bool,
}

/// Placement-relevant projection of the observation journal's private target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementObservationTarget {
    Use {
        site: UseSite,
        /// Where the normalized operation consuming this use is emitted, which
        /// is not the consuming instruction's own block when normalization
        /// materialized that operation on an edge.
        block: u64,
    },
    CertifiedValueRead {
        value: r2ssa::ValueId,
        at: InstId,
        binding: BindingId,
        symbol: crate::symbol::SymbolId,
    },
    Write {
        inst: InstId,
        projection: r2ssa::MachineWriteProjection,
        /// Where the normalized definition is emitted.
        ///
        /// Normalization materializes one phi definition as a copy on each
        /// incoming edge, so several emitted operations implement one original
        /// instruction and each lives in the predecessor that supplies its
        /// edge. Taking the block from `inst` gave every copy the phi's own
        /// block, which put an occurrence in a region whose entry cannot
        /// dominate it.
        block: u64,
    },
    StackAccess {
        access: r2ssa::StructuredAccessId,
        object: r2ssa::ObjectId,
        binding: BindingId,
        symbol: crate::symbol::SymbolId,
        is_write: bool,
    },
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FinalPlacementOccurrences {
    reads: Box<[FinalBindingRead]>,
    writes: Box<[FinalBindingWrite]>,
}

impl FinalPlacementOccurrences {
    pub(crate) fn reads(&self) -> &[FinalBindingRead] {
        &self.reads
    }

    pub(crate) fn writes(&self) -> &[FinalBindingWrite] {
        &self.writes
    }
}

/// Join the final marker-bearing AST to the canonical source graph and sealed
/// binding plan. This is intentionally a one-shot emit-time calculation.
pub(crate) fn collect_final_placement_occurrences(
    function: &CFunction,
    regions: &SealedStructuredRegionArtifact,
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    expected_observations: usize,
    mut target_for: impl FnMut(RenderObservationId) -> Option<PlacementObservationTarget>,
) -> Result<FinalPlacementOccurrences, PlacementAnalysisError> {
    if !regions.matches_source(source.authority()) {
        return Err(PlacementAnalysisError::SourceAuthorityMismatch);
    }
    crate::structured_region::validate_final_region_marker_tree(&function.body, regions)
        .map_err(PlacementAnalysisError::RegionMarkers)?;
    let mut targets = vec![None; expected_observations];
    let mut statement_assignment = vec![None; expected_observations];
    inspect_render_observations(function, expected_observations, |id, node| {
        let target = target_for(id)
            .ok_or(PlacementAnalysisError::MissingObservationTarget { observation: id })?;
        if let PlacementObservationTarget::CertifiedValueRead {
            value,
            at,
            binding,
            symbol,
        } = target
        {
            if !certified_value_read_matches(source, names, value, at, binding, symbol) {
                return Err(PlacementAnalysisError::InvalidCertifiedValueRead { value, at });
            }
            let RenderObservationNode::Expr(expr) = node else {
                return Err(PlacementAnalysisError::UnobservedBindingRead { binding });
            };
            if !expr_reads_symbol(expr, symbol) {
                return Err(PlacementAnalysisError::UnobservedBindingRead { binding });
            }
        }
        if let PlacementObservationTarget::StackAccess {
            access,
            object,
            binding,
            symbol,
            is_write,
        } = target
        {
            if !stack_access_matches(source, names, access, object, binding, symbol, is_write) {
                return Err(PlacementAnalysisError::InvalidUse {
                    site: UseSite {
                        inst: access.inst,
                        input_idx: 0,
                    },
                });
            }
            let RenderObservationNode::Expr(expr) = node else {
                return Err(if is_write {
                    PlacementAnalysisError::UnobservedBindingWrite { binding }
                } else {
                    PlacementAnalysisError::UnobservedBindingRead { binding }
                });
            };
            if !expr_reads_symbol(expr, symbol) {
                return Err(if is_write {
                    PlacementAnalysisError::UnobservedBindingWrite { binding }
                } else {
                    PlacementAnalysisError::UnobservedBindingRead { binding }
                });
            }
        }
        let index = id.index() as usize;
        targets[index] = Some(target);
        statement_assignment[index] = match node {
            RenderObservationNode::Stmt(stmt) => assigned_symbol(stmt),
            RenderObservationNode::Expr(_) => None,
        };
        Ok(())
    })
    .map_err(|error| match error {
        crate::ast::RenderObservationInspectError::Markers(error) => {
            PlacementAnalysisError::ObservationMarkers(error)
        }
        crate::ast::RenderObservationInspectError::Observer(error) => error,
    })?;

    let mut after_label = BTreeSet::new();
    observations_directly_after_a_label(&function.body, &mut after_label);
    let scoped = collect_final_observation_scopes(&function.body, regions, &targets);

    for (index, target) in targets.iter().copied().enumerate() {
        if matches!(
            target,
            Some(
                PlacementObservationTarget::Use { .. }
                    | PlacementObservationTarget::CertifiedValueRead { .. }
                    | PlacementObservationTarget::Write { .. }
                    | PlacementObservationTarget::StackAccess { .. }
            )
        ) {
            match scoped[index] {
                None => {
                    return Err(PlacementAnalysisError::UnscopedObservation {
                        observation: RenderObservationId::from_dense_index(index),
                    });
                }
                Some(FinalObservationScope::Ambiguous) => {
                    // The refusal names an observation id, and an id alone
                    // says nothing about which occurrence could not be
                    // ordered. What the observation stands for, and -- for a
                    // write -- the instruction and value behind it, is what
                    // an investigation starts from; finding it back from the
                    // id cost a whole session once. The group that declared
                    // the ambiguity names itself in `record_observation_group`
                    // under the same switch.
                    if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                        eprintln!("ambiguous observation {index} target {target:?}");
                        if let Some(PlacementObservationTarget::Write { inst, .. }) = target {
                            let output = source.graph().inst(inst).and_then(|inst| inst.output);
                            eprintln!(
                                "  write of {inst:?} output {output:?} disposition {:?}",
                                output.and_then(|value| names.plan().disposition(value))
                            );
                        }
                    }
                    return Err(PlacementAnalysisError::AmbiguousExecutionOrder {
                        observation: RenderObservationId::from_dense_index(index),
                    });
                }
                Some(FinalObservationScope::Exact { .. }) => {}
            }
        }
    }

    let graph = source.graph();
    let answered_effect_sites = crate::binding_plan::certified_dead_frame_slot_accesses(source);
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    for (index, target) in targets.iter().copied().enumerate() {
        let Some(FinalObservationScope::Exact { region, order }) = scoped[index] else {
            continue;
        };
        let observation = RenderObservationId::from_dense_index(index);
        match target.expect("only reachable observations receive a scope") {
            PlacementObservationTarget::Use { site, block } => {
                let inst = graph
                    .inst(site.inst)
                    .ok_or(PlacementAnalysisError::InvalidUse { site })?;
                let value = *inst
                    .inputs
                    .get(site.input_idx)
                    .ok_or(PlacementAnalysisError::InvalidUse { site })?;
                if let Some(binding) = bound_value(names, value)? {
                    reads.push(FinalBindingRead {
                        binding,
                        source: PlacementRead::Use(site),
                        region,
                        block,
                        order,
                    });
                }
            }
            PlacementObservationTarget::CertifiedValueRead {
                value,
                at,
                binding,
                symbol: _,
            } => {
                let inst = graph
                    .inst(at)
                    .ok_or(PlacementAnalysisError::InvalidWrite { inst: at })?;
                if bound_value(names, value)? == Some(binding) {
                    let block = graph
                        .block(inst.block)
                        .ok_or(PlacementAnalysisError::InvalidWrite { inst: at })?
                        .addr;
                    reads.push(FinalBindingRead {
                        binding,
                        source: PlacementRead::CertifiedValue { value, at },
                        region,
                        block,
                        order,
                    });
                }
            }
            PlacementObservationTarget::Write {
                inst: inst_id,
                projection,
                block,
            } => {
                let inst = graph
                    .inst(inst_id)
                    .ok_or(PlacementAnalysisError::InvalidWrite { inst: inst_id })?;
                let value = inst
                    .output
                    .ok_or(PlacementAnalysisError::InvalidWrite { inst: inst_id })?;
                if let Some(binding) = bound_value(names, value)? {
                    if matches!(projection, r2ssa::MachineWriteProjection::Insert { .. }) {
                        reads.push(FinalBindingRead {
                            binding,
                            source: PlacementRead::PreservedCarrierWrite(inst_id),
                            region,
                            block,
                            order,
                        });
                    }
                    writes.push(FinalBindingWrite {
                        binding,
                        inst: inst_id,
                        region,
                        block,
                        order,
                        observation,
                        inline_eligible: statement_assignment[index]
                            == names.symbol_for_binding(binding)
                            && !after_label.contains(&observation),
                        effectful: removing_statement_would_lose_an_effect(
                            source,
                            inst_id,
                            &answered_effect_sites,
                        ),
                    });
                }
            }
            PlacementObservationTarget::StackAccess {
                access,
                object: _,
                binding,
                symbol: _,
                is_write,
            } => {
                let inst = graph
                    .inst(access.inst)
                    .ok_or(PlacementAnalysisError::InvalidUse {
                        site: UseSite {
                            inst: access.inst,
                            input_idx: 0,
                        },
                    })?;
                let block = graph
                    .block(inst.block)
                    .ok_or(PlacementAnalysisError::InvalidUse {
                        site: UseSite {
                            inst: access.inst,
                            input_idx: 0,
                        },
                    })?
                    .addr;
                if is_write {
                    writes.push(FinalBindingWrite {
                        binding,
                        inst: access.inst,
                        region,
                        block,
                        order,
                        observation,
                        inline_eligible: false,
                        effectful: removing_statement_would_lose_an_effect(
                            source,
                            access.inst,
                            &answered_effect_sites,
                        ),
                    });
                } else {
                    let indexed = source
                        .certificates()
                        .memory_accesses
                        .get(&access)
                        .is_some_and(|fact| source.objects().address_is_indexed(fact.address));
                    reads.push(FinalBindingRead {
                        binding,
                        source: if indexed {
                            PlacementRead::IndexedStackAccess(access)
                        } else {
                            PlacementRead::StackAccess(access)
                        },
                        region,
                        block,
                        order,
                    });
                }
            }
            PlacementObservationTarget::Other => {}
        }
    }

    audit_plan_symbols(function, source, names, &targets)?;
    reads.sort_by_key(|read| (read.order, read.binding, read.source));
    writes.sort_by_key(|write| (write.order, write.binding, write.inst));
    Ok(FinalPlacementOccurrences {
        reads: reads.into_boxed_slice(),
        writes: writes.into_boxed_slice(),
    })
}

/// Whether removing this instruction's statement would lose an effect.
///
/// A dead store drops the statements that write an object nothing reads, and
/// the effect ledger answers separately for whatever else those statements did.
/// That holds for producing a value and for a read whose result nothing wants.
/// It does not hold for an effect the program can observe from outside: a store
/// into memory is one, and dropping it leaves the ledger with an obligation no
/// rendering answers.
///
/// Unless something already answers it. A slot certified to lie in this
/// function's own frame, written and never read, has its stores elided by the
/// effect ledger on that certificate, and those may go.
fn removing_statement_would_lose_an_effect(
    source: &r2ssa::SsaArtifact,
    inst: InstId,
    answered: &BTreeSet<(u64, usize)>,
) -> bool {
    use r2ssa::SemanticObligationKind as Kind;
    let site = source.graph().op_site_for_inst(inst);
    if site.is_some_and(|site| answered.contains(&site)) {
        return false;
    }
    // A `CallDefine` is judged by the call it names.
    //
    // The call operation itself deliberately renders nothing when a
    // `CallDefine` names its result, so that the function is not called twice;
    // the assignment is the call's only statement. Its obligations, though, sit
    // on the call operation rather than on the `CallDefine`, so asking only
    // about the `CallDefine` found nothing observable and the assignment was
    // removed as a dead store -- taking the call with it. That is how
    // `fprintf(stderr, "...")`, whose result nobody reads, disappeared from
    // every function in a `-O0` binary while the proof line read `0 refused`.
    let mut instructions = vec![inst];
    if let Some((block_addr, op_index)) = site
        && matches!(
            source.graph().inst(inst).map(|i| &i.payload),
            Some(r2ssa::InstPayload::Op(r2ssa::SSAOp::CallDefine { .. }))
        )
    {
        // A call is followed by one `CallDefine` per register the convention
        // lets it clobber -- ten of them on amd64 -- so the one naming the
        // result is not necessarily the operation directly after the call.
        // Walking back over the run of them finds the call that owns them all.
        let mut previous = op_index;
        while let Some(earlier) = previous.checked_sub(1) {
            previous = earlier;
            let Some(inst_id) = source.graph().inst_id_for_op_site(block_addr, earlier) else {
                break;
            };
            match source.graph().inst(inst_id).map(|i| &i.payload) {
                Some(r2ssa::InstPayload::Op(r2ssa::SSAOp::CallDefine { .. })) => continue,
                Some(r2ssa::InstPayload::Op(
                    r2ssa::SSAOp::Call { .. } | r2ssa::SSAOp::CallInd { .. },
                )) => {
                    instructions.push(inst_id);
                    break;
                }
                _ => break,
            }
        }
    }
    instructions
        .into_iter()
        .flat_map(|inst| source.obligations().obligations_for_inst(inst))
        .any(|obligation| {
            // Everything whose absence the reader would never learn about.
            //
            // This asked only about a write into memory, on the reasoning that
            // nothing else in the family could arise on a statement that writes
            // an object nothing reads. A call can: `RAX_4 = fprintf(...)` writes
            // a result no one uses *and* calls fprintf. The statement was
            // removed as a dead store and the call went with it, silently --
            // fourteen of the twenty-six calls in one `-O0` binary, in every
            // function rendered, under proof lines reading `0 refused`.
            //
            // A trap, a fence and an atomic are the same argument: the effect
            // belongs to the operation, not to the value it happens to leave
            // behind, so removing the statement removes the effect.
            //
            // A trap is deliberately not here yet, though the argument is the
            // same. A division carries one, and protecting its statement keeps
            // an assignment whose result nothing reads, which `-Werror` rejects
            // as an unused variable. Keeping the effect without the variable
            // needs a rendering form this does not have -- the operation as a
            // bare expression statement -- so the trap keeps its old treatment
            // until that exists rather than trading one wrong answer for a cell
            // that will not compile.
            matches!(
                obligation.id.kind,
                Kind::ObservableMemoryWrite
                    | Kind::Call
                    | Kind::CallResult
                    | Kind::Atomicity
                    | Kind::MemoryOrdering
                    | Kind::VolatileOrUnknownEffect
            )
        })
}

fn bound_value(
    names: &BindingNameResolution,
    value: r2ssa::ValueId,
) -> Result<Option<BindingId>, PlacementAnalysisError> {
    match names.disposition_for_value(value) {
        Some(ValueDisposition::Bound { binding }) => Ok(Some(*binding)),
        Some(ValueDisposition::Inline { .. } | ValueDisposition::Elided { .. }) => Ok(None),
        Some(ValueDisposition::Refused { .. }) => {
            Err(PlacementAnalysisError::RefusedPlannedValue { value })
        }
        None => Err(PlacementAnalysisError::MissingPlannedValue { value }),
    }
}

fn assigned_symbol(statement: &CStmt) -> Option<crate::symbol::SymbolId> {
    let CStmt::Expr(CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        ..
    }) = statement.unobserved()
    else {
        return None;
    };
    match left.unobserved() {
        CExpr::Var(symbol) => Some(*symbol),
        _ => None,
    }
}

/// The region each surviving observation was finally emitted in.
///
/// Placement collects the same answer for the observations it reasons about,
/// filtered to those and ordered among them, because the filtering and the
/// order are part of what it proves. The effect ledger needs the region of
/// every observation and needs no order, so it is collected on its own rather
/// than by widening a walk whose selectivity is load-bearing.
pub(crate) fn final_observation_regions(
    statements: &[CStmt],
    regions: &SealedStructuredRegionArtifact,
    count: usize,
) -> Vec<Option<RegionId>> {
    let mut scoped = vec![None; count];
    for statement in statements {
        collect_stmt_observation_regions(statement, None, regions, &mut scoped);
    }
    scoped
}

fn record_observation_region(
    id: RenderObservationId,
    region: Option<RegionId>,
    scoped: &mut [Option<RegionId>],
) {
    if let (Some(region), Some(slot)) = (region, scoped.get_mut(id.index() as usize)) {
        *slot = Some(region);
    }
}

fn collect_expr_observation_regions(
    expr: &CExpr,
    region: Option<RegionId>,
    scoped: &mut [Option<RegionId>],
) {
    let mut ids = Vec::new();
    visit_expr_observations(expr, &mut |id| ids.push(id));
    for id in ids {
        record_observation_region(id, region, scoped);
    }
}

fn collect_stmt_observation_regions(
    statement: &CStmt,
    current: Option<RegionId>,
    regions: &SealedStructuredRegionArtifact,
    scoped: &mut [Option<RegionId>],
) {
    if let CStmt::StructuredRegion { marker, stmt } = statement {
        let entered = regions.node_for_marker(marker).map(|(id, _)| id);
        collect_stmt_observation_regions(stmt, entered.or(current), regions, scoped);
        return;
    }
    let mut semantic = statement;
    while let CStmt::Observed { id, stmt } = semantic {
        record_observation_region(*id, current, scoped);
        semantic = stmt;
    }
    match semantic {
        CStmt::StructuredRegion { .. } => {
            collect_stmt_observation_regions(semantic, current, regions, scoped);
        }
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
            collect_expr_observation_regions(expr, current, scoped);
        }
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                collect_expr_observation_regions(init, current, scoped);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            collect_expr_observation_regions(cond, current, scoped);
            collect_stmt_observation_regions(then_body, current, regions, scoped);
            if let Some(else_body) = else_body {
                collect_stmt_observation_regions(else_body, current, regions, scoped);
            }
        }
        CStmt::While { cond, body } => {
            collect_expr_observation_regions(cond, current, scoped);
            collect_stmt_observation_regions(body, current, regions, scoped);
        }
        CStmt::DoWhile { body, cond } => {
            collect_stmt_observation_regions(body, current, regions, scoped);
            collect_expr_observation_regions(cond, current, scoped);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                collect_stmt_observation_regions(init, current, regions, scoped);
            }
            if let Some(cond) = cond {
                collect_expr_observation_regions(cond, current, scoped);
            }
            collect_stmt_observation_regions(body, current, regions, scoped);
            if let Some(update) = update {
                collect_expr_observation_regions(update, current, scoped);
            }
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            collect_expr_observation_regions(expr, current, scoped);
            for case in cases {
                collect_expr_observation_regions(&case.value, current, scoped);
                for statement in &case.body {
                    collect_stmt_observation_regions(statement, current, regions, scoped);
                }
            }
            if let Some(default) = default {
                for statement in default {
                    collect_stmt_observation_regions(statement, current, regions, scoped);
                }
            }
        }
        CStmt::Block(statements) => {
            for statement in statements {
                collect_stmt_observation_regions(statement, current, regions, scoped);
            }
        }
        CStmt::Observed { .. } => unreachable!("leading observations were consumed"),
        CStmt::Empty
        | CStmt::Return(None)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

fn collect_final_observation_scopes(
    statements: &[CStmt],
    regions: &SealedStructuredRegionArtifact,
    targets: &[Option<PlacementObservationTarget>],
) -> Vec<Option<FinalObservationScope>> {
    let mut scoped = vec![None; targets.len()];
    let mut order = 0_u64;
    for statement in statements {
        collect_stmt_observation_scopes(statement, None, regions, targets, &mut order, &mut scoped);
    }
    scoped
}

/// Observations carried by a statement that directly follows a label.
///
/// C requires a label to be followed by a statement, so a declaration cannot be
/// emitted there. A write in that position therefore cannot become a
/// declaration with an initializer; it keeps its assignment and takes its
/// declaration from the enclosing region, which is where a jump to the label
/// needs the object to already exist in any case.
///
/// Every observation of the following statement is collected. Being generous
/// here only falls back to a lexical declaration, which is legal in every
/// position an inline declaration is.
fn observations_directly_after_a_label(
    statements: &[CStmt],
    after: &mut BTreeSet<RenderObservationId>,
) {
    let mut previous_was_label = false;
    for statement in statements {
        if previous_was_label {
            collect_statement_observations(statement, after);
        }
        previous_was_label = matches!(statement.unobserved(), CStmt::Label(_));
        visit_nested_statement_lists(statement, after);
    }
}

/// Every observation marker carried by one statement, including its own.
fn collect_statement_observations(statement: &CStmt, into: &mut BTreeSet<RenderObservationId>) {
    match statement {
        CStmt::Observed { id, stmt } => {
            into.insert(*id);
            collect_statement_observations(stmt, into);
        }
        CStmt::StructuredRegion { stmt, .. } => collect_statement_observations(stmt, into),
        CStmt::Expr(expr) => {
            visit_expr_observations(expr, &mut |id| {
                into.insert(id);
            });
        }
        CStmt::Decl {
            init: Some(expr), ..
        } => {
            visit_expr_observations(expr, &mut |id| {
                into.insert(id);
            });
        }
        _ => {}
    }
}

/// Walk into every statement list a statement owns.
fn visit_nested_statement_lists(statement: &CStmt, after: &mut BTreeSet<RenderObservationId>) {
    match statement.unobserved() {
        CStmt::Block(statements) => observations_directly_after_a_label(statements, after),
        CStmt::StructuredRegion { stmt, .. } => visit_nested_statement_lists(stmt, after),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            visit_nested_statement_lists(then_body, after);
            if let Some(else_body) = else_body {
                visit_nested_statement_lists(else_body, after);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            visit_nested_statement_lists(body, after);
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                visit_nested_statement_lists(init, after);
            }
            visit_nested_statement_lists(body, after);
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                observations_directly_after_a_label(&case.body, after);
            }
            if let Some(default) = default {
                observations_directly_after_a_label(default, after);
            }
        }
        _ => {}
    }
}

#[track_caller]
fn record_observation_group(
    ids: &[RenderObservationId],
    region: Option<RegionId>,
    ambiguous: bool,
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    if ids.is_empty() {
        return;
    }
    // Which construct declared the group unorderable. Several do, and the
    // refusal reports only the observation, so the caller's line is the one
    // fact that says whether the answer is a call, an assignment, an operand
    // of a binary, or a control statement's own marker.
    if ambiguous && std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
        eprintln!(
            "ambiguous group {ids:?} recorded at {}",
            std::panic::Location::caller()
        );
    }
    let current = FinalOccurrenceOrder(*order);
    *order = order.saturating_add(1);
    let Some(region) = region else { return };
    for id in ids {
        scoped[id.index() as usize] = Some(if ambiguous {
            FinalObservationScope::Ambiguous
        } else {
            FinalObservationScope::Exact {
                region,
                order: current,
            }
        });
    }
}

fn observation_target(
    targets: &[Option<PlacementObservationTarget>],
    id: RenderObservationId,
) -> Option<PlacementObservationTarget> {
    targets.get(id.index() as usize).copied().flatten()
}

fn observation_is_placement_relevant(
    targets: &[Option<PlacementObservationTarget>],
    id: RenderObservationId,
) -> bool {
    matches!(
        observation_target(targets, id),
        Some(
            PlacementObservationTarget::Use { .. }
                | PlacementObservationTarget::CertifiedValueRead { .. }
                | PlacementObservationTarget::Write { .. }
                | PlacementObservationTarget::StackAccess { .. }
        )
    )
}

fn observation_is_write(
    targets: &[Option<PlacementObservationTarget>],
    id: RenderObservationId,
) -> bool {
    matches!(
        observation_target(targets, id),
        Some(
            PlacementObservationTarget::Write { .. }
                | PlacementObservationTarget::StackAccess { is_write: true, .. }
        )
    )
}

fn expression_has_placement_write(
    expr: &CExpr,
    targets: &[Option<PlacementObservationTarget>],
) -> bool {
    let mut has_write = false;
    visit_expr_observations(expr, &mut |id| {
        has_write |= observation_is_write(targets, id);
    });
    has_write
}

/// Return the exact stack-write markers on a direct variable assignment
/// target.
///
/// A certified stack-object lvalue is already a `BindingId`-owned C variable,
/// so evaluating that lvalue has no address computation or side effect.  C
/// sequences the assignment itself after the right-hand value computation;
/// retaining this narrow shape lets placement order the stack write without
/// pretending that arbitrary binary operands have a defined evaluation order.
/// The exact observations carried by a direct stack-slot assignment target.
///
/// The destination of `slot = value` is an lvalue, not an operand whose order
/// against another operand is unspecified: the address it names is evaluated as
/// part of that lvalue and the store belongs to it. Every observation the target
/// carries is therefore ordered -- the address reads before the store that uses
/// them -- and none of them makes the statement ambiguous.
///
/// Only a chain that bottoms out in a plain variable qualifies. Anything else is
/// a computed destination whose order this cannot state, and stays ambiguous.
fn direct_stack_assignment_observations(
    expr: &CExpr,
    targets: &[Option<PlacementObservationTarget>],
) -> Option<(Vec<RenderObservationId>, Vec<RenderObservationId>)> {
    fn collect(
        expr: &CExpr,
        targets: &[Option<PlacementObservationTarget>],
        reads: &mut Vec<RenderObservationId>,
        writes: &mut Vec<RenderObservationId>,
    ) -> bool {
        match expr {
            CExpr::Observed { id, expr } => {
                match observation_target(targets, *id) {
                    Some(PlacementObservationTarget::StackAccess { is_write: true, .. }) => {
                        writes.push(*id);
                    }
                    // The address this destination names, and any value read to
                    // form it. Both are evaluated before the store they serve.
                    Some(
                        PlacementObservationTarget::Use { .. }
                        | PlacementObservationTarget::CertifiedValueRead { .. }
                        | PlacementObservationTarget::StackAccess {
                            is_write: false, ..
                        },
                    ) => {
                        reads.push(*id);
                    }
                    Some(PlacementObservationTarget::Other) => {}
                    // A write that is not this destination's own store, or an
                    // observation with no target, is not something this can order.
                    Some(PlacementObservationTarget::Write { .. }) | None => return false,
                }
                collect(expr, targets, reads, writes)
            }
            CExpr::Paren(expr) => collect(expr, targets, reads, writes),
            CExpr::Var(_) => true,
            _ => false,
        }
    }

    let mut reads = Vec::new();
    let mut writes = Vec::new();
    (collect(expr, targets, &mut reads, &mut writes) && !writes.is_empty())
        .then_some((reads, writes))
}

fn record_completion_observations(
    ids: &[RenderObservationId],
    current: Option<RegionId>,
    targets: &[Option<PlacementObservationTarget>],
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    let (writes, reads): (Vec<_>, Vec<_>) = ids
        .iter()
        .copied()
        .partition(|id| observation_is_write(targets, *id));
    record_observation_group(&reads, current, false, order, scoped);
    record_observation_group(&writes, current, false, order, scoped);
}

#[track_caller]
fn record_control_observations(
    ids: &[RenderObservationId],
    current: Option<RegionId>,
    targets: &[Option<PlacementObservationTarget>],
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    let ambiguous = ids
        .iter()
        .copied()
        .any(|id| observation_is_placement_relevant(targets, id));
    record_observation_group(ids, current, ambiguous, order, scoped);
}

#[track_caller]
fn record_ambiguous_expr_group<'a>(
    exprs: impl IntoIterator<Item = &'a CExpr>,
    current: Option<RegionId>,
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    let mut ids = Vec::new();
    for expr in exprs {
        visit_expr_observations(expr, &mut |id| ids.push(id));
    }
    record_observation_group(&ids, current, true, order, scoped);
}

fn collect_expr_observation_scopes(
    expr: &CExpr,
    current: Option<RegionId>,
    targets: &[Option<PlacementObservationTarget>],
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    let mut leading = Vec::new();
    let mut semantic = expr;
    while let CExpr::Observed { id, expr } = semantic {
        leading.push(*id);
        semantic = expr;
    }

    match semantic {
        CExpr::Observed { .. } => unreachable!("leading observations were consumed"),
        CExpr::Comma(items) => {
            for item in items {
                collect_expr_observation_scopes(item, current, targets, order, scoped);
            }
        }
        CExpr::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            left,
            right,
        } => {
            collect_expr_observation_scopes(left, current, targets, order, scoped);
            if expression_has_placement_write(right, targets) {
                record_ambiguous_expr_group([right.as_ref()], current, order, scoped);
            } else {
                collect_expr_observation_scopes(right, current, targets, order, scoped);
            }
        }
        CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        } => {
            if let Some((reads, writes)) = direct_stack_assignment_observations(left, targets) {
                collect_expr_observation_scopes(right, current, targets, order, scoped);
                // The destination's address is read before the store that uses it.
                record_observation_group(&reads, current, false, order, scoped);
                record_observation_group(&writes, current, false, order, scoped);
            } else if expression_has_placement_write(left, targets)
                || expression_has_placement_write(right, targets)
            {
                record_ambiguous_expr_group(
                    [left.as_ref(), right.as_ref()],
                    current,
                    order,
                    scoped,
                );
            } else {
                collect_expr_observation_scopes(left, current, targets, order, scoped);
                collect_expr_observation_scopes(right, current, targets, order, scoped);
            }
        }
        CExpr::Binary { left, right, .. } => {
            if expression_has_placement_write(left, targets)
                || expression_has_placement_write(right, targets)
            {
                record_ambiguous_expr_group(
                    [left.as_ref(), right.as_ref()],
                    current,
                    order,
                    scoped,
                );
            } else {
                collect_expr_observation_scopes(left, current, targets, order, scoped);
                collect_expr_observation_scopes(right, current, targets, order, scoped);
            }
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_observation_scopes(cond, current, targets, order, scoped);
            if expression_has_placement_write(then_expr, targets)
                || expression_has_placement_write(else_expr, targets)
            {
                record_ambiguous_expr_group(
                    [then_expr.as_ref(), else_expr.as_ref()],
                    current,
                    order,
                    scoped,
                );
            } else {
                collect_expr_observation_scopes(then_expr, current, targets, order, scoped);
                collect_expr_observation_scopes(else_expr, current, targets, order, scoped);
            }
        }
        CExpr::Call { func, args, .. } => {
            if expression_has_placement_write(func, targets)
                || args
                    .iter()
                    .any(|arg| expression_has_placement_write(arg, targets))
            {
                record_ambiguous_expr_group(
                    std::iter::once(func.as_ref()).chain(args.iter()),
                    current,
                    order,
                    scoped,
                );
            } else {
                collect_expr_observation_scopes(func, current, targets, order, scoped);
                for arg in args {
                    collect_expr_observation_scopes(arg, current, targets, order, scoped);
                }
            }
        }
        CExpr::Subscript { base, index } => {
            if expression_has_placement_write(base, targets)
                || expression_has_placement_write(index, targets)
            {
                record_ambiguous_expr_group(
                    [base.as_ref(), index.as_ref()],
                    current,
                    order,
                    scoped,
                );
            } else {
                collect_expr_observation_scopes(base, current, targets, order, scoped);
                collect_expr_observation_scopes(index, current, targets, order, scoped);
            }
        }
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand)
        | CExpr::Paren(operand)
        | CExpr::Member { base: operand, .. }
        | CExpr::PtrMember { base: operand, .. } => {
            collect_expr_observation_scopes(operand, current, targets, order, scoped);
        }
        CExpr::Sizeof(operand) => {
            record_ambiguous_expr_group([operand.as_ref()], current, order, scoped);
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
    }

    record_completion_observations(&leading, current, targets, order, scoped);
}

fn collect_stmt_observation_scopes(
    statement: &CStmt,
    current: Option<RegionId>,
    regions: &SealedStructuredRegionArtifact,
    targets: &[Option<PlacementObservationTarget>],
    order: &mut u64,
    scoped: &mut [Option<FinalObservationScope>],
) {
    if let CStmt::StructuredRegion { marker, stmt } = statement {
        let (region, _) = regions
            .node_for_marker(marker)
            .expect("the final marker tree was validated before scope collection");
        collect_stmt_observation_scopes(stmt, Some(region), regions, targets, order, scoped);
        return;
    }
    let mut leading = Vec::new();
    let mut semantic = statement;
    while let CStmt::Observed { id, stmt } = semantic {
        leading.push(*id);
        semantic = stmt;
    }
    match semantic {
        CStmt::StructuredRegion { .. } => {
            record_control_observations(&leading, current, targets, order, scoped);
            collect_stmt_observation_scopes(semantic, current, regions, targets, order, scoped);
        }
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
            collect_expr_observation_scopes(expr, current, targets, order, scoped);
            record_completion_observations(&leading, current, targets, order, scoped);
        }
        CStmt::Decl { init, .. } => {
            if let Some(init) = init {
                collect_expr_observation_scopes(init, current, targets, order, scoped);
            }
            record_completion_observations(&leading, current, targets, order, scoped);
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            record_control_observations(&leading, current, targets, order, scoped);
            collect_expr_observation_scopes(cond, current, targets, order, scoped);
            collect_stmt_observation_scopes(then_body, current, regions, targets, order, scoped);
            if let Some(else_body) = else_body {
                collect_stmt_observation_scopes(
                    else_body, current, regions, targets, order, scoped,
                );
            }
        }
        CStmt::While { cond, body } => {
            record_control_observations(&leading, current, targets, order, scoped);
            collect_expr_observation_scopes(cond, current, targets, order, scoped);
            collect_stmt_observation_scopes(body, current, regions, targets, order, scoped);
        }
        CStmt::DoWhile { body, cond } => {
            record_control_observations(&leading, current, targets, order, scoped);
            collect_stmt_observation_scopes(body, current, regions, targets, order, scoped);
            collect_expr_observation_scopes(cond, current, targets, order, scoped);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            record_control_observations(&leading, current, targets, order, scoped);
            if let Some(init) = init {
                collect_stmt_observation_scopes(init, current, regions, targets, order, scoped);
            }
            if let Some(cond) = cond {
                collect_expr_observation_scopes(cond, current, targets, order, scoped);
            }
            collect_stmt_observation_scopes(body, current, regions, targets, order, scoped);
            if let Some(update) = update {
                collect_expr_observation_scopes(update, current, targets, order, scoped);
            }
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            record_control_observations(&leading, current, targets, order, scoped);
            collect_expr_observation_scopes(expr, current, targets, order, scoped);
            for case in cases {
                record_ambiguous_expr_group([&case.value], current, order, scoped);
                for statement in &case.body {
                    collect_stmt_observation_scopes(
                        statement, current, regions, targets, order, scoped,
                    );
                }
            }
            if let Some(default) = default {
                for statement in default {
                    collect_stmt_observation_scopes(
                        statement, current, regions, targets, order, scoped,
                    );
                }
            }
        }
        CStmt::Block(statements) => {
            record_control_observations(&leading, current, targets, order, scoped);
            for statement in statements {
                collect_stmt_observation_scopes(
                    statement, current, regions, targets, order, scoped,
                );
            }
        }
        CStmt::Observed { .. } => unreachable!("leading observations were consumed"),
        CStmt::Empty
        | CStmt::Return(None)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {
            record_completion_observations(&leading, current, targets, order, scoped);
        }
    }
}

fn visit_expr_observations(expr: &CExpr, visit: &mut impl FnMut(RenderObservationId)) {
    if let CExpr::Observed { id, expr } = expr {
        visit(*id);
        visit_expr_observations(expr, visit);
        return;
    }
    match expr {
        CExpr::Observed { .. } => unreachable!("leading observation was consumed"),
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => visit_expr_observations(operand, visit),
        CExpr::Binary { left, right, .. } => {
            visit_expr_observations(left, visit);
            visit_expr_observations(right, visit);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            visit_expr_observations(cond, visit);
            visit_expr_observations(then_expr, visit);
            visit_expr_observations(else_expr, visit);
        }
        CExpr::Call { func, args, .. } => {
            visit_expr_observations(func, visit);
            for arg in args {
                visit_expr_observations(arg, visit);
            }
        }
        CExpr::Subscript { base, index } => {
            visit_expr_observations(base, visit);
            visit_expr_observations(index, visit);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            visit_expr_observations(base, visit);
        }
        CExpr::Comma(items) => {
            for item in items {
                visit_expr_observations(item, visit);
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SymbolAccess {
    Read,
    Write,
}

fn audit_plan_symbols(
    function: &CFunction,
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    targets: &[Option<PlacementObservationTarget>],
) -> Result<(), PlacementAnalysisError> {
    let by_symbol = names
        .plan()
        .bindings()
        .filter_map(|(binding, _)| {
            names
                .symbol_for_binding(binding)
                .map(|symbol| (symbol, binding))
        })
        .collect::<BTreeMap<_, _>>();
    for local in &function.locals {
        if !by_symbol.contains_key(&local.name) {
            return Err(PlacementAnalysisError::UnauthorizedProgramVariable { symbol: local.name });
        }
    }
    for statement in &function.body {
        audit_statement(statement, source, names, targets, &by_symbol)?;
    }
    Ok(())
}

fn audit_statement(
    statement: &CStmt,
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    targets: &[Option<PlacementObservationTarget>],
    by_symbol: &BTreeMap<crate::symbol::SymbolId, BindingId>,
) -> Result<(), PlacementAnalysisError> {
    if let CStmt::StructuredRegion { stmt, .. } = statement {
        return audit_statement(stmt, source, names, targets, by_symbol);
    }
    let mut active = Vec::new();
    let mut semantic = statement;
    while let CStmt::Observed { id, stmt } = semantic {
        if let Some(target) = targets.get(id.index() as usize).copied().flatten() {
            active.push(target);
        }
        semantic = stmt;
    }
    match semantic {
        CStmt::StructuredRegion { stmt, .. } => {
            audit_statement(stmt, source, names, targets, by_symbol)?;
        }
        CStmt::Observed { .. } => unreachable!("leading observations were consumed"),
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
            audit_expr(
                expr,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CStmt::Decl { name, init, .. } => {
            audit_program_symbol(
                *name,
                SymbolAccess::Write,
                &active,
                source,
                names,
                by_symbol,
            )?;
            if let Some(init) = init {
                audit_expr(
                    init,
                    SymbolAccess::Read,
                    &active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CStmt::Block(statements) => {
            for statement in statements {
                audit_statement(statement, source, names, targets, by_symbol)?;
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            audit_expr(
                cond,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
            audit_statement(then_body, source, names, targets, by_symbol)?;
            if let Some(else_body) = else_body {
                audit_statement(else_body, source, names, targets, by_symbol)?;
            }
        }
        CStmt::While { cond, body } => {
            audit_expr(
                cond,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
            audit_statement(body, source, names, targets, by_symbol)?;
        }
        CStmt::DoWhile { body, cond } => {
            audit_statement(body, source, names, targets, by_symbol)?;
            audit_expr(
                cond,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                audit_statement(init, source, names, targets, by_symbol)?;
            }
            if let Some(cond) = cond {
                audit_expr(
                    cond,
                    SymbolAccess::Read,
                    &active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
            if let Some(update) = update {
                audit_expr(
                    update,
                    SymbolAccess::Read,
                    &active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
            audit_statement(body, source, names, targets, by_symbol)?;
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            audit_expr(
                expr,
                SymbolAccess::Read,
                &active,
                source,
                names,
                targets,
                by_symbol,
            )?;
            for case in cases {
                audit_expr(
                    &case.value,
                    SymbolAccess::Read,
                    &active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
                for statement in &case.body {
                    audit_statement(statement, source, names, targets, by_symbol)?;
                }
            }
            if let Some(default) = default {
                for statement in default {
                    audit_statement(statement, source, names, targets, by_symbol)?;
                }
            }
        }
        CStmt::Empty
        | CStmt::Return(None)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
    Ok(())
}

fn audit_expr(
    expr: &CExpr,
    access: SymbolAccess,
    active: &[PlacementObservationTarget],
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    targets: &[Option<PlacementObservationTarget>],
    by_symbol: &BTreeMap<crate::symbol::SymbolId, BindingId>,
) -> Result<(), PlacementAnalysisError> {
    if let CExpr::Observed { id, expr } = expr {
        let mut nested = active.to_vec();
        if let Some(target) = targets.get(id.index() as usize).copied().flatten() {
            nested.push(target);
        }
        return audit_expr(expr, access, &nested, source, names, targets, by_symbol);
    }
    match expr {
        CExpr::Var(symbol) => {
            audit_program_symbol(*symbol, access, active, source, names, by_symbol)?;
        }
        CExpr::Observed { .. } => unreachable!("leading observation was consumed"),
        CExpr::Unary { op, operand } => {
            if matches!(
                op,
                crate::ast::UnaryOp::PreInc
                    | crate::ast::UnaryOp::PreDec
                    | crate::ast::UnaryOp::PostInc
                    | crate::ast::UnaryOp::PostDec
            ) && matches!(operand.unobserved(), CExpr::Var(_))
            {
                audit_expr(
                    operand,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
                audit_expr(
                    operand,
                    SymbolAccess::Write,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            } else {
                audit_expr(
                    operand,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::Binary { op, left, right } => {
            let assignment = matches!(
                op,
                BinaryOp::Assign
                    | BinaryOp::AddAssign
                    | BinaryOp::SubAssign
                    | BinaryOp::MulAssign
                    | BinaryOp::DivAssign
                    | BinaryOp::ModAssign
                    | BinaryOp::BitAndAssign
                    | BinaryOp::BitOrAssign
                    | BinaryOp::BitXorAssign
                    | BinaryOp::ShlAssign
                    | BinaryOp::ShrAssign
            );
            if assignment && matches!(left.unobserved(), CExpr::Var(_)) {
                if *op != BinaryOp::Assign {
                    audit_expr(
                        left,
                        SymbolAccess::Read,
                        active,
                        source,
                        names,
                        targets,
                        by_symbol,
                    )?;
                }
                audit_expr(
                    left,
                    SymbolAccess::Write,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            } else {
                audit_expr(
                    left,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
            audit_expr(
                right,
                SymbolAccess::Read,
                active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            for expr in [cond.as_ref(), then_expr.as_ref(), else_expr.as_ref()] {
                audit_expr(
                    expr,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::Cast { expr, .. }
        | CExpr::Sizeof(expr)
        | CExpr::AddrOf(expr)
        | CExpr::Deref(expr)
        | CExpr::Paren(expr) => {
            audit_expr(
                expr,
                SymbolAccess::Read,
                active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CExpr::Call { func, args, .. } => {
            audit_expr(
                func,
                SymbolAccess::Read,
                active,
                source,
                names,
                targets,
                by_symbol,
            )?;
            for arg in args {
                audit_expr(
                    arg,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::Subscript { base, index } => {
            for expr in [base.as_ref(), index.as_ref()] {
                audit_expr(
                    expr,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            audit_expr(
                base,
                SymbolAccess::Read,
                active,
                source,
                names,
                targets,
                by_symbol,
            )?;
        }
        CExpr::Comma(items) => {
            for item in items {
                audit_expr(
                    item,
                    SymbolAccess::Read,
                    active,
                    source,
                    names,
                    targets,
                    by_symbol,
                )?;
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
    }
    Ok(())
}

fn audit_program_symbol(
    symbol: crate::symbol::SymbolId,
    access: SymbolAccess,
    active: &[PlacementObservationTarget],
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    by_symbol: &BTreeMap<crate::symbol::SymbolId, BindingId>,
) -> Result<(), PlacementAnalysisError> {
    let binding = by_symbol
        .get(&symbol)
        .copied()
        .ok_or(PlacementAnalysisError::UnauthorizedProgramVariable { symbol })?;
    if active
        .iter()
        .copied()
        .any(|target| target_authorizes_binding(target, access, binding, source, names))
    {
        return Ok(());
    }
    r2il::refusal_evidence!(
        "binding-symbol-observed",
        "{access:?} binding={binding:?} name={:?} members={:?} active={:?}",
        names.spelling(symbol),
        (0..source.graph().values.len())
            .filter(|index| {
                u32::try_from(*index).ok().is_some_and(|index| {
                    names
                        .disposition_for_value(r2ssa::ValueId(index))
                        .is_some_and(|disposition| {
                            matches!(disposition, ValueDisposition::Bound { binding: owner } if *owner == binding)
                        })
                })
            })
            .collect::<Vec<_>>(),
        active.iter().map(|t| format!("{t:?}")).collect::<Vec<_>>()
    );
    Err(match access {
        SymbolAccess::Read => PlacementAnalysisError::UnobservedBindingRead { binding },
        SymbolAccess::Write => PlacementAnalysisError::UnobservedBindingWrite { binding },
    })
}

fn target_authorizes_binding(
    target: PlacementObservationTarget,
    access: SymbolAccess,
    binding: BindingId,
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
) -> bool {
    let graph = source.graph();
    match (target, access) {
        (PlacementObservationTarget::Use { site, .. }, SymbolAccess::Read) => graph
            .inst(site.inst)
            .and_then(|inst| inst.inputs.get(site.input_idx))
            .and_then(|value| names.disposition_for_value(*value))
            .is_some_and(|disposition| {
                matches!(disposition, ValueDisposition::Bound { binding: owner } if *owner == binding)
            }),
        (
            PlacementObservationTarget::CertifiedValueRead {
                value,
                at,
                binding: certified_binding,
                symbol,
            },
            SymbolAccess::Read,
        ) => {
            certified_binding == binding
                && certified_value_read_matches(
                    source,
                    names,
                    value,
                    at,
                    certified_binding,
                    symbol,
                )
        }
        (
            PlacementObservationTarget::Write {
                inst,
                projection: _,
                block: _,
            },
            SymbolAccess::Write,
        ) => graph
            .inst(inst)
            .and_then(|inst| inst.output)
            .and_then(|value| names.disposition_for_value(value))
            .is_some_and(|disposition| {
                matches!(disposition, ValueDisposition::Bound { binding: owner } if *owner == binding)
            }),
        (
            PlacementObservationTarget::Write {
                inst,
                projection,
                block: _,
            },
            SymbolAccess::Read,
        ) => {
            matches!(projection, r2ssa::MachineWriteProjection::Insert { .. })
                && graph
                .inst(inst)
                .and_then(|inst| inst.output)
                .and_then(|value| names.disposition_for_value(value))
                .is_some_and(|disposition| {
                    matches!(disposition, ValueDisposition::Bound { binding: owner } if *owner == binding)
                })
        }
        (
            PlacementObservationTarget::StackAccess {
                access,
                object,
                binding: stack_binding,
                symbol,
                is_write,
            },
            SymbolAccess::Write,
        ) => {
            is_write
                && stack_binding == binding
                && stack_access_matches(
                    source,
                    names,
                    access,
                    object,
                    stack_binding,
                    symbol,
                    true,
                )
        }
        (
            PlacementObservationTarget::StackAccess {
                access,
                object,
                binding: stack_binding,
                symbol,
                is_write,
            },
            SymbolAccess::Read,
        ) => {
            !is_write
                && stack_binding == binding
                && stack_access_matches(
                    source,
                    names,
                    access,
                    object,
                    stack_binding,
                    symbol,
                    false,
                )
        }
        (PlacementObservationTarget::Use { .. }, SymbolAccess::Write)
        | (PlacementObservationTarget::CertifiedValueRead { .. }, SymbolAccess::Write)
        | (PlacementObservationTarget::Other, _) => false,
    }
}

/// Whether the source certifies that this instruction reads this value at a
/// boundary for which the graph records no use.
///
/// A value crossing a boundary is read by an instruction that does not take it
/// as an operand. `SSAOp::Return` carries only the control target and
/// `SSAOp::Call` only the callee, so a returned value and a call argument
/// alike have no `UseSite` anywhere in the graph. The boundary certificate is
/// the only record that the read happens, and it is the same kind of record in
/// both directions: the return certificate names the one value leaving the
/// function, and the callsite certificate names each value entering the
/// callee.
pub(crate) fn certified_boundary_read(
    source: &r2ssa::SsaArtifact,
    value: r2ssa::ValueId,
    at: InstId,
) -> bool {
    let graph = source.graph();
    let Some(site) = graph.op_site_for_inst(at) else {
        return false;
    };
    let Some(payload) = graph.inst(at).map(|inst| &inst.payload) else {
        return false;
    };
    let certificates = source.certificates();
    let returns = certificates
        .returns_by_inst
        .get(&at)
        .and_then(|index| certificates.returns.get(*index))
        .is_some_and(|certificate| {
            certificate.at == at
                // Any value the return carries, not only its base. A composed
                // return reads its base and every overlay at this one site, so
                // asking about the base alone refuses the overlays' reads.
                && certificate.values().any(|carried| carried == value)
                && (certificate.block_addr, certificate.op_index) == site
                && matches!(payload, r2ssa::InstPayload::Op(r2ssa::SSAOp::Return { .. }))
        });
    // A call result seen at another width reads the carrier it is a slice of.
    // The `Derived` certificate is that proof: it names this value, the call
    // site, and the identity result it derives from, so the read of the
    // carrier's name is certified in the same sense the return and argument
    // boundaries are.
    // A call result seen at another width reads the carrier it is a slice of.
    // The instruction here defines that slice, and its `Derived` certificate
    // names the call site; the value being read is the identity result of the
    // same site. That pair is the proof, in the same sense the return and
    // argument boundaries are proofs.
    let derived_result = graph
        .inst(at)
        .and_then(|inst| inst.output)
        .and_then(|defined| source.call_result_certificate_for_value(defined))
        .is_some_and(|slice| {
            !slice.relation.is_identity()
                && source
                    .call_result_certificate_for_value(value)
                    .is_some_and(|carrier| {
                        carrier.relation.is_identity() && carrier.call_site == slice.call_site
                    })
        });
    // The value a certified switch dispatches on, read at its dispatch. The
    // switch certificate names the block and the selector, and the instruction
    // is that block's indirect branch: the same pair of facts the return and
    // argument boundaries are proved by. A dispatch has no operand for the
    // selector -- its only input is the address it computed -- so without this
    // the `switch (...)` heading reads a program variable no table authorizes,
    // which is what refused every function with a jump table.
    let switch_selector = graph
        .inst(at)
        .and_then(|inst| graph.block(inst.block))
        .and_then(|block| certificates.switches.get(&block.addr))
        .is_some_and(|certificate| {
            certificate.selector == Some(value)
                && matches!(
                    payload,
                    r2ssa::InstPayload::Op(r2ssa::SSAOp::BranchInd { .. })
                )
        });
    returns
        || derived_result
        || switch_selector
        || certificates
            .callsites_by_inst
            .get(&at)
            .and_then(|call_site| certificates.callsites.get(call_site))
            .is_some_and(|certificate| {
                certificate.at == at
                    && (certificate.block_addr, certificate.op_index) == site
                    && certificate
                        .argument_certificates
                        .iter()
                        .any(|argument| argument.value == value)
                    && matches!(
                        payload,
                        r2ssa::InstPayload::Op(
                            r2ssa::SSAOp::Call { .. } | r2ssa::SSAOp::CallInd { .. }
                        )
                    )
            })
}

/// Revalidate the complete source-to-render identity chain carried by a
/// certified value-read marker. The boundary certificate owns `(ValueId,
/// InstId)`; the sealed binding plan owns `ValueId -> BindingId`; and name
/// resolution owns `BindingId -> SymbolId`. No one of those links is a
/// substitute for the others.
fn certified_value_read_matches(
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    value: r2ssa::ValueId,
    at: InstId,
    binding: BindingId,
    symbol: crate::symbol::SymbolId,
) -> bool {
    certified_boundary_read(source, value, at)
        && matches!(
            names.disposition_for_value(value),
            Some(ValueDisposition::Bound { binding: owner }) if *owner == binding
        )
        && names.symbol_for_binding(binding) == Some(symbol)
}

/// Revalidate one stack-object occurrence without resolving a stack offset or
/// inspecting a presentation spelling.
fn stack_access_matches(
    source: &r2ssa::SsaArtifact,
    names: &BindingNameResolution,
    access: r2ssa::StructuredAccessId,
    object: r2ssa::ObjectId,
    binding: BindingId,
    symbol: crate::symbol::SymbolId,
    is_write: bool,
) -> bool {
    source
        .structured()
        .memory_accesses
        .get(&access)
        .is_some_and(|fact| {
            fact.id == access
                && fact.object == object
                && fact.is_write == is_write
                && fact.provenance_complete
        })
        && matches!(
            names.plan().stack_object_disposition(object),
            Some(crate::binding_plan::StackObjectDisposition::Bound { binding: owner })
                if owner == binding
        )
        && names.symbol_for_binding(binding) == Some(symbol)
}

/// Whether evaluating this expression reads the exact program symbol.
///
/// This follows C read semantics closely enough to reject a forged marker on
/// `symbol = literal`, `&symbol`, or `sizeof(symbol)`, while retaining exact
/// casts and slice projections produced from the planned value expression.
pub(crate) fn expr_reads_symbol(expr: &CExpr, symbol: crate::symbol::SymbolId) -> bool {
    match expr.unobserved() {
        CExpr::Var(actual) => *actual == symbol,
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => expr_reads_symbol(operand, symbol),
        CExpr::Binary { op, left, right } => {
            expr_reads_symbol(right, symbol)
                || (!matches!(op, BinaryOp::Assign) || !matches!(left.unobserved(), CExpr::Var(_)))
                    && expr_reads_symbol(left, symbol)
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_reads_symbol(cond, symbol)
                || expr_reads_symbol(then_expr, symbol)
                || expr_reads_symbol(else_expr, symbol)
        }
        CExpr::Call { func, args, .. } => {
            expr_reads_symbol(func, symbol) || args.iter().any(|arg| expr_reads_symbol(arg, symbol))
        }
        CExpr::Subscript { base, index } => {
            expr_reads_symbol(base, symbol) || expr_reads_symbol(index, symbol)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            expr_reads_symbol(base, symbol)
        }
        CExpr::Comma(items) => items.iter().any(|item| expr_reads_symbol(item, symbol)),
        CExpr::Observed { .. } => unreachable!("unobserved expression returned a wrapper"),
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::External { .. }
        | CExpr::Sizeof(_)
        | CExpr::SizeofType(_)
        | CExpr::AddrOf(_) => false,
    }
}

/// A decision consumed immediately by final emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementDecision {
    /// The binding is already declared by the function signature and is
    /// assigned on function entry by the calling convention.
    ExternallyDeclared,
    /// Declare at the start of the lowest valid lexical region, then assign at
    /// each surviving write occurrence.
    LexicalDeclaration { region: RegionId },
    /// Replace the sole dominating assignment with a declaration initializer.
    ///
    /// `region` is where the binding is declared if the inline turns out not to
    /// be expressible. Folding a write into a declaration moves the declaration
    /// to wherever that write is written, and C's scopes do not always follow
    /// the nesting of the tree: a `do { ... } while (cond)` evaluates its
    /// condition outside the braces, so a write inside the body becomes a
    /// declaration the condition's read cannot see. Whether that has happened
    /// is a fact about the emitted tree, so it is settled after the decisions
    /// are applied, and this is what the binding falls back to.
    Inline { write: InstId, region: RegionId },
    /// Nothing reads this object, so it needs no declaration and its writes
    /// need no statement. The obligations those statements carried are
    /// accounted as elided when the journal seals.
    ///
    /// `region` is where the binding is declared if the removal turns out not
    /// to be expressible, for the same reason `Inline` carries one. The
    /// occurrence set records placement-relevant reads, which is not every
    /// mention: a read folded into another expression names the symbol without
    /// leaving an occurrence. When the trial removal finds the name still
    /// there, the object is not dead after all, and it needs the declaration
    /// this names. Leaving the decision as it was dropped the declaration and
    /// kept the statements -- an undeclared identifier, which is the one thing
    /// placement must never emit.
    DeadStore { region: Option<RegionId> },
    /// Honest C cannot be emitted for this binding.
    Refused(PlacementRefusal),
}

/// Dense result in ascending `BindingId` order.
///
/// `None` means that the binding has no surviving occurrence and needs no C
/// declaration. The vector is transient and is not retained by `BindingPlan`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PlacementDecisions {
    decisions: Box<[Option<PlacementDecision>]>,
}

impl PlacementDecisions {
    /// A decision set stated directly, for tests that need one specific
    /// decision rather than whatever the derivation would choose.
    #[cfg(test)]
    pub(crate) fn from_decisions_for_test(decisions: Vec<Option<PlacementDecision>>) -> Self {
        Self {
            decisions: decisions.into_boxed_slice(),
        }
    }

    #[cfg(test)]
    pub(crate) fn decision(&self, binding: BindingId) -> Option<PlacementDecision> {
        self.decisions.get(binding.index()).copied().flatten()
    }

    pub(crate) fn iter(
        &self,
    ) -> impl ExactSizeIterator<Item = (BindingId, Option<PlacementDecision>)> + '_ {
        self.decisions.iter().enumerate().map(|(index, decision)| {
            let binding = BindingId::from_dense_index(index)
                .expect("placement decision count fits BindingId");
            (binding, *decision)
        })
    }
}

/// Structural mismatch between final occurrences and their two authorities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PlacementAnalysisError {
    SourceAuthorityMismatch,
    BindingOutsidePlan { binding: BindingId },
    RegionOutsideArtifact { region: RegionId },
    BlockOutsideFunction { block: u64 },
    RegionDoesNotDominateOccurrence { region: RegionId, block: u64 },
    ExternalBindingOutsidePlan { binding: BindingId },
    RegionMarkers(crate::structured_region::StructuredRegionFinalizationError),
    ObservationMarkers(crate::ast::RenderObservationStripError),
    MissingObservationTarget { observation: RenderObservationId },
    InvalidUse { site: UseSite },
    InvalidWrite { inst: InstId },
    InvalidCertifiedValueRead { value: r2ssa::ValueId, at: InstId },
    MissingPlannedValue { value: r2ssa::ValueId },
    RefusedPlannedValue { value: r2ssa::ValueId },
    UnscopedObservation { observation: RenderObservationId },
    AmbiguousExecutionOrder { observation: RenderObservationId },
    UnauthorizedProgramVariable { symbol: crate::symbol::SymbolId },
    UnobservedBindingRead { binding: BindingId },
    UnobservedBindingWrite { binding: BindingId },
}

/// Failure to apply a derived decision to the exact final marked tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PlacementApplicationError {
    Refused(PlacementRefusal),
    MissingBinding { binding: BindingId },
    MissingBindingSymbol { binding: BindingId },
    ExternalBindingMissingParameter { binding: BindingId },
    MissingRegion { region: RegionId },
    DuplicateRegion { region: RegionId },
    MissingInlineWrite { inst: InstId },
    DuplicateInlineWrite { inst: InstId },
}

/// Apply a decision set transactionally to the exact marker-bearing function.
/// Apply the derived decisions, reporting which bindings actually lost their
/// statements.
///
/// The caller has to tell the ledger which writes were elided so their
/// obligations are closed out at the seal. It used to predict that set from the
/// decisions, before this ran. The prediction and the action can disagree --
/// a decision can be declined here because the tree still mentions the symbol,
/// and a binding the derivation never called dead can lose its last reader to
/// another binding's removal -- so what is reported is what happened, not what
/// was planned.
pub(crate) fn apply_placement_decisions(
    function: &mut CFunction,
    regions: &SealedStructuredRegionArtifact,
    names: &BindingNameResolution,
    decisions: &PlacementDecisions,
    writes: &[FinalBindingWrite],
) -> Result<PlacementRemovals, PlacementApplicationError> {
    // Inlining a write moves the binding's declaration to wherever that write
    // is written, and whether the result is in scope for the reads is a fact
    // about the emitted tree, not about the occurrence set the decisions were
    // derived from. So the tree is asked: apply, check the property, and demote
    // any inline the check reports to the lexical declaration it carries as its
    // fallback. A demotion can only ever turn an inline into a declaration, so
    // the loop terminates.
    // One copy, kept because a demotion has to start again from the tree as it
    // was and because an application that refuses must leave the emitted
    // function untouched -- `finish_enforcing` goes on to inspect it. The
    // decisions are applied to the real tree rather than to a second copy of
    // this one, so the common case, where nothing is demoted, pays for this
    // snapshot and nothing else.
    let original = function.clone();
    let mut demoted = BTreeMap::<BindingId, PlacementDecision>::new();
    loop {
        let removals =
            match apply_decisions_once(function, regions, names, decisions, writes, &demoted) {
                Ok(removals) => removals,
                Err(error) => {
                    *function = original;
                    return Err(error);
                }
            };
        let undeclared = crate::unrendered::names_mentioned_without_a_declaration(function);
        let mut progressed = false;
        for symbol in undeclared {
            let Some((binding, region)) =
                decisions
                    .iter()
                    .find_map(|(binding, decision)| match decision {
                        Some(PlacementDecision::Inline { region, .. })
                            if names.symbol_for_binding(binding) == Some(symbol) =>
                        {
                            Some((binding, region))
                        }
                        _ => None,
                    })
            else {
                continue;
            };
            if demoted.contains_key(&binding) {
                continue;
            }
            demoted.insert(binding, PlacementDecision::LexicalDeclaration { region });
            progressed = true;
        }
        if !progressed {
            return Ok(removals);
        }
        *function = original.clone();
    }
}

fn apply_decisions_once(
    function: &mut CFunction,
    regions: &SealedStructuredRegionArtifact,
    names: &BindingNameResolution,
    decisions: &PlacementDecisions,
    writes: &[FinalBindingWrite],
    demoted: &BTreeMap<BindingId, PlacementDecision>,
) -> Result<PlacementRemovals, PlacementApplicationError> {
    // The caller hands over a copy it discards unless the whole application
    // succeeds, and it is the caller that writes the result back to the real
    // tree. Cloning again here bought nothing: the transactional property --
    // an early `return Err` leaves the emitted function untouched -- is the
    // caller's, not this function's.
    let candidate = &mut *function;
    let mut discarded_bindings = BTreeSet::new();
    let mut discarded_observations = BTreeSet::<RenderObservationId>::new();
    let mut declarations =
        BTreeMap::<RegionId, Vec<(BindingId, crate::ast::CType, crate::symbol::SymbolId)>>::new();
    let plan = names.plan();

    for (binding, decision) in decisions.iter() {
        let decision = demoted.get(&binding).copied().or(decision);
        let symbol = names
            .symbol_for_binding(binding)
            .ok_or(PlacementApplicationError::MissingBindingSymbol { binding })?;
        let binding_fact = plan
            .binding(binding)
            .ok_or(PlacementApplicationError::MissingBinding { binding })?;
        match decision {
            None => candidate.locals.retain(|local| local.name != symbol),
            Some(PlacementDecision::ExternallyDeclared) => {
                if !candidate.params.iter().any(|param| param.name == symbol) {
                    return Err(PlacementApplicationError::ExternalBindingMissingParameter {
                        binding,
                    });
                }
                candidate.locals.retain(|local| local.name != symbol);
            }
            Some(PlacementDecision::LexicalDeclaration { region }) => {
                candidate.locals.retain(|local| local.name != symbol);
                declarations.entry(region).or_default().push((
                    binding,
                    binding_fact.declaration_type().clone(),
                    symbol,
                ));
            }
            Some(PlacementDecision::DeadStore { region }) => {
                // The occurrence set records placement-relevant reads, which is
                // not the same as every mention: a read folded into another
                // expression leaves no occurrence but still names the symbol.
                // Dropping the declaration then emits an undeclared identifier,
                // which is the one thing this must never do, so the tree itself
                // is asked before anything is removed.
                let targets = binding_write_observations(writes, binding);
                if discarding_clears_symbol(&candidate.body, &targets, symbol) {
                    let mut removed_observations = BTreeSet::new();
                    for target in &targets {
                        discard_observed_statement(
                            &mut candidate.body,
                            *target,
                            &mut removed_observations,
                        );
                    }
                    candidate.locals.retain(|local| local.name != symbol);
                    discarded_bindings.insert(binding);
                    discarded_observations.append(&mut removed_observations);
                } else if function_body_mentions_symbol(&candidate.body, symbol)
                    && let Some(region) = region
                {
                    // The name survived the removal, so something reads the
                    // object without leaving a placement occurrence, and it is
                    // not dead after all. The trial is dropped -- every
                    // statement stays -- and the binding takes the declaration
                    // it would have had. Keeping the dead-store decision here
                    // would leave those statements naming a symbol nothing
                    // declares. A binding whose name is nowhere in the body is
                    // the ordinary dead store and still gets no declaration.
                    candidate.locals.retain(|local| local.name != symbol);
                    declarations.entry(region).or_default().push((
                        binding,
                        binding_fact.declaration_type().clone(),
                        symbol,
                    ));
                }
            }
            Some(PlacementDecision::Inline { write, .. }) => {
                candidate.locals.retain(|local| local.name != symbol);
                let matching = writes
                    .iter()
                    .filter(|occurrence| occurrence.binding == binding && occurrence.inst == write)
                    .collect::<Vec<_>>();
                let [occurrence] = matching.as_slice() else {
                    return Err(if matching.is_empty() {
                        PlacementApplicationError::MissingInlineWrite { inst: write }
                    } else {
                        PlacementApplicationError::DuplicateInlineWrite { inst: write }
                    });
                };
                let replacements = inline_exact_write(
                    &mut candidate.body,
                    occurrence.observation,
                    symbol,
                    binding_fact.declaration_type(),
                );
                if replacements != 1 {
                    return Err(if replacements == 0 {
                        PlacementApplicationError::MissingInlineWrite { inst: write }
                    } else {
                        PlacementApplicationError::DuplicateInlineWrite { inst: write }
                    });
                }
            }
            Some(PlacementDecision::Refused(reason)) => {
                return Err(PlacementApplicationError::Refused(reason));
            }
        }
    }

    // Deadness is transitive. Discarding a dead binding's statements discards
    // the reads they performed, which can leave another binding with no reader
    // at all -- an address temporary the stack-object rendering had already
    // replaced everywhere else, and behind it the stack pointer's own update,
    // which by then reads nothing but itself.
    //
    // This is the same rule the derivation applies, asked again once the tree
    // says something new, not a wider one: a binding is only reconsidered
    // because a removal took its last mention away, and it is still only
    // removed when the trial copy shows no mention survives discarding its own
    // writes.
    //
    // An inlined binding is reconsidered along with the rest. Inlining turns its
    // write into a declaration that carries the value, which is spoken for only
    // as long as something still reads it -- once the reader goes, what is left
    // is a declaration nothing consumes. Externally declared bindings are the
    // exception: a parameter is named by the signature and cannot be dropped
    // just because the body stopped mentioning it.
    loop {
        let reconsider = decisions
            .iter()
            .filter(|(binding, decision)| {
                !discarded_bindings.contains(binding)
                    && matches!(
                        decision,
                        None | Some(PlacementDecision::DeadStore { .. })
                            | Some(PlacementDecision::LexicalDeclaration { .. })
                            | Some(PlacementDecision::Inline { .. })
                    )
            })
            .collect::<Vec<_>>();
        let mut removed_any = false;
        for (binding, _) in reconsider {
            let Some(symbol) = names.symbol_for_binding(binding) else {
                continue;
            };
            if !function_body_mentions_symbol(&candidate.body, symbol) {
                // Nothing names it any more. Something this pass already
                // removed took its last mention with it -- a frame slot's
                // store, say, whose address was the only thing that read the
                // entry frame pointer -- and a declaration for an object the
                // body never mentions states nothing. `RBP_0` was left declared
                // and unused exactly this way.
                let was_declared = candidate.locals.iter().any(|local| local.name == symbol)
                    || declarations
                        .values()
                        .any(|declared| declared.iter().any(|(id, _, _)| *id == binding));
                if was_declared {
                    candidate.locals.retain(|local| local.name != symbol);
                    for declared in declarations.values_mut() {
                        declared.retain(|(declared, _, _)| *declared != binding);
                    }
                    discarded_bindings.insert(binding);
                    removed_any = true;
                }
                continue;
            }
            // The same bar the dead-store decision keeps: a statement whose
            // effect nothing else answers for is not removable, however unread
            // the object it writes.
            if writes
                .iter()
                .any(|write| write.binding == binding && write.effectful)
            {
                continue;
            }
            let targets = binding_write_observations(writes, binding);
            if !discarding_clears_symbol(&candidate.body, &targets, symbol) {
                continue;
            }
            let mut removed_observations = BTreeSet::new();
            for target in &targets {
                discard_observed_statement(&mut candidate.body, *target, &mut removed_observations);
            }
            candidate.locals.retain(|local| local.name != symbol);
            discarded_observations.append(&mut removed_observations);
            for declared in declarations.values_mut() {
                declared.retain(|(declared, _, _)| *declared != binding);
            }
            discarded_bindings.insert(binding);
            removed_any = true;
        }
        if !removed_any {
            break;
        }
    }

    // A trailing parameter the body never mentions is not one the function has.
    //
    // The slot list comes from radare2's argument detection, which counts a
    // register the function writes without ever reading: `xor edx, edx` at -O2
    // makes `edx` look like a third argument to `djb2`, which has two. Whether
    // any read of it survives is a fact about the emitted tree, so it is asked
    // here rather than assumed from the slot claim, and a strict compile
    // rejects the whole function over the unused parameter otherwise.
    //
    // Only from the end. Dropping a parameter from the middle would renumber
    // every slot after it, and the caller passes arguments by position.
    while let Some(last) = candidate.params.last() {
        if function_body_mentions_symbol(&candidate.body, last.name) {
            break;
        }
        candidate.params.pop();
    }

    for (region, declarations) in &mut declarations {
        declarations.sort_by_key(|(binding, _, _)| *binding);
        let statements = declarations
            .iter()
            .map(|(_, ty, name)| CStmt::Decl {
                ty: ty.clone(),
                name: *name,
                init: None,
            })
            .collect::<Vec<_>>();
        match insert_region_declarations(&mut candidate.body, regions, *region, &statements) {
            0 => return Err(PlacementApplicationError::MissingRegion { region: *region }),
            1 => {}
            _ => return Err(PlacementApplicationError::DuplicateRegion { region: *region }),
        }
    }

    Ok(PlacementRemovals {
        bindings: discarded_bindings,
        observations: discarded_observations,
    })
}

/// What applying the decisions actually removed.
///
/// Both halves are needed. The bindings say which writes lost their statements,
/// which is what the effect ledger keys on. The observations say which cells
/// those statements carried, which is the only way to reach a caller-supplied
/// value: it is version zero with no defining instruction, so no write answers
/// for it.
#[derive(Debug, Default)]
pub(crate) struct PlacementRemovals {
    pub(crate) bindings: BTreeSet<BindingId>,
    pub(crate) observations: BTreeSet<RenderObservationId>,
}

fn insert_region_declarations(
    statements: &mut [CStmt],
    regions: &SealedStructuredRegionArtifact,
    target: RegionId,
    declarations: &[CStmt],
) -> usize {
    statements
        .iter_mut()
        .map(|statement| {
            insert_region_declarations_in_stmt(statement, regions, target, declarations)
        })
        .sum()
}

fn insert_region_declarations_in_stmt(
    statement: &mut CStmt,
    regions: &SealedStructuredRegionArtifact,
    target: RegionId,
    declarations: &[CStmt],
) -> usize {
    if let CStmt::StructuredRegion { marker, stmt } = statement {
        let is_target = regions
            .node_for_marker(marker)
            .is_some_and(|(region, _)| region == target);
        if is_target {
            let semantic = std::mem::replace(stmt.as_mut(), CStmt::Empty);
            **stmt = match semantic {
                CStmt::Block(mut statements) => {
                    let mut placed = declarations.to_vec();
                    placed.append(&mut statements);
                    CStmt::Block(placed)
                }
                semantic => {
                    let mut placed = declarations.to_vec();
                    placed.push(semantic);
                    CStmt::Block(placed)
                }
            };
            return 1;
        }
        return insert_region_declarations_in_stmt(stmt, regions, target, declarations);
    }

    if let CStmt::Observed { stmt, .. } = statement {
        return insert_region_declarations_in_stmt(stmt, regions, target, declarations);
    }

    match statement {
        CStmt::StructuredRegion { .. } | CStmt::Observed { .. } => {
            unreachable!("leading wrappers handled above")
        }
        CStmt::Block(statements) => {
            insert_region_declarations(statements, regions, target, declarations)
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            insert_region_declarations_in_stmt(then_body, regions, target, declarations)
                + else_body.as_deref_mut().map_or(0, |body| {
                    insert_region_declarations_in_stmt(body, regions, target, declarations)
                })
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            insert_region_declarations_in_stmt(body, regions, target, declarations)
        }
        CStmt::For { init, body, .. } => {
            init.as_deref_mut().map_or(0, |init| {
                insert_region_declarations_in_stmt(init, regions, target, declarations)
            }) + insert_region_declarations_in_stmt(body, regions, target, declarations)
        }
        CStmt::Switch { cases, default, .. } => {
            let cases = cases
                .iter_mut()
                .map(|case| {
                    insert_region_declarations(&mut case.body, regions, target, declarations)
                })
                .sum::<usize>();
            cases
                + default.as_mut().map_or(0, |body| {
                    insert_region_declarations(body, regions, target, declarations)
                })
        }
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => 0,
    }
}

/// Replace one observed statement with nothing.
///
/// The markers go with it: the obligations they carried are filled in as elided
/// when the journal seals, which is the only point at which what the renderer
/// actually emitted is known.
/// Whether any statement still names this symbol.
fn function_body_mentions_symbol(statements: &[CStmt], symbol: crate::symbol::SymbolId) -> bool {
    statements
        .iter()
        .any(|statement| statement_mentions_symbol(statement, symbol))
}

fn statement_mentions_symbol(statement: &CStmt, symbol: crate::symbol::SymbolId) -> bool {
    match statement {
        CStmt::Observed { stmt, .. } | CStmt::StructuredRegion { stmt, .. } => {
            statement_mentions_symbol(stmt, symbol)
        }
        CStmt::Block(statements) => function_body_mentions_symbol(statements, symbol),
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => expr_mentions_symbol(expr, symbol),
        CStmt::Decl { name, init, .. } => {
            *name == symbol
                || init
                    .as_ref()
                    .is_some_and(|init| expr_mentions_symbol(init, symbol))
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            expr_mentions_symbol(cond, symbol)
                || statement_mentions_symbol(then_body, symbol)
                || else_body
                    .as_ref()
                    .is_some_and(|body| statement_mentions_symbol(body, symbol))
        }
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            expr_mentions_symbol(cond, symbol) || statement_mentions_symbol(body, symbol)
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            init.as_ref()
                .is_some_and(|init| statement_mentions_symbol(init, symbol))
                || cond
                    .as_ref()
                    .is_some_and(|c| expr_mentions_symbol(c, symbol))
                || update
                    .as_ref()
                    .is_some_and(|s| expr_mentions_symbol(s, symbol))
                || statement_mentions_symbol(body, symbol)
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            expr_mentions_symbol(expr, symbol)
                || cases
                    .iter()
                    .any(|case| function_body_mentions_symbol(&case.body, symbol))
                || default
                    .as_ref()
                    .is_some_and(|body| function_body_mentions_symbol(body, symbol))
        }
        _ => false,
    }
}

fn expr_mentions_symbol(expr: &CExpr, symbol: crate::symbol::SymbolId) -> bool {
    let mut found = false;
    expr.visit(&mut |node| {
        if matches!(node, CExpr::Var(name) if *name == symbol) {
            found = true;
        }
    });
    found
}

/// Every observation one binding's writes are marked on.
fn binding_write_observations(
    writes: &[FinalBindingWrite],
    binding: BindingId,
) -> BTreeSet<RenderObservationId> {
    writes
        .iter()
        .filter(|write| write.binding == binding)
        .map(|write| write.observation)
        .collect()
}

/// Whether discarding every statement `targets` names would leave the body
/// with no mention of `symbol`, and name at least one statement to discard.
///
/// This is the question a trial copy used to answer by cloning the whole
/// function, discarding into the copy and looking at the result -- once per
/// binding, so a render copied its entire AST as many times as it had
/// candidate dead stores. No copy is needed. `discard_observed_statement`
/// replaces a whole statement with `CStmt::Empty` and touches nothing else, so
/// the mentions that disappear are exactly those inside the statements
/// carrying a target, and a mention survives precisely when it lies outside
/// all of them.
///
/// Order does not enter into it, which is why one traversal can answer what a
/// sequence of discards would produce. Where one target's statement contains
/// another's, the outer takes the inner with it, so the union of removed
/// content is the same whichever is discarded first -- and the union is what
/// this asks about. The count differs by order, but the count is only ever
/// compared against zero, and at least one statement is emptied whenever any
/// carries a target.
fn discarding_clears_symbol(
    statements: &[CStmt],
    targets: &BTreeSet<RenderObservationId>,
    symbol: crate::symbol::SymbolId,
) -> bool {
    let mut probe = DiscardProbe::default();
    probe_discarded_body(statements, targets, symbol, &mut probe);
    probe.discards && !probe.survives
}

#[derive(Default)]
struct DiscardProbe {
    /// A statement carrying one of the targets was found, so discarding would
    /// remove something.
    discards: bool,
    /// A mention of the symbol lies outside every statement that would go.
    survives: bool,
}

/// Whether this statement is one `discard_observed_statement` would empty.
///
/// It mirrors that function's two reasons exactly: a marker on any of the
/// observation layers wrapping the statement, or a marker on the target of an
/// assignment, which is how a store into a stack object is marked.
fn statement_is_discarded(statement: &CStmt, targets: &BTreeSet<RenderObservationId>) -> bool {
    let mut current = statement;
    while let CStmt::Observed { id, stmt } = current {
        if targets.contains(id) {
            return true;
        }
        current = stmt;
    }
    matches!(
        current,
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            ..
        }) if expr_carries_any_observation(left, targets)
    )
}

/// Whether this expression is marked with any of the observations, at any of
/// the layers wrapping the expression itself.
fn expr_carries_any_observation(expr: &CExpr, targets: &BTreeSet<RenderObservationId>) -> bool {
    let mut current = expr;
    loop {
        match current {
            CExpr::Observed { id, expr } => {
                if targets.contains(id) {
                    return true;
                }
                current = expr;
            }
            _ => return false,
        }
    }
}

fn probe_discarded_body(
    statements: &[CStmt],
    targets: &BTreeSet<RenderObservationId>,
    symbol: crate::symbol::SymbolId,
    probe: &mut DiscardProbe,
) {
    for statement in statements {
        probe_discarded_statement(statement, targets, symbol, probe);
    }
}

/// Descends exactly the statement positions `discard_observed_statement`
/// descends, so the two agree about what a discard reaches.
fn probe_discarded_statement(
    statement: &CStmt,
    targets: &BTreeSet<RenderObservationId>,
    symbol: crate::symbol::SymbolId,
    probe: &mut DiscardProbe,
) {
    if statement_is_discarded(statement, targets) {
        probe.discards = true;
        return;
    }
    match statement.unobserved() {
        CStmt::StructuredRegion { stmt, .. } => {
            probe_discarded_statement(stmt, targets, symbol, probe);
        }
        CStmt::Block(statements) => probe_discarded_body(statements, targets, symbol, probe),
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            probe.survives |= expr_mentions_symbol(cond, symbol);
            probe_discarded_statement(then_body, targets, symbol, probe);
            if let Some(body) = else_body {
                probe_discarded_statement(body, targets, symbol, probe);
            }
        }
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            probe.survives |= expr_mentions_symbol(cond, symbol);
            probe_discarded_statement(body, targets, symbol, probe);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                probe_discarded_statement(init, targets, symbol, probe);
            }
            if let Some(cond) = cond {
                probe.survives |= expr_mentions_symbol(cond, symbol);
            }
            if let Some(update) = update {
                probe.survives |= expr_mentions_symbol(update, symbol);
            }
            probe_discarded_statement(body, targets, symbol, probe);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            probe.survives |= expr_mentions_symbol(expr, symbol);
            for case in cases {
                probe_discarded_body(&case.body, targets, symbol, probe);
            }
            if let Some(body) = default {
                probe_discarded_body(body, targets, symbol, probe);
            }
        }
        // Every remaining variant is a leaf as far as discarding is concerned:
        // it holds no statement a discard could reach, so its own mentions
        // survive.
        leaf => probe.survives |= statement_mentions_symbol(leaf, symbol),
    }
}

/// Discard the statement carrying `target`, recording every observation that
/// went with it.
///
/// A statement is removed whole, so the markers nested inside it are removed
/// too. Their cells would otherwise stay empty and the seal would refuse the
/// function for a value nothing rendered. Naming them here is what lets the
/// journal close out exactly what placement dropped, rather than closing out
/// whatever happens to be unaccounted -- which would answer the check instead
/// of answering to it.
fn discard_observed_statement(
    statements: &mut [CStmt],
    target: RenderObservationId,
    discarded: &mut BTreeSet<RenderObservationId>,
) -> usize {
    let mut removed = 0;
    for statement in statements.iter_mut() {
        removed += discard_observed_statement_in_stmt(statement, target, discarded);
    }
    removed
}

/// Whether this expression is marked with an observation, at any of the layers
/// wrapping the expression itself.
fn expr_carries_observation(expr: &CExpr, target: RenderObservationId) -> bool {
    let mut current = expr;
    loop {
        match current {
            CExpr::Observed { id, expr } => {
                if *id == target {
                    return true;
                }
                current = expr;
            }
            _ => return false,
        }
    }
}

fn discard_observed_statement_in_stmt(
    statement: &mut CStmt,
    target: RenderObservationId,
    discarded: &mut BTreeSet<RenderObservationId>,
) -> usize {
    if let CStmt::Observed { id, .. } = statement
        && *id == target
    {
        collect_statement_observations(statement, discarded);
        *statement = CStmt::Empty;
        return 1;
    }
    // A write is not always marked on the statement. A store into a stack
    // object is marked on the object expression the assignment writes to, so
    // the statement performing the write is the one whose assignment target
    // carries the mark. Looking only at statement markers found nothing to
    // discard for those, and a frame slot the function writes and never reads
    // survived as a variable that is set and not used.
    //
    // Only the assignment target. A mark anywhere else belongs to something the
    // statement reads, and removing the statement for it would discard a write
    // on the strength of a read.
    let assigns_target = matches!(
        statement.unobserved(),
        CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            ..
        }) if expr_carries_observation(left, target)
    );
    if assigns_target {
        collect_statement_observations(statement, discarded);
        *statement = CStmt::Empty;
        return 1;
    }
    match statement {
        CStmt::Observed { stmt, .. } | CStmt::StructuredRegion { stmt, .. } => {
            discard_observed_statement_in_stmt(stmt, target, discarded)
        }
        CStmt::Block(statements) => discard_observed_statement(statements, target, discarded),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            discard_observed_statement_in_stmt(then_body, target, discarded)
                + else_body.as_mut().map_or(0, |body| {
                    discard_observed_statement_in_stmt(body, target, discarded)
                })
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            discard_observed_statement_in_stmt(body, target, discarded)
        }
        CStmt::For { init, body, .. } => {
            init.as_mut().map_or(0, |init| {
                discard_observed_statement_in_stmt(init, target, discarded)
            }) + discard_observed_statement_in_stmt(body, target, discarded)
        }
        CStmt::Switch { cases, default, .. } => {
            cases
                .iter_mut()
                .map(|case| discard_observed_statement(&mut case.body, target, discarded))
                .sum::<usize>()
                + default.as_mut().map_or(0, |body| {
                    discard_observed_statement(body, target, discarded)
                })
        }
        _ => 0,
    }
}

fn inline_exact_write(
    statements: &mut [CStmt],
    target: RenderObservationId,
    symbol: crate::symbol::SymbolId,
    ty: &crate::ast::CType,
) -> usize {
    statements
        .iter_mut()
        .map(|statement| inline_exact_write_in_stmt(statement, target, symbol, ty))
        .sum()
}

fn inline_exact_write_in_stmt(
    statement: &mut CStmt,
    target: RenderObservationId,
    symbol: crate::symbol::SymbolId,
    ty: &crate::ast::CType,
) -> usize {
    if let CStmt::Observed { id, stmt } = statement {
        if *id == target {
            return usize::from(replace_assignment_with_declaration(stmt, symbol, ty));
        }
        return inline_exact_write_in_stmt(stmt, target, symbol, ty);
    }
    match statement {
        CStmt::StructuredRegion { stmt, .. } => {
            inline_exact_write_in_stmt(stmt, target, symbol, ty)
        }
        CStmt::Block(statements) => inline_exact_write(statements, target, symbol, ty),
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            inline_exact_write_in_stmt(then_body, target, symbol, ty)
                + else_body.as_deref_mut().map_or(0, |body| {
                    inline_exact_write_in_stmt(body, target, symbol, ty)
                })
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            inline_exact_write_in_stmt(body, target, symbol, ty)
        }
        CStmt::For { init, body, .. } => {
            init.as_deref_mut().map_or(0, |init| {
                inline_exact_write_in_stmt(init, target, symbol, ty)
            }) + inline_exact_write_in_stmt(body, target, symbol, ty)
        }
        CStmt::Switch { cases, default, .. } => {
            let cases = cases
                .iter_mut()
                .map(|case| inline_exact_write(&mut case.body, target, symbol, ty))
                .sum::<usize>();
            cases
                + default
                    .as_mut()
                    .map_or(0, |body| inline_exact_write(body, target, symbol, ty))
        }
        CStmt::Observed { .. } => unreachable!("leading observation handled above"),
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Decl { .. }
        | CStmt::Return(_)
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => 0,
    }
}

fn replace_assignment_with_declaration(
    statement: &mut CStmt,
    symbol: crate::symbol::SymbolId,
    ty: &crate::ast::CType,
) -> bool {
    if let CStmt::Observed { stmt, .. } = statement {
        return replace_assignment_with_declaration(stmt, symbol, ty);
    }
    let CStmt::Expr(CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        ..
    }) = statement
    else {
        return false;
    };
    if !matches!(left.unobserved(), CExpr::Var(name) if *name == symbol) {
        return false;
    }
    let CStmt::Expr(CExpr::Binary { right, .. }) = std::mem::replace(statement, CStmt::Empty)
    else {
        unreachable!("assignment shape was checked before move")
    };
    *statement = CStmt::Decl {
        ty: ty.clone(),
        name: symbol,
        init: Some(*right),
    };
    true
}

/// Derive all declaration decisions from canonical facts and final occurrences.
pub(crate) fn derive_placement_decisions(
    regions: &SealedStructuredRegionArtifact,
    function: &SSAFunction,
    binding_count: usize,
    externally_declared: &BTreeSet<BindingId>,
    entry_declared: &BTreeSet<BindingId>,
    reads: &[FinalBindingRead],
    writes: &[FinalBindingWrite],
) -> Result<PlacementDecisions, PlacementAnalysisError> {
    derive_with_cfg(
        regions,
        function,
        binding_count,
        externally_declared,
        entry_declared,
        reads,
        writes,
    )
}

trait PlacementControlFlow {
    fn entry(&self) -> u64;
    fn block_addrs(&self) -> Vec<u64>;
    fn predecessors(&self, block: u64) -> Vec<u64>;
    fn successors(&self, block: u64) -> Vec<u64>;
    fn dominates(&self, dominator: u64, block: u64) -> bool;
}

impl PlacementControlFlow for SSAFunction {
    fn entry(&self) -> u64 {
        self.entry
    }

    fn block_addrs(&self) -> Vec<u64> {
        SSAFunction::block_addrs(self).to_vec()
    }

    fn predecessors(&self, block: u64) -> Vec<u64> {
        SSAFunction::predecessors(self, block)
    }

    fn successors(&self, block: u64) -> Vec<u64> {
        SSAFunction::successors(self, block)
    }

    fn dominates(&self, dominator: u64, block: u64) -> bool {
        SSAFunction::dominates(self, dominator, block)
    }
}

fn derive_with_cfg<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    binding_count: usize,
    externally_declared: &BTreeSet<BindingId>,
    entry_declared: &BTreeSet<BindingId>,
    reads: &[FinalBindingRead],
    writes: &[FinalBindingWrite],
) -> Result<PlacementDecisions, PlacementAnalysisError> {
    let mut block_addrs = cfg.block_addrs();
    block_addrs.sort_unstable();
    block_addrs.dedup();
    let block_indices = block_addrs
        .iter()
        .copied()
        .enumerate()
        .map(|(index, block)| (block, index))
        .collect::<BTreeMap<_, _>>();

    if let Some(binding) = externally_declared
        .iter()
        .copied()
        .find(|binding| binding.index() >= binding_count)
    {
        return Err(PlacementAnalysisError::ExternalBindingOutsidePlan { binding });
    }

    for read in reads {
        validate_occurrence(
            regions,
            cfg,
            binding_count,
            &block_indices,
            read.binding,
            read.region,
            read.block,
        )?;
    }
    for write in writes {
        validate_occurrence(
            regions,
            cfg,
            binding_count,
            &block_indices,
            write.binding,
            write.region,
            write.block,
        )?;
    }

    let mut occurrences = vec![Vec::<Occurrence>::new(); binding_count];
    for read in reads {
        occurrences[read.binding.index()].push(Occurrence {
            region: read.region,
            block: read.block,
            order: read.order,
            kind: OccurrenceKind::Read(read.source),
        });
    }
    for write in writes {
        occurrences[write.binding.index()].push(Occurrence {
            region: write.region,
            block: write.block,
            order: write.order,
            kind: OccurrenceKind::Write {
                inst: write.inst,
                inline_eligible: write.inline_eligible,
            },
        });
    }
    for binding_occurrences in &mut occurrences {
        binding_occurrences.sort_by_key(Occurrence::sort_key);
    }

    // Both a parameter and a caller-supplied entry value hold a value when the
    // function starts, so both are already assigned on entry to the entry
    // block. Only where they are *declared* differs.
    let assigned_on_entry = externally_declared
        .union(entry_declared)
        .copied()
        .collect::<BTreeSet<_>>();
    let must_in = match must_assignment_inputs(
        cfg,
        binding_count,
        &block_addrs,
        &block_indices,
        &occurrences,
        &assigned_on_entry,
    ) {
        Ok(inputs) => inputs,
        Err(mismatch) => {
            return Ok(refuse_unprovable_binding_domain(binding_count, mismatch));
        }
    };
    let mut decisions = vec![None; binding_count];

    for (binding_index, binding_occurrences) in occurrences.iter().enumerate() {
        if binding_occurrences.is_empty() {
            continue;
        }
        let binding = BindingId::from_dense_index(binding_index)
            .expect("binding_count is already addressable by BindingId occurrences");
        let writes_for_binding = binding_occurrences
            .iter()
            .filter_map(|occurrence| match occurrence.kind {
                OccurrenceKind::Write {
                    inst,
                    inline_eligible,
                } => Some((occurrence, inst, inline_eligible)),
                OccurrenceKind::Read(_) => None,
            })
            .collect::<Vec<_>>();
        if externally_declared.contains(&binding) {
            decisions[binding_index] = Some(PlacementDecision::ExternallyDeclared);
            continue;
        }
        if writes_for_binding.is_empty() && !entry_declared.contains(&binding) {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::MissingDefinition { binding },
            ));
            continue;
        }

        // Nothing reads the object, so no declaration is owed and no statement
        // has to survive to assign it. The effect ledger answers separately for
        // anything those statements did besides producing this value, which is
        // what makes dropping them safe rather than a guess.
        if binding_occurrences
            .iter()
            .all(|occurrence| matches!(occurrence.kind, OccurrenceKind::Write { .. }))
            && !writes
                .iter()
                .any(|write| write.binding == binding && write.effectful)
        {
            decisions[binding_index] = Some(PlacementDecision::DeadStore {
                region: lowest_dominating_region(regions, cfg, binding_occurrences),
            });
            continue;
        }
        if !occurrence_regions_have_proven_order(regions, binding_occurrences) {
            r2il::refusal_evidence!(
                "occurrence-region-order",
                "binding={binding:?} occurrences={:?}",
                binding_occurrences
                    .iter()
                    .map(|occurrence| (
                        occurrence.block,
                        occurrence.region,
                        occurrence.order,
                        matches!(occurrence.kind, OccurrenceKind::Write { .. })
                            .then_some("write")
                            .unwrap_or("read"),
                    ))
                    .collect::<Vec<_>>()
            );
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::UnprovableExecutionOrder { binding },
            ));
            continue;
        }

        if let Some(read) =
            first_read_before_assignment(binding, binding_occurrences, &must_in, &block_indices)
        {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::ReadBeforeAssignment { binding, read },
            ));
            continue;
        }

        let Some(region) = lowest_dominating_region(regions, cfg, binding_occurrences) else {
            decisions[binding_index] = Some(PlacementDecision::Refused(
                PlacementRefusal::NoDominatingRegion { binding },
            ));
            continue;
        };

        if let [(write, inst, inline_eligible)] = writes_for_binding.as_slice()
            && *inline_eligible
            && binding_occurrences.iter().all(|occurrence| {
                matches!(occurrence.kind, OccurrenceKind::Write { .. })
                    || (write.order <= occurrence.order
                        && cfg.dominates(write.block, occurrence.block))
            })
        {
            decisions[binding_index] = Some(PlacementDecision::Inline {
                write: *inst,
                region,
            });
        } else {
            decisions[binding_index] = Some(PlacementDecision::LexicalDeclaration { region });
        }
    }

    Ok(PlacementDecisions {
        decisions: decisions.into_boxed_slice(),
    })
}

/// Whether the regions a block's occurrences of one binding fall in are ordered
/// well enough for a block-granular assignment proof to hold.
///
/// One machine block can be rendered more than once -- the structured form
/// duplicates a shared tail rather than jumping to it -- and then two
/// occurrences of one binding carry the same block address while sitting in
/// regions that are not nested. The read-before-assignment proof reasons per
/// block, so it cannot tell the copies apart, and requiring the regions to nest
/// is what kept it sound.
///
/// A copy that assigns the object before it reads it needs nothing from any
/// other copy, so where it sits relative to them cannot make a read precede an
/// assignment. Where every copy is self-contained in that sense there is no
/// ordering question to answer. A comparator whose two `return` tails each
/// place their own constant in the result register is the case: four
/// occurrences, two blocks, each block written then read in both of its copies.
fn occurrence_regions_have_proven_order(
    regions: &SealedStructuredRegionArtifact,
    occurrences: &[Occurrence],
) -> bool {
    let mut by_block = BTreeMap::<u64, BTreeMap<RegionId, Vec<&Occurrence>>>::new();
    for occurrence in occurrences {
        by_block
            .entry(occurrence.block)
            .or_default()
            .entry(occurrence.region)
            .or_default()
            .push(occurrence);
    }
    by_block.values().all(|block_regions| {
        let self_contained = |region_occurrences: &Vec<&Occurrence>| {
            region_occurrences
                .iter()
                .min_by_key(|occurrence| occurrence.order)
                .is_some_and(|first| matches!(first.kind, OccurrenceKind::Write { .. }))
        };
        if block_regions.values().all(self_contained) {
            return true;
        }
        block_regions.keys().all(|left| {
            block_regions.keys().all(|right| {
                region_is_ancestor(regions, *left, *right)
                    || region_is_ancestor(regions, *right, *left)
            })
        })
    })
}

fn region_is_ancestor(
    regions: &SealedStructuredRegionArtifact,
    ancestor: RegionId,
    mut region: RegionId,
) -> bool {
    loop {
        if region == ancestor {
            return true;
        }
        let Some(parent) = regions.node(region).and_then(|node| node.parent()) else {
            return false;
        };
        region = parent;
    }
}

fn validate_occurrence<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    binding_count: usize,
    block_indices: &BTreeMap<u64, usize>,
    binding: BindingId,
    region: RegionId,
    block: u64,
) -> Result<(), PlacementAnalysisError> {
    if binding.index() >= binding_count {
        return Err(PlacementAnalysisError::BindingOutsidePlan { binding });
    }
    let Some(node) = regions.node(region) else {
        return Err(PlacementAnalysisError::RegionOutsideArtifact { region });
    };
    if !block_indices.contains_key(&block) {
        return Err(PlacementAnalysisError::BlockOutsideFunction { block });
    }
    if !cfg.dominates(node.entry(), block) {
        return Err(PlacementAnalysisError::RegionDoesNotDominateOccurrence { region, block });
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Occurrence {
    region: RegionId,
    block: u64,
    order: FinalOccurrenceOrder,
    kind: OccurrenceKind,
}

impl Occurrence {
    fn sort_key(&self) -> (FinalOccurrenceOrder, u8, u64, usize, u32, usize) {
        match self.kind {
            OccurrenceKind::Read(PlacementRead::Use(site)) => (
                self.order,
                0,
                self.block,
                self.region.index(),
                site.inst.0,
                site.input_idx,
            ),
            OccurrenceKind::Read(PlacementRead::CertifiedValue { value, at }) => (
                self.order,
                0,
                self.block,
                self.region.index(),
                at.0,
                value.0 as usize,
            ),
            OccurrenceKind::Read(
                PlacementRead::StackAccess(access) | PlacementRead::IndexedStackAccess(access),
            ) => (
                self.order,
                0,
                self.block,
                self.region.index(),
                access.inst.0,
                access.ordinal as usize,
            ),
            OccurrenceKind::Read(PlacementRead::PreservedCarrierWrite(inst)) => {
                (self.order, 0, self.block, self.region.index(), inst.0, 0)
            }
            OccurrenceKind::Write { inst, .. } => {
                (self.order, 1, self.block, self.region.index(), inst.0, 0)
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OccurrenceKind {
    Read(PlacementRead),
    Write { inst: InstId, inline_eligible: bool },
}

fn lowest_dominating_region<C: PlacementControlFlow + ?Sized>(
    regions: &SealedStructuredRegionArtifact,
    cfg: &C,
    occurrences: &[Occurrence],
) -> Option<RegionId> {
    let mut candidate = occurrences.first()?.region;
    for occurrence in &occurrences[1..] {
        candidate = lowest_common_ancestor(regions, candidate, occurrence.region)?;
    }

    loop {
        let node = regions.node(candidate)?;
        if occurrences
            .iter()
            .all(|occurrence| cfg.dominates(node.entry(), occurrence.block))
        {
            return Some(candidate);
        }
        candidate = node.parent()?;
    }
}

fn lowest_common_ancestor(
    regions: &SealedStructuredRegionArtifact,
    mut left: RegionId,
    mut right: RegionId,
) -> Option<RegionId> {
    let mut left_depth = regions.node(left)?.depth();
    let mut right_depth = regions.node(right)?.depth();
    while left_depth > right_depth {
        left = regions.node(left)?.parent()?;
        left_depth -= 1;
    }
    while right_depth > left_depth {
        right = regions.node(right)?.parent()?;
        right_depth -= 1;
    }
    while left != right {
        left = regions.node(left)?.parent()?;
        right = regions.node(right)?.parent()?;
    }
    Some(left)
}

fn first_read_before_assignment(
    binding: BindingId,
    occurrences: &[Occurrence],
    must_in: &[DenseBindingSet],
    block_indices: &BTreeMap<u64, usize>,
) -> Option<PlacementRead> {
    let mut by_rendered_block = BTreeMap::<u64, Vec<&Occurrence>>::new();
    for occurrence in occurrences {
        by_rendered_block
            .entry(occurrence.block)
            .or_default()
            .push(occurrence);
    }

    for (block, mut block_occurrences) in by_rendered_block {
        block_occurrences.sort_by_key(|occurrence| occurrence.sort_key());
        let block_index = block_indices[&block];
        let mut assigned = must_in[block_index].contains(binding);
        for occurrence in block_occurrences {
            match occurrence.kind {
                OccurrenceKind::Read(PlacementRead::IndexedStackAccess(_)) => {}
                OccurrenceKind::Read(read) if !assigned => return Some(read),
                OccurrenceKind::Read(_) => {}
                OccurrenceKind::Write { .. } => assigned = true,
            }
        }
    }
    None
}

/// A malformed dense-set domain invalidates the must-assignment proof for the
/// whole binding domain. Refuse every binding so no caller can accidentally
/// consume a partial `zip` result as a placement proof.
fn refuse_unprovable_binding_domain(
    binding_count: usize,
    _mismatch: DenseBindingDomainMismatch,
) -> PlacementDecisions {
    let decisions = (0..binding_count)
        .map(|index| {
            let binding = BindingId::from_dense_index(index)
                .expect("binding_count was already accepted as a dense BindingId domain");
            Some(PlacementDecision::Refused(
                PlacementRefusal::UnprovableExecutionOrder { binding },
            ))
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    PlacementDecisions { decisions }
}

fn must_assignment_inputs<C: PlacementControlFlow + ?Sized>(
    cfg: &C,
    binding_count: usize,
    block_addrs: &[u64],
    block_indices: &BTreeMap<u64, usize>,
    occurrences: &[Vec<Occurrence>],
    externally_declared: &BTreeSet<BindingId>,
) -> Result<Vec<DenseBindingSet>, DenseBindingDomainMismatch> {
    let mut generated = vec![DenseBindingSet::empty(binding_count); block_addrs.len()];
    for (binding_index, binding_occurrences) in occurrences.iter().enumerate() {
        let binding = BindingId::from_dense_index(binding_index)
            .expect("binding occurrence index fits BindingId");
        for occurrence in binding_occurrences {
            if matches!(occurrence.kind, OccurrenceKind::Write { .. }) {
                generated[block_indices[&occurrence.block]].insert(binding)?;
            }
        }
    }

    let mut inputs = vec![DenseBindingSet::all(binding_count); block_addrs.len()];
    let mut outputs = vec![DenseBindingSet::all(binding_count); block_addrs.len()];
    let mut worklist = (0..block_addrs.len()).collect::<BTreeSet<_>>();
    while let Some(block_index) = worklist.pop_first() {
        let block = block_addrs[block_index];
        let mut predecessors = cfg.predecessors(block);
        predecessors.sort_unstable();
        predecessors.dedup();
        let next_input = if block == cfg.entry() {
            DenseBindingSet::from_bindings(binding_count, externally_declared)?
        } else if predecessors.is_empty() {
            DenseBindingSet::empty(binding_count)
        } else {
            let first = predecessors.remove(0);
            let mut intersection = outputs[block_indices[&first]].clone();
            for predecessor in predecessors {
                intersection.intersect_with(&outputs[block_indices[&predecessor]])?;
            }
            intersection
        };
        let mut next_output = next_input.clone();
        next_output.union_with(&generated[block_index])?;
        let output_changed = next_output != outputs[block_index];
        inputs[block_index] = next_input;
        outputs[block_index] = next_output;
        if output_changed {
            let mut successors = cfg.successors(block);
            successors.sort_unstable();
            successors.dedup();
            for successor in successors {
                worklist.insert(block_indices[&successor]);
            }
        }
    }
    Ok(inputs)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DenseBindingDomainMismatch;

#[derive(Debug, Clone, PartialEq, Eq)]
struct DenseBindingSet {
    words: Vec<u64>,
    binding_count: usize,
}

impl DenseBindingSet {
    fn empty(binding_count: usize) -> Self {
        Self {
            words: vec![0; binding_count.div_ceil(u64::BITS as usize)],
            binding_count,
        }
    }

    fn all(binding_count: usize) -> Self {
        let mut set = Self {
            words: vec![u64::MAX; binding_count.div_ceil(u64::BITS as usize)],
            binding_count,
        };
        if let Some(last) = set.words.last_mut() {
            let used = binding_count % u64::BITS as usize;
            if used != 0 {
                *last &= (1_u64 << used) - 1;
            }
        }
        set
    }

    fn from_bindings(
        binding_count: usize,
        bindings: &BTreeSet<BindingId>,
    ) -> Result<Self, DenseBindingDomainMismatch> {
        let mut set = Self::empty(binding_count);
        for binding in bindings {
            set.insert(*binding)?;
        }
        Ok(set)
    }

    fn contains(&self, binding: BindingId) -> bool {
        let index = binding.index();
        index < self.binding_count
            && self.words[index / u64::BITS as usize] & (1_u64 << (index % u64::BITS as usize)) != 0
    }

    fn insert(&mut self, binding: BindingId) -> Result<(), DenseBindingDomainMismatch> {
        let index = binding.index();
        if index >= self.binding_count {
            return Err(DenseBindingDomainMismatch);
        }
        self.words[index / u64::BITS as usize] |= 1_u64 << (index % u64::BITS as usize);
        Ok(())
    }

    fn intersect_with(&mut self, other: &Self) -> Result<(), DenseBindingDomainMismatch> {
        self.validate_domain(other)?;
        for (left, right) in self.words.iter_mut().zip(&other.words) {
            *left &= *right;
        }
        Ok(())
    }

    fn union_with(&mut self, other: &Self) -> Result<(), DenseBindingDomainMismatch> {
        self.validate_domain(other)?;
        for (left, right) in self.words.iter_mut().zip(&other.words) {
            *left |= *right;
        }
        Ok(())
    }

    fn validate_domain(&self, other: &Self) -> Result<(), DenseBindingDomainMismatch> {
        if self.binding_count == other.binding_count && self.words.len() == other.words.len() {
            Ok(())
        } else {
            Err(DenseBindingDomainMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::Region;
    use crate::structured_region::{
        StructuredRegionDraft, StructuredRegionKind, StructuredRegionMarker,
        seal_structured_body_for_test as seal_structured_body,
    };
    use crate::symbol::{SymbolRole, SymbolTable};

    fn observation(index: u32) -> RenderObservationId {
        crate::observation_journal::test_render_observation_id(index)
    }

    #[test]
    fn dense_binding_sets_refuse_mismatched_domains_without_partial_mutation() {
        let binding = BindingId::from_dense_index(0).expect("binding");
        let mut one_binding = DenseBindingSet::empty(1);
        one_binding.insert(binding).expect("in-domain binding");
        let two_bindings = DenseBindingSet::all(2);
        let original = one_binding.clone();
        let mismatch = DenseBindingDomainMismatch;

        assert_eq!(one_binding.intersect_with(&two_bindings), Err(mismatch));
        assert_eq!(one_binding, original);
        assert_eq!(one_binding.union_with(&two_bindings), Err(mismatch));
        assert_eq!(one_binding, original);
        assert_eq!(
            one_binding.insert(BindingId::from_dense_index(1).expect("binding")),
            Err(mismatch)
        );
        assert_eq!(one_binding, original);
    }

    #[test]
    fn invalid_dense_domain_refuses_every_placement_binding() {
        let decisions = refuse_unprovable_binding_domain(2, DenseBindingDomainMismatch);
        for index in 0..2 {
            let binding = BindingId::from_dense_index(index).expect("binding");
            assert_eq!(
                decisions.decision(binding),
                Some(PlacementDecision::Refused(
                    PlacementRefusal::UnprovableExecutionOrder { binding },
                ))
            );
        }
    }

    #[derive(Debug)]
    struct TestCfg {
        entry: u64,
        successors: BTreeMap<u64, Vec<u64>>,
        predecessors: BTreeMap<u64, Vec<u64>>,
        dominators: BTreeMap<u64, BTreeSet<u64>>,
    }

    impl TestCfg {
        fn new(entry: u64, edges: &[(u64, u64)]) -> Self {
            let mut blocks = BTreeSet::from([entry]);
            let mut successors = BTreeMap::<u64, Vec<u64>>::new();
            let mut predecessors = BTreeMap::<u64, Vec<u64>>::new();
            for &(from, to) in edges {
                blocks.extend([from, to]);
                successors.entry(from).or_default().push(to);
                predecessors.entry(to).or_default().push(from);
            }
            for block in &blocks {
                successors.entry(*block).or_default().sort_unstable();
                predecessors.entry(*block).or_default().sort_unstable();
            }

            let mut dominators = blocks
                .iter()
                .map(|block| {
                    let set = if *block == entry {
                        BTreeSet::from([entry])
                    } else {
                        blocks.clone()
                    };
                    (*block, set)
                })
                .collect::<BTreeMap<_, _>>();
            loop {
                let mut changed = false;
                for block in blocks.iter().copied().filter(|block| *block != entry) {
                    let preds = &predecessors[&block];
                    let mut next = if let Some(first) = preds.first() {
                        dominators[first].clone()
                    } else {
                        BTreeSet::new()
                    };
                    for predecessor in preds.iter().skip(1) {
                        next = next
                            .intersection(&dominators[predecessor])
                            .copied()
                            .collect();
                    }
                    next.insert(block);
                    if next != dominators[&block] {
                        dominators.insert(block, next);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            Self {
                entry,
                successors,
                predecessors,
                dominators,
            }
        }
    }

    impl PlacementControlFlow for TestCfg {
        fn entry(&self) -> u64 {
            self.entry
        }

        fn block_addrs(&self) -> Vec<u64> {
            self.successors.keys().copied().collect()
        }

        fn predecessors(&self, block: u64) -> Vec<u64> {
            self.predecessors[&block].clone()
        }

        fn successors(&self, block: u64) -> Vec<u64> {
            self.successors[&block].clone()
        }

        fn dominates(&self, dominator: u64, block: u64) -> bool {
            self.dominators[&block].contains(&dominator)
        }
    }

    fn diamond_regions() -> SealedStructuredRegionArtifact {
        let region = Region::Sequence(vec![
            Region::IfThenElse {
                cond_block: 0x1000,
                then_region: Box::new(Region::Block(0x1010)),
                else_region: Some(Box::new(Region::Block(0x1020))),
                merge_block: Some(0x1030),
            },
            Region::Block(0x1030),
        ]);
        StructuredRegionDraft::from_region(0x1000, &region)
            .expect("diamond region")
            .seal()
    }

    fn region_with_entry(
        regions: &SealedStructuredRegionArtifact,
        entry: u64,
        kind: StructuredRegionKind,
    ) -> RegionId {
        let index = regions
            .nodes()
            .iter()
            .position(|node| node.entry() == entry && node.kind() == kind)
            .expect("region entry");
        regions
            .node_for_anchor(
                regions.authority(),
                regions.nodes()[index].emission_anchor(),
            )
            .expect("dense region")
            .0
    }

    fn diamond_cfg() -> TestCfg {
        TestCfg::new(
            0x1000,
            &[
                (0x1000, 0x1010),
                (0x1000, 0x1020),
                (0x1010, 0x1030),
                (0x1020, 0x1030),
            ],
        )
    }

    #[test]
    fn diamond_with_both_arms_assigned_places_one_lexical_declaration() {
        let regions = diamond_regions();
        let cfg = diamond_cfg();
        let binding = BindingId::from_dense_index(0).expect("binding");
        let then_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let else_region = region_with_entry(&regions, 0x1020, StructuredRegionKind::Block);
        let merge_region = region_with_entry(&regions, 0x1030, StructuredRegionKind::Block);
        let writes = [
            FinalBindingWrite {
                effectful: false,
                binding,
                inst: InstId(1),
                region: then_region,
                block: 0x1010,
                order: FinalOccurrenceOrder(1),
                observation: observation(1),
                inline_eligible: true,
            },
            FinalBindingWrite {
                effectful: false,
                binding,
                inst: InstId(2),
                region: else_region,
                block: 0x1020,
                order: FinalOccurrenceOrder(2),
                observation: observation(2),
                inline_eligible: true,
            },
        ];
        let reads = [FinalBindingRead {
            binding,
            source: PlacementRead::Use(UseSite {
                inst: InstId(3),
                input_idx: 0,
            }),
            region: merge_region,
            block: 0x1030,
            order: FinalOccurrenceOrder(3),
        }];

        let decisions = derive_with_cfg(
            &regions,
            &cfg,
            1,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &reads,
            &writes,
        )
        .expect("placement");
        let sequence = regions.source_root();
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::LexicalDeclaration { region: sequence })
        );
    }

    #[test]
    fn diamond_with_one_arm_unassigned_refuses_merge_read() {
        let regions = diamond_regions();
        let cfg = diamond_cfg();
        let binding = BindingId::from_dense_index(0).expect("binding");
        let then_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let merge_region = region_with_entry(&regions, 0x1030, StructuredRegionKind::Block);
        let site = UseSite {
            inst: InstId(3),
            input_idx: 0,
        };
        let writes = [FinalBindingWrite {
            effectful: false,
            binding,
            inst: InstId(1),
            region: then_region,
            block: 0x1010,
            order: FinalOccurrenceOrder(1),
            observation: observation(1),
            inline_eligible: true,
        }];
        let reads = [FinalBindingRead {
            binding,
            source: PlacementRead::Use(site),
            region: merge_region,
            block: 0x1030,
            order: FinalOccurrenceOrder(2),
        }];

        let decisions = derive_with_cfg(
            &regions,
            &cfg,
            1,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &reads,
            &writes,
        )
        .expect("placement");
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::Refused(
                PlacementRefusal::ReadBeforeAssignment {
                    binding,
                    read: PlacementRead::Use(site),
                }
            ))
        );
    }

    #[test]
    fn inserted_carrier_write_reads_before_its_same_occurrence_write() {
        let region = Region::Block(0x1000);
        let regions = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("single block region")
            .seal();
        let cfg = TestCfg::new(0x1000, &[]);
        let binding = BindingId::from_dense_index(0).expect("binding");
        let block_region = region_with_entry(&regions, 0x1000, StructuredRegionKind::Block);
        let inst = InstId(0);
        let order = FinalOccurrenceOrder(0);
        let reads = [FinalBindingRead {
            binding,
            source: PlacementRead::PreservedCarrierWrite(inst),
            region: block_region,
            block: 0x1000,
            order,
        }];
        let writes = [FinalBindingWrite {
            effectful: false,
            binding,
            inst,
            region: block_region,
            block: 0x1000,
            order,
            observation: observation(0),
            inline_eligible: true,
        }];

        let decisions = derive_with_cfg(
            &regions,
            &cfg,
            1,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &reads,
            &writes,
        )
        .expect("typed placement result");
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::Refused(
                PlacementRefusal::ReadBeforeAssignment {
                    binding,
                    read: PlacementRead::PreservedCarrierWrite(inst),
                }
            ))
        );
    }

    #[test]
    fn one_dominating_write_is_inlined_at_its_exact_assignment() {
        let region = Region::Sequence(vec![Region::Block(0x1000), Region::Block(0x1010)]);
        let regions = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("linear region")
            .seal();
        let cfg = TestCfg::new(0x1000, &[(0x1000, 0x1010)]);
        let binding = BindingId::from_dense_index(0).expect("binding");
        let write_region = region_with_entry(&regions, 0x1000, StructuredRegionKind::Block);
        let read_region = region_with_entry(&regions, 0x1010, StructuredRegionKind::Block);
        let write = InstId(1);
        let decisions = derive_with_cfg(
            &regions,
            &cfg,
            1,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &[FinalBindingRead {
                binding,
                source: PlacementRead::Use(UseSite {
                    inst: InstId(2),
                    input_idx: 0,
                }),
                region: read_region,
                block: 0x1010,
                order: FinalOccurrenceOrder(2),
            }],
            &[FinalBindingWrite {
                effectful: false,
                binding,
                inst: write,
                region: write_region,
                block: 0x1000,
                order: FinalOccurrenceOrder(1),
                observation: observation(1),
                inline_eligible: true,
            }],
        )
        .expect("placement");

        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::Inline {
                write,
                // The fallback the inline carries if the emitted tree turns out
                // to put its declaration out of scope: the lowest region that
                // dominates both the write and the read.
                region: lowest_common_ancestor(&regions, write_region, read_region)
                    .expect("common ancestor"),
            })
        );
    }

    #[test]
    fn certified_parameter_read_uses_entry_assignment_without_a_local() {
        let region = Region::Block(0x1000);
        let regions = StructuredRegionDraft::from_region(0x1000, &region)
            .expect("parameter region")
            .seal();
        let cfg = TestCfg::new(0x1000, &[]);
        let binding = BindingId::from_dense_index(0).expect("binding");
        let block_region = region_with_entry(&regions, 0x1000, StructuredRegionKind::Block);
        let reads = [FinalBindingRead {
            binding,
            source: PlacementRead::Use(UseSite {
                inst: InstId(0),
                input_idx: 0,
            }),
            region: block_region,
            block: 0x1000,
            order: FinalOccurrenceOrder(0),
        }];

        let decisions = derive_with_cfg(
            &regions,
            &cfg,
            1,
            &BTreeSet::from([binding]),
            &BTreeSet::new(),
            &reads,
            &[],
        )
        .expect("parameter placement");
        assert_eq!(
            decisions.decision(binding),
            Some(PlacementDecision::ExternallyDeclared)
        );

        let uncertified = derive_with_cfg(
            &regions,
            &cfg,
            1,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &reads,
            &[],
        )
        .expect("uncertified placement");
        assert_eq!(
            uncertified.decision(binding),
            Some(PlacementDecision::Refused(
                PlacementRefusal::MissingDefinition { binding }
            ))
        );
    }

    #[test]
    fn exact_region_insertion_uses_the_sealed_anchor_not_the_block_address() {
        let repeated_entry = CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::Block(vec![
                CStmt::structured_region(
                    StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::Block),
                    CStmt::comment("first"),
                ),
                CStmt::structured_region(
                    StructuredRegionMarker::unsealed(0x1010, StructuredRegionKind::Block),
                    CStmt::comment("second"),
                ),
            ]),
        );
        let sealed = seal_structured_body(repeated_entry).expect("sealed occurrences");
        let target = sealed
            .regions()
            .node_for_anchor(
                sealed.regions().authority(),
                sealed.regions().nodes()[2].emission_anchor(),
            )
            .expect("second occurrence")
            .0;
        let (statement, regions) = sealed.into_marked_parts();
        let mut statements = vec![statement];
        let declaration = CStmt::comment("declaration");

        assert_eq!(
            insert_region_declarations(&mut statements, &regions, target, &[declaration]),
            1
        );
        let CStmt::StructuredRegion { stmt: root, .. } = &statements[0] else {
            panic!("function marker")
        };
        let CStmt::Block(children) = root.as_ref() else {
            panic!("function body")
        };
        let CStmt::StructuredRegion { stmt: first, .. } = &children[0] else {
            panic!("first marker")
        };
        let CStmt::StructuredRegion { stmt: second, .. } = &children[1] else {
            panic!("second marker")
        };
        assert!(!format!("{first:?}").contains("declaration"));
        assert!(format!("{second:?}").contains("declaration"));
    }

    #[test]
    fn inline_replaces_only_the_exact_marked_assignment() {
        let symbols = std::rc::Rc::new(std::cell::RefCell::new(SymbolTable::new()));
        let symbol = symbols.borrow_mut().declare(
            "value",
            crate::ast::CType::Int {
                bits: 32,
                signedness: r2types::Signedness::Unsigned,
            },
            SymbolRole::Carrier,
        );
        let marker = observation(7);
        let assignment = CStmt::observed(
            marker,
            CStmt::expr(CExpr::assign(CExpr::Var(symbol), CExpr::UIntLit(9))),
        );
        let mut statements = vec![assignment, CStmt::comment("untouched")];

        assert_eq!(
            inline_exact_write(
                &mut statements,
                marker,
                symbol,
                &crate::ast::CType::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Unsigned
                },
            ),
            1
        );
        assert!(matches!(
            statements[0].unobserved(),
            CStmt::Decl {
                name,
                init: Some(CExpr::UIntLit(9)),
                ..
            } if *name == symbol
        ));
    }

    #[test]
    fn final_scope_order_matches_do_while_execution() {
        let body_id = observation(0);
        let condition_id = observation(1);
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::DoWhile {
                body: Box::new(CStmt::observed(body_id, CStmt::Empty)),
                cond: CExpr::observed(condition_id, CExpr::UIntLit(1)),
            },
        ))
        .expect("sealed do-while");
        let (statement, regions) = sealed.into_marked_parts();
        let targets = vec![Some(PlacementObservationTarget::Other); 2];
        let scopes = collect_final_observation_scopes(&[statement], &regions, &targets);
        let order_of = |index| match scopes[index] {
            Some(FinalObservationScope::Exact { order, .. }) => order,
            other => panic!("expected exact scope, got {other:?}"),
        };
        assert!(order_of(0) < order_of(1));
    }

    #[test]
    fn final_scope_order_matches_for_execution_phases() {
        let init_id = observation(0);
        let condition_id = observation(1);
        let body_id = observation(2);
        let update_id = observation(3);
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::For {
                init: Some(Box::new(CStmt::observed(init_id, CStmt::Empty))),
                cond: Some(CExpr::observed(condition_id, CExpr::UIntLit(1))),
                update: Some(CExpr::observed(update_id, CExpr::UIntLit(0))),
                body: Box::new(CStmt::observed(body_id, CStmt::Empty)),
            },
        ))
        .expect("sealed for");
        let (statement, regions) = sealed.into_marked_parts();
        let targets = vec![Some(PlacementObservationTarget::Other); 4];
        let scopes = collect_final_observation_scopes(&[statement], &regions, &targets);
        let order_of = |index| match scopes[index] {
            Some(FinalObservationScope::Exact { order, .. }) => order,
            other => panic!("expected exact scope, got {other:?}"),
        };
        assert!(order_of(0) < order_of(1));
        assert!(order_of(1) < order_of(2));
        assert!(order_of(2) < order_of(3));
    }

    #[test]
    fn final_scope_sequences_comma_reads_output_write_and_later_read() {
        let operand_read = observation(0);
        let output_write = observation(1);
        let later_read = observation(2);
        let expression = CExpr::Comma(vec![
            CExpr::observed(
                output_write,
                CExpr::observed(operand_read, CExpr::UIntLit(1)),
            ),
            CExpr::observed(later_read, CExpr::UIntLit(2)),
        ]);
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::Expr(expression),
        ))
        .expect("sealed comma expression");
        let (statement, regions) = sealed.into_marked_parts();
        let targets = [
            Some(PlacementObservationTarget::Use {
                site: UseSite {
                    inst: InstId(0),
                    input_idx: 0,
                },
                block: 0x1000,
            }),
            Some(PlacementObservationTarget::Write {
                inst: InstId(1),
                projection: r2ssa::MachineWriteProjection::Full,
                block: 0x1000,
            }),
            Some(PlacementObservationTarget::Use {
                site: UseSite {
                    inst: InstId(2),
                    input_idx: 0,
                },
                block: 0x1000,
            }),
        ];
        let scopes = collect_final_observation_scopes(&[statement], &regions, &targets);
        let order_of = |index| match scopes[index] {
            Some(FinalObservationScope::Exact { order, .. }) => order,
            other => panic!("expected exact scope, got {other:?}"),
        };

        assert!(order_of(0) < order_of(1));
        assert!(order_of(1) < order_of(2));
    }

    #[test]
    fn final_scope_refuses_alternative_write_phase() {
        let branch_write = observation(0);
        let competing_read = observation(1);
        let expression = CExpr::Ternary {
            cond: Box::new(CExpr::UIntLit(1)),
            then_expr: Box::new(CExpr::observed(branch_write, CExpr::UIntLit(2))),
            else_expr: Box::new(CExpr::observed(competing_read, CExpr::UIntLit(3))),
        };
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::Expr(expression),
        ))
        .expect("sealed alternative expression");
        let (statement, regions) = sealed.into_marked_parts();
        let targets = [
            Some(PlacementObservationTarget::Write {
                inst: InstId(0),
                projection: r2ssa::MachineWriteProjection::Full,
                block: 0x1000,
            }),
            Some(PlacementObservationTarget::Use {
                site: UseSite {
                    inst: InstId(1),
                    input_idx: 0,
                },
                block: 0x1000,
            }),
        ];
        let scopes = collect_final_observation_scopes(&[statement], &regions, &targets);

        assert_eq!(scopes[0], Some(FinalObservationScope::Ambiguous));
        assert_eq!(scopes[1], Some(FinalObservationScope::Ambiguous));
    }

    #[test]
    fn final_scope_refuses_unsequenced_write_phase() {
        let operand_write = observation(0);
        let competing_read = observation(1);
        let expression = CExpr::binary(
            BinaryOp::Add,
            CExpr::observed(operand_write, CExpr::UIntLit(1)),
            CExpr::observed(competing_read, CExpr::UIntLit(2)),
        );
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::Expr(expression),
        ))
        .expect("sealed unsequenced expression");
        let (statement, regions) = sealed.into_marked_parts();
        let targets = [
            Some(PlacementObservationTarget::Write {
                inst: InstId(0),
                projection: r2ssa::MachineWriteProjection::Full,
                block: 0x1000,
            }),
            Some(PlacementObservationTarget::Use {
                site: UseSite {
                    inst: InstId(1),
                    input_idx: 0,
                },
                block: 0x1000,
            }),
        ];
        let scopes = collect_final_observation_scopes(&[statement], &regions, &targets);

        assert_eq!(scopes[0], Some(FinalObservationScope::Ambiguous));
        assert_eq!(scopes[1], Some(FinalObservationScope::Ambiguous));
    }

    #[test]
    fn final_scope_sequences_direct_stack_assignment_after_its_value() {
        let stack_write = observation(0);
        let elided_address_use = observation(1);
        let value_read = observation(2);
        let symbols = std::rc::Rc::new(std::cell::RefCell::new(SymbolTable::new()));
        let symbol = symbols.borrow_mut().declare(
            "stack_m16",
            crate::ast::CType::Int {
                bits: 32,
                signedness: r2types::Signedness::Unsigned,
            },
            SymbolRole::StackLocal(-16),
        );
        let expression = CExpr::assign(
            CExpr::observed(
                elided_address_use,
                CExpr::observed(stack_write, CExpr::Var(symbol)),
            ),
            CExpr::observed(value_read, CExpr::UIntLit(7)),
        );
        let sealed = seal_structured_body(CStmt::structured_region(
            StructuredRegionMarker::unsealed(0x1000, StructuredRegionKind::FunctionBody),
            CStmt::Expr(expression),
        ))
        .expect("sealed stack assignment");
        let (statement, regions) = sealed.into_marked_parts();
        let binding = BindingId::from_dense_index(0).expect("binding");
        let targets = [
            Some(PlacementObservationTarget::StackAccess {
                access: r2ssa::StructuredAccessId {
                    inst: InstId(0),
                    ordinal: 0,
                },
                object: r2ssa::ObjectId(0),
                binding,
                symbol,
                is_write: true,
            }),
            Some(PlacementObservationTarget::Other),
            Some(PlacementObservationTarget::Use {
                site: UseSite {
                    inst: InstId(0),
                    input_idx: 0,
                },
                block: 0x1000,
            }),
        ];
        let scopes = collect_final_observation_scopes(&[statement], &regions, &targets);
        let order_of = |index| match scopes[index] {
            Some(FinalObservationScope::Exact { order, .. }) => order,
            other => panic!("expected exact scope, got {other:?}"),
        };

        assert!(order_of(2) < order_of(0));
        assert_eq!(scopes[1], None);
    }
}
