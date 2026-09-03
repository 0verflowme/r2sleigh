use std::cell::Cell;
#[cfg(test)]
use std::cell::OnceCell;
#[cfg(test)]
use std::collections::HashMap;
use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
use std::sync::OnceLock;

use crate::analysis;
use crate::ast::{CExpr, CType};
use r2ssa::{BlockId, InstId, SemanticObligationId, SsaArtifact, UseSite, ValueId};
use r2types::{CalleeFact, CalleeResolutionFacts, FunctionFacts};
#[cfg(test)]
use r2types::{ExternalStackSlotSpec, StackSlotKey, VisibleBinding};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EffectOccurrenceKind {
    Expression,
    MemoryRead,
    MemoryWrite,
    Return,
}

#[derive(Debug, Clone)]
pub(crate) struct FoldArchConfig {
    pub(crate) ptr_size: u32,
    pub(crate) arg_regs: Vec<String>,
}

#[derive(Clone, Copy)]
pub(crate) struct FoldInputs<'a> {
    pub(crate) arch: &'a FoldArchConfig,
    #[cfg(test)]
    pub(crate) function_names: &'a HashMap<u64, String>,
    #[cfg(test)]
    /// What the binary calls the thing at an address, not a name this
    /// rendering declares.
    pub(crate) binary_symbols: &'a HashMap<u64, String>,
    pub(crate) function_facts: &'a FunctionFacts,
    #[cfg(test)]
    pub(crate) stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    #[cfg(test)]
    pub(crate) visible_bindings: &'a [VisibleBinding],
    pub(crate) function_return_type: Option<&'a CType>,
    pub(crate) prepared_ssa: Option<&'a SsaArtifact>,
    /// Sole `BindingId -> SymbolId` projection for this native rendering.
    pub(crate) binding_names: Option<&'a std::rc::Rc<crate::binding_plan::BindingNameResolution>>,
    pub(crate) prepared_semantic_view: Option<&'a analysis::PreparedSemanticView>,
    /// Exact origin of every operation in the normalized function.
    pub(crate) normalization_origins: Option<&'a crate::normalize::NormalizationOrigins>,
    /// Sole authority-bound observation journal for this native rendering.
    /// Test and residual-only folds deliberately carry no journal.
    pub(crate) observation_journal:
        Option<&'a std::cell::RefCell<crate::observation_journal::LegacyObservationJournal>>,
}

impl<'a> FoldInputs<'a> {
    pub(crate) fn callee_facts(&self) -> &'a BTreeMap<u64, CalleeFact> {
        &self.function_facts.type_facts().callee_facts
    }

    pub(crate) fn callee_resolution(&self) -> Option<&'a CalleeResolutionFacts> {
        self.function_facts.callee_resolution()
    }

    pub(crate) fn callsite_facts(&self) -> Option<&'a r2types::FunctionCallsiteFacts> {
        self.function_facts.callsites()
    }

    pub(crate) fn call_result_facts(&self) -> Option<&'a r2types::FunctionCallResultFacts> {
        self.function_facts.call_results()
    }

    pub(crate) fn call_render_facts(&self) -> Option<&'a r2types::FunctionCallRenderFacts> {
        self.function_facts.call_render()
    }

    pub(crate) fn control_facts(&self) -> Option<&'a r2types::FunctionControlFacts> {
        self.function_facts.control()
    }

    pub(crate) fn render_facts(&self) -> Option<&'a r2types::FunctionRenderFacts> {
        self.function_facts.render()
    }
}

#[cfg(test)]
pub(crate) fn empty_function_facts() -> &'static FunctionFacts {
    static EMPTY_FUNCTION_FACTS: OnceLock<FunctionFacts> = OnceLock::new();
    EMPTY_FUNCTION_FACTS.get_or_init(FunctionFacts::default)
}

#[derive(Debug, Clone, Default)]
pub(crate) struct FoldState {
    pub(crate) analysis_ctx: analysis::DecompilerFacts,
}

/// Internal executable-folding state.
///
/// Public callers must enter through [`crate::DecompilerInput`], which retains
/// the exact source-owned facts for its prepared SSA. Raw SSA exports use the
/// residual-only [`crate::fold::lower_ssa_ops_to_stmts`] boundary instead.
///
/// ```compile_fail
/// let _ = r2dec::fold::FoldingContext::new(64);
/// ```
pub(crate) struct FoldingContext<'a> {
    pub(crate) inputs: FoldInputs<'a>,
    pub(crate) state: FoldState,
    pub(crate) current_block_addr: Cell<Option<u64>>,
    pub(crate) current_block_id: Cell<Option<BlockId>>,
    /// Where each name is defined in the block being walked.
    ///
    /// Finding a definition by scanning the block costs one pass per question,
    /// so a block with many definitions costs the square of its size. One pass
    /// answers every question about that block, and it is rebuilt when the walk
    /// moves on.
    pub(crate) current_op_idx: Cell<Option<usize>>,
    /// Set while an operation is lowered to stand as an expression at the place
    /// its result is read, rather than as its own statement.
    ///
    /// Statement lowering spells a left-hand side before it builds the
    /// right-hand side, and an inlined value has no left-hand side to spell --
    /// the binding plan gave it no symbol precisely because it is written
    /// nowhere. Under this flag the left-hand side is not asked for and the
    /// assignment collapses to the expression alone, so both forms come out of
    /// one body and cannot drift apart.
    pub(crate) inlined_definition: Cell<bool>,
    /// What the right-hand side of the assignment being lowered has.
    ///
    /// The operation's lowering states it when it spells the assignment,
    /// and the finaliser reads it when it applies the write projection and
    /// the conversion to the declared object, which happen after the
    /// statement has been built. One transaction sets and takes it.
    pub(crate) pending_assignment_type: Cell<Option<r2rewrite::CValue>>,
    /// Legacy cache retained only as a negative test fixture: production
    /// inlining is authorized exclusively by the sealed binding plan.
    ///
    /// Leaving a statement out is a promise that the reader will show the value
    /// instead. The promise used to be made by one rule and kept by another, and
    /// when they disagreed the reader printed the value's name and nothing
    /// defined it. The expression the skipped statement would have carried is
    /// recorded here as it is skipped, so the rule that decides and the rule that
    /// renders are reading the same answer.
    #[cfg(test)]
    pub(crate) inlined_renderings: std::cell::RefCell<HashMap<String, CExpr>>,
    #[cfg(test)]
    pub(crate) prepared_semantic_view_cache: OnceCell<analysis::PreparedSemanticView>,
    /// Blocks the fold walked, which is what expresses a merge standing at their head.
    pub(crate) folded_blocks: std::cell::RefCell<std::collections::BTreeSet<u64>>,
    /// A prototype for each function this rendering calls, keyed by the name
    /// the call spells, collected while the calls are lowered because that is
    /// where the callee's interface is in hand. Handed to the function when it
    /// is built.
    pub(crate) callee_declarations:
        std::cell::RefCell<std::collections::BTreeMap<String, crate::ast::CExternDecl>>,
    /// Names minted while folding, handed to the function when it is built.
    ///
    /// A cell because the builders take `&self`. Minting has to borrow, insert
    /// and drop inside one statement: a borrow held across a nested build would
    /// panic, and nested builds are the ordinary case here.
    /// The names this rendering declares, shared with whatever else renders
    /// the same function. An identifier only means something in the table that
    /// issued it, so the passes cannot each hold a copy.
    pub(crate) symbols: std::rc::Rc<std::cell::RefCell<crate::symbol::SymbolTable>>,
    /// First exact-observation failure. Lowering is largely `Option`-based, so
    /// marker issuance records the typed failure here and the native boundary
    /// retains it in the non-consuming audit while emitting the same marker-free
    /// native program.
    pub(crate) observation_error:
        std::cell::RefCell<Option<crate::observation_journal::LegacyObservationJournalError>>,
    /// Transaction-local lowering failure. Legacy helpers are still mostly
    /// expression-returning, so an exact projection failure records this flag
    /// and the operation boundary discards the whole candidate AST.
    pub(crate) pending_lowering_refusal: Cell<Option<crate::fold::op_lower::OpLoweringRefusal>>,
}

impl FoldArchConfig {
    #[cfg(test)]
    pub(crate) fn for_ptr_size(ptr_size: u32) -> Self {
        let arg_regs = if ptr_size == 64 {
            vec![
                "rdi".to_string(),
                "rsi".to_string(),
                "rdx".to_string(),
                "rcx".to_string(),
                "r8".to_string(),
                "r9".to_string(),
            ]
        } else {
            vec![]
        };
        Self { ptr_size, arg_regs }
    }
}

impl<'a> FoldingContext<'a> {
    pub(crate) fn from_inputs(inputs: FoldInputs<'a>) -> Self {
        Self {
            symbols: std::rc::Rc::new(std::cell::RefCell::new(crate::symbol::SymbolTable::new())),
            inputs,
            state: FoldState::default(),
            current_block_addr: Cell::new(None),
            current_block_id: Cell::new(None),
            current_op_idx: Cell::new(None),
            inlined_definition: Cell::new(false),
            pending_assignment_type: Cell::new(None),
            #[cfg(test)]
            inlined_renderings: std::cell::RefCell::new(HashMap::new()),
            #[cfg(test)]
            prepared_semantic_view_cache: OnceCell::new(),
            folded_blocks: std::cell::RefCell::new(std::collections::BTreeSet::new()),
            callee_declarations: std::cell::RefCell::new(std::collections::BTreeMap::new()),
            observation_error: std::cell::RefCell::new(None),
            pending_lowering_refusal: Cell::new(None),
        }
    }

    pub(crate) fn normalized_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<crate::normalize::NormalizedOpSite> {
        let block = self
            .inputs
            .prepared_ssa?
            .graph()
            .block_id_for_addr(block_addr)?;
        Some(crate::normalize::NormalizedOpSite { block, op_idx })
    }

    fn observation_site(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Result<
        crate::normalize::NormalizedOpSite,
        crate::observation_journal::LegacyObservationJournalError,
    > {
        self.normalized_site(block_addr, op_idx).ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedBlock(
                block_addr,
            ),
        )
    }

    pub(super) fn retain_first_observation_error(
        &self,
        error: crate::observation_journal::LegacyObservationJournalError,
    ) {
        if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
            eprintln!("OBSERVATION_ERROR {error:?}");
        }
        let mut first = self.observation_error.borrow_mut();
        if first.is_none() {
            *first = Some(error);
        }
    }

    /// Store the first refusal this fold decided, and say where.
    ///
    /// A stored refusal is raised later by whoever finishes the transaction, so
    /// it does not pass through any of the propagation paths and instrumenting
    /// those never finds it. This is the only place it can be caught, which is
    /// why the location is captured here rather than left to be rediscovered.
    #[track_caller]
    pub(super) fn retain_first_lowering_refusal(
        &self,
        refusal: crate::fold::op_lower::OpLoweringRefusal,
    ) {
        if self.pending_lowering_refusal.get().is_none() {
            if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                eprintln!(
                    "refusal {refusal:?} retained at {}",
                    std::panic::Location::caller()
                );
            }
            self.pending_lowering_refusal.set(Some(refusal));
        }
    }

    /// Materialize one cached fold as a distinct final-AST occurrence.
    ///
    /// Folding is stateful and must not be replayed merely to obtain fresh
    /// diagnostic identities. The journal duplicates its own authority-bound
    /// targets; on allocation failure the semantic clone survives marker-free
    /// and the typed audit failure is retained.
    pub(crate) fn clone_cached_render_occurrence(
        &self,
        stmts: &[crate::ast::CStmt],
    ) -> Vec<crate::ast::CStmt> {
        let Some(journal) = self.inputs.observation_journal else {
            return stmts.to_vec();
        };
        let fallback = stmts
            .iter()
            .map(crate::ast::CStmt::clone_without_render_observations)
            .collect();
        match journal.borrow_mut().clone_render_occurrence(stmts) {
            Ok(clone) => clone,
            Err(error) => {
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    pub(crate) fn observe_optional_normalized_input_value_expr(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        input_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        let Some(journal) = self.inputs.observation_journal else {
            return expr;
        };
        let Some(site) = site else {
            self.retain_first_observation_error(
                crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
            );
            return expr;
        };
        let fallback = expr.clone();
        match journal
            .borrow_mut()
            .observe_normalized_input_value_expr(site, input_idx, expr)
        {
            Ok(marked) => marked,
            Err(error) => {
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    pub(crate) fn observe_optional_normalized_input_uses_expr(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        input_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        let Some(journal) = self.inputs.observation_journal else {
            return expr;
        };
        let Some(site) = site else {
            self.retain_first_observation_error(
                crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
            );
            return expr;
        };
        let fallback = expr.clone();
        match journal
            .borrow_mut()
            .observe_normalized_input_uses_expr(site, input_idx, expr)
        {
            Ok(marked) => marked,
            Err(error) => {
                r2il::refusal_evidence!("input-use-observation", "{error:?} at {site:?}");
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    /// The obligations a definition carries, asked of the source instruction
    /// rather than of a normalized site.
    ///
    /// A definition rendered where its value is read has no normalized site of
    /// its own to ask about, and its obligations are otherwise never requested
    /// at all, which the ledger scores as refused.
    pub(crate) fn exact_effect_obligations_for_source_inst(
        &self,
        kind: EffectOccurrenceKind,
        source_inst: r2ssa::InstId,
        value: Option<ValueId>,
    ) -> BTreeSet<SemanticObligationId> {
        self.exact_value_obligations(kind, source_inst, value.as_slice())
    }

    /// Mark every cell the instructions a rendered expression discharges still
    /// owe, and the effects they answered for.
    ///
    /// Nothing asks a statement that is not emitted for its obligations, and
    /// the ledger scores an obligation nobody asked about as refused; so the
    /// effects move with the expression, exactly as its cells do.
    pub(crate) fn observe_discharged_expr(
        &self,
        value: r2ssa::ValueId,
        discharged: &[r2ssa::InstId],
        expr: CExpr,
    ) -> CExpr {
        let Some(journal) = self.inputs.observation_journal else {
            return expr;
        };
        let fallback = expr.clone();
        let marked = match journal
            .borrow_mut()
            .observe_discharged_expr(value, discharged, expr)
        {
            Ok(marked) => marked,
            Err(error) => {
                if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                    eprintln!(
                        "could not mark discharged value {value:?} definitions={discharged:?}: {error:?}"
                    );
                }
                self.retain_first_observation_error(error);
                return fallback;
            }
        };
        let mut obligations = BTreeSet::new();
        for definition in discharged {
            let output = self
                .inputs
                .prepared_ssa
                .and_then(|prepared| prepared.graph().inst(*definition))
                .and_then(|inst| inst.output);
            obligations.extend(self.exact_effect_obligations_for_source_inst(
                EffectOccurrenceKind::Expression,
                *definition,
                output,
            ));
        }
        self.observe_effect_expr(&obligations, marked)
    }

    /// Mark the value an inlined expression produces.
    pub(crate) fn observe_inlined_value_expr(&self, value: r2ssa::ValueId, expr: CExpr) -> CExpr {
        let Some(journal) = self.inputs.observation_journal else {
            return expr;
        };
        let fallback = expr.clone();
        match journal.borrow_mut().observe_inlined_value_expr(value, expr) {
            Ok(marked) => marked,
            Err(error) => {
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    pub(crate) fn observe_certified_value_read_expr(
        &self,
        value: r2ssa::ValueId,
        at: r2ssa::InstId,
        expr: CExpr,
    ) -> CExpr {
        let Some(journal) = self.inputs.observation_journal else {
            return expr;
        };
        let fallback = expr.clone();
        let Some(symbol) = self
            .inputs
            .binding_names
            .and_then(|names| names.symbol_for_value(value))
        else {
            self.retain_first_observation_error(
                crate::observation_journal::LegacyObservationJournalError::RenderedValueRequired(
                    value,
                ),
            );
            return fallback;
        };
        match journal
            .borrow_mut()
            .observe_certified_value_read_expr(value, at, symbol, expr)
        {
            Ok(marked) => marked,
            Err(error) => {
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    /// Wrap one exact normalized definition that survives as a statement.
    pub(crate) fn observe_normalized_output_stmt(
        &self,
        block_addr: u64,
        op_idx: usize,
        stmt: crate::ast::CStmt,
    ) -> crate::ast::CStmt {
        let Some(journal) = self.inputs.observation_journal else {
            return stmt;
        };
        let fallback = stmt.clone();
        let result = self.observation_site(block_addr, op_idx).and_then(|site| {
            journal
                .borrow_mut()
                .observe_normalized_output_stmt(site, stmt)
        });
        match result {
            Ok(marked) => marked,
            Err(error) => {
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    /// Attach exact source-effect cells to the statement occurrence that
    /// discharges them. No construction-time side table participates: if this
    /// statement is deleted, its markers are deleted with it.
    pub(crate) fn observe_effect_stmt(
        &self,
        obligation_ids: &BTreeSet<SemanticObligationId>,
        stmt: crate::ast::CStmt,
    ) -> crate::ast::CStmt {
        let Some(journal) = self.inputs.observation_journal else {
            return stmt;
        };
        if obligation_ids.is_empty() {
            return stmt;
        }
        let fallback = stmt.clone();
        match journal
            .borrow_mut()
            .observe_effect_stmt(obligation_ids, stmt)
        {
            Ok(marked) => marked,
            Err(error) => {
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    /// Expression twin of [`Self::observe_effect_stmt`].
    pub(crate) fn observe_effect_expr(
        &self,
        obligation_ids: &BTreeSet<SemanticObligationId>,
        expr: CExpr,
    ) -> CExpr {
        let Some(journal) = self.inputs.observation_journal else {
            return expr;
        };
        if obligation_ids.is_empty() {
            return expr;
        }
        let fallback = expr.clone();
        match journal
            .borrow_mut()
            .observe_effect_expr(obligation_ids, expr)
        {
            Ok(marked) => marked,
            Err(error) => {
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    /// O(1) origin lookup once the caller holds the normalized block's dense id.
    pub(crate) fn source_inst_for_normalized_site(
        &self,
        site: crate::normalize::NormalizedOpSite,
    ) -> Option<InstId> {
        if let Some(origins) = self.inputs.normalization_origins {
            return match origins.origin(site)? {
                crate::normalize::NormalizedOpOrigin::Original(inst) => Some(*inst),
                crate::normalize::NormalizedOpOrigin::PhiEdgeCopy(_)
                | crate::normalize::NormalizedOpOrigin::RelocatedInitializer(_) => None,
            };
        }

        // A context without normalization origins is walking the unchanged
        // source function (principally focused unit tests). This is not a
        // fallback for a malformed normalized artifact: once an origins table
        // is supplied, only `Original` rows above can reach source facts.
        let graph = self.inputs.prepared_ssa?.graph();
        let block = graph.block(site.block)?;
        graph.inst_id_for_op_site(block.addr, site.op_idx)
    }

    pub(crate) fn source_inst_for_normalized_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<InstId> {
        self.source_inst_for_normalized_site(self.normalized_site(block_addr, op_idx)?)
    }

    pub(crate) fn source_op_site_for_normalized_op(
        &self,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<(u64, usize)> {
        if self.inputs.normalization_origins.is_none() {
            return Some((block_addr, op_idx));
        }
        let inst = self.source_inst_for_normalized_op(block_addr, op_idx)?;
        self.inputs.prepared_ssa?.inst_op_site(inst)
    }

    pub(crate) fn current_source_op_site(&self) -> Option<(u64, usize)> {
        let block_addr = self.current_block_addr.get()?;
        let op_idx = self.current_op_idx.get()?;
        if let Some(block) = self.current_block_id.get() {
            let inst =
                self.source_inst_for_normalized_site(crate::normalize::NormalizedOpSite {
                    block,
                    op_idx,
                })?;
            return self.inputs.prepared_ssa?.inst_op_site(inst);
        }
        self.source_op_site_for_normalized_op(block_addr, op_idx)
    }

    pub(crate) fn is_unconditional_materialized_phi_edge_copy(
        &self,
        block_addr: u64,
        op_idx: usize,
        successor: u64,
    ) -> bool {
        let Some(site) = self.normalized_site(block_addr, op_idx) else {
            return false;
        };
        self.inputs
            .normalization_origins
            .is_some_and(|origins| origins.is_unconditional_phi_edge_copy(site, successor))
    }

    /// Takes every value the occurrence carries, because a return can carry
    /// more than one: a composed ABI register is a base with ordered overlays
    /// laid over it, and each of them is seeded as its own obligation.
    fn exact_value_obligations(
        &self,
        kind: EffectOccurrenceKind,
        source_inst: InstId,
        values: &[ValueId],
    ) -> BTreeSet<SemanticObligationId> {
        use r2ssa::SemanticObligationKind as ObligationKind;

        // Every occurrence but a composed return carries at most one value,
        // and the rules below are written about that one.
        let value: Option<ValueId> = match values {
            [single] => Some(*single),
            _ => None,
        };
        let Some(prepared) = self.inputs.prepared_ssa else {
            return BTreeSet::new();
        };
        let Some(inst) = prepared.graph().inst(source_inst) else {
            return BTreeSet::new();
        };
        let source_site = prepared.inst_op_site(source_inst);
        let call_fact = source_site.and_then(|(block_addr, op_idx)| {
            self.inputs
                .call_render_facts()?
                .fact_for_site(r2types::CallsiteKey {
                    block_addr,
                    op_index: op_idx,
                })
        });
        // A return is certified when the plan says which value it carries, and
        // also when the source says it carries none.
        //
        // Only the first was asked, so a function returning nothing could not
        // discharge its own `Return` obligation: no return-value fact exists for
        // a void boundary, and none ever will. The obligation was scored
        // unaccounted and the function refused for the one statement it had
        // certainly rendered. A complete boundary with no values and no
        // compositions is the source's own statement that the return carries
        // nothing, which is exactly what `return;` renders.
        let void_return = values.is_empty()
            && prepared
                .facts()
                .boundaries
                .returns
                .get(&source_inst)
                .is_some_and(|boundary| {
                    boundary.at == source_inst
                        && boundary.complete
                        && boundary.values.is_empty()
                        && boundary.register_compositions.is_empty()
                });
        let return_certified = void_return
            || source_site
                .and_then(|(block_addr, op_idx)| {
                    self.inputs
                        .render_facts()?
                        .return_for_op(block_addr, op_idx)
                })
                .is_some_and(|fact| fact.values().eq(values.iter().copied()));
        let rendered_call = call_fact.filter(|fact| {
            !matches!(
                fact.disposition,
                r2types::CallsiteRenderDisposition::Suppressed
                    | r2types::CallsiteRenderDisposition::Residualized
            )
        });
        // Every carried value owns exactly one return-value obligation. A
        // composed return discharges all of them at the one expression that
        // reassembles it, so a value whose obligation is ambiguous disqualifies
        // the whole occurrence rather than being silently dropped from it.
        // One return-value obligation carries the whole composition, with every
        // value it is assembled from as its ordered inputs -- not one
        // obligation per value, which is what this first assumed and what the
        // ledger disproved: `inputs=[ValueId(11), ValueId(32)]` on a single
        // obligation. A composed return discharges that one obligation at the
        // one expression that reassembles it.
        let unique_return_value = !values.is_empty()
            && prepared
                .obligations()
                .obligations_for_inst(source_inst)
                .filter(|obligation| {
                    obligation.id.kind == ObligationKind::ReturnValue
                        && obligation.inputs.as_slice() == values
                })
                .count()
                == 1;
        let unique_call_result = value.is_some_and(|value| {
            prepared
                .obligations()
                .obligations_for_inst(source_inst)
                .filter(|obligation| {
                    obligation.id.kind == ObligationKind::CallResult && obligation.inputs == [value]
                })
                .count()
                == 1
        });

        let mut obligation_ids = BTreeSet::new();
        for obligation in prepared.obligations().obligations_for_inst(source_inst) {
            let exact = match kind {
                EffectOccurrenceKind::Return => {
                    return_certified
                        && (obligation.id.kind == ObligationKind::Return
                            || (obligation.id.kind == ObligationKind::ReturnValue
                                && unique_return_value
                                && obligation.inputs.as_slice() == values))
                }
                EffectOccurrenceKind::Expression => match &inst.payload {
                    r2ssa::InstPayload::Op(
                        r2ssa::SSAOp::Branch { .. } | r2ssa::SSAOp::BranchInd { .. },
                    ) => obligation.id.kind == ObligationKind::ControlTransfer,
                    r2ssa::InstPayload::Op(r2ssa::SSAOp::CBranch { .. }) => matches!(
                        obligation.id.kind,
                        ObligationKind::ControlPredicate | ObligationKind::ControlTransfer
                    ),
                    r2ssa::InstPayload::Op(
                        r2ssa::SSAOp::Call { .. } | r2ssa::SSAOp::CallInd { .. },
                    ) => {
                        if obligation.id.kind == ObligationKind::CallArgument
                            && obligation.inputs.is_empty()
                        {
                            r2il::refusal_evidence!(
                                "call-argument-occurrence",
                                "component={:?} has no inputs, so no rendering can discharge it; \
                                 rendered_call={} proof_values={:?}",
                                obligation.id.component,
                                rendered_call.is_some(),
                                rendered_call.map(|fact| fact.proof_values.clone())
                            );
                        }
                        rendered_call.is_some()
                            && (obligation.id.kind == ObligationKind::Call
                                || (obligation.id.kind == ObligationKind::CallArgument
                                    && !obligation.inputs.is_empty()
                                    && obligation.inputs.iter().all(|input| {
                                        rendered_call
                                            .is_some_and(|fact| fact.proof_values.contains(input))
                                    }))
                                || (obligation.id.kind == ObligationKind::CallResult
                                    && unique_call_result
                                    && obligation.inputs.as_slice() == value.as_slice()))
                    }
                    r2ssa::InstPayload::Op(
                        r2ssa::SSAOp::IntDiv { .. }
                        | r2ssa::SSAOp::IntSDiv { .. }
                        | r2ssa::SSAOp::IntRem { .. }
                        | r2ssa::SSAOp::IntSRem { .. },
                    ) => {
                        inst.output == value
                            && matches!(
                                obligation.id.kind,
                                ObligationKind::LiveValueProducer | ObligationKind::Trap
                            )
                    }
                    // A trap renders as the statement that takes it --
                    // `__builtin_trap()` -- and that statement produces no
                    // value, so the occurrence carries none either. Without
                    // this arm the trap fell to the value-producer case below,
                    // which no valueless statement can satisfy, and every
                    // function containing a guard instruction was refused for
                    // an effect it had in fact rendered.
                    r2ssa::InstPayload::Op(r2ssa::SSAOp::Breakpoint) => {
                        obligation.id.kind == ObligationKind::Trap && inst.output == value
                    }
                    _ => {
                        obligation.id.kind == ObligationKind::LiveValueProducer
                            && inst.output == value
                    }
                },
                EffectOccurrenceKind::MemoryRead | EffectOccurrenceKind::MemoryWrite => false,
            };
            if exact {
                obligation_ids.insert(obligation.id);
            }
        }
        obligation_ids
    }

    fn exact_effect_obligations_for_phi_edges(
        &self,
        definition: InstId,
        sites: &[UseSite],
    ) -> BTreeSet<SemanticObligationId> {
        use r2ssa::{SemanticObligationComponent, SemanticObligationKind};

        let Some(prepared) = self.inputs.prepared_ssa else {
            return BTreeSet::new();
        };
        let graph = prepared.graph();
        let mut obligation_ids = BTreeSet::new();
        for site in sites {
            for obligation in prepared.obligations().obligations_for_inst(definition) {
                if obligation.id.kind == SemanticObligationKind::LiveStateTransition
                    && matches!(
                        obligation.id.component,
                        SemanticObligationComponent::LoopTransition { .. }
                    )
                    && obligation.edge_use == Some(*site)
                    && obligation.inputs
                        == graph
                            .inst(site.inst)
                            .and_then(|inst| inst.inputs.get(site.input_idx))
                            .copied()
                            .into_iter()
                            .collect::<Vec<_>>()
                {
                    obligation_ids.insert(obligation.id);
                }
            }
        }
        obligation_ids
    }

    /// Exact source obligations discharged by one normalized value
    /// occurrence. Synthetic phi copies project only their named original
    /// edge obligations; ordinary operations project only their source InstId.
    pub(crate) fn exact_effect_obligations_for_normalized_value(
        &self,
        kind: EffectOccurrenceKind,
        block_addr: u64,
        op_idx: usize,
        value: Option<ValueId>,
    ) -> BTreeSet<SemanticObligationId> {
        self.exact_effect_obligations_for_normalized_values(
            kind,
            block_addr,
            op_idx,
            value.as_slice(),
        )
    }

    /// The occurrence carries several values, which only a composed return
    /// does: its ABI register is a base with ordered overlays laid over it and
    /// every one of them owns an obligation the single expression discharges.
    pub(crate) fn exact_effect_obligations_for_normalized_values(
        &self,
        kind: EffectOccurrenceKind,
        block_addr: u64,
        op_idx: usize,
        values: &[ValueId],
    ) -> BTreeSet<SemanticObligationId> {
        let Some(site) = self.normalized_site(block_addr, op_idx) else {
            return BTreeSet::new();
        };
        let Some(origins) = self.inputs.normalization_origins else {
            return self
                .source_inst_for_normalized_site(site)
                .map(|inst| self.exact_value_obligations(kind, inst, values))
                .unwrap_or_default();
        };
        match origins.origin(site) {
            Some(crate::normalize::NormalizedOpOrigin::Original(inst)) => {
                self.exact_value_obligations(kind, *inst, values)
            }
            Some(crate::normalize::NormalizedOpOrigin::PhiEdgeCopy(origin)) => self
                .exact_effect_obligations_for_phi_edges(
                    origin.definition.inst,
                    std::slice::from_ref(&origin.incoming),
                ),
            Some(crate::normalize::NormalizedOpOrigin::RelocatedInitializer(origin)) => self
                .exact_effect_obligations_for_phi_edges(
                    origin.definition.inst,
                    &origin.replaced_sites,
                ),
            None => BTreeSet::new(),
        }
    }

    fn exact_effect_obligations_for_inst_memory(
        &self,
        kind: EffectOccurrenceKind,
        source_inst: InstId,
        space: r2il::SpaceId,
        address: Option<ValueId>,
        value: Option<ValueId>,
    ) -> BTreeSet<SemanticObligationId> {
        use r2ssa::{SemanticObligationComponent, SemanticObligationKind};

        let Some(prepared) = self.inputs.prepared_ssa else {
            return BTreeSet::new();
        };
        let Some((block_addr, op_idx)) = prepared.inst_op_site(source_inst) else {
            return BTreeSet::new();
        };
        let is_write = kind == EffectOccurrenceKind::MemoryWrite;
        let Some(fact) = self
            .inputs
            .render_facts()
            .and_then(|facts| facts.memory_access_for_op(block_addr, op_idx, is_write, space))
            .filter(|fact| {
                fact.access.inst == source_inst
                    && address == Some(fact.address)
                    && fact.value == value
                    && fact.is_write == is_write
            })
        else {
            return BTreeSet::new();
        };
        let expected_inputs = address
            .into_iter()
            .chain(is_write.then_some(value).flatten())
            .collect::<Vec<ValueId>>();
        prepared
            .obligations()
            .obligations_for_inst(source_inst)
            .filter(|obligation| {
                obligation.id.kind
                    == if is_write {
                        SemanticObligationKind::ObservableMemoryWrite
                    } else {
                        SemanticObligationKind::ObservableMemoryRead
                    }
                    && obligation.id.component
                        == SemanticObligationComponent::MemoryAccess(fact.access.ordinal)
                    && obligation.inputs == expected_inputs
            })
            .map(|obligation| obligation.id)
            .collect::<BTreeSet<_>>()
    }

    pub(crate) fn exact_effect_obligations_for_normalized_memory(
        &self,
        kind: EffectOccurrenceKind,
        block_addr: u64,
        op_idx: usize,
        space: r2il::SpaceId,
        address: Option<ValueId>,
        value: Option<ValueId>,
    ) -> BTreeSet<SemanticObligationId> {
        self.source_inst_for_normalized_op(block_addr, op_idx)
            .map(|inst| {
                self.exact_effect_obligations_for_inst_memory(kind, inst, space, address, value)
            })
            .unwrap_or_default()
    }

    pub(crate) fn exact_effect_obligations_for_source_memory(
        &self,
        kind: EffectOccurrenceKind,
        block_addr: u64,
        op_idx: usize,
        space: r2il::SpaceId,
        address: Option<ValueId>,
        value: Option<ValueId>,
    ) -> BTreeSet<SemanticObligationId> {
        self.inputs
            .prepared_ssa
            .and_then(|prepared| prepared.graph().inst_id_for_op_site(block_addr, op_idx))
            .map(|inst| {
                self.exact_effect_obligations_for_inst_memory(kind, inst, space, address, value)
            })
            .unwrap_or_default()
    }

    /// Internal/test convenience constructor. It deliberately has no
    /// source-owned authority and therefore cannot be a public render entry.
    #[cfg(test)]
    pub(crate) fn new(ptr_size: u32) -> Self {
        #[cfg(test)]
        static EMPTY_U64_STRING: OnceLock<HashMap<u64, String>> = OnceLock::new();
        #[cfg(test)]
        static EMPTY_STACK_SLOTS: OnceLock<BTreeMap<StackSlotKey, ExternalStackSlotSpec>> =
            OnceLock::new();
        #[cfg(test)]
        static EMPTY_VISIBLE_BINDINGS: OnceLock<Vec<VisibleBinding>> = OnceLock::new();
        static ARCH64: OnceLock<FoldArchConfig> = OnceLock::new();
        static ARCH32: OnceLock<FoldArchConfig> = OnceLock::new();

        let arch = match ptr_size {
            64 => ARCH64.get_or_init(|| FoldArchConfig::for_ptr_size(64)),
            32 => ARCH32.get_or_init(|| FoldArchConfig::for_ptr_size(32)),
            other => Box::leak(Box::new(FoldArchConfig::for_ptr_size(other))),
        };

        let inputs = FoldInputs {
            normalization_origins: None,
            observation_journal: None,
            binding_names: None,
            arch,
            #[cfg(test)]
            function_names: EMPTY_U64_STRING.get_or_init(HashMap::new),
            #[cfg(test)]
            binary_symbols: EMPTY_U64_STRING.get_or_init(HashMap::new),
            function_facts: empty_function_facts(),
            #[cfg(test)]
            stack_slots: EMPTY_STACK_SLOTS.get_or_init(BTreeMap::new),
            #[cfg(test)]
            visible_bindings: EMPTY_VISIBLE_BINDINGS.get_or_init(Vec::new),
            function_return_type: None,
            prepared_ssa: None,
            prepared_semantic_view: None,
        };

        Self::from_inputs(inputs)
    }
}
