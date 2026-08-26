use std::cell::{Cell, OnceCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
#[cfg(test)]
use std::sync::OnceLock;

use crate::analysis;
use crate::ast::{CExpr, CType};
use r2ssa::{
    BlockId, InstId, MemorySSAFacts, ObjectModel, SemanticObligationId, SsaArtifact, UseSite,
    ValueId,
};
#[cfg(test)]
use r2types::ExternalStackVarSpec;
use r2types::{
    CalleeFact, CalleeResolutionFacts, ExternalStackSlotSpec, ExternalTypeDb,
    FieldAccessCertificate, FunctionFacts, InterprocSummaryView, SignatureRegistry, StackSlotKey,
    TypeOracle, VisibleBinding,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ResolutionPhase {
    Semantic,
    Definition,
    DefinitionRaw,
    Visible,
    ImportedArg,
    Memory,
    Return,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ResolutionGuardKey {
    pub(crate) phase: ResolutionPhase,
    pub(crate) name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EffectRenderProofKind {
    Call,
    Expression,
    MemoryRead,
    MemoryWrite,
    Return,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PhiEdgeRenderKind {
    Direct,
    UnconditionalDeadOnOtherEdges,
    Guarded { condition: ValueId, truth: bool },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct PhiEdgeRenderProof {
    /// Exact original phi inputs implemented by this normalized operation.
    pub(crate) sites: Box<[UseSite]>,
    pub(crate) kind: PhiEdgeRenderKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct EffectRenderProof {
    pub(crate) kind: EffectRenderProofKind,
    /// Exact canonical source obligations discharged by this render event.
    ///
    /// Keeping the IDs on the event prevents one rendered component from
    /// silently claiming every obligation owned by the same instruction.
    pub(crate) obligation_ids: BTreeSet<SemanticObligationId>,
    pub(crate) call_disposition: Option<r2types::CallsiteRenderDisposition>,
    pub(crate) target: Option<ValueId>,
    pub(crate) space: Option<r2il::SpaceId>,
    pub(crate) address: Option<ValueId>,
    pub(crate) value: Option<ValueId>,
    pub(crate) values: Vec<ValueId>,
    pub(crate) phi_edge: Option<PhiEdgeRenderProof>,
}

#[derive(Debug, Clone)]
pub(crate) struct FoldArchConfig {
    pub(crate) ptr_size: u32,
    pub(crate) sp_name: String,
    pub(crate) fp_name: String,
    pub(crate) ret_reg_name: String,
    pub(crate) arg_regs: Vec<String>,
    pub(crate) caller_saved_regs: HashSet<String>,
    /// Registers that are condition codes, as the target's register file defines them.
    pub(crate) flag_regs: HashSet<String>,
}

#[derive(Clone, Copy)]
pub(crate) struct FoldInputs<'a> {
    pub(crate) arch: &'a FoldArchConfig,
    #[cfg(test)]
    pub(crate) function_names: &'a HashMap<u64, String>,
    #[cfg(test)]
    pub(crate) strings: &'a HashMap<u64, String>,
    #[cfg(test)]
    /// What the binary calls the thing at an address, not a name this
    /// rendering declares.
    pub(crate) binary_symbols: &'a HashMap<u64, String>,
    pub(crate) function_facts: &'a FunctionFacts,
    /// Spellings for addresses this function touches, for rendering only.
    pub(crate) display_names: &'a r2types::DisplayNames,
    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) certified_rendering_required: bool,
    pub(crate) stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    #[cfg(test)]
    pub(crate) external_stack_vars: &'a HashMap<i64, ExternalStackVarSpec>,
    pub(crate) visible_bindings: &'a [VisibleBinding],
    pub(crate) external_type_db: &'a ExternalTypeDb,
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
    pub(crate) type_hints: &'a HashMap<String, CType>,
    pub(crate) type_oracle: Option<&'a dyn TypeOracle>,
    pub(crate) function_return_type: Option<&'a CType>,
    pub(crate) prepared_ssa: Option<&'a SsaArtifact>,
    /// Sole `BindingId -> SymbolId` projection for this native rendering.
    pub(crate) binding_names:
        Option<&'a std::rc::Rc<crate::binding_plan::BindingNameResolution>>,
    pub(crate) prepared_semantic_view: Option<&'a analysis::PreparedSemanticView>,
    pub(crate) prepared_objects: Option<&'a ObjectModel>,
    #[allow(dead_code)]
    pub(crate) prepared_memory: Option<&'a MemorySSAFacts>,
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

    pub(crate) fn summary_view(&self) -> Option<&'a InterprocSummaryView> {
        Some(self.function_facts.summary_view())
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
    pub(crate) exit_block: Option<u64>,
    pub(crate) return_blocks: HashSet<u64>,
    pub(crate) return_stack_slots: HashSet<i64>,
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
    pub(crate) block_producer_sites: std::cell::RefCell<Option<(u64, HashMap<String, usize>)>>,
    /// Known names grouped by SSA version.
    ///
    /// Resolving a rendered alias needs the names sharing one version, and
    /// finding them by filtering every known name costs a pass per question. The
    /// names do not change once the analysis is built, so one pass answers all
    /// of them.
    pub(crate) names_by_version: OnceCell<BTreeMap<u32, Vec<String>>>,
    pub(crate) current_op_idx: Cell<Option<usize>>,
    pub(crate) hide_stack_frame: bool,
    pub(crate) signature_registry: SignatureRegistry,
    pub(crate) rendered_alias_lookup_cache: std::cell::RefCell<HashMap<String, Option<String>>>,
    pub(crate) preferred_entry_arg_lookup_cache:
        std::cell::RefCell<HashMap<String, Option<String>>>,
    pub(crate) forwarded_source_cache: std::cell::RefCell<HashMap<String, Option<r2ssa::SSAVar>>>,
    pub(crate) load_expr_memo: std::cell::RefCell<HashMap<(ValueId, String), CExpr>>,
    /// What a value renders as, for values whose statement was left out.
    ///
    /// Leaving a statement out is a promise that the reader will show the value
    /// instead. The promise used to be made by one rule and kept by another, and
    /// when they disagreed the reader printed the value's name and nothing
    /// defined it. The expression the skipped statement would have carried is
    /// recorded here as it is skipped, so the rule that decides and the rule that
    /// renders are reading the same answer.
    pub(crate) inlined_renderings: std::cell::RefCell<HashMap<String, CExpr>>,
    pub(crate) call_result_owner_name_cache:
        std::cell::RefCell<BTreeMap<(u64, usize), Option<String>>>,
    pub(crate) owned_call_visible_names_cache: std::cell::RefCell<Option<HashSet<String>>>,
    #[cfg(test)]
    pub(crate) prepared_semantic_view_cache: OnceCell<analysis::PreparedSemanticView>,
    pub(crate) semantic_render_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) value_render_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) definition_lookup_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) definition_raw_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) resolution_guard: std::cell::RefCell<HashSet<ResolutionGuardKey>>,
    pub(crate) effect_render_proofs: std::cell::RefCell<Vec<EffectRenderProof>>,
    /// Blocks the fold walked, which is what expresses a merge standing at their head.
    pub(crate) folded_blocks: std::cell::RefCell<std::collections::BTreeSet<u64>>,
    /// One name per certified loop carrier, derived once because it is settled once.
    pub(crate) carrier_aliases: HashMap<String, String>,
    /// Values that are a carrier read at one of its other widths.
    pub(crate) carrier_member_views: HashMap<String, crate::normalize::CarrierMemberView>,
    /// Names some other block reads, which a block-local prune must not delete.
    pub(crate) cross_block_reads: std::cell::RefCell<HashSet<String>>,
    /// Names minted while folding, handed to the function when it is built.
    ///
    /// A cell because the builders take `&self`. Minting has to borrow, insert
    /// and drop inside one statement: a borrow held across a nested build would
    /// panic, and nested builds are the ordinary case here.
    /// The names this rendering declares, shared with whatever else renders
    /// the same function. An identifier only means something in the table that
    /// issued it, so the passes cannot each hold a copy.
    pub(crate) symbols: std::rc::Rc<std::cell::RefCell<crate::symbol::SymbolTable>>,
    /// Exact canonical obligations the fold can prove do not require output.
    /// Downstream dead-name heuristics are not authority to populate this map.
    pub(crate) elided_obligations:
        std::cell::RefCell<std::collections::BTreeMap<SemanticObligationId, &'static str>>,
    /// First exact-observation failure. Lowering is largely `Option`-based, so
    /// marker issuance records the typed failure here and the native boundary
    /// retains it in the non-consuming audit while emitting the same marker-free
    /// native program.
    pub(crate) observation_error:
        std::cell::RefCell<Option<crate::observation_journal::LegacyObservationJournalError>>,
}

impl FoldArchConfig {
    #[cfg(test)]
    pub(crate) fn for_ptr_size(ptr_size: u32) -> Self {
        let sp_name = if ptr_size == 64 {
            "rsp".to_string()
        } else {
            "esp".to_string()
        };
        let fp_name = if ptr_size == 64 {
            "rbp".to_string()
        } else {
            "ebp".to_string()
        };
        let ret_reg_name = if ptr_size == 64 {
            "rax".to_string()
        } else {
            "eax".to_string()
        };
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
        let caller_saved_regs = {
            let mut regs = HashSet::new();
            if ptr_size == 64 {
                for r in ["rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"] {
                    regs.insert(r.to_string());
                }
            } else {
                for r in ["eax", "ecx", "edx"] {
                    regs.insert(r.to_string());
                }
            }
            regs
        };

        Self {
            ptr_size,
            flag_regs: crate::fold::arch::X86_FLAG_REGISTERS
                .iter()
                .map(|name| (*name).to_string())
                .collect(),
            sp_name,
            fp_name,
            ret_reg_name,
            arg_regs,
            caller_saved_regs,
        }
    }
}

/// Extend the legacy presentation-name table across exact normalized value
/// edges while Stage 5 still renders through that table.
///
/// The normalization certificate owns edge identity. This temporary adapter
/// uses only its `ValueId`s, closes them with a sorted worklist, and converts to
/// display spelling only at the legacy boundary. Naming cutover deletes it.
fn extend_legacy_carrier_aliases_over_normalization(
    aliases: &mut HashMap<String, String>,
    prepared: &SsaArtifact,
    origins: &crate::normalize::NormalizationOrigins,
) {
    let graph = prepared.graph();
    let mut neighbors = BTreeMap::<ValueId, BTreeSet<ValueId>>::new();
    for (left, right) in origins.materialized_value_edges() {
        neighbors.entry(left).or_default().insert(right);
        neighbors.entry(right).or_default().insert(left);
    }

    let mut binding_by_value = BTreeMap::<ValueId, String>::new();
    for value in &graph.values {
        if let Some(binding) = aliases.get(&value.var.display_name()) {
            binding_by_value.insert(value.id, binding.clone());
        }
    }

    close_unambiguous_normalization_components(&neighbors, &mut binding_by_value);

    for (value, binding) in binding_by_value {
        if let Some(value) = graph.value(value) {
            aliases.entry(value.var.display_name()).or_insert(binding);
        }
    }
}

fn close_unambiguous_normalization_components(
    neighbors: &BTreeMap<ValueId, BTreeSet<ValueId>>,
    binding_by_value: &mut BTreeMap<ValueId, String>,
) {
    let mut visited = BTreeSet::<ValueId>::new();
    for start in neighbors.keys().copied() {
        if visited.contains(&start) {
            continue;
        }
        let mut pending = BTreeSet::from([start]);
        let mut component = BTreeSet::new();
        while let Some(value) = pending.pop_first() {
            if !visited.insert(value) {
                continue;
            }
            component.insert(value);
            pending.extend(
                neighbors
                    .get(&value)
                    .into_iter()
                    .flatten()
                    .filter(|neighbor| !visited.contains(neighbor))
                    .copied(),
            );
        }
        let mut bindings = component
            .iter()
            .filter_map(|value| binding_by_value.get(value))
            .cloned()
            .collect::<BTreeSet<_>>();
        if bindings.len() != 1 {
            // No seed means there is nothing to extend. More than one seed is a
            // conflict; this presentation adapter must leave the whole newly
            // reached component unaliased rather than choosing by worklist order.
            continue;
        }
        let Some(binding) = bindings.pop_first() else {
            continue;
        };
        for value in component {
            binding_by_value
                .entry(value)
                .or_insert_with(|| binding.clone());
        }
    }
}

#[cfg(test)]
mod normalization_alias_tests {
    use super::*;

    #[test]
    fn conflicted_component_leaves_every_unseeded_member_unaliased() {
        let neighbors = BTreeMap::from([
            (ValueId(0), BTreeSet::from([ValueId(1)])),
            (ValueId(1), BTreeSet::from([ValueId(0), ValueId(2)])),
            (ValueId(2), BTreeSet::from([ValueId(1), ValueId(3)])),
            (ValueId(3), BTreeSet::from([ValueId(2)])),
        ]);
        let mut bindings = BTreeMap::from([
            (ValueId(0), "left".to_string()),
            (ValueId(3), "right".to_string()),
        ]);

        close_unambiguous_normalization_components(&neighbors, &mut bindings);

        assert_eq!(
            bindings,
            BTreeMap::from([
                (ValueId(0), "left".to_string()),
                (ValueId(3), "right".to_string()),
            ]),
            "a conflicted component must not be partially filled by ValueId order"
        );
    }
}

impl<'a> FoldingContext<'a> {
    pub(crate) fn from_inputs(inputs: FoldInputs<'a>) -> Self {
        let mut carrier_aliases = match (inputs.prepared_ssa, inputs.function_facts.render()) {
            (Some(prepared), Some(render)) => {
                crate::normalize::carrier_name_aliases(prepared, render)
            }
            _ => HashMap::new(),
        };
        if let (Some(prepared), Some(origins)) = (inputs.prepared_ssa, inputs.normalization_origins)
        {
            extend_legacy_carrier_aliases_over_normalization(
                &mut carrier_aliases,
                prepared,
                origins,
            );
        }
        let carrier_member_views = match (inputs.prepared_ssa, inputs.function_facts.render()) {
            (Some(prepared), Some(render)) => {
                crate::normalize::carrier_member_views(prepared, render, &carrier_aliases)
            }
            _ => HashMap::new(),
        };
        if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
            let mut entries = carrier_aliases.iter().collect::<Vec<_>>();
            entries.sort();
            for (member, name) in entries {
                eprintln!("FOLDALIAS member={member} name={name}");
            }
            let mut views = carrier_member_views.iter().collect::<Vec<_>>();
            views.sort_by(|left, right| left.0.cmp(right.0));
            for (member, view) in views {
                eprintln!(
                    "FOLDVIEW member={member} carrier={} width={} carrier_width={}",
                    view.carrier, view.width, view.carrier_width
                );
            }
        }
        Self {
            carrier_aliases,
            carrier_member_views,
            cross_block_reads: std::cell::RefCell::new(HashSet::new()),
            symbols: std::rc::Rc::new(std::cell::RefCell::new(crate::symbol::SymbolTable::new())),
            inputs,
            state: FoldState::default(),
            current_block_addr: Cell::new(None),
            current_block_id: Cell::new(None),
            block_producer_sites: std::cell::RefCell::new(None),
            names_by_version: OnceCell::new(),
            current_op_idx: Cell::new(None),
            hide_stack_frame: true,
            signature_registry: SignatureRegistry::from_embedded_json(),
            rendered_alias_lookup_cache: std::cell::RefCell::new(HashMap::new()),
            preferred_entry_arg_lookup_cache: std::cell::RefCell::new(HashMap::new()),
            forwarded_source_cache: std::cell::RefCell::new(HashMap::new()),
            load_expr_memo: std::cell::RefCell::new(HashMap::new()),
            inlined_renderings: std::cell::RefCell::new(HashMap::new()),
            call_result_owner_name_cache: std::cell::RefCell::new(BTreeMap::new()),
            owned_call_visible_names_cache: std::cell::RefCell::new(None),
            #[cfg(test)]
            prepared_semantic_view_cache: OnceCell::new(),
            semantic_render_in_progress: std::cell::RefCell::new(HashSet::new()),
            value_render_in_progress: std::cell::RefCell::new(HashSet::new()),
            definition_lookup_in_progress: std::cell::RefCell::new(HashSet::new()),
            definition_raw_in_progress: std::cell::RefCell::new(HashSet::new()),
            resolution_guard: std::cell::RefCell::new(HashSet::new()),
            effect_render_proofs: std::cell::RefCell::new(Vec::new()),
            folded_blocks: std::cell::RefCell::new(std::collections::BTreeSet::new()),
            elided_obligations: std::cell::RefCell::new(std::collections::BTreeMap::new()),
            observation_error: std::cell::RefCell::new(None),
        }
    }

    pub(crate) fn folded_block_addrs(&self) -> std::collections::BTreeSet<u64> {
        self.folded_blocks.borrow().clone()
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

    fn retain_first_observation_error(
        &self,
        error: crate::observation_journal::LegacyObservationJournalError,
    ) {
        let mut first = self.observation_error.borrow_mut();
        if first.is_none() {
            *first = Some(error);
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

    /// Wrap one exact normalized operand occurrence. The journal owns every
    /// translation from normalized coordinates to original V/U identities.
    pub(crate) fn observe_normalized_input_expr(
        &self,
        block_addr: u64,
        op_idx: usize,
        input_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        let site = match self.observation_site(block_addr, op_idx) {
            Ok(site) => Some(site),
            Err(error) => {
                if self.inputs.observation_journal.is_some() {
                    self.retain_first_observation_error(error);
                }
                None
            }
        };
        self.observe_optional_normalized_input_expr(site, input_idx, expr)
    }

    pub(crate) fn observe_optional_normalized_input_expr(
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
        let result = journal
            .borrow_mut()
            .observe_normalized_input_expr(site, input_idx, expr);
        match result {
            Ok(marked) => marked,
            Err(error) => {
                self.retain_first_observation_error(error);
                fallback
            }
        }
    }

    pub(crate) fn observe_current_normalized_input_expr(
        &self,
        input_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        let Some(block_addr) = self.current_block_addr.get() else {
            if self.inputs.observation_journal.is_some() {
                self.retain_first_observation_error(
                    crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
                );
            }
            return expr;
        };
        let Some(op_idx) = self.current_op_idx.get() else {
            if self.inputs.observation_journal.is_some() {
                self.retain_first_observation_error(
                    crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
                );
            }
            return expr;
        };
        self.observe_normalized_input_expr(block_addr, op_idx, input_idx, expr)
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

    /// Wrap one exact normalized definition that survives inside a consumer.
    pub(crate) fn observe_normalized_output_expr(
        &self,
        block_addr: u64,
        op_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        let Some(journal) = self.inputs.observation_journal else {
            return expr;
        };
        let fallback = expr.clone();
        let result = self.observation_site(block_addr, op_idx).and_then(|site| {
            journal
                .borrow_mut()
                .observe_normalized_output_expr(site, expr)
        });
        match result {
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

    pub(crate) fn note_elided_normalized_op(
        &self,
        _block_addr: u64,
        _op_idx: usize,
        _reason: &'static str,
    ) {
        // Stack-frame/dead-name pruning is a renderer heuristic, not canonical
        // evidence that a source semantic obligation may be erased. Keep such
        // operations as unpaid obligations so the ledger refuses conservatively.
    }

    pub(crate) fn elided_obligations(
        &self,
    ) -> std::collections::BTreeMap<SemanticObligationId, &'static str> {
        self.elided_obligations.borrow().clone()
    }

    pub(crate) fn effect_render_proofs_since(&self, checkpoint: usize) -> Vec<EffectRenderProof> {
        self.effect_render_proofs
            .borrow()
            .get(checkpoint..)
            .unwrap_or_default()
            .to_vec()
    }

    pub(crate) fn append_effect_render_proofs(&self, proofs: &[EffectRenderProof]) {
        self.effect_render_proofs
            .borrow_mut()
            .extend_from_slice(proofs);
    }

    pub(crate) fn effect_render_proof_checkpoint(&self) -> usize {
        self.effect_render_proofs.borrow().len()
    }

    pub(crate) fn truncate_effect_render_proofs(&self, checkpoint: usize) {
        self.effect_render_proofs.borrow_mut().truncate(checkpoint);
    }

    fn exact_value_obligations(
        &self,
        kind: EffectRenderProofKind,
        source_inst: InstId,
        value: Option<ValueId>,
    ) -> (
        BTreeSet<SemanticObligationId>,
        Option<r2types::CallsiteRenderDisposition>,
        Option<ValueId>,
        Vec<ValueId>,
    ) {
        use r2ssa::SemanticObligationKind as ObligationKind;

        let Some(prepared) = self.inputs.prepared_ssa else {
            return (BTreeSet::new(), None, None, Vec::new());
        };
        let Some(inst) = prepared.graph().inst(source_inst) else {
            return (BTreeSet::new(), None, None, Vec::new());
        };
        let source_site = prepared.inst_op_site(source_inst);
        let call_fact = source_site.and_then(|(block_addr, op_idx)| {
            self.inputs.call_render_facts()?.fact_for_site(
                r2types::CallsiteKey {
                    block_addr,
                    op_index: op_idx,
                },
            )
        });
        let return_certified = source_site
            .and_then(|(block_addr, op_idx)| {
                self.inputs.render_facts()?.return_for_op(block_addr, op_idx)
            })
            .is_some_and(|fact| Some(fact.value) == value);
        let rendered_call = call_fact.filter(|fact| {
            !matches!(
                fact.disposition,
                r2types::CallsiteRenderDisposition::Suppressed
                    | r2types::CallsiteRenderDisposition::Residualized
            )
        });
        let unique_return_value = value.is_some_and(|value| {
            prepared
                .obligations()
                .obligations_for_inst(source_inst)
                .filter(|obligation| {
                    obligation.id.kind == ObligationKind::ReturnValue
                        && obligation.inputs == [value]
                })
                .count()
                == 1
        });
        let unique_call_result = value.is_some_and(|value| {
            prepared
                .obligations()
                .obligations_for_inst(source_inst)
                .filter(|obligation| {
                    obligation.id.kind == ObligationKind::CallResult
                        && obligation.inputs == [value]
                })
                .count()
                == 1
        });

        let mut obligation_ids = BTreeSet::new();
        for obligation in prepared.obligations().obligations_for_inst(source_inst) {
            let exact = match kind {
                EffectRenderProofKind::Return => {
                    return_certified
                        && (obligation.id.kind == ObligationKind::Return
                            || (obligation.id.kind == ObligationKind::ReturnValue
                                && unique_return_value
                                && obligation.inputs.as_slice() == value.as_slice()))
                }
                EffectRenderProofKind::Call => {
                    rendered_call.is_some() && obligation.id.kind == ObligationKind::Call
                }
                EffectRenderProofKind::Expression => match &inst.payload {
                    r2ssa::InstPayload::Op(
                        r2ssa::SSAOp::Branch { .. } | r2ssa::SSAOp::BranchInd { .. },
                    ) => obligation.id.kind == ObligationKind::ControlTransfer,
                    r2ssa::InstPayload::Op(r2ssa::SSAOp::CBranch { .. }) => matches!(
                        obligation.id.kind,
                        ObligationKind::ControlPredicate | ObligationKind::ControlTransfer
                    ),
                    r2ssa::InstPayload::Op(
                        r2ssa::SSAOp::Call { .. } | r2ssa::SSAOp::CallInd { .. },
                    ) => rendered_call.is_some()
                        && (obligation.id.kind == ObligationKind::Call
                            || (obligation.id.kind == ObligationKind::CallArgument
                                && !obligation.inputs.is_empty()
                                && obligation.inputs.iter().all(|input| {
                                    rendered_call
                                        .is_some_and(|fact| fact.proof_values.contains(input))
                                }))
                            || (obligation.id.kind == ObligationKind::CallResult
                                && unique_call_result
                                && obligation.inputs.as_slice() == value.as_slice())),
                    _ => obligation.id.kind == ObligationKind::LiveValueProducer
                        && inst.output == value,
                },
                EffectRenderProofKind::MemoryRead | EffectRenderProofKind::MemoryWrite => false,
            };
            if exact {
                obligation_ids.insert(obligation.id);
            }
        }
        (
            obligation_ids,
            rendered_call.map(|fact| fact.disposition),
            rendered_call.and_then(|fact| fact.target),
            rendered_call
                .map(|fact| fact.proof_values.clone())
                .unwrap_or_default(),
        )
    }

    fn record_effect_render_proof_for_inst_value(
        &self,
        kind: EffectRenderProofKind,
        source_inst: InstId,
        value: Option<ValueId>,
    ) {
        let (obligation_ids, call_disposition, target, values) =
            self.exact_value_obligations(kind, source_inst, value);
        if obligation_ids.is_empty() {
            return;
        }
        self.effect_render_proofs.borrow_mut().push(EffectRenderProof {
            kind,
            obligation_ids,
            call_disposition,
            target,
            space: None,
            address: None,
            value,
            values,
            phi_edge: None,
        });
    }

    pub(crate) fn record_effect_render_proof_for_normalized_value(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        value: Option<ValueId>,
    ) {
        let Some(site) = self.normalized_site(block_addr, op_idx) else {
            return;
        };
        let Some(origins) = self.inputs.normalization_origins else {
            if let Some(inst) = self.source_inst_for_normalized_site(site) {
                self.record_effect_render_proof_for_inst_value(kind, inst, value);
            }
            return;
        };
        match origins.origin(site) {
            Some(crate::normalize::NormalizedOpOrigin::Original(inst)) => {
                self.record_effect_render_proof_for_inst_value(kind, *inst, value);
            }
            Some(crate::normalize::NormalizedOpOrigin::PhiEdgeCopy(origin)) => {
                self.record_phi_edge_render_proof(
                    kind,
                    origin.definition.inst,
                    std::slice::from_ref(&origin.incoming),
                    origin.guarded.map_or(PhiEdgeRenderKind::Direct, |guarded| {
                        PhiEdgeRenderKind::Guarded {
                            condition: self
                                .inputs
                                .prepared_ssa
                                .and_then(|prepared| prepared.graph().inst(guarded.guard.inst))
                                .and_then(|inst| inst.inputs.get(guarded.guard.input_idx))
                                .copied()
                                .unwrap_or(origin.incoming_value),
                            truth: origin.incoming_input_idx == 1,
                        }
                    }),
                    value,
                );
            }
            Some(crate::normalize::NormalizedOpOrigin::RelocatedInitializer(origin)) => {
                self.record_phi_edge_render_proof(
                    kind,
                    origin.definition.inst,
                    &origin.replaced_sites,
                    PhiEdgeRenderKind::Direct,
                    value,
                );
            }
            None => {}
        }
    }

    fn record_phi_edge_render_proof(
        &self,
        kind: EffectRenderProofKind,
        definition: InstId,
        sites: &[UseSite],
        edge_kind: PhiEdgeRenderKind,
        value: Option<ValueId>,
    ) {
        use r2ssa::{SemanticObligationComponent, SemanticObligationKind};

        let Some(prepared) = self.inputs.prepared_ssa else {
            return;
        };
        let graph = prepared.graph();
        let mut obligation_ids = BTreeSet::new();
        for site in sites {
            let predecessor = graph.inst(site.inst).and_then(|inst| match &inst.payload {
                r2ssa::InstPayload::Phi { predecessors } => predecessors.get(site.input_idx),
                r2ssa::InstPayload::Op(_) => None,
            });
            let predecessor = predecessor
                .and_then(|block| graph.block(*block))
                .map(|block| block.addr);
            for obligation in prepared.obligations().obligations_for_inst(definition) {
                if obligation.id.kind == SemanticObligationKind::LiveStateTransition
                    && matches!(
                        obligation.id.component,
                        SemanticObligationComponent::LoopTransition { predecessor: owner, .. }
                            if Some(owner) == predecessor
                    )
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
        self.effect_render_proofs.borrow_mut().push(EffectRenderProof {
            kind,
            obligation_ids,
            call_disposition: None,
            target: None,
            space: None,
            address: None,
            value,
            values: Vec::new(),
            phi_edge: Some(PhiEdgeRenderProof {
                sites: sites.to_vec().into_boxed_slice(),
                kind: edge_kind,
            }),
        });
    }

    pub(crate) fn record_effect_render_proof_for_source_value(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        value: Option<ValueId>,
    ) {
        if let Some(inst) = self
            .inputs
            .prepared_ssa
            .and_then(|prepared| prepared.graph().inst_id_for_op_site(block_addr, op_idx))
        {
            self.record_effect_render_proof_for_inst_value(kind, inst, value);
        }
    }

    fn record_effect_render_proof_for_inst_memory(
        &self,
        kind: EffectRenderProofKind,
        source_inst: InstId,
        space: r2il::SpaceId,
        address: Option<ValueId>,
        value: Option<ValueId>,
    ) {
        use r2ssa::{SemanticObligationComponent, SemanticObligationKind};

        let Some(prepared) = self.inputs.prepared_ssa else {
            return;
        };
        let Some((block_addr, op_idx)) = prepared.inst_op_site(source_inst) else {
            return;
        };
        let is_write = kind == EffectRenderProofKind::MemoryWrite;
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
            return;
        };
        let expected_inputs = address
            .into_iter()
            .chain(is_write.then_some(value).flatten())
            .collect::<Vec<ValueId>>();
        let obligation_ids = prepared
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
            .collect::<BTreeSet<_>>();
        if obligation_ids.is_empty() {
            return;
        }
        let proof = EffectRenderProof {
            kind,
            obligation_ids,
            call_disposition: None,
            target: None,
            space: Some(space),
            address,
            value,
            values: Vec::new(),
            phi_edge: None,
        };
        let mut proofs = self.effect_render_proofs.borrow_mut();
        if !proofs.contains(&proof) {
            proofs.push(proof);
        }
    }

    pub(crate) fn record_effect_render_proof_for_normalized_memory(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        space: r2il::SpaceId,
        address: Option<ValueId>,
        value: Option<ValueId>,
    ) {
        if let Some(inst) = self.source_inst_for_normalized_op(block_addr, op_idx) {
            self.record_effect_render_proof_for_inst_memory(kind, inst, space, address, value);
        }
    }

    pub(crate) fn record_effect_render_proof_for_source_memory(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        space: r2il::SpaceId,
        address: Option<ValueId>,
        value: Option<ValueId>,
    ) {
        if let Some(inst) = self
            .inputs
            .prepared_ssa
            .and_then(|prepared| prepared.graph().inst_id_for_op_site(block_addr, op_idx))
        {
            self.record_effect_render_proof_for_inst_memory(kind, inst, space, address, value);
        }
    }

    /// Internal/test convenience constructor. It deliberately has no
    /// source-owned authority and therefore cannot be a public render entry.
    #[cfg(test)]
    pub(crate) fn new(ptr_size: u32) -> Self {
        #[cfg(test)]
        static EMPTY_U64_STRING: OnceLock<HashMap<u64, String>> = OnceLock::new();
        static EMPTY_STACK_SLOTS: OnceLock<BTreeMap<StackSlotKey, ExternalStackSlotSpec>> =
            OnceLock::new();
        static EMPTY_FIELD_CERTS: OnceLock<Vec<FieldAccessCertificate>> = OnceLock::new();
        #[cfg(test)]
        static EMPTY_I64_STACK: OnceLock<HashMap<i64, ExternalStackVarSpec>> = OnceLock::new();
        static EMPTY_VISIBLE_BINDINGS: OnceLock<Vec<VisibleBinding>> = OnceLock::new();
        static EMPTY_TYPE_DB: OnceLock<ExternalTypeDb> = OnceLock::new();
        static EMPTY_STRING_STRING: OnceLock<HashMap<String, String>> = OnceLock::new();
        static EMPTY_STRING_CTYPE: OnceLock<HashMap<String, CType>> = OnceLock::new();
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
            display_names: crate::empty_display_names(),
            arch,
            #[cfg(test)]
            function_names: EMPTY_U64_STRING.get_or_init(HashMap::new),
            #[cfg(test)]
            strings: EMPTY_U64_STRING.get_or_init(HashMap::new),
            #[cfg(test)]
            binary_symbols: EMPTY_U64_STRING.get_or_init(HashMap::new),
            function_facts: empty_function_facts(),
            #[cfg(test)]
            certified_rendering_required: false,
            stack_slots: EMPTY_STACK_SLOTS.get_or_init(BTreeMap::new),
            #[cfg(test)]
            external_stack_vars: EMPTY_I64_STACK.get_or_init(HashMap::new),
            visible_bindings: EMPTY_VISIBLE_BINDINGS.get_or_init(Vec::new),
            external_type_db: EMPTY_TYPE_DB.get_or_init(ExternalTypeDb::default),
            param_register_aliases: EMPTY_STRING_STRING.get_or_init(HashMap::new),
            type_hints: EMPTY_STRING_CTYPE.get_or_init(HashMap::new),
            type_oracle: None,
            function_return_type: None,
            prepared_ssa: None,
            prepared_semantic_view: None,
            prepared_objects: None,
            prepared_memory: None,
        };

        Self::from_inputs(inputs)
    }
}
