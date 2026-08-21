use std::cell::{Cell, OnceCell};
use std::collections::{BTreeMap, HashMap, HashSet};
#[cfg(test)]
use std::sync::OnceLock;

use crate::analysis;
use crate::ast::{CExpr, CType};
use r2ssa::{MemorySSAFacts, ObjectModel, SsaArtifact, ValueId};
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct PhiEdgeRenderProof {
    pub(crate) source: ValueId,
    pub(crate) kind: PhiEdgeRenderKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct EffectRenderProof {
    pub(crate) kind: EffectRenderProofKind,
    pub(crate) block_addr: u64,
    pub(crate) op_idx: usize,
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
}

#[derive(Clone, Copy)]
pub(crate) struct FoldInputs<'a> {
    pub(crate) arch: &'a FoldArchConfig,
    #[cfg(test)]
    pub(crate) function_names: &'a HashMap<u64, String>,
    #[cfg(test)]
    pub(crate) strings: &'a HashMap<u64, String>,
    #[cfg(test)]
    pub(crate) symbols: &'a HashMap<u64, String>,
    pub(crate) function_facts: &'a FunctionFacts,
    /// Spellings for addresses this function touches, for rendering only.
    pub(crate) display_names: &'a r2types::DisplayNames,
    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) certified_rendering_required: bool,
    pub(crate) stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub(crate) field_access_certificates: &'a [FieldAccessCertificate],
    #[cfg(test)]
    pub(crate) external_stack_vars: &'a HashMap<i64, ExternalStackVarSpec>,
    pub(crate) visible_bindings: &'a [VisibleBinding],
    pub(crate) external_type_db: &'a ExternalTypeDb,
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
    pub(crate) type_hints: &'a HashMap<String, CType>,
    pub(crate) type_oracle: Option<&'a dyn TypeOracle>,
    pub(crate) function_return_type: Option<&'a CType>,
    pub(crate) prepared_ssa: Option<&'a SsaArtifact>,
    pub(crate) prepared_semantic_view: Option<&'a analysis::PreparedSemanticView>,
    pub(crate) prepared_objects: Option<&'a ObjectModel>,
    #[allow(dead_code)]
    pub(crate) prepared_memory: Option<&'a MemorySSAFacts>,
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
    pub(crate) current_op_idx: Cell<Option<usize>>,
    pub(crate) hide_stack_frame: bool,
    pub(crate) signature_registry: SignatureRegistry,
    pub(crate) rendered_alias_lookup_cache: std::cell::RefCell<HashMap<String, Option<String>>>,
    pub(crate) preferred_entry_arg_lookup_cache:
        std::cell::RefCell<HashMap<String, Option<String>>>,
    pub(crate) forwarded_source_cache: std::cell::RefCell<HashMap<String, Option<r2ssa::SSAVar>>>,
    pub(crate) load_expr_memo: std::cell::RefCell<HashMap<(ValueId, String), CExpr>>,
    pub(crate) call_result_owner_name_cache:
        std::cell::RefCell<BTreeMap<(u64, usize), Option<String>>>,
    pub(crate) owned_call_visible_names_cache: std::cell::RefCell<Option<HashSet<String>>>,
    pub(crate) prepared_semantic_view_cache: OnceCell<analysis::PreparedSemanticView>,
    pub(crate) prepared_semantic_view_building: Cell<bool>,
    pub(crate) semantic_render_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) value_render_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) definition_lookup_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) definition_raw_in_progress: std::cell::RefCell<HashSet<String>>,
    pub(crate) resolution_guard: std::cell::RefCell<HashSet<ResolutionGuardKey>>,
    pub(crate) effect_render_proofs: std::cell::RefCell<Vec<EffectRenderProof>>,
    /// Blocks the fold walked, which is what expresses a merge standing at their head.
    pub(crate) folded_blocks: std::cell::RefCell<std::collections::BTreeSet<u64>>,
    /// Op sites the fold dropped without recording that anything rendered them,
    /// keyed by why. An accounting of what the output owes reads these as debts
    /// it never paid, so knowing which are deliberate is what separates a
    /// rendering gap from a bookkeeping one.
    pub(crate) elided_op_sites:
        std::cell::RefCell<std::collections::BTreeMap<(u64, usize), &'static str>>,
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
            sp_name,
            fp_name,
            ret_reg_name,
            arg_regs,
            caller_saved_regs,
        }
    }
}

impl<'a> FoldingContext<'a> {
    pub(crate) fn from_inputs(inputs: FoldInputs<'a>) -> Self {
        Self {
            inputs,
            state: FoldState::default(),
            current_block_addr: Cell::new(None),
            current_op_idx: Cell::new(None),
            hide_stack_frame: true,
            signature_registry: SignatureRegistry::from_embedded_json(),
            rendered_alias_lookup_cache: std::cell::RefCell::new(HashMap::new()),
            preferred_entry_arg_lookup_cache: std::cell::RefCell::new(HashMap::new()),
            forwarded_source_cache: std::cell::RefCell::new(HashMap::new()),
            load_expr_memo: std::cell::RefCell::new(HashMap::new()),
            call_result_owner_name_cache: std::cell::RefCell::new(BTreeMap::new()),
            owned_call_visible_names_cache: std::cell::RefCell::new(None),
            prepared_semantic_view_cache: OnceCell::new(),
            prepared_semantic_view_building: Cell::new(false),
            semantic_render_in_progress: std::cell::RefCell::new(HashSet::new()),
            value_render_in_progress: std::cell::RefCell::new(HashSet::new()),
            definition_lookup_in_progress: std::cell::RefCell::new(HashSet::new()),
            definition_raw_in_progress: std::cell::RefCell::new(HashSet::new()),
            resolution_guard: std::cell::RefCell::new(HashSet::new()),
            effect_render_proofs: std::cell::RefCell::new(Vec::new()),
            folded_blocks: std::cell::RefCell::new(std::collections::BTreeSet::new()),
            elided_op_sites: std::cell::RefCell::new(std::collections::BTreeMap::new()),
        }
    }

    pub(crate) fn folded_block_addrs(&self) -> std::collections::BTreeSet<u64> {
        self.folded_blocks.borrow().clone()
    }

    pub(crate) fn note_elided_op_site(&self, block_addr: u64, op_idx: usize, reason: &'static str) {
        // Only an explicit request pays for this: every folded op that renders
        // nothing reaches here, and the map is read by nothing else.
        if !crate::unowned_report_requested() {
            return;
        }
        self.elided_op_sites
            .borrow_mut()
            .insert((block_addr, op_idx), reason);
    }

    pub(crate) fn elided_op_sites(
        &self,
    ) -> std::collections::BTreeMap<(u64, usize), &'static str> {
        self.elided_op_sites.borrow().clone()
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

    pub(crate) fn record_effect_render_proof_for_value(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        value: Option<ValueId>,
    ) {
        self.effect_render_proofs
            .borrow_mut()
            .push(EffectRenderProof {
                kind,
                block_addr,
                op_idx,
                call_disposition: None,
                target: None,
                space: None,
                address: None,
                value,
                values: Vec::new(),
                phi_edge: None,
            });
    }

    pub(crate) fn record_effect_render_proof_for_memory(
        &self,
        kind: EffectRenderProofKind,
        block_addr: u64,
        op_idx: usize,
        space: r2il::SpaceId,
        address: Option<ValueId>,
        value: Option<ValueId>,
    ) {
        let proof = EffectRenderProof {
            kind,
            block_addr,
            op_idx,
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
            display_names: crate::empty_display_names(),
            arch,
            #[cfg(test)]
            function_names: EMPTY_U64_STRING.get_or_init(HashMap::new),
            #[cfg(test)]
            strings: EMPTY_U64_STRING.get_or_init(HashMap::new),
            #[cfg(test)]
            symbols: EMPTY_U64_STRING.get_or_init(HashMap::new),
            function_facts: empty_function_facts(),
            #[cfg(test)]
            certified_rendering_required: false,
            stack_slots: EMPTY_STACK_SLOTS.get_or_init(BTreeMap::new),
            field_access_certificates: EMPTY_FIELD_CERTS.get_or_init(Vec::new),
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
