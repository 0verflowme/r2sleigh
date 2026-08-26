//! Variable naming and recovery.
//!
//! This module handles variable naming, stack variable recovery,
//! and parameter detection.

use std::collections::{HashMap, HashSet};

use r2ssa::{ObjectKind, SSAFunction, SSAOp, SSAVar, SsaArtifact};
use r2types::{
    CTypeLike, ExternalStackBase, ExternalStackSlotRole, FunctionTypeFacts, StackSlotKey,
    VisibleBinding, VisibleBindingKind, register_alias_names,
};

use crate::DecompilerInput;
use crate::analysis::utils;
use crate::ast::{BinaryOp, CExpr, CType};

pub(crate) fn type_like_to_ctype(ty: &CTypeLike) -> CType {
    match ty {
        CTypeLike::Void => CType::Void,
        CTypeLike::Bool => CType::Bool,
        CTypeLike::Int { bits, signedness } => match signedness {
            r2types::Signedness::Unsigned => CType::UInt(*bits),
            _ => CType::Int(*bits),
        },
        CTypeLike::Float(bits) => CType::Float(*bits),
        CTypeLike::Pointer(inner) => CType::Pointer(Box::new(type_like_to_ctype(inner))),
        CTypeLike::Array(inner, len) => CType::Array(Box::new(type_like_to_ctype(inner)), *len),
        CTypeLike::Struct(name) => CType::Struct(name.clone()),
        CTypeLike::Union(name) => CType::Union(name.clone()),
        CTypeLike::Enum(name) => CType::Enum(name.clone()),
        CTypeLike::Typedef(name) => CType::Typedef(name.clone()),
        CTypeLike::Function | CTypeLike::Unknown => CType::Unknown,
    }
}

fn parse_const_value(name: &str) -> Option<u64> {
    utils::parse_const_value(name)
}

/// Variable information.
#[derive(Debug, Clone)]
pub struct VarInfo {
    /// The SSA variable.
    pub ssa_var: SSAVar,
    /// The C name for this variable.
    pub name: String,
    /// The inferred type.
    pub ty: CType,
    /// Whether this is a parameter.
    pub is_param: bool,
    /// Whether this is a local variable.
    pub is_local: bool,
    /// Stack offset (if stack variable).
    pub stack_offset: Option<i64>,
    /// Exact upstream object identity for a certified stack local. An offset
    /// without this identity is only a legacy recovery hint and cannot select a
    /// planned binding.
    pub stack_object: Option<r2ssa::ObjectId>,
    /// Stable recovery order for deterministic output.
    order_index: usize,
    /// ABI slot ordinal for parameters before any external rename.
    param_ordinal: Option<usize>,
}

#[derive(Debug, Clone, Copy, Default)]
struct VarAttrs {
    is_param: bool,
    is_local: bool,
    stack_offset: Option<i64>,
    stack_object: Option<r2ssa::ObjectId>,
    param_ordinal: Option<usize>,
}

/// The register a source name spells, ignoring the space that qualifies it.
///
/// Sleigh writes a register source either bare (`x0`) or qualified by the space
/// it lives in (`reg:x0`), and the argument-register test has to see the same
/// token either way.
fn register_token(name_lower: &str) -> Option<&str> {
    let token = name_lower.rsplit(':').next()?;
    (!token.is_empty()).then_some(token)
}

impl VarAttrs {
    const fn local(stack_offset: i64, stack_object: Option<r2ssa::ObjectId>) -> Self {
        Self {
            is_param: false,
            is_local: true,
            stack_offset: Some(stack_offset),
            stack_object,
            param_ordinal: None,
        }
    }

    const fn param(param_ordinal: usize) -> Self {
        Self {
            is_param: true,
            is_local: false,
            stack_offset: None,
            stack_object: None,
            param_ordinal: Some(param_ordinal),
        }
    }
}

/// Variable recovery and naming context.
pub struct VariableRecovery {
    /// All recovered variables.
    vars: HashMap<SSAVar, VarInfo>,
    /// Name counter for generating unique names.
    name_counters: HashMap<String, usize>,
    /// Used parameter names (to avoid duplicates).
    used_param_names: HashSet<String>,
    /// Used local variable names (to avoid duplicates).
    used_local_names: HashSet<String>,
    /// Stable C identity for each recovered stack slot.
    stack_names_by_offset: HashMap<i64, String>,
    /// Stack storage objects keyed independently from the SSA values stored in them.
    stack_locals_by_offset: HashMap<i64, VarInfo>,
    /// Used general variable names (to avoid duplicates).
    used_var_names: HashSet<String>,
    /// Stack pointer register name.
    sp_name: String,
    /// Frame pointer register name.
    fp_name: String,
    /// Pointer size in bits (reserved for architecture-aware type sizing).
    #[allow(dead_code)]
    ptr_size: u32,
    /// Loop variable counter (i, j, k, ...).
    loop_var_idx: usize,
    /// Return-value registers for the active ABI.
    ret_regs: Vec<String>,
    /// Ordered argument registers for the active ABI.
    arg_regs: Vec<String>,
    /// Externally recovered type and layout facts.
    type_facts: FunctionTypeFacts,
    /// Stable insertion order for recovered variables.
    next_order_index: usize,
}

impl VariableRecovery {
    /// Create a new variable recovery context with explicit ABI registers.
    pub fn new_with_abi(
        sp_name: &str,
        fp_name: &str,
        ptr_size: u32,
        arg_regs: Vec<String>,
        ret_regs: Vec<String>,
    ) -> Self {
        Self {
            vars: HashMap::new(),
            name_counters: HashMap::new(),
            used_param_names: HashSet::new(),
            used_local_names: HashSet::new(),
            stack_names_by_offset: HashMap::new(),
            stack_locals_by_offset: HashMap::new(),
            used_var_names: HashSet::new(),
            sp_name: sp_name.to_string(),
            fp_name: fp_name.to_string(),
            ptr_size,
            loop_var_idx: 0,
            ret_regs,
            arg_regs,
            type_facts: FunctionTypeFacts::default(),
            next_order_index: 0,
        }
    }

    /// Set externally recovered type/layout facts.
    #[cfg(test)]
    pub fn set_type_facts(&mut self, type_facts: FunctionTypeFacts) {
        self.type_facts = type_facts.canonicalized();
    }

    fn is_visible_external_stack_name_role(role: ExternalStackSlotRole) -> bool {
        matches!(
            role,
            ExternalStackSlotRole::Local
                | ExternalStackSlotRole::StackArg
                | ExternalStackSlotRole::Unknown
        )
    }

    fn is_reserved_param_name(&self, name: &str) -> bool {
        if self
            .used_param_names
            .iter()
            .any(|used| used.eq_ignore_ascii_case(name))
        {
            return true;
        }

        let lower = name.to_ascii_lowercase();
        if let Some(rest) = lower.strip_prefix("arg")
            && let Ok(idx) = rest.parse::<usize>()
            && idx < self.arg_regs.len()
        {
            return true;
        }

        self.type_facts
            .visible_bindings
            .iter()
            .filter(|binding| matches!(binding.kind, VisibleBindingKind::Param))
            .any(|binding| binding.name.eq_ignore_ascii_case(name))
            || self
                .type_facts
                .render_authorized_signature()
                .map(|sig| {
                    sig.params
                        .iter()
                        .take(self.arg_regs.len())
                        .any(|param| param.name.eq_ignore_ascii_case(name))
                })
                .unwrap_or(false)
    }

    fn visible_param_binding(&self, index: usize) -> Option<&VisibleBinding> {
        self.type_facts.visible_bindings.iter().find(|binding| {
            matches!(binding.kind, VisibleBindingKind::Param) && binding.param_index == Some(index)
        })
    }

    fn visible_stack_binding_for_offset(&self, offset: i64) -> Option<&VisibleBinding> {
        self.type_facts.visible_bindings.iter().find(|binding| {
            !matches!(
                binding.kind,
                VisibleBindingKind::Param
                    | VisibleBindingKind::HiddenHome
                    | VisibleBindingKind::HiddenSaved
            ) && binding
                .stack_slot
                .as_ref()
                .is_some_and(|slot| Self::stack_slot_matches_offset(slot, offset))
        })
    }

    fn stack_slot_matches_offset(slot: &StackSlotKey, offset: i64) -> bool {
        if slot.offset == offset {
            return true;
        }
        matches!(slot.base, ExternalStackBase::FramePointer) && -slot.offset == offset
    }

    fn external_stack_name_for_offset(&self, offset: i64) -> Option<String> {
        if let Some(binding) = self.visible_stack_binding_for_offset(offset)
            && !binding.name.is_empty()
            && !self.is_reserved_param_name(&binding.name)
        {
            return Some(binding.name.clone());
        }

        for (slot_key, slot_spec) in &self.type_facts.stack_slots {
            if !Self::stack_slot_matches_offset(slot_key, offset) {
                continue;
            }
            if !slot_spec.name.is_empty()
                && Self::is_visible_external_stack_name_role(slot_spec.role)
                && !self.is_reserved_param_name(&slot_spec.name)
            {
                return Some(slot_spec.name.clone());
            }
        }

        None
    }

    fn visible_stack_type_for_offset(&self, offset: i64) -> Option<CType> {
        if let Some(ty) = self
            .visible_stack_binding_for_offset(offset)
            .and_then(|binding| binding.ty.as_ref())
            .map(type_like_to_ctype)
        {
            return Some(ty);
        }

        self.type_facts
            .stack_slots
            .iter()
            .find_map(|(slot_key, slot_spec)| {
                (Self::stack_slot_matches_offset(slot_key, offset)
                    && Self::is_visible_external_stack_name_role(slot_spec.role))
                .then(|| slot_spec.ty.as_ref().map(type_like_to_ctype))
                .flatten()
            })
    }

    /// Recover variables from an SSA function.
    pub fn recover(
        &mut self,
        func: &SSAFunction,
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    ) {

        // First pass: identify stack variables
        self.find_stack_variables(func, None, symbols);

        self.recover_non_stack_variables(func);
    }

    /// Recover variables from one source-owned decompiler input.
    pub(crate) fn recover_input(
        &mut self,
        input: &DecompilerInput,
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    ) {

        self.type_facts = input.function_facts().type_facts().clone();
        let prepared = input.prepared_ssa();
        let func = prepared.function();
        self.find_stack_variables(func, Some(prepared), symbols);
        self.recover_non_stack_variables(func);
    }

    fn recover_non_stack_variables(&mut self, func: &SSAFunction) {
        // Second pass: identify parameters
        self.find_parameters(func);

        // Third pass: identify special variables (return values, loop counters)
        self.find_special_variables(func);

        // Fourth pass: name remaining variables
        self.name_remaining(func);
    }

    /// Find special variables like return values and loop counters.
    fn find_special_variables(&mut self, func: &SSAFunction) {
        // Find potential loop counters (variables incremented in a block)
        let mut increment_vars: HashSet<String> = HashSet::new();

        for block in func.blocks() {
            for op in &block.ops {
                // Look for patterns like: x = x + 1
                if let SSAOp::IntAdd { dst, a, b } = op {
                    // Check if adding a constant 1
                    if b.is_const() && b.name.contains("1") {
                        // Check if dst is a new version of a
                        let dst_base = dst.name.split('_').next().unwrap_or(&dst.name);
                        let a_base = a.name.split('_').next().unwrap_or(&a.name);
                        if dst_base == a_base {
                            increment_vars.insert(dst_base.to_lowercase());
                        }
                    }
                }
            }
        }

        // Name loop counters
        for block in func.blocks() {
            for op in &block.ops {
                if let Some(dst) = op.dst() {
                    if self.vars.contains_key(dst) {
                        continue;
                    }

                    let base = dst
                        .name
                        .split('_')
                        .next()
                        .unwrap_or(&dst.name)
                        .to_lowercase();

                    // Check if this is a loop counter
                    if increment_vars.contains(&base) && dst.size == 32 {
                        let name = self.next_loop_var();
                        let ty = self.type_from_size(dst.size);
                        self.insert_var_info(dst.clone(), name, ty, VarAttrs::default());
                    }
                }
            }
        }

        // Find return values (last rax assignment before return)
        self.find_return_values(func);
    }

    /// Find return value variables.
    fn find_return_values(&mut self, func: &SSAFunction) {
        // Look for the last assignment to the return register in each exit block
        for block in func.blocks() {
            let mut last_ret_var: Option<SSAVar> = None;
            let mut has_return = false;

            for op in &block.ops {
                // Check if this block ends with a branch (could be a return)
                // Returns typically load RIP from stack and branch indirectly
                if let SSAOp::Branch { .. } | SSAOp::BranchInd { .. } = op {
                    has_return = true;
                }

                // Track last assignment to return register
                if let Some(dst) = op.dst() {
                    let name_lower = dst.name.to_lowercase();
                    if self
                        .ret_regs
                        .iter()
                        .any(|reg| name_lower.contains(&reg.to_ascii_lowercase()))
                    {
                        last_ret_var = Some(dst.clone());
                    }
                }
            }

            // If this block has a return and we found a return register assignment
            if has_return
                && let Some(ret_var) = last_ret_var
                && !self.vars.contains_key(&ret_var)
            {
                let name = self.make_unique_var_name("result".to_string());
                let ty = self.type_from_size(ret_var.size);
                self.insert_var_info(ret_var.clone(), name, ty, VarAttrs::default());
            }
        }
    }

    /// Get the next loop variable name (i, j, k, l, m, n, then idx1, idx2, ...).
    fn next_loop_var(&mut self) -> String {
        const LOOP_VARS: [&str; 6] = ["i", "j", "k", "l", "m", "n"];

        let name = if self.loop_var_idx < LOOP_VARS.len() {
            LOOP_VARS[self.loop_var_idx].to_string()
        } else {
            format!("idx{}", self.loop_var_idx - LOOP_VARS.len() + 1)
        };

        self.loop_var_idx += 1;
        self.make_unique_var_name(name)
    }

    /// Make a variable name unique.
    fn make_unique_var_name(&mut self, base_name: String) -> String {
        if !self.used_var_names.contains(&base_name) {
            self.used_var_names.insert(base_name.clone());
            return base_name;
        }

        let mut counter = 2;
        loop {
            let candidate = format!("{}_{}", base_name, counter);
            if !self.used_var_names.contains(&candidate) {
                self.used_var_names.insert(candidate.clone());
                return candidate;
            }
            counter += 1;
        }
    }

    /// Find stack variables (loads/stores relative to SP/FP).
    fn find_stack_variables(
        &mut self,
        func: &SSAFunction,
        prepared: Option<&SsaArtifact>,
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    ) {

        let definitions = self.collect_definitions(func, symbols);
        for block in func.blocks() {
            for op in &block.ops {
                match op {
                    SSAOp::Load {
                        dst,
                        space: r2il::SpaceId::Ram,
                        addr,
                    } => {
                        if let Some((object, offset)) =
                            self.get_stack_object(func, prepared, addr, &definitions, symbols)
                        {
                            self.ensure_stack_local(object, offset, dst.size);
                        }
                    }
                    SSAOp::Store {
                        space: r2il::SpaceId::Ram,
                        addr,
                        val,
                    } => {
                        if let Some((object, offset)) =
                            self.get_stack_object(func, prepared, addr, &definitions, symbols)
                        {
                            self.ensure_stack_local(object, offset, val.size);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn ensure_stack_local(
        &mut self,
        object: Option<r2ssa::ObjectId>,
        offset: i64,
        size: u32,
    ) {
        if let Some(existing) = self.stack_locals_by_offset.get_mut(&offset) {
            if existing.stack_object.is_none() {
                existing.stack_object = object;
            }
            return;
        }
        let name = self.gen_stack_var_name(offset);
        let ty = self
            .visible_stack_type_for_offset(offset)
            .unwrap_or_else(|| self.type_from_size(size));
        let synthetic = SSAVar::new(format!("stack:{offset}"), 0, size);
        let info = self.make_var_info(synthetic, name, ty, VarAttrs::local(offset, object));
        self.stack_locals_by_offset.insert(offset, info);
    }

    /// Get stack offset from an address variable.
    fn get_stack_object(
        &self,
        func: &SSAFunction,
        prepared: Option<&SsaArtifact>,
        addr: &SSAVar,
        definitions: &HashMap<String, CExpr>,
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    ) -> Option<(Option<r2ssa::ObjectId>, i64)> {

        if let Some((object, offset)) = prepared
            .and_then(|artifact| {
                artifact
                    .object_for_var(addr, r2il::SpaceId::Ram)
                    .map(|object| (artifact, object))
            })
            .and_then(|(artifact, object)| {
                artifact.objects().object(object).and_then(|fact| match fact.kind {
                    ObjectKind::StackSlot { offset, .. }
                    | ObjectKind::FrameObject { offset, .. } => Some((object, offset)),
                    _ => None,
                })
            })
        {
            return Some((Some(object), offset));
        }
        if let Some(offset) = func
            .decompile_prep_facts()
            .and_then(|facts| facts.stack_address_root_of(addr))
            .map(|root| root.offset)
        {
            return Some((None, offset));
        }
        utils::extract_stack_offset_from_var(
            symbols,
            addr,
            &|name: &str| definitions.get(name).cloned(),
            &self.fp_name,
            &self.sp_name,
        )
        .map(|offset| (None, offset))
    }

    fn collect_definitions(
        &self,
        func: &SSAFunction,
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    ) -> HashMap<String, CExpr> {

        let mut definitions = HashMap::new();
        for block in func.blocks() {
            for op in &block.ops {
                match op {
                    SSAOp::Copy { dst, src } => {
                        definitions.insert(dst.display_name(), self.expr_for_ssa_var(src, symbols));
                    }
                    SSAOp::IntAdd { dst, a, b } => {
                        definitions.insert(
                            dst.display_name(),
                            CExpr::binary(
                                BinaryOp::Add,
                                self.expr_for_ssa_var(a, symbols),
                                self.expr_for_ssa_var(b, symbols),
                            ),
                        );
                    }
                    SSAOp::IntSub { dst, a, b } => {
                        definitions.insert(
                            dst.display_name(),
                            CExpr::binary(
                                BinaryOp::Sub,
                                self.expr_for_ssa_var(a, symbols),
                                self.expr_for_ssa_var(b, symbols),
                            ),
                        );
                    }
                    _ => {}
                }
            }
        }
        definitions
    }

    fn expr_for_ssa_var(
        &self,
        var: &SSAVar,
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    ) -> CExpr {

        if let Some(val) = parse_const_value(&var.name) {
            if let Ok(signed) = i64::try_from(val) {
                return CExpr::IntLit(signed);
            }
            return CExpr::UIntLit(val);
        }
        // An SSA display name is an internal key, not a spelling. Minting one as
        // a rendered identifier makes a second symbol for a value that already
        // has one -- `X10_2` beside `x10_2` -- and the definition follows only
        // one of them, so the other names nothing. Spell it the way every other
        // site spells it.
        crate::symbol::var_ref(
            symbols,
            crate::analysis::utils::format_traced_name(&var.display_name(), &HashMap::new()),
        )
    }

    /// Generate a name for a stack variable.
    fn gen_stack_var_name(&mut self, offset: i64) -> String {
        if let Some(name) = self.stack_names_by_offset.get(&offset) {
            return name.clone();
        }
        let base_name = self
            .external_stack_name_for_offset(offset)
            .unwrap_or_else(|| {
                if offset >= 0 {
                    format!("local_{:x}", offset)
                } else {
                    format!("arg_{:x}", -offset)
                }
            });

        // Ensure uniqueness
        if !self.used_local_names.contains(&base_name) {
            self.used_local_names.insert(base_name.clone());
            self.stack_names_by_offset.insert(offset, base_name.clone());
            return base_name;
        }

        // Find a unique suffix
        let mut counter = 2;
        loop {
            let candidate = format!("{}_{}", base_name, counter);
            if !self.used_local_names.contains(&candidate) {
                self.used_local_names.insert(candidate.clone());
                self.stack_names_by_offset.insert(offset, candidate.clone());
                return candidate;
            }
            counter += 1;
        }
    }

    /// Find function parameters using calling-convention-aware detection.
    ///
    /// Scans the *entire function* for version-0 uses of calling convention
    /// argument registers (RDI, RSI, RDX, RCX, R8, R9 for SysV x86-64).
    /// Parameters are ordered by their CC position and stop at the first
    /// unused arg register (no gaps allowed).
    fn find_parameters(&mut self, func: &SSAFunction) {
        if self.arg_regs.is_empty() {
            return;
        }

        // Scan entire function for version-0 uses of CC arg registers.
        //
        // A register is an argument register when it *is* one, not when its name
        // happens to contain one. Matching by substring made `x29` answer for
        // `x2` and `x30` for `x3`, so every non-leaf arm64 function recovered
        // its frame pointer and link register as its third and fourth
        // parameters -- and the real third argument, spelled `w2`, never
        // matched `x2` at all. The alias table already knows that `x2` is
        // spelled `x2` or `w2` and nothing else.
        let alias_to_cc_reg: HashMap<String, String> = self
            .arg_regs
            .iter()
            .flat_map(|cc_reg| {
                register_alias_names(cc_reg)
                    .into_iter()
                    .map(move |alias| (alias, cc_reg.to_string()))
            })
            .collect();
        let mut seen_v0: HashMap<String, SSAVar> = HashMap::new();

        for block in func.blocks() {
            for op in &block.ops {
                for src in op.sources() {
                    if src.version == 0 {
                        let name_lower = src.name.to_ascii_lowercase();
                        if let Some(cc_reg) =
                            register_token(&name_lower).and_then(|token| alias_to_cc_reg.get(token))
                        {
                            seen_v0.entry(cc_reg.clone()).or_insert_with(|| src.clone());
                        }
                    }
                }
            }
            // Also check phi sources
            for phi in &block.phis {
                for (_, src) in &phi.sources {
                    if src.version == 0 {
                        let name_lower = src.name.to_ascii_lowercase();
                        if let Some(cc_reg) =
                            register_token(&name_lower).and_then(|token| alias_to_cc_reg.get(token))
                        {
                            seen_v0.entry(cc_reg.clone()).or_insert_with(|| src.clone());
                        }
                    }
                }
            }
        }

        // Emit parameters in CC order, stopping at the first gap
        for (idx, cc_reg) in self.arg_regs.clone().into_iter().enumerate() {
            if let Some(var) = seen_v0.get(&cc_reg) {
                let mut name = format!("arg{idx}");
                let mut ty = self.type_from_size(var.size);
                self.apply_external_param_override(idx, &mut name, &mut ty);
                let name = self.make_unique_param_name(name);
                self.insert_var_info(var.clone(), name, ty, VarAttrs::param(idx));
            } else {
                // No gap: stop at first unused arg register
                break;
            }
        }
    }

    fn apply_external_param_override(&self, index: usize, name: &mut String, ty: &mut CType) {
        if let Some(binding) = self.visible_param_binding(index) {
            if !is_generic_arg_name(&binding.name) {
                *name = binding.name.clone();
            }
            if let Some(binding_ty) = binding.ty.as_ref() {
                *ty = type_like_to_ctype(binding_ty);
            }
        }

        if let Some(ext_ty) = self
            .type_facts
            .merged_signature
            .as_ref()
            .and_then(|signature| signature.params.get(index))
            .and_then(|param| param.ty.as_ref())
        {
            *ty = type_like_to_ctype(ext_ty);
        }
        if let Some(ext) = self
            .type_facts
            .render_authorized_signature()
            .and_then(|signature| signature.params.get(index))
            && !is_generic_arg_name(&ext.name)
        {
            *name = ext.name.clone();
        }
    }

    /// Generate a parameter name from register conventions.
    #[allow(dead_code)] // Used in tests
    fn gen_param_name(&mut self, var: &SSAVar) -> String {
        // Use register name if it's a common parameter register
        let name = var.name.to_lowercase();
        let base_name = if name.contains("rdi") || name.contains("edi") {
            "arg0".to_string()
        } else if name.contains("rsi") || name.contains("esi") {
            "arg1".to_string()
        } else if name.contains("rdx") || name.contains("edx") {
            "arg2".to_string()
        } else if name.contains("rcx") || name.contains("ecx") {
            "arg3".to_string()
        } else if name.contains("r8") {
            "arg4".to_string()
        } else if name.contains("r9") {
            "arg5".to_string()
        // ARM calling convention
        } else if name.contains("r0") || name.contains("x0") {
            "arg0".to_string()
        } else if name.contains("r1") || name.contains("x1") {
            "arg1".to_string()
        } else if name.contains("r2") || name.contains("x2") {
            "arg2".to_string()
        } else if name.contains("r3") || name.contains("x3") {
            "arg3".to_string()
        } else {
            // Generic parameter name
            let count = self.name_counters.entry("arg".to_string()).or_insert(0);
            let name = format!("arg{count}");
            *count += 1;
            name
        };

        // Ensure uniqueness
        self.make_unique_param_name(base_name)
    }

    /// Make a parameter name unique by adding a suffix if needed.
    fn make_unique_param_name(&mut self, base_name: String) -> String {
        if !self.used_param_names.contains(&base_name) {
            self.used_param_names.insert(base_name.clone());
            return base_name;
        }

        // Find a unique suffix
        let mut counter = 2;
        loop {
            let candidate = format!("{}_{}", base_name, counter);
            if !self.used_param_names.contains(&candidate) {
                self.used_param_names.insert(candidate.clone());
                return candidate;
            }
            counter += 1;
        }
    }

    /// Name remaining variables.
    fn name_remaining(&mut self, func: &SSAFunction) {
        for block in func.blocks() {
            for op in &block.ops {
                if let Some(dst) = op.dst()
                    && !self.vars.contains_key(dst)
                {
                    let name = self.gen_var_name(dst);
                    let ty = self.type_from_size(dst.size);
                    self.insert_var_info(dst.clone(), name, ty, VarAttrs::default());
                }
            }
        }
    }

    fn insert_var_info(&mut self, ssa_var: SSAVar, name: String, ty: CType, attrs: VarAttrs) {
        let info = self.make_var_info(ssa_var.clone(), name, ty, attrs);
        self.vars.insert(ssa_var, info);
    }

    fn make_var_info(
        &mut self,
        ssa_var: SSAVar,
        name: String,
        ty: CType,
        attrs: VarAttrs,
    ) -> VarInfo {
        let order_index = self.next_order_index;
        self.next_order_index += 1;
        VarInfo {
            ssa_var,
            name,
            ty,
            is_param: attrs.is_param,
            is_local: attrs.is_local,
            stack_offset: attrs.stack_offset,
            stack_object: attrs.stack_object,
            order_index,
            param_ordinal: attrs.param_ordinal,
        }
    }

    /// Generate a variable name.
    fn gen_var_name(&mut self, var: &SSAVar) -> String {
        let base = if var.name_kind().is_temporary() {
            "t"
        } else {
            "v"
        };

        let count = self.name_counters.entry(base.to_string()).or_insert(0);
        *count += 1;
        format!("{}{}", base, count)
    }

    /// Get a type from a byte size.
    fn type_from_size(&self, size: u32) -> CType {
        match size {
            0 => CType::Unknown,
            1 => CType::Int(8),
            2 => CType::Int(16),
            4 => CType::Int(32),
            8 => CType::Int(64),
            16 => CType::Int(128),
            _ => CType::BitVector(size.saturating_mul(8)),
        }
    }

    /// Get variable info.
    pub fn get_var(&self, var: &SSAVar) -> Option<&VarInfo> {
        self.vars.get(var)
    }

    /// Get the C name for a variable.
    pub fn get_name(&self, var: &SSAVar) -> String {
        self.vars
            .get(var)
            .map(|v| v.name.clone())
            .unwrap_or_else(|| format!("unk_{}", var.version))
    }

    /// Get all parameters.
    pub fn parameters(&self) -> Vec<&VarInfo> {
        let mut params: Vec<_> = self.vars.values().filter(|v| v.is_param).collect();
        params.sort_by(|a, b| {
            a.param_ordinal
                .unwrap_or(usize::MAX)
                .cmp(&b.param_ordinal.unwrap_or(usize::MAX))
                .then_with(|| a.name.cmp(&b.name))
                .then_with(|| a.ssa_var.display_name().cmp(&b.ssa_var.display_name()))
                .then_with(|| a.order_index.cmp(&b.order_index))
        });
        params
    }

    /// Get all local variables.
    pub fn locals(&self) -> Vec<&VarInfo> {
        let mut locals: Vec<_> = self
            .stack_locals_by_offset
            .values()
            .chain(self.vars.values().filter(|v| v.is_local))
            .collect();
        locals.sort_by(|a, b| {
            match (a.stack_offset, b.stack_offset) {
                (Some(a_off), Some(b_off)) => a_off.cmp(&b_off),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => std::cmp::Ordering::Equal,
            }
            .then_with(|| a.name.cmp(&b.name))
            .then_with(|| a.ssa_var.display_name().cmp(&b.ssa_var.display_name()))
            .then_with(|| a.order_index.cmp(&b.order_index))
        });
        locals
    }

    /// Update variable type.
    pub fn set_type(&mut self, var: &SSAVar, ty: CType) {
        if let Some(info) = self.vars.get_mut(var) {
            info.ty = ty;
        }
    }
}

fn is_generic_arg_name(name: &str) -> bool {

    let lower = name.trim().to_ascii_lowercase();
    lower
        .strip_prefix("arg")
        .map(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
        .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    /// The System V AMD64 registers these tests were written against.
    ///
    /// Naming the target here keeps the one ABI table in the decompiler with
    /// the lifter that supplies it. Inferring an ABI from a pointer width, as
    /// this used to, answers x86-64 for arm64 as well.
    fn sysv_amd64_recovery() -> VariableRecovery {
        VariableRecovery::new_with_abi(
            "rsp",
            "rbp",
            64,
            ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ["rax", "eax"].into_iter().map(str::to_string).collect(),
        )
    }

    use super::*;
    use r2il::{R2ILBlock, R2ILOp, Varnode};
    use r2ssa::SSAFunction;
    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }
    use r2types::{
        ExternalStackBase, ExternalStackSlotRole, ExternalStackVarSpec, FunctionParamSpec,
        FunctionSignatureSpec, FunctionTypeFacts, StackSlotKey, VisibleBinding, VisibleBindingKind,
    };

    fn stack_var_spec_from_ctype(
        name: &str,
        ty: Option<CType>,
        base: Option<&str>,
    ) -> ExternalStackVarSpec {
        ExternalStackVarSpec {
            name: name.to_string(),
            ty: ty.as_ref().map(super::super::ctype_to_type_like),
            base: match base.map(|raw| raw.to_ascii_lowercase()) {
                Some(raw) if raw == "rbp" || raw == "ebp" || raw == "bp" || raw == "fp" => {
                    ExternalStackBase::FramePointer
                }
                Some(raw) if raw == "rsp" || raw == "esp" || raw == "sp" => {
                    ExternalStackBase::StackPointer
                }
                Some(raw) => ExternalStackBase::Named(raw),
                None => ExternalStackBase::default(),
            },
            role: ExternalStackSlotRole::Unknown,
            param_index: None,
            param_name: None,
            source_reg: None,
        }
    }

    fn signature_spec(params: Vec<(&str, Option<CType>)>) -> FunctionSignatureSpec {
        FunctionSignatureSpec {
            ret_type: None,
            params: params
                .into_iter()
                .map(|(name, ty)| FunctionParamSpec {
                    name: name.to_string(),
                    ty: ty.as_ref().map(super::super::ctype_to_type_like),
                })
                .collect(),
        }
    }

    fn type_facts_with_external_signature(signature: FunctionSignatureSpec) -> FunctionTypeFacts {
        let signature_certificate = r2types::SignatureCertificate::from_signature(
            &signature,
            [r2types::SignatureCertificateSource::ExternalContext],
        );
        FunctionTypeFacts {
            merged_signature: Some(signature),
            signature_certificate,
            ..FunctionTypeFacts::default()
        }
    }

    fn visible_stack_binding(name: &str, ty: Option<CType>, offset: i64) -> VisibleBinding {
        VisibleBinding {
            name: name.to_string(),
            ty: ty.as_ref().map(super::super::ctype_to_type_like),
            kind: VisibleBindingKind::Local,
            stack_slot: Some(StackSlotKey {
                base: ExternalStackBase::FramePointer,
                offset,
            }),
            param_index: None,
            source_reg: None,
        }
    }

    fn visible_param_binding(
        name: &str,
        ty: Option<CType>,
        index: usize,
        reg: &str,
    ) -> VisibleBinding {
        VisibleBinding {
            name: name.to_string(),
            ty: ty.as_ref().map(super::super::ctype_to_type_like),
            kind: VisibleBindingKind::Param,
            stack_slot: None,
            param_index: Some(index),
            source_reg: Some(reg.to_string()),
        }
    }

    #[test]
    fn test_gen_param_name() {
        let mut vr = sysv_amd64_recovery();

        let var_rdi = SSAVar::new("reg:rdi", 0, 64);
        assert_eq!(vr.gen_param_name(&var_rdi), "arg0");

        let var_rsi = SSAVar::new("reg:rsi", 0, 64);
        assert_eq!(vr.gen_param_name(&var_rsi), "arg1");
    }

    #[test]
    fn test_gen_var_name() {
        let mut vr = sysv_amd64_recovery();

        let var1 = SSAVar::new("reg:0", 1, 64);
        let name1 = vr.gen_var_name(&var1);

        let var2 = SSAVar::new("reg:8", 1, 64);
        let name2 = vr.gen_var_name(&var2);

        assert_ne!(name1, name2);

        let temp_name = vr.gen_var_name(&SSAVar::new("tmp:11f80", 1, 64));
        let unique_name = vr.gen_var_name(&SSAVar::new("unique:11f80", 1, 64));

        assert!(temp_name.starts_with('t'));
        assert!(unique_name.starts_with('t'));
    }

    #[test]
    fn test_stack_var_name() {
        let mut vr = sysv_amd64_recovery();

        let name = vr.gen_stack_var_name(8);
        assert_eq!(name, "local_8");

        let name = vr.gen_stack_var_name(-8);
        assert_eq!(name, "arg_8");
    }

    #[test]
    fn same_stack_slot_reuses_one_c_identity() {
        let mut vr = sysv_amd64_recovery();

        assert_eq!(vr.gen_stack_var_name(-8), "arg_8");
        assert_eq!(vr.gen_stack_var_name(-8), "arg_8");
    }

    #[test]
    fn test_external_stack_var_name_preferred() {
        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(FunctionTypeFacts {
            visible_bindings: vec![visible_stack_binding(
                "user_input",
                Some(CType::ptr(CType::Int(8))),
                -8,
            )],
            external_stack_vars: HashMap::from([(
                8,
                stack_var_spec_from_ctype("user_input", None, Some("RBP")),
            )]),
            ..FunctionTypeFacts::default()
        });

        let name = vr.gen_stack_var_name(8);
        assert_eq!(name, "user_input");
    }

    #[test]
    fn test_external_stack_var_name_fallback_when_missing() {
        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(FunctionTypeFacts {
            external_stack_vars: HashMap::from([(
                -0x10,
                stack_var_spec_from_ctype("buf", None, Some("RBP")),
            )]),
            ..FunctionTypeFacts::default()
        });

        let name = vr.gen_stack_var_name(8);
        assert_eq!(name, "local_8");
    }

    #[test]
    fn test_external_stack_var_name_collision_still_unique() {
        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(FunctionTypeFacts {
            external_stack_vars: HashMap::from([
                (8, stack_var_spec_from_ctype("buf", None, Some("RBP"))),
                (16, stack_var_spec_from_ctype("buf", None, Some("RBP"))),
            ]),
            ..FunctionTypeFacts::default()
        });

        let first = vr.gen_stack_var_name(8);
        let second = vr.gen_stack_var_name(16);
        assert_eq!(first, "buf");
        assert_eq!(second, "buf_2");
    }

    #[test]
    fn test_external_stack_var_name_prefers_mirrored_rbp_offset() {
        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(FunctionTypeFacts {
            external_stack_vars: HashMap::from([(
                -4,
                stack_var_spec_from_ctype("result", None, Some("RBP")),
            )]),
            ..FunctionTypeFacts::default()
        });

        let name = vr.gen_stack_var_name(4);
        assert_eq!(name, "result");
    }

    #[test]
    fn test_external_stack_var_name_matching_param_alias_falls_back_to_generic_local() {
        let mut vr = sysv_amd64_recovery();
        let mut type_facts = type_facts_with_external_signature(signature_spec(vec![
            ("a", Some(CType::Int(32))),
            ("b", Some(CType::Int(32))),
        ]));
        type_facts.external_stack_vars = HashMap::from([(
            -8,
            stack_var_spec_from_ctype("a", Some(CType::Int(32)), Some("RBP")),
        )]);
        vr.set_type_facts(type_facts);

        let name = vr.gen_stack_var_name(8);
        assert_eq!(name, "local_8");
    }

    #[test]
    fn test_external_signature_overrides_meaningful_param_name_and_type() {
        let mut vr = sysv_amd64_recovery();
        let mut type_facts = type_facts_with_external_signature(signature_spec(vec![(
            "user_input",
            Some(CType::ptr(CType::Int(8))),
        )]));
        type_facts.visible_bindings = vec![visible_param_binding(
            "user_input",
            Some(CType::ptr(CType::Int(8))),
            0,
            "rdi",
        )];
        vr.set_type_facts(type_facts);

        let mut name = "arg1".to_string();
        let mut ty = CType::Int(64);
        vr.apply_external_param_override(0, &mut name, &mut ty);

        assert_eq!(name, "user_input");
        assert_eq!(ty, CType::ptr(CType::Int(8)));
    }

    #[test]
    fn visible_binding_type_and_name_drive_stack_local_recovery() {
        let symbols = test_table();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[block]).expect("ssa function");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntAdd {
                dst: SSAVar::new("tmp:addr", 1, 8),
                a: SSAVar::new("RBP", 1, 8),
                b: SSAVar::new("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Load {
                dst: SSAVar::new("tmp:len", 1, 8),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:addr", 1, 8),
            },
            SSAOp::Return {
                target: SSAVar::new("tmp:len", 1, 8),
            },
        ];

        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(FunctionTypeFacts {
            visible_bindings: vec![visible_stack_binding("len", Some(CType::UInt(64)), -8)],
            ..FunctionTypeFacts::default()
        });

        vr.recover(&func, &symbols);

        let local = vr
            .locals()
            .into_iter()
            .find(|info| info.name == "len")
            .expect("visible stack local");
        assert_eq!(local.name, "len");
        assert_eq!(local.ty, CType::UInt(64));
    }

    #[test]
    fn canonical_stack_slot_type_drives_stack_local_recovery() {
        let symbols = test_table();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[block]).expect("ssa function");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntAdd {
                dst: SSAVar::new("tmp:addr", 1, 8),
                a: SSAVar::new("RBP", 1, 8),
                b: SSAVar::new("const:ffffffffffffffff", 0, 8),
            },
            SSAOp::Load {
                dst: SSAVar::new("tmp:byte", 1, 1),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:addr", 1, 8),
            },
            SSAOp::Return {
                target: SSAVar::new("tmp:byte", 1, 1),
            },
        ];

        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(FunctionTypeFacts {
            stack_slots: std::collections::BTreeMap::from([(
                StackSlotKey {
                    base: ExternalStackBase::FramePointer,
                    offset: -1,
                },
                stack_var_spec_from_ctype("c", Some(CType::UInt(8)), Some("RBP")),
            )]),
            ..FunctionTypeFacts::default()
        });

        vr.recover(&func, &symbols);

        let local = vr
            .locals()
            .into_iter()
            .find(|info| info.name == "c")
            .expect("canonical typed stack local");
        assert_eq!(local.ty, CType::UInt(8));
    }

    #[test]
    fn test_external_signature_generic_param_name_is_ignored() {
        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(type_facts_with_external_signature(signature_spec(vec![(
            "arg0",
            Some(CType::Int(32)),
        )])));

        let mut name = "arg1".to_string();
        let mut ty = CType::Int(64);
        vr.apply_external_param_override(0, &mut name, &mut ty);

        assert_eq!(name, "arg1");
        assert_eq!(ty, CType::Int(32));
    }

    #[test]
    fn test_external_signature_type_override_only_when_available() {
        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(type_facts_with_external_signature(signature_spec(vec![(
            "count", None,
        )])));

        let mut name = "arg1".to_string();
        let mut ty = CType::Int(64);
        vr.apply_external_param_override(0, &mut name, &mut ty);

        assert_eq!(name, "count");
        assert_eq!(ty, CType::Int(64));
    }

    #[test]
    fn test_recover_finds_stack_local_through_temp_frame_address() {
        let symbols = test_table();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[block]).expect("ssa function");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::IntAdd {
                dst: SSAVar::new("tmp:addr", 1, 8),
                a: SSAVar::new("RBP", 1, 8),
                b: SSAVar::new("const:fffffffffffffffc", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:addr", 1, 8),
                val: SSAVar::new("EAX", 1, 4),
            },
            SSAOp::Return {
                target: SSAVar::new("RIP", 1, 8),
            },
        ];

        let mut vr = sysv_amd64_recovery();
        vr.set_type_facts(FunctionTypeFacts {
            external_stack_vars: HashMap::from([(
                -4,
                stack_var_spec_from_ctype("sum", Some(CType::Int(32)), Some("RBP")),
            )]),
            ..FunctionTypeFacts::default()
        });

        vr.recover(&func, &symbols);

        let local_names: Vec<_> = vr
            .locals()
            .into_iter()
            .map(|info| info.name.clone())
            .collect();
        assert!(
            local_names.iter().any(|name| name == "sum"),
            "expected temp-address store to recover named stack local, got {local_names:?}"
        );
        assert_ne!(
            vr.get_name(&SSAVar::new("EAX", 1, 4)),
            "sum",
            "a stored SSA value must not inherit the identity of its destination object"
        );
    }

    #[test]
    fn only_ram_accesses_recover_stack_locals() {
        let symbols = test_table();
        let function_for_space = |space| {
            let mut block = R2ILBlock::new(0x1000, 1);
            block.push(R2ILOp::Return {
                target: Varnode::constant(0, 8),
            });
            let mut func = SSAFunction::from_blocks_raw_no_arch(&[block]).expect("ssa function");
            func.get_block_mut(0x1000).expect("entry").ops = vec![
                SSAOp::IntSub {
                    dst: SSAVar::new("tmp:load_addr", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Load {
                    dst: SSAVar::new("tmp:loaded", 1, 4),
                    space,
                    addr: SSAVar::new("tmp:load_addr", 1, 8),
                },
                SSAOp::IntSub {
                    dst: SSAVar::new("tmp:store_addr", 1, 8),
                    a: SSAVar::new("RBP", 1, 8),
                    b: SSAVar::constant(16, 8),
                },
                SSAOp::Store {
                    space,
                    addr: SSAVar::new("tmp:store_addr", 1, 8),
                    val: SSAVar::new("EAX", 1, 4),
                },
            ];
            func
        };
        let stack_offsets_for_space = |space| {
            let mut recovery = sysv_amd64_recovery();
            recovery.recover(&function_for_space(space), &symbols);
            recovery
                .locals()
                .into_iter()
                .filter_map(|local| local.stack_offset)
                .collect::<Vec<_>>()
        };

        assert_eq!(stack_offsets_for_space(r2il::SpaceId::Ram), vec![-16, -8]);
        assert!(stack_offsets_for_space(r2il::SpaceId::Custom(7)).is_empty());
    }

    #[test]
    fn frame_and_link_registers_are_not_recovered_as_arguments() {
        // `x29` contains `x2` and `x30` contains `x3`, so a substring test made
        // every non-leaf arm64 function recover its frame pointer and link
        // register as its third and fourth arguments -- while the real third
        // argument, spelled `w2`, matched nothing. The recovered parameters are
        // then paired to the declared ones by position, so `x29` was handed the
        // name `arg2` and every address it held rendered as that argument.
        let symbols = test_table();
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut func = SSAFunction::from_blocks_raw_no_arch(&[block]).expect("ssa function");
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("tmp:a", 1, 8),
                src: SSAVar::new("x0", 0, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:b", 1, 8),
                src: SSAVar::new("x1", 0, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:c", 1, 4),
                src: SSAVar::new("w2", 0, 4),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:frame", 1, 8),
                src: SSAVar::new("x29", 0, 8),
            },
            SSAOp::Copy {
                dst: SSAVar::new("tmp:link", 1, 8),
                src: SSAVar::new("x30", 0, 8),
            },
        ];

        let mut recovery = VariableRecovery::new_with_abi(
            "sp",
            "x29",
            64,
            ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]
                .into_iter()
                .map(str::to_string)
                .collect(),
            ["x0"].into_iter().map(str::to_string).collect(),
        );
        recovery.recover(&func, &symbols);

        let recovered: Vec<_> = recovery
            .parameters()
            .into_iter()
            .map(|info| info.ssa_var.name.to_ascii_lowercase())
            .collect();
        assert_eq!(
            recovered,
            vec!["x0", "x1", "w2"],
            "the third argument is spelled w2, and x29/x30 are not arguments at all"
        );
    }

    #[test]
    fn parameters_are_sorted_by_abi_ordinal_before_rendered_name() {
        let mut vr = sysv_amd64_recovery();
        let first = SSAVar::new("reg:rdi", 0, 64);
        let second = SSAVar::new("reg:rsi", 0, 64);

        vr.insert_var_info(
            second.clone(),
            "aaa_second".to_string(),
            CType::Int(64),
            VarAttrs::param(1),
        );
        vr.insert_var_info(
            first.clone(),
            "zzz_first".to_string(),
            CType::Int(64),
            VarAttrs::param(0),
        );

        let names: Vec<_> = vr
            .parameters()
            .into_iter()
            .map(|info| info.name.clone())
            .collect();
        assert_eq!(names, vec!["zzz_first", "aaa_second"]);
    }

    #[test]
    fn locals_are_sorted_by_stack_offset_then_name_then_ssa_name() {
        let mut vr = sysv_amd64_recovery();
        let local_c = SSAVar::new("tmp:c", 1, 32);
        let local_a = SSAVar::new("tmp:a", 1, 32);
        let local_b = SSAVar::new("tmp:b", 1, 32);
        let temp = SSAVar::new("tmp:no_offset", 1, 32);

        vr.insert_var_info(
            local_c.clone(),
            "slot".to_string(),
            CType::Int(32),
            VarAttrs::local(8, None),
        );
        vr.insert_var_info(
            local_b.clone(),
            "slot".to_string(),
            CType::Int(32),
            VarAttrs::local(8, None),
        );
        vr.insert_var_info(
            local_a.clone(),
            "alpha".to_string(),
            CType::Int(32),
            VarAttrs::local(4, None),
        );
        vr.insert_var_info(
            temp.clone(),
            "zeta".to_string(),
            CType::Int(32),
            VarAttrs {
                is_local: true,
                ..VarAttrs::default()
            },
        );

        let names: Vec<_> = vr
            .locals()
            .into_iter()
            .map(|info| info.name.clone())
            .collect();
        let ssa_names: Vec<_> = vr
            .locals()
            .into_iter()
            .map(|info| info.ssa_var.display_name())
            .collect();
        assert_eq!(names, vec!["alpha", "slot", "slot", "zeta"]);
        assert_eq!(
            ssa_names,
            vec!["tmp:a_1", "tmp:b_1", "tmp:c_1", "tmp:no_offset_1"]
        );
    }
}
