use r2ssa::{SSAOp, SSAVar};

use crate::ast::{BinaryOp, CExpr};

use super::context::FoldingContext;
use super::op_lower::is_generic_arg_name;
use super::{MAX_STACK_ALIAS_DEPTH, MAX_STACK_OFFSET_DEPTH};

/// Threshold for detecting 64-bit negative values stored as unsigned.
/// Values above this are likely negative offsets (within ~65536 of u64::MAX).
/// This handles cases like stack offsets: 0xffffffffffffffb8 represents -72.
const LIKELY_NEGATIVE_THRESHOLD: u64 = 0xffffffffffff0000;

impl<'a> FoldingContext<'a> {
    fn stack_synthetic_name(offset: i64) -> String {
        if offset < 0 {
            format!("local_{:x}", (-offset) as u64)
        } else {
            format!("stack_{:x}", offset as u64)
        }
    }

    fn is_reserved_param_alias_name(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        self.inputs
            .param_register_aliases
            .values()
            .any(|alias| alias.eq_ignore_ascii_case(&lower))
    }

    /// Try to extract a stack offset from a variable name or its definition.
    pub(crate) fn extract_stack_offset_from_var(&self, var: &SSAVar) -> Option<i64> {
        let name_lower = var.name.to_lowercase();

        // Direct fp/sp reference
        if self.inputs.arch.is_stack_base_name(&name_lower) {
            return Some(0);
        }

        let key = var.display_name();
        if let Some(slot) = self.stack_slots_map().get(&key) {
            return Some(slot.offset);
        }

        // Check if this variable was defined as fp/sp + offset
        if let Some(expr) = self.definitions_map().get(&key) {
            return self.extract_offset_from_expr(expr);
        }

        None
    }

    /// Extract stack offset from an expression like (rbp + -0x48).
    pub(super) fn extract_offset_from_expr(&self, expr: &CExpr) -> Option<i64> {
        self.extract_offset_from_expr_with_depth(expr, 0)
    }

    pub(super) fn extract_offset_from_expr_with_depth(
        &self,
        expr: &CExpr,
        depth: u32,
    ) -> Option<i64> {
        if depth > MAX_STACK_OFFSET_DEPTH {
            return None;
        }

        match expr {
            CExpr::Paren(inner) => self.extract_offset_from_expr_with_depth(inner, depth + 1),
            CExpr::Cast { expr: inner, .. } => {
                self.extract_offset_from_expr_with_depth(inner, depth + 1)
            }
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                if self.is_stack_base_expr(left) {
                    return self.expr_to_offset(right);
                }
                if self.is_stack_base_expr(right) {
                    return self.expr_to_offset(left);
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                if self.is_stack_base_expr(left) {
                    return self.expr_to_offset(right).map(|off| -off);
                }
                None
            }
            CExpr::Var(name) => {
                let name_lower = name.to_lowercase();
                if self.inputs.arch.is_stack_base_name(&name_lower) {
                    return Some(0);
                }
                self.lookup_definition(name)
                    .and_then(|inner| self.extract_offset_from_expr_with_depth(&inner, depth + 1))
            }
            _ => None,
        }
    }

    pub(super) fn is_stack_base_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => self.inputs.arch.is_stack_base_name(&name.to_lowercase()),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } | CExpr::AddrOf(inner) => {
                self.is_stack_base_expr(inner)
            }
            _ => false,
        }
    }

    /// Convert an expression to an offset value.
    pub(super) fn expr_to_offset(&self, expr: &CExpr) -> Option<i64> {
        match expr {
            CExpr::IntLit(v) => Some(*v),
            CExpr::UIntLit(v) => {
                // Handle negative offsets stored as unsigned
                if *v > LIKELY_NEGATIVE_THRESHOLD {
                    let neg = (!*v).wrapping_add(1);
                    Some(-(neg as i64))
                } else {
                    Some(*v as i64)
                }
            }
            _ => None,
        }
    }

    pub(super) fn arg_alias_for_register_name(&self, reg_name: &str) -> Option<String> {
        let lower = reg_name.to_ascii_lowercase();
        if let Some(alias) = self.inputs.param_register_aliases.get(&lower) {
            return Some(alias.clone());
        }
        self.inputs.arch.arg_alias_for_register_name(reg_name)
    }

    pub(super) fn arg_alias_for_rendered_name(&self, name: &str) -> Option<String> {
        let lower = name.to_lowercase();
        if let Some((base, version)) = lower.rsplit_once('_') {
            if version != "0" {
                return None;
            }
            return self.arg_alias_for_register_name(base);
        }
        self.arg_alias_for_register_name(&lower)
    }

    pub(super) fn is_entry_arg_alias_copy(&self, dst: &SSAVar, src: &SSAVar) -> bool {
        if src.version != 0 {
            return false;
        }
        let Some(src_alias) = self.arg_alias_for_register_name(&src.name) else {
            return false;
        };
        let dst_name = self.var_name(dst);
        is_generic_arg_name(&dst_name) && dst_name.eq_ignore_ascii_case(&src_alias)
    }

    pub(super) fn is_entry_arg_alias_store(&self, addr: &SSAVar, val: &SSAVar) -> bool {
        if val.version != 0 {
            return false;
        }
        if self.arg_alias_for_register_name(&val.name).is_none() {
            return false;
        }
        self.stack_slots_map()
            .get(&addr.display_name())
            .map(|slot| slot.offset)
            .or_else(|| self.extract_stack_offset_from_var(addr))
            .is_some()
    }

    pub(super) fn arg_alias_for_expr(&self, expr: &CExpr) -> Option<String> {
        match expr {
            CExpr::Var(name) => self.arg_alias_for_rendered_name(name),
            CExpr::Paren(inner) => self.arg_alias_for_expr(inner),
            CExpr::Cast { expr: inner, .. } => self.arg_alias_for_expr(inner),
            _ => None,
        }
    }

    /// Check if an address expression is a stack access and return the variable name.
    pub fn simplify_stack_access(&self, addr_expr: &CExpr) -> Option<String> {
        match addr_expr {
            CExpr::Paren(inner) => return self.simplify_stack_access(inner),
            CExpr::Cast { expr: inner, .. } => return self.simplify_stack_access(inner),
            CExpr::AddrOf(inner) => return self.simplify_stack_access(inner),
            CExpr::Var(name) => {
                if let Some(stripped) = name.strip_prefix('&') {
                    return Some(stripped.to_string());
                }
            }
            _ => {}
        }

        if let Some(offset) = self.extract_offset_from_expr(addr_expr) {
            return self.resolve_stack_var(offset);
        }
        None
    }

    pub(super) fn resolve_stack_alias_from_addr_expr(
        &self,
        expr: &CExpr,
        depth: u32,
    ) -> Option<String> {
        if depth > MAX_STACK_ALIAS_DEPTH {
            return None;
        }

        if let Some(alias) = self.simplify_stack_access(expr) {
            return Some(alias);
        }

        match expr {
            CExpr::Var(name) => {
                if let Some(stripped) = name.strip_prefix('&') {
                    return Some(stripped.to_string());
                }
                let parsed_offset = if name == "saved_fp" {
                    Some(0)
                } else if let Some(suffix) = name.strip_prefix("local_") {
                    i64::from_str_radix(suffix, 16).ok().map(|v| -v)
                } else if let Some(suffix) = name.strip_prefix("stack_") {
                    i64::from_str_radix(suffix, 16).ok()
                } else if let Some(suffix) = name.strip_prefix("arg_") {
                    i64::from_str_radix(suffix, 16).ok().map(|v| -v)
                } else {
                    None
                };
                if let Some(offset) = parsed_offset
                    && let Some(alias) = self.resolve_stack_var(offset)
                {
                    return Some(alias);
                }
                self.lookup_definition(name)
                    .and_then(|inner| self.resolve_stack_alias_from_addr_expr(&inner, depth + 1))
            }
            CExpr::Paren(inner) => self.resolve_stack_alias_from_addr_expr(inner, depth + 1),
            CExpr::Cast { expr: inner, .. } => {
                self.resolve_stack_alias_from_addr_expr(inner, depth + 1)
            }
            CExpr::Deref(inner) => self.resolve_stack_alias_from_addr_expr(inner, depth + 1),
            _ => None,
        }
    }
    pub(crate) fn stack_var_for_addr_var(&self, addr: &SSAVar) -> Option<String> {
        let addr_key = addr.display_name();
        if let Some(alias) =
            self.resolve_stack_alias_from_addr_expr(&CExpr::Var(addr_key.clone()), 0)
        {
            return Some(alias);
        }
        if let Some(alias) =
            self.resolve_stack_alias_from_addr_expr(&CExpr::Var(self.var_name(addr)), 0)
        {
            return Some(alias);
        }
        self.extract_stack_offset_from_var(addr)
            .and_then(|offset| self.resolve_stack_var(offset))
    }

    pub(super) fn external_stack_name_for_offset(&self, offset: i64) -> Option<String> {
        if let Some(var) = self.inputs.external_stack_vars.get(&offset)
            && !var.name.is_empty()
            && !self.is_reserved_param_alias_name(&var.name)
        {
            return Some(var.name.clone());
        }

        for (ext_offset, var) in self.inputs.external_stack_vars {
            if var.name.is_empty() {
                continue;
            }
            let base_lower = var.base.as_deref().unwrap_or_default().to_ascii_lowercase();
            let is_frame_based = self.inputs.arch.is_frame_pointer_name(&base_lower);
            if is_frame_based
                && -*ext_offset == offset
                && !self.is_reserved_param_alias_name(&var.name)
            {
                return Some(var.name.clone());
            }
        }

        None
    }

    pub(super) fn canonicalize_stack_name(&self, name: &str) -> Option<String> {
        let offset = if name == "saved_fp" {
            Some(0)
        } else if let Some(suffix) = name.strip_prefix("local_") {
            i64::from_str_radix(suffix, 16).ok()
        } else if let Some(suffix) = name.strip_prefix("stack_") {
            i64::from_str_radix(suffix, 16).ok()
        } else if let Some(suffix) = name.strip_prefix("arg_") {
            i64::from_str_radix(suffix, 16).ok().map(|v| -v)
        } else {
            None
        }?;

        self.external_stack_name_for_offset(offset)
    }

    /// Resolve a stack variable name by signed stack offset.
    pub fn resolve_stack_var(&self, offset: i64) -> Option<String> {
        let resolved = self
            .stack_vars_map()
            .get(&offset)
            .cloned()
            .map(|name| self.canonicalize_stack_name(&name).unwrap_or(name))
            .or_else(|| self.external_stack_name_for_offset(offset))
            .or_else(|| {
                self.stack_slots_map()
                    .values()
                    .any(|slot| slot.offset == offset)
                    .then(|| Self::stack_synthetic_name(offset))
            })
            .or_else(|| {
                (offset < 0
                    && (!self.stack_slots_map().is_empty() || !self.definitions_map().is_empty()))
                .then(|| Self::stack_synthetic_name(offset))
            });
        resolved.map(|name| {
            if self.is_reserved_param_alias_name(&name) {
                Self::stack_synthetic_name(offset)
            } else {
                name
            }
        })
    }

    pub(super) fn rewrite_stack_expr(&self, expr: CExpr) -> CExpr {
        let rewritten = expr.map_children(&mut |child| self.rewrite_stack_expr(child));

        if let CExpr::Var(name) = &rewritten
            && let Some(alias) =
                self.resolve_stack_alias_from_addr_expr(&CExpr::Var(name.clone()), 0)
            && alias != *name
            && !super::op_lower::is_generic_stack_placeholder_alias(&alias)
        {
            return CExpr::Var(alias);
        }

        if matches!(
            rewritten,
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                ..
            } | CExpr::Paren(_)
                | CExpr::Cast { .. }
        ) && let Some(alias) = self.resolve_stack_alias_from_addr_expr(&rewritten, 0)
            && !super::op_lower::is_generic_stack_placeholder_alias(&alias)
        {
            return CExpr::Var(alias);
        }

        match rewritten {
            CExpr::Deref(inner) => {
                if let Some(alias) = self.resolve_stack_alias_from_addr_expr(&inner, 0)
                    && !super::op_lower::is_generic_stack_placeholder_alias(&alias)
                {
                    return CExpr::Var(alias);
                }
                if let Some(var_name) = self.extract_known_stack_var_name(&inner) {
                    return CExpr::Var(var_name);
                }
                CExpr::Deref(inner)
            }
            other => other,
        }
    }

    pub(super) fn extract_known_stack_var_name(&self, expr: &CExpr) -> Option<String> {
        match expr {
            CExpr::Var(name) => {
                if self
                    .stack_vars_map()
                    .values()
                    .any(|candidate| candidate == name)
                {
                    Some(name.clone())
                } else {
                    None
                }
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.extract_known_stack_var_name(inner)
            }
            _ => None,
        }
    }

    pub(super) fn is_zeroing_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Binary {
                op: BinaryOp::BitXor | BinaryOp::Sub,
                left,
                right,
            } => left == right,
            _ => false,
        }
    }

    /// Check if an operation is part of stack frame setup/teardown (prologue/epilogue).
    pub fn is_stack_frame_op(&self, op: &SSAOp) -> bool {
        if !self.hide_stack_frame {
            return false;
        }

        match op {
            // push rbp: Store to (rsp - 8) where value is rbp
            SSAOp::Store { addr, val, .. } => {
                let addr_name = addr.name.to_lowercase();
                let val_name = val.name.to_lowercase();
                let addr_is_sp = self.inputs.arch.is_stack_pointer_name(&addr_name);
                // Store of fp to stack (push fp)
                if self.inputs.arch.is_frame_pointer_name(&val_name)
                    && (addr_is_sp || addr_name.contains("tmp:"))
                {
                    return true;
                }
                // Store return address to stack
                if val_name.contains("rip") || val_name.contains("eip") {
                    return true;
                }
                // Store constant to RSP-derived address (pre-call return address push)
                if val.is_const() && (addr_is_sp || addr_name.contains("tmp:")) {
                    // Check if this constant was consumed by call-arg analysis
                    let val_key = val.display_name();
                    if self.consumed_by_call_set().contains(&val_key) {
                        return true;
                    }
                }
                // Store callee-saved register to stack (prologue push)
                // The P-code often uses temps: Copy tmp:X = RBX; Store [RSP], tmp:X
                // So we need to check both direct and indirect through temps.
                if (addr_is_sp || addr_name.contains("tmp:")) && !val.is_const() {
                    // Direct: val is a callee-saved register
                    if self.inputs.arch.is_callee_saved_name(&val_name) {
                        return true;
                    }
                    // Indirect: val is a temp, trace it back via copy_sources
                    if val.name.starts_with("tmp:") {
                        let val_key = val.display_name();
                        if let Some(src_key) = self.copy_sources_map().get(&val_key) {
                            let src_lower = src_key.to_lowercase();
                            if self.inputs.arch.is_callee_saved_name(&src_lower)
                                || self.inputs.arch.is_frame_pointer_name(&src_lower)
                            {
                                return true;
                            }
                        }
                    }
                }
                false
            }
            // mov rbp, rsp: Copy from sp to fp
            SSAOp::Copy { dst, src } => {
                let dst_name = dst.name.to_lowercase();
                let src_name = src.name.to_lowercase();
                // mov fp, sp (frame pointer setup)
                if self.inputs.arch.is_frame_pointer_name(&dst_name)
                    && self.inputs.arch.is_stack_pointer_name(&src_name)
                {
                    return true;
                }
                // mov sp, fp (frame pointer teardown)
                if self.inputs.arch.is_stack_pointer_name(&dst_name)
                    && self.inputs.arch.is_frame_pointer_name(&src_name)
                {
                    return true;
                }
                false
            }
            // sub rsp, N: Stack allocation
            SSAOp::IntSub { dst, a, b } => {
                let dst_name = dst.name.to_lowercase();
                let a_name = a.name.to_lowercase();
                // sp = sp - const (stack allocation)
                if self.inputs.arch.is_stack_pointer_name(&dst_name)
                    && self.inputs.arch.is_stack_pointer_name(&a_name)
                    && b.is_const()
                {
                    return true;
                }
                false
            }
            // add rsp, N: Stack deallocation
            SSAOp::IntAdd { dst, a, b } => {
                let dst_name = dst.name.to_lowercase();
                let a_name = a.name.to_lowercase();
                // sp = sp + const (stack deallocation)
                if self.inputs.arch.is_stack_pointer_name(&dst_name)
                    && self.inputs.arch.is_stack_pointer_name(&a_name)
                    && b.is_const()
                {
                    return true;
                }
                // sp = fp + const (leave instruction equivalent)
                if self.inputs.arch.is_stack_pointer_name(&dst_name)
                    && self.inputs.arch.is_frame_pointer_name(&a_name)
                    && b.is_const()
                {
                    return true;
                }
                false
            }
            // pop rbp: Load from stack to fp
            SSAOp::Load { dst, addr, .. } => {
                let dst_name = dst.name.to_lowercase();
                let addr_name = addr.name.to_lowercase();
                let addr_is_sp = self.inputs.arch.is_stack_pointer_name(&addr_name);
                // Load fp from stack (pop fp)
                if self.inputs.arch.is_frame_pointer_name(&dst_name)
                    && (addr_is_sp || addr_name.contains("tmp:"))
                {
                    return true;
                }
                // Load return address (ret)
                if dst_name.contains("rip") || dst_name.contains("eip") {
                    return true;
                }
                // Load callee-saved register from stack (epilogue pop)
                if (addr_is_sp || addr_name.contains("tmp:"))
                    && self.inputs.arch.is_callee_saved_name(&dst_name)
                {
                    return true;
                }
                false
            }
            _ => false,
        }
    }
}
