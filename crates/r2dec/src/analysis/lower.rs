use std::collections::{HashMap, HashSet};

use r2ssa::{SSAOp, SSAVar};
use r2types::TypeOracle;

use super::utils::{
    format_traced_name, is_constant_or_memory_name, is_low_signal_ssa_storage_name,
    is_temporary_name, is_temporary_or_constant_name, parse_const_value, ssa_render_base_name,
};
use super::{
    BaseRef, NormalizedAddr, PtrArith, ScalarValue, SemanticValue, StackSlotProvenance, UseInfo,
    ValueProvenance, ValueRef,
};
use crate::address::parse_address_from_var_name;
use crate::ast::{BinaryOp, CExpr, CType, UnaryOp};

pub(crate) fn no_string_literals() -> &'static std::collections::BTreeMap<u64, String> {
    static EMPTY: std::sync::OnceLock<std::collections::BTreeMap<u64, String>> =
        std::sync::OnceLock::new();
    EMPTY.get_or_init(std::collections::BTreeMap::new)
}

pub(crate) struct LowerCtx<'a> {
    pub(crate) use_info: Option<&'a UseInfo>,
    pub(crate) definitions: &'a HashMap<String, CExpr>,
    pub(crate) semantic_values: &'a HashMap<String, SemanticValue>,
    pub(crate) use_counts: &'a HashMap<String, usize>,
    pub(crate) condition_vars: &'a HashSet<String>,
    pub(crate) pinned: &'a HashSet<String>,
    pub(crate) var_aliases: &'a HashMap<String, String>,
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
    pub(crate) type_hints: &'a HashMap<String, CType>,
    pub(crate) ptr_arith: &'a HashMap<String, PtrArith>,
    pub(crate) stack_slots: &'a HashMap<String, StackSlotProvenance>,
    pub(crate) forwarded_values: &'a HashMap<String, ValueProvenance>,
    pub(crate) type_oracle: Option<&'a dyn TypeOracle>,
    /// Where a rendered name is written down, so building a reference can mint one.
    pub(crate) symbols: &'a std::cell::RefCell<crate::symbol::SymbolTable>,
    /// String literals the source recorded, for rendering a constant that
    /// points at text as the text.
    pub(crate) string_literals: &'a std::collections::BTreeMap<u64, String>,
}

impl<'a> LowerCtx<'a> {
    /// How a reference is spelled, as a handle that outlives the table borrow.
    pub(crate) fn spelling(&self, id: crate::symbol::SymbolId) -> std::rc::Rc<str> {
        crate::symbol::spelling(self.symbols, id)
    }

    fn lookup_type_hint(&self, name: &str) -> Option<&CType> {

        self.use_info
            .map(|info| &info.type_hints)
            .unwrap_or(self.type_hints)
            .get(name)
            .or_else(|| {
                self.use_info
                    .map(|info| &info.type_hints)
                    .unwrap_or(self.type_hints)
                    .get(&name.to_ascii_lowercase())
            })
    }

    fn definition_for_name(&self, name: &str) -> Option<&CExpr> {

        self.definitions.get(name).or_else(|| {
            self.use_info.and_then(|info| {
                info.value_id_for_name(name)
                    .and_then(|value_id| info.render_definition_for_value(value_id))
                    .or_else(|| info.render_definition_for_name(name))
            })
        })
    }

    /// The definition of what this identifier renders.
    ///
    /// A rendered spelling is not the SSA display name the definitions are keyed
    /// by, so asking with the spelling misses a definition that is present.
    fn definition_for_symbol(&self, id: crate::symbol::SymbolId) -> Option<&CExpr> {
        match self.symbols.borrow().ssa_name(id) {
            Some(ssa_name) => self.definition_for_name(&ssa_name),
            None => self.definition_for_name(&self.spelling(id)),
        }
    }

    fn definition_for_var(&self, var: &SSAVar) -> Option<&CExpr> {
        let key = var.display_name();
        self.definitions
            .get(&key)
            .or_else(|| self.use_info.and_then(|info| info.definition_for_var(var)))
    }

    fn semantic_value_for_name(&self, name: &str) -> Option<&SemanticValue> {
        self.semantic_values.get(name).or_else(|| {
            self.use_info.and_then(|info| {
                info.value_id_for_name(name)
                    .and_then(|value_id| info.render_semantic_value_for_value(value_id))
                    .or_else(|| info.render_semantic_value_for_name(name))
            })
        })
    }

    fn semantic_value_for_var(&self, var: &SSAVar) -> Option<&SemanticValue> {
        let key = var.display_name();
        self.semantic_values.get(&key).or_else(|| {
            self.use_info
                .and_then(|info| info.semantic_value_for_var(var))
        })
    }

    fn forwarded_value_for_name(&self, name: &str) -> Option<&ValueProvenance> {
        self.forwarded_values.get(name).or_else(|| {
            self.use_info.and_then(|info| {
                info.value_id_for_name(name)
                    .and_then(|value_id| info.render_forwarded_value_for_value(value_id))
                    .or_else(|| info.render_forwarded_value_for_name(name))
            })
        })
    }

    fn forwarded_value_for_var(&self, var: &SSAVar) -> Option<&ValueProvenance> {
        let key = var.display_name();
        self.forwarded_values.get(&key).or_else(|| {
            self.use_info
                .and_then(|info| info.forwarded_value_for_var(var))
        })
    }

    fn ptr_arith_for_var(&self, var: &SSAVar) -> Option<&PtrArith> {
        let key = var.display_name();
        self.ptr_arith
            .get(&key)
            .or_else(|| self.use_info.and_then(|info| info.ptr_arith_for_var(var)))
    }

    fn use_count_for_name(&self, name: &str) -> usize {
        self.use_info
            .map(|info| info.use_count_for_name(name))
            .unwrap_or_else(|| self.use_counts.get(name).copied().unwrap_or(0))
    }

    fn is_condition_name(&self, name: &str) -> bool {
        self.use_info
            .map(|info| info.is_condition_name(name))
            .unwrap_or_else(|| self.condition_vars.contains(name))
    }

    fn var_alias_for_name(&self, name: &str) -> Option<&String> {
        self.var_aliases.get(name)
    }

    fn stack_slot_name_map(&self) -> &HashMap<String, StackSlotProvenance> {
        self.stack_slots
    }

    pub(crate) fn var_name(&self, var: &SSAVar) -> String {
        crate::naming::spell_var(var, self)
    }

    pub(crate) fn get_expr(&self, var: &SSAVar) -> CExpr {
        self.get_expr_with_depth(var, 0, &mut HashSet::new())
    }

    fn get_expr_with_depth(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if var.is_const() {
            return self.const_to_expr(var);
        }

        if let Some(addr) = parse_address_from_var_name(&var.name)
            && let Some(expr) = self.resolve_addr_literal(addr)
        {
            return expr;
        }

        let key = var.display_name();
        if let Some(prov) = self.forwarded_value_for_var(var)
            && depth < 8
            && visited.insert(format!("prov:{key}"))
        {
            return self.expr_for_ssa_name_with_depth(&prov.source, depth + 1, visited);
        }
        if let Some(expr) = self.render_semantic_value_for_var(var, depth, visited) {
            return expr;
        }
        if depth < 8
            && self.should_inline(&key)
            && visited.insert(key.clone())
            && let Some(expr) = self.definition_for_var(var)
        {
            return expr.clone();
        }

        crate::symbol::var_ref(self.symbols, self.var_name(var))
    }

    pub(crate) fn expr_for_ssa_name(&self, name: &str) -> CExpr {

        self.expr_for_ssa_name_with_depth(name, 0, &mut HashSet::new())
    }

    pub(crate) fn expr_for_semantic_value(&self, value: &SemanticValue) -> Option<CExpr> {
        self.render_semantic_value(value, 0, &mut HashSet::new())
    }

    fn expr_for_ssa_name_with_depth(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > 8 {
            return crate::symbol::var_ref(self.symbols, format_traced_name(name, self.var_aliases));
        }

        if let Some(val) = parse_const_value(name) {
            if let Some(expr) = self.resolve_addr_literal(val) {
                return expr;
            }
            return if val > 0x7fffffff {
                CExpr::UIntLit(val)
            } else {
                CExpr::IntLit(val as i64)
            };
        }

        if let Some(addr) = parse_address_from_var_name(name)
            && let Some(expr) = self.resolve_addr_literal(addr)
        {
            return expr;
        }

        if let Some(prov) = self.forwarded_value_for_name(name)
            && visited.insert(format!("prov:{name}"))
        {
            return self.expr_for_ssa_name_with_depth(&prov.source, depth + 1, visited);
        }

        if let Some(expr) = self.render_semantic_value_by_name(name, depth, visited) {
            return expr;
        }

        if let Some(expr) = self.definition_for_name(name)
            && visited.insert(name.to_string())
        {
            return expr.clone();
        }

        if let Some(alias) = self.var_alias_for_name(name) {
            return crate::symbol::var_ref(self.symbols, alias.clone());
        }

        crate::symbol::var_ref(self.symbols, format_traced_name(name, self.var_aliases))
    }

    pub(crate) fn op_to_expr(&self, op: &SSAOp) -> CExpr {
        match op {
            SSAOp::Copy { src, .. } => self.get_expr(src),
            SSAOp::Load { dst, addr, space } if *space != r2il::SpaceId::Ram => CExpr::call(
                crate::symbol::var_ref(self.symbols, "r2s_unsupported_space_load".to_string()),
                vec![
                    CExpr::StringLit(space.to_string()),
                    self.get_expr(addr),
                    CExpr::UIntLit(u64::from(dst.size)),
                ],
            ),
            SSAOp::Load { dst, addr, .. } => {
                let prefer_memory_access = matches!(
                    self.semantic_value_for_var(dst),
                    Some(SemanticValue::Address(_))
                );
                if prefer_memory_access {
                    if let Some(sub) = self.try_subscript_from_var(addr, dst.size) {
                        return sub;
                    }
                    if let Some(member) = self.try_member_access_from_var(addr) {
                        return member;
                    }
                }
                if let Some(expr) = self.render_semantic_value_for_var(dst, 0, &mut HashSet::new())
                {
                    expr
                } else if let Some(sub) = self.try_subscript_from_var(addr, dst.size) {
                    sub
                } else if let Some(member) = self.try_member_access_from_var(addr) {
                    member
                } else {
                    self.typed_deref_expr(addr, dst.size)
                }
            }
            SSAOp::IntAdd { a, b, .. } => self.binary_expr(BinaryOp::Add, a, b),
            SSAOp::IntSub { a, b, .. } => self.binary_expr(BinaryOp::Sub, a, b),
            SSAOp::IntMult { a, b, .. } => self.binary_expr(BinaryOp::Mul, a, b),
            SSAOp::IntDiv { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Div, a, b, Some(uint_type_from_size(dst.size)))
            }
            SSAOp::IntSDiv { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Div, a, b, Some(type_from_size(dst.size)))
            }
            SSAOp::IntRem { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Mod, a, b, Some(uint_type_from_size(dst.size)))
            }
            SSAOp::IntSRem { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Mod, a, b, Some(type_from_size(dst.size)))
            }
            SSAOp::IntAnd { a, b, .. } => self.binary_expr(BinaryOp::BitAnd, a, b),
            SSAOp::IntOr { a, b, .. } => self.binary_expr(BinaryOp::BitOr, a, b),
            SSAOp::IntXor { a, b, .. } => self.binary_expr(BinaryOp::BitXor, a, b),
            SSAOp::IntLeft { a, b, .. } => self.binary_expr(BinaryOp::Shl, a, b),
            SSAOp::IntRight { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Shr, a, b, Some(uint_type_from_size(dst.size)))
            }
            SSAOp::IntSRight { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Shr, a, b, Some(type_from_size(dst.size)))
            }
            SSAOp::IntLess { a, b, .. } => self.typed_binary_expr(
                BinaryOp::Lt,
                a,
                b,
                Some(uint_type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntSLess { a, b, .. } => {
                self.typed_binary_expr(BinaryOp::Lt, a, b, Some(type_from_size(a.size.max(b.size))))
            }
            SSAOp::IntLessEqual { a, b, .. } => self.typed_binary_expr(
                BinaryOp::Le,
                a,
                b,
                Some(uint_type_from_size(a.size.max(b.size))),
            ),
            SSAOp::IntSLessEqual { a, b, .. } => {
                self.typed_binary_expr(BinaryOp::Le, a, b, Some(type_from_size(a.size.max(b.size))))
            }
            SSAOp::IntEqual { a, b, .. } => self.binary_expr(BinaryOp::Eq, a, b),
            SSAOp::IntNotEqual { a, b, .. } => self.binary_expr(BinaryOp::Ne, a, b),
            SSAOp::IntNegate { src, .. } => CExpr::unary(UnaryOp::Neg, self.get_expr(src)),
            SSAOp::IntNot { src, .. } => CExpr::unary(UnaryOp::BitNot, self.get_expr(src)),
            SSAOp::BoolAnd { a, b, .. } => self.binary_expr(BinaryOp::And, a, b),
            SSAOp::BoolOr { a, b, .. } => self.binary_expr(BinaryOp::Or, a, b),
            SSAOp::BoolXor { a, b, .. } => self.binary_expr(BinaryOp::BitXor, a, b),
            SSAOp::BoolNot { src, .. } => CExpr::unary(UnaryOp::Not, self.get_expr(src)),
            SSAOp::IntZExt { dst, src } | SSAOp::IntSExt { dst, src } => {
                CExpr::cast(type_from_size(dst.size), self.get_expr(src))
            }
            SSAOp::Trunc { dst, src } => CExpr::cast(type_from_size(dst.size), self.get_expr(src)),
            SSAOp::Piece { dst, hi, lo } => {
                let shift_bits = lo.size.saturating_mul(8);
                let dst_ty = uint_type_from_size(dst.size);
                let hi_cast = CExpr::cast(dst_ty.clone(), self.get_expr(hi));
                let lo_cast = CExpr::cast(dst_ty.clone(), self.get_expr(lo));
                let shifted = if shift_bits == 0 {
                    hi_cast
                } else {
                    CExpr::binary(BinaryOp::Shl, hi_cast, CExpr::IntLit(shift_bits as i64))
                };
                CExpr::binary(BinaryOp::BitOr, shifted, lo_cast)
            }
            SSAOp::Subpiece { dst, src, offset } => {
                if *offset == 0 && dst.size == src.size {
                    self.get_expr(src)
                } else if *offset == 0 {
                    CExpr::cast(uint_type_from_size(dst.size), self.get_expr(src))
                } else {
                    let shift_bits = offset.saturating_mul(8);
                    let src_cast = CExpr::cast(uint_type_from_size(src.size), self.get_expr(src));
                    let shifted =
                        CExpr::binary(BinaryOp::Shr, src_cast, CExpr::IntLit(shift_bits as i64));
                    CExpr::cast(uint_type_from_size(dst.size), shifted)
                }
            }
            SSAOp::FloatAdd { a, b, .. } => self.binary_expr(BinaryOp::Add, a, b),
            SSAOp::FloatSub { a, b, .. } => self.binary_expr(BinaryOp::Sub, a, b),
            SSAOp::FloatMult { a, b, .. } => self.binary_expr(BinaryOp::Mul, a, b),
            SSAOp::FloatDiv { a, b, .. } => self.binary_expr(BinaryOp::Div, a, b),
            SSAOp::FloatNeg { src, .. } => CExpr::unary(UnaryOp::Neg, self.get_expr(src)),
            SSAOp::FloatAbs { src, .. } => {
                CExpr::call(crate::symbol::var_ref(self.symbols, "fabs".to_string()), vec![self.get_expr(src)])
            }
            SSAOp::FloatSqrt { src, .. } => {
                CExpr::call(crate::symbol::var_ref(self.symbols, "sqrt".to_string()), vec![self.get_expr(src)])
            }
            SSAOp::FloatCeil { src, .. } => {
                CExpr::call(crate::symbol::var_ref(self.symbols, "ceil".to_string()), vec![self.get_expr(src)])
            }
            SSAOp::FloatFloor { src, .. } => {
                CExpr::call(crate::symbol::var_ref(self.symbols, "floor".to_string()), vec![self.get_expr(src)])
            }
            SSAOp::FloatRound { src, .. } => {
                CExpr::call(crate::symbol::var_ref(self.symbols, "round".to_string()), vec![self.get_expr(src)])
            }
            SSAOp::FloatNaN { src, .. } => {
                CExpr::call(crate::symbol::var_ref(self.symbols, "isnan".to_string()), vec![self.get_expr(src)])
            }
            SSAOp::FloatLess { a, b, .. } => self.binary_expr(BinaryOp::Lt, a, b),
            SSAOp::FloatLessEqual { a, b, .. } => self.binary_expr(BinaryOp::Le, a, b),
            SSAOp::FloatEqual { a, b, .. } => self.binary_expr(BinaryOp::Eq, a, b),
            SSAOp::FloatNotEqual { a, b, .. } => self.binary_expr(BinaryOp::Ne, a, b),
            SSAOp::Int2Float { dst, src } => {
                let ty = CType::Float(dst.size);
                CExpr::cast(ty, self.get_expr(src))
            }
            SSAOp::Float2Int { dst, src } => {
                CExpr::cast(type_from_size(dst.size), self.get_expr(src))
            }
            SSAOp::FloatFloat { dst, src } => {
                CExpr::cast(CType::Float(dst.size), self.get_expr(src))
            }
            SSAOp::Cast { dst, src } => CExpr::cast(type_from_size(dst.size), self.get_expr(src)),
            SSAOp::Select {
                cond,
                if_true,
                if_false,
                ..
            } => CExpr::Ternary {
                cond: Box::new(self.get_expr(cond)),
                then_expr: Box::new(self.get_expr(if_true)),
                else_expr: Box::new(self.get_expr(if_false)),
            },
            SSAOp::Call { target } => CExpr::call(self.get_expr(target), vec![]),
            SSAOp::CallInd { target } => {
                CExpr::call(CExpr::Deref(Box::new(self.get_expr(target))), vec![])
            }
            SSAOp::CallOther {
                output: _,
                userop,
                inputs,
            } => {
                let mut args = Vec::with_capacity(inputs.len() + 1);
                args.push(CExpr::StringLit(format!("userop_{}", userop)));
                for input in inputs {
                    args.push(self.get_expr(input));
                }
                CExpr::call(CExpr::External {
                    name: "callother".to_string(),
                    kind: crate::symbol::ExternalKind::Intrinsic,
                }, args)
            }
            SSAOp::CpuId { .. } => CExpr::call(
                CExpr::External {
                    name: "callother".to_string(),
                    kind: crate::symbol::ExternalKind::Intrinsic,
                },
                vec![CExpr::StringLit("cpuid".to_string())],
            ),
            SSAOp::PtrAdd {
                dst,
                base,
                index,
                element_size,
            } => self
                .render_semantic_value_for_var(dst, 0, &mut HashSet::new())
                .unwrap_or_else(|| self.ptr_arith_expr(base, index, *element_size, false)),
            SSAOp::PtrSub {
                dst,
                base,
                index,
                element_size,
            } => self
                .render_semantic_value_for_var(dst, 0, &mut HashSet::new())
                .unwrap_or_else(|| self.ptr_arith_expr(base, index, *element_size, true)),
            _ => {
                if let Some(dst) = op.dst() {
                    crate::symbol::var_ref(self.symbols, self.var_name(dst))
                } else {
                    CExpr::External {
                        name: "__unhandled_op__".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    }
                }
            }
        }
    }

    fn render_semantic_value_by_name(
        &self,
        name: &str,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {

        if depth > 8 || !visited.insert(format!("sem:{name}")) {
            return None;
        }

        let rendered = self
            .semantic_value_for_name(name)
            .and_then(|value| self.render_semantic_value(value, depth + 1, visited));
        visited.remove(&format!("sem:{name}"));
        rendered
    }

    fn render_semantic_value_for_var(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let name = var.display_name();
        if depth > 8 || !visited.insert(format!("sem:{name}")) {
            return None;
        }

        let rendered = self
            .semantic_value_for_var(var)
            .and_then(|value| self.render_semantic_value(value, depth + 1, visited));
        visited.remove(&format!("sem:{name}"));
        rendered
    }

    fn render_semantic_value(
        &self,
        value: &SemanticValue,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        match value {
            SemanticValue::Scalar(ScalarValue::Expr(expr)) => Some(expr.clone()),
            SemanticValue::Scalar(ScalarValue::Root(value)) => {
                self.render_value_ref(value, depth, visited)
            }
            SemanticValue::Address(shape) => self.render_addr_shape(shape, depth, visited),
            SemanticValue::Load { space, addr, size } => Some(if *space == r2il::SpaceId::Ram {
                self.render_load_from_shape(addr, *size, depth, visited)?
            } else {
                self.unsupported_space_load_expr(*space, addr, *size, depth, visited)
            }),
            SemanticValue::Unknown => None,
        }
    }

    fn render_load_from_shape(
        &self,
        shape: &NormalizedAddr,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if shape.index.is_none()
            && shape.offset_bytes == 0
            && let BaseRef::StackSlot(offset) = shape.base
            && let Some(name) = self.stack_slot_name_for_offset(offset)
            && (matches!(
                self.lookup_type_hint(&name),
                Some(CType::Pointer(_)) | Some(CType::Array(_, _))
            ) || (elem_size < self.ptr_bytes()
                && self.stack_slot_has_pointer_backed_source(offset, elem_size)))
        {
            return Some(CExpr::Deref(Box::new(crate::symbol::var_ref(self.symbols, name))));
        }

        if let Some(index) = &shape.index {
            let scale = shape.scale_bytes.unsigned_abs() as u32;
            if scale == elem_size && shape.offset_bytes == 0 {
                let base_expr = self.render_addr_base(shape, depth + 1, visited)?;
                let index_expr = self.render_value_ref(index, depth + 1, visited)?;
                return self.build_subscript_expr(
                    self.normalize_pointer_base_expr(&base_expr, 0),
                    self.normalize_index_expr(&index_expr, 0)?,
                    uint_type_from_size(elem_size),
                    shape.scale_bytes < 0,
                );
            }
        }

        self.render_addr_shape(shape, depth + 1, visited)
            .map(|expr| CExpr::Deref(Box::new(expr)))
    }

    fn unsupported_space_load_expr(
        &self,
        space: r2il::SpaceId,
        addr: &NormalizedAddr,
        size: u32,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        let addr = self
            .render_addr_shape(addr, depth + 1, visited)
            .unwrap_or_else(|| crate::symbol::var_ref(self.symbols, "r2s_unresolved_memory_address".to_string()));
        CExpr::call(
            crate::symbol::var_ref(self.symbols, "r2s_unsupported_space_load".to_string()),
            vec![
                CExpr::StringLit(space.to_string()),
                addr,
                CExpr::UIntLit(u64::from(size)),
            ],
        )
    }

    fn render_addr_shape(
        &self,
        shape: &NormalizedAddr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        if depth > 8 {
            return None;
        }

        let mut expr = self.render_addr_base(shape, depth + 1, visited)?;
        if let Some(index) = &shape.index {
            let index_expr = self.render_value_ref(index, depth + 1, visited)?;
            let scaled = if shape.scale_bytes.unsigned_abs() <= 1 {
                index_expr
            } else {
                CExpr::binary(
                    BinaryOp::Mul,
                    index_expr,
                    CExpr::IntLit(shape.scale_bytes.unsigned_abs() as i64),
                )
            };
            expr = CExpr::binary(
                if shape.scale_bytes < 0 {
                    BinaryOp::Sub
                } else {
                    BinaryOp::Add
                },
                expr,
                scaled,
            );
        }
        if shape.offset_bytes != 0 {
            expr = CExpr::binary(
                if shape.offset_bytes < 0 {
                    BinaryOp::Sub
                } else {
                    BinaryOp::Add
                },
                expr,
                CExpr::IntLit(shape.offset_bytes.unsigned_abs() as i64),
            );
        }
        Some(expr)
    }

    fn render_addr_base(
        &self,
        shape: &NormalizedAddr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        match &shape.base {
            BaseRef::StackSlot(_) => None,
            BaseRef::Value(base) => self.render_value_ref(base, depth + 1, visited),
            BaseRef::Raw(expr) => Some(expr.clone()),
        }
    }

    fn stack_slot_name_for_offset(&self, offset: i64) -> Option<String> {
        self.stack_slot_name_map()
            .iter()
            .filter(|(_, slot)| slot.offset == offset)
            .map(|(name, _)| name.clone())
            .min_by_key(|name| {
                let generic = name.starts_with("local_") || name.starts_with("stack_");
                let synthetic = is_temporary_name(name) || name.contains(':');
                (generic, synthetic, name.clone())
            })
    }

    fn ptr_bytes(&self) -> u32 {
        self.stack_slot_name_map()
            .keys()
            .find_map(|name| self.lookup_type_hint(name).and_then(|ty| ty.bits()))
            .map(|bits| bits.div_ceil(8).max(1))
            .unwrap_or(8)
    }

    fn stack_slot_has_pointer_backed_source(&self, offset: i64, elem_size: u32) -> bool {
        self.forwarded_values.values().any(|prov| {
            prov.stack_slot == Some(offset)
                && prov
                    .source_var
                    .as_ref()
                    .is_some_and(|var| var.size > elem_size && var.size >= self.ptr_bytes())
        })
    }

    fn render_value_ref(
        &self,
        value: &ValueRef,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> Option<CExpr> {
        let name = value.display_name();
        let visit_key = format!("val:{name}");
        if !visited.insert(visit_key.clone()) {
            return None;
        }
        let expr = self.expr_for_ssa_name_with_depth(&name, depth, visited);
        visited.remove(&visit_key);
        Some(expr)
    }

    fn should_inline(&self, var_name: &str) -> bool {
        let use_count = self.use_count_for_name(var_name);
        if use_count == 0 || use_count > 3 {
            return false;
        }

        if self.pinned.contains(var_name) {
            return false;
        }

        if self.is_condition_name(var_name) {
            return false;
        }

        if is_temporary_or_constant_name(var_name) {
            return true;
        }

        use_count == 1
    }

    fn const_to_expr(&self, var: &SSAVar) -> CExpr {
        let val = parse_const_value(&var.name).unwrap_or(0);
        if let Some(expr) = self.resolve_addr_literal(val) {
            return expr;
        }
        if let Some(addr) = parse_address_from_var_name(&var.name)
            && let Some(expr) = self.resolve_addr_literal(addr)
        {
            return expr;
        }
        if val > 0x7fffffff {
            CExpr::UIntLit(val)
        } else {
            CExpr::IntLit(val as i64)
        }
    }

    /// The literal stored at `addr`, when the source said what is there.
    ///
    /// Only strings resolve. A function or symbol name at an address is a label
    /// for that address, not the value held in it, and printing one where a
    /// value belongs would state something the program never says. A string is
    /// different: it is the content, and `"secret123"` is the same fact as the
    /// address of those bytes, spelled so a reader can use it.
    fn resolve_addr_literal(&self, addr: u64) -> Option<CExpr> {
        self.string_literals
            .get(&addr)
            .map(|text| CExpr::StringLit(text.clone()))
    }

    fn binary_expr(&self, op: BinaryOp, a: &SSAVar, b: &SSAVar) -> CExpr {
        CExpr::binary(op, self.binary_operand_expr(a), self.binary_operand_expr(b))
    }

    fn cast_expr_if_needed(&self, expr: CExpr, ty: CType) -> CExpr {
        if let CExpr::Cast { ty: existing, .. } = &expr
            && *existing == ty
        {
            return expr;
        }
        CExpr::cast(ty, expr)
    }

    fn typed_binary_expr(
        &self,
        op: BinaryOp,
        a: &SSAVar,
        b: &SSAVar,
        operand_ty: Option<CType>,
    ) -> CExpr {
        let mut lhs = self.binary_operand_expr(a);
        let mut rhs = self.binary_operand_expr(b);
        if let Some(ty) = operand_ty {
            lhs = self.cast_expr_if_needed(lhs, ty.clone());
            rhs = self.cast_expr_if_needed(rhs, ty);
        }
        CExpr::binary(op, lhs, rhs)
    }

    fn binary_operand_expr(&self, var: &SSAVar) -> CExpr {
        let key = var.display_name();
        if self.should_keep_low_signal_address_temp_visible(&key) {
            return crate::symbol::var_ref(self.symbols, self.var_name(var));
        }
        self.get_expr(var)
    }

    fn should_keep_low_signal_address_temp_visible(&self, name: &str) -> bool {
        if !is_low_signal_lowering_name(name) {
            return false;
        }
        if !matches!(
            self.semantic_value_for_name(name),
            Some(SemanticValue::Address(_))
        ) {
            return false;
        }
        matches!(
            self.render_semantic_value_by_name(name, 0, &mut HashSet::new()),
            Some(CExpr::Var(_))
        )
    }

    fn ptr_arith_expr(
        &self,
        base: &SSAVar,
        index: &SSAVar,
        element_size: u32,
        is_sub: bool,
    ) -> CExpr {
        let base_expr = self.get_expr(base);
        let index_expr = self.get_expr(index);
        let scaled = if element_size <= 1 {
            index_expr
        } else {
            CExpr::binary(
                BinaryOp::Mul,
                index_expr,
                CExpr::IntLit(element_size as i64),
            )
        };
        let op = if is_sub { BinaryOp::Sub } else { BinaryOp::Add };
        CExpr::binary(op, base_expr, scaled)
    }

    fn ptr_subscript_expr(
        &self,
        base: &SSAVar,
        index: &SSAVar,
        element_size: u32,
        is_sub: bool,
    ) -> Option<CExpr> {
        let elem_ty = if let Some(oracle) = self.type_oracle {
            let base_ty = oracle.type_of(base);
            if oracle.is_array(base_ty) || oracle.is_pointer(base_ty) {
                uint_type_from_size(element_size)
            } else {
                type_from_size(element_size)
            }
        } else {
            uint_type_from_size(element_size)
        };
        let base_expr =
            self.normalize_pointer_base_expr(&self.expr_for_ssa_name(&base.display_name()), 0);
        let index_expr =
            self.normalize_index_expr(&self.expr_for_ssa_name(&index.display_name()), 0)?;
        self.build_subscript_expr(base_expr, index_expr, elem_ty, is_sub)
    }

    fn typed_deref_expr(&self, addr: &SSAVar, elem_size: u32) -> CExpr {
        let addr_expr = self.get_expr(addr);
        let addr_ty = self.type_oracle.map(|oracle| oracle.type_of(addr));
        let is_pointer_typed = if let (Some(oracle), Some(ty)) = (self.type_oracle, addr_ty) {
            oracle.is_pointer(ty) || oracle.is_array(ty)
        } else {
            false
        };

        let casted = if is_pointer_typed || self.looks_like_pointer_expr(&addr_expr) {
            addr_expr
        } else {
            let elem_ty = uint_type_from_size(elem_size);
            CExpr::cast(CType::ptr(elem_ty), addr_expr)
        };
        CExpr::Deref(Box::new(casted))
    }

    fn looks_like_pointer_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Cast { ty, .. } => matches!(ty, CType::Pointer(_)),
            CExpr::Deref(_)
            | CExpr::Subscript { .. }
            | CExpr::Member { .. }
            | CExpr::PtrMember { .. } => true,
            CExpr::Var(name) => {
                let lower = self.spelling(*name).to_ascii_lowercase();
                lower.starts_with("arg")
                    || lower.contains("ptr")
                    || lower.contains("addr")
                    || self
                        .lookup_type_hint(&self.spelling(*name))
                        .map(|ty| matches!(ty, CType::Pointer(_) | CType::Struct(_)))
                        .unwrap_or(false)
            }
            CExpr::Paren(inner) => self.looks_like_pointer_expr(inner),
            _ => false,
        }
    }

    fn try_subscript_from_var(&self, addr: &SSAVar, elem_size: u32) -> Option<CExpr> {
        if let Some(expr) = self.definition_for_var(addr)
            && let Some(sub) = self.try_subscript_from_addr_expr(expr, elem_size)
        {
            return Some(sub);
        }
        let resolved = self.expr_for_ssa_name(&addr.display_name());
        if let Some(sub) = self.try_subscript_from_addr_expr(&resolved, elem_size) {
            return Some(sub);
        }
        if let Some(ptr) = self.ptr_arith_for_var(addr) {
            return self.ptr_subscript_expr(&ptr.base, &ptr.index, ptr.element_size, ptr.is_sub);
        }
        None
    }

    fn try_member_access_from_var(&self, addr: &SSAVar) -> Option<CExpr> {
        if let Some(expr) = self.definition_for_var(addr)
            && let Some(member) = self.try_member_access_from_addr_expr(Some(addr), expr)
        {
            return Some(member);
        }
        let resolved = self.expr_for_ssa_name(&addr.display_name());
        if let Some(member) = self.try_member_access_from_addr_expr(Some(addr), &resolved) {
            return Some(member);
        }
        None
    }

    fn try_subscript_from_addr_expr(&self, expr: &CExpr, elem_size: u32) -> Option<CExpr> {
        let (base_expr, index_expr, _scale, is_sub) = self.extract_base_index_scale(expr)?;
        let elem_ty = uint_type_from_size(elem_size);
        let base_expr = self.normalize_pointer_base_expr(&base_expr, 0);
        let index_expr = self.normalize_index_expr(&index_expr, 0)?;
        self.build_subscript_expr(base_expr, index_expr, elem_ty, is_sub)
    }

    fn try_member_access_from_addr_expr(
        &self,
        addr: Option<&SSAVar>,
        expr: &CExpr,
    ) -> Option<CExpr> {
        let (base_expr_raw, offset) = self
            .extract_base_const_offset(expr)
            .or_else(|| Some((expr.clone(), 0)))?;
        let base_expr = self.stable_member_base_expr(&base_expr_raw, 0)?;
        let member = self.oracle_member_name(addr, &base_expr, offset)?;
        self.is_semantic_member_base(&base_expr)
            .then(|| self.member_access_expr(base_expr, member))
    }

    fn extract_base_index_scale(&self, expr: &CExpr) -> Option<(CExpr, CExpr, u32, bool)> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => self.extract_base_index_from_add(left, right),
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => self
                .extract_base_index_from_add(left, right)
                .map(|(base, index, scale, is_sub)| (base, index, scale, !is_sub)),
            CExpr::Cast { expr: inner, .. } | CExpr::Paren(inner) => {
                self.extract_base_index_scale(inner)
            }
            CExpr::Var(name) => self
                .definitions
                .get(&*self.spelling(*name))
                .and_then(|inner| self.extract_base_index_scale(inner))
                .or_else(|| {
                    let resolved = self.expr_for_ssa_name(&self.spelling(*name));
                    (resolved != expr.clone())
                        .then(|| self.extract_base_index_scale(&resolved))
                        .flatten()
                }),
            _ => None,
        }
    }

    fn extract_base_const_offset(&self, expr: &CExpr) -> Option<(CExpr, i64)> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } => {
                if let Some(off) = self.literal_to_i64(right) {
                    return Some((left.as_ref().clone(), off));
                }
                if let Some(off) = self.literal_to_i64(left) {
                    return Some((right.as_ref().clone(), off));
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => self
                .literal_to_i64(right)
                .map(|off| (left.as_ref().clone(), -off)),
            CExpr::Cast { expr: inner, .. } | CExpr::Paren(inner) => {
                self.extract_base_const_offset(inner)
            }
            CExpr::Var(name) => self
                .definitions
                .get(&*self.spelling(*name))
                .and_then(|def| self.extract_base_const_offset(def))
                .or_else(|| {
                    let resolved = self.expr_for_ssa_name(&self.spelling(*name));
                    (resolved != expr.clone())
                        .then(|| self.extract_base_const_offset(&resolved))
                        .flatten()
                }),
            _ => None,
        }
    }

    fn extract_base_index_from_add(
        &self,
        left: &CExpr,
        right: &CExpr,
    ) -> Option<(CExpr, CExpr, u32, bool)> {
        if let Some((index, scale)) = self.extract_mul_const(right, 0) {
            let elem_size = self.scale_to_elem_size(scale)?;
            return Some((left.clone(), index, elem_size, scale < 0));
        }
        if let Some((index, scale)) = self.extract_mul_const(left, 0) {
            let elem_size = self.scale_to_elem_size(scale)?;
            return Some((right.clone(), index, elem_size, scale < 0));
        }
        None
    }

    fn scale_to_elem_size(&self, scale: i64) -> Option<u32> {
        let abs = scale.checked_abs()? as u64;
        if abs == 0 {
            return None;
        }
        u32::try_from(abs).ok()
    }

    fn extract_mul_const(&self, expr: &CExpr, depth: u32) -> Option<(CExpr, i64)> {
        if depth > 8 {
            return None;
        }

        match expr {
            CExpr::Binary {
                op: BinaryOp::Mul,
                left,
                right,
            } => {
                if let Some(scale) = self.literal_to_i64(right) {
                    let index = left.as_ref().clone();
                    if self.is_semantic_index_expr(&index) {
                        return Some((index, scale));
                    }
                    return None;
                }
                if let Some(scale) = self.literal_to_i64(left) {
                    let index = right.as_ref().clone();
                    if self.is_semantic_index_expr(&index) {
                        return Some((index, scale));
                    }
                    return None;
                }
                None
            }
            CExpr::Binary {
                op: BinaryOp::Shl,
                left,
                right,
            } => {
                let shift = self.literal_to_i64(right)?;
                if !(0..=62).contains(&shift) {
                    return None;
                }
                let scale = 1_i64.checked_shl(shift as u32)?;
                self.extract_mul_const(left, depth + 1)
                    .and_then(|(inner, inner_scale)| {
                        inner_scale
                            .checked_mul(scale)
                            .map(|combined| (inner, combined))
                    })
                    .or_else(|| {
                        let index = left.as_ref().clone();
                        self.is_semantic_index_expr(&index)
                            .then_some((index, scale))
                    })
            }
            CExpr::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                left,
                right,
            } => {
                let (left_expr, left_scale) = self.extract_mul_const(left, depth + 1)?;
                let (right_expr, right_scale) = self.extract_mul_const(right, depth + 1)?;
                let left_norm = self.normalize_index_expr(&left_expr, 0)?;
                let right_norm = self.normalize_index_expr(&right_expr, 0)?;
                if left_norm != right_norm {
                    return None;
                }
                let combined = match expr {
                    CExpr::Binary {
                        op: BinaryOp::Add, ..
                    } => left_scale.checked_add(right_scale)?,
                    CExpr::Binary {
                        op: BinaryOp::Sub, ..
                    } => left_scale.checked_sub(right_scale)?,
                    _ => unreachable!(),
                };
                (combined != 0).then_some((left_norm, combined))
            }
            CExpr::Unary {
                op: UnaryOp::Neg,
                operand,
            } => self
                .extract_mul_const(operand, depth + 1)
                .map(|(expr, scale)| (expr, -scale))
                .or_else(|| Some((operand.as_ref().clone(), -1))),
            CExpr::Cast { expr: inner, .. } | CExpr::Paren(inner) => {
                self.extract_mul_const(inner, depth + 1)
            }
            CExpr::Var(name) => {
                let lower = self.spelling(*name).to_ascii_lowercase();
                let semantic_visible_name = !is_low_signal_ssa_storage_name(&self.spelling(*name))
                    && !lower.starts_with("local_")
                    && !lower.starts_with('t')
                    && !lower.starts_with('v');
                if semantic_visible_name
                    && !self.is_non_index_pointer_expr(expr)
                    && self.is_semantic_index_expr(expr)
                {
                    return Some((expr.clone(), 1));
                }
                if let Some(inner) = self.definition_for_symbol(*name) {
                    self.extract_mul_const(inner, depth + 1)
                } else if !self.is_non_index_pointer_expr(expr) && self.is_semantic_index_expr(expr)
                {
                    Some((expr.clone(), 1))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn literal_to_i64(&self, expr: &CExpr) -> Option<i64> {
        match expr {
            CExpr::IntLit(v) => Some(*v),
            CExpr::UIntLit(v) => i64::try_from(*v).ok(),
            _ => None,
        }
    }

    fn is_semantic_index_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => self
                .definitions
                .get(&*self.spelling(*name))
                .map(|inner| self.is_semantic_index_expr(inner))
                .unwrap_or_else(|| {
                    let lower = self.spelling(*name).to_ascii_lowercase();
                    let stack_placeholder =
                        lower == "stack" || lower == "saved_fp" || lower.starts_with("stack_");
                    !is_constant_or_memory_name(&self.spelling(*name))
                        && (!stack_placeholder
                            && (!self.stack_slot_name_map().contains_key(&*self.spelling(*name))
                                || lower.starts_with("local_")
                                || lower.starts_with("arg")))
                }),
            CExpr::Unary { operand, .. } => self.is_semantic_index_expr(operand),
            CExpr::Binary { left, right, .. } => {
                self.is_semantic_index_expr(left) || self.is_semantic_index_expr(right)
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_semantic_index_expr(inner)
            }
            _ => false,
        }
    }

    fn build_subscript_expr(
        &self,
        base_expr: CExpr,
        index_expr: CExpr,
        elem_ty: CType,
        is_sub: bool,
    ) -> Option<CExpr> {
        if !self.looks_like_pointer_expr(&base_expr)
            || self.is_non_index_pointer_expr(&index_expr)
            || !self.is_semantic_index_expr(&index_expr)
            || base_expr == index_expr
        {
            return None;
        }

        let base_cast = CExpr::cast(CType::ptr(elem_ty), base_expr);
        let index_final = if is_sub {
            CExpr::unary(UnaryOp::Neg, index_expr)
        } else {
            index_expr
        };

        Some(CExpr::Subscript {
            base: Box::new(base_cast),
            index: Box::new(index_final),
        })
    }

    fn normalize_pointer_base_expr(&self, expr: &CExpr, depth: u32) -> CExpr {
        if depth > 4 {
            return expr.clone();
        }

        match expr {
            CExpr::Var(name) => {
                if let Some(inner) = self.definition_for_symbol(*name) {
                    return self.normalize_pointer_base_expr(inner, depth + 1);
                }
                let resolved = self.expr_for_ssa_name(&self.spelling(*name));
                if resolved != expr.clone() && self.looks_like_pointer_expr(&resolved) {
                    return self.normalize_pointer_base_expr(&resolved, depth + 1);
                }
                expr.clone()
            }
            CExpr::Paren(inner) => {
                CExpr::Paren(Box::new(self.normalize_pointer_base_expr(inner, depth + 1)))
            }
            CExpr::Cast { ty, expr: inner } => CExpr::Cast {
                ty: ty.clone(),
                expr: Box::new(self.normalize_pointer_base_expr(inner, depth + 1)),
            },
            _ => expr.clone(),
        }
    }

    fn normalize_index_expr(&self, expr: &CExpr, depth: u32) -> Option<CExpr> {
        if depth > 4 {
            return self.is_semantic_index_expr(expr).then_some(expr.clone());
        }

        match expr {
            CExpr::Var(name) => {
                let lower = self.spelling(*name).to_ascii_lowercase();
                let semantic_visible_name = !is_low_signal_ssa_storage_name(&self.spelling(*name))
                    && !lower.starts_with("local_")
                    && !lower.starts_with('t')
                    && !lower.starts_with('v');
                if semantic_visible_name
                    && !self.is_non_index_pointer_expr(expr)
                    && self.is_semantic_index_expr(expr)
                {
                    return Some(expr.clone());
                }
                if let Some(inner) = self.definition_for_symbol(*name)
                    && let Some(normalized) = self.normalize_index_expr(inner, depth + 1)
                    && !self.is_non_index_pointer_expr(&normalized)
                {
                    return Some(normalized);
                }
                let resolved = self.expr_for_ssa_name(&self.spelling(*name));
                if resolved != expr.clone()
                    && let Some(normalized) = self.normalize_index_expr(&resolved, depth + 1)
                    && !self.is_non_index_pointer_expr(&normalized)
                {
                    return Some(normalized);
                }
                if self.definition_for_symbol(*name).is_some() {
                    return None;
                }
                if self.is_non_index_pointer_expr(expr) {
                    None
                } else {
                    self.is_semantic_index_expr(expr).then_some(expr.clone())
                }
            }
            CExpr::Paren(inner) => self
                .normalize_index_expr(inner, depth + 1)
                .map(|normalized| CExpr::Paren(Box::new(normalized))),
            CExpr::Cast { ty, expr: inner } => self
                .normalize_index_expr(inner, depth + 1)
                .map(|normalized| CExpr::cast(ty.clone(), normalized)),
            CExpr::Unary { op, operand } => self
                .normalize_index_expr(operand, depth + 1)
                .map(|normalized| CExpr::unary(*op, normalized)),
            _ => self.is_semantic_index_expr(expr).then_some(expr.clone()),
        }
    }

    fn is_non_index_pointer_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Cast { ty, .. } => matches!(ty, CType::Pointer(_)),
            CExpr::Deref(_) | CExpr::Subscript { .. } | CExpr::PtrMember { .. } => true,
            CExpr::Var(name) => {
                let lower = self.spelling(*name).to_ascii_lowercase();
                lower.contains("ptr")
                    || lower.contains("addr")
                    || self.stack_slot_name_map().contains_key(&*self.spelling(*name))
                    || self
                        .lookup_type_hint(&self.spelling(*name))
                        .map(|ty| matches!(ty, CType::Pointer(_) | CType::Struct(_)))
                        .unwrap_or(false)
            }
            CExpr::Paren(inner) => self.is_non_index_pointer_expr(inner),
            CExpr::Unary { operand, .. } => self.is_non_index_pointer_expr(operand),
            _ => false,
        }
    }

    fn is_semantic_member_base(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                let lower = self.spelling(*name).to_ascii_lowercase();
                !is_temporary_name(&self.spelling(*name))
                    && !lower.starts_with('r')
                    && !lower.starts_with('e')
                    && !matches!(lower.as_str(), "stack" | "saved_fp")
            }
            CExpr::Subscript { .. } | CExpr::Member { .. } => true,
            CExpr::Cast { expr, .. } | CExpr::Paren(expr) => self.is_semantic_member_base(expr),
            _ => self.looks_like_pointer_expr(expr),
        }
    }

    fn stable_member_base_expr(&self, expr: &CExpr, depth: u32) -> Option<CExpr> {
        if depth > 1 {
            return None;
        }

        let base_expr = self.normalize_pointer_base_expr(expr, 0);
        if self.is_semantic_member_base(&base_expr) {
            return Some(base_expr);
        }

        if let CExpr::Var(name) = expr
            && let Some(candidate) = self.definition_for_symbol(*name)
        {
            let normalized = self.normalize_pointer_base_expr(candidate, 0);
            if self.is_semantic_member_base(&normalized) {
                return Some(normalized);
            }
        }

        None
    }

    fn oracle_member_name(
        &self,
        addr: Option<&SSAVar>,
        _base_expr: &CExpr,
        offset: i64,
    ) -> Option<String> {
        if offset < 0 {
            return None;
        }
        let oracle = self.type_oracle?;
        let offset = offset as u64;

        if let Some(addr) = addr
            && offset == 0
            && let Some(name) = oracle.field_name(oracle.type_of(addr), offset)
        {
            return Some(name.to_string());
        }

        None
    }

    fn member_access_expr(&self, base_expr: CExpr, member: String) -> CExpr {
        match base_expr {
            CExpr::Subscript { .. } | CExpr::Member { .. } => CExpr::Member {
                base: Box::new(base_expr),
                member,
            },
            _ => CExpr::PtrMember {
                base: Box::new(base_expr),
                member,
            },
        }
    }
}

fn type_from_size(size: u32) -> CType {
    match size {
        0 => CType::Unknown,
        1 => CType::Int(8),
        2 => CType::Int(16),
        4 => CType::Int(32),
        8 => CType::Int(64),
        _ => CType::Int(size.saturating_mul(8)),
    }
}

fn uint_type_from_size(size: u32) -> CType {
    match size {
        0 => CType::Unknown,
        1 => CType::UInt(8),
        2 => CType::UInt(16),
        4 => CType::UInt(32),
        8 => CType::UInt(64),
        _ => CType::UInt(size.saturating_mul(8)),
    }
}

fn is_low_signal_lowering_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    let is_temp_family = |prefix: char| {
        lower
            .strip_prefix(prefix)
            .and_then(|rest| {
                let (head, tail) = rest.split_once('_').unwrap_or((rest, ""));
                head.chars()
                    .all(|ch| ch.is_ascii_hexdigit())
                    .then_some(tail)
            })
            .is_some_and(|tail| tail.is_empty() || tail.chars().all(|ch| ch.is_ascii_digit()))
    };
    is_low_signal_ssa_storage_name(name)
        || lower.starts_with("tmp")
        || is_temp_family('t')
        || is_temp_family('v')
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    #[allow(clippy::too_many_arguments)]
    fn make_ctx<'a>(
        symbols: &'a std::cell::RefCell<crate::symbol::SymbolTable>,
        definitions: &'a HashMap<String, CExpr>,
        use_counts: &'a HashMap<String, usize>,
        condition_vars: &'a HashSet<String>,
        pinned: &'a HashSet<String>,
        var_aliases: &'a HashMap<String, String>,
        ptr_arith: &'a HashMap<String, PtrArith>,
        stack_slots: &'a HashMap<String, StackSlotProvenance>,
        forwarded_values: &'a HashMap<String, ValueProvenance>,
        #[cfg(test)] _function_names: &'a HashMap<u64, String>,
        #[cfg(test)] _strings: &'a HashMap<u64, String>,
        #[cfg(test)] _symbols: &'a HashMap<u64, String>,
    ) -> LowerCtx<'a> {
        let type_hints = Box::leak(Box::new(HashMap::new()));
        let semantic_values = Box::leak(Box::new(HashMap::new()));
        let param_register_aliases = Box::leak(Box::new(HashMap::new()));
        LowerCtx {
            symbols,
            string_literals: crate::analysis::lower::no_string_literals(),
            use_info: None,
            definitions,
            semantic_values,
            use_counts,
            condition_vars,
            pinned,
            var_aliases,
            param_register_aliases,
            type_hints,
            ptr_arith,
            stack_slots,
            forwarded_values,
            type_oracle: None,
        }
    }

    #[test]
    fn resolve_addr_literal_ignores_raw_function_string_symbol_maps() {
        let symbols = test_table();
        let mut fn_map = HashMap::new();
        let mut str_map = HashMap::new();
        let mut sym_map = HashMap::new();

        fn_map.insert(0x401000, "sym.main".to_string());
        str_map.insert(0x402000, "format: %d\\n".to_string());
        sym_map.insert(0x403000, "obj.global".to_string());
        str_map.insert(0x404000, "string_wins_over_symbol".to_string());
        sym_map.insert(0x404000, "obj.same_addr".to_string());
        fn_map.insert(0x405000, "sym.wins".to_string());
        str_map.insert(0x405000, "string_loses".to_string());
        sym_map.insert(0x405000, "symbol_loses".to_string());
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        for addr in [0x401000, 0x402000, 0x403000, 0x404000, 0x405000] {
            assert_eq!(
                ctx.resolve_addr_literal(addr),
                None,
                "raw function/string/symbol maps must not authorize address literal rendering"
            );
        }
    }

    #[test]
    fn resolve_addr_literal_skips_small_and_unknown_values() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(ctx.resolve_addr_literal(0xff), None);
        assert_eq!(ctx.resolve_addr_literal(0x5000), None);
    }

    #[test]
    fn callother_ids_share_explicit_lowering() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        for userop in [7, 0x7fff_ffff, 0x8000_0000, u32::MAX] {
            let expr = ctx.op_to_expr(&SSAOp::CallOther {
                output: Some(SSAVar::new("X30", 1, 8)),
                userop,
                inputs: vec![SSAVar::new("X30", 0, 8), SSAVar::new("SP", 0, 8)],
            });

            assert_eq!(
                expr,
                CExpr::call(
                    CExpr::External {
                    name: "callother".to_string(),
                    kind: crate::symbol::ExternalKind::Intrinsic,
                },
                    vec![
                        CExpr::StringLit(format!("userop_{userop}")),
                        crate::symbol::var_ref(&symbols, "x30"),
                        crate::symbol::var_ref(&symbols, "sp"),
                    ],
                ),
                "numeric userop must remain an explicit CallOther"
            );
        }
    }

    #[test]
    fn op_to_expr_preserves_select_value_semantics() {
        let symbols = test_table();
        let function_names = HashMap::new();
        let strings = HashMap::new();
        let binary_symbols = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &function_names,
            &strings,
            &binary_symbols,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Select {
                dst: SSAVar::new("tmp:result", 1, 4),
                cond: SSAVar::new("cond", 0, 1),
                if_true: SSAVar::new("when_true", 0, 4),
                if_false: SSAVar::new("when_false", 0, 4),
            }),
            CExpr::Ternary {
                cond: Box::new(crate::symbol::var_ref(&symbols, "cond")),
                then_expr: Box::new(crate::symbol::var_ref(&symbols, "when_true")),
                else_expr: Box::new(crate::symbol::var_ref(&symbols, "when_false")),
            }
        );
    }

    #[test]
    fn get_expr_keeps_ram_addresses_numeric_without_typed_string_fact() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let mut str_map = HashMap::new();
        let sym_map = HashMap::new();
        str_map.insert(0x403048, "Usage: %s <test_num> [args...]\\n".to_string());
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let var = SSAVar::new("ram:403048", 0, 8);
        assert_eq!(ctx.get_expr(&var), crate::symbol::var_ref(&symbols, "ram:403048"));
    }

    #[test]
    fn load_generic_deref_casts_non_pointer_like_address() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:5001", 1, 4),
            space: r2il::SpaceId::Ram,
            addr: SSAVar::new("tmp:5000", 1, 8),
        });
        let CExpr::Deref(inner) = expr else {
            panic!("expected dereference expression");
        };
        assert!(
            matches!(
                inner.as_ref(),
                CExpr::Cast {
                    ty: CType::Pointer(_),
                    ..
                }
            ),
            "generic lower path should cast non-pointer-like address expressions"
        );
    }

    #[test]
    fn custom_space_load_never_becomes_an_ordinary_c_dereference() {
        let symbols = test_table();
        let function_names = HashMap::new();
        let strings = HashMap::new();
        let binary_symbols = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &function_names,
            &strings,
            &binary_symbols,
        );
        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:custom_result", 1, 4),
            space: r2il::SpaceId::Custom(7),
            addr: SSAVar::new("tmp:custom_addr", 1, 8),
        });

        assert!(
            matches!(
                expr,
                CExpr::Call { ref func, ref args, .. }
                    if **func == crate::symbol::var_ref(&symbols, "r2s_unsupported_space_load")
                        && args.first() == Some(&CExpr::StringLit("space7".to_string()))
            ),
            "custom-space memory must stay explicit and unsupported: {expr:?}"
        );
    }

    #[test]
    fn semantic_load_rendering_preserves_exact_memory_space() {
        let symbols = test_table();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let function_names = HashMap::new();
        let strings = HashMap::new();
        let binary_symbols = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &function_names,
            &strings,
            &binary_symbols,
        );
        let addr = NormalizedAddr {
            base: BaseRef::Value(ValueRef::from(SSAVar::new("tmp:addr", 1, 8))),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        };
        let ram = ctx
            .expr_for_semantic_value(&SemanticValue::Load {
                space: r2il::SpaceId::Ram,
                addr: addr.clone(),
                size: 4,
            })
            .expect("RAM semantic load");
        let custom = ctx
            .expr_for_semantic_value(&SemanticValue::Load {
                space: r2il::SpaceId::Custom(7),
                addr,
                size: 4,
            })
            .expect("Custom semantic load refusal");

        assert!(matches!(ram, CExpr::Deref(_)));
        assert!(matches!(
            custom,
            CExpr::Call { ref func, ref args, .. }
                if **func == crate::symbol::var_ref(&symbols, "r2s_unsupported_space_load")
                    && args.first() == Some(&CExpr::StringLit("space7".to_string()))
        ));
    }

    #[test]
    fn load_generic_deref_avoids_cast_for_pointer_like_address() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:5101", 1, 4),
            space: r2il::SpaceId::Ram,
            addr: SSAVar::new("arg1", 0, 8),
        });
        let CExpr::Deref(inner) = expr else {
            panic!("expected dereference expression");
        };
        assert!(
            !matches!(
                inner.as_ref(),
                CExpr::Cast {
                    ty: CType::Pointer(_),
                    ..
                }
            ),
            "pointer-like address expressions should not be re-cast"
        );
    }

    #[test]
    fn load_preserves_negative_index_subscript_shape() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let definitions = HashMap::from([(
            "tmp:addr_1".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                crate::symbol::var_ref(&symbols, "arg1"),
                CExpr::binary(
                    BinaryOp::Mul,
                    CExpr::Cast {
                        ty: CType::Int(64),
                        expr: Box::new(CExpr::unary(UnaryOp::Neg, crate::symbol::var_ref(&symbols, "arg2"))),
                    },
                    CExpr::IntLit(4),
                ),
            ),
        )]);
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:5002", 1, 4),
            space: r2il::SpaceId::Ram,
            addr: SSAVar::new("tmp:addr", 1, 8),
        });

        let CExpr::Subscript { base, index } = expr else {
            panic!("expected subscript expression");
        };
        assert!(matches!(base.as_ref(), CExpr::Cast { .. }));
        assert!(
            matches!(
                index.as_ref(),
                CExpr::Cast { expr, .. }
                    if matches!(expr.as_ref(), CExpr::Unary { op: UnaryOp::Neg, .. })
            ),
            "negative index shape should survive lowering"
        );
    }

    #[test]
    fn load_does_not_fabricate_stack_slot_aliases() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::from([(
            "tmp:stackaddr_1".to_string(),
            StackSlotProvenance::new(-0x18),
        )]);
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:5003", 1, 4),
            space: r2il::SpaceId::Ram,
            addr: SSAVar::new("tmp:stackaddr", 1, 8),
        });

        let CExpr::Deref(inner) = expr else {
            panic!("expected conservative dereference expression");
        };
        assert!(
            !matches!(inner.as_ref(), CExpr::Var(name) if ctx.spelling(*name).starts_with("local_") || &*crate::symbol::spelling(&symbols, *name) == "stack"),
            "analysis lowering should not fabricate visible stack aliases"
        );
    }

    #[test]
    fn load_base_plus_const_does_not_become_fake_subscript() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let definitions = HashMap::from([(
            "tmp:addr_1".to_string(),
            CExpr::binary(
                BinaryOp::Add,
                crate::symbol::var_ref(&symbols, "arg1"),
                CExpr::IntLit(8),
            ),
        )]);
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:5004", 1, 4),
            space: r2il::SpaceId::Ram,
            addr: SSAVar::new("tmp:addr", 1, 8),
        });

        assert!(
            !matches!(expr, CExpr::Subscript { .. }),
            "base + const should stay as pointer arithmetic/deref, not fake subscript"
        );
    }

    #[test]
    fn load_alias_expanded_const_index_does_not_become_fake_subscript() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let definitions = HashMap::from([
            ("tmp:index_1".to_string(), CExpr::IntLit(0)),
            (
                "tmp:addr_1".to_string(),
                CExpr::binary(
                    BinaryOp::Add,
                    crate::symbol::var_ref(&symbols, "arg1"),
                    CExpr::binary(
                        BinaryOp::Mul,
                        crate::symbol::var_ref(&symbols, "tmp:index_1"),
                        CExpr::IntLit(4),
                    ),
                ),
            ),
        ]);
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:5005", 1, 4),
            space: r2il::SpaceId::Ram,
            addr: SSAVar::new("tmp:addr", 1, 8),
        });

        assert!(
            !matches!(expr, CExpr::Subscript { .. }),
            "constant-resolved index carriers must not become fake array subscripts"
        );
    }

    #[test]
    fn load_unstable_alias_expanded_base_does_not_become_member_access() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let ptr_arith = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let definitions = HashMap::from([
            ("tmp:base_1".to_string(), crate::symbol::var_ref(&symbols, "rdx_1")),
            (
                "tmp:addr_1".to_string(),
                CExpr::binary(
                    BinaryOp::Add,
                    crate::symbol::var_ref(&symbols, "tmp:base_1"),
                    CExpr::IntLit(8),
                ),
            ),
        ]);
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:5006", 1, 4),
            space: r2il::SpaceId::Ram,
            addr: SSAVar::new("tmp:addr", 1, 8),
        });

        assert!(
            !matches!(expr, CExpr::PtrMember { .. }),
            "unstable alias-expanded bases must not become pointer member syntax"
        );
    }

    #[test]
    fn ptr_arith_prefers_expression_recovered_real_index_over_pointer_local() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let var_aliases = HashMap::new();
        let stack_slots = HashMap::new();
        let forwarded_values = HashMap::new();
        let addr = SSAVar::new("tmp:addr", 1, 8);
        let arr = SSAVar::new("arg1", 0, 8);
        let ptr_local = SSAVar::new("tmp:arr_local", 1, 8);
        let ptr_arith = HashMap::from([(
            addr.display_name(),
            PtrArith {
                base: arr.clone(),
                index: ptr_local,
                element_size: 4,
                is_sub: false,
            },
        )]);
        let definitions = HashMap::from([
            (
                "tmp:arr_local_1".to_string(),
                crate::symbol::var_ref(&symbols, "local_8"),
            ),
            ("local_8".to_string(), crate::symbol::var_ref(&symbols, "arg1")),
            ("local_c".to_string(), crate::symbol::var_ref(&symbols, "arg2")),
            (
                addr.display_name(),
                CExpr::binary(
                    BinaryOp::Add,
                    crate::symbol::var_ref(&symbols, "local_8"),
                    CExpr::binary(
                        BinaryOp::Mul,
                        crate::symbol::var_ref(&symbols, "local_c"),
                        CExpr::IntLit(4),
                    ),
                ),
            ),
        ]);
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &var_aliases,
            &ptr_arith,
            &stack_slots,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let expr = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:5007", 1, 4),
            space: r2il::SpaceId::Ram,
            addr,
        });

        let CExpr::Subscript { base, index } = expr else {
            panic!("expected subscript expression");
        };
        assert!(
            matches!(base.as_ref(), CExpr::Cast { expr, .. } if matches!(expr.as_ref(), CExpr::Var(name) if &*crate::symbol::spelling(&symbols, *name) == "arg1")),
            "subscript base should normalize back to the semantic pointer source"
        );
        assert!(
            matches!(index.as_ref(), CExpr::Var(name) if &*crate::symbol::spelling(&symbols, *name) == "arg2"),
            "subscript index should use the semantic index source, not the pointer local alias: {index:?}"
        );
    }
}

impl crate::naming::NameSource for LowerCtx<'_> {
    fn carrier_alias(&self, _display: &str) -> Option<String> {
        None
    }

    fn var_alias(&self, display: &str) -> Option<String> {
        self.var_alias_for_name(display).cloned()
    }

    fn param_alias(&self, register: &str) -> Option<String> {
        self.param_register_aliases
            .get(&register.to_ascii_lowercase())
            .cloned()
    }
}
