#[cfg(test)]
use std::collections::HashMap;
use std::collections::HashSet;

use r2ssa::{SSAOp, SSAVar, ValueId};
use r2types::TypeOracle;

#[cfg(test)]
use super::utils::parse_const_value;
use super::{
    BaseRef, NormalizedAddr, PtrArith, ScalarValue, SemanticValue, UseInfo, ValueProvenance,
    ValueRef,
};
use crate::ast::{BinaryOp, CExpr, CType, UnaryOp};
use crate::binding_plan::PlannedValueSymbol;

/// Proof that a refusal was decided through a constructor.
///
/// The field is private to this module, so no other module can name it and no
/// other module can build a refusal without going through the constructors
/// below. That is the whole point: instrumenting construction sites by hand
/// left holes, twice, and a refusal that escaped the instrumentation cost a
/// full pass to find each time. Now the compiler enumerates them.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct RefusalOrigin(());

impl std::fmt::Debug for RefusalOrigin {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

/// Defensive renderer result for operations whose canonical disposition is
/// owned by `r2ssa::MachineProjection`.
///
/// This is not a second support classifier: production must already have
/// received `MachineBuildError::UnsupportedOperation` from the projection.
/// The renderer result exists only so legacy helpers cannot turn an opaque
/// operation into executable C when called directly.
///
/// Every variant carries a witness that only this module can make, so a
/// refusal cannot be built without the constructor that records where it was
/// decided. `R2DEC_TRACE_REFUSAL` prints that.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum OpLoweringRefusal {
    MissingMachineProjectionAuthorization(RefusalOrigin),
    MissingProgramVariableAuthorization(RefusalOrigin),
    UnrepresentableOperation(RefusalOrigin),
}

impl std::fmt::Debug for OpLoweringRefusal {
    /// Named as it always was. The witness the variants carry is a
    /// construction guard, not information, and it reaches rendered residual
    /// comments through this.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::MissingMachineProjectionAuthorization(_) => {
                "MissingMachineProjectionAuthorization"
            }
            Self::MissingProgramVariableAuthorization(_) => "MissingProgramVariableAuthorization",
            Self::UnrepresentableOperation(_) => "UnrepresentableOperation",
        })
    }
}

impl OpLoweringRefusal {
    #[track_caller]
    fn note(name: &str) -> RefusalOrigin {
        if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
            eprintln!(
                "refusal {name} decided at {}",
                std::panic::Location::caller()
            );
        }
        RefusalOrigin(())
    }

    #[track_caller]
    pub(crate) fn missing_machine_projection() -> Self {
        Self::MissingMachineProjectionAuthorization(Self::note("machine-projection"))
    }

    #[track_caller]
    pub(crate) fn missing_program_variable() -> Self {
        Self::MissingProgramVariableAuthorization(Self::note("program-variable"))
    }

    #[track_caller]
    pub(crate) fn unrepresentable_operation() -> Self {
        Self::UnrepresentableOperation(Self::note("unrepresentable-operation"))
    }
}

pub(crate) fn no_string_literals() -> &'static std::collections::BTreeMap<u64, String> {
    static EMPTY: std::sync::OnceLock<std::collections::BTreeMap<u64, String>> =
        std::sync::OnceLock::new();
    EMPTY.get_or_init(std::collections::BTreeMap::new)
}

pub(crate) struct LowerCtx<'a> {
    /// The sole binding-name projection for this rendering. Value identity is
    /// still resolved through `UseInfo`; no parallel ValueId table lives here.
    pub(crate) binding_names: Option<&'a crate::binding_plan::BindingNameResolution>,
    pub(crate) use_info: Option<&'a UseInfo>,
    pub(crate) pinned: &'a HashSet<String>,
    pub(crate) type_oracle: Option<&'a dyn TypeOracle>,
    /// The table that owns plan-minted presentation handles. Production only
    /// reads an already-sealed handle; fixture adapters may mint test symbols.
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

    fn definition_for_var(&self, var: &SSAVar) -> Option<&CExpr> {
        self.use_info.and_then(|info| info.definition_for_var(var))
    }

    fn semantic_value_for_var(&self, var: &SSAVar) -> Option<&SemanticValue> {
        self.use_info
            .and_then(|info| info.semantic_value_for_var(var))
    }

    fn forwarded_value_for_var(&self, var: &SSAVar) -> Option<&ValueProvenance> {
        self.use_info
            .and_then(|info| info.forwarded_value_for_var(var))
    }

    fn ptr_arith_for_var(&self, var: &SSAVar) -> Option<&PtrArith> {
        // One store answers for pointer arithmetic, keyed by identity. This used
        // to consult a name-keyed copy first and fall back to the real one,
        // which meant the answer depended on which of the two the caller had
        // been handed.
        self.use_info.and_then(|info| info.ptr_arith_for_var(var))
    }

    fn use_count_for_value(&self, value: ValueId) -> usize {
        self.use_info
            .map(|info| info.use_count_for_value(value))
            .unwrap_or(0)
    }

    fn is_condition_value(&self, value: ValueId) -> bool {
        self.use_info
            .is_some_and(|info| info.is_condition_value(value))
    }

    fn exact_value_id(&self, var: &SSAVar) -> Result<ValueId, OpLoweringRefusal> {
        self.use_info
            .and_then(|info| info.exact_value_id_for_var(var))
            .ok_or_else(|| OpLoweringRefusal::missing_program_variable())
    }

    fn bound_program_symbol(
        &self,
        var: &SSAVar,
    ) -> Result<crate::symbol::SymbolId, OpLoweringRefusal> {
        let resolver = self
            .binding_names
            .ok_or_else(|| OpLoweringRefusal::missing_program_variable())?;
        let value = self.exact_value_id(var)?;
        match resolver
            .require_value(value)
            .map_err(|_| OpLoweringRefusal::missing_program_variable())?
        {
            PlannedValueSymbol::Bound(symbol) => Ok(symbol),
            PlannedValueSymbol::Inline(_)
            | PlannedValueSymbol::Elided(_)
            | PlannedValueSymbol::Refused(_)
            | PlannedValueSymbol::Absent => Err(OpLoweringRefusal::missing_program_variable()),
        }
    }

    /// The identifier for a value, from the binding plan and nowhere else.
    ///
    /// This used to fall back, under test only, to a ladder of alias tables
    /// spelling a name from the SSA variable. Release builds already refused
    /// instead, and every one of those tables was empty, so the ladder decided
    /// nothing while still being a second thing that could answer.
    pub(crate) fn var_name(&self, var: &SSAVar) -> Result<String, OpLoweringRefusal> {
        Ok(self.spelling(self.bound_program_symbol(var)?).to_string())
    }

    pub(crate) fn get_expr(&self, var: &SSAVar) -> Result<CExpr, OpLoweringRefusal> {
        self.get_expr_with_depth(var, 0, &mut HashSet::new())
    }

    fn get_expr_with_depth(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut HashSet<ValueId>,
    ) -> Result<CExpr, OpLoweringRefusal> {
        if let Some(value) = var.constant_bits() {
            return Ok(self.constant_to_expr(value));
        }

        #[cfg(test)]
        if var.is_const() {
            return self.fixture_constant_to_expr(var);
        }

        // Without a binding plan there is no name to give, in any build. The
        // string-keyed spelling that used to answer here could not recover a
        // value identity from a rendered name, which is why it was already
        // refused outside tests.
        if self.binding_names.is_none() {
            return Err(OpLoweringRefusal::missing_program_variable());
        }

        let value_id = self.exact_value_id(var)?;
        let key = var.display_name();
        let trace = std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some();
        // A version-zero register is the value the function was entered with, so
        // nothing forwarded it here and provenance cannot speak for it.
        if var.version > 0
            && let Some(prov) = self.forwarded_value_for_var(var)
            && depth < 8
            && visited.insert(value_id)
        {
            if trace {
                eprintln!("RESOLVE key={key} via=forwarded source={}", prov.source);
            }
            if let Some(source_var) = prov.source_var.as_ref() {
                return self.get_expr_with_depth(source_var, depth + 1, visited);
            }
            if let Some(source_var) = prov
                .source_value_id
                .and_then(|value| self.use_info?.var_for_value_id(value))
            {
                return self.get_expr_with_depth(source_var, depth + 1, visited);
            }
        }
        if let Some(expr) = self.render_semantic_value_for_var(var, depth, visited)? {
            if trace {
                eprintln!("RESOLVE key={key} via=semantic");
            }
            return Ok(expr);
        }
        if trace && self.definition_for_var(var).is_some() {
            eprintln!(
                "RESOLVE key={key} via=definition inline={}",
                self.should_inline_value(value_id)
            );
        }
        if depth < 8
            && self.should_inline_value(value_id)
            && visited.insert(value_id)
            && let Some(expr) = self.definition_for_var(var)
        {
            return Ok(expr.clone());
        }

        if std::env::var_os("R2SLEIGH_DEBUG_MERGES").is_some() {
            eprintln!(
                "BARENAME key={key} name={} depth={depth} uses={} inline={} has_def={} visited={}",
                self.var_name(var)?,
                self.use_count_for_value(value_id),
                self.should_inline_value(value_id),
                self.definition_for_var(var).is_some(),
                visited.contains(&value_id)
            );
        }
        Ok(CExpr::Var(self.bound_program_symbol(var)?))
    }

    #[cfg(test)]
    pub(crate) fn expr_for_semantic_value(
        &self,
        value: &SemanticValue,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        self.render_semantic_value(value, 0, &mut HashSet::new())
    }

    pub(crate) fn op_to_expr(&self, op: &SSAOp) -> Result<CExpr, OpLoweringRefusal> {
        self.require_op_value_identities(op)?;
        Ok(match op {
            SSAOp::CallOther { .. } | SSAOp::CpuId { .. } => {
                return Err(OpLoweringRefusal::missing_machine_projection());
            }
            SSAOp::Load { space, .. } if *space != r2il::SpaceId::Ram => {
                return Err(OpLoweringRefusal::missing_machine_projection());
            }
            SSAOp::Copy { src, .. } => self.get_expr(src)?,
            SSAOp::Load { dst, addr, .. } => {
                let prefer_memory_access = matches!(
                    self.semantic_value_for_var(dst),
                    Some(SemanticValue::Address(_))
                );
                if prefer_memory_access {
                    if let Some(sub) = self.try_subscript_from_var(addr, dst.size)? {
                        return Ok(sub);
                    }
                    if let Some(member) = self.try_member_access_from_var(addr)? {
                        return Ok(member);
                    }
                }
                if let Some(expr) =
                    self.render_semantic_value_for_var(dst, 0, &mut HashSet::new())?
                {
                    expr
                } else if let Some(sub) = self.try_subscript_from_var(addr, dst.size)? {
                    sub
                } else if let Some(member) = self.try_member_access_from_var(addr)? {
                    member
                } else {
                    self.typed_deref_expr(addr, dst.size)?
                }
            }
            SSAOp::IntAdd { a, b, .. } => self.binary_expr(BinaryOp::Add, a, b)?,
            SSAOp::IntSub { a, b, .. } => self.binary_expr(BinaryOp::Sub, a, b)?,
            SSAOp::IntMult { a, b, .. } => self.binary_expr(BinaryOp::Mul, a, b)?,
            SSAOp::IntDiv { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Div, a, b, Some(uint_type_from_size(dst.size)))?
            }
            SSAOp::IntSDiv { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Div, a, b, Some(type_from_size(dst.size)))?
            }
            SSAOp::IntRem { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Mod, a, b, Some(uint_type_from_size(dst.size)))?
            }
            SSAOp::IntSRem { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Mod, a, b, Some(type_from_size(dst.size)))?
            }
            SSAOp::IntAnd { a, b, .. } => self.binary_expr(BinaryOp::BitAnd, a, b)?,
            SSAOp::IntOr { a, b, .. } => self.binary_expr(BinaryOp::BitOr, a, b)?,
            SSAOp::IntXor { a, b, .. } => self.binary_expr(BinaryOp::BitXor, a, b)?,
            SSAOp::IntLeft { a, b, .. } => self.binary_expr(BinaryOp::Shl, a, b)?,
            SSAOp::IntRight { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Shr, a, b, Some(uint_type_from_size(dst.size)))?
            }
            SSAOp::IntSRight { dst, a, b } => {
                self.typed_binary_expr(BinaryOp::Shr, a, b, Some(type_from_size(dst.size)))?
            }
            SSAOp::IntLess { a, b, .. } => self.typed_binary_expr(
                BinaryOp::Lt,
                a,
                b,
                Some(uint_type_from_size(a.size.max(b.size))),
            )?,
            SSAOp::IntSLess { a, b, .. } => self.typed_binary_expr(
                BinaryOp::Lt,
                a,
                b,
                Some(type_from_size(a.size.max(b.size))),
            )?,
            SSAOp::IntLessEqual { a, b, .. } => self.typed_binary_expr(
                BinaryOp::Le,
                a,
                b,
                Some(uint_type_from_size(a.size.max(b.size))),
            )?,
            SSAOp::IntSLessEqual { a, b, .. } => self.typed_binary_expr(
                BinaryOp::Le,
                a,
                b,
                Some(type_from_size(a.size.max(b.size))),
            )?,
            SSAOp::IntEqual { a, b, .. } => self.binary_expr(BinaryOp::Eq, a, b)?,
            SSAOp::IntNotEqual { a, b, .. } => self.binary_expr(BinaryOp::Ne, a, b)?,
            SSAOp::IntNegate { src, .. } => CExpr::unary(UnaryOp::Neg, self.get_expr(src)?),
            SSAOp::IntNot { src, .. } => CExpr::unary(UnaryOp::BitNot, self.get_expr(src)?),
            SSAOp::BoolAnd { a, b, .. } => self.binary_expr(BinaryOp::And, a, b)?,
            SSAOp::BoolOr { a, b, .. } => self.binary_expr(BinaryOp::Or, a, b)?,
            SSAOp::BoolXor { a, b, .. } => self.binary_expr(BinaryOp::BitXor, a, b)?,
            SSAOp::BoolNot { src, .. } => CExpr::unary(UnaryOp::Not, self.get_expr(src)?),
            SSAOp::IntZExt { dst, src } | SSAOp::IntSExt { dst, src } => {
                CExpr::cast(type_from_size(dst.size), self.get_expr(src)?)
            }
            SSAOp::Trunc { dst, src } => CExpr::cast(type_from_size(dst.size), self.get_expr(src)?),
            SSAOp::Piece { dst, hi, lo } => {
                let shift_bits = lo.size.saturating_mul(8);
                let dst_ty = uint_type_from_size(dst.size);
                let hi_cast = CExpr::cast(dst_ty.clone(), self.get_expr(hi)?);
                let lo_cast = CExpr::cast(dst_ty.clone(), self.get_expr(lo)?);
                let shifted = if shift_bits == 0 {
                    hi_cast
                } else {
                    CExpr::binary(BinaryOp::Shl, hi_cast, CExpr::IntLit(shift_bits as i64))
                };
                CExpr::binary(BinaryOp::BitOr, shifted, lo_cast)
            }
            SSAOp::Subpiece { dst, src, offset } => {
                if *offset == 0 && dst.size == src.size {
                    self.get_expr(src)?
                } else if *offset == 0 {
                    CExpr::cast(uint_type_from_size(dst.size), self.get_expr(src)?)
                } else {
                    let shift_bits = offset.saturating_mul(8);
                    let src_cast = CExpr::cast(uint_type_from_size(src.size), self.get_expr(src)?);
                    let shifted =
                        CExpr::binary(BinaryOp::Shr, src_cast, CExpr::IntLit(shift_bits as i64));
                    CExpr::cast(uint_type_from_size(dst.size), shifted)
                }
            }
            SSAOp::FloatAdd { a, b, .. } => self.binary_expr(BinaryOp::Add, a, b)?,
            SSAOp::FloatSub { a, b, .. } => self.binary_expr(BinaryOp::Sub, a, b)?,
            SSAOp::FloatMult { a, b, .. } => self.binary_expr(BinaryOp::Mul, a, b)?,
            SSAOp::FloatDiv { a, b, .. } => self.binary_expr(BinaryOp::Div, a, b)?,
            SSAOp::FloatNeg { src, .. } => CExpr::unary(UnaryOp::Neg, self.get_expr(src)?),
            SSAOp::FloatAbs { src, .. } => self.intrinsic_call("fabs", src)?,
            SSAOp::FloatSqrt { src, .. } => self.intrinsic_call("sqrt", src)?,
            SSAOp::FloatCeil { src, .. } => self.intrinsic_call("ceil", src)?,
            SSAOp::FloatFloor { src, .. } => self.intrinsic_call("floor", src)?,
            SSAOp::FloatRound { src, .. } => self.intrinsic_call("round", src)?,
            SSAOp::FloatNaN { src, .. } => self.intrinsic_call("isnan", src)?,
            SSAOp::FloatLess { a, b, .. } => self.binary_expr(BinaryOp::Lt, a, b)?,
            SSAOp::FloatLessEqual { a, b, .. } => self.binary_expr(BinaryOp::Le, a, b)?,
            SSAOp::FloatEqual { a, b, .. } => self.binary_expr(BinaryOp::Eq, a, b)?,
            SSAOp::FloatNotEqual { a, b, .. } => self.binary_expr(BinaryOp::Ne, a, b)?,
            SSAOp::Int2Float { dst, src } => {
                let ty = CType::Float(dst.size);
                CExpr::cast(ty, self.get_expr(src)?)
            }
            SSAOp::Float2Int { dst, src } => {
                CExpr::cast(type_from_size(dst.size), self.get_expr(src)?)
            }
            SSAOp::FloatFloat { dst, src } => {
                CExpr::cast(CType::Float(dst.size), self.get_expr(src)?)
            }
            SSAOp::Cast { dst, src } => CExpr::cast(type_from_size(dst.size), self.get_expr(src)?),
            SSAOp::Select {
                cond,
                if_true,
                if_false,
                ..
            } => CExpr::Ternary {
                cond: Box::new(self.get_expr(cond)?),
                then_expr: Box::new(self.get_expr(if_true)?),
                else_expr: Box::new(self.get_expr(if_false)?),
            },
            SSAOp::Call { target } => CExpr::call(self.get_expr(target)?, vec![]),
            SSAOp::CallInd { target } => {
                CExpr::call(CExpr::Deref(Box::new(self.get_expr(target)?)), vec![])
            }
            SSAOp::PtrAdd {
                dst,
                base,
                index,
                element_size,
            } => match self.render_semantic_value_for_var(dst, 0, &mut HashSet::new())? {
                Some(expr) => expr,
                None => self.ptr_arith_expr(base, index, *element_size, false)?,
            },
            SSAOp::PtrSub {
                dst,
                base,
                index,
                element_size,
            } => match self.render_semantic_value_for_var(dst, 0, &mut HashSet::new())? {
                Some(expr) => expr,
                None => self.ptr_arith_expr(base, index, *element_size, true)?,
            },
            _ => return Err(OpLoweringRefusal::unrepresentable_operation()),
        })
    }

    fn require_op_value_identities(&self, op: &SSAOp) -> Result<(), OpLoweringRefusal> {
        let Some(resolver) = self.binding_names else {
            #[cfg(test)]
            return Ok(());
            #[cfg(not(test))]
            return Err(OpLoweringRefusal::missing_program_variable());
        };
        let info = self
            .use_info
            .ok_or_else(|| OpLoweringRefusal::missing_program_variable())?;
        for var in op.sources() {
            if var.constant_bits().is_some() {
                continue;
            }
            let value = info
                .exact_value_id_for_var(var)
                .ok_or_else(|| OpLoweringRefusal::missing_program_variable())?;
            if !matches!(
                resolver
                    .require_value(value)
                    .map_err(|_| OpLoweringRefusal::missing_program_variable())?,
                PlannedValueSymbol::Bound(_)
            ) {
                return Err(OpLoweringRefusal::missing_program_variable());
            }
        }
        Ok(())
    }

    fn intrinsic_call(&self, name: &str, source: &SSAVar) -> Result<CExpr, OpLoweringRefusal> {
        Ok(CExpr::call(
            CExpr::External {
                name: name.to_string(),
                kind: crate::symbol::ExternalKind::Intrinsic,
            },
            vec![self.get_expr(source)?],
        ))
    }

    fn render_semantic_value_for_var(
        &self,
        var: &SSAVar,
        depth: u32,
        visited: &mut HashSet<ValueId>,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        let value_id = self.exact_value_id(var)?;
        if depth > 8 || !visited.insert(value_id) {
            return Ok(None);
        }

        let rendered = match self.semantic_value_for_var(var) {
            Some(value) => self.render_semantic_value(value, depth + 1, visited)?,
            None => None,
        };
        visited.remove(&value_id);
        Ok(rendered)
    }

    fn render_semantic_value(
        &self,
        value: &SemanticValue,
        depth: u32,
        visited: &mut HashSet<ValueId>,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        match value {
            SemanticValue::Scalar(ScalarValue::Expr(expr)) => Ok(Some(expr.clone())),
            SemanticValue::Scalar(ScalarValue::Root(value)) => {
                self.render_value_ref(value, depth, visited)
            }
            SemanticValue::Address(shape) => self.render_addr_shape(shape, depth, visited),
            SemanticValue::Load { space, addr, size } => {
                // This cache is advisory only. MachineProjection owns whether a
                // load is renderable; omission here can never authorize an AST
                // node for a non-RAM space.
                if *space == r2il::SpaceId::Ram {
                    self.render_load_from_shape(addr, *size, depth, visited)
                } else {
                    Ok(None)
                }
            }
            SemanticValue::Unknown => Ok(None),
        }
    }

    fn render_load_from_shape(
        &self,
        shape: &NormalizedAddr,
        elem_size: u32,
        depth: u32,
        visited: &mut HashSet<ValueId>,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        if let Some(index) = &shape.index {
            let scale = shape.scale_bytes.unsigned_abs() as u32;
            if scale == elem_size && shape.offset_bytes == 0 {
                let Some(base_expr) = self.render_addr_base(shape, depth + 1, visited)? else {
                    return Ok(None);
                };
                let Some(index_expr) = self.render_value_ref(index, depth + 1, visited)? else {
                    return Ok(None);
                };
                let Some(index_expr) = self.normalize_index_expr(&index_expr, 0) else {
                    return Ok(None);
                };
                return Ok(self.build_subscript_expr(
                    self.normalize_pointer_base_expr(&base_expr, 0),
                    index_expr,
                    uint_type_from_size(elem_size),
                    shape.scale_bytes < 0,
                ));
            }
        }

        Ok(self
            .render_addr_shape(shape, depth + 1, visited)?
            .map(|expr| CExpr::Deref(Box::new(expr))))
    }

    fn render_addr_shape(
        &self,
        shape: &NormalizedAddr,
        depth: u32,
        visited: &mut HashSet<ValueId>,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        if depth > 8 {
            return Ok(None);
        }

        let Some(mut expr) = self.render_addr_base(shape, depth + 1, visited)? else {
            return Ok(None);
        };
        if let Some(index) = &shape.index {
            let Some(index_expr) = self.render_value_ref(index, depth + 1, visited)? else {
                return Ok(None);
            };
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
        Ok(Some(expr))
    }

    fn render_addr_base(
        &self,
        shape: &NormalizedAddr,
        depth: u32,
        visited: &mut HashSet<ValueId>,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        match &shape.base {
            BaseRef::StackSlot(_) => Ok(None),
            BaseRef::Value(base) => self.render_value_ref(base, depth + 1, visited),
            BaseRef::Raw(expr) => Ok(Some(expr.clone())),
        }
    }

    fn render_value_ref(
        &self,
        value: &ValueRef,
        depth: u32,
        visited: &mut HashSet<ValueId>,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        let value_id = self.exact_value_id(&value.var)?;
        if value
            .value_id
            .is_some_and(|certificate| certificate != value_id)
        {
            return Err(OpLoweringRefusal::missing_program_variable());
        }
        if !visited.insert(value_id) {
            return Ok(None);
        }
        if let Some(resolver) = self.binding_names {
            resolver
                .require_value(value_id)
                .map_err(|_| OpLoweringRefusal::missing_program_variable())?;
        }
        let expr = self.get_expr_with_depth(&value.var, depth, visited);
        visited.remove(&value_id);
        expr.map(Some)
    }

    fn should_inline_value(&self, value: ValueId) -> bool {
        let use_count = self.use_count_for_value(value);
        if use_count == 0 || use_count > 3 {
            return false;
        }

        // Legacy pinning has no value identity. Until its producer carries
        // ValueIds, any pin conservatively disables optional inlining.
        if !self.pinned.is_empty() {
            return false;
        }

        if self.is_condition_value(value) {
            return false;
        }

        use_count == 1
    }

    fn constant_to_expr(&self, val: u64) -> CExpr {
        if let Some(expr) = self.resolve_addr_literal(val) {
            return expr;
        }
        if val > 0x7fffffff {
            CExpr::UIntLit(val)
        } else {
            CExpr::IntLit(val as i64)
        }
    }

    #[cfg(test)]
    fn fixture_constant_to_expr(&self, var: &SSAVar) -> Result<CExpr, OpLoweringRefusal> {
        let value = parse_const_value(&var.name)
            .ok_or_else(|| OpLoweringRefusal::missing_program_variable())?;
        Ok(self.constant_to_expr(value))
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

    fn binary_expr(
        &self,
        op: BinaryOp,
        a: &SSAVar,
        b: &SSAVar,
    ) -> Result<CExpr, OpLoweringRefusal> {
        Ok(CExpr::binary(op, self.get_expr(a)?, self.get_expr(b)?))
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
    ) -> Result<CExpr, OpLoweringRefusal> {
        let mut lhs = self.get_expr(a)?;
        let mut rhs = self.get_expr(b)?;
        if let Some(ty) = operand_ty {
            lhs = self.cast_expr_if_needed(lhs, ty.clone());
            rhs = self.cast_expr_if_needed(rhs, ty);
        }
        Ok(CExpr::binary(op, lhs, rhs))
    }

    fn ptr_arith_expr(
        &self,
        base: &SSAVar,
        index: &SSAVar,
        element_size: u32,
        is_sub: bool,
    ) -> Result<CExpr, OpLoweringRefusal> {
        let base_expr = self.get_expr(base)?;
        let index_expr = self.get_expr(index)?;
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
        Ok(CExpr::binary(op, base_expr, scaled))
    }

    fn ptr_subscript_expr(
        &self,
        base: &SSAVar,
        index: &SSAVar,
        element_size: u32,
        is_sub: bool,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
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
        let base_expr = self.normalize_pointer_base_expr(&self.get_expr(base)?, 0);
        let Some(index_expr) = self.normalize_index_expr(&self.get_expr(index)?, 0) else {
            return Ok(None);
        };
        Ok(self.build_subscript_expr(base_expr, index_expr, elem_ty, is_sub))
    }

    fn typed_deref_expr(&self, addr: &SSAVar, elem_size: u32) -> Result<CExpr, OpLoweringRefusal> {
        let addr_expr = self.get_expr(addr)?;
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
        Ok(CExpr::Deref(Box::new(casted)))
    }

    fn looks_like_pointer_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Cast { ty, .. } => matches!(ty, CType::Pointer(_)),
            CExpr::Deref(_)
            | CExpr::Subscript { .. }
            | CExpr::Member { .. }
            | CExpr::PtrMember { .. } => true,
            // A SymbolId is a presentation handle, not a recoverable SSAVar.
            // Exact pointer evidence is queried before this structural helper.
            CExpr::Var(_) => false,
            CExpr::Paren(inner) => self.looks_like_pointer_expr(inner),
            _ => false,
        }
    }

    fn try_subscript_from_var(
        &self,
        addr: &SSAVar,
        elem_size: u32,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        if let Some(expr) = self.definition_for_var(addr)
            && let Some(sub) = self.try_subscript_from_addr_expr(expr, elem_size)
        {
            return Ok(Some(sub));
        }
        let resolved = self.get_expr(addr)?;
        if let Some(sub) = self.try_subscript_from_addr_expr(&resolved, elem_size) {
            return Ok(Some(sub));
        }
        if let Some(ptr) = self.ptr_arith_for_var(addr) {
            return self.ptr_subscript_expr(&ptr.base, &ptr.index, ptr.element_size, ptr.is_sub);
        }
        Ok(None)
    }

    fn try_member_access_from_var(
        &self,
        addr: &SSAVar,
    ) -> Result<Option<CExpr>, OpLoweringRefusal> {
        if let Some(expr) = self.definition_for_var(addr)
            && let Some(member) = self.try_member_access_from_addr_expr(Some(addr), expr)
        {
            return Ok(Some(member));
        }
        let resolved = self.get_expr(addr)?;
        if let Some(member) = self.try_member_access_from_addr_expr(Some(addr), &resolved) {
            return Ok(Some(member));
        }
        Ok(None)
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
            CExpr::Var(_) => None,
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
            CExpr::Var(_) => None,
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
            CExpr::Var(_) => Some((expr.clone(), 1)),
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
            CExpr::Var(_) => true,
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
            CExpr::Var(_) => expr.clone(),
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
            CExpr::Var(_) => Some(expr.clone()),
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
            // No reverse spelling-to-type lookup. Callers with an SSAVar ask
            // TypeOracle before reaching this structural fallback.
            CExpr::Var(_) => false,
            CExpr::Paren(inner) => self.is_non_index_pointer_expr(inner),
            CExpr::Unary { operand, .. } => self.is_non_index_pointer_expr(operand),
            _ => false,
        }
    }

    fn is_semantic_member_base(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(_) => true,
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
        _definitions: &'a HashMap<String, CExpr>,
        _use_counts: &'a HashMap<String, usize>,
        _condition_vars: &'a HashSet<String>,
        pinned: &'a HashSet<String>,
        _ptr_arith: &'a HashMap<String, PtrArith>,
        _forwarded_values: &'a HashMap<String, ValueProvenance>,
        #[cfg(test)] _function_names: &'a HashMap<u64, String>,
        #[cfg(test)] _strings: &'a HashMap<u64, String>,
        #[cfg(test)] _symbol_names: &'a HashMap<u64, String>,
    ) -> LowerCtx<'a> {
        LowerCtx {
            binding_names: None,
            symbols,
            string_literals: crate::analysis::lower::no_string_literals(),
            // These facts live in one store keyed by identity, so the maps a
            // test hands in are seeded into a `UseInfo` rather than being
            // consulted as a second source. Leaked because the context borrows
            // it and the tests build both inline.
            use_info: Some(Box::leak(Box::new({
                let mut info = crate::analysis::UseInfo::default();
                for (name, expr) in _definitions {
                    info.insert_definition_for_name_if_absent(name, expr.clone());
                }
                for (name, count) in _use_counts {
                    if let Some(value_id) = info.value_id_for_name_or_bind(name) {
                        info.use_counts_by_value.insert(value_id, *count);
                    }
                }
                for name in _condition_vars {
                    if let Some(value_id) = info.value_id_for_name_or_bind(name) {
                        info.condition_values.insert(value_id);
                    }
                }
                for (name, ptr) in _ptr_arith {
                    if let Some(value_id) = info.value_id_for_name_or_bind(name) {
                        info.ptr_arith_by_value.insert(value_id, ptr.clone());
                    }
                }
                for (name, provenance) in _forwarded_values {
                    if let Some(value_id) = info.value_id_for_name_or_bind(name) {
                        info.forwarded_values_by_value
                            .insert(value_id, provenance.clone());
                    }
                }
                info
            }))),
            pinned,
            type_oracle: None,
        }
    }

    #[test]
    fn floating_intrinsic_is_external_not_a_program_variable() {
        let symbols = test_table();
        let empty_exprs = HashMap::new();
        let empty_counts = HashMap::new();
        let empty_names = HashSet::new();
        let empty_ptrs = HashMap::new();
        let empty_forwarded = HashMap::new();
        let empty_addresses = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &empty_exprs,
            &empty_counts,
            &empty_names,
            &empty_names,
            &empty_ptrs,
            &empty_forwarded,
            &empty_addresses,
            &empty_addresses,
            &empty_addresses,
        );
        let op = SSAOp::FloatAbs {
            dst: SSAVar::new("tmp:dst", 1, 8),
            src: SSAVar::constant(1, 8),
        };

        assert_eq!(
            ctx.op_to_expr(&op),
            Ok(CExpr::call(
                CExpr::External {
                    name: "fabs".to_string(),
                    kind: crate::symbol::ExternalKind::Intrinsic,
                },
                vec![CExpr::IntLit(1)],
            ))
        );
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
        let ptr_arith = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &ptr_arith,
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
        let ptr_arith = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(ctx.resolve_addr_literal(0xff), None);
        assert_eq!(ctx.resolve_addr_literal(0x5000), None);
    }

    #[test]
    fn opaque_machine_operations_cannot_be_lowered_to_executable_c() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        let opaque = [
            SSAOp::CallOther {
                output: Some(SSAVar::new("X30", 1, 8)),
                userop: 7,
                inputs: vec![SSAVar::new("X30", 0, 8), SSAVar::new("SP", 0, 8)],
            },
            SSAOp::CpuId {
                dst: SSAVar::new("EAX", 1, 4),
            },
        ];
        for op in opaque {
            assert_eq!(
                ctx.op_to_expr(&op),
                Err(OpLoweringRefusal::missing_machine_projection()),
                "opaque operations must retain the canonical machine refusal"
            );
        }
    }

    #[test]
    fn ram_load_without_exact_value_bindings_is_refused() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Load {
                dst: SSAVar::new("tmp:5001", 1, 4),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:5000", 1, 8),
            }),
            Err(OpLoweringRefusal::missing_program_variable()),
            "a raw SSA spelling cannot authorize an executable memory expression"
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
        let ptr_arith = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &ptr_arith,
            &forwarded_values,
            &function_names,
            &strings,
            &binary_symbols,
        );
        let refusal = ctx.op_to_expr(&SSAOp::Load {
            dst: SSAVar::new("tmp:custom_result", 1, 4),
            space: r2il::SpaceId::Custom(7),
            addr: SSAVar::new("tmp:custom_addr", 1, 8),
        });

        assert_eq!(
            refusal,
            Err(OpLoweringRefusal::missing_machine_projection()),
            "custom-space memory requires an upstream machine projection"
        );
    }

    #[test]
    fn semantic_load_rendering_requires_exact_value_identity_for_ram() {
        let symbols = test_table();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
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
            &ptr_arith,
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
        let ram = ctx.expr_for_semantic_value(&SemanticValue::Load {
            space: r2il::SpaceId::Ram,
            addr: addr.clone(),
            size: 4,
        });
        let custom = ctx.expr_for_semantic_value(&SemanticValue::Load {
            space: r2il::SpaceId::Custom(7),
            addr,
            size: 4,
        });

        assert_eq!(
            ram,
            Err(OpLoweringRefusal::missing_program_variable()),
            "a raw value root cannot authorize an executable RAM access"
        );
        assert_eq!(custom, Ok(None));
    }

    #[test]
    fn pointer_spelling_does_not_authorize_a_ram_load() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Load {
                dst: SSAVar::new("tmp:5101", 1, 4),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("arg1", 0, 8),
            }),
            Err(OpLoweringRefusal::missing_program_variable()),
            "a pointer-like spelling is not a machine projection certificate"
        );
    }

    #[test]
    fn name_keyed_negative_index_definition_does_not_authorize_a_load() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
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
                        expr: Box::new(CExpr::unary(
                            UnaryOp::Neg,
                            crate::symbol::var_ref(&symbols, "arg2"),
                        )),
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
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Load {
                dst: SSAVar::new("tmp:5002", 1, 4),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:addr", 1, 8),
            }),
            Err(OpLoweringRefusal::missing_program_variable()),
            "a name-keyed address definition cannot authorize a subscript"
        );
    }

    #[test]
    fn name_keyed_stack_slot_does_not_authorize_a_load() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let definitions = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
        let forwarded_values = HashMap::new();
        let ctx = make_ctx(
            &symbols,
            &definitions,
            &use_counts,
            &condition_vars,
            &pinned,
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Load {
                dst: SSAVar::new("tmp:5003", 1, 4),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:stackaddr", 1, 8),
            }),
            Err(OpLoweringRefusal::missing_program_variable()),
            "a name-keyed stack offset is not an ObjectId-backed projection"
        );
    }

    #[test]
    fn name_keyed_base_plus_const_does_not_authorize_a_load() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
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
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Load {
                dst: SSAVar::new("tmp:5004", 1, 4),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:addr", 1, 8),
            }),
            Err(OpLoweringRefusal::missing_program_variable()),
            "a name-keyed expression cannot authorize pointer arithmetic"
        );
    }

    #[test]
    fn name_keyed_const_index_alias_does_not_authorize_a_load() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
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
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Load {
                dst: SSAVar::new("tmp:5005", 1, 4),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:addr", 1, 8),
            }),
            Err(OpLoweringRefusal::missing_program_variable()),
            "a name-keyed alias chain cannot authorize an array subscript"
        );
    }

    #[test]
    fn name_keyed_base_alias_does_not_authorize_a_load() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
        let ptr_arith = HashMap::new();
        let forwarded_values = HashMap::new();
        let definitions = HashMap::from([
            (
                "tmp:base_1".to_string(),
                crate::symbol::var_ref(&symbols, "rdx_1"),
            ),
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
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Load {
                dst: SSAVar::new("tmp:5006", 1, 4),
                space: r2il::SpaceId::Ram,
                addr: SSAVar::new("tmp:addr", 1, 8),
            }),
            Err(OpLoweringRefusal::missing_program_variable()),
            "a name-keyed base alias cannot authorize member syntax"
        );
    }

    #[test]
    fn name_keyed_pointer_arithmetic_does_not_authorize_a_load() {
        let symbols = test_table();
        let fn_map = HashMap::new();
        let str_map = HashMap::new();
        let sym_map = HashMap::new();
        let use_counts = HashMap::new();
        let condition_vars = HashSet::new();
        let pinned = HashSet::new();
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
            (
                "local_8".to_string(),
                crate::symbol::var_ref(&symbols, "arg1"),
            ),
            (
                "local_c".to_string(),
                crate::symbol::var_ref(&symbols, "arg2"),
            ),
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
            &ptr_arith,
            &forwarded_values,
            &fn_map,
            &str_map,
            &sym_map,
        );

        assert_eq!(
            ctx.op_to_expr(&SSAOp::Load {
                dst: SSAVar::new("tmp:5007", 1, 4),
                space: r2il::SpaceId::Ram,
                addr,
            }),
            Err(OpLoweringRefusal::missing_program_variable()),
            "name-keyed pointer arithmetic cannot authorize an exact projection"
        );
    }
}
