use crate::ast::{BinaryOp, CExpr};
use r2ssa::{ObjectId, ObjectKind, SSAVar};

use super::MAX_STACK_OFFSET_DEPTH;
use super::context::FoldingContext;

/// Threshold for detecting 64-bit negative values stored as unsigned.
/// Values above this are likely negative offsets (within ~65536 of u64::MAX).
/// This handles cases like stack offsets: 0xffffffffffffffb8 represents -72.
const LIKELY_NEGATIVE_THRESHOLD: u64 = 0xffffffffffff0000;

impl<'a> FoldingContext<'a> {
    fn prepared_stack_alias_view(&self) -> Option<&crate::analysis::PreparedSemanticView> {
        self.prepared_semantic_view()
    }

    pub(super) fn prepared_stack_offset_for_var(&self, var: &SSAVar) -> Option<i64> {
        let objects = self.prepared_objects()?;
        let object = self
            .inputs
            .prepared_ssa?
            .object_for_var(var, r2il::SpaceId::Ram)
            .or_else(|| {
                self.prepared_canonical_value_root(var).and_then(|root| {
                    self.inputs
                        .prepared_ssa?
                        .object_for_var(&root, r2il::SpaceId::Ram)
                })
            })?;
        let fact = objects.object(object)?;
        match fact.kind {
            ObjectKind::StackSlot { offset, .. } | ObjectKind::FrameObject { offset, .. } => {
                Some(offset)
            }
            _ => None,
        }
    }

    pub(super) fn certified_stack_var_expr_for_object(&self, object: ObjectId) -> Option<CExpr> {
        let names = self.inputs.binding_names?;
        match names.require_stack(object) {
            Ok(crate::binding_plan::PlannedStackSymbol::Bound(symbol)) => Some(CExpr::Var(symbol)),
            Ok(
                crate::binding_plan::PlannedStackSymbol::Refused(_)
                | crate::binding_plan::PlannedStackSymbol::Absent,
            ) => unreachable!("require_stack cannot return absent or refused"),
            Err(_) => {
                self.retain_first_lowering_refusal(
                    super::op_lower::OpLoweringRefusal::MissingProgramVariableAuthorization,
                );
                None
            }
        }
    }

    /// Try to extract a stack offset from a variable name or its definition.
    pub(crate) fn extract_stack_offset_from_var(&self, var: &SSAVar) -> Option<i64> {
        if let Some(offset) = self
            .prepared_stack_alias_view()
            .and_then(|view| view.stack_offset_for_var(var))
        {
            return Some(offset);
        }
        if let Some(offset) = self.prepared_stack_offset_for_var(var) {
            return Some(offset);
        }

        let name_lower = var.name.to_lowercase();

        // Direct fp/sp reference
        if self.inputs.arch.is_stack_base_name(&name_lower) {
            return Some(0);
        }

        if let Some(slot) = self.stack_slot_provenance_for_var(var) {
            return Some(slot.offset);
        }

        // Check if this variable was defined as fp/sp + offset
        if let Some(expr) = self.definition_for_name(&var.display_name()) {
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

        match expr.unobserved() {
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
                let name_lower = self.spelling(*name).to_lowercase();
                if self.inputs.arch.is_stack_base_name(&name_lower) {
                    return Some(0);
                }
                // Stack provenance is a property of the raw SSA address chain.
                // Full visible-definition resolution also ranks semantic values,
                // call-result owners, and rendered aliases, which cannot improve
                // an FP/SP-relative offset and may erase the address shape.
                self.lookup_definition_raw(&self.spelling(*name))
                    .and_then(|inner| self.extract_offset_from_expr_with_depth(&inner, depth + 1))
            }
            _ => None,
        }
    }

    pub(super) fn is_stack_base_expr(&self, expr: &CExpr) -> bool {
        match expr.unobserved() {
            CExpr::Var(name) => self
                .inputs
                .arch
                .is_stack_base_name(&self.spelling(*name).to_lowercase()),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } | CExpr::AddrOf(inner) => {
                self.is_stack_base_expr(inner)
            }
            _ => false,
        }
    }

    /// Convert an expression to an offset value.
    pub(super) fn expr_to_offset(&self, expr: &CExpr) -> Option<i64> {
        match expr.unobserved() {
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

    /// Whether a copy restates a carrier update the block has already rendered.
    ///
    /// Materialising a merge replaces it with a copy on every predecessor edge,
    /// so a loop carries its update back to the header as `X8_2 = X8_3`. Once the
    /// alias map covers what materialisation introduced, both sides are spelled
    /// by the carrier's one name and the copy says `x8 = x8`, which the statement
    /// that computed the update has already said.
    ///
    /// The edge into the loop is the same kind of copy and must be kept, because
    /// nothing else introduces the carrier there. The two are told apart by
    /// whether the source is an entry value: a version-0 source is the value the
    /// function was called with and has no defining statement of its own, so the
    /// copy is the only place the carrier is given it.
    pub(super) fn is_carrier_self_copy(&self, dst: &SSAVar, src: &SSAVar) -> bool {
        if src.version == 0 {
            return false;
        }
        let (Some(dst_value), Some(src_value), Some(names), Some(render)) = (
            self.prepared_value_id_for_var(dst),
            self.prepared_value_id_for_var(src),
            self.inputs.binding_names,
            self.inputs.render_facts(),
        ) else {
            return false;
        };
        if render.loop_carrier_for_value(dst_value).is_none()
            || render.loop_carrier_for_value(src_value).is_none()
        {
            return false;
        }
        matches!(
            (names.require_value(dst_value), names.require_value(src_value)),
            (
                Ok(crate::binding_plan::PlannedValueSymbol::Bound(dst_symbol)),
                Ok(crate::binding_plan::PlannedValueSymbol::Bound(src_symbol)),
            ) if dst_symbol == src_symbol
        )
    }

    pub(crate) fn stack_var_expr_for_addr_var(&self, addr: &SSAVar) -> Option<CExpr> {
        let prepared = self.inputs.prepared_ssa?;
        let object = prepared
            .object_for_var(addr, r2il::SpaceId::Ram)
            .or_else(|| {
                self.prepared_canonical_value_root(addr)
                    .and_then(|root| prepared.object_for_var(&root, r2il::SpaceId::Ram))
            })?;
        let fact = prepared.objects().object(object)?;
        if !matches!(
            fact.kind,
            ObjectKind::StackSlot { .. } | ObjectKind::FrameObject { .. }
        ) {
            return None;
        }
        self.certified_stack_var_expr_for_object(object)
    }

    pub(crate) fn refuse_missing_stack_object_origin(&self, offset: i64) -> Option<String> {
        let _ = crate::binding_plan::RenderedIdentityRefusal::MissingStackObjectOrigin { offset };
        if self.inputs.binding_names.is_some() {
            self.retain_first_lowering_refusal(
                super::op_lower::OpLoweringRefusal::MissingProgramVariableAuthorization,
            );
        }
        None
    }

    pub(super) fn rewrite_stack_expr(&self, expr: CExpr) -> CExpr {
        if let CExpr::Observed { id, expr } = expr {
            return CExpr::observed(id, self.rewrite_stack_expr(*expr));
        }
        // Once an expression contains only SymbolIds, an offset/name lookup
        // cannot prove which source-owned stack object it denotes. Exact stack
        // projection happens earlier from ObjectId; this late pass only walks
        // the already-authorized expression.
        expr.map_children(&mut |child| self.rewrite_stack_expr(child))
    }
}

#[cfg(test)]
mod observation_transparency_tests {
    use super::*;
    use crate::ast::{CFunction, CStmt, CType, RenderObservationOwner, strip_render_observations};

    fn marked_stack_address(ctx: &FoldingContext<'_>, owner: &mut RenderObservationOwner) -> CExpr {
        let (_, base) = owner.observe_expr(ctx.name_ref("rbp")).unwrap();
        let (_, offset) = owner.observe_expr(CExpr::IntLit(-8)).unwrap();
        let address = CExpr::binary(BinaryOp::Add, CExpr::Paren(Box::new(base)), offset);
        let (_, address) = owner.observe_expr(address).unwrap();
        CExpr::Paren(Box::new(address))
    }

    fn validate_and_strip_expr(expr: CExpr, owner: &RenderObservationOwner) -> CExpr {
        let mut function =
            CFunction::new("observation_test", CType::Void).with_body(vec![CStmt::Expr(expr)]);
        let reachable = strip_render_observations(&mut function, owner.expected_count()).unwrap();
        assert_eq!(reachable.ids().count(), owner.expected_count());
        let CStmt::Expr(expr) = function.body.pop().unwrap() else {
            panic!("test expression changed statement kind");
        };
        expr
    }

    #[test]
    fn nested_observed_frame_pointer_offset_is_semantically_visible() {
        let ctx = FoldingContext::new(64);
        let mut owner = RenderObservationOwner::new();
        let address = marked_stack_address(&ctx, &mut owner);

        assert_eq!(ctx.extract_offset_from_expr(&address), Some(-8));
        let stripped = validate_and_strip_expr(address, &owner);
        assert_eq!(ctx.extract_offset_from_expr(&stripped), Some(-8));
    }
}
