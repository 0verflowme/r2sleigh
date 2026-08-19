use super::calls::CertifiedCallArgs;
use super::*;

impl<'a> FoldingContext<'a> {
    pub(super) fn lowered_from_stmt(stmt: CStmt) -> LoweredOp {
        match stmt {
            CStmt::Expr(CExpr::Binary {
                op: BinaryOp::Assign,
                left,
                right,
            }) => LoweredOp::Assign {
                lhs: *left,
                rhs: *right,
            },
            CStmt::Expr(expr) => LoweredOp::Expr(expr),
            CStmt::Return(expr) => LoweredOp::Return(expr),
            CStmt::Comment(text) => LoweredOp::Comment(text),
            CStmt::Empty => LoweredOp::None,
            _ => LoweredOp::None,
        }
    }

    pub(super) fn lowered_to_stmt(&self, lowered: LoweredOp) -> Option<CStmt> {
        match lowered {
            LoweredOp::Assign { lhs, rhs } => self.assign_stmt(lhs, rhs),
            LoweredOp::Expr(expr) => Some(CStmt::Expr(expr)),
            LoweredOp::Return(expr) => Some(CStmt::Return(expr)),
            LoweredOp::Comment(text) => Some(CStmt::Comment(text)),
            LoweredOp::None => None,
        }
    }

    fn lower_certified_statement_call(
        &self,
        block_addr: u64,
        op_idx: usize,
        call: CExpr,
        certified_args: CertifiedCallArgs,
    ) -> LoweredOp {
        if let Some(owner) =
            self.materializable_call_result_expr_for_call_expr((block_addr, op_idx), &call)
        {
            return LoweredOp::Assign {
                lhs: owner,
                rhs: call,
            };
        }
        return LoweredOp::Expr(call);

        let Some(callsite) = self.certified_callsite_for_op(block_addr, op_idx) else {
            return LoweredOp::Comment(format!(
                "r2sleigh residual: missing FunctionFacts callsite for rendered call at 0x{block_addr:x}:{op_idx}"
            ));
        };
        let Some(render_fact) = self.certified_call_render_fact_for_op(block_addr, op_idx) else {
            return LoweredOp::Comment(format!(
                "r2sleigh residual: missing FunctionFacts call-render disposition at 0x{block_addr:x}:{op_idx}"
            ));
        };
        if render_fact.target != Some(callsite.target) {
            return LoweredOp::Comment(format!(
                "r2sleigh residual: FunctionFacts call-render target mismatch at 0x{block_addr:x}:{op_idx}"
            ));
        }
        let mut render_proof_values = render_fact.proof_values.clone();
        if let Some(max_arity) = self.non_variadic_call_arity_for_site_with_direct_target(
            block_addr,
            op_idx,
            callsite.direct_target,
        ) {
            render_proof_values.truncate(max_arity);
        }
        if render_proof_values != certified_args.values {
            return LoweredOp::Comment(format!(
                "r2sleigh residual: FunctionFacts call-render argument proof mismatch at 0x{block_addr:x}:{op_idx}"
            ));
        }

        match render_fact.disposition {
            r2types::CallsiteRenderDisposition::AssignedResult => {
                let Some(owner) =
                    self.materializable_call_result_expr_for_call_expr((block_addr, op_idx), &call)
                else {
                    return LoweredOp::Comment(format!(
                        "r2sleigh residual: FunctionFacts assigned call lacks materializable call-result owner at 0x{block_addr:x}:{op_idx}"
                    ));
                };
                self.record_call_effect_render_proof(
                    block_addr,
                    op_idx,
                    render_fact.target,
                    certified_args.values.clone(),
                    render_fact.disposition,
                );
                self.record_certified_call_arg_memory_render_proofs(&certified_args.values);
                LoweredOp::Assign {
                    lhs: owner,
                    rhs: call,
                }
            }
            r2types::CallsiteRenderDisposition::SideEffectStatement => {
                self.record_call_effect_render_proof(
                    block_addr,
                    op_idx,
                    render_fact.target,
                    certified_args.values.clone(),
                    render_fact.disposition,
                );
                self.record_certified_call_arg_memory_render_proofs(&certified_args.values);
                LoweredOp::Expr(call)
            }
            r2types::CallsiteRenderDisposition::NestedExpression
            | r2types::CallsiteRenderDisposition::Suppressed
            | r2types::CallsiteRenderDisposition::Residualized => LoweredOp::Comment(format!(
                "r2sleigh residual: FunctionFacts call-render disposition {:?} is not a statement call at 0x{block_addr:x}:{op_idx}",
                render_fact.disposition
            )),
        }
    }

    pub(super) fn lower_op(&self, op: &SSAOp, frame: &mut LowerFrame) -> LoweredOp {
        match frame.mode {
            LowerMode::Expr => LoweredOp::Expr(self.op_to_expr_impl(op)),
            LowerMode::Stmt => {
                if frame.with_call_args {
                    match op {
                        SSAOp::Call { target } => {
                            let direct_target = parse_address_from_var_name(&target.name);
                            let func_expr = self.resolve_call_target_for_site(
                                frame.block_addr,
                                frame.op_idx,
                                target,
                            );
                            let raw_args = self
                                .call_args_map()
                                .get(&(frame.block_addr, frame.op_idx))
                                .cloned()
                                .unwrap_or_default();
                            let Some(mut certified_args) = self
                                .certified_call_args_for_site_with_direct_target(
                                    frame.block_addr,
                                    frame.op_idx,
                                    &func_expr,
                                    direct_target,
                                    raw_args,
                                )
                            else {
                                return LoweredOp::Comment(format!(
                                    "r2sleigh residual: uncertified callsite arguments at 0x{:x}:{}",
                                    frame.block_addr, frame.op_idx
                                ));
                            };
                            let mut args = certified_args.args.clone();
                            if let Some(max_arity) = self
                                .non_variadic_call_arity_for_site_with_direct_target(
                                    frame.block_addr,
                                    frame.op_idx,
                                    direct_target,
                                )
                            {
                                args.truncate(max_arity);
                                certified_args.values.truncate(max_arity);
                            }
                            let call = CExpr::call(func_expr, args);
                            return self.lower_certified_statement_call(
                                frame.block_addr,
                                frame.op_idx,
                                call,
                                certified_args,
                            );
                        }
                        SSAOp::CallInd { target } => {
                            let resolved_target = self.resolve_call_target_for_site(
                                frame.block_addr,
                                frame.op_idx,
                                target,
                            );
                            let func_expr = match resolved_target {
                                CExpr::Var(_) => resolved_target,
                                other => CExpr::Deref(Box::new(other)),
                            };
                            let raw_args = self
                                .call_args_map()
                                .get(&(frame.block_addr, frame.op_idx))
                                .cloned()
                                .unwrap_or_default();
                            let Some(mut certified_args) = self.certified_call_args_for_site(
                                frame.block_addr,
                                frame.op_idx,
                                &func_expr,
                                raw_args,
                            ) else {
                                return LoweredOp::Comment(format!(
                                    "r2sleigh residual: uncertified indirect-call arguments at 0x{:x}:{}",
                                    frame.block_addr, frame.op_idx
                                ));
                            };
                            let mut args = certified_args.args.clone();
                            if let Some(max_arity) = self
                                .non_variadic_call_arity_for_site(frame.block_addr, frame.op_idx)
                            {
                                args.truncate(max_arity);
                                certified_args.values.truncate(max_arity);
                            }
                            let call = CExpr::call(func_expr, args);
                            return self.lower_certified_statement_call(
                                frame.block_addr,
                                frame.op_idx,
                                call,
                                certified_args,
                            );
                        }
                        _ => {}
                    }
                }

                self.op_to_stmt_impl(op)
                    .map(Self::lowered_from_stmt)
                    .unwrap_or(LoweredOp::None)
            }
        }
    }

    pub(crate) fn op_to_expr(&self, op: &SSAOp) -> CExpr {
        let mut frame = LowerFrame::for_expr();
        match self.lower_op(op, &mut frame) {
            LoweredOp::Expr(expr) => expr,
            LoweredOp::Assign { lhs, rhs } => CExpr::assign(lhs, rhs),
            LoweredOp::Return(Some(expr)) => expr,
            LoweredOp::Return(None) => CExpr::Var("return".to_string()),
            LoweredOp::Comment(_) | LoweredOp::None => {
                if let Some(dst) = op.dst() {
                    CExpr::Var(self.var_name(dst))
                } else {
                    CExpr::Var("__unhandled_op__".to_string())
                }
            }
        }
    }

    /// Convert an SSA operation to a C statement, with call argument context.
    pub(super) fn op_to_stmt_with_args(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<CStmt> {
        let mut frame = LowerFrame::for_stmt(block_addr, op_idx, true);
        let stmt = self.lowered_to_stmt(self.lower_op(op, &mut frame))?;
        if self.requires_certified_rendering()
            && !matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. })
            && self
                .record_certified_call_render_proofs_for_stmt_with_current(
                    &stmt,
                    Some((block_addr, op_idx)),
                )
                .is_none()
        {
            return Some(self.certified_residual_comment(format!(
                "uncertified rendered call at 0x{:x}:{}",
                block_addr, op_idx
            )));
        }
        if self.requires_certified_rendering() && stmt_is_side_effect_free_generated_carrier(&stmt)
        {
            return None;
        }
        if self.requires_certified_rendering()
            && self.stmt_is_side_effect_free_versioned_register_carrier(&stmt)
        {
            return Some(stmt);
        }
        if self.requires_certified_rendering() && stmt_requires_expression_render_proof(&stmt) {
            let phi_edge = self.certified_phi_edge_render_proof(op, &stmt, block_addr);
            let value = match op {
                SSAOp::Store { val, .. } => self.prepared_value_id_for_var(val),
                _ => op.dst().and_then(|dst| self.prepared_value_id_for_var(dst)),
            };
            match value {
                Some(value)
                    if self
                        .certified_render_context()
                        .is_some_and(|proof| proof.expression_is_renderable(value)) =>
                {
                    if let Some(phi_edge) = phi_edge {
                        self.record_effect_render_proof_for_phi_edge(
                            block_addr,
                            op_idx,
                            Some(value),
                            phi_edge,
                        );
                    } else {
                        self.record_effect_render_proof_for_value(
                            EffectRenderProofKind::Expression,
                            block_addr,
                            op_idx,
                            Some(value),
                        );
                    }
                }
                Some(value) => {
                    return Some(self.certified_residual_comment(format!(
                        "uncertified expression value {:?} at 0x{:x}:{}",
                        value, block_addr, op_idx
                    )));
                }
                None => {
                    return Some(self.certified_residual_comment(format!(
                        "missing expression value proof at 0x{:x}:{}",
                        block_addr, op_idx
                    )));
                }
            }
        }
        if stmt_contains_memory_like_access(&stmt) {
            match op {
                SSAOp::Load { .. } => {
                    if let Some((space, address, value)) = self
                        .certified_memory_access_for_current_op(false)
                        .map(|cert| (cert.space, cert.address, cert.value))
                    {
                        self.record_effect_render_proof_for_memory(
                            EffectRenderProofKind::MemoryRead,
                            block_addr,
                            op_idx,
                            space,
                            address,
                            value,
                        );
                    }
                }
                SSAOp::Store { .. } => {
                    if let Some((space, address, value)) = self
                        .certified_memory_access_for_current_op(true)
                        .map(|cert| (cert.space, cert.address, cert.value))
                    {
                        self.record_effect_render_proof_for_memory(
                            EffectRenderProofKind::MemoryWrite,
                            block_addr,
                            op_idx,
                            space,
                            address,
                            value,
                        );
                    }
                }
                _ => {
                    if self.requires_certified_rendering()
                        && let Some(value) =
                            op.dst().and_then(|dst| self.prepared_value_id_for_var(dst))
                        && let Some((block_addr, op_index, space, address, value)) = self
                            .certified_memory_read_for_value_dependency(value)
                            .map(|cert| {
                                (
                                    cert.block_addr,
                                    cert.op_index,
                                    cert.space,
                                    cert.address,
                                    cert.value,
                                )
                            })
                    {
                        self.record_effect_render_proof_for_memory(
                            EffectRenderProofKind::MemoryRead,
                            block_addr,
                            op_index,
                            space,
                            address,
                            value,
                        );
                    }
                }
            }
        }
        Some(stmt)
    }
}
