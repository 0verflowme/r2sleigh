use super::calls::CertifiedCallArgs;
use super::*;

impl<'a> FoldingContext<'a> {
    pub(super) fn observed_input(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        if frame.observe_inputs {
            self.observe_optional_normalized_input_expr(frame.normalized_site, input_idx, expr)
        } else {
            expr
        }
    }

    pub(super) fn lowered_from_stmt(stmt: CStmt) -> LoweredOp {
        match stmt {
            CStmt::Empty => LoweredOp::None,
            stmt => LoweredOp::FinalizedStmt(stmt),
        }
    }

    pub(super) fn lowered_to_stmt(&self, lowered: LoweredOp) -> Option<CStmt> {
        match lowered {
            LoweredOp::Assign { lhs, rhs } => self.assign_stmt(lhs, rhs),
            LoweredOp::FinalizedStmt(stmt) => Some(stmt),
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
        _certified_args: CertifiedCallArgs,
    ) -> LoweredOp {
        if let Some(owner) =
            self.materializable_call_result_expr_for_call_expr((block_addr, op_idx), &call)
        {
            return LoweredOp::Assign {
                lhs: owner,
                rhs: call,
            };
        }
        LoweredOp::Expr(call)
    }

    pub(super) fn lower_op(&self, op: &SSAOp, frame: &mut LowerFrame) -> LoweredOp {
        match frame.mode {
            LowerMode::Expr => self
                .op_to_expr_impl(op, frame)
                .map(LoweredOp::Expr)
                .unwrap_or(LoweredOp::None),
            LowerMode::Stmt => {
                if frame.with_call_args {
                    match op {
                        SSAOp::Call { target } => {
                            let Some((source_block, source_op_idx)) = frame.source_call_site else {
                                return LoweredOp::Comment(
                                    "r2sleigh residual: missing exact source callsite".to_string(),
                                );
                            };
                            let direct_target = parse_address_from_var_name(&target.name);
                            let func_expr = self.resolve_call_target_for_site(
                                source_block,
                                source_op_idx,
                                target,
                            );
                            let func_expr = self.observed_input(frame, 0, func_expr);
                            let raw_args = self
                                .call_args_map()
                                .get(&(source_block, source_op_idx))
                                .cloned()
                                .unwrap_or_default();
                            let Some(mut certified_args) = self
                                .certified_call_args_for_site_with_direct_target(
                                    source_block,
                                    source_op_idx,
                                    &func_expr,
                                    direct_target,
                                    raw_args,
                                )
                            else {
                                return LoweredOp::Comment(format!(
                                    "r2sleigh residual: uncertified callsite arguments at 0x{:x}:{}",
                                    source_block, source_op_idx
                                ));
                            };
                            let mut args = certified_args.args.clone();
                            if let Some(max_arity) = self
                                .non_variadic_call_arity_for_site_with_direct_target(
                                    source_block,
                                    source_op_idx,
                                    direct_target,
                                )
                            {
                                args.truncate(max_arity);
                                certified_args.values.truncate(max_arity);
                            }
                            let call =
                                CExpr::call_at((source_block, source_op_idx), func_expr, args);
                            return self.lower_certified_statement_call(
                                source_block,
                                source_op_idx,
                                call,
                                certified_args,
                            );
                        }
                        SSAOp::CallInd { target } => {
                            let Some((source_block, source_op_idx)) = frame.source_call_site else {
                                return LoweredOp::Comment(
                                    "r2sleigh residual: missing exact source callsite".to_string(),
                                );
                            };
                            let resolved_target = self.resolve_call_target_for_site(
                                source_block,
                                source_op_idx,
                                target,
                            );
                            let resolved_target = self.observed_input(frame, 0, resolved_target);
                            let func_expr = Self::indirect_callable_expr(resolved_target);
                            let raw_args = self
                                .call_args_map()
                                .get(&(source_block, source_op_idx))
                                .cloned()
                                .unwrap_or_default();
                            let Some(mut certified_args) = self.certified_call_args_for_site(
                                source_block,
                                source_op_idx,
                                &func_expr,
                                raw_args,
                            ) else {
                                return LoweredOp::Comment(format!(
                                    "r2sleigh residual: uncertified indirect-call arguments at 0x{:x}:{}",
                                    source_block, source_op_idx
                                ));
                            };
                            let mut args = certified_args.args.clone();
                            if let Some(max_arity) = self
                                .non_variadic_call_arity_for_site(source_block, source_op_idx)
                            {
                                args.truncate(max_arity);
                                certified_args.values.truncate(max_arity);
                            }
                            let call = CExpr::call(func_expr, args);
                            return self.lower_certified_statement_call(
                                source_block,
                                source_op_idx,
                                call,
                                certified_args,
                            );
                        }
                        _ => {}
                    }
                }

                self.op_to_stmt_impl(op, frame)
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
            LoweredOp::FinalizedStmt(CStmt::Expr(expr)) => expr,
            LoweredOp::FinalizedStmt(CStmt::Return(Some(expr))) => expr,
            LoweredOp::FinalizedStmt(_) => CExpr::External {
                name: "__unhandled_op__".to_string(),
                kind: crate::symbol::ExternalKind::Intrinsic,
            },
            LoweredOp::Return(Some(expr)) => expr,
            LoweredOp::Return(None) => CExpr::External {
                name: "return".to_string(),
                kind: crate::symbol::ExternalKind::Intrinsic,
            },
            LoweredOp::Comment(_) | LoweredOp::None => {
                if let Some(dst) = op.dst() {
                    self.name_ref(&self.var_name(dst))
                } else {
                    CExpr::External {
                        name: "__unhandled_op__".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    }
                }
            }
        }
    }

    pub(crate) fn op_to_expr_at(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
    ) -> LoweredExprAt {
        // Occurrence identity must not alter semantic lowering. Lower through
        // the exact marker-free expression path, then decorate that answer.
        let mut frame = LowerFrame::for_expr();
        let lowered = self.lower_op(op, &mut frame);
        let lowered = match lowered {
            LoweredOp::Expr(expr) => LoweredExprAt::Rendered(expr),
            LoweredOp::Assign { lhs, rhs } => {
                LoweredExprAt::Rendered(CExpr::assign(lhs, rhs))
            }
            LoweredOp::FinalizedStmt(CStmt::Expr(expr)) => LoweredExprAt::Rendered(expr),
            LoweredOp::FinalizedStmt(CStmt::Return(Some(expr))) => {
                LoweredExprAt::Rendered(expr)
            }
            LoweredOp::FinalizedStmt(_) => LoweredExprAt::DestinationFallback(CExpr::External {
                name: "__unhandled_op__".to_string(),
                kind: crate::symbol::ExternalKind::Intrinsic,
            }),
            LoweredOp::Return(Some(expr)) => LoweredExprAt::Rendered(expr),
            LoweredOp::Return(None) => LoweredExprAt::Rendered(CExpr::External {
                name: "return".to_string(),
                kind: crate::symbol::ExternalKind::Intrinsic,
            }),
            LoweredOp::Comment(_) | LoweredOp::None => {
                LoweredExprAt::DestinationFallback(if let Some(dst) = op.dst() {
                    self.name_ref(&self.var_name(dst))
                } else {
                    CExpr::External {
                        name: "__unhandled_op__".to_string(),
                        kind: crate::symbol::ExternalKind::Intrinsic,
                    }
                })
            }
        };
        match lowered {
            LoweredExprAt::Rendered(expr) => LoweredExprAt::Rendered(
                self.observe_normalized_computed_expr(op, block_addr, op_idx, expr),
            ),
            fallback @ LoweredExprAt::DestinationFallback(_) => fallback,
        }
    }

    /// Attach exact input/output identities to a custom expression that
    /// represents one normalized computation but bypassed ordinary opcode
    /// lowering (currently the tracked return-register path).
    pub(crate) fn observe_normalized_computed_expr(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
        mut expr: CExpr,
    ) -> CExpr {
        for input_idx in 0..op.sources().len() {
            expr = self.observe_normalized_input_expr(block_addr, op_idx, input_idx, expr);
        }
        if op.dst().is_some() {
            expr = self.observe_normalized_output_expr(block_addr, op_idx, expr);
        }
        expr
    }

    /// Convert an SSA operation to a C statement, with call argument context.
    pub(super) fn op_to_stmt_with_args(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
    ) -> Option<CStmt> {
        let source_site = self.source_op_site_for_normalized_op(block_addr, op_idx);
        if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) && source_site.is_none() {
            return Some(self.certified_residual_comment(format!(
                "synthetic operation cannot carry callsite facts at 0x{block_addr:x}:{op_idx}"
            )));
        }
        let normalized_site = self.normalized_site(block_addr, op_idx);
        let source_call_site = source_site.or(Some((block_addr, op_idx)));
        let mut frame = LowerFrame::for_stmt(normalized_site, source_call_site, true);
        let stmt = self.lowered_to_stmt(self.lower_op(op, &mut frame))?;

        if stmt_contains_memory_like_access(&stmt) {
            match op {
                SSAOp::Load { .. } => {
                    if let Some((space, address, value)) = self
                        .certified_memory_access_for_current_op(false)
                        .map(|cert| (cert.space, cert.address, cert.value))
                    {
                        self.record_effect_render_proof_for_normalized_memory(
                            EffectRenderProofKind::MemoryRead,
                            block_addr,
                            op_idx,
                            space,
                            Some(address),
                            value,
                        );
                    }
                }
                SSAOp::Store { .. } => {
                    if let Some((space, address, value)) = self
                        .certified_memory_access_for_current_op(true)
                        .map(|cert| (cert.space, cert.address, cert.value))
                    {
                        self.record_effect_render_proof_for_normalized_memory(
                            EffectRenderProofKind::MemoryWrite,
                            block_addr,
                            op_idx,
                            space,
                            Some(address),
                            value,
                        );
                    }
                }
                _ => {}
            }
        }
        let stmt = if op.dst().is_some()
            && !matches!(stmt.unobserved(), CStmt::Comment(_) | CStmt::Empty)
        {
            self.observe_normalized_output_stmt(block_addr, op_idx, stmt)
        } else {
            stmt
        };
        Some(stmt)
    }

    /// Render one resolved indirect-call target without letting occurrence
    /// metadata change whether an already-callable variable is dereferenced.
    pub(super) fn indirect_callable_expr(resolved_target: CExpr) -> CExpr {
        match resolved_target.unobserved() {
            CExpr::Var(_) => resolved_target,
            _ => CExpr::Deref(Box::new(resolved_target)),
        }
    }
}
