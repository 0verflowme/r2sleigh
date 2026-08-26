use super::calls::CertifiedCallArgs;
use super::projection::{project_machine_use, project_machine_write};
use super::*;

impl<'a> FoldingContext<'a> {
    fn normalized_output_projection(
        &self,
        site: crate::normalize::NormalizedOpSite,
    ) -> Result<crate::normalize::NormalizedOutputProjection, crate::observation_journal::LegacyObservationJournalError>
    {
        let prepared = self.inputs.prepared_ssa.ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
        )?;
        self.inputs
            .normalization_origins
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
            )?
            .projection(site, prepared)
            .map_err(crate::observation_journal::LegacyObservationJournalError::Normalization)?
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedSite(
                    site,
                ),
            )?
            .output
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::MissingNormalizedOutput(
                    site,
                ),
            )
    }

    fn project_planned_assignment(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        lhs: CExpr,
        rhs: CExpr,
    ) -> Result<(CExpr, CExpr), crate::observation_journal::LegacyObservationJournalError> {
        let Some(site) = site else {
            return Ok((lhs, rhs));
        };
        let Some(names) = self.inputs.binding_names else {
            return Ok((lhs, rhs));
        };
        let output = self.normalized_output_projection(site)?;
        match names.write_disposition(output.inst) {
            Some(r2ssa::MachineWriteDisposition::Exact(projection)) => {
                project_machine_write(lhs, rhs, *projection).map_err(|_| {
                    crate::observation_journal::LegacyObservationJournalError::RefusedRenderedWrite(
                        output.inst,
                    )
                })
            }
            Some(r2ssa::MachineWriteDisposition::Refused(_)) => Err(
                crate::observation_journal::LegacyObservationJournalError::RefusedRenderedWrite(
                    output.inst,
                ),
            ),
            None => Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidWrite(
                    output.inst,
                ),
            ),
        }
    }

    fn project_lowered_assignment(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        lowered: LoweredOp,
    ) -> LoweredOp {
        let LoweredOp::Assign { lhs, rhs } = lowered else {
            return lowered;
        };
        match self.project_planned_assignment(site, lhs.clone(), rhs.clone()) {
            Ok((lhs, rhs)) => LoweredOp::Assign { lhs, rhs },
            Err(error) => {
                self.retain_first_observation_error(error);
                LoweredOp::Assign { lhs, rhs }
            }
        }
    }

    /// Apply a source write only when the finalized statement targets the
    /// exact plan-owned output binding. Synthetic assignments emitted while
    /// folding the same opcode (for example a recovered return slot) are not
    /// definitions of that `InstId` and must not inherit its machine effect.
    fn project_finalized_assignment_stmt(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        stmt: CStmt,
    ) -> CStmt {
        let Some(site) = site else {
            return stmt;
        };
        let Ok(output) = self.normalized_output_projection(site) else {
            return stmt;
        };
        let Some(names) = self.inputs.binding_names else {
            return stmt;
        };
        let crate::binding_plan::PlannedValueSymbol::Bound(symbol) =
            names.resolve_value(output.value)
        else {
            return stmt;
        };
        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) = stmt
        else {
            return stmt;
        };
        let lhs = *left;
        let rhs = *right;
        let planned_lhs = CExpr::Var(symbol);
        if !lhs.transparently_eq(&planned_lhs) {
            return CStmt::Expr(CExpr::assign(lhs, rhs));
        }
        match self.project_planned_assignment(Some(site), lhs.clone(), rhs.clone()) {
            Ok((lhs, rhs)) => CStmt::Expr(CExpr::assign(lhs, rhs)),
            Err(error) => {
                self.retain_first_observation_error(error);
                CStmt::Expr(CExpr::assign(lhs, rhs))
            }
        }
    }

    fn planned_value_expr(
        &self,
        value: ValueId,
    ) -> Result<CExpr, crate::observation_journal::LegacyObservationJournalError> {
        let Some(names) = self.inputs.binding_names else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::RenderedValueRequired(
                    value,
                ),
            );
        };
        match names.resolve_value(value) {
            crate::binding_plan::PlannedValueSymbol::Bound(symbol) => Ok(CExpr::Var(symbol)),
            crate::binding_plan::PlannedValueSymbol::Inline(expr) => {
                let Some(machine_expr) = names.inline_expr(expr) else {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                            value,
                            expr,
                        },
                    );
                };
                let r2ssa::MachineExprKind::Constant {
                    binding,
                    value: literal,
                } = machine_expr.kind()
                else {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                            value,
                            expr,
                        },
                    );
                };
                if binding.value() != value {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                            value,
                            expr,
                        },
                    );
                }
                let bits = literal.bits();
                Ok(if bits > i64::MAX as u64 {
                    CExpr::UIntLit(bits)
                } else {
                    CExpr::IntLit(bits as i64)
                })
            }
            crate::binding_plan::PlannedValueSymbol::Elided(reason) => Err(
                crate::observation_journal::LegacyObservationJournalError::PlannedElidedValueRendered {
                    value,
                    reason,
                },
            ),
            crate::binding_plan::PlannedValueSymbol::Refused(reason) => Err(
                crate::observation_journal::LegacyObservationJournalError::PlannedRefusedValueRendered {
                    value,
                    reason,
                },
            ),
            crate::binding_plan::PlannedValueSymbol::Absent => Err(
                crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(
                    value,
                ),
            ),
        }
    }

    fn planned_input_expr(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
        contextual_expr: CExpr,
    ) -> Result<CExpr, crate::observation_journal::LegacyObservationJournalError> {
        let site = frame.normalized_site.ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
        )?;
        let prepared = self.inputs.prepared_ssa.ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
        )?;
        let projection = self
            .inputs
            .normalization_origins
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::MissingNormalizedSiteContext,
            )?
            .projection(site, prepared)
            .map_err(crate::observation_journal::LegacyObservationJournalError::Normalization)?
            .ok_or(
                crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedSite(
                    site,
                ),
            )?;
        let input = projection.inputs.get(input_idx).ok_or(
            crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedInput {
                site,
                input_idx,
            },
        )?;
        let Some(first_site) = input.uses.first().copied() else {
            // Synthetic preservation inputs have no original graph use and
            // therefore no source-owned projection to apply.
            return Ok(self.observe_optional_normalized_input_value_expr(
                frame.normalized_site,
                input_idx,
                self.planned_value_expr(input.value)?,
            ));
        };
        let Some(names) = self.inputs.binding_names else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::RenderedValueRequired(
                    input.value,
                ),
            );
        };
        let first_disposition = match names.use_disposition(first_site) {
            Some(disposition @ (r2ssa::MachineUseDisposition::Exact(_)
            | r2ssa::MachineUseDisposition::MemoryAddress(_))) => *disposition,
            Some(r2ssa::MachineUseDisposition::Refused(_)) => {
                return Err(
                    crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                        first_site,
                    ),
                );
            }
            None => {
                return Err(
                    crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                        first_site,
                    ),
                );
            }
        };
        for use_site in input.uses.iter().copied().skip(1) {
            match names.use_disposition(use_site) {
                Some(disposition) if *disposition == first_disposition => {}
                Some(r2ssa::MachineUseDisposition::Refused(_)) => {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                            use_site,
                        ),
                    );
                }
                Some(
                    r2ssa::MachineUseDisposition::Exact(_)
                    | r2ssa::MachineUseDisposition::MemoryAddress(_),
                ) => {
                    // One relocated normalized expression cannot implement two
                    // different source projections. Keep the normalized site
                    // typed and refuse the projection instead of choosing one.
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedInput {
                            site,
                            input_idx,
                        },
                    );
                }
                None => {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                            use_site,
                        ),
                    );
                }
            }
        }
        match first_disposition {
            r2ssa::MachineUseDisposition::Exact(slice) => {
                let base = self.observe_optional_normalized_input_value_expr(
                    frame.normalized_site,
                    input_idx,
                    self.planned_value_expr(input.value)?,
                );
                project_machine_use(base, slice).map_err(|_| {
                    // The machine use is exact, but the strict C dialect cannot spell
                    // this projection without more type evidence. Refuse the emitted
                    // occurrence instead of inventing an integer or pointer type.
                    crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                        first_site,
                    )
                })
            }
            r2ssa::MachineUseDisposition::MemoryAddress(address) => {
                if address.binding().value() != input.value
                    || address.memory_access().is_none()
                {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                            first_site,
                        ),
                    );
                }
                // The load/store renderer has already consumed the source-owned
                // structured-access certificate. Preserve that contextual AST:
                // substituting the value's ordinary binding here would turn a
                // certified stack/object access back into an SP/RBP expression.
                // This node is the contextual projection, not an occurrence
                // of the value's ordinary binding. Mark only the exact
                // `UseSite`; wrapping it as a bound `ValueId` would make the
                // audit claim that a C variable was rendered where the AST in
                // fact contains a structured memory access.
                Ok(contextual_expr)
            }
            r2ssa::MachineUseDisposition::Refused(_) => unreachable!(
                "the refused source use returned before projection"
            ),
        }
    }

    pub(super) fn planned_current_output_expr(
        &self,
    ) -> Result<Option<CExpr>, crate::observation_journal::LegacyObservationJournalError> {
        if self.inputs.observation_journal.is_none() {
            return Ok(None);
        }
        let Some(block_addr) = self.current_block_addr.get() else {
            return Ok(None);
        };
        let Some(op_idx) = self.current_op_idx.get() else {
            return Ok(None);
        };
        let site = self.normalized_site(block_addr, op_idx).ok_or(
            crate::observation_journal::LegacyObservationJournalError::MissingNormalizedBlock(
                block_addr,
            ),
        )?;
        let value = self.normalized_output_projection(site)?.value;
        match self.inputs.binding_names.map(|names| names.resolve_value(value)) {
            Some(crate::binding_plan::PlannedValueSymbol::Bound(symbol)) => {
                Ok(Some(CExpr::Var(symbol)))
            }
            Some(crate::binding_plan::PlannedValueSymbol::Inline(expr)) => Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                    value,
                    expr,
                },
            ),
            // An attempted lowering is not a rendered occurrence. Keep the
            // legacy candidate long enough for dead-code and structuring
            // rewrites to delete it; the final surviving value marker is the
            // only place allowed to turn either disposition into an error.
            Some(
                crate::binding_plan::PlannedValueSymbol::Elided(_)
                | crate::binding_plan::PlannedValueSymbol::Refused(_),
            ) => Ok(None),
            Some(crate::binding_plan::PlannedValueSymbol::Absent) | None => Err(
                crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(
                    value,
                ),
            ),
        }
    }

    pub(super) fn observed_input(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        if frame.observe_inputs {
            let expr = match self.planned_input_expr(frame, input_idx, expr.clone()) {
                Ok(planned) => planned,
                Err(
                    crate::observation_journal::LegacyObservationJournalError::PlannedElidedValueRendered { .. }
                    | crate::observation_journal::LegacyObservationJournalError::PlannedRefusedValueRendered { .. },
                ) => {
                    return self.observe_optional_normalized_input_expr(
                        frame.normalized_site,
                        input_idx,
                        expr,
                    );
                }
                Err(error) => {
                    self.retain_first_observation_error(error);
                    return expr;
                }
            };
            self.observe_optional_normalized_input_uses_expr(frame.normalized_site, input_idx, expr)
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
                            if let Some(max_arity) =
                                self.non_variadic_call_arity_for_site(source_block, source_op_idx)
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
        // Operand observations are attached while their exact expression
        // positions still exist. Wrapping the completed expression once per
        // input would falsely make every operand own the same aggregate node.
        let normalized_site = self.normalized_site(block_addr, op_idx);
        let mut frame = LowerFrame::for_observed_expr(normalized_site);
        let lowered = self.project_lowered_assignment(
            normalized_site,
            self.lower_op(op, &mut frame),
        );
        let lowered = match lowered {
            LoweredOp::Expr(expr) => LoweredExprAt::Rendered(expr),
            LoweredOp::Assign { lhs, rhs } => LoweredExprAt::Rendered(CExpr::assign(lhs, rhs)),
            LoweredOp::FinalizedStmt(CStmt::Expr(expr)) => LoweredExprAt::Rendered(expr),
            LoweredOp::FinalizedStmt(CStmt::Return(Some(expr))) => LoweredExprAt::Rendered(expr),
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
            LoweredExprAt::Rendered(expr) if op.dst().is_some() => LoweredExprAt::Rendered(
                self.observe_normalized_output_expr(block_addr, op_idx, expr),
            ),
            LoweredExprAt::Rendered(expr) => LoweredExprAt::Rendered(expr),
            fallback @ LoweredExprAt::DestinationFallback(_) => fallback,
        }
    }

    /// Attach only the exact result identity to a custom producer expression.
    ///
    /// Its operand positions no longer correspond to ordinary opcode lowering,
    /// so claiming them on the aggregate expression would relocate every input.
    pub(crate) fn observe_normalized_result_expr(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
        expr: CExpr,
    ) -> CExpr {
        if op.dst().is_some() {
            self.observe_normalized_output_expr(block_addr, op_idx, expr)
        } else {
            expr
        }
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
        let lowered = self.lower_op(op, &mut frame);
        let stmt = self.lowered_to_stmt(lowered)?;
        let stmt = self.project_finalized_assignment_stmt(normalized_site, stmt);

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
