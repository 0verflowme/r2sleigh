use super::calls::CertifiedCallArgs;
use super::memory_renderer::CertifiedMemoryAccessExpr;
use super::projection::project_machine_write;
use super::*;

fn operation_requires_final_write_projection(op: &SSAOp) -> bool {
    op.dst().is_some()
}

impl<'a> FoldingContext<'a> {
    fn observation_lowering_refusal(
        error: &crate::observation_journal::LegacyObservationJournalError,
    ) -> OpLoweringRefusal {
        use crate::observation_journal::LegacyObservationJournalError as Error;
        match error {
            Error::RenderedValueRequired(_)
            | Error::InvalidPlannedInline { .. }
            | Error::PlannedElidedValueRendered { .. }
            | Error::PlannedRefusedValueRendered { .. }
            | Error::MissingPlannedValue(_) => {
                if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                    eprintln!("refusal from journal error {error:?}");
                }
                OpLoweringRefusal::missing_program_variable()
            }
            other => {
                if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                    eprintln!("refusal from journal error {other:?}");
                }
                OpLoweringRefusal::missing_machine_projection()
            }
        }
    }

    fn exact_normalized_op_effects(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
    ) -> std::collections::BTreeSet<r2ssa::SemanticObligationId> {
        // A call has no `dst`. One statement implements two instructions --
        // the call supplies the effect, the `CallDefine` owns the write -- so
        // the value the occurrence names has to come from the site's certified
        // result rather than from the operation's own output, which does not
        // exist. Without it the call-result obligation matched no occurrence
        // and every function that called anything was refused for a result its
        // rendering did assign.
        let rendered_value = match op {
            SSAOp::Call { .. } | SSAOp::CallInd { .. } => {
                self.certified_call_result_value((block_addr, op_idx))
            }
            _ => op.dst().and_then(|dst| self.value_id_for_rendered_op(dst)),
        };
        let mut obligations = self.exact_effect_obligations_for_normalized_value(
            EffectOccurrenceKind::Expression,
            block_addr,
            op_idx,
            rendered_value,
        );
        // The other half of the same statement. `x = f()` renders the call and
        // the definition of its result at once, so the `CallDefine`'s own
        // obligations are answered here; the `CallDefine` itself lowers to no
        // statement precisely because this one already assigned it, and left
        // alone its producer obligation had nothing to name.
        if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. })
            && let Some((define_block, define_idx)) =
                self.certified_call_result_definition_site((block_addr, op_idx))
        {
            obligations.extend(self.exact_effect_obligations_for_normalized_value(
                EffectOccurrenceKind::Expression,
                define_block,
                define_idx,
                rendered_value,
            ));
        }
        // Memory-effect ownership comes from the exact source operation and its
        // certified access, not from the finalized C shape. A stack-object
        // assignment is still the same source Store even though its AST no
        // longer contains a pointer dereference.
        let memory = match op {
            SSAOp::Load { .. } => self
                .certified_memory_access_for_current_op(false)
                .map(|cert| (EffectOccurrenceKind::MemoryRead, cert)),
            SSAOp::Store { .. } => self
                .certified_memory_access_for_current_op(true)
                .map(|cert| (EffectOccurrenceKind::MemoryWrite, cert)),
            _ => None,
        };
        if let Some((kind, cert)) = memory {
            obligations.extend(self.exact_effect_obligations_for_normalized_memory(
                kind,
                block_addr,
                op_idx,
                cert.space,
                Some(cert.address),
                cert.value,
            ));
        }
        obligations
    }

    fn normalized_output_projection(
        &self,
        site: crate::normalize::NormalizedOpSite,
    ) -> Result<
        crate::normalize::NormalizedOutputProjection,
        crate::observation_journal::LegacyObservationJournalError,
    > {
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
        let output = self.normalized_output_projection(site)?;
        let Some(names) = self.inputs.binding_names else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(
                    output.value,
                ),
            );
        };
        match names.require_write(output.inst) {
            Ok(r2ssa::MachineWriteDisposition::Exact(projection)) => {
                // A value already spelled at the object's own type is not
                // projected again. The projection exists to say how the
                // machine writes a carrier -- a lane, or a zero-extension into
                // the full register -- in that carrier's unsigned integer, and
                // applying it to an expression that is already the pointer the
                // object is declared as converts it straight back to an
                // integer and the assignment stops compiling.
                if matches!(
                    rhs.unobserved(),
                    CExpr::Cast {
                        ty: CType::Pointer(_),
                        ..
                    }
                ) {
                    return Ok((lhs, rhs));
                }
                let (lhs, rhs) = project_machine_write(lhs, rhs, *projection).map_err(|_| {
                    crate::observation_journal::LegacyObservationJournalError::RefusedRenderedWrite(
                        output.inst,
                    )
                })?;
                // The projection spells how the machine writes the carrier --
                // a lane, or a zero-extension into the full register -- in the
                // carrier's unsigned integer. That is the last word only while
                // the object being written is that integer. Where the plan
                // declared it a pointer, the conversion to the declaration is
                // what the compiler reads, and it goes outside the projection
                // rather than under it.
                if let Some(declared @ CType::Pointer(_)) =
                    self.value_declaration_type(output.value)
                {
                    return Ok((lhs, CExpr::cast(declared, rhs)));
                }
                Ok((lhs, rhs))
            }
            Ok(r2ssa::MachineWriteDisposition::Refused(_)) => {
                unreachable!("require_write cannot return a refused disposition")
            }
            Err(crate::binding_plan::RenderedIdentityRefusal::MachineWrite { .. }) => Err(
                crate::observation_journal::LegacyObservationJournalError::RefusedRenderedWrite(
                    output.inst,
                ),
            ),
            Err(_) => Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidWrite(
                    output.inst,
                ),
            ),
        }
    }

    /// Apply a source write only when the finalized statement targets the
    /// exact plan-owned output binding. A different target has no typed
    /// synthetic-origin certificate, so it cannot waive the `InstId` write
    /// projection.
    fn project_finalized_assignment_stmt(
        &self,
        site: Option<crate::normalize::NormalizedOpSite>,
        stmt: CStmt,
    ) -> OpLoweringResult<CStmt> {
        let Some(site) = site else {
            return Ok(stmt);
        };
        let output = match self.normalized_output_projection(site) {
            Ok(output) => output,
            Err(error) => {
                self.retain_first_observation_error(error);
                return Err(OpLoweringRefusal::missing_machine_projection());
            }
        };
        let Some(names) = self.inputs.binding_names else {
            return Err(OpLoweringRefusal::missing_program_variable());
        };
        let symbol = match names.require_value(output.value) {
            Ok(crate::binding_plan::PlannedValueSymbol::Bound(symbol)) => symbol,
            Ok(
                crate::binding_plan::PlannedValueSymbol::Inline(_)
                | crate::binding_plan::PlannedValueSymbol::Elided(_),
            ) => return Ok(stmt),
            Ok(
                crate::binding_plan::PlannedValueSymbol::Refused(_)
                | crate::binding_plan::PlannedValueSymbol::Absent,
            ) => unreachable!("require_value cannot return an absent or refused disposition"),
            Err(_) => return Err(OpLoweringRefusal::missing_program_variable()),
        };
        let CStmt::Expr(CExpr::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }) = stmt
        else {
            return Ok(stmt);
        };
        let lhs = *left;
        let rhs = *right;
        let planned_lhs = CExpr::Var(symbol);
        if !lhs.transparently_eq(&planned_lhs) {
            return Err(OpLoweringRefusal::missing_program_variable());
        }
        match self.project_planned_assignment(Some(site), lhs.clone(), rhs.clone()) {
            Ok((lhs, rhs)) => Ok(CStmt::Expr(CExpr::assign(lhs, rhs))),
            Err(error) => {
                let refusal = Self::observation_lowering_refusal(&error);
                self.retain_first_observation_error(error);
                Err(refusal)
            }
        }
    }

    /// Render a machine expression as the C expression it stands for.
    ///
    /// A value the plan marks inline is rendered where it is read rather than in
    /// a statement of its own, and until this existed the only expression that
    /// could be was a literal. Everything else answered `InvalidPlannedInline`,
    /// which is why a comparison's flag reached the reader as
    /// `ZF_1 = (a - b) == 0; if (!ZF_1)` and why a chain of machine temporaries
    /// each got a name.
    ///
    /// A `Source` leaf is where the recursion leaves the machine and re-enters
    /// the plan: it names another value, and what that value renders as is the
    /// plan's answer, not this function's. Anything the plan has not settled, or
    /// an expression deeper than a rendered expression has any business being,
    /// refuses rather than guesses.
    /// The expression the operation lowering itself produces for a value's
    /// definition, so that a folded value renders exactly as it would have
    /// rendered in its own statement.
    ///
    /// Deriving the expression a second time over the machine arena was the
    /// earlier approach, and it disagreed with this one about signedness: the
    /// arena's `interpretation` records how a value is later read, not how the
    /// defining operation computes it, so a signed comparison came back
    /// unsigned and folded into a test that is never true.
    ///
    /// Lowering in expression mode at the definition's own site also gives the
    /// operands their ordinary observations, which is what authorises reads
    /// that now sit nested inside another statement.
    fn inlined_definition_expr(&self, definition: r2ssa::InstId) -> Option<CExpr> {
        let prepared = self.inputs.prepared_ssa?;
        let (block_addr, op_idx) = prepared.inst_op_site(definition)?;
        // The operation being lowered right now cannot render itself: asking
        // for its own output as an expression is how a statement spells its
        // left-hand side, and re-entering would observe its operands twice.
        if self.current_block_addr.get() == Some(block_addr)
            && self.current_op_idx.get() == Some(op_idx)
        {
            return None;
        }
        let site = self.normalized_site(block_addr, op_idx)?;
        let op = prepared.function().get_block(block_addr)?.ops.get(op_idx)?;
        let previous_block = self.current_block_addr.replace(Some(block_addr));
        let previous_op = self.current_op_idx.replace(Some(op_idx));
        let frame = super::LowerFrame::for_observed_expr(Some(site));
        let previous_inlined = self.inlined_definition.replace(true);
        let lowered = self.op_to_expr_impl(op, &frame);
        self.inlined_definition.set(previous_inlined);
        self.current_block_addr.set(previous_block);
        self.current_op_idx.set(previous_op);
        lowered.ok().flatten()
    }

    /// The type the plan declares for a value, if it declares one.
    fn value_declaration_type(&self, value: ValueId) -> Option<CType> {
        let names = self.inputs.binding_names?;
        let crate::binding_plan::ValueDisposition::Bound { binding } =
            names.disposition_for_value(value)?
        else {
            return None;
        };
        Some(names.plan().binding(*binding)?.declaration_type().clone())
    }

    fn materialize_machine_expr(
        &self,
        names: &crate::binding_plan::BindingNameResolution,
        value: ValueId,
        expr: r2ssa::MachineExprId,
        depth: u32,
    ) -> Result<CExpr, crate::observation_journal::LegacyObservationJournalError> {
        use r2ssa::MachineExprKind as Kind;
        let invalid =
            || crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                value,
                expr,
            };
        if depth > 16 {
            return Err(invalid());
        }
        let Some(machine_expr) = names.inline_expr(expr) else {
            return Err(invalid());
        };
        let child =
            |id: r2ssa::MachineExprId| self.materialize_machine_expr(names, value, id, depth + 1);
        Ok(match machine_expr.kind() {
            Kind::Constant {
                binding,
                value: literal,
            } => {
                let bits = literal.bits();
                let rendered = if bits > i64::MAX as u64 {
                    CExpr::UIntLit(bits)
                } else {
                    CExpr::IntLit(bits as i64)
                };
                // Every value owes a cell, and a constant reached as a leaf of
                // a moved expression is rendered here rather than as an operand
                // of an emitted statement, so this is where it is marked.
                let constant = binding.value();
                if constant == value {
                    rendered
                } else {
                    self.observe_inlined_value_expr(constant, rendered)
                }
            }
            Kind::Source { binding, .. } => {
                let source = binding.value();
                if source == value {
                    return Err(invalid());
                }
                let rendered = self.planned_value_expr(source)?;
                // The read is authorised by the use the discharged definition
                // recorded: this leaf is one of its operands, and that use is
                // marked on the expression the leaf now sits in. What the leaf
                // still owes here is the value's own cell, when the leaf names
                // an object -- a value that is itself rendered where it is read
                // produced an expression rather than a name, and marked its
                // cell on the way.
                let names_a_symbol = self
                    .inputs
                    .binding_names
                    .and_then(|names| names.disposition_for_value(source))
                    .is_some_and(|disposition| {
                        matches!(
                            disposition,
                            crate::binding_plan::ValueDisposition::Bound { .. }
                        )
                    });
                if names_a_symbol {
                    self.observe_inlined_value_expr(source, rendered)
                } else {
                    rendered
                }
            }
            Kind::Copy { input } => child(*input)?,
            Kind::Arithmetic {
                op, left, right, ..
            } => CExpr::binary(
                match op {
                    r2ssa::MachineArithmeticOp::Add => BinaryOp::Add,
                    r2ssa::MachineArithmeticOp::Subtract => BinaryOp::Sub,
                    r2ssa::MachineArithmeticOp::Multiply => BinaryOp::Mul,
                },
                child(*left)?,
                child(*right)?,
            ),
            Kind::Bitwise { op, left, right } => CExpr::binary(
                match op {
                    r2ssa::MachineBitwiseOp::And => BinaryOp::BitAnd,
                    r2ssa::MachineBitwiseOp::Or => BinaryOp::BitOr,
                    r2ssa::MachineBitwiseOp::Xor => BinaryOp::BitXor,
                },
                child(*left)?,
                child(*right)?,
            ),
            Kind::Boolean { op, left, right } => CExpr::binary(
                match op {
                    r2ssa::MachineBooleanOp::And => BinaryOp::And,
                    r2ssa::MachineBooleanOp::Or => BinaryOp::Or,
                    // C has no boolean exclusive-or; on values the machine
                    // already reduced to zero or one, inequality is it.
                    r2ssa::MachineBooleanOp::Xor => BinaryOp::Ne,
                },
                child(*left)?,
                child(*right)?,
            ),
            Kind::Compare {
                op, left, right, ..
            } => CExpr::binary(
                match op {
                    r2ssa::MachineComparisonOp::Equal => BinaryOp::Eq,
                    r2ssa::MachineComparisonOp::NotEqual => BinaryOp::Ne,
                    r2ssa::MachineComparisonOp::LessThan => BinaryOp::Lt,
                    r2ssa::MachineComparisonOp::LessThanOrEqual => BinaryOp::Le,
                },
                child(*left)?,
                child(*right)?,
            ),
            Kind::Shift {
                kind,
                value: shifted,
                count,
                ..
            } => {
                // An arithmetic right shift is `>>` on a signed operand and
                // nothing else, so the operand is cast rather than the operator
                // changed -- the same mistake as the comparison above, and the
                // same fix.
                let value_expr = child(*shifted)?;
                let value_expr = if matches!(kind, r2ssa::MachineShiftKind::ArithmeticRight) {
                    let bits = names
                        .inline_expr(*shifted)
                        .map(|expr| expr.ty().width_bits())
                        .unwrap_or(32);
                    CExpr::cast(
                        CType::Int {
                            bits,
                            signedness: r2types::Signedness::Signed,
                        },
                        value_expr,
                    )
                } else {
                    value_expr
                };
                CExpr::binary(
                    match kind {
                        r2ssa::MachineShiftKind::Left => BinaryOp::Shl,
                        r2ssa::MachineShiftKind::LogicalRight
                        | r2ssa::MachineShiftKind::ArithmeticRight => BinaryOp::Shr,
                    },
                    value_expr,
                    child(*count)?,
                )
            }
            Kind::BitwiseNot { input } => CExpr::unary(UnaryOp::BitNot, child(*input)?),
            Kind::BooleanNot { input } => CExpr::unary(UnaryOp::Not, child(*input)?),
            Kind::Negate { input, .. } => CExpr::unary(UnaryOp::Neg, child(*input)?),
            Kind::Select {
                condition,
                if_true,
                if_false,
            } => CExpr::Ternary {
                cond: Box::new(child(*condition)?),
                then_expr: Box::new(child(*if_true)?),
                else_expr: Box::new(child(*if_false)?),
            },
            // Everything else -- a memory read, a merge, a division that traps,
            // a flag or a width change whose C form depends on a type this does
            // not carry -- keeps its own statement.
            _ => return Err(invalid()),
        })
    }

    pub(crate) fn planned_value_expr(
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
        match names.require_value(value) {
            Ok(crate::binding_plan::PlannedValueSymbol::Bound(symbol)) => Ok(CExpr::Var(symbol)),
            Ok(crate::binding_plan::PlannedValueSymbol::Inline(expr)) => {
                let Some(machine_expr) = names.inline_expr(expr) else {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                            value,
                            expr,
                        },
                    );
                };
                // A literal still owes its cells. Returning it straight to the
                // caller skipped every observation the value and its defining
                // instruction owe, so a copy of a constant -- `tmp = 0xcc9e2d51`
                // in `murmur3_32` -- folded into its use and left the effect it
                // answered for with no rendered occurrence anywhere.
                let literal = match machine_expr.kind() {
                    r2ssa::MachineExprKind::Constant { binding, value: literal } => {
                        if binding.value() != value {
                            return Err(
                                crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                                    value,
                                    expr,
                                },
                            );
                        }
                        let bits = literal.bits();
                        Some(if bits > i64::MAX as u64 {
                            CExpr::UIntLit(bits)
                        } else {
                            CExpr::IntLit(bits as i64)
                        })
                    }
                    _ => None,
                };
                // A value defined by an operation renders as the expression
                // that operation's own lowering produces, moved to where the
                // value is read. Deriving it a second time over the machine
                // arena was the earlier approach and disagreed about
                // signedness: the arena's `interpretation` records how a value
                // is later read, not how the defining operation computes it, so
                // a signed comparison came back unsigned and folded into a test
                // that is never true.
                //
                // A value with no operation behind it -- a live-in register, a
                // merge -- has no lowering to move, and the arena still answers
                // for it.
                let definition = self
                    .prepared_ssa()
                    .and_then(|prepared| prepared.graph().def_inst(value));
                let rendered = match literal {
                    Some(literal) => literal,
                    None => match definition
                        .and_then(|definition| self.inlined_definition_expr(definition))
                    {
                        Some(rendered) => rendered,
                        None => self.materialize_machine_expr(names, value, expr, 0)?,
                    },
                };
                // A constant has no defining instruction and owes no write or
                // operand cells, but it still owes its own.
                let Some(definition) = definition else {
                    return Ok(self.observe_inlined_value_expr(value, rendered));
                };
                Ok(self.observe_discharged_expr(value, &[definition], rendered))
            }
            Ok(crate::binding_plan::PlannedValueSymbol::Elided(reason)) => Err(
                crate::observation_journal::LegacyObservationJournalError::PlannedElidedValueRendered {
                    value,
                    reason,
                },
            ),
            Ok(
                crate::binding_plan::PlannedValueSymbol::Refused(_)
                | crate::binding_plan::PlannedValueSymbol::Absent,
            ) => unreachable!("require_value cannot return an absent or refused disposition"),
            Err(crate::binding_plan::RenderedIdentityRefusal::Value { reason, .. }) => Err(
                crate::observation_journal::LegacyObservationJournalError::PlannedRefusedValueRendered {
                    value,
                    reason,
                },
            ),
            Err(_) => Err(
                crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(
                    value,
                ),
            ),
        }
    }

    fn normalized_input_projection(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
    ) -> Result<
        (
            crate::normalize::NormalizedOpSite,
            crate::normalize::NormalizedInputProjection,
        ),
        crate::observation_journal::LegacyObservationJournalError,
    > {
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
        let input = projection.inputs.get(input_idx).cloned().ok_or(
            crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedInput {
                site,
                input_idx,
            },
        )?;
        Ok((site, input))
    }

    fn uniform_planned_input_disposition(
        &self,
        site: crate::normalize::NormalizedOpSite,
        input_idx: usize,
        input: &crate::normalize::NormalizedInputProjection,
    ) -> Result<
        Option<(r2ssa::UseSite, r2ssa::MachineUseDisposition)>,
        crate::observation_journal::LegacyObservationJournalError,
    > {
        let Some(first_site) = input.uses.first().copied() else {
            return Ok(None);
        };
        let Some(names) = self.inputs.binding_names else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::RenderedValueRequired(
                    input.value,
                ),
            );
        };
        let first_disposition = match names.require_use(first_site) {
            Ok(
                disposition @ (r2ssa::MachineUseDisposition::Exact(_)
                | r2ssa::MachineUseDisposition::MemoryAddress(_)),
            ) => *disposition,
            Ok(r2ssa::MachineUseDisposition::Refused(_)) => {
                unreachable!("require_use cannot return a refused disposition")
            }
            Err(crate::binding_plan::RenderedIdentityRefusal::MachineUse { .. }) => {
                return Err(
                    crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                        first_site,
                    ),
                );
            }
            Err(_) => {
                return Err(
                    crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                        first_site,
                    ),
                );
            }
        };
        for use_site in input.uses.iter().copied().skip(1) {
            match names.require_use(use_site) {
                Ok(disposition) if *disposition == first_disposition => {}
                Ok(r2ssa::MachineUseDisposition::Refused(_)) => {
                    unreachable!("require_use cannot return a refused disposition")
                }
                Err(crate::binding_plan::RenderedIdentityRefusal::MachineUse { .. }) => {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                            use_site,
                        ),
                    );
                }
                Ok(
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
                Err(_) => {
                    return Err(
                        crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                            use_site,
                        ),
                    );
                }
            }
        }
        Ok(Some((first_site, first_disposition)))
    }

    fn planned_input_expr(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
    ) -> Result<CExpr, crate::observation_journal::LegacyObservationJournalError> {
        let (site, input) = self.normalized_input_projection(frame, input_idx)?;
        let Some((first_site, first_disposition)) =
            self.uniform_planned_input_disposition(site, input_idx, &input)?
        else {
            // Synthetic preservation inputs have no original graph use and
            // therefore no source-owned projection to apply.
            return Ok(self.observe_optional_normalized_input_value_expr(
                frame.normalized_site,
                input_idx,
                self.planned_value_expr(input.value)?,
            ));
        };
        match first_disposition {
            r2ssa::MachineUseDisposition::Exact(slice) => {
                let base = self.observe_optional_normalized_input_value_expr(
                    frame.normalized_site,
                    input_idx,
                    self.planned_value_expr(input.value)?,
                );
                // A pointer read whole is spelled at its own type. The
                // projection casts to the unsigned integer of the carrier's
                // width, which is what every object used to be declared as;
                // applied to an object the evidence declared a pointer it says
                // `(uint64_t)p`, and the assignment that follows will not
                // compile. The slice is the whole carrier at offset zero, so
                // the projection selects nothing and the declared type is the
                // exact statement to make about what is read.
                let declared_pointer = matches!(
                    self.value_declaration_type(input.value),
                    Some(CType::Pointer(_))
                );
                if declared_pointer
                    && slice.bit_offset() == 0
                    && slice.width_bits() == slice.carrier_width_bits()
                    && let Some(declared) = self.value_declaration_type(input.value)
                {
                    return Ok(CExpr::cast(declared, base));
                }
                super::projection::project_machine_use_of(base, slice, declared_pointer).map_err(
                    |_| {
                    // The machine use is exact, but the strict C dialect cannot spell
                    // this projection without more type evidence. Refuse the emitted
                    // occurrence instead of inventing an integer or pointer type.
                        crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                            first_site,
                        )
                    },
                )
            }
            // A contextual address cannot be projected from an arbitrary AST.
            // Only `planned_memory_input_expr` accepts the opaque expression
            // minted from the exact structured-access render fact.
            r2ssa::MachineUseDisposition::MemoryAddress(_) => Err(
                crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                    first_site,
                ),
            ),
            r2ssa::MachineUseDisposition::Refused(_) => {
                unreachable!("the refused source use returned before projection")
            }
        }
    }

    fn planned_memory_input_expr(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
        certified: CertifiedMemoryAccessExpr,
    ) -> Result<CExpr, crate::observation_journal::LegacyObservationJournalError> {
        let (site, input) = self.normalized_input_projection(frame, input_idx)?;
        let Some((first_site, disposition)) =
            self.uniform_planned_input_disposition(site, input_idx, &input)?
        else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidNormalizedInput {
                    site,
                    input_idx,
                },
            );
        };
        let r2ssa::MachineUseDisposition::MemoryAddress(address) = disposition else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::RefusedRenderedUse(
                    first_site,
                ),
            );
        };
        let Some(access) = address.memory_access() else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidUse(first_site),
            );
        };
        let source_is_write = match self
            .inputs
            .prepared_ssa
            .and_then(|prepared| prepared.graph().inst(first_site.inst))
            .map(|inst| &inst.payload)
        {
            Some(r2ssa::InstPayload::Op(SSAOp::Load { .. })) => false,
            Some(r2ssa::InstPayload::Op(SSAOp::Store { .. })) => true,
            _ => {
                return Err(
                    crate::observation_journal::LegacyObservationJournalError::InvalidUse(
                        first_site,
                    ),
                );
            }
        };
        if address.binding().value() != input.value
            || certified.address() != input.value
            || certified.access() != access
            || certified.access().inst != first_site.inst
            || certified.is_write() != source_is_write
        {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidUse(first_site),
            );
        }
        let access = certified.access();
        let is_write = certified.is_write();
        let expr = certified.into_expr();
        let Some(journal) = self.inputs.observation_journal else {
            return Ok(expr);
        };
        journal
            .borrow_mut()
            .observe_stack_access_expr(access, is_write, expr)
    }

    pub(crate) fn planned_input_expr_at(
        &self,
        block_addr: u64,
        op_idx: usize,
        input_idx: usize,
    ) -> OpLoweringResult<CExpr> {
        let frame = LowerFrame::for_observed_expr(self.normalized_site(block_addr, op_idx));
        match self.planned_input_expr(&frame, input_idx) {
            Ok(expr) => Ok(self.observe_optional_normalized_input_uses_expr(
                frame.normalized_site,
                input_idx,
                expr,
            )),
            Err(error) => {
                let refusal = Self::observation_lowering_refusal(&error);
                self.retain_first_observation_error(error);
                Err(refusal)
            }
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
        let Some(names) = self.inputs.binding_names else {
            return Err(
                crate::observation_journal::LegacyObservationJournalError::MissingPlannedValue(
                    value,
                ),
            );
        };
        match names.require_value(value) {
            Ok(crate::binding_plan::PlannedValueSymbol::Bound(symbol)) => {
                Ok(Some(CExpr::Var(symbol)))
            }
            Ok(crate::binding_plan::PlannedValueSymbol::Inline(expr)) => Err(
                crate::observation_journal::LegacyObservationJournalError::InvalidPlannedInline {
                    value,
                    expr,
                },
            ),
            // An attempted lowering is not a rendered occurrence. Keep the
            // legacy candidate long enough for dead-code and structuring
            // rewrites to delete it; the final surviving value marker is the
            // only place allowed to turn either disposition into an error.
            Ok(
                crate::binding_plan::PlannedValueSymbol::Elided(_)
            ) => Ok(None),
            Ok(
                crate::binding_plan::PlannedValueSymbol::Refused(_)
                | crate::binding_plan::PlannedValueSymbol::Absent,
            ) => unreachable!("require_value cannot return an absent or refused disposition"),
            Err(crate::binding_plan::RenderedIdentityRefusal::Value { reason, .. }) => Err(
                crate::observation_journal::LegacyObservationJournalError::PlannedRefusedValueRendered {
                    value,
                    reason,
                },
            ),
            Err(_) => Err(
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
            let expr = match self.planned_input_expr(frame, input_idx) {
                Ok(planned) => planned,
                Err(error) => {
                    let refusal = Self::observation_lowering_refusal(&error);
                    self.retain_first_observation_error(error);
                    self.retain_first_lowering_refusal(refusal);
                    return expr;
                }
            };
            self.observe_optional_normalized_input_uses_expr(frame.normalized_site, input_idx, expr)
        } else {
            expr
        }
    }

    pub(super) fn observed_memory_input(
        &self,
        frame: &LowerFrame,
        input_idx: usize,
        certified: CertifiedMemoryAccessExpr,
    ) -> CExpr {
        let fallback = certified.expr().clone();
        if !frame.observe_inputs {
            return fallback;
        }
        let expr = match self.planned_memory_input_expr(frame, input_idx, certified) {
            Ok(planned) => planned,
            Err(error) => {
                let refusal = Self::observation_lowering_refusal(&error);
                self.retain_first_observation_error(error);
                self.retain_first_lowering_refusal(refusal);
                return fallback;
            }
        };
        self.observe_optional_normalized_input_uses_expr(frame.normalized_site, input_idx, expr)
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
            // The object the result is assigned to decides the conversion,
            // exactly as it does everywhere else. A call site that owns its
            // result assigns it directly, and where the plan declared that
            // object a pointer the callee's integer return has to be
            // converted or the assignment does not compile.
            let call = match self
                .certified_call_result_value((block_addr, op_idx))
                .and_then(|value| self.value_declaration_type(value))
            {
                Some(declared @ CType::Pointer(_)) => CExpr::cast(declared, call),
                _ => call,
            };
            return LoweredOp::Assign {
                lhs: owner,
                rhs: call,
            };
        }
        LoweredOp::Expr(call)
    }

    fn certified_call_target_expr(
        &self,
        frame: &LowerFrame,
        target: &SSAVar,
        cert: &r2types::CallsiteArgumentFacts,
        direct: bool,
    ) -> OpLoweringResult<CExpr> {
        if self.prepared_value_id_for_var(target) != Some(cert.target) {
            return Err(OpLoweringRefusal::missing_machine_projection());
        }
        // A direct call spells its callee's name, which the call site's own
        // identity supplies. Asking the plan for the operand's expression
        // would be asking for the object that holds the callee's address, and
        // there is none: the plan elides that value, and the operand's
        // occurrence is elided beside it. Only an indirect call reads a target
        // the program computed, and only there is the planned expression the
        // thing being called.
        if direct {
            let address = cert
                .direct_target
                .ok_or_else(|| OpLoweringRefusal::missing_machine_projection())?;
            return Ok(self.callee_identity_expr(&self.callee_identity_for_direct_target(address)));
        }
        let planned = self.planned_input_expr(frame, 0).map_err(|error| {
            let refusal = Self::observation_lowering_refusal(&error);
            self.retain_first_observation_error(error);
            refusal
        })?;
        if cert.direct_target.is_some() {
            return Err(OpLoweringRefusal::missing_machine_projection());
        }
        let target = Self::indirect_callable_expr(planned);
        Ok(self.observe_optional_normalized_input_uses_expr(frame.normalized_site, 0, target))
    }

    pub(super) fn lower_op(
        &self,
        op: &SSAOp,
        frame: &mut LowerFrame,
    ) -> OpLoweringResult<LoweredOp> {
        self.pending_lowering_refusal.set(None);
        let lowered = match frame.mode {
            LowerMode::Expr => self
                .op_to_expr_impl(op, frame)?
                .map(LoweredOp::Expr)
                .unwrap_or(LoweredOp::None),
            LowerMode::Stmt => {
                if frame.with_call_args {
                    match op {
                        SSAOp::Call { target } => {
                            let Some((source_block, source_op_idx)) = frame.source_call_site else {
                                return Err(OpLoweringRefusal::missing_machine_projection());
                            };
                            let (cert, _) = self.admitted_callsite(source_block, source_op_idx)?;
                            let func_expr =
                                self.certified_call_target_expr(frame, target, cert, true)?;
                            let certified_args =
                                self.certified_call_args_for_site(source_block, source_op_idx)?;
                            self.record_callee_declaration(
                                &func_expr,
                                source_block,
                                source_op_idx,
                                &certified_args,
                            )?;
                            let call = CExpr::call_at(
                                (source_block, source_op_idx),
                                func_expr,
                                certified_args.args.clone(),
                            );
                            return self.finish_lowering_transaction(
                                self.lower_certified_statement_call(
                                    source_block,
                                    source_op_idx,
                                    call,
                                    certified_args,
                                ),
                            );
                        }
                        SSAOp::CallInd { target } => {
                            let Some((source_block, source_op_idx)) = frame.source_call_site else {
                                return Err(OpLoweringRefusal::missing_machine_projection());
                            };
                            let (cert, _) = self.admitted_callsite(source_block, source_op_idx)?;
                            let func_expr =
                                self.certified_call_target_expr(frame, target, cert, false)?;
                            let certified_args =
                                self.certified_call_args_for_site(source_block, source_op_idx)?;
                            let call = CExpr::call_at(
                                (source_block, source_op_idx),
                                func_expr,
                                certified_args.args.clone(),
                            );
                            return self.finish_lowering_transaction(
                                self.lower_certified_statement_call(
                                    source_block,
                                    source_op_idx,
                                    call,
                                    certified_args,
                                ),
                            );
                        }
                        _ => {}
                    }
                }

                self.op_to_stmt_impl(op, frame)?
                    .map(Self::lowered_from_stmt)
                    .unwrap_or(LoweredOp::None)
            }
        };
        self.finish_lowering_transaction(lowered)
    }

    fn finish_lowering_transaction(&self, lowered: LoweredOp) -> OpLoweringResult<LoweredOp> {
        match self.pending_lowering_refusal.take() {
            Some(refusal) => {
                if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                    eprintln!("refusal {refusal:?} raised by finish_lowering_transaction");
                }
                Err(refusal)
            }
            None => Ok(lowered),
        }
    }

    /// Convert an SSA operation to a C statement, with call argument context.
    pub(super) fn op_to_stmt_with_args(
        &self,
        op: &SSAOp,
        block_addr: u64,
        op_idx: usize,
    ) -> OpLoweringResult<Option<CStmt>> {
        let source_site = self.source_op_site_for_normalized_op(block_addr, op_idx);
        if matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) && source_site.is_none() {
            return Ok(Some(self.certified_residual_comment(format!(
                "synthetic operation cannot carry callsite facts at 0x{block_addr:x}:{op_idx}"
            ))));
        }
        let normalized_site = self.normalized_site(block_addr, op_idx);
        let source_call_site = source_site.or(Some((block_addr, op_idx)));
        let mut frame = LowerFrame::for_stmt(normalized_site, source_call_site, true);
        let lowered = self.lower_op(op, &mut frame)?;
        let Some(stmt) = self.lowered_to_stmt(lowered) else {
            return Ok(None);
        };
        // Final write projection belongs only to an operation with a typed SSA
        // output. Calls and stores are source effects with exact input/effect
        // observations but no destination; asking them for a normalized output
        // fabricates an assignment contract they do not have.
        let stmt = if operation_requires_final_write_projection(op) {
            self.project_finalized_assignment_stmt(normalized_site, stmt)?
        } else {
            stmt
        };

        let obligations = self.exact_normalized_op_effects(op, block_addr, op_idx);
        let rendered = !matches!(stmt.unobserved(), CStmt::Comment(_) | CStmt::Empty);
        let stmt = if op.dst().is_some() && rendered {
            self.observe_normalized_output_stmt(block_addr, op_idx, stmt)
        } else if rendered
            && matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. })
            && self.call_site_assigns_its_own_result((block_addr, op_idx))
            && let Some((definition_block, definition_idx)) =
                self.certified_call_result_definition_site((block_addr, op_idx))
        {
            self.observe_normalized_output_stmt(definition_block, definition_idx, stmt)
        } else {
            stmt
        };
        Ok(Some(self.observe_effect_stmt(&obligations, stmt)))
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

#[cfg(test)]
mod typed_output_contract_tests {
    use super::*;

    #[test]
    fn only_operations_with_typed_outputs_require_final_write_projection() {
        let dst = r2ssa::SSAVar::new("dst", 1, 8);
        let input = r2ssa::SSAVar::new("input", 0, 8);

        assert!(operation_requires_final_write_projection(&SSAOp::Copy {
            dst,
            src: input.clone(),
        }));
        assert!(!operation_requires_final_write_projection(&SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr: input.clone(),
            val: input.clone(),
        }));
        assert!(!operation_requires_final_write_projection(&SSAOp::Call {
            target: input.clone(),
        }));
        assert!(!operation_requires_final_write_projection(
            &SSAOp::CallInd { target: input }
        ));
    }
}
