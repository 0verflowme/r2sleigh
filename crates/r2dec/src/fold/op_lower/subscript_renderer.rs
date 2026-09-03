//! Subscripts from the rewriter's canonical terms.
//!
//! The memory renderer used to take an address apart as a C expression --
//! find the operand that looked like a pointer, divide the index by the
//! element width -- and every such decision was a second rewriting layer with
//! no proof behind it. The rewriter decides now: a load or a store whose cell
//! canonicalises to a `Subscript` renders as `base[index]`, and this module
//! only spells the term and accounts for what the spelling stands in for.
//!
//! The accounting is the one every rendered equivalence pays. The producers
//! the term absorbed are discharged on the subscript, cells and effects both;
//! a constant the term folded away still owes its own cell and is marked on
//! the subscript too; and a leaf that names a bound object marks that object's
//! cell as any read of it does. The access's own address operand is marked by
//! the caller, exactly as it is for a dereference.
//!
//! # Why there is no tie-break between a declared member and a proven stride
//!
//! A declared struct member and a proven constant stride look like two
//! authorities over one access, and they are not: they cannot both answer.
//! `certified_member_fact_for_memory` returns a fact only when it matches
//! this access's object, its access id *and* its width, and only when exactly
//! one such fact exists. So the member fact is either a description of this
//! very access or it is absent, and the three reachable states are disjoint:
//!
//! - a member fact matches, and the member owns the access -- the subscript
//!   path declines, because `p->hash` and `((uint64_t *)p)[1]` are both true
//!   of the address and only the first is true of the *object*, which is what
//!   scoring recovered types against DWARF asks;
//! - the widths differ, or two facts match, in which case no member fact is
//!   returned at all and there is nothing to outrank the proven stride;
//! - neither exists, and the rewriter's subscript answers if it proved one.
//!
//! This is one owner per access rather than a ranking, so do not add a
//! tie-break here: a tie cannot occur, and code to resolve one would be a
//! second answerer for a question that already has exactly one.
//!
//! One case is decided rather than derived. Where a member fact matches but
//! the member renderer cannot build an expression -- the C address carries no
//! base identity to split around -- the access renders as a dereference and
//! not as a subscript. Asserting an array shape that a declared type
//! contradicts is worse than declining to name the shape at all, which is the
//! same reason a conflicting type refuses per value instead of guessing. It
//! is worth revisiting only on a measurement showing such accesses are common
//! enough to cost `type_match`.

use r2rewrite::{TermArena, TermId, TermKind};
use r2ssa::CanonicalInstructionSite;

use super::*;

impl<'a> FoldingContext<'a> {
    /// The access as `base[index]`, when the rewriter proved the cell is an
    /// element. `None` is a decline: the cell is not one, or something in the
    /// term has no C spelling, and the caller renders the address instead.
    pub(super) fn certified_subscript_expr_for_fact(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
        elem_ty: &CType,
    ) -> Option<CExpr> {
        // A declared aggregate outranks a proven address equivalence. Both
        // statements are true -- the cell at `p + 8` is `((T *)p)[1]` -- but
        // the source says that cell is a named struct field, and spelling it
        // as an array element claims a shape the declared type contradicts.
        // The member path owns this access, and where it cannot render one
        // the dereference stands.
        if self.certified_member_fact_for_memory(fact).is_some() {
            return None;
        }
        let names = self.inputs.binding_names?;
        let plan = names.plan();
        let canonical = plan.canonical();
        let access = canonical.access(fact.access)?;
        let arena = canonical.arena();
        let TermKind::Subscript { base, index } = arena.term(access.canonical).kind else {
            return None;
        };
        let prepared = self.prepared_ssa()?;
        let graph = prepared.graph();

        let base_expr = self.render_subscript_term(arena, base)?;
        let base_expr = self.subscript_base_at_element_type(arena, base, base_expr, elem_ty);
        let index_expr = self.render_subscript_term(arena, index)?;
        let mut expr = CExpr::Subscript {
            base: Box::new(base_expr),
            index: Box::new(index_expr),
        };

        let discharged: Vec<r2ssa::InstId> = access
            .discharges
            .iter()
            .filter_map(|id| match id.site {
                CanonicalInstructionSite::Op(ordinal) => usize::try_from(ordinal)
                    .ok()
                    .and_then(|op_idx| graph.inst_id_for_op_site(id.block_addr, op_idx)),
                CanonicalInstructionSite::Phi(_) | CanonicalInstructionSite::NativeSpan { .. } => {
                    None
                }
            })
            .collect();
        if discharged.len() != access.discharges.len() {
            return None;
        }
        // A literal operand of an instruction this term consumed is rendered
        // here too, and it is the one cell `observe_discharged_expr` cannot
        // fill. That function marks each discharged instruction's write, its
        // output value, and its operands' *uses*; a constant has no defining
        // instruction, so it is nobody's output and never appears in the
        // discharged set at all, while its only occurrence was inside the
        // address expression this subscript replaced.
        //
        // The earlier attempt looked for these among the term's leaves and
        // found none, because import turns a constant into `TermKind::Literal`
        // and `leaves` collects only `Leaf` and `Opaque`. Asking the graph for
        // the instruction's operands avoids depending on how a constant
        // happens to be represented in a term. Deduplicated, because one
        // literal may be an operand of two consumed instructions and would
        // otherwise be counted as two occurrences of one execution.
        let mut folded_literals = std::collections::BTreeSet::new();
        for inst in &discharged {
            let graph_inst = graph.inst(*inst)?;
            for input in graph_inst.inputs.iter().copied() {
                if graph.def_inst(input).is_some() {
                    continue;
                }
                if matches!(
                    names.disposition_for_value(input),
                    Some(crate::binding_plan::ValueDisposition::Inline { .. })
                ) {
                    folded_literals.insert(input);
                }
            }
        }
        for literal in folded_literals {
            expr = self.observe_inlined_value_expr(literal, expr);
        }

        // Always, even when the term absorbed nothing. The subscript is where
        // this address is rendered: the dereference path marks the address
        // value on its way through `certified_memory_address_expr`, and this
        // path does not go through it, so the cell has no other answerer.
        //
        // An empty discharge set is not the rare case. `constant_stride`
        // absorbs the add and the multiply, so the set is non-empty;
        // `pointer_walk` rewrites a bare merge leaf and absorbs nothing, so
        // the set is empty and the address would go unaccounted.
        expr = self.observe_discharged_expr(fact.address, &discharged, expr);
        Some(expr)
    }

    /// The base at the type the subscript reads through.
    ///
    /// C scales a subscript by the pointee, so the base has to be a pointer
    /// to the element type. A name already declared at that type is spelled
    /// bare; anything else -- an integer that held the address, a pointer to
    /// another width -- is converted once, at the base, which is the one
    /// place the conversion means something.
    fn subscript_base_at_element_type(
        &self,
        arena: &TermArena,
        base: TermId,
        rendered: CExpr,
        elem_ty: &CType,
    ) -> CExpr {
        let declared = match arena.term(base).kind {
            TermKind::ObjectAddress(_) | TermKind::Leaf(_) => {
                self.declared_type_of_rendered(&rendered)
            }
            _ => None,
        };
        let already_typed = match declared {
            Some(CType::Pointer(pointee)) | Some(CType::Array(pointee, _)) => *pointee == *elem_ty,
            _ => false,
        };
        if already_typed {
            rendered
        } else {
            CExpr::cast(CType::ptr(elem_ty.clone()), rendered)
        }
    }

    /// The declared type of a rendered name, through the observation markers
    /// and casts a read collects.
    fn declared_type_of_rendered(&self, expr: &CExpr) -> Option<CType> {
        match expr {
            CExpr::Observed { expr, .. } | CExpr::Paren(expr) => {
                self.declared_type_of_rendered(expr)
            }
            CExpr::Var(name) => Some(self.symbols.borrow().get(*name).ty.clone()),
            _ => None,
        }
    }

    /// A term of a subscript as C. Only what an element base or index can
    /// be made of: leaves, literals, placed objects, and integer arithmetic,
    /// conversions and selections over them. A memory read inside a term is
    /// declined -- the rewriter never expands one, so none is expected --
    /// and so is anything without a C form.
    fn render_subscript_term(&self, arena: &TermArena, id: TermId) -> Option<CExpr> {
        let term = arena.term(id);
        let width = term.width_bits();
        let unsigned = |bits: u32| CType::Int {
            bits,
            signedness: r2types::Signedness::Unsigned,
        };
        let signed = |bits: u32| CType::Int {
            bits,
            signedness: r2types::Signedness::Signed,
        };
        // C promotes anything narrower than `int` before operating on it, so
        // a result narrower than that is truncated back to the width the
        // machine wrapped at.
        let at_width = |expr: CExpr| {
            if width < 32 {
                CExpr::cast(unsigned(width), expr)
            } else {
                expr
            }
        };
        let child = |child: TermId| self.render_subscript_term(arena, child);
        Some(match term.kind {
            TermKind::Leaf(expr) => {
                let names = self.inputs.binding_names?;
                let plan = names.plan();
                match plan.machine_projection().expr(expr)?.kind() {
                    r2ssa::MachineExprKind::Source { binding, .. } => {
                        let value = binding.value();
                        let rendered = match self.planned_value_expr(value) {
                            Ok(rendered) => rendered,
                            Err(error) => {
                                self.retain_first_observation_error(error);
                                return None;
                            }
                        };
                        // A leaf that names a bound object owes that object's
                        // cell here, as any read of it does; a value rendered
                        // where it is read marked its own on the way.
                        let names_a_symbol = matches!(
                            names.disposition_for_value(value),
                            Some(crate::binding_plan::ValueDisposition::Bound { .. })
                        );
                        if names_a_symbol {
                            self.observe_inlined_value_expr(value, rendered)
                        } else {
                            rendered
                        }
                    }
                    r2ssa::MachineExprKind::Constant { binding, value } => {
                        let rendered = literal_expr(value.bits());
                        self.observe_inlined_value_expr(binding.value(), rendered)
                    }
                    _ => return None,
                }
            }
            TermKind::Literal(bits) => literal_expr(bits.bits()),
            TermKind::ObjectAddress(object) => self.certified_stack_var_expr_for_object(object)?,
            TermKind::Arithmetic { op, left, right } => at_width(CExpr::binary(
                match op {
                    r2ssa::MachineArithmeticOp::Add => BinaryOp::Add,
                    r2ssa::MachineArithmeticOp::Subtract => BinaryOp::Sub,
                    r2ssa::MachineArithmeticOp::Multiply => BinaryOp::Mul,
                },
                child(left)?,
                child(right)?,
            )),
            TermKind::Negate(input) => at_width(CExpr::unary(UnaryOp::Neg, child(input)?)),
            TermKind::Bitwise { op, left, right } => at_width(CExpr::binary(
                match op {
                    r2ssa::MachineBitwiseOp::And => BinaryOp::BitAnd,
                    r2ssa::MachineBitwiseOp::Or => BinaryOp::BitOr,
                    r2ssa::MachineBitwiseOp::Xor => BinaryOp::BitXor,
                },
                child(left)?,
                child(right)?,
            )),
            TermKind::BitwiseNot(input) => at_width(CExpr::unary(UnaryOp::BitNot, child(input)?)),
            TermKind::Boolean { op, left, right } => CExpr::binary(
                match op {
                    r2ssa::MachineBooleanOp::And => BinaryOp::And,
                    r2ssa::MachineBooleanOp::Or => BinaryOp::Or,
                    r2ssa::MachineBooleanOp::Xor => BinaryOp::Ne,
                },
                child(left)?,
                child(right)?,
            ),
            TermKind::BooleanNot(input) => CExpr::unary(UnaryOp::Not, child(input)?),
            TermKind::Shift {
                kind, value, count, ..
            } => {
                let shifted = child(value)?;
                let shifted = if matches!(kind, r2ssa::MachineShiftKind::ArithmeticRight) {
                    CExpr::cast(signed(arena.term(value).width_bits()), shifted)
                } else {
                    shifted
                };
                at_width(CExpr::binary(
                    match kind {
                        r2ssa::MachineShiftKind::Left => BinaryOp::Shl,
                        r2ssa::MachineShiftKind::LogicalRight
                        | r2ssa::MachineShiftKind::ArithmeticRight => BinaryOp::Shr,
                    },
                    shifted,
                    child(count)?,
                ))
            }
            TermKind::Compare {
                op,
                interpretation,
                left,
                right,
            } => {
                let operand_width = arena.term(left).width_bits();
                let convert = |expr: CExpr| match interpretation {
                    r2ssa::MachineSignedness::Signed => CExpr::cast(signed(operand_width), expr),
                    r2ssa::MachineSignedness::Unsigned => expr,
                };
                CExpr::binary(
                    match op {
                        r2ssa::MachineComparisonOp::Equal => BinaryOp::Eq,
                        r2ssa::MachineComparisonOp::NotEqual => BinaryOp::Ne,
                        r2ssa::MachineComparisonOp::LessThan => BinaryOp::Lt,
                        r2ssa::MachineComparisonOp::LessThanOrEqual => BinaryOp::Le,
                    },
                    convert(child(left)?),
                    convert(child(right)?),
                )
            }
            TermKind::Cast { kind, input } => {
                let from = arena.term(input).width_bits();
                let inner = child(input)?;
                match kind {
                    r2ssa::MachineCastKind::ZeroExtend => CExpr::cast(unsigned(width), inner),
                    r2ssa::MachineCastKind::SignExtend => {
                        CExpr::cast(signed(width), CExpr::cast(signed(from), inner))
                    }
                    r2ssa::MachineCastKind::Truncate => CExpr::cast(unsigned(width), inner),
                    r2ssa::MachineCastKind::BitReinterpret => inner,
                    r2ssa::MachineCastKind::IntegerToAddress
                    | r2ssa::MachineCastKind::AddressToInteger => return None,
                }
            }
            TermKind::Extract { input, lsb_bits } => {
                let inner = child(input)?;
                let shifted = if lsb_bits == 0 {
                    inner
                } else {
                    CExpr::binary(BinaryOp::Shr, inner, CExpr::IntLit(i64::from(lsb_bits)))
                };
                CExpr::cast(unsigned(width), shifted)
            }
            TermKind::Select {
                condition,
                if_true,
                if_false,
            } => CExpr::Ternary {
                cond: Box::new(child(condition)?),
                then_expr: Box::new(child(if_true)?),
                else_expr: Box::new(child(if_false)?),
            },
            TermKind::Opaque(_)
            | TermKind::Variable(_)
            | TermKind::Flag { .. }
            | TermKind::Concat { .. }
            | TermKind::Load { .. }
            | TermKind::Subscript { .. } => return None,
        })
    }
}

fn literal_expr(bits: u64) -> CExpr {
    if bits > i64::MAX as u64 {
        CExpr::UIntLit(bits)
    } else {
        CExpr::IntLit(bits as i64)
    }
}
