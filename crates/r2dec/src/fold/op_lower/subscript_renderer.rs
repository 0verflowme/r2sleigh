//! Subscripts from the rewriter's canonical terms.
//!
//! The memory renderer used to take an address apart as a C expression --
//! find the operand that looked like a pointer, divide the index by the
//! element width -- and every such decision was a second rewriting layer with
//! no proof behind it. The rewriter decides now: a load or a store whose cell
//! canonicalises to a `Subscript` renders as `base[index]`, and this module
//! only spells the term and accounts for what the spelling stands in for.
//!
//! This module does not account cells. It returns an opaque pending replacement
//! containing the rendered syntax and the structural access identity. The one
//! finalizer derives the absorbed producers from that access and marks their
//! values, inputs, writes, definitionless literals, and effects together with
//! the address value. The expression cannot be extracted before that happens.
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

use super::*;
use r2rewrite::{TermArena, TermId, TermKind};

impl<'a> FoldingContext<'a> {
    /// The access as `base[index]`, when the rewriter proved the cell is an
    /// element. `None` is a decline: the cell is not one, or something in the
    /// term has no C spelling, and the caller renders the address instead.
    pub(super) fn certified_subscript_expr_for_fact(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
        elem_ty: &CType,
    ) -> Option<PendingReplacementExpr> {
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
        let base_expr = self.render_subscript_term(arena, base)?;
        let base_expr = self.subscript_base_at_element_type(arena, base, base_expr, elem_ty);
        let mut index_expr = self.render_subscript_term(arena, index)?;
        if let Some(value) = self.certified_stack_array_index_value(fact, arena, index) {
            index_expr = self.observe_certified_array_index_expr(fact.access, value, index_expr);
        }
        let expr = CExpr::Subscript {
            base: Box::new(base_expr),
            index: Box::new(index_expr),
        };
        Some(PendingReplacementExpr::canonical_access(fact, expr))
    }

    /// The exact bound value an array-layout certificate substituted for this
    /// access's byte address.
    ///
    /// Ordinary subscript leaves are already operands of the machine address
    /// expression and carry their graph-use marker through the rewrite. A
    /// bound stack-array cell is different: its canonical term replaces the
    /// completed address with the certified element index while leaving the
    /// address producer intact. Naming that earlier value here therefore
    /// needs the certificate-owned placement read installed by the caller.
    fn certified_stack_array_index_value(
        &self,
        fact: &r2types::MemoryAccessRenderFact,
        arena: &TermArena,
        index: TermId,
    ) -> Option<r2ssa::ValueId> {
        let TermKind::Leaf(node) = arena.term(index).kind else {
            return None;
        };
        let r2ssa::MachineExprKind::Source { binding, .. } = self
            .inputs
            .binding_names?
            .plan()
            .machine_projection()
            .expr(node)?
            .kind()
        else {
            return None;
        };
        let value = binding.value();
        let prepared = self.prepared_ssa()?;
        let memory = prepared.structured().memory_accesses.get(&fact.access)?;
        let layout = prepared
            .certificates()
            .stack_slots
            .get(&memory.object)
            .and_then(|slot| match &slot.array_layout {
                r2ssa::StackArrayLayoutDisposition::Proven(layout) => Some(layout),
                r2ssa::StackArrayLayoutDisposition::NotIndexed
                | r2ssa::StackArrayLayoutDisposition::Refused(_) => None,
            })?;
        layout
            .indexed_elements
            .iter()
            .find(|element| element.address == fact.address)
            .and_then(|element| match element.element_index {
                Some(r2ssa::StackArrayElementIndex::Value(index)) if index == value => Some(value),
                Some(r2ssa::StackArrayElementIndex::Value(_))
                | Some(r2ssa::StackArrayElementIndex::Constant(_))
                | None => None,
            })
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
                        let crate::binding_plan::ValueDisposition::Bound { binding } =
                            names.disposition_for_value(value)?
                        else {
                            // An inline producer belongs in the canonical
                            // access's discharge set, not as a second nested
                            // renderer. Elided and refused values cannot be
                            // occurrences at all.
                            return None;
                        };
                        CExpr::Var(names.symbol_for_binding(*binding)?)
                    }
                    r2ssa::MachineExprKind::Constant { value, .. } => literal_expr(value.bits()),
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
