//! Canonical parameter-relative address provenance.
//!
//! This pass owns affine pointer identity for prepared SSA. It propagates
//! parameter bases through arithmetic and proven stack spills so object,
//! memory-SSA, summary, symbolic, type, and render consumers share one fact.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::data_ref::parse_const_value;
use crate::{SSAFunction, SSAOp, SSAVar, SsaGraph, StackAddressRoot, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AffineAddressTerm {
    pub value: ValueId,
    pub coefficient: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ParameterAddressExpression {
    pub parameter: usize,
    pub terms: Vec<AffineAddressTerm>,
    pub offset: i64,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AddressProvenanceFacts {
    pub parameter_expressions: BTreeMap<ValueId, ParameterAddressExpression>,
}

impl AddressProvenanceFacts {
    pub fn parameter_expression(&self, value: ValueId) -> Option<&ParameterAddressExpression> {
        self.parameter_expressions.get(&value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AffineScalar {
    terms: BTreeMap<ValueId, i128>,
    constant: i128,
}

impl AffineScalar {
    fn constant(value: i64) -> Self {
        Self {
            terms: BTreeMap::new(),
            constant: i128::from(value),
        }
    }

    fn term(value: ValueId) -> Self {
        Self {
            terms: BTreeMap::from([(value, 1)]),
            constant: 0,
        }
    }

    fn combine(mut self, other: Self, sign: i128) -> Option<Self> {
        self.constant = self
            .constant
            .checked_add(other.constant.checked_mul(sign)?)?;
        for (value, coefficient) in other.terms {
            let delta = coefficient.checked_mul(sign)?;
            let coefficient = self.terms.entry(value).or_default();
            *coefficient = coefficient.checked_add(delta)?;
        }
        self.terms.retain(|_, coefficient| *coefficient != 0);
        Some(self)
    }

    fn scale(mut self, factor: i128) -> Option<Self> {
        self.constant = self.constant.checked_mul(factor)?;
        for coefficient in self.terms.values_mut() {
            *coefficient = coefficient.checked_mul(factor)?;
        }
        self.terms.retain(|_, coefficient| *coefficient != 0);
        Some(self)
    }
}

struct AddressCollector<'a> {
    function: &'a SSAFunction,
    graph: &'a SsaGraph,
    definitions: HashMap<SSAVar, SSAOp>,
    expressions: BTreeMap<ValueId, ParameterAddressExpression>,
    scalar_memo: HashMap<ValueId, Option<AffineScalar>>,
    scalar_visiting: HashSet<ValueId>,
    stack_in: BTreeMap<u64, BTreeMap<StackAddressRoot, ParameterAddressExpression>>,
    stack_out: BTreeMap<u64, BTreeMap<StackAddressRoot, ParameterAddressExpression>>,
}

impl<'a> AddressCollector<'a> {
    fn new(function: &'a SSAFunction, graph: &'a SsaGraph) -> Self {
        let definitions = function
            .blocks()
            .flat_map(|block| block.ops.iter())
            .filter_map(|op| op.dst().map(|dst| (dst.clone(), op.clone())))
            .collect();
        let mut expressions = BTreeMap::new();
        if let Some(prep) = function.decompile_prep_facts() {
            for (var, parameter) in &prep.formal_parameter_bases {
                if let Some(value) = graph.value_id_for_var(var) {
                    expressions.insert(
                        value,
                        ParameterAddressExpression {
                            parameter: *parameter,
                            terms: Vec::new(),
                            offset: 0,
                        },
                    );
                }
            }
        }
        Self {
            function,
            graph,
            definitions,
            expressions,
            scalar_memo: HashMap::new(),
            scalar_visiting: HashSet::new(),
            stack_in: BTreeMap::new(),
            stack_out: BTreeMap::new(),
        }
    }

    fn collect(mut self) -> AddressProvenanceFacts {
        let mut ready = self
            .function
            .block_addrs()
            .iter()
            .copied()
            .collect::<VecDeque<_>>();
        let mut queued = ready.iter().copied().collect::<BTreeSet<_>>();
        while let Some(block_addr) = ready.pop_front() {
            queued.remove(&block_addr);
            let input = self.merge_predecessor_stack(block_addr);
            let input_changed = self.stack_in.get(&block_addr) != Some(&input);
            if input_changed {
                self.stack_in.insert(block_addr, input.clone());
            }
            let (output, expression_changed) = self.transfer_block(block_addr, input);
            let output_changed = self.stack_out.get(&block_addr) != Some(&output);
            if output_changed {
                self.stack_out.insert(block_addr, output);
            }
            if input_changed || output_changed || expression_changed {
                for successor in self.function.successors(block_addr) {
                    if queued.insert(successor) {
                        ready.push_back(successor);
                    }
                }
            }
        }
        AddressProvenanceFacts {
            parameter_expressions: self.expressions,
        }
    }

    fn merge_predecessor_stack(
        &self,
        block_addr: u64,
    ) -> BTreeMap<StackAddressRoot, ParameterAddressExpression> {
        let predecessors = self.function.predecessors(block_addr);
        let known = predecessors
            .iter()
            .filter_map(|pred| self.stack_out.get(pred))
            .collect::<Vec<_>>();
        let Some(first) = known.first() else {
            return BTreeMap::new();
        };
        first
            .iter()
            .filter(|(slot, expression)| {
                known
                    .iter()
                    .skip(1)
                    .all(|state| state.get(slot) == Some(*expression))
            })
            .map(|(slot, expression)| (*slot, expression.clone()))
            .collect()
    }

    fn transfer_block(
        &mut self,
        block_addr: u64,
        mut stack: BTreeMap<StackAddressRoot, ParameterAddressExpression>,
    ) -> (BTreeMap<StackAddressRoot, ParameterAddressExpression>, bool) {
        let Some(block) = self.function.get_block(block_addr) else {
            return (stack, false);
        };
        let mut changed = false;
        for phi in &block.phis {
            let expressions = phi
                .sources
                .iter()
                .map(|(_, source)| self.expression_for_var(source))
                .collect::<Option<Vec<_>>>();
            let expression = expressions.and_then(|expressions| {
                let first = expressions.first()?.clone();
                expressions
                    .iter()
                    .all(|value| *value == first)
                    .then_some(first)
            });
            if let Some(expression) = expression {
                changed |= self.insert_expression(&phi.dst, expression);
            }
        }
        for op in &block.ops {
            match op {
                SSAOp::Store { addr, val, .. } | SSAOp::StoreGuarded { addr, val, .. } => {
                    if let Some(slot) = self.stack_root(addr) {
                        if let Some(expression) = self.expression_for_var(val) {
                            stack.insert(slot, expression);
                        } else {
                            stack.remove(&slot);
                        }
                    }
                }
                SSAOp::Load { dst, addr, .. }
                | SSAOp::LoadLinked { dst, addr, .. }
                | SSAOp::LoadGuarded { dst, addr, .. } => {
                    if let Some(expression) = self
                        .stack_root(addr)
                        .and_then(|slot| stack.get(&slot).cloned())
                    {
                        changed |= self.insert_expression(dst, expression);
                    }
                }
                _ => {}
            }
            if let Some((dst, expression)) = self.derive_op_expression(op) {
                changed |= self.insert_expression(dst, expression);
            }
        }
        (stack, changed)
    }

    fn derive_op_expression<'b>(
        &mut self,
        op: &'b SSAOp,
    ) -> Option<(&'b SSAVar, ParameterAddressExpression)> {
        match op {
            SSAOp::Copy { dst, src }
            | SSAOp::Cast { dst, src }
            | SSAOp::New { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Subpiece {
                dst,
                src,
                offset: 0,
            } => self
                .expression_for_var(src)
                .map(|expression| (dst, expression)),
            SSAOp::IntAdd { dst, a, b } => self
                .derive_additive_expression(a, b, 1, 1)
                .map(|expression| (dst, expression)),
            SSAOp::PtrAdd {
                dst,
                base,
                index,
                element_size,
            } => self
                .derive_additive_expression(base, index, 1, i128::from(*element_size))
                .map(|expression| (dst, expression)),
            SSAOp::IntSub { dst, a, b } => self
                .derive_additive_expression(a, b, -1, 1)
                .map(|expression| (dst, expression)),
            SSAOp::PtrSub {
                dst,
                base,
                index,
                element_size,
            } => self
                .derive_additive_expression(base, index, -1, i128::from(*element_size))
                .map(|expression| (dst, expression)),
            _ => None,
        }
    }

    fn derive_additive_expression(
        &mut self,
        left: &SSAVar,
        right: &SSAVar,
        right_sign: i128,
        right_scale: i128,
    ) -> Option<ParameterAddressExpression> {
        let left_base = self.expression_for_var(left);
        let right_base = self.expression_for_var(right);
        if left_base.is_some() && right_base.is_some() {
            return None;
        }
        if let Some(base) = left_base {
            let delta = self
                .scalar_for_var(right)?
                .scale(right_sign.checked_mul(right_scale)?)?;
            return add_delta(base, delta);
        }
        if right_sign > 0
            && let Some(base) = right_base
        {
            let delta = self.scalar_for_var(left)?;
            return add_delta(base, delta);
        }
        None
    }

    fn expression_for_var(&self, var: &SSAVar) -> Option<ParameterAddressExpression> {
        let value = self.graph.value_id_for_var(var)?;
        self.expressions.get(&value).cloned()
    }

    fn insert_expression(&mut self, var: &SSAVar, expression: ParameterAddressExpression) -> bool {
        let Some(value) = self.graph.value_id_for_var(var) else {
            return false;
        };
        match self.expressions.get(&value) {
            Some(existing) if *existing == expression => false,
            Some(_) => false,
            None => {
                self.expressions.insert(value, expression);
                true
            }
        }
    }

    fn stack_root(&self, var: &SSAVar) -> Option<StackAddressRoot> {
        let prep = self.function.decompile_prep_facts()?;
        prep.stack_address_root_of(var).copied().or_else(|| {
            prep.canonical_root_of(var)
                .and_then(|root| prep.stack_address_root_of(root))
                .copied()
        })
    }

    fn scalar_for_var(&mut self, var: &SSAVar) -> Option<AffineScalar> {
        let value = self.graph.value_id_for_var(var)?;
        self.scalar_for_value(value)
    }

    fn scalar_for_value(&mut self, value: ValueId) -> Option<AffineScalar> {
        if let Some(cached) = self.scalar_memo.get(&value) {
            return cached.clone();
        }
        if !self.scalar_visiting.insert(value) {
            return None;
        }
        let result = self.compute_scalar(value);
        self.scalar_visiting.remove(&value);
        self.scalar_memo.insert(value, result.clone());
        result
    }

    fn compute_scalar(&mut self, value: ValueId) -> Option<AffineScalar> {
        let var = self.graph.value(value)?.var.clone();
        if let Some(constant) = signed_constant(&var) {
            return Some(AffineScalar::constant(constant));
        }
        let Some(op) = self.definitions.get(&var).cloned() else {
            return Some(AffineScalar::term(value));
        };
        match op {
            SSAOp::Copy { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::New { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Subpiece { src, offset: 0, .. } => self.scalar_for_var(&src),
            SSAOp::IntNegate { src, .. } => self.scalar_for_var(&src)?.scale(-1),
            SSAOp::IntAdd { a, b, .. } => self
                .scalar_for_var(&a)?
                .combine(self.scalar_for_var(&b)?, 1),
            SSAOp::IntSub { a, b, .. } => self
                .scalar_for_var(&a)?
                .combine(self.scalar_for_var(&b)?, -1),
            SSAOp::IntMult { a, b, .. } => {
                let left = self.scalar_for_var(&a)?;
                let right = self.scalar_for_var(&b)?;
                if left.terms.is_empty() {
                    right.scale(left.constant)
                } else if right.terms.is_empty() {
                    left.scale(right.constant)
                } else {
                    None
                }
            }
            SSAOp::IntLeft { a, b, .. } => {
                let shift = self.scalar_for_var(&b)?;
                if !shift.terms.is_empty() {
                    return None;
                }
                let shift = u32::try_from(shift.constant).ok()?;
                self.scalar_for_var(&a)?.scale(1i128.checked_shl(shift)?)
            }
            _ => Some(AffineScalar::term(value)),
        }
    }
}

fn add_delta(
    mut base: ParameterAddressExpression,
    delta: AffineScalar,
) -> Option<ParameterAddressExpression> {
    let mut terms = base
        .terms
        .drain(..)
        .map(|term| (term.value, i128::from(term.coefficient)))
        .collect::<BTreeMap<_, _>>();
    for (value, coefficient) in delta.terms {
        let current = terms.entry(value).or_default();
        *current = current.checked_add(coefficient)?;
    }
    terms.retain(|_, coefficient| *coefficient != 0);
    base.offset = i64::try_from(i128::from(base.offset).checked_add(delta.constant)?).ok()?;
    base.terms = terms
        .into_iter()
        .map(|(value, coefficient)| {
            Some(AffineAddressTerm {
                value,
                coefficient: i64::try_from(coefficient).ok()?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(base)
}

fn signed_constant(var: &SSAVar) -> Option<i64> {
    let value = parse_const_value(&var.name)?;
    let bits = var.size.saturating_mul(8).min(64);
    if bits == 0 || bits == 64 {
        return Some(value as i64);
    }
    let sign = 1u64.checked_shl(bits - 1)?;
    let mask = 1u64.checked_shl(bits)?.wrapping_sub(1);
    let value = value & mask;
    Some(if value & sign == 0 {
        value as i64
    } else {
        (value | !mask) as i64
    })
}

pub(crate) fn collect_address_provenance(
    function: &SSAFunction,
    graph: &SsaGraph,
) -> AddressProvenanceFacts {
    AddressCollector::new(function, graph).collect()
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};

    use crate::{ObjectKind, RelativeMemoryAddress, SSAOp, SsaArtifact};

    fn aarch64_two_arg_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("aarch64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("x0", 0, 8));
        arch.add_register(RegisterDef::new("w0", 0, 4));
        arch.add_register(RegisterDef::new("x1", 8, 8));
        arch.add_register(RegisterDef::new("w1", 8, 4));
        arch.add_register(RegisterDef::new("sp", 16, 8));
        arch
    }

    #[test]
    fn parameter_address_survives_stack_spill_and_affine_index() {
        let arch = aarch64_two_arg_arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntSub {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
            val: Varnode::register(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x20, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::IntMult {
            dst: Varnode::unique(0x30, 8),
            a: Varnode::register(8, 8),
            b: Varnode::constant(40, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x40, 8),
            a: Varnode::unique(0x20, 8),
            b: Varnode::unique(0x30, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x50, 8),
            a: Varnode::unique(0x40, 8),
            b: Varnode::constant(16, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("artifact");
        let value = artifact
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.starts_with("tmp:50"))
            .expect("address value");
        let expression = artifact
            .addresses()
            .parameter_expression(value.id)
            .expect("parameter-relative expression");
        assert_eq!(expression.parameter, 0);
        assert_eq!(expression.offset, 16);
        assert_eq!(expression.terms.len(), 1);
        assert_eq!(expression.terms[0].coefficient, 40);
    }

    #[test]
    fn narrow_scalar_formal_is_not_a_parameter_address_base() {
        let arch = aarch64_two_arg_arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 4),
            a: Varnode::register(8, 4),
            b: Varnode::constant(4, 4),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("artifact");
        let scalar = artifact
            .graph()
            .values
            .iter()
            .find(|value| value.var.name == "w1")
            .expect("narrow formal");
        assert!(
            artifact
                .addresses()
                .parameter_expression(scalar.id)
                .is_none()
        );
    }

    #[test]
    fn adding_two_full_width_parameter_bases_is_not_certified() {
        let arch = aarch64_two_arg_arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0, 8),
            b: Varnode::register(8, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("artifact");
        let sum = artifact
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.starts_with("tmp:10"))
            .expect("sum");
        assert!(artifact.addresses().parameter_expression(sum.id).is_none());
    }

    #[test]
    fn parameter_address_survives_pointer_spill_after_affine_index() {
        let arch = aarch64_two_arg_arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntSub {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(32, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(16, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x20, 8),
            val: Varnode::register(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x30, 8),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x20, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x38, 8),
            src: Varnode::constant(40, 8),
        });
        block.push(R2ILOp::IntMult {
            dst: Varnode::unique(0x40, 8),
            a: Varnode::register(8, 8),
            b: Varnode::unique(0x38, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x50, 8),
            a: Varnode::unique(0x30, 8),
            b: Varnode::unique(0x40, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
            val: Varnode::unique(0x50, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x60, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x70, 8),
            a: Varnode::unique(0x60, 8),
            b: Varnode::constant(16, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x70, 8),
            val: Varnode::constant(1, 4),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x80, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x90, 8),
            a: Varnode::unique(0x80, 8),
            b: Varnode::constant(4, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0xa0, 2),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x90, 8),
        });

        let artifact = SsaArtifact::for_decompile(&[block], Some(&arch)).expect("artifact");
        let value = artifact
            .graph()
            .values
            .iter()
            .find(|value| value.var.name.starts_with("tmp:90"))
            .expect("field address value");
        let expression = artifact
            .addresses()
            .parameter_expression(value.id)
            .expect("parameter-relative expression after second spill");
        assert_eq!(expression.parameter, 0);
        assert_eq!(expression.offset, 4);
        assert_eq!(expression.terms.len(), 1);
        assert_eq!(expression.terms[0].coefficient, 40);
    }

    #[test]
    fn parameter_spill_survives_a_loop_backedge() {
        let arch = aarch64_two_arg_arch();
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::IntSub {
            dst: Varnode::register(16, 8),
            a: Varnode::register(16, 8),
            b: Varnode::constant(8, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
            val: Varnode::register(0, 8),
        });
        entry.push(R2ILOp::Branch {
            target: Varnode::constant(0x1004, 8),
        });

        let mut header = R2ILBlock::new(0x1004, 4);
        header.push(R2ILOp::Load {
            dst: Varnode::unique(0x10, 8),
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        header.push(R2ILOp::CBranch {
            target: Varnode::constant(0x100c, 8),
            cond: Varnode::register(8, 8),
        });

        let mut backedge = R2ILBlock::new(0x1008, 4);
        backedge.push(R2ILOp::Branch {
            target: Varnode::constant(0x1004, 8),
        });

        let mut exit = R2ILBlock::new(0x100c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let artifact = SsaArtifact::for_decompile(&[entry, header, backedge, exit], Some(&arch))
            .expect("artifact");
        let loaded = artifact
            .graph()
            .values
            .iter()
            .find(|value| value.var.name == "tmp:10" && value.var.version == 2)
            .expect("reloaded parameter");
        let expression = artifact
            .addresses()
            .parameter_expression(loaded.id)
            .expect("loop-carried stack spill");
        assert_eq!(expression.parameter, 0);
        assert!(expression.terms.is_empty());
        assert_eq!(expression.offset, 0);
    }

    #[test]
    fn affine_field_ranges_keep_independent_memory_versions() {
        let arch = aarch64_two_arg_arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::IntMult {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(8, 8),
            b: Varnode::constant(40, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::register(0, 8),
            b: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x30, 8),
            a: Varnode::unique(0x20, 8),
            b: Varnode::constant(16, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::unique(0x30, 8),
            val: Varnode::constant(0, 4),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x40, 8),
            a: Varnode::unique(0x20, 8),
            b: Varnode::constant(4, 8),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x50, 2),
            space: SpaceId::Ram,
            addr: Varnode::unique(0x40, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("artifact");
        let (load_index, _) = artifact
            .get_block(0x1000)
            .expect("block")
            .ops
            .iter()
            .enumerate()
            .find(|(_, op)| matches!(op, SSAOp::Load { .. }))
            .expect("load");
        let uses = artifact
            .memory_uses_for_op_site(0x1000, load_index)
            .expect("memory use");
        assert_eq!(uses.len(), 1);
        assert_eq!(uses[0].version.version, 0);
        assert!(matches!(
            artifact
                .objects()
                .object(uses[0].location.object)
                .map(|object| &object.kind),
            Some(ObjectKind::Parameter { index: 0 })
        ));
        assert!(matches!(
            &uses[0].location.address,
            RelativeMemoryAddress::Affine { terms, offset }
                if *offset == 4 && terms.len() == 1 && terms[0].coefficient == 40
        ));
    }

    #[test]
    fn distinct_parameter_bases_remain_may_alias() {
        let arch = aarch64_two_arg_arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
            val: Varnode::constant(0x42, 1),
        });
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x10, 1),
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
        });
        let artifact = SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("artifact");
        let block = artifact.get_block(0x1000).expect("block");
        let store_index = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Store { .. }))
            .expect("store");
        let load_index = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Load { .. }))
            .expect("load");
        let written = artifact
            .memory_defs_for_op_site(0x1000, store_index)
            .and_then(|defs| defs.first())
            .expect("memory def")
            .next_version;
        let uses = artifact
            .memory_uses_for_op_site(0x1000, load_index)
            .expect("memory use");
        assert_eq!(uses.len(), 1);
        assert_eq!(uses[0].version, written);
        assert_ne!(uses[0].location.object, written.object);
    }
}
